-- Prove2me | Definitions.Def_PackingLPAccel_Layout
-- name    : PackingLPAccel_Layout
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:24.60889+00:00
-- url     : https://prove2.me/theorems/9f093e41-5a6d-4966-81e6-68f33629a8bc
-- title:
--   Memory layouts: arrays, sparse enumerations, oracle blocks
-- statement:
--   A layout places two lists, one of reals and one of integers, from address $0$ of the shared memories, with $0$ in every other cell. A matrix is given by an enumeration $e$ of its nonzero entries in any order, as positions $\mathrm{row}_0,\mathrm{col}_0,\mathrm{row}_1,\mathrm{col}_1,\dots$ together with the list of values. Negative addresses form the oracle block, whose cell number $k$ is $-1-k$.
--
--   A bound of order $\mathrm{nnz}(A)$ on the work forces a sparse input, since a program must be able to avoid reading every position of a dense array. These helpers keep the input and output conventions of the mission's programs explicit.
--
--   **Formalization Note** The paper fixes no encoding, so the layouts are readings of the mission. Every theorem quantifies over all enumerations of the nonzero entries. $\mathsf{HoldsBlocks}$ says that the registers $p[1]$, $p[0]$ point at output blocks holding two given lists.
-- source:
--   Chen, Chen, Graur, Sidford, Accelerated Parallel Algorithms for Packing Linear Programming, STOC 2027 submission (manuscript sha256 1dac7711…), footnote 4, p.1 (pdf 2); nnz(A), p.6 (pdf 7)

import Mathlib
import Definitions.Def_PackingLPAccel_Machine

namespace PackingLPAccel

/-!
# Memory layouts

Chen, Chen, Graur, Sidford, *Accelerated Parallel Algorithms for Packing Linear Programming*,
STOC 2027 submission (manuscript sha256 1dac7711…). The paper fixes no encoding, so these are readings
of the mission. An `nnz(A)`-time bound forces a sparse input, hence the triples (p.1, p.6).

**Formalization Note.** A layout is two lists read from address `0`: every other cell holds `0`.
Nonnegative addresses hold the input and the output. Negative addresses are the oracle block: the cell
number `k` of the block is `-1 - k`. Enumerations of the nonzero entries are arbitrary: every theorem
quantifies over all of them.
-/

/-- The real memory holding a list from address `0`, and `0` elsewhere. -/
noncomputable def realArray (xs : List ℝ) : ℤ → ℝ :=
  fun a => if 0 ≤ a then xs.getD a.toNat 0 else 0

/-- The integer memory holding a list from address `0`, and `0` elsewhere. -/
def intArray (ys : List ℤ) : ℤ → ℤ :=
  fun a => if 0 ≤ a then ys.getD a.toNat 0 else 0

/-- The initial state of a program: zero registers, zero calls, the two lists in memory. -/
noncomputable def initState (xs : List ℝ) (ys : List ℤ) : State :=
  ⟨fun _ => 0, fun _ => 0, realArray xs, intArray ys, 0⟩

/-- `e` enumerates exactly the nonzero entries of `A`, each once, in any order. -/
def IsNonzeroEnum {ι κ : Type*} {N : ℕ} (A : ι → κ → ℝ) (e : Fin N → ι × κ) : Prop :=
  Function.Injective e ∧ Set.range e = {ij | A ij.1 ij.2 ≠ 0}

/-- The list of the values of the enumerated entries. -/
noncomputable def sparseVals {r c N : ℕ} (A : Fin r → Fin c → ℝ) (e : Fin N → Fin r × Fin c) :
    List ℝ :=
  List.ofFn fun t => A (e t).1 (e t).2

/-- The list `row₀, col₀, row₁, col₁, …` of the enumerated positions. -/
def sparseIdx {r c N : ℕ} (e : Fin N → Fin r × Fin c) : List ℤ :=
  (List.ofFn fun t => [(((e t).1 : ℕ) : ℤ), (((e t).2 : ℕ) : ℤ)]).flatten

/-- Cell number `k` of the oracle block. -/
def blockAddr (k : ℕ) : ℤ := -1 - (k : ℤ)

/-- The memory `M` with cells `off, …, off + len - 1` of the oracle block overwritten by `f`. -/
noncomputable def writeBlock (M : ℤ → ℝ) (off len : ℕ) (f : ℕ → ℝ) : ℤ → ℝ :=
  fun a => if a < 0 ∧ off ≤ (-1 - a).toNat ∧ (-1 - a).toNat < off + len then
    f ((-1 - a).toNat - off) else M a

/-- The vector held in the oracle block from cell `off`. -/
def readBlock {ι : ℕ} (M : ℤ → ℝ) (off : ℕ) : Fin ι → ℝ := fun j => M (blockAddr (off + j))

/-- At the end of a program, private registers `p[1]`, `p[0]` point at the output blocks, which hold
the two lists. -/
def HoldsBlocks (s : State) (xs : List ℝ) (ys : List ℤ) : Prop :=
  (∀ k (h : k < xs.length), s.M (s.p 1 + (k : ℤ)) = xs[k]) ∧
    (∀ k (h : k < ys.length), s.I (s.p 0 + (k : ℤ)) = ys[k])

end PackingLPAccel


