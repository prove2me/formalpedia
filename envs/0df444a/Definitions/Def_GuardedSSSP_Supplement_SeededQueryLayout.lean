-- Prove2me | Definitions.Def_GuardedSSSP_Supplement_SeededQueryLayout
-- name    : GuardedSSSP_Supplement_SeededQueryLayout
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:20:49.24121+00:00
-- url     : https://prove2.me/theorems/cd25d47d-0494-4ff3-8ecc-6214bd8aad16
-- title:
--   Input and output layouts of the preprocessing and query programs of Theorem C.1
-- statement:
--   Let $H=(V,E)$ have $n$ vertices and $m$ arcs, root $r$, weights $w$, dominator tree $\mathrm{dpar}$ and calibration $p$.
--
--   1. **Preprocessing input.** Integer memory holds $n$, $m$, $r$, the arc tails, the arc heads (the base mission's SSSP layout) and then the dominator-tree parent array; real memory holds $w$ and then $p$.
--   2. **Query input.** A query starts from the final memory of the preprocessing run with registers reset, and the seed vector written over it: integer cell $-1-v$ is $1$ for a present seed and $0$ for an absent one, real cell $-1-v$ holds $\beta(v)$ (or $0$ if absent).
--   3. **Output.** At halting, integer cell $-1-v$ is $0$ when $d_\beta(v)=\infty$ and $1$ otherwise, and then real cell $-1-v$ holds $d_\beta(v)$.
--
--   These layouts make Theorem C.1's preprocessing/query pair a statement about two programs of the base RAM. Every query restarts from the same prepared memory, so queries whose seeds depend on earlier answers are covered by a statement for every seed vector.
--
--   **Formalization Note** The tree and the calibration are supplied to the preprocessing program because Theorem C.1 charges their computation separately as $T_{\mathrm{dom}}$ and $T_{\mathrm{cal}}$.
-- source:
--   Cai, Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths, STOC 2027 submission (manuscript sha256 bcda0e91…), Theorem C.1, p.37 (PDF p.38); (44), p.36 (PDF p.37)

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Network
import Definitions.Def_GuardedSSSP_dist
import Definitions.Def_GuardedSSSP_Machine
import Definitions.Def_GuardedSSSP_Supplement_seededDist

namespace GuardedSSSP

namespace Supplement

open AtomicDynRouting.ResidenceTime GuardedSSSP.Machine

/-!
# Input and output layouts of the preprocessing / query pair of Theorem C.1

Bin Cai, *Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths*, STOC 2027
submission (manuscript sha256 bcda0e91…), Theorem C.1, p.37 (PDF p.38): "Let T_dom and T_cal be the actual
RAM costs of computing that tree and the scalar distances p(v) = dist_H(r, v), respectively. … Every query
returns all values in (44) as held scalar registers or infinity tags. … These bounds include reading the
seeds, initializing the query state, and writing all outputs."

**Formalization Note.**
* **Preprocessing input.** Integer memory: the base mission's SSSP layout with source `r`
  (`Machine.inputInts G r`: cell `0` is `n`, cell `1` is `m`, cell `2` is `r`, cells `3 + e` the tails,
  cells `3 + m + e` the heads), followed by the dominator-tree parent array: cell `3 + 2m + v` is the
  parent of `v` (the root's slot holds `r`). Real memory: cell `e` holds `w e` for `e < m`, cell `m + v`
  holds `p(v)`. All other cells, all registers and the program counter are `0`.
  The tree and the calibration are supplied because the theorem charges them separately as `T_dom` and
  `T_cal`; the remaining preprocessing must then cost `O(m + n)`.
* **Query input.** A query starts from the final memory of the preprocessing run (both banks), with
  registers and program counter reset to `0`, and the seed vector written over it: integer cell `−1 − v`
  is `1` for a present seed and `0` for an absent seed (`β(v) = ∞`), real cell `−1 − v` holds `β(v)` for a
  present seed and `0` otherwise. Every query starts from the same prepared memory, whatever earlier
  queries were asked; since the theorem is stated for every seed vector, seeds chosen adaptively from
  earlier answers are covered.
* **Output.** The base mission's convention: at halting, integer cell `−1 − v` is `0` when `d_β(v) = ∞`
  and `1` otherwise, and then real cell `−1 − v` holds `d_β(v)`.
-/

/-- The seed vector `β` with presence flags `flag` and values `val`: `β v = val v` if `flag v`, else `⊤`
(absent). -/
noncomputable def seedVec {n : ℕ} (flag : Fin n → Bool) (val : Fin n → ℝ) (v : Fin n) : EReal :=
  if flag v then ((val v : ℝ) : EReal) else ⊤

/-- The initial state of the preprocessing run on `(G, w, r)`, given the dominator-tree parent array
`dpar` and the calibration `p`. -/
def prepInit {n m : ℕ} (G : Network (Fin n) (Fin m)) (r : Fin n) (w : Fin m → ℝ)
    (dpar : Fin n → Fin n) (p : Fin n → ℝ) : State where
  pc := 0
  ireg := fun _ => 0
  imem := fun z =>
    if 0 ≤ z then (inputInts G r ++ List.ofFn (fun v : Fin n => (((dpar v : ℕ)) : ℤ))).getD z.toNat 0
    else 0
  rreg := fun _ => 0
  rmem := fun z => if 0 ≤ z then (List.ofFn w ++ List.ofFn p).getD z.toNat 0 else 0
  halted := false
  stuck := false

/-- The initial state of a query: the prepared memory of `σ`, registers and program counter reset, and
the seeds written at cells `−1 − v`. -/
noncomputable def queryInit {n : ℕ} (σ : State) (flag : Fin n → Bool) (val : Fin n → ℝ) : State where
  pc := 0
  ireg := fun _ => 0
  imem := fun z =>
    if z ≤ -1 ∧ (-1 - z).toNat < n then
      (List.ofFn (fun v : Fin n => if flag v then (1 : ℤ) else 0)).getD (-1 - z).toNat 0
    else σ.imem z
  rreg := fun _ => 0
  rmem := fun z =>
    if z ≤ -1 ∧ (-1 - z).toNat < n then
      (List.ofFn (fun v : Fin n => if flag v then val v else 0)).getD (-1 - z).toNat 0
    else σ.rmem z
  halted := false
  stuck := false

/-- The state `σ` holds the exact seeded distances `d_β`: the infinity flag in integer cell `−1 − v`
and the finite value in real cell `−1 − v`. -/
def SeededOutputCorrect {n m : ℕ} (G : Network (Fin n) (Fin m)) (w : Fin m → ℝ)
    (β : Fin n → EReal) (σ : State) : Prop :=
  ∀ v : Fin n,
    (seededDist G w β v = ⊤ → σ.imem (-1 - (v : ℕ)) = 0) ∧
    (seededDist G w β v ≠ ⊤ →
      σ.imem (-1 - (v : ℕ)) = 1 ∧ ((σ.rmem (-1 - (v : ℕ)) : ℝ) : EReal) = seededDist G w β v)

end Supplement

end GuardedSSSP


