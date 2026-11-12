-- Prove2me | Definitions.Def_ImpuritySim_Machine
-- name    : ImpuritySim_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:28:10.698393+00:00
-- url     : https://prove2.me/theorems/35043683-5164-4299-9ec3-0d89269de188
-- title:
--   The deterministic unit-cost real RAM, the input $(n,m,\delta,\alpha,h,c)$ of Theorem 5.3, and enumeration of threshold sets
-- statement:
--   Theorem 5.3 asks for "a classical algorithm … with runtime $\mathrm{poly}(n,\delta^{-1})$" and Theorem 4.1 for an enumeration "in time $O(n|S|)$ by a classical algorithm". The machine is the published unit-cost real RAM `SubsetConvFPRAS`: real registers with $+,-,\times,\div$ and comparisons, integer pointers with $+,-$, integer memory, a cast from integers to reals, and `halt` with a real output. It has no square root, floor, exponential, logarithm or eigen-decomposition instruction. A program is
--
--   1. **admissible** if all its real literals are rational, and
--   2. **deterministic** if it contains no coin-flip and no oracle instruction.
--
--   **Input of Theorem 5.3.** The integer memory holds $n$ and $m$; the real memory holds $\delta$ in cell $0$, $\alpha$ in cell $1$, $h_{jk}$ in cell $2+2nj+k$ ($0$-based $j,k<2n$), and $c_A$ in cell $2+4n^2+\sum_{a\in A}2^a$ for every even $A\subseteq\{0,\dots,2m-1\}$. Each executed instruction costs one step, and after `halt` the state no longer changes.
--
--   **Threshold sets.** For weights $w\in\mathbb R^n_{\ge0}$ and $T\ge0$ let $S=\{x\in\{0,1\}^n:\sum_iw_ix_i\le T\}$ (it contains $x=0$). A program **enumerates threshold sets in $C\,n\,|S|$ steps** if, for every $n\ge1$, $w\ge0$ and $T\ge0$, on input $n$ (integer cell $0$), $w_0,\dots,w_{n-1}$ (real cells $0,\dots,n-1$) and $T$ (real cell $n$), it has halted within $C\,n\,|S|$ steps with $|S|$ in integer cell $0$ and the elements of $S$ listed without repetition, bit $i$ of the $k$-th one in integer cell $1+kn+i$.
--
--   **Formalization Note** "Deterministic" is the published predicate `SYKCavity.Deterministic`. The bitmap ground set is empty and the oracles are $0$; a deterministic program reads neither them nor the coin tape.
-- source:
--   Jiang–Ju–Parekh–Rayudu–Zhao, Polynomial-time classical and quantum simulation of quantum impurity models, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Theorem 5.3, p.27; Theorem 4.1, p.20; enumeration algorithm, App. B.1, p.55

import Mathlib
import Definitions.Def_SubsetConvFPRAS_Machine
import Definitions.Def_SYKCavity_Machine

namespace ImpuritySim

/-!
# The deterministic real RAM, the input of Theorem 5.3, and threshold-set enumeration

J. Jiang, N. Ju, O. Parekh, C. Rayudu, A. Zhao, *Polynomial-time classical and quantum simulation
of quantum impurity models*, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2):
Theorem 5.3, p.27 ("a classical algorithm … with runtime poly(n, δ⁻¹)"); Theorem 4.1, p.20 ("the
set S can be enumerated in time O(n|S|) by a classical algorithm"); App. B.1, p.55.

**Formalization Note.**
* The machine is the published `SubsetConvFPRAS` unit-cost real RAM: `+ − × ÷` on reals
  (`x / 0 = 0`), comparisons, integer pointers with `+ −`, integer memory, a cast of a pointer to a
  real, and `halt` with a real output. It has no square root, floor, exponential, logarithm or
  eigen-decomposition instruction. Programs here are `Admissible` (rational literals only) and
  `SYKCavity.Deterministic` (the published predicate: no `coin` and no `query` instruction), so a run does not read the coin tape or
  the value oracles; the bitmap ground set is `Fin 0` and the oracles are `0`.
* Input of Theorem 5.3 (`start`): integer memory `I 0 = n`, `I 1 = m`, `0` elsewhere; real memory
  `M 0 = δ`, `M 1 = α`, `M (2 + 2n·j + k) = h_{jk}` for `j, k : Fin (2n)` (0-based),
  `M (2 + 4n² + Σ_{a ∈ A} 2^a) = c_A` for every even `A ⊆ Fin (2m)`, and `0` elsewhere. These cells
  are pairwise distinct.
* Every executed instruction costs one step; after `halt` the state stutters, so the output after
  `T` steps is final once it is `some _`.
* `wSet w T = {x ∈ {0,1}^n : Σ_i w_i x_i ≤ T}`. `EnumeratesThresholdSets P C`: for every `n ≥ 1`,
  every `w ≥ 0` and every `T ≥ 0`, the run of `P` on input `I 0 = n`, `M i = w_i` (`i < n`),
  `M n = T` has halted within `C·n·|S|` steps (`S = wSet w T`, `|S| ≥ 1` since `0 ∈ S`), and its
  integer memory lists `S`: `I 0 = |S|` and the `i`-th bit of the `k`-th listed string is
  `I (1 + k·n + i)`; the listed strings are distinct elements of `S`, hence all of `S`.
-/

/-- Integer input of Theorem 5.3: `I 0 = n`, `I 1 = m`. -/
def encodeInts (n m : ℕ) : ℤ → ℤ := fun z =>
  if z = 0 then (n : ℤ) else if z = 1 then (m : ℤ) else 0

/-- Real input of Theorem 5.3: `δ`, `α`, then `h` row by row, then the impurity coefficients `c_A`
of the even sets `A ⊆ Fin (2m)` at `2 + 4n² + Σ_{a ∈ A} 2^a`. -/
noncomputable def encodeReals (n m : ℕ) (δ α : ℝ) (h : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (c : Finset (Fin (2 * m)) → ℝ) : ℤ → ℝ := fun z =>
  if z = 0 then δ else if z = 1 then α else
    (∑ j : Fin (2 * n), ∑ k : Fin (2 * n),
        if z = (2 + 2 * n * j.val + k.val : ℕ) then h j k else 0) +
      ∑ A : Finset (Fin (2 * m)),
        if Even A.card ∧ z = (2 + 4 * n ^ 2 + ∑ a ∈ A, 2 ^ a.val : ℕ) then c A else 0

/-- The initial state on input `(n, m, δ, α, h, c)`. -/
noncomputable def start (n m : ℕ) (δ α : ℝ) (h : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (c : Finset (Fin (2 * m)) → ℝ) : SubsetConvFPRAS.State 0 :=
  SubsetConvFPRAS.mkInit (encodeInts n m) (fun _ => ∅) (encodeReals n m δ α h c)

/-- The output register after `T` steps of `P` on input `(n, m, δ, α, h, c)` (no coins, zero
oracles). -/
noncomputable def outputAfter (P : SubsetConvFPRAS.Program) (n m : ℕ) (δ α : ℝ)
    (h : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (c : Finset (Fin (2 * m)) → ℝ) (T : ℕ) :
    Option ℝ :=
  (SubsetConvFPRAS.run P (fun _ => 0) (fun _ => 0) (start n m δ α h c) (fun _ => false) T).output

/-- The threshold set `{x ∈ {0,1}^n : Σ_i w_i x_i ≤ T}`. -/
noncomputable def wSet {n : ℕ} (w : Fin n → ℝ) (T : ℝ) : Finset (Fin n → Fin 2) :=
  Finset.univ.filter fun x => ∑ i, w i * ((x i : ℕ) : ℝ) ≤ T

/-- The input of the enumerator: `I 0 = n`; `M i = w_i` for `i < n`, `M n = T`. -/
noncomputable def enumStart (n : ℕ) (w : Fin n → ℝ) (T : ℝ) : SubsetConvFPRAS.State 0 :=
  SubsetConvFPRAS.mkInit (fun z => if z = 0 then (n : ℤ) else 0) (fun _ => ∅)
    (fun z => if z = n then T else if h : 0 ≤ z ∧ z.toNat < n then w ⟨z.toNat, h.2⟩ else 0)

/-- `P` enumerates every threshold set `wSet w T` (`w ≥ 0`, `T ≥ 0`) in at most `C·n·|S|` steps,
leaving the list of its elements in integer memory: `I 0 = |S|`, bit `i` of the `k`-th string at
`I (1 + k·n + i)`. -/
def EnumeratesThresholdSets (P : SubsetConvFPRAS.Program) (C : ℕ) : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (w : Fin n → ℝ), (∀ i, 0 ≤ w i) → ∀ T : ℝ, 0 ≤ T →
    let S := wSet w T
    let s := SubsetConvFPRAS.run P (fun _ => 0) (fun _ => 0) (enumStart n w T) (fun _ => false)
      (C * n * S.card)
    s.output.isSome ∧ s.integerMemory 0 = (S.card : ℤ) ∧
      ∃ f : Fin S.card → (Fin n → Fin 2), Function.Injective f ∧ (∀ k, f k ∈ S) ∧
        ∀ (k : Fin S.card) (i : Fin n),
          s.integerMemory ((1 + k.val * n + i.val : ℕ) : ℤ) = ((f k i : ℕ) : ℤ)

end ImpuritySim


