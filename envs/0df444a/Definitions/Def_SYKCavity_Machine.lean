-- Prove2me | Definitions.Def_SYKCavity_Machine
-- name    : SYKCavity_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:34:33.645349+00:00
-- url     : https://prove2.me/theorems/8db55cdf-9973-4423-a75f-9966793ca236
-- title:
--   The deterministic unit-cost real RAM and the input $(N,w,i_1<\dots<i_w,\beta,J)$ of Theorem 2
-- statement:
--   Theorem 2 asks for a **deterministic classical algorithm** running in time $O(N^K)$. The model is the published unit-cost real RAM `SubsetConvFPRAS` (real registers with $+,-,\times,\div$ and comparisons, integer pointers and integer memory, a cast from integers to reals, and `halt` with a real output; no floor, square root, exponential or logarithm instruction). A program is
--
--   1. **admissible** if all its real literals are rational, and
--   2. **deterministic** if it contains no coin-flip and no oracle instruction.
--
--   On input $(N,w,i_1<\dots<i_w,\beta,J)$ the integer memory holds $N$, $w$ and the sites $i_1,\dots,i_w$, and the real memory holds $\beta$ in cell $0$ and $J_A$ in cell $1+\operatorname{colex}(A)$, where for $A=\{a<b<c<d\}$
--   $$\operatorname{colex}(A)=\binom a1+\binom b2+\binom c3+\binom d4$$
--   is the colexicographic rank, a bijection onto $\{0,\dots,\binom N4-1\}$. Each executed instruction costs one step; `outputAfter` is the output register after $T$ steps.
--
--   **Formalization Note** The bitmap ground set is empty and the oracles are $0$; a deterministic program never reads them or the coin tape.
-- source:
--   Schmidhuber–Zlokapa, Polynomial-time algorithms for mean-field models up to the glass transition, arXiv:2610.06807 (held version, sha256 25d817ba…cfc5), Theorem 2, pp.4–5; operation count (4.40), p.31

import Mathlib
import Definitions.Def_SubsetConvFPRAS_Machine
import Definitions.Def_SYKCavity_Majorana

namespace SYKCavity

/-!
# The deterministic real RAM and the input of Theorem 2

A. Schmidhuber, A. Zlokapa, *Polynomial-time algorithms for mean-field models up to the glass
transition*, arXiv:2610.06807 (held version, sha256 25d817ba…cfc5), Theorem 2, pp.4–5: "There is a
deterministic classical algorithm which … outputs `f̂_O(β, J)` … in time at most `O(N^K)`".

**Formalization Note.**
* The machine is the published `SubsetConvFPRAS` unit-cost real RAM (`+ − × ÷` on reals, comparisons,
  integer pointers and integer memory, a cast of an integer to a real, `halt` with a real output; no
  floor, square root, exponential or logarithm instruction). Programs used here are `Admissible`
  (rational literals only) and `Deterministic` (no `coin` and no `query` instruction), so a run does
  not depend on the coin tape or on the value oracles. The ground set of the bitmaps is `Fin 0`.
* Input: the integer memory holds `I 0 = N`, `I 1 = w`, `I (2 + k) = i_{k+1}` (0-based site of the
  `k`-th Majorana of `O`), and `0` elsewhere; the real memory holds `M 0 = β` and
  `M (1 + colexRank A) = J_A` for every 4-subset `A`, and `0` elsewhere.
* `colexRank {a < b < c < d} = C(a,1) + C(b,2) + C(c,3) + C(d,4)` (0-based sites), the colexicographic
  rank, a bijection from the 4-subsets of `Fin N` onto `{0, …, C(N,4) − 1}`.
* Every executed instruction costs one step; `run P μ ν s₀ ω k` is the state after `k` steps.
-/

/-- No randomness and no oracle: the program contains no `coin` and no `query` instruction. -/
def Deterministic (P : SubsetConvFPRAS.Program) : Prop :=
  ∀ op ∈ P, (∀ d, op ≠ SubsetConvFPRAS.Instr.coin d) ∧
    ∀ (which : Bool) (d bank : ℕ), op ≠ SubsetConvFPRAS.Instr.query which d bank

/-- The colexicographic rank of a 4-subset: `Σ_{a ∈ A} C(a, #{b ∈ A | b < a} + 1)`. -/
def colexRank {N : ℕ} (A : Finset (Fin N)) : ℕ :=
  ∑ a ∈ A, Nat.choose a.val ((A.filter (· < a)).card + 1)

/-- Integer input: `N`, `w`, then the sites `i_1 < ⋯ < i_w` of the observable. -/
def encodeInts (N w : ℕ) (idx : Fin w ↪o Fin N) : ℤ → ℤ := fun z =>
  if z = 0 then (N : ℤ) else if z = 1 then (w : ℤ)
  else if h : 0 ≤ z - 2 ∧ (z - 2).toNat < w then ((idx ⟨(z - 2).toNat, h.2⟩ : ℕ) : ℤ) else 0

/-- Real input: `β` in cell `0`, `J_A` in cell `1 + colexRank A`. -/
noncomputable def encodeReals {N : ℕ} (β : ℝ) (J : Quad N → ℝ) : ℤ → ℝ := fun z =>
  if z = 0 then β else ∑ A : Quad N, if (1 + colexRank A.1 : ℤ) = z then J A else 0

/-- The initial state on input `(N, w, i_1 < ⋯ < i_w, β, J)`. -/
noncomputable def start (N w : ℕ) (idx : Fin w ↪o Fin N) (β : ℝ) (J : Quad N → ℝ) :
    SubsetConvFPRAS.State 0 :=
  SubsetConvFPRAS.mkInit (encodeInts N w idx) (fun _ => ∅) (encodeReals β J)

/-- The output register after `T` steps of `P` from `start N w idx β J` (no coins, zero oracles). -/
noncomputable def outputAfter (P : SubsetConvFPRAS.Program) (N w : ℕ) (idx : Fin w ↪o Fin N)
    (β : ℝ) (J : Quad N → ℝ) (T : ℕ) : Option ℝ :=
  (SubsetConvFPRAS.run P (fun _ => 0) (fun _ => 0) (start N w idx β J) (fun _ => false) T).output

end SYKCavity


