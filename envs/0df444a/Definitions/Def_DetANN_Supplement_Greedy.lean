-- Prove2me | Definitions.Def_DetANN_Supplement_Greedy
-- name    : DetANN_Supplement_Greedy
-- status  : Definition
-- author  : @milia
-- created : 2026-11-21T07:11:53.476156+00:00
-- url     : https://prove2.me/theorems/b194a550-93fa-4b57-a462-7531703e3184
-- title:
--   The sign layout and the cost bound of the conditional-expectation subroutine
-- statement:
--   Two definitions used by the construction program `pre` (definition `DetANN_Supplement_PreProg`).
--   - $\mathrm{SignsAt}(\mathrm{mem},L,k,\xi)$, for $\xi:[L]\times[2^k]\to\{\text{true},\text{false}\}$: for all $\ell<L$, $r<2^k$ the real cell $-2^k-1-(\ell\cdot2^k+r)$ holds $\mathrm{signOf}(\xi_{\ell r})\in\{\pm1\}$. This is the layout written by `pre` and read by the evaluation program `ev`.
--   - $\mathrm{evalB}(N,d,L,p_0)=100\,(N+1)(d+1)(L+1)(d+4p_0+3)^3$: the step bound of one call of the subroutine `EVAL` of `pre`, which evaluates the conditional expectation of Lemma 6.2 for $N$ difference vectors in dimension $d$, $L$ repetitions and moment order $p_0$.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a proof of DetANN.Supplement.theorem_3_2 (Feng, Indyk, STOC 2027 submission, Theorem 3.2, p.7; the construction of §6.1, p.14, and the conditional expectation of Lemma 6.2). The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_DetANN_SignedBlocks

/-!
# Milestone 21 (`DetANN.Supplement.theorem_3_2`): the sign layout and the cost of `EVAL`

`SignsAt mem L k ξ` says that the sign `signOf (ξ ℓ r) ∈ {±1}` is stored in the real cell
`-2^k - 1 - (ℓ·2^k + r)`, the layout written by the construction program `pre` and read by the
evaluation program `ev`. `evalB N d L p₀` is the step bound of one call of the subroutine `EVAL` of
`pre` (the conditional expectation of Lemma 6.2) for `N` difference vectors, dimension `d`, `L`
repetitions and moment order `p₀`.
-/

namespace DetANN.Supplement.Thm32

open DetANN

/-- The signs `ξ` are stored at the real cells `-2^k - 1 - (ℓ·2^k + r)`. -/
def SignsAt (mem : ℤ → ℝ) (L k : ℕ) (ξ : Fin L → Fin (2 ^ k) → Bool) : Prop :=
  ∀ (ℓ : Fin L) (r : Fin (2 ^ k)), mem (-(2 ^ k : ℤ) - 1 - ((ℓ : ℤ) * 2 ^ k + r)) = signOf (ξ ℓ r)

/-- The step bound of one call of `EVAL`. -/
def evalB (N d L p₀ : ℕ) : ℕ := 100 * (N + 1) * (d + 1) * (L + 1) * (d + 4 * p₀ + 3) ^ 3

end DetANN.Supplement.Thm32


