-- Prove2me | Definitions.Def_ChapterOperatorSeriesEsa
-- name    : ChapterOperatorSeriesEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-05T13:10:02.184154+00:00
-- url     : https://prove2.me/theorems/54cfc00c-0262-4158-a200-3aecd3c57e89
-- title:
--   ChapterOperatorSeriesEsa
-- statement:
--   ChapterOperatorSeriesEsa

import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Mathlib


/-!
# Summable series of symmetric operators, and the Faris–Lavine bounds

The Faris–Lavine (Nelson commutator) route to essential self-adjointness needs two
inequalities relative to a positive comparison operator `N`: a relative bound
`‖H x‖ ≤ A‖N x‖` and a commutator-form bound `|⟪x, i[H, N]x⟫| ≤ B⟪x, N x⟫`.  Both are
*additive*, and both survive an **infinite sum** of operators as soon as the two
constants are summable.  That is exactly what a second-quantized Hamiltonian with
infinitely many modes is: a sum over the modes (or over pairs of modes) of elementary
operators, each individually controlled by the number operator.

This module isolates that step, once and for all, on `ℓ²(ι)` with the multiplication
comparison operator `N = diagMax c` of
`BookProof.ChapterNavierStokesIkebeKato`.

## What is proved

* `commForm_eq_neg_two_im` — the commutator form is `-2 Im⟪H x, N x⟫`; in particular it
  is additive in `H`.
* `seriesOp` — the sum `∑' k, T k` of a family of operators on the maximal domain of a
  symbol, well defined as soon as the relative bounds are summable.
* `seriesOp_symmetricOn`, `seriesOp_norm_le`, `seriesOp_commForm_le` — the three
  properties pass to the sum, with the summed constants.
* `essentiallySelfAdjointOn_finiteModes_of_bounds` — the packaging of the Faris–Lavine
  criterion in the "relative bound + commutator bound" form used here.
* `essentiallySelfAdjointOn_finiteModes_of_series` — **the instrument**: a summable
  family of symmetric operators, each relatively bounded by the comparison operator and
  with commutator form dominated by it, sums to an operator which is essentially
  self-adjoint on the finite-mode core.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.OperatorSeries

open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat

noncomputable section

/-! ## 1. The commutator form as an imaginary part -/

section CommForm

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}





end CommForm

/-! ## 2. The series of operators -/

section Series

variable {ι κ : Type*} {c : ι → ℝ}

variable (T : κ → (maxDom c →ₗ[ℂ] L2I ι)) (a : κ → ℝ)

/-- Summability of the family `k ↦ T k x`, from the summable relative bounds. -/
theorem summable_apply
    (hnorm : ∀ (k : κ) (x : maxDom c), ‖(T k x : L2I ι)‖ ≤ a k * ‖(diagMax c x : L2I ι)‖)
    (ha : Summable a) (x : maxDom c) : Summable fun k => (T k x : L2I ι) := by
  refine Summable.of_norm_bounded (g := fun k => a k * ‖(diagMax c x : L2I ι)‖) ?_ ?_
  · exact ha.mul_right _
  · intro k; exact hnorm k x

/-- **The sum of a summable family of operators.** -/
def seriesOp
    (hnorm : ∀ (k : κ) (x : maxDom c), ‖(T k x : L2I ι)‖ ≤ a k * ‖(diagMax c x : L2I ι)‖)
    (ha : Summable a) : maxDom c →ₗ[ℂ] L2I ι where
  toFun x := ∑' k, (T k x : L2I ι)
  map_add' x y := by
    have hx := summable_apply T a hnorm ha x
    have hy := summable_apply T a hnorm ha y
    have hxy : ∀ k, (T k (x + y) : L2I ι) = (T k x : L2I ι) + (T k y : L2I ι) := by
      intro k; rw [map_add]
    simp only [hxy]
    exact Summable.tsum_add hx hy
  map_smul' r x := by
    have hx := summable_apply T a hnorm ha x
    have hxy : ∀ k, (T k (r • x) : L2I ι) = r • (T k x : L2I ι) := by
      intro k; rw [map_smul]
    simp only [hxy, RingHom.id_apply]
    exact tsum_const_smul'' r

variable {T} {a}











end Series

/-! ## 3. The Faris–Lavine payoff -/

section Payoff

variable {ι : Type*} {c : ι → ℝ}





end Payoff

end

end BookProof.OperatorSeries


