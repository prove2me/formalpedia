-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:39:57.787796+00:00
-- url     : https://prove2.me/theorems/7b14910e-1818-490d-b23f-766e8297a449
-- title:
--   Level Sizes Joint Mean
-- statement:
--   Definitions and structural lemmas for Level Sizes Joint Mean, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelSizesJointMean.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.Jx2
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped nonZeroDivisors ComplexConjugate
section Euclid
open NumberField.mixedEmbedding MeasureTheory
open scoped Classical
noncomputable section
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
theorem isC (w : InfinitePlace E) : w.IsComplex := IsTotallyComplex.isComplex w
local instance isEmptyReal : IsEmpty {w : InfinitePlace E // w.IsReal} :=
  ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.2 (isC E w.1)) w.2⟩
variable {E} in
theorem mext {y z : euclidean.mixedSpace E} (h : ∀ w, y.snd w = z.snd w) : y = z := by
  have h1 : y.fst = z.fst := by
    ext w
    exact isEmptyElim w
  have h2 : y.snd = z.snd := by
    ext w
    exact h w
  first
  | exact WithLp.prod_ext h1 h2
  | exact WithLp.ofLp_injective 2 (Prod.ext h1 h2)
  | exact WithLp.ofLp_injective (Prod.ext h1 h2)
  | (apply WithLp.prod_ext <;> assumption)
  | (rcases y with ⟨y⟩; rcases z with ⟨z⟩; exact congrArg (WithLp.toLp 2) (Prod.ext h1 h2))
def phiL : CV E ≃ₗ[ℝ] euclidean.mixedSpace E where
  toFun x := WithLp.toLp 2 (0, WithLp.toLp 2 (fun w : {w : InfinitePlace E // w.IsComplex} => x w.1))
  invFun y := WithLp.toLp 2 (fun w : InfinitePlace E => y.snd ⟨w, isC E w⟩)
  map_add' x y := mext fun w => by simp
  map_smul' c x := mext fun w => by simp
  left_inv x := by ext w; simp
  right_inv y := mext fun w => by simp
theorem phi_norm (x : CV E) : ‖phiL E x‖ = ‖x‖ := by
  have key : ‖phiL E x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq (phiL E x).snd,
      EuclideanSpace.norm_sq_eq x]
    have hf : (phiL E x).fst = 0 := rfl
    rw [hf, norm_zero, zero_pow two_ne_zero, zero_add]
    exact Fintype.sum_equiv (Equiv.subtypeUnivEquiv (isC E)) _ _ (fun w => rfl)
  rw [← Real.sqrt_sq (norm_nonneg (phiL E x)), key, Real.sqrt_sq (norm_nonneg x)]
def phi : CV E ≃ₗᵢ[ℝ] euclidean.mixedSpace E := ⟨phiL E, phi_norm E⟩
def ee : CV E ≃L[ℝ] mixedSpace E := (phi E).toContinuousLinearEquiv.trans (euclidean.toMixed E)
end
end Euclid
end Formalism.FourierDecayAlt.P.Jx2
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


