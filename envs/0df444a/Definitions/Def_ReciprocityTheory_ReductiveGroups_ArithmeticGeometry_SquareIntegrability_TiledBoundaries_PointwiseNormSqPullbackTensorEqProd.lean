-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_PointwiseNormSqPullbackTensorEqProd
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_PointwiseNormSqPullbackTensorEqProd
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T14:40:15.219987+00:00
-- url     : https://prove2.me/theorems/f247206c-f0f5-4062-b540-ca2f0d01b146
-- title:
--   Pointwise Norm Sq Pullback Tensor Eq Prod
-- statement:
--   Definitions and structural lemmas for Pointwise Norm Sq Pullback Tensor Eq Prod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TiledBoundaries/PointwiseNormSqPullbackTensorEqProd.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_DimStatement
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory Complex
noncomputable section
def StepT : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (X : PT E) (n : ℕ) (F : Type) [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (g : (Fin n → Vsp X.dim) → F), Continuous g →
    (∀ γ : Fin n → Vsp X.dim, (∀ k, γ k ∈ X.L) → ∀ v, g (v + γ) = g v) →
    ∀ a, (⨍ v in X.fd n, g (v - a)) = ⨍ v in X.fd n, g v
def StepI : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (X : PT E) (n : ℕ) (g : (Fin n → Vsp X.dim) → ℂ),
    Continuous g → IntegrableOn g (X.fd n)
def StepF : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (X : PT E) (n : ℕ) (f : Vsp X.dim → ℝ), Continuous f →
    (⨍ v in X.fd n, ∏ k, f (v k)) = (⨍ w in ZSpan.fundamentalDomain X.b, f w) ^ n
def StepP : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (X : PT E) (q : ℕ) (π : Vsp X.dim →ₗ[ℂ] Vsp X.dim),
    1 ≤ q → IsPi X q π → ∀ g : Vsp X.dim → ℝ, Continuous g →
    (∀ γ ∈ X.L, ∀ v, g (v + γ) = g v) →
    (⨍ w in ZSpan.fundamentalDomain X.b, g (π w)) = ⨍ w in ZSpan.fundamentalDomain X.b, g w
def StepPos : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (X : PT E) (q n : ℕ) (F : (Fin n → Vsp X.dim) → ℂ),
    F ∈ X.Sec q n → F ≠ 0 → 0 < X.l2 q F
def StepDual : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (X : PT E) (x : Vsp X.dim),
    (∀ y ∈ X.L, ∃ m : ℤ, (Hf x y).im = m) → x ∈ X.L
def StepK : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (X : PT E) (q n : ℕ) (π : Vsp X.dim →ₗ[ℂ] Vsp X.dim),
    1 ≤ q → IsPi X q π → ∀ K, IsReps X q n π K → q ^ (Fintype.card (Idx X.dim) * n) ≤ K.card
def StepD : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (X : PT E) (q n : ℕ), 1 ≤ q →
    FiniteDimensional ℂ (X.Sec q n) ∧
      Module.finrank ℂ (X.Sec q n) ≤ q ^ (Fintype.card (Idx X.dim) * n)
section Elem
variable {E : Type} [Field E] [NumberField E]
end Elem
end
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries


