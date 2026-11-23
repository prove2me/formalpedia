-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:10:59.413525+00:00
-- url     : https://prove2.me/theorems/7ccc6388-62e2-4f51-aa42-cbaab745af33
-- title:
--   Continuous On Fderiv Phi P
-- statement:
--   Definitions and structural lemmas for Continuous On Fderiv Phi P, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ContinuousOnFderivPhiP.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace Ps1
local notation "𝕄" => Fin n → Fin n → ℂ
def PhiP (μ : Fin n → ℤ) : 𝕄 → ℂ := fun y => PhiM μ y
def conjLin (A B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun H := A * H * B
  map_add' H H' := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c H := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]
def conjCLM (A B : Matrix (Fin n) (Fin n) ℂ) : 𝕄 →L[ℂ] 𝕄 :=
  LinearMap.toContinuousLinearMap (conjLin A B : 𝕄 →ₗ[ℂ] 𝕄)
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
def Uset (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {z | ∀ k : KG ε, toMK k⁻¹ * z * toMK k ∈ OmegaSet n}
def GintD (T : KType ε Λ) (μ : Fin n → ℤ) (x : Matrix (Fin n) (Fin n) ℂ) (k : KG ε) :
    𝕄 →L[ℂ] (T.V →L[ℂ] T.V) :=
  fderiv ℂ (fun y : 𝕄 => Gint T μ y k) x
end Ps1
end ReciprocityTheory.ChartRestriction.DS.S7


