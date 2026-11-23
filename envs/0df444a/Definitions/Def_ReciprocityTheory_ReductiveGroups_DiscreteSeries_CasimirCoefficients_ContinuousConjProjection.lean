-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousConjProjection
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousConjProjection
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:13:31.727339+00:00
-- url     : https://prove2.me/theorems/97dbcd07-e21f-4d54-b90c-5981adbdd6e4
-- title:
--   Continuous Conj Projection
-- statement:
--   Definitions and structural lemmas for Continuous Conj Projection, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ContinuousConjProjection.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Jm_mul_self

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
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
lemma kType_op_mul (T : KType ε Λ) (a b : KG ε) : T.op (a * b) = T.op a * T.op b := by
  unfold KType.op
  rw [map_mul]
  rfl
lemma kType_op_one (T : KType ε Λ) : T.op 1 = 1 := by
  unfold KType.op
  rw [map_one]
  rfl
lemma kType_op_mul_inv (T : KType ε Λ) (a : KG ε) : T.op a * T.op a⁻¹ = 1 := by
  rw [← kType_op_mul, mul_inv_cancel, kType_op_one]
lemma kType_op_inv_mul (T : KType ε Λ) (a : KG ε) : T.op a⁻¹ * T.op a = 1 := by
  rw [← kType_op_mul, inv_mul_cancel, kType_op_one]
def ps2E (T : KType ε Λ) (k : KG ε) : T.V ≃L[ℂ] T.V :=
  ContinuousLinearEquiv.equivOfInverse (T.op k) (T.op k⁻¹)
    (fun v => by
      have := congrArg (fun A : T.V →L[ℂ] T.V => A v) (kType_op_inv_mul T k)
      simpa using this)
    (fun v => by
      have := congrArg (fun A : T.V →L[ℂ] T.V => A v) (kType_op_mul_inv T k)
      simpa using this)
def ps2C (T : KType ε Λ) (k : KG ε) : (T.V →L[ℂ] T.V) ≃L[ℂ] (T.V →L[ℂ] T.V) :=
  (ps2E T k).arrowCongr (ps2E T k)
def ps2J (ε : Fin n → Bool) : KG ε :=
  ⟨⟨⟨Jm ε, Jm ε, Jm_mul_self ε, Jm_mul_self ε⟩, by
      show (Jm ε)ᴴ * Jm ε * Jm ε = Jm ε
      rw [Jm_conjTranspose, Jm_mul_self, Matrix.one_mul]⟩,
    by
      show Jm ε ∈ Kset ε
      refine ⟨?_, rfl⟩
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Jm_conjTranspose, Jm_mul_self]⟩
end ReciprocityTheory.ChartRestriction.DS.S7


