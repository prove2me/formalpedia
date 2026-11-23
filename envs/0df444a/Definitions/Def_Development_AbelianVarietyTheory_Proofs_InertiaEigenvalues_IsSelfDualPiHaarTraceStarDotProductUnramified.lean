-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSelfDualPiHaarTraceStarDotProductUnramified
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSelfDualPiHaarTraceStarDotProductUnramified
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:54:42.939379+00:00
-- url     : https://prove2.me/theorems/b3ecf802-4cda-4276-83ab-53092d7d95ff
-- title:
--   Is Self Dual Pi Haar Trace Star Dot Product Unramified
-- statement:
--   Definitions and structural lemmas for Is Self Dual Pi Haar Trace Star Dot Product Unramified, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsSelfDualPiHaarTraceStarDotProductUnramified.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
namespace GlobalTheory.JR.PiSelfDual
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E]
theorem star_smul_F {r : ℕ} (a : F) (c : Fin r → E) : star (a • c) = a • star c := by
  funext i
  show star (a • c i) = a • star (c i)
  rw [Algebra.smul_def, Algebra.smul_def, star_mul, Unram.star_fix (E := E) a, mul_comm]
def trForm (r : ℕ) : LinearMap.BilinForm F (Fin r → E) :=
  LinearMap.mk₂ F (fun c b => Algebra.trace F E (star c ⬝ᵥ b))
    (fun c c' b => by simp [star_add, add_dotProduct])
    (fun a c b => by rw [star_smul_F, smul_dotProduct, LinearMap.map_smul])
    (fun c b b' => by simp [dotProduct_add])
    (fun a c b => by rw [dotProduct_smul, LinearMap.map_smul])
def intLat (r : ℕ) : AddSubgroup (Fin r → E) :=
  haveI : IsUltrametricDist E := Unram.ultraE F
  { carrier := {b | ∀ i, ‖b i‖ ≤ 1}
    add_mem' := fun {a b} ha hb i => by
      simp only [Set.mem_setOf_eq, Pi.add_apply] at *
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (hb i))
    zero_mem' := fun i => by simp
    neg_mem' := fun {a} ha i => by simpa using ha i }
end GlobalTheory.JR.PiSelfDual


