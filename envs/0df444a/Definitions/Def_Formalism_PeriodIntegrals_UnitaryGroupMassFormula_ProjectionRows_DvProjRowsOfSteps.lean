-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_DvProjRowsOfSteps
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_DvProjRowsOfSteps
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:00:33.157198+00:00
-- url     : https://prove2.me/theorems/fc05a104-d9ff-4d8e-83d7-05740661f6a0
-- title:
--   Dv Proj Rows Of Steps
-- statement:
--   Definitions and structural lemmas for Dv Proj Rows Of Steps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/DvProjRowsOfSteps.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Development
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_DvRows_h_smul_left
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
namespace PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
variable {K : Type} [Field K] [NumberField K] [StarRing K]
lemma star_mem_range (c : 𝓞 K) : star (algebraMap (𝓞 K) K c) ∈ Set.range (algebraMap (𝓞 K) K) := by
  have hc : IsIntegral ℤ (algebraMap (𝓞 K) K c) := c.2
  have : IsIntegral ℤ ((starRingEnd K) (algebraMap (𝓞 K) K c)) := hc.map (starRingEnd K).toIntAlgHom
  exact ⟨⟨_, this⟩, rfl⟩
def lamSub (A : HLat K) (e : Module.End K A.V) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K)
    (U : Submodule K A.V) : Submodule (𝓞 K) A.V where
  carrier := {y | LamStar A e h U y}
  add_mem' := by
    rintro x y ⟨hx1, hx2, hx3⟩ ⟨hy1, hy2, hy3⟩
    refine ⟨Submodule.add_mem _ hx1 hy1, fun u hu => ?_, fun m hm => ?_⟩
    · rw [map_add, LinearMap.add_apply, hx2 u hu, hy2 u hu, add_zero]
    · rw [map_add, LinearMap.add_apply]
      obtain ⟨a, ha⟩ := hx3 m hm
      obtain ⟨b, hb⟩ := hy3 m hm
      exact ⟨a + b, by rw [map_add, ha, hb]⟩
  zero_mem' := by
    refine ⟨Submodule.zero_mem _, fun u _ => by simp, fun m _ => ⟨0, by simp⟩⟩
  smul_mem' := by
    rintro c y ⟨hy1, hy2, hy3⟩
    refine ⟨?_, fun u hu => ?_, fun m hm => ?_⟩
    · exact Submodule.smul_of_tower_mem _ c hy1
    · rw [h_smul_left, hy2 u hu, mul_zero]
    · rw [h_smul_left]
      obtain ⟨a, ha⟩ := hy3 m hm
      obtain ⟨s, hs⟩ := star_mem_range c
      exact ⟨s * a, by rw [map_mul, ha, hs]⟩
def DegDual : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K] [IsGalois ℚ K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K),
    StarIsConj K → IsProj A e n → IsHermE A e h → IsCMFormE A e h →
    ∀ U : Submodule K A.V, U ≤ LinearMap.range e →
      degL A (cutE A e A.L ⊓ U.restrictScalars (𝓞 K)) - degL A (cutE A e A.L) =
        degL A (lamSub A e h U)
def DegDualBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K] [IsGalois ℚ K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K),
    StarIsConj K → IsProj A e n → IsHermE A e h → IsCMFormE A e h →
    ∀ U : Submodule K A.V, U ≤ LinearMap.range e →
    ∀ γ : HeightOneSpectrum (𝓞 K) → ℤ, (∀ w, IsValG A e h U w (γ w)) →
      degL A (lamSub A e h U) ≤ ∑ᶠ w, lw K w * (γ w : ℝ)
end PI.DvRows


