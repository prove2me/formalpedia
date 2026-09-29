-- Prove2me | solution 1 for AutomorphicForm.exists_forall_norm_apply_le_of_isInducedSection_etaFst_etaSnd_of_flat_of_isUnitaryChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/0fdc4093-4cc2-54ea-8180-90d95d716b0c

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_norm_apply_le_of_isInducedSection_etaFst_etaSnd_of_flat_of_isUnitaryChar
p2m_attr_erase "instance" "HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar AutomorphicForm
open IsDedekindDomain
open scoped NNReal

theorem solution
    (K : Type) [Field K] [NumberField K] :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φ p.1 p.2))
      (_hφflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        φ s (k : AdelicGL2 (𝓞 K) K) = φ 0 (k : AdelicGL2 (𝓞 K) K)),
    ∀ (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
      ∃ M : ℝ, ∀ σ' : ℝ, |σ'| ≤ σ₀ →
        ∀ (t : ℝ), ∀ g ∈ C, ‖φ ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ M := by
  intro αm hαm μ ν _hμ _hν φ hφ hφjc hφflat σ₀ C hC

  have key : ∀ (σ' t : ℝ) (g : AdelicGL2 (𝓞 K) K),
      ‖φ ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ = ‖φ (σ' : ℂ) g‖ := by
    intro σ' t g
    obtain ⟨b, k, hb, hk1, hk2, rfl⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq K g
    have hkK : k ∈ adelicMaximalCompact K := mem_adelicMaximalCompact_iff.mpr ⟨hk1, hk2⟩
    have hf1 : φ ((σ' : ℂ) + (t : ℂ) * Complex.I) k = φ 0 k := hφflat ((σ' : ℂ) + (t : ℂ) * Complex.I) ⟨k, hkK⟩
    have hf2 : φ (σ' : ℂ) k = φ 0 k := hφflat (σ' : ℂ) ⟨k, hkK⟩
    rw [hφ _ b hb k, hφ (σ' : ℂ) b hb k, hf1, hf2]
    simp only [norm_mul, etaFst_apply, etaSnd_apply, Units.val_mul, cpowChar_apply_val,
      Complex.norm_cpow_eq_rpow_re_of_pos (hαm _)]
    have r1 : (((σ' : ℂ) + (t : ℂ) * Complex.I) + 1 / 2).re = ((σ' : ℂ) + 1 / 2).re := by simp
    have r2 : (-(((σ' : ℂ) + (t : ℂ) * Complex.I) + 1 / 2)).re = (-((σ' : ℂ) + 1 / 2)).re := by simp
    rw [r1, r2]
  have hcont : Continuous fun p : ℝ × AdelicGL2 (𝓞 K) K => φ (p.1 : ℂ) p.2 :=
    hφjc.comp ((Complex.continuous_ofReal.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod hC).exists_bound_of_continuousOn
    (f := fun p : ℝ × AdelicGL2 (𝓞 K) K => φ (p.1 : ℂ) p.2) (s := Set.Icc (-σ₀) σ₀ ×ˢ C) hcont.continuousOn
  refine ⟨M, fun σ' hσ' t g hg => ?_⟩
  rw [key]
  exact hM (σ', g) ⟨abs_le.1 hσ', hg⟩

end S_AutomorphicForm_exists_forall_norm_apply_le_of_isInducedSection_etaFst_etaSnd_of_flat_of_isUnitaryChar
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_norm_apply_le_of_isInducedSection_etaFst_etaSnd_of_flat_of_isUnitaryChar (solution)
