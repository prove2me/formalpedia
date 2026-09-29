-- Prove2me | solution 1 for AutomorphicForm.exists_forall_apply_mul_eq_of_mem_maximalCompactAway_of_flat_family
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/d464d439-485c-5376-bae0-33d584ffa277

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Analysis.Meromorphic.Order
import Theorems.Thm_AutomorphicForm_exists_maximalCompactAway_subset_of_mem_nhds_one
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_apply_mul_eq_of_mem_maximalCompactAway_of_flat_family
p2m_attr_erase "instance" "HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel Filter Topology
open scoped NNReal

open FLT.SmoothVectors

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (_hφflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          φ s k = φ s' k),
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)),
      ∀ (s : ℂ) (g k : AdelicGL2 (𝓞 F) F), k ∈ maximalCompactAway F S₀ → φ s (g * k) = φ s g := by
  intro α hα φ hφ hφK hφf hφjc hφhol hφflat

  have hv := hφf 0
  rw [isKfSmooth_iff, isSmoothVector_iff_isOpen_stabilizer] at hv
  obtain ⟨W, hWopen, hWpre⟩ := isOpen_induced_iff.mp hv
  have h1W : (1 : AdelicGL2 (𝓞 F) F) ∈ W := by
    have : (⟨1, (finiteAdelicGL2Subgroup F).one_mem⟩ : finiteAdelicGL2Subgroup F)
        ∈ (Subtype.val ⁻¹' W : Set (finiteAdelicGL2Subgroup F)) := by
      rw [hWpre]
      exact (MulAction.stabilizer (finiteAdelicGL2Subgroup F) (RightTranslationFn.mk (φ 0))).one_mem
    exact this
  obtain ⟨S₀, hS₀⟩ := AutomorphicForm.exists_maximalCompactAway_subset_of_mem_nhds_one F W
    (hWopen.mem_nhds h1W)
  have hlevel0 : ∀ k ∈ maximalCompactAway F S₀, ∀ x : AdelicGL2 (𝓞 F) F, φ 0 (x * k) = φ 0 x := by
    intro k hk x
    have hkH : k ∈ finiteAdelicGL2Subgroup F := by
      rw [mem_finiteAdelicGL2Subgroup_iff]
      exact (mem_maximalCompactAway_iff.mp hk).2.1
    have hkstab : (⟨k, hkH⟩ : finiteAdelicGL2Subgroup F)
        ∈ MulAction.stabilizer (finiteAdelicGL2Subgroup F) (RightTranslationFn.mk (φ 0)) := by
      have : (⟨k, hkH⟩ : finiteAdelicGL2Subgroup F) ∈ (Subtype.val ⁻¹' W : Set (finiteAdelicGL2Subgroup F)) :=
        hS₀ hk
      rw [hWpre] at this
      exact this
    rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def] at hkstab
    have := congrArg (fun f => RightTranslationFn.toFun f x) hkstab
    simpa [RightTranslationFn.toFun_smul] using this

  refine ⟨S₀, fun s g k hk => ?_⟩
  have hkK : k ∈ adelicMaximalCompact F := maximalCompactAway_le F S₀ hk
  obtain ⟨b, kg, hb, hkgf, hkga, rfl⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F g
  have hkgK : kg ∈ adelicMaximalCompact F := mem_adelicMaximalCompact_iff.mpr ⟨hkgf, hkga⟩
  have hkgk := (adelicMaximalCompact F).mul_mem hkgK hkK
  rw [mul_assoc, hφ s b hb (kg * k), hφ s b hb kg]
  congr 1
  calc φ s (kg * k) = φ 0 (kg * k) := hφflat s 0 (kg * k) hkgk.1 hkgk.2
    _ = φ 0 kg := hlevel0 k hk kg
    _ = φ s kg := hφflat 0 s kg hkgf hkga

end S_AutomorphicForm_exists_forall_apply_mul_eq_of_mem_maximalCompactAway_of_flat_family
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_apply_mul_eq_of_mem_maximalCompactAway_of_flat_family (solution)
