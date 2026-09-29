-- Prove2me | solution 1 for AutomorphicForm.exists_finset_convOp_eq_of_le_isotypicCuspSubmodule_inf_archCutSubmodule_of_isFundamentalDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/057250d2-2e23-55e3-bf05-890e1b5ad463

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_isotypicCuspSubmodule_inf_archCutSubmodule_le_of_isFundamentalDomain_of_pos
import Theorems.Thm_AutomorphicForm_exists_finset_convOp_eq_of_ne_zero_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule
import Theorems.Thm_AutomorphicForm_exists_finset_convOp_convOp_eq_sum_on_isotypicCuspSubmodule_inf_archCutSubmodule
import Theorems.Thm_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType
import Theorems.Thm_AutomorphicForm_finiteDimensional_isotypicCuspSubmodule_inf_archCutSubmodule
import Theorems.Thm_AutomorphicForm_SiegelCovering_exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet
import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Data.Nat.PrimeFin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_finset_convOp_eq_of_le_isotypicCuspSubmodule_inf_archCutSubmodule_of_isFundamentalDomain
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalConstituent.rightRegular_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero"
p2m_attr_erase "simp" "LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.iotaZsqrtdNegTwo_apply LanglandsTunnell.TateLocal.conductorExponentAt_one HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicHaar
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace EndomorphismSpan

section Burnside

variable {k A V : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [IsSimpleModule A V] [FiniteDimensional k V]

private def endLinearOverEnd (f : Module.End k V) : V →ₗ[Module.End A V] V where
  toFun := f
  map_add' := f.map_add
  map_smul' := by
    intro g v
    obtain ⟨c, rfl⟩ :=
      (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := A) (V := V) k).2 g
    simp only [RingHom.id_apply, Module.End.smul_def, Module.algebraMap_end_apply]
    exact f.map_smul c v

private theorem burnside_exists_smul_eq (f : Module.End k V) : ∃ a : A, ∀ v : V, a • v = f v := by
  haveI : Module.Finite (Module.End A V) V := Module.Finite.of_restrictScalars_finite k _ V
  obtain ⟨a, ha⟩ :=
    Module.Finite.toModuleEnd_moduleEnd_surjective (R := A) (M := V) (endLinearOverEnd (A := A) f)
  exact ⟨a, fun v => LinearMap.congr_fun ha v⟩

end Burnside

section Core

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

private def restrictOp (W : Submodule ℂ M) (T : M → M) (hmaps : ∀ u ∈ W, T u ∈ W)
    (hadd : ∀ u ∈ W, ∀ w ∈ W, T (u + w) = T u + T w)
    (hsmul : ∀ (c : ℂ) (u : M), u ∈ W → T (c • u) = c • T u) : Module.End ℂ W where
  toFun u := ⟨T u, hmaps u u.2⟩
  map_add' u w := Subtype.ext (hadd u u.2 w w.2)
  map_smul' c u := Subtype.ext (hsmul c u u.2)

@[scoped simp] private theorem restrictOp_apply_coe (W : Submodule ℂ M) (T : M → M) (hmaps : ∀ u ∈ W, T u ∈ W)
    (hadd : ∀ u ∈ W, ∀ w ∈ W, T (u + w) = T u + T w)
    (hsmul : ∀ (c : ℂ) (u : M), u ∈ W → T (c • u) = c • T u) (u : W) :
    ((restrictOp W T hmaps hadd hsmul u : W) : M) = T u :=
  rfl

private theorem core {ι : Type*} (P : ι → Prop) (op : ι → M → M) (W : Submodule ℂ M) [FiniteDimensional ℂ W]
    (hmaps : ∀ i, P i → ∀ u ∈ W, op i u ∈ W)
    (hadd : ∀ i, P i → ∀ u ∈ W, ∀ w ∈ W, op i (u + w) = op i u + op i w)
    (hsmul : ∀ i, P i → ∀ (c : ℂ) (u : M), u ∈ W → op i (c • u) = c • op i u)
    (hcomp : ∀ i j, P i → P j → ∃ (s : Finset ι) (a : ι → ℂ), (∀ k ∈ s, P k) ∧
      ∀ w ∈ W, op i (op j w) = ∑ k ∈ s, a k • op k w)
    (hcyc : ∀ w ∈ W, w ≠ 0 → ∀ w' ∈ W, ∃ (s : Finset ι) (a : ι → ℂ), (∀ k ∈ s, P k) ∧
      w' = ∑ k ∈ s, a k • op k w)
    (V : Submodule ℂ M) (hV : V ≤ W) (f : Module.End ℂ V) :
    ∃ (s : Finset ι) (c : ι → ℂ), (∀ k ∈ s, P k) ∧
      ∀ v : V, ((f v : V) : M) = ∑ k ∈ s, c k • op k (v : M) := by
  classical

  let ρ : {i // P i} → Module.End ℂ W :=
    fun i => restrictOp W (op i) (hmaps i i.2) (hadd i i.2) (hsmul i i.2)
  have hρ : ∀ (i : {i // P i}) (u : W), ((ρ i u : W) : M) = op i u := fun _ _ => rfl
  let Sp : Submodule ℂ (Module.End ℂ W) := Submodule.span ℂ (Set.range ρ)

  have sumOp : ∀ (s : Finset ι) (a : ι → ℂ) (hs : ∀ k ∈ s, P k),
      ∃ T ∈ Sp, ∀ u : W, ((T u : W) : M) = ∑ k ∈ s, a k • op k u := by
    intro s a hs
    refine ⟨∑ k ∈ s.attach, a k • ρ ⟨k, hs k k.2⟩, ?_, ?_⟩
    · exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · intro u
      rw [LinearMap.sum_apply, Submodule.coe_sum]
      simp only [LinearMap.smul_apply, Submodule.coe_smul, hρ]
      exact Finset.sum_attach s (fun k => a k • op k (u : M))

  have irr : ∀ w : W, w ≠ 0 → ∀ w' : W, ∃ T ∈ Sp, T w = w' := by
    intro w hw w'
    have hw0 : (w : M) ≠ 0 := fun h => hw (Subtype.ext h)
    obtain ⟨s, a, hs, heq⟩ := hcyc w w.2 hw0 w' w'.2
    obtain ⟨T, hT, hTu⟩ := sumOp s a hs
    exact ⟨T, hT, Subtype.ext ((hTu w).trans heq.symm)⟩

  have mulGen : ∀ i j : {i // P i}, ρ i * ρ j ∈ Sp := by
    intro i j
    obtain ⟨s, a, hs, heq⟩ := hcomp i j i.2 j.2
    obtain ⟨T, hT, hTu⟩ := sumOp s a hs
    have hprod : ρ i * ρ j = T := by
      refine LinearMap.ext fun u => Subtype.ext ?_
      rw [hTu u]
      exact heq u u.2
    rw [hprod]
    exact hT
  have mulSp : ∀ S ∈ Sp, ∀ T ∈ Sp, S * T ∈ Sp := by
    intro S hS T hT
    induction hS using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      induction hT using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        exact mulGen i j
      | zero =>
        rw [mul_zero]
        exact Sp.zero_mem
      | add y z _ _ hy hz =>
        rw [mul_add]
        exact Sp.add_mem hy hz
      | smul c y _ hy =>
        rw [mul_smul_comm]
        exact Sp.smul_mem c hy
    | zero =>
      rw [zero_mul]
      exact Sp.zero_mem
    | add x y _ _ hx hy =>
      rw [add_mul]
      exact Sp.add_mem hx hy
    | smul c x _ hx =>
      rw [smul_mul_assoc]
      exact Sp.smul_mem c hx

  let A : Subalgebra ℂ (Module.End ℂ W) := Algebra.adjoin ℂ (Set.range ρ)
  have hSpA : Sp ≤ Subalgebra.toSubmodule A := Submodule.span_le.mpr Algebra.subset_adjoin
  have hA : ∀ x ∈ A, ∃ (c : ℂ), ∃ T ∈ Sp, x = c • (1 : Module.End ℂ W) + T := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      exact ⟨0, x, Submodule.subset_span hx, by rw [zero_smul, zero_add]⟩
    | algebraMap r =>
      exact ⟨r, 0, Sp.zero_mem, by rw [Algebra.algebraMap_eq_smul_one, add_zero]⟩
    | add x y _ _ hx hy =>
      obtain ⟨c₁, T₁, hT₁, rfl⟩ := hx
      obtain ⟨c₂, T₂, hT₂, rfl⟩ := hy
      exact ⟨c₁ + c₂, T₁ + T₂, Sp.add_mem hT₁ hT₂, by rw [add_smul]; abel⟩
    | mul x y _ _ hx hy =>
      obtain ⟨c₁, T₁, hT₁, rfl⟩ := hx
      obtain ⟨c₂, T₂, hT₂, rfl⟩ := hy
      refine ⟨c₁ * c₂, c₁ • T₂ + c₂ • T₁ + T₁ * T₂,
        Sp.add_mem (Sp.add_mem (Sp.smul_mem _ hT₂) (Sp.smul_mem _ hT₁)) (mulSp _ hT₁ _ hT₂), ?_⟩
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      module

  rcases subsingleton_or_nontrivial W with hW | hW
  · refine ⟨∅, fun _ => 0, fun k hk => by simp at hk, fun v => ?_⟩
    have hv : (⟨(v : M), hV v.2⟩ : W) = 0 := Subsingleton.elim _ _
    have hv0 : (v : M) = 0 := congrArg Subtype.val hv
    have hvz : v = 0 := Subtype.ext hv0
    rw [hvz, map_zero, Finset.sum_empty]
    rfl

  haveI : IsSimpleModule A W := by
    rw [isSimpleModule_iff_toSpanSingleton_surjective]
    refine ⟨hW, fun w hw w' => ?_⟩
    obtain ⟨T, hT, hTw⟩ := irr w hw w'
    exact ⟨⟨T, hSpA hT⟩, hTw⟩

  haveI : IsScalarTower ℂ A W :=
    ⟨fun c a w => show ((c • a : A) : Module.End ℂ W) w = c • ((a : Module.End ℂ W) w) by
      rw [Subalgebra.coe_smul, LinearMap.smul_apply]⟩

  have hEnd : ∀ G : Module.End ℂ W, ∃ (c : ℂ), ∃ T ∈ Sp, G = c • (1 : Module.End ℂ W) + T := by
    intro G
    obtain ⟨a, ha⟩ := burnside_exists_smul_eq (k := ℂ) (A := A) (V := W) G
    have hG : G = (a : Module.End ℂ W) := LinearMap.ext fun w => (ha w).symm
    obtain ⟨c, T, hT, h⟩ := hA a a.2
    exact ⟨c, T, hT, hG.trans h⟩

  have leftIdeal : ∀ (G : Module.End ℂ W), ∀ T ∈ Sp, G * T ∈ Sp := by
    intro G T hT
    obtain ⟨c, T', hT', rfl⟩ := hEnd G
    rw [add_mul, smul_mul_assoc, one_mul]
    exact Sp.add_mem (Sp.smul_mem c hT) (mulSp _ hT' _ hT)
  have rightIdeal : ∀ T ∈ Sp, ∀ G : Module.End ℂ W, T * G ∈ Sp := by
    intro T hT G
    obtain ⟨c, T', hT', rfl⟩ := hEnd G
    rw [mul_add, mul_smul_comm, mul_one]
    exact Sp.add_mem (Sp.smul_mem c hT) (mulSp _ hT _ hT')

  have one_mem : (1 : Module.End ℂ W) ∈ Sp := by
    obtain ⟨w₀, hw₀⟩ := exists_ne (0 : W)
    let b := Module.finBasis ℂ W
    have h1 : (1 : Module.End ℂ W) = ∑ i, (b.coord i).smulRight (b i) := by
      refine LinearMap.ext fun w => ?_
      rw [Module.End.one_apply, LinearMap.sum_apply]
      simp only [LinearMap.smulRight_apply, Module.Basis.coord_apply]
      exact (b.sum_repr w).symm
    rw [h1]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨C, hC, hCw⟩ := irr w₀ hw₀ (b i)
    have hrank : (b.coord i).smulRight (b i) = C * (b.coord i).smulRight w₀ := by
      refine LinearMap.ext fun w => ?_
      rw [Module.End.mul_apply, LinearMap.smulRight_apply, LinearMap.smulRight_apply, map_smul, hCw]
    rw [hrank]
    exact rightIdeal C hC _
  have hSpTop : ∀ G : Module.End ℂ W, G ∈ Sp := fun G => by
    have h := leftIdeal G 1 one_mem
    rwa [mul_one] at h

  let p : Submodule ℂ W := Submodule.comap W.subtype V
  let e : p ≃ₗ[ℂ] V := Submodule.comapSubtypeEquivOfLe hV
  let g : p →ₗ[ℂ] W := (Submodule.inclusion hV) ∘ₗ f ∘ₗ e.toLinearMap
  obtain ⟨F, hF⟩ := LinearMap.exists_extend g
  have hFv : ∀ v : V, ((F ⟨(v : M), hV v.2⟩ : W) : M) = ((f v : V) : M) := by
    intro v
    have hmem : (⟨(v : M), hV v.2⟩ : W) ∈ p := v.2
    have h1 : F ⟨(v : M), hV v.2⟩ = g ⟨⟨(v : M), hV v.2⟩, hmem⟩ :=
      LinearMap.congr_fun hF ⟨⟨(v : M), hV v.2⟩, hmem⟩
    have h2 : e ⟨⟨(v : M), hV v.2⟩, hmem⟩ = v := Subtype.ext rfl
    rw [h1]
    show ((Submodule.inclusion hV (f (e ⟨⟨(v : M), hV v.2⟩, hmem⟩)) : W) : M) = _
    rw [h2, Submodule.coe_inclusion]
  obtain ⟨cf, hcf⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp (hSpTop F)
  refine ⟨cf.support.image Subtype.val, fun k => if h : P k then cf ⟨k, h⟩ else 0, ?_, fun v => ?_⟩
  · intro k hk
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
    exact i.2
  · rw [← hFv v, ← hcf, Finset.sum_image (fun i _ j _ h => Subtype.ext h), Finsupp.sum,
      LinearMap.sum_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [LinearMap.smul_apply, Submodule.coe_smul, hρ, dif_pos i.2, Subtype.coe_eta]

end Core

end EndomorphismSpan
p2m_reactivate "P2MW.S_AutomorphicForm_exists_finset_convOp_eq_of_le_isotypicCuspSubmodule_inf_archCutSubmodule_of_isFundamentalDomain.EndomorphismSpan"

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsUnitFactorizableAboveOfType IsIsotypicCuspFormAt isotypicCuspSubmodule convOp convOp_smul convOp_add ArchTypeFamily archCutSubmodule continuous_of_mem_isotypicCuspSubmodule_inf CarrierPins productionPinsOf AdelicGL2 globalPoints finiteAdelicGL2Subgroup HeckeEigensystem isotypicCuspSubmodule_inf_archCutSubmodule_le_of_isFundamentalDomain_of_pos exists_finset_convOp_eq_of_ne_zero_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule exists_finset_convOp_convOp_eq_sum_on_isotypicCuspSubmodule_inf_archCutSubmodule convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType finiteDimensional_isotypicCuspSubmodule_inf_archCutSubmodule SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet"
namespace CuspLevelGlue
p2m_open "AutomorphicForm"

private theorem infinite_heightOneSpectrum (K : Type) [Field K] [NumberField K] :
    Infinite (HeightOneSpectrum (𝓞 K)) := by
  classical
  have key : ∀ q : Nat.Primes, ∃ P : HeightOneSpectrum (𝓞 K),
      P.asIdeal.comap (algebraMap ℤ (𝓞 K)) = Ideal.span {((q : ℕ) : ℤ)} := by
    intro q
    have hq0 : ((q : ℕ) : ℤ) ≠ 0 := by exact_mod_cast q.2.ne_zero
    haveI : (Ideal.span {((q : ℕ) : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime hq0).mpr (Nat.prime_iff_prime_int.mp q.2)
    have hinj : Function.Injective (algebraMap ℤ (𝓞 K)) := (algebraMap ℤ (𝓞 K)).injective_int
    have hker : RingHom.ker (algebraMap ℤ (𝓞 K)) ≤ Ideal.span {((q : ℕ) : ℤ)} := by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
      exact bot_le
    obtain ⟨Q, hQ, hQc⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (Ideal.span {((q : ℕ) : ℤ)}) hker
    refine ⟨⟨Q, hQ, ?_⟩, hQc⟩
    rintro rfl
    rw [Ideal.comap_bot_of_injective (f := algebraMap ℤ (𝓞 K)) hinj] at hQc
    exact hq0 (Ideal.span_singleton_eq_bot.mp hQc.symm)
  choose P hP using key
  refine Infinite.of_injective P fun q q' h => ?_
  have hspan : Ideal.span {((q : ℕ) : ℤ)} = Ideal.span {((q' : ℕ) : ℤ)} := by rw [← hP q, ← hP q', h]
  have hdvd : ((q' : ℕ) : ℤ) ∣ ((q : ℕ) : ℤ) :=
    Ideal.mem_span_singleton.mp (hspan ▸ Ideal.mem_span_singleton_self _)
  have hdvd' : (q' : ℕ) ∣ (q : ℕ) := by exact_mod_cast hdvd
  exact Subtype.ext (((Nat.prime_dvd_prime_iff_eq q'.2 q.2).mp hdvd').symm)

private theorem exists_finset_fibre (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (SK : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ F : Finset (HeightOneSpectrum (𝓞 L)),
      ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∈ SK → w ∈ F := by
  classical
  have hfin : ∀ p : HeightOneSpectrum (𝓞 K),
      Set.Finite {w : HeightOneSpectrum (𝓞 L) | HeightOneSpectrum.under (𝓞 K) w = p} := by
    intro p
    haveI := p.isMaximal
    have hp0 : p.asIdeal ≠ ⊥ := p.ne_bot
    have hsub : {w : HeightOneSpectrum (𝓞 L) | HeightOneSpectrum.under (𝓞 K) w = p} ⊆
        {w : HeightOneSpectrum (𝓞 L) | w.asIdeal ∣ Ideal.map (algebraMap (𝓞 K) (𝓞 L)) p.asIdeal} := by
      intro w hw
      have hle : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) p.asIdeal ≤ w.asIdeal := by
        have hp : p.asIdeal = w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) := by
          rw [← hw]
          rfl
        rw [hp]
        exact Ideal.map_comap_le
      exact Ideal.dvd_iff_le.mpr hle
    refine Set.Finite.subset ?_ hsub
    haveI : Finite
        ({w : HeightOneSpectrum (𝓞 L) | w.asIdeal ∣ Ideal.map (algebraMap (𝓞 K) (𝓞 L)) p.asIdeal} :
          Set (HeightOneSpectrum (𝓞 L))) :=
      Finite.of_equiv _ (HeightOneSpectrum.equivPrimesOver (𝓞 L) hp0).symm
    exact Set.toFinite _
  refine ⟨SK.biUnion fun p => (hfin p).toFinset, fun w hw => ?_⟩
  exact Finset.mem_biUnion.mpr ⟨_, hw, (hfin _).mem_toFinset.mpr rfl⟩

private theorem isotypicCuspSubmodule_mono (F : Type) [Field F] [NumberField F] {pins : CarrierPins F}
    {ξ : pins.Z →* ℂˣ} {N : Ideal (𝓞 F)} {S S' : Finset (HeightOneSpectrum (𝓞 F))} (h : S ⊆ S')
    {Φ : HeckeEigensystem F ℂ} :
    isotypicCuspSubmodule F pins ξ N S Φ ≤ isotypicCuspSubmodule F pins ξ N S' Φ :=
  Submodule.span_mono fun φ (hφ : IsIsotypicCuspFormAt F pins ξ N S Φ φ) =>
    (⟨hφ.smoothCusp, hφ.continuous, hφ.level_invariant,
      fun v hv => hφ.hecke_eigen v fun hvS => hv (h hvS),
      fun v hv => hφ.central_eigen v fun hvS => hv (h hvS)⟩ :
      IsIsotypicCuspFormAt F pins ξ N S' Φ φ)

end AutomorphicForm.CuspLevelGlue
p2m_reactivate "P2MW.S_AutomorphicForm_exists_finset_convOp_eq_of_le_isotypicCuspSubmodule_inf_archCutSubmodule_of_isFundamentalDomain.EndomorphismSpan"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_finset_convOp_eq_of_le_isotypicCuspSubmodule_inf_archCutSubmodule_of_isFundamentalDomain.EndomorphismSpan"

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_finset_convOp_eq_of_le_isotypicCuspSubmodule_inf_archCutSubmodule_of_isFundamentalDomain.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (S : Set (AdelicGL2 (𝓞 L) L))
    (hSs : S ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hS : IsFundamentalDomain (globalPoints (𝓞 L) L).range S
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (productionPinsOf L S
        (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
        (adelicBox L)).Z →* ℂˣ)
    (NK : Ideal (𝓞 K)) (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    (Ψ : HeckeEigensystem L ℂ) (tys : ArchTypeFamily L)
    (V : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ))
    (hV : V ≤ isotypicCuspSubmodule L
          (productionPinsOf L S
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) ξ (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ
        ⊓ archCutSubmodule L tys)
    (f : Module.End ℂ V) :
    ∃ (s : Finset (AdelicGL2 (𝓞 L) L → ℂ)) (c : (AdelicGL2 (𝓞 L) L → ℂ) → ℂ),
      (∀ φ ∈ s, IsUnitFactorizableAboveOfType K L tys
          (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK φ ∧
        Continuous φ ∧ HasCompactSupport φ) ∧
      ∀ v : V, ((f v : V) : AdelicGL2 (𝓞 L) L → ℂ) = ∑ φ ∈ s, c φ • convOp L φ (v : AdelicGL2 (𝓞 L) L → ℂ) := by
  classical
  have _ := hSs
  haveI := CuspLevelGlue.infinite_heightOneSpectrum K

  have hNK : NK ≠ ⊥ := by
    intro h
    obtain ⟨p, hp⟩ := Infinite.exists_notMem_finset SK
    exact hp (hNS p (Ideal.dvd_iff_le.mpr (h ▸ bot_le)))
  have hNL : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK ≠ ⊥ := fun h =>
    hNK ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.algebraMap.injective K L)).mp h)

  obtain ⟨Tw, c, hc, u, hwin⟩ :=
    AutomorphicForm.SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet L
  have hd : (1 : ℝ) < 2 := by norm_num
  have hcov := hwin 1 2 two_pos hd.le

  obtain ⟨Fb, hFb⟩ := CuspLevelGlue.exists_finset_fibre K L SK
  have habove : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∈ SK → w ∈ SL ∪ Fb :=
    fun w hw => Finset.mem_union_right _ (hFb w hw)
  have hSL : SL ⊆ SL ∪ Fb := Finset.subset_union_left

  haveI hfd := AutomorphicForm.finiteDimensional_isotypicCuspSubmodule_inf_archCutSubmodule L c u 1 2 Tw hd
    hcov ξ (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) hNL (SL ∪ Fb) tys Ψ

  have hmono : isotypicCuspSubmodule L
          (productionPinsOf L S
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) ξ (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ
        ⊓ archCutSubmodule L tys
      ≤ isotypicCuspSubmodule L
          (productionPinsOf L S
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) ξ (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) (SL ∪ Fb) Ψ
        ⊓ archCutSubmodule L tys :=
    inf_le_inf_right _ (CuspLevelGlue.isotypicCuspSubmodule_mono L hSL)
  have hslab : isotypicCuspSubmodule L
          (productionPinsOf L S
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) ξ (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) (SL ∪ Fb) Ψ
        ⊓ archCutSubmodule L tys
      ≤ isotypicCuspSubmodule L
          (productionPinsOf L (⋃ x ∈ Tw, (· * x) '' centreCutSiegelSet L c u 1 2)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) ξ (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) (SL ∪ Fb) Ψ
        ⊓ archCutSubmodule L tys :=
    AutomorphicForm.isotypicCuspSubmodule_inf_archCutSubmodule_le_of_isFundamentalDomain_of_pos L α β hα hαβ S
      hS ξ (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) hNL (SL ∪ Fb) tys Ψ c u 1 2 Tw hc one_pos
  have hVW : V ≤ isotypicCuspSubmodule L
          (productionPinsOf L (⋃ x ∈ Tw, (· * x) '' centreCutSiegelSet L c u 1 2)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) ξ (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) (SL ∪ Fb) Ψ
        ⊓ archCutSubmodule L tys :=
    hV.trans (hmono.trans hslab)

  exact EndomorphismSpan.core
    (fun φ => IsUnitFactorizableAboveOfType K L tys
        (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK φ ∧
      Continuous φ ∧ HasCompactSupport φ)
    (convOp L)
    (isotypicCuspSubmodule L
          (productionPinsOf L (⋃ x ∈ Tw, (· * x) '' centreCutSiegelSet L c u 1 2)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) ξ (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) (SL ∪ Fb) Ψ
        ⊓ archCutSubmodule L tys)
    (fun φ hφ w hw =>
      AutomorphicForm.convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType K L c u
        1 2 Tw hd hc one_pos hcov ξ NK SK (SL ∪ Fb) habove hNS Ψ tys φ hφ.1 w hw)
    (fun φ hφ w hw w' hw' => convOp_add L hφ.2.1 hφ.2.2
      (continuous_of_mem_isotypicCuspSubmodule_inf L w hw) (continuous_of_mem_isotypicCuspSubmodule_inf L w' hw'))
    (fun φ _ a w _ => convOp_smul L φ a w)
    (fun φ ψ hφ hψ =>
      AutomorphicForm.exists_finset_convOp_convOp_eq_sum_on_isotypicCuspSubmodule_inf_archCutSubmodule K L c u 1
        2 Tw hd hcov ξ NK SK (SL ∪ Fb) hNS Ψ tys ψ φ hψ hφ)
    (fun w hw hw0 w' hw' =>
      AutomorphicForm.exists_finset_convOp_eq_of_ne_zero_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule K L c u
        1 2 Tw hd hcov ξ NK SK (SL ∪ Fb) hNS Ψ tys w w' hw hw0 hw')
    V hVW f

#print axioms solution

end S_AutomorphicForm_exists_finset_convOp_eq_of_le_isotypicCuspSubmodule_inf_archCutSubmodule_of_isFundamentalDomain
end P2MW
export P2MW.S_AutomorphicForm_exists_finset_convOp_eq_of_le_isotypicCuspSubmodule_inf_archCutSubmodule_of_isFundamentalDomain (solution)
