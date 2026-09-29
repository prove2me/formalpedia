-- Prove2me | solution 1 for AutomorphicForm.continuous_and_hasCompactSupport_setIntegral_fundamentalDomain_conj_centralScalar_mul_of_mem_ellipticCell
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/4d03b6d5-0947-5252-84cf-3c00f80c9d9c

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_AutomorphicForm_exists_continuous_hasCompactSupport_forall_isOrbitalIntegralOn_mul_centralScalar_of_mem_ellipticCell
import Theorems.Thm_AutomorphicForm_setIntegral_fundamentalDomain_slab_eq_measureReal_mul_of_isOrbitalIntegralOn
import Theorems.Thm_MeasureTheory_exists_measurableSet_isFundamentalDomain_op_of_discreteTopology
import Theorems.Thm_AutomorphicForm_adelicKernelLocalFiniteness
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_continuous_and_hasCompactSupport_setIntegral_fundamentalDomain_conj_centralScalar_mul_of_mem_ellipticCell
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "centralizerBorel IsRegularSemisimple isRegularSemisimple_iff_ne_zero AdelicGL2 globalPoints centralScalar ellipticCell exists_continuous_hasCompactSupport_forall_isOrbitalIntegralOn_mul_centralScalar_of_mem_ellipticCell setIntegral_fundamentalDomain_slab_eq_measureReal_mul_of_isOrbitalIntegralOn adelicKernelLocalFiniteness"
namespace SlabCC
p2m_open "AutomorphicForm"

section Scalars

variable (F : Type) [Field F] [NumberField F]

theorem centralScalar_mul_comm (z : (AdeleRing (𝓞 F) F)ˣ) (g : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
    AutomorphicForm.centralScalar (𝓞 F) F z * g = g * AutomorphicForm.centralScalar (𝓞 F) F z := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  exact congrFun (congrFun (Matrix.scalar_commute (z : AdeleRing (𝓞 F) F) (fun r' => mul_comm _ r')
    (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))).eq i) j

theorem conj_mul_centralScalar (z : (AdeleRing (𝓞 F) F)ˣ) (γ x : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
    x⁻¹ * γ * (AutomorphicForm.centralScalar (𝓞 F) F z * x) =
      x⁻¹ * γ * x * AutomorphicForm.centralScalar (𝓞 F) F z := by
  rw [centralScalar_mul_comm, ← mul_assoc]

end Scalars

section Regular

variable {A : Type*} [CommRing A]

theorem entries_of_commute (g X : Matrix (Fin 2) (Fin 2) A) (h : X * g = g * X) (u : A)
    (hu : u * ((g 0 0 - g 1 1) ^ 2 + 4 * g 0 1 * g 1 0) = 1) :
    X 0 1 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * g 0 1 ∧
    X 1 0 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * g 1 0 ∧
    X 0 0 - X 1 1 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * (g 0 0 - g 1 1) := by
  have e00 := congr_fun (congr_fun h 0) 0
  have e01 := congr_fun (congr_fun h 0) 1
  have e10 := congr_fun (congr_fun h 1) 0
  have e11 := congr_fun (congr_fun h 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-(X 0 1)) * hu + (-(u * (g 0 0 - g 1 1))) * e01
  · linear_combination (-(X 1 0)) * hu + (u * (g 0 0 - g 1 1)) * e10 +
      (-(4 * u * g 1 0)) * e00
  · linear_combination (-(X 0 0 - X 1 1)) * hu + (4 * u * g 1 0) * e01

theorem mul_comm_of_mem_centralizer {γ : GL (Fin 2) A} (hγ : AutomorphicForm.IsRegularSemisimple γ)
    {s t : GL (Fin 2) A} (hs : s ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)))
    (ht : t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) : s * t = t * s := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hs ht
  obtain ⟨u, hu⟩ := IsUnit.exists_left_inv hγ
  set g : Matrix (Fin 2) (Fin 2) A := (γ : Matrix (Fin 2) (Fin 2) A) with hg
  have hu' : u * ((g 0 0 - g 1 1) ^ 2 + 4 * g 0 1 * g 1 0) = 1 := by
    rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hu
    linear_combination hu
  have hsX : (s : Matrix (Fin 2) (Fin 2) A) * g = g * s := by
    simpa [hg] using congrArg Units.val hs
  have htX : (t : Matrix (Fin 2) (Fin 2) A) * g = g * t := by
    simpa [hg] using congrArg Units.val ht
  obtain ⟨a1, a2, a3⟩ := entries_of_commute g s hsX u hu'
  obtain ⟨b1, b2, b3⟩ := entries_of_commute g t htX u hu'
  set X : Matrix (Fin 2) (Fin 2) A := (s : Matrix (Fin 2) (Fin 2) A)
  set Y : Matrix (Fin 2) (Fin 2) A := (t : Matrix (Fin 2) (Fin 2) A)
  set p := u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1))
  set q := u * (4 * g 1 0 * Y 0 1 + (g 0 0 - g 1 1) * (Y 0 0 - Y 1 1))
  apply Units.ext
  change X * Y = Y * X
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.zero_eta,
    Fin.mk_one]
  · linear_combination (Y 1 0) * a1 + (p * g 0 1) * b2 - (X 1 0) * b1 - (q * g 0 1) * a2
  · linear_combination (X 0 0 - X 1 1) * b1 + (q * g 0 1) * a3 - (Y 0 0 - Y 1 1) * a1 -
      (p * g 0 1) * b3
  · linear_combination (Y 0 0 - Y 1 1) * a2 + (p * g 1 0) * b3 - (X 0 0 - X 1 1) * b2 -
      (q * g 1 0) * a3
  · linear_combination (Y 0 1) * a2 + (p * g 1 0) * b1 - (X 0 1) * b2 - (q * g 1 0) * a1

theorem isMulRightInvariant_of_comm {G : Type*} [Group G] (T : Subgroup G) (hcomm : ∀ s t : T, s * t = t * s)
    [MeasurableSpace T] (τ : Measure T) [τ.IsMulLeftInvariant] : τ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have : (fun t : T => t * g) = fun t : T => g * t := funext fun t => hcomm t g
  rw [this]
  exact map_mul_left_eq_self τ g

theorem isRegularSemisimple_of_mem_ellipticCell {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    {γ : GL (Fin 2) F} (hγ : γ ∈ AutomorphicForm.ellipticCell F) :
    AutomorphicForm.IsRegularSemisimple γ := by
  rw [AutomorphicForm.isRegularSemisimple_iff_ne_zero]
  intro hdisc
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  apply hγ (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) F) / 2)
  rw [Polynomial.IsRoot, Matrix.charpoly_fin_two]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C]
  simp only [Matrix.trace_fin_two, Matrix.det_fin_two] at hdisc ⊢
  set s : F := ((γ : Matrix (Fin 2) (Fin 2) F) 0 0 + (γ : Matrix (Fin 2) (Fin 2) F) 1 1) / 2 with hs
  have key : (γ : Matrix (Fin 2) (Fin 2) F) 0 0 + (γ : Matrix (Fin 2) (Fin 2) F) 1 1 = 2 * s := by
    rw [hs]; field_simp
  rw [key] at hdisc ⊢
  have hP : (4 : F) * (s ^ 2 - ((γ : Matrix (Fin 2) (Fin 2) F) 0 0 * (γ : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (γ : Matrix (Fin 2) (Fin 2) F) 0 1 * (γ : Matrix (Fin 2) (Fin 2) F) 1 0)) = 0 := by
    linear_combination hdisc
  rcases mul_eq_zero.mp hP with h | h
  · exact absurd h h4
  · linear_combination (-1 : F) * h

theorem isRegularSemisimple_map {F : Type*} [Field F] {B : Type*} [CommRing B] (φ : F →+* B)
    {γ : GL (Fin 2) F} (hγ : AutomorphicForm.IsRegularSemisimple γ) :
    AutomorphicForm.IsRegularSemisimple (Matrix.GeneralLinearGroup.map φ γ) := by
  rw [AutomorphicForm.isRegularSemisimple_iff_ne_zero] at hγ
  unfold AutomorphicForm.IsRegularSemisimple
  have h : Matrix.trace ((Matrix.GeneralLinearGroup.map φ γ : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B) ^ 2 -
      4 * Matrix.det ((Matrix.GeneralLinearGroup.map φ γ : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B) =
      φ (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) F) ^ 2 - 4 * Matrix.det (γ : Matrix (Fin 2) (Fin 2) F)) := by
    simp only [Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.GeneralLinearGroup.map_apply,
      map_sub, map_pow, map_add, map_mul, map_ofNat]
  rw [h]
  exact (IsUnit.mk0 _ hγ).map φ

end Regular

section Discrete

variable (F : Type) [Field F] [NumberField F]

theorem discreteTopology_range_globalPoints :
    DiscreteTopology ((AutomorphicForm.globalPoints (𝓞 F) F).range) := by
  rw [discreteTopology_iff_isOpen_singleton]
  rintro ⟨s, hs⟩
  obtain ⟨C, hC, hCs⟩ := exists_compact_mem_nhds s
  have hfin : {γ : GL (Fin 2) F | (1 : AutomorphicForm.AdelicGL2 (𝓞 F) F)⁻¹ *
      AutomorphicForm.globalPoints (𝓞 F) F γ * 1 ∈ C}.Finite :=
    AutomorphicForm.adelicKernelLocalFiniteness F C hC 1 1
  set E : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F) :=
    (AutomorphicForm.globalPoints (𝓞 F) F '' {γ : GL (Fin 2) F |
      (1 : AutomorphicForm.AdelicGL2 (𝓞 F) F)⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * 1 ∈ C}) \ {s}
    with hE
  have hEc : IsClosed E := ((hfin.image _).subset Set.diff_subset).isClosed
  refine isOpen_induced_iff.mpr ⟨interior C \ E, isOpen_interior.sdiff hEc, ?_⟩
  ext ⟨x, hx⟩
  simp only [Set.mem_preimage, Set.mem_diff, Set.mem_singleton_iff, Subtype.mk.injEq]
  constructor
  · rintro ⟨hxC, hxE⟩
    by_contra hne
    apply hxE
    rw [hE]
    refine ⟨?_, hne⟩
    obtain ⟨γ, rfl⟩ := hx
    exact ⟨γ, by simpa using interior_subset hxC, rfl⟩
  · rintro rfl
    refine ⟨mem_interior_iff_mem_nhds.mpr hCs, ?_⟩
    rw [hE]
    exact fun h => h.2 rfl

theorem discreteTopology_subgroupOf (Γ T : Subgroup (AutomorphicForm.AdelicGL2 (𝓞 F) F))
    (hΓ : Γ ≤ (AutomorphicForm.globalPoints (𝓞 F) F).range) :
    DiscreteTopology (Γ.subgroupOf T) := by
  haveI := discreteTopology_range_globalPoints F
  refine DiscreteTopology.of_continuous_injective
    (f := fun x : Γ.subgroupOf T => (⟨((x : T) : AutomorphicForm.AdelicGL2 (𝓞 F) F),
      hΓ (Subgroup.mem_subgroupOf.mp x.2)⟩ : (AutomorphicForm.globalPoints (𝓞 F) F).range)) ?_ ?_
  · exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  · intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg Subtype.val hxy
    exact this

end Discrete

end AutomorphicForm.SlabCC

end

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open AutomorphicForm.SlabCC in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (α β : ℝ) (hα : 0 < α)
    (γ₀ : GL (Fin 2) F) (hγ₀ : γ₀ ∈ AutomorphicForm.ellipticCell F)
    (Ψ : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F))
    (hΨs : Ψ ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΨ : IsFundamentalDomain
      ((Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) F))).map (AutomorphicForm.globalPoints (𝓞 F) F)) Ψ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    Continuous (fun z : (AdeleRing (𝓞 F) F)ˣ =>
      ∫ x in Ψ, f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ₀ *
        (AutomorphicForm.centralScalar (𝓞 F) F z * x)) ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) ∧
    HasCompactSupport (fun z : (AdeleRing (𝓞 F) F)ˣ =>
      ∫ x in Ψ, f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ₀ *
        (AutomorphicForm.centralScalar (𝓞 F) F z * x)) ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) := by

  haveI : BorelSpace (AutomorphicForm.AdelicGL2 (𝓞 F) F) :=
    NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : SecondCountableTopology (AutomorphicForm.AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure :=
    NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI : SigmaCompactSpace (AutomorphicForm.AdelicGL2 (𝓞 F) F) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite (adelicGLHaar (Fin 2) (𝓞 F) F) := inferInstance
  haveI : SFinite (adelicGLHaar (Fin 2) (𝓞 F) F) := instSFiniteOfSigmaFinite

  set γA : AutomorphicForm.AdelicGL2 (𝓞 F) F := AutomorphicForm.globalPoints (𝓞 F) F γ₀ with hγA
  set T : Subgroup (AutomorphicForm.AdelicGL2 (𝓞 F) F) := Subgroup.centralizer ({γA} : Set _) with hT
  have hTc : IsClosed (T : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F)) := Set.isClosed_centralizer _
  haveI : BorelSpace T := ⟨rfl⟩
  haveI : LocallyCompactSpace T := hTc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology T :=
    (Topology.IsInducing.subtypeVal :
      Topology.IsInducing (Subtype.val : T → AutomorphicForm.AdelicGL2 (𝓞 F) F)).secondCountableTopology
  haveI : SigmaCompactSpace T := sigmaCompactSpace_of_locallyCompact_secondCountable
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hreg : AutomorphicForm.IsRegularSemisimple γA :=
    isRegularSemisimple_map _ (isRegularSemisimple_of_mem_ellipticCell h2 hγ₀)
  have hcomm : ∀ s t : T, s * t = t * s := fun s t =>
    Subtype.ext (mul_comm_of_mem_centralizer hreg s.2 t.2)
  set τ : Measure T := Measure.haar with hτ
  haveI : τ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  haveI : SigmaFinite τ := inferInstance
  haveI : SFinite τ := instSFiniteOfSigmaFinite
  haveI : τ.IsMulRightInvariant := isMulRightInvariant_of_comm _ hcomm τ

  set Γ : Subgroup (AutomorphicForm.AdelicGL2 (𝓞 F) F) :=
    (Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) F))).map (AutomorphicForm.globalPoints (𝓞 F) F) with hΓ
  have hΓle : Γ ≤ (AutomorphicForm.globalPoints (𝓞 F) F).range := Subgroup.map_le_range _ _
  haveI : DiscreteTopology (Γ.subgroupOf T) := discreteTopology_subgroupOf F Γ T hΓle
  obtain ⟨D, -, -, hDall⟩ :=
    MeasureTheory.exists_measurableSet_isFundamentalDomain_op_of_discreteTopology (Γ.subgroupOf T)
      inferInstance
  have hD := hDall τ

  obtain ⟨G, hGc, hGs, hG⟩ :=
    AutomorphicForm.exists_continuous_hasCompactSupport_forall_isOrbitalIntegralOn_mul_centralScalar_of_mem_ellipticCell
      F γ₀ hγ₀ τ 1 f hf hfc
  simp only [one_smul] at hG

  set c : ℝ := τ.real (D ∩ {t | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det
        (t : AutomorphicForm.AdelicGL2 (𝓞 F) F)) ∈ Set.Icc α β}) with hc
  have hz : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
      ∫ x in Ψ, f (x⁻¹ * γA * (AutomorphicForm.centralScalar (𝓞 F) F z * x))
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F) = (c : ℂ) * G z := by
    intro z
    have hmz : Measurable fun g : AutomorphicForm.AdelicGL2 (𝓞 F) F =>
        f (g * AutomorphicForm.centralScalar (𝓞 F) F z) :=
      (hf.comp (continuous_mul_const _)).measurable
    have key :=
      AutomorphicForm.setIntegral_fundamentalDomain_slab_eq_measureReal_mul_of_isOrbitalIntegralOn
        F (adelicGLHaar (Fin 2) (𝓞 F) F) γ₀ τ α β hα Ψ hΨ D hD
        (fun g => f (g * AutomorphicForm.centralScalar (𝓞 F) F z)) hmz (G z) (hG z)
    rw [Measure.restrict_restrict_of_subset hΨs] at key
    simp only [conj_mul_centralScalar]
    exact key
  have hO : (fun z : (AdeleRing (𝓞 F) F)ˣ =>
      ∫ x in Ψ, f (x⁻¹ * γA * (AutomorphicForm.centralScalar (𝓞 F) F z * x))
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) = fun z => (c : ℂ) * G z := funext hz
  refine ⟨?_, ?_⟩
  · rw [hO]; exact continuous_const.mul hGc
  · rw [hO]; exact hGs.mul_left

end S_AutomorphicForm_continuous_and_hasCompactSupport_setIntegral_fundamentalDomain_conj_centralScalar_mul_of_mem_ellipticCell
end P2MW
export P2MW.S_AutomorphicForm_continuous_and_hasCompactSupport_setIntegral_fundamentalDomain_conj_centralScalar_mul_of_mem_ellipticCell (solution)
