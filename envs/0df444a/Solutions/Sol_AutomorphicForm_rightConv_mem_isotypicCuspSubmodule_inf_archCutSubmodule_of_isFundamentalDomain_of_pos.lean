-- Prove2me | solution 1 for AutomorphicForm.rightConv_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isFundamentalDomain_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/548a5f89-b7bc-5247-a38e-6b541178d5e9

import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Theorems.Thm_AutomorphicForm_isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_rightConv_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isFundamentalDomain_of_pos
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace ArchimedeanSmoothing

open AutomorphicForm

section TypePiece

variable {H G : Type*} [Group H] [Group G]
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

private theorem exists_out_mul_eq (ι : H →* G) (x : G) :
    ∃ k : H, (QuotientGroup.mk x : G ⧸ ι.range).out * ι k = x := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ι.range x
  obtain ⟨k, hk⟩ := h.2
  exact ⟨k⁻¹, by rw [map_inv, hh, ← hk, mul_inv_cancel_right]⟩

private noncomputable def cosetCoord (ι : H →* G) (x : G) : H :=
  (exists_out_mul_eq ι x).choose

private theorem out_mul_cosetCoord (ι : H →* G) (x : G) :
    (QuotientGroup.mk x : G ⧸ ι.range).out * ι (cosetCoord ι x) = x :=
  (exists_out_mul_eq ι x).choose_spec

private theorem cosetCoord_unique {ι : H →* G} (hι : Function.Injective ι) {x : G} {k : H}
    (hk : (QuotientGroup.mk x : G ⧸ ι.range).out * ι k = x) : k = cosetCoord ι x :=
  hι (mul_left_cancel (hk.trans (out_mul_cosetCoord ι x).symm))

private theorem cosetCoord_mul {ι : H →* G} (hι : Function.Injective ι) (x : G) (k : H) :
    cosetCoord ι (x * ι k) = cosetCoord ι x * k := by
  symm
  apply cosetCoord_unique hι
  have hmk : (QuotientGroup.mk (x * ι k) : G ⧸ ι.range) = QuotientGroup.mk x := by
    rw [QuotientGroup.eq]
    exact ⟨k⁻¹, by rw [map_inv, mul_inv_rev, inv_mul_cancel_right]⟩
  rw [hmk, map_mul, ← mul_assoc, out_mul_cosetCoord]

private theorem mem_typeSubmodule_of_isRightEquivariantOn {ι : H →* G} (hι : Function.Injective ι)
    (ρ : Representation ℂ H W) (P : Submodule ℂ W) (hP : ∀ (k : H), ∀ v ∈ P, ρ k v ∈ P)
    (S : P →ₗ[ℂ] (G → ℂ))
    (hS : ∀ (k : H) (v : P) (x : G), S ⟨ρ k v, hP k v v.2⟩ x = S v (x * ι k)) (v : P) :
    S v ∈ AutomorphicForm.typeSubmodule ι ρ := by
  classical
  let ℓ : G ⧸ ι.range → (P →ₗ[ℂ] ℂ) := fun c =>
    { toFun := fun p => S p c.out
      map_add' := fun p q => by rw [map_add]; rfl
      map_smul' := fun a p => by rw [map_smul]; rfl }
  have hext : ∀ c, ∃ g : W →ₗ[ℂ] ℂ, g.comp P.subtype = ℓ c := fun c => LinearMap.exists_extend (ℓ c)
  let ℓ' : G ⧸ ι.range → (W →ₗ[ℂ] ℂ) := fun c => (hext c).choose
  have hℓ' : ∀ c (p : P), ℓ' c (p : W) = S p c.out := fun c p => by
    have := LinearMap.congr_fun (hext c).choose_spec p
    simpa [ℓ] using this
  let T : W →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun w x => ℓ' (QuotientGroup.mk x) (ρ (cosetCoord ι x) w)
      map_add' := fun w₁ w₂ => funext fun x => by simp only [map_add, Pi.add_apply]
      map_smul' := fun a w => funext fun x => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] }
  have hT : AutomorphicForm.IsRightEquivariant ι ρ T := by
    intro k w x
    show ℓ' (QuotientGroup.mk x) (ρ (cosetCoord ι x) (ρ k w)) =
      ℓ' (QuotientGroup.mk (x * ι k)) (ρ (cosetCoord ι (x * ι k)) w)
    have hmk : (QuotientGroup.mk (x * ι k) : G ⧸ ι.range) = QuotientGroup.mk x := by
      rw [QuotientGroup.eq]
      exact ⟨k⁻¹, by rw [map_inv, mul_inv_rev, inv_mul_cancel_right]⟩
    rw [hmk, cosetCoord_mul hι, map_mul]
    rfl
  have hTS : T (v : W) = S v := by
    funext x
    show ℓ' (QuotientGroup.mk x) (ρ (cosetCoord ι x) (v : W)) = S v x
    have hmem : ρ (cosetCoord ι x) (v : W) ∈ P := hP _ _ v.2
    have h1 := hℓ' (QuotientGroup.mk x) ⟨_, hmem⟩
    simp only at h1
    rw [h1, hS (cosetCoord ι x) v, out_mul_cosetCoord]
  rw [← hTS]
  exact AutomorphicForm.mem_typeSubmodule_of_isRightEquivariant hT _

end TypePiece

section PiRep

variable {H : Type*} [Group H]
variable {A : Type*} {W : A → Type*} [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)]

private def piRep (ρ : ∀ a, Representation ℂ H (W a)) : Representation ℂ H (∀ a, W a) where
  toFun k := LinearMap.pi fun a => (ρ a k).comp (LinearMap.proj a)
  map_one' := by
    ext v a
    simp
  map_mul' k₁ k₂ := by
    ext v a
    simp

private theorem piRep_apply (ρ : ∀ a, Representation ℂ H (W a)) (k : H) (v : ∀ a, W a) (a : A) :
    piRep ρ k v a = ρ a k (v a) :=
  rfl

private theorem piRep_single [DecidableEq A] (ρ : ∀ a, Representation ℂ H (W a)) (k : H) (a : A)
    (v : W a) : piRep ρ k (Pi.single a v) = Pi.single a (ρ a k v) := by
  funext b
  rw [piRep_apply]
  by_cases hb : b = a
  · subst hb
    simp only [Pi.single_eq_same]
  · simp only [Pi.single_eq_of_ne hb, map_zero]

end PiRep

section Transport

variable {H G : Type*} [Group H] [Group G]

private theorem typeSubmodule_piRep_le {A : Type*} [Fintype A] [DecidableEq A] {W : A → Type*}
    [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)] (ι : H →* G)
    (ρ : ∀ a, Representation ℂ H (W a)) :
    typeSubmodule ι (piRep ρ) ≤ ⨆ a, typeSubmodule ι (ρ a) := by
  refine Submodule.span_le.mpr ?_
  rintro f ⟨T, hT, v, rfl⟩
  show T v ∈ ⨆ a, typeSubmodule ι (ρ a)
  rw [← Finset.univ_sum_single v, map_sum]
  refine Submodule.sum_mem _ fun a _ => Submodule.mem_iSup_of_mem a ?_
  have hTa : IsRightEquivariant ι (ρ a) (T.comp (LinearMap.single ℂ W a)) := by
    intro k w x
    show T (Pi.single a (ρ a k w)) x = T (Pi.single a w) (x * ι k)
    rw [← piRep_single]
    exact hT k (Pi.single a w) x
  exact mem_typeSubmodule_of_isRightEquivariant hTa (v a)

private theorem mem_iSup_typeSubmodule_of_isRightEquivariantOn_pi {A : Type*} [Fintype A] [DecidableEq A]
    {W : A → Type*} [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)] {ι : H →* G}
    (hι : Function.Injective ι) (ρ : ∀ a, Representation ℂ H (W a)) (Q : Submodule ℂ (∀ a, W a))
    (hQ : ∀ (k : H), ∀ v ∈ Q, piRep ρ k v ∈ Q) (S : Q →ₗ[ℂ] (G → ℂ))
    (hS : ∀ (k : H) (v : Q) (x : G), S ⟨piRep ρ k v, hQ k v v.2⟩ x = S v (x * ι k)) (v : Q) :
    S v ∈ ⨆ a, typeSubmodule ι (ρ a) :=
  typeSubmodule_piRep_le ι ρ (mem_typeSubmodule_of_isRightEquivariantOn hι (piRep ρ) Q hQ S hS v)

private theorem exists_isRightEquivariant_mem_range_of_mem_iSup_typeSubmodule {J : Type*} {W : J → Type*}
    [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)] (ι : H →* G)
    (ρ : ∀ j, Representation ℂ H (W j)) {θ : G → ℂ} (hθ : θ ∈ ⨆ j, typeSubmodule ι (ρ j)) :
    ∃ (t : Finset (G → ℂ)) (i : t → J) (Φ : (∀ a : t, W (i a)) →ₗ[ℂ] (G → ℂ)),
      IsRightEquivariant ι (piRep fun a => ρ (i a)) Φ ∧ θ ∈ LinearMap.range Φ := by
  classical
  have h1 : θ ∈ Submodule.span ℂ
      (⋃ j, {f : G → ℂ | ∃ T : W j →ₗ[ℂ] (G → ℂ),
        IsRightEquivariant ι (ρ j) T ∧ f ∈ LinearMap.range T}) := by
    rw [Submodule.span_iUnion]
    exact hθ
  obtain ⟨t, ht, hθt⟩ := Submodule.mem_span_finite_of_mem_span h1
  have hgen : ∀ f : t, ∃ j : J, ∃ T : W j →ₗ[ℂ] (G → ℂ),
      IsRightEquivariant ι (ρ j) T ∧ (f : G → ℂ) ∈ LinearMap.range T := fun f => by
    have hf := ht f.2
    rw [Set.mem_iUnion] at hf
    obtain ⟨j, T, hT, hfT⟩ := hf
    exact ⟨j, T, hT, hfT⟩
  choose i T hT hfT using hgen
  let Φ : (∀ a : t, W (i a)) →ₗ[ℂ] (G → ℂ) := ∑ a : t, (T a).comp (LinearMap.proj a)
  have hΦ : ∀ w : ∀ a : t, W (i a), Φ w = ∑ a : t, T a (w a) := fun w => by
    simp only [Φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  refine ⟨t, i, Φ, ?_, ?_⟩
  · intro k w x
    rw [hΦ, hΦ, Finset.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun a _ => hT a k (w a) x
  · refine (Submodule.span_le.mpr ?_) hθt
    intro f hf
    obtain ⟨v, hv⟩ := hfT ⟨f, hf⟩
    refine ⟨Pi.single (⟨f, hf⟩ : t) v, ?_⟩
    rw [hΦ, Finset.sum_eq_single (⟨f, hf⟩ : t)]
    · rw [Pi.single_eq_same]
      exact hv
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, map_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h

private theorem mem_iSup_typeSubmodule_of_intertwines {G' : Type*} [Group G'] {J : Type*} {W : J → Type*}
    [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)] (ι : H →* G) {ι' : H →* G'}
    (hι' : Function.Injective ι') (ρ : ∀ j, Representation ℂ H (W j)) (P₀ : Submodule ℂ (G → ℂ))
    (hP₀ : ∀ (k : H), ∀ θ ∈ P₀, (fun x => θ (x * ι k)) ∈ P₀) (A : P₀ →ₗ[ℂ] (G' → ℂ))
    (hA : ∀ (k : H) (θ : P₀) (y : G'), A ⟨fun x => (θ : G → ℂ) (x * ι k), hP₀ k θ θ.2⟩ y =
      A θ (y * ι' k))
    (θ : P₀) (hθ : (θ : G → ℂ) ∈ ⨆ j, typeSubmodule ι (ρ j)) :
    A θ ∈ ⨆ j, typeSubmodule ι' (ρ j) := by
  classical
  obtain ⟨t, i, Φ, hΦ, v, hv⟩ :=
    exists_isRightEquivariant_mem_range_of_mem_iSup_typeSubmodule ι ρ hθ
  have hQ : ∀ (k : H), ∀ w ∈ P₀.comap Φ, piRep (fun a => ρ (i a)) k w ∈ P₀.comap Φ := by
    intro k w hw
    rw [Submodule.mem_comap] at hw ⊢
    have hw' : Φ (piRep (fun a => ρ (i a)) k w) = fun x => Φ w (x * ι k) :=
      funext fun x => hΦ k w x
    rw [hw']
    exact hP₀ k _ hw
  let ΦQ : P₀.comap Φ →ₗ[ℂ] P₀ :=
    LinearMap.codRestrict P₀ (Φ.comp (P₀.comap Φ).subtype) fun w => w.2
  have hΦQ : ∀ w : P₀.comap Φ, ((ΦQ w : P₀) : G → ℂ) = Φ (w : ∀ a : t, W (i a)) := fun _ => rfl
  let S : P₀.comap Φ →ₗ[ℂ] (G' → ℂ) := A.comp ΦQ
  have hS : ∀ (k : H) (w : P₀.comap Φ) (y : G'),
      S ⟨piRep (fun a => ρ (i a)) k w, hQ k w w.2⟩ y = S w (y * ι' k) := by
    intro k w y
    have h1 : ΦQ ⟨piRep (fun a => ρ (i a)) k w, hQ k w w.2⟩ =
        ⟨fun x => ((ΦQ w : P₀) : G → ℂ) (x * ι k), hP₀ k _ (ΦQ w).2⟩ := by
      apply Subtype.ext
      funext x
      exact hΦ k w x
    show A (ΦQ ⟨piRep (fun a => ρ (i a)) k w, hQ k w w.2⟩) y = A (ΦQ w) (y * ι' k)
    rw [h1]
    exact hA k (ΦQ w) y
  have hv' : v ∈ P₀.comap Φ := by
    rw [Submodule.mem_comap, hv]
    exact θ.2
  have hmem := mem_iSup_typeSubmodule_of_isRightEquivariantOn_pi hι' (fun a => ρ (i a)) (P₀.comap Φ)
    hQ S hS ⟨v, hv'⟩
  have hSv : S ⟨v, hv'⟩ = A θ := by
    show A (ΦQ ⟨v, hv'⟩) = A θ
    congr 1
    exact Subtype.ext hv
  rw [hSv] at hmem
  exact (iSup_le fun a => le_iSup (fun j => typeSubmodule ι' (ρ j)) (i a)) hmem

end Transport

section Interchange

private noncomputable def integralCLM {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] (ρ : Measure Y) [IsFiniteMeasure ρ] :
    C(Y, ℂ) →L[ℝ] ℂ :=
  haveI : IsFiniteMeasureOnCompacts ρ :=
    isFiniteMeasure_iff_isFiniteMeasureOnCompacts_of_compactSpace.mp inferInstance
  have hint : ∀ F : C(Y, ℂ), Integrable (fun y => F y) ρ := fun F =>
    F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  LinearMap.mkContinuous
    { toFun := fun F => ∫ y, F y ∂ρ
      map_add' := fun F₁ F₂ => by
        simp only [ContinuousMap.add_apply]
        exact integral_add (hint F₁) (hint F₂)
      map_smul' := fun r F => by
        simp only [ContinuousMap.smul_apply, RingHom.id_apply]
        exact integral_smul r fun y => F y }
    (ρ.real Set.univ) fun F => by
      refine (norm_integral_le_of_norm_le_const (μ := ρ)
        (Filter.Eventually.of_forall fun y => F.norm_coe_le_norm y)).trans ?_
      rw [mul_comm]

private theorem integralCLM_apply {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] (ρ : Measure Y) [IsFiniteMeasure ρ]
    (F : C(Y, ℂ)) : integralCLM ρ F = ∫ y, F y ∂ρ :=
  rfl

section Slices

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
  {Q : Type*} [TopologicalSpace Q] (S : Set Q)
  {u : Q → G} (hu : Continuous u) {φ : G → ℂ} (hφ : Continuous φ) {f : G → ℂ} (hf : Continuous f)
  (g : G)

private def sliceFn : C(G × S, ℂ) :=
  ⟨fun p => φ (u p.2 * g * p.1) * f p.1, by fun_prop⟩

private noncomputable def slice (x : G) : C(S, ℂ) :=
  (sliceFn S hu hφ hf g).curry x

private theorem slice_apply (x : G) (q : S) : slice S hu hφ hf g x q = φ (u q * g * x) * f x :=
  rfl

private theorem continuous_slice : Continuous (slice S hu hφ hf g) :=
  (sliceFn S hu hφ hf g).curry.continuous

private theorem hasCompactSupport_slice (hfs : HasCompactSupport f) :
    HasCompactSupport (slice S hu hφ hf g) := by
  refine hfs.mono fun x hx => ?_
  rw [Function.mem_support] at hx ⊢
  intro hfx
  apply hx
  ext q
  rw [slice_apply, hfx, mul_zero, ContinuousMap.zero_apply]

end Slices

private theorem integral_integral_eq_zero
    {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] [MeasurableSpace G]
    [OpensMeasurableSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    {Q : Type*} [TopologicalSpace Q] [T2Space Q] [MeasurableSpace Q] [OpensMeasurableSpace Q]
    (ν : Measure Q) [IsFiniteMeasure ν] {S : Set Q} (hS : IsCompact S) (hνS : ∀ᵐ q ∂ν, q ∈ S)
    {u : Q → G} (hu : Continuous u) {φ : G → ℂ} (hφ : Continuous φ) {f : G → ℂ}
    (hf : Continuous f) (hfs : HasCompactSupport f) (g : G)
    (hzero : ∀ h : G, ∫ q, φ (u q * h) ∂ν = 0) :
    ∫ q, (∫ x, φ (u q * g * x) * f x ∂μ) ∂ν = 0 := by
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hres : ν.restrict S = ν := Measure.restrict_eq_self_of_ae_mem hνS
  have hsub : ∀ h : Q → ℂ, ∫ q : S, h q ∂(ν.comap Subtype.val) = ∫ q, h q ∂ν := fun h => by
    rw [integral_subtype_comap hSm, hres]
  have hΦi : Integrable (slice S hu hφ hf g) μ :=
    (continuous_slice S hu hφ hf g).integrable_of_hasCompactSupport
      (hasCompactSupport_slice S hu hφ hf g hfs)
  have hJΦ : ∀ x, integralCLM (ν.comap (Subtype.val : S → Q)) (slice S hu hφ hf g x) = 0 :=
    fun x => by
      rw [integralCLM_apply]
      simp only [slice_apply]
      rw [hsub fun q => φ (u q * g * x) * f x, integral_mul_const]
      simp only [mul_assoc]
      rw [hzero (g * x), zero_mul]
  have hev : ∀ q : S, (∫ x, slice S hu hφ hf g x ∂μ) q = ∫ x, φ (u q * g * x) * f x ∂μ :=
    fun q => by
      rw [ContinuousMap.integral_apply hΦi q]
      simp only [slice_apply]
  calc ∫ q, (∫ x, φ (u q * g * x) * f x ∂μ) ∂ν
      = ∫ q : S, (∫ x, slice S hu hφ hf g x ∂μ) q ∂(ν.comap (Subtype.val : S → Q)) := by
        rw [← hsub fun q => ∫ x, φ (u q * g * x) * f x ∂μ]
        exact integral_congr_ae (Filter.Eventually.of_forall fun q => (hev q).symm)
    _ = integralCLM (ν.comap (Subtype.val : S → Q)) (∫ x, slice S hu hφ hf g x ∂μ) :=
        (integralCLM_apply _ _).symm
    _ = ∫ x, integralCLM (ν.comap (Subtype.val : S → Q)) (slice S hu hφ hf g x) ∂μ :=
        (ContinuousLinearMap.integral_comp_comm _ hΦi).symm
    _ = 0 := by simp only [hJΦ, integral_zero]

end Interchange

section Adelic

open AutomorphicForm.SmoothCusp FLT.SmoothVectors
open scoped ProbabilityTheory

variable (K : Type) [Field K] [NumberField K]

private abbrev pinsAt (X : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K)) :
    CarrierPins K :=
  productionPinsOf K X U (fun v => heckeGen (𝓞 K) K v) (adelicBox K)

private theorem eq_of_glArch_eq_of_glFin_eq {a b : AdelicGL2 (𝓞 K) K} (h1 : glArch (𝓞 K) K a = glArch (𝓞 K) K b)
    (h2 : glFin (𝓞 K) K a = glFin (𝓞 K) K b) : a = b := by
  refine Matrix.GeneralLinearGroup.ext fun i j => Prod.ext ?_ ?_
  · exact congrArg (fun g : GL (Fin 2) (InfiniteAdeleRing K) =>
      (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j) h1
  · exact congrArg (fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
      (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) h2

private theorem mul_comm_of_glFin_eq_one {a m : AdelicGL2 (𝓞 K) K} (ha : glFin (𝓞 K) K a = 1)
    (hm : glArch (𝓞 K) K m = 1) : a * m = m * a :=
  eq_of_glArch_eq_of_glFin_eq K (by rw [map_mul, map_mul, hm, mul_one, one_mul])
    (by rw [map_mul, map_mul, ha, one_mul, mul_one])

private theorem glArch_heckeGen (v : HeightOneSpectrum (𝓞 K)) : glArch (𝓞 K) K (heckeGen (𝓞 K) K v) = 1 := by
  refine Units.ext ?_
  rw [Units.val_one]
  ext i j
  rw [glArch_apply]
  exact heckeGenAt_fst _ i j

private theorem glArch_eq_one_of_mem_doubleCoset {V : Subgroup (AdelicGL2 (𝓞 K) K)}
    (hV : V ≤ finiteAdelicGL2Subgroup K) {t x : AdelicGL2 (𝓞 K) K} (ht : glArch (𝓞 K) K t = 1)
    (hx : x ∈ HeckePair.doubleCoset V t) :
    glArch (𝓞 K) K x = 1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  rw [map_mul, map_mul, ht, (mem_finiteAdelicGL2Subgroup_iff K a).mp (hV ha),
    (mem_finiteAdelicGL2Subgroup_iff K b).mp (hV hb), mul_one, mul_one]

section Pointwise

variable {V : Subgroup (AdelicGL2 (𝓞 K) K)} {f : AdelicGL2 (𝓞 K) K → ℂ}
  (hfs : ∀ x : AdelicGL2 (𝓞 K) K, f x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K a = 1 ∧ k ∈ V ∧ x = a * k)
  {θ : AdelicGL2 (𝓞 K) K → ℂ} (hθV : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ V, θ (g * k) = θ g)

include hfs hθV

private theorem apply_mul_mul_eq {m : AdelicGL2 (𝓞 K) K} (hm₁ : glArch (𝓞 K) K m = 1)
    (hm : ∀ y : AdelicGL2 (𝓞 K) K, θ (y * m) = θ y) (y x : AdelicGL2 (𝓞 K) K) :
    θ (y * m * x) * f x = θ (y * x) * f x := by
  by_cases hx : f x = 0
  · rw [hx, mul_zero, mul_zero]
  · obtain ⟨a, k, ha, hk, rfl⟩ := hfs x hx
    have e : y * m * (a * k) = y * a * m * k := by
      rw [← mul_assoc, mul_assoc y m a, ← mul_comm_of_glFin_eq_one K ha hm₁, ← mul_assoc]
    rw [e, hθV _ _ hk, hm, ← mul_assoc y a k, hθV _ _ hk]

private theorem sum_apply_mul_mul_eq {n : ℕ} {reps : Fin n → AdelicGL2 (𝓞 K) K}
    (hreps : ∀ i, glArch (𝓞 K) K (reps i) = 1) {cv : ℂ}
    (heq : ∀ g : AdelicGL2 (𝓞 K) K, heckeCosetSum K reps θ g = cv * θ g) (g x : AdelicGL2 (𝓞 K) K) :
    ∑ i, θ (g * reps i * x) * f x = cv * (θ (g * x) * f x) := by
  by_cases hx : f x = 0
  · simp only [hx, mul_zero, Finset.sum_const_zero]
  · obtain ⟨a, k, ha, hk, rfl⟩ := hfs x hx
    have e : ∀ i, θ (g * reps i * (a * k)) = θ (g * a * reps i) := fun i => by
      rw [← mul_assoc, mul_assoc g (reps i) a, ← mul_comm_of_glFin_eq_one K ha (hreps i), ← mul_assoc,
        hθV _ _ hk]
    have hsum : ∑ i, θ (g * reps i * (a * k)) * f (a * k) = (∑ i, θ (g * a * reps i)) * f (a * k) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by rw [e i]
    rw [hsum, ← mul_assoc g a k, hθV _ _ hk, ← mul_assoc cv]
    exact congrArg (· * f (a * k)) (heq (g * a))

private theorem rightConv_mul_eq {m : AdelicGL2 (𝓞 K) K} (hm₁ : glArch (𝓞 K) K m = 1)
    (hm : ∀ y : AdelicGL2 (𝓞 K) K, θ (y * m) = θ y) (y : AdelicGL2 (𝓞 K) K) :
    rightConv K θ f (y * m) = rightConv K θ f y := by
  show (∫ x, θ (y * m * x) * f x ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
    ∫ x, θ (y * x) * f x ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => apply_mul_mul_eq K hfs hθV hm₁ hm y x)

end Pointwise

private theorem integrable_apply_mul_mul {θ f : AdelicGL2 (𝓞 K) K → ℂ} (hθ : Continuous θ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (g : AdelicGL2 (𝓞 K) K) :
    Integrable (fun x => θ (g * x) * f x) (adelicGLHaar (Fin 2) (𝓞 K) K) := by
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  exact ((hθ.comp (continuous_const.mul continuous_id)).mul hf).integrable_of_hasCompactSupport hfc.mul_left

private theorem measurableSet_window (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) :
    MeasurableSet (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) := by
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  refine T.measurableSet_biUnion fun x _ => ?_
  show MeasurableSet ((· * x) '' centreCutSiegelSet K c u d₁ d₂)
  rw [Set.image_mul_right]
  exact measurable_mul_const x⁻¹ (measurableSet_centreCutSiegelSet c u d₁ d₂)

private theorem measure_window_lt_top {c : ℝ} (hc : 0 < c) (u : ℝ) {d₁ : ℝ} (hd₁ : 0 < d₁) (d₂ : ℝ)
    (T : Finset (AdelicGL2 (𝓞 K) K)) :
    adelicGLHaar (Fin 2) (𝓞 K) K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) < ⊤ := by
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI := isMulRightInvariant_adelicGLHaar K
  refine (measure_biUnion_finset_le T _).trans_lt (ENNReal.sum_lt_top.mpr fun x _ => ?_)
  show adelicGLHaar (Fin 2) (𝓞 K) K ((· * x) '' centreCutSiegelSet K c u d₁ d₂) < ⊤
  rw [Set.image_mul_right, measure_preimage_mul_right]
  exact NumberField.SiegelVolume.measure_centreCutSiegelSet_lt_top _ hc u hd₁ d₂

private theorem memLp_two_restrict_of_bound {X : Set (AdelicGL2 (𝓞 K) K)} (hX : MeasurableSet X)
    (hXμ : adelicGLHaar (Fin 2) (𝓞 K) K X < ⊤) {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Continuous φ) {C : ℝ}
    (hC : ∀ g ∈ X, ‖φ g‖ ≤ C) : MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict X) := by
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict X) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hXμ⟩
  exact MemLp.of_bound hφ.aestronglyMeasurable C (ae_restrict_of_forall_mem hX hC)

private theorem isIsotypicCuspFormAt_rightConv (α β : ℝ) (hβ : 0 < β) (hαβ : α < β)
    (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K)) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 K)) (hU : U N ≤ finiteAdelicGL2Subgroup K) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (π : HeckeEigensystem K ℂ) {c : ℝ} (u : ℝ) {d₁ : ℝ} (d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : IsFactorizableTestFn K f)
    (hfs : ∀ x : AdelicGL2 (𝓞 K) K, f x ≠ 0 →
      ∃ a k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K a = 1 ∧ k ∈ U N ∧ x = a * k)
    {θ : AdelicGL2 (𝓞 K) K → ℂ} (hθ : IsIsotypicCuspFormAt K (pinsAt K Φ U) ξ N S π θ) :
    IsIsotypicCuspFormAt K (pinsAt K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) U) ξ N S π
      (rightConv K θ f) := by
  obtain ⟨hfc, hfcs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K f hf
  have hθc : Continuous θ := hθ.continuous
  letI : MeasurableSpace (AdelicGL2 (𝓞 K) K) := glBorel (Fin 2) (𝓞 K) K
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K
  haveI : BorelSpace (AdeleRing (𝓞 K) K) := borelSpace_adeleBorel (𝓞 K) K
  haveI : IsProbabilityMeasure ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) :=
    isProbabilityMeasure_cond_adelicBox K
  have hls : IsLsXiFunction (𝓞 K) K (pinsAt K Φ U).Z ξ θ :=
    ((lsXiMemberAt_iff (𝓞 K) K _ _ ξ _ θ).mp hθ.smoothCusp.1.1).1
  have hθU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ U N, θ (g * k) = θ g := hθ.level_invariant
  have hlevel : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ U N, rightConv K θ f (g * k) = rightConv K θ f g :=
    fun g k hk => rightConv_mul_eq K hfs hθU ((mem_finiteAdelicGL2Subgroup_iff K k).mp (hU hk))
      (fun y => hθU y k hk) g
  have hcont : Continuous (rightConv K θ f) :=
    (continuous_rightConv_and_contDiff_of_isFactorizableTestFn K θ hθc f hf).1
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hcont, hlevel, ?_, ?_⟩
  ·
    refine (lsXiMemberAt_iff (𝓞 K) K _ _ ξ _ _).mpr ⟨⟨?_, ?_⟩, ?_⟩
    · intro γ g
      show (∫ x, θ (globalPoints (𝓞 K) K γ * g * x) * f x ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
        ∫ x, θ (g * x) * f x ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
        simp only [mul_assoc, hls.left_invariant])
    · intro z g
      have hz : ∀ y : AdelicGL2 (𝓞 K) K,
          θ (centralScalar (𝓞 K) K (z : (AdeleRing (𝓞 K) K)ˣ) * y) = ((ξ z : ℂˣ) : ℂ) * θ y :=
        fun y => hls.central_transform z y
      show (∫ x, θ (centralScalar (𝓞 K) K (z : (AdeleRing (𝓞 K) K)ˣ) * g * x) * f x
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
        ((ξ z : ℂˣ) : ℂ) * ∫ x, θ (g * x) * f x ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      exact (integral_congr_ae (Filter.Eventually.of_forall fun x => by
        rw [mul_assoc, hz, mul_assoc])).trans (integral_const_mul _ _)
    · show MemLp (rightConv K θ f) 2
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
      obtain ⟨C, hC⟩ :=
        isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_isFundamentalDomain K α β hβ hαβ Φ hΦ
          U (fun v => heckeGen (𝓞 K) K v) ξ θ hθ.smoothCusp.1 hθc f hf c u d₁ d₂ T hc hd₁
      exact memLp_two_restrict_of_bound K (measurableSet_window K c u d₁ d₂ T)
        (measure_window_lt_top K hc u hd₁ d₂ T) hcont hC
  ·
    intro g
    obtain ⟨S₀, hS₀, hBS⟩ := exists_isCompact_adelicBox_subset K
    have hνS : ∀ᵐ q ∂((adelicAddHaar (𝓞 K) K)[|adelicBox K]), q ∈ S₀ :=
      (ProbabilityTheory.ae_cond_mem (measurableSet_adelicBox K)).mono fun q hq => hBS hq
    have hcusp : ∀ h : AdelicGL2 (𝓞 K) K,
        ∫ q, θ (unipotentGL2 q * h) ∂((adelicAddHaar (𝓞 K) K)[|adelicBox K]) = 0 :=
      fun h => hθ.smoothCusp.1.2 h
    show ∫ q, rightConv K θ f (unipotentGL2 q * g) ∂((adelicAddHaar (𝓞 K) K)[|adelicBox K]) = 0
    exact integral_integral_eq_zero (adelicGLHaar (Fin 2) (𝓞 K) K) ((adelicAddHaar (𝓞 K) K)[|adelicBox K])
      hS₀ hνS continuous_unipotentGL2 hθc hfc hfcs g hcusp
  ·
    rw [isKfSmooth_iff, isSmoothVector_iff_exists_isOpen_subgroup]
    obtain ⟨V, hVo, hV⟩ :=
      isSmoothVector_iff_exists_isOpen_subgroup.mp ((isKfSmooth_iff K θ).mp hθ.smoothCusp.2)
    refine ⟨V, hVo, fun m hm => ?_⟩
    have hmθ : ∀ y : AdelicGL2 (𝓞 K) K, θ (y * (m : AdelicGL2 (𝓞 K) K)) = θ y := fun y =>
      congrArg (fun F : RightTranslationFn (AdelicGL2 (𝓞 K) K) ℂ => RightTranslationFn.toFun F y) (hV m hm)
    rw [Subgroup.smul_def]
    exact RightTranslationFn.ext fun y =>
      rightConv_mul_eq K hfs hθU ((mem_finiteAdelicGL2Subgroup_iff K _).mp m.2) hmθ y
  ·
    intro v hv
    obtain ⟨reps, hsys, heq⟩ := hθ.hecke_eigen v hv
    refine ⟨reps, hsys, fun g => ?_⟩
    have hreps : ∀ i, glArch (𝓞 K) K (reps i) = 1 := fun i =>
      glArch_eq_one_of_mem_doubleCoset K hU (glArch_heckeGen K v) (hsys.mem_doubleCoset i)
    show (∑ i, ∫ x, θ (g * reps i * x) * f x ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
      π.a v * ∫ x, θ (g * x) * f x ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
    rw [← integral_finsetSum Finset.univ fun i _ => integrable_apply_mul_mul K hθc hfc hfcs (g * reps i)]
    exact (integral_congr_ae (Filter.Eventually.of_forall fun x =>
      sum_apply_mul_mul_eq K hfs hθU hreps heq g x)).trans (integral_const_mul _ _)
  ·
    intro v hv g
    have hce : ∀ y : AdelicGL2 (𝓞 K) K,
        θ (centralScalar (𝓞 K) K (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) * y) =
          π.toRawCentral.b v * θ y :=
      fun y => hθ.central_eigen v hv y
    show (∫ x, θ (centralScalar (𝓞 K) K (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) * g * x) * f x
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
      π.toRawCentral.b v * ∫ x, θ (g * x) * f x ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
    exact (integral_congr_ae (Filter.Eventually.of_forall fun x => by
      rw [mul_assoc, hce, mul_assoc])).trans (integral_const_mul _ _)

private theorem archComponent_glArch_rowIsometryInclAt₀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion) :
    archComponent K w (glArch (𝓞 K) K (rowIsometryInclAt₀ K w k)) = (k : GL (Fin 2) w.Completion) := by
  rw [glArch_rowIsometryInclAt₀]
  exact archComponent_archGLIncl_self K w (k : GL (Fin 2) w.Completion)

private theorem rowIsometryInclAt₀_injective (w : InfinitePlace K) : Function.Injective (rowIsometryInclAt₀ K w) :=
  fun a b h => by
    have ha := archComponent_glArch_rowIsometryInclAt₀ K w a
    have hb := archComponent_glArch_rowIsometryInclAt₀ K w b
    rw [h] at ha
    exact Subtype.ext (ha.symm.trans hb)

private def continuousSubmodule : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) where
  carrier := {θ | Continuous θ}
  zero_mem' := continuous_zero
  add_mem' := by
    intro θ₁ θ₂ h₁ h₂
    exact h₁.add h₂
  smul_mem' := by
    intro a θ h
    exact h.const_smul a

private theorem mem_continuousSubmodule_iff (θ : AdelicGL2 (𝓞 K) K → ℂ) :
    θ ∈ continuousSubmodule K ↔ Continuous θ :=
  Iff.rfl

private def convOn {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    continuousSubmodule K →ₗ[ℂ] (AdelicGL2 (𝓞 K) K → ℂ) where
  toFun θ := rightConv K θ f
  map_add' θ₁ θ₂ := by
    show rightConv K ((θ₁ : AdelicGL2 (𝓞 K) K → ℂ) + θ₂) f = rightConv K θ₁ f + rightConv K θ₂ f
    exact rightConv_add_left K ((mem_continuousSubmodule_iff K _).mp θ₁.2)
      ((mem_continuousSubmodule_iff K _).mp θ₂.2) hf hfc
  map_smul' a θ := by
    show rightConv K (a • (θ : AdelicGL2 (𝓞 K) K → ℂ)) f = a • rightConv K θ f
    exact convOp_smul K f a θ

private theorem convOn_apply {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (θ : continuousSubmodule K) : convOn K hf hfc θ = rightConv K θ f :=
  rfl

private theorem rightConv_comp_mul_right {f : AdelicGL2 (𝓞 K) K → ℂ} {k₀ : AdelicGL2 (𝓞 K) K}
    (hk : ∀ y : AdelicGL2 (𝓞 K) K, f (k₀⁻¹ * y * k₀) = f y) (θ : AdelicGL2 (𝓞 K) K → ℂ)
    (y : AdelicGL2 (𝓞 K) K) : rightConv K (fun x => θ (x * k₀)) f y = rightConv K θ f (y * k₀) := by
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI := isMulRightInvariant_adelicGLHaar K
  show (∫ x, θ (y * x * k₀) * f x ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
    ∫ x, θ (y * k₀ * x) * f x ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
  symm
  calc ∫ x, θ (y * k₀ * x) * f x ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      = ∫ x, θ (y * k₀ * (k₀⁻¹ * x)) * f (k₀⁻¹ * x) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
        (integral_mul_left_eq_self (fun x => θ (y * k₀ * x) * f x) k₀⁻¹).symm
    _ = ∫ x, θ (y * k₀ * (k₀⁻¹ * (x * k₀))) * f (k₀⁻¹ * (x * k₀)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
        (integral_mul_right_eq_self (fun x => θ (y * k₀ * (k₀⁻¹ * x)) * f (k₀⁻¹ * x)) k₀).symm
    _ = ∫ x, θ (y * x * k₀) * f x ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by
          show θ (y * k₀ * (k₀⁻¹ * (x * k₀))) * f (k₀⁻¹ * (x * k₀)) = θ (y * x * k₀) * f x
          rw [mul_assoc y k₀, mul_inv_cancel_left, ← mul_assoc y x k₀, ← mul_assoc k₀⁻¹ x k₀, hk x])

private theorem rightConv_mem_archCutSubmodule {tys : ArchTypeFamily K} {f : AdelicGL2 (𝓞 K) K → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfK : ∀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion) (y : AdelicGL2 (𝓞 K) K),
      f (rowIsometryInclAt₀ K w k * y * (rowIsometryInclAt₀ K w k)⁻¹) = f y)
    {θ : AdelicGL2 (𝓞 K) K → ℂ} (hθ : Continuous θ) (hθt : θ ∈ archCutSubmodule K tys) :
    rightConv K θ f ∈ archCutSubmodule K tys := by
  have hk : ∀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion) (y : AdelicGL2 (𝓞 K) K),
      f ((rowIsometryInclAt₀ K w k)⁻¹ * y * rowIsometryInclAt₀ K w k) = f y := fun w k y => by
    have h := hfK w k⁻¹ y
    rwa [map_inv, inv_inv] at h
  rw [mem_archCutSubmodule_iff] at hθt ⊢
  intro w
  refine mem_iSup_typeSubmodule_of_intertwines (rowIsometryInclAt₀ K w) (rowIsometryInclAt₀_injective K w)
    (fun i => (tys.rep w i).ρ) (continuousSubmodule K) (fun k θ' hθ' => ?_) (convOn K hf hfc)
    (fun k θ' y => rightConv_comp_mul_right K (hk w k) (θ' : AdelicGL2 (𝓞 K) K → ℂ) y)
    ⟨θ, (mem_continuousSubmodule_iff K θ).mpr hθ⟩ (hθt w)
  exact (mem_continuousSubmodule_iff K _).mpr
    (((mem_continuousSubmodule_iff K θ').mp hθ').comp (continuous_mul_const (rowIsometryInclAt₀ K w k)))

end Adelic

end ArchimedeanSmoothing

end

open AutomorphicForm ArchimedeanSmoothing in

theorem solution
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hβ : 0 < β) (hαβ : α < β) (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (N : Ideal (𝓞 K)) (hU : U N ≤ finiteAdelicGL2Subgroup K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (tys : ArchTypeFamily K) (π : HeckeEigensystem K ℂ)
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hc : 0 < c) (hd₁ : 0 < d₁)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f)
    (hfs : ∀ x : AdelicGL2 (𝓞 K) K, f x ≠ 0 →
      ∃ a k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K a = 1 ∧ k ∈ U N ∧ x = a * k)
    (hfK : ∀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion) (y : AdelicGL2 (𝓞 K) K),
      f (rowIsometryInclAt₀ K w k * y * (rowIsometryInclAt₀ K w k)⁻¹) = f y) :
    ∀ φ ∈ isotypicCuspSubmodule K (productionPinsOf K Φ U (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          ξ N S π ⊓ archCutSubmodule K tys,
      rightConv K φ f ∈ isotypicCuspSubmodule K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) U
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S π
        ⊓ archCutSubmodule K tys := by
  intro φ hφ
  rw [Submodule.mem_inf] at hφ ⊢
  obtain ⟨hfc, hfcs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K f hf
  refine ⟨?_, rightConv_mem_archCutSubmodule K hfc hfcs hfK (continuous_of_mem_isotypicCuspSubmodule hφ.1) hφ.2⟩
  refine Submodule.span_induction
    (p := fun θ _ => rightConv K θ f ∈
      isotypicCuspSubmodule K (pinsAt K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) U) ξ N S π)
    ?_ ?_ ?_ ?_ hφ.1
  · exact fun θ hθ =>
      (isIsotypicCuspFormAt_rightConv K α β hβ hαβ Φ hΦ U ξ N hU S π u d₂ T hc hd₁ hf hfs hθ).mem_isotypicCuspSubmodule
  · show rightConv K 0 f ∈ _
    rw [show rightConv K 0 f = 0 from convOp_zero K f]
    exact Submodule.zero_mem _
  · intro θ₁ θ₂ h₁ h₂ hθ₁ hθ₂
    show rightConv K (θ₁ + θ₂) f ∈ _
    rw [rightConv_add_left K (continuous_of_mem_isotypicCuspSubmodule h₁) (continuous_of_mem_isotypicCuspSubmodule h₂)
      hfc hfcs]
    exact Submodule.add_mem _ hθ₁ hθ₂
  · intro a θ _ hθ
    show rightConv K (a • θ) f ∈ _
    rw [show rightConv K (a • θ) f = a • rightConv K θ f from convOp_smul K f a θ]
    exact Submodule.smul_mem _ a hθ

end S_AutomorphicForm_rightConv_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isFundamentalDomain_of_pos
end P2MW
export P2MW.S_AutomorphicForm_rightConv_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isFundamentalDomain_of_pos (solution)
