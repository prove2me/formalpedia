-- Prove2me | solution 1 for AutomorphicForm.exists_isCompact_setOf_twistedConj_mem_subset_twistedCentralizer_mul_of_forall_ne_scalar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/00544b4d-8a9d-514d-9dbe-ad990a28315a

import Theorems.Thm_AutomorphicForm_isSigmaConjugate_adeleRing_of_normString_eq_of_normString_mem_center_of_finrank_eq_two
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isCompact_setOf_twistedConj_mem_subset_twistedCentralizer_mul_of_forall_ne_scalar_of_finrank_eq_two
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace P2mSecondKindProper

open NumberField Filter Function Set Topology
open scoped TensorProduct TensorProduct.RightActions Pointwise

section Lift

theorem exists_isCompact_subset_image {G X : Type*} [TopologicalSpace G] [TopologicalSpace X]
    [LocallyCompactSpace G] (ω : G → X) (hω : IsOpenMap ω) (hsurj : Function.Surjective ω)
    {T : Set X} (hT : IsCompact T) :
    ∃ C : Set G, IsCompact C ∧ T ⊆ ω '' C := by
  classical
  choose g hg using hsurj
  have hN : ∀ x : X, ∃ N : Set G, IsCompact N ∧ N ∈ 𝓝 (g x) := fun x =>
    let ⟨N, hN, hNc⟩ := exists_compact_mem_nhds (g x)
    ⟨N, hN, hNc⟩
  choose N hNc hNn using hN
  have hU : ∀ x ∈ T, ω '' N x ∈ 𝓝 x := by
    intro x _
    have h := hω.image_mem_nhds (hNn x)
    rwa [hg x] at h
  obtain ⟨t, -, hcover⟩ := hT.elim_nhds_subcover (fun x => ω '' N x) hU
  refine ⟨⋃ x ∈ t, N x, t.isCompact_biUnion fun x _ => hNc x, ?_⟩
  intro y hy
  obtain ⟨x, hxt, hyx⟩ : ∃ x ∈ t, y ∈ ω '' N x := by
    have := hcover hy
    simp only [Set.mem_iUnion] at this
    obtain ⟨x, hx, h⟩ := this
    exact ⟨x, hx, h⟩
  obtain ⟨n, hn, rfl⟩ := hyx
  exact ⟨n, Set.mem_biUnion hxt hn, rfl⟩

end Lift

section Topology

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

omit [IsTopologicalRing A] in
theorem t2Space_GL [T2Space A] : T2Space (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  exact Units.isEmbedding_embedProduct.t2Space

omit [IsTopologicalRing A] in
theorem secondCountableTopology_GL [SecondCountableTopology A] :
    SecondCountableTopology (GL (Fin 2) A) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem locallyCompactSpace_GL [T2Space A] [LocallyCompactSpace A] :
    LocallyCompactSpace (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → A))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

end Topology

section TensorTopology

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

theorem secondCountableTopology_tensor [SecondCountableTopology A] :
    SecondCountableTopology (L ⊗[K] A) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  let ι := Module.Free.ChooseBasisIndex A (L ⊗[K] A)
  haveI : Fintype ι := Module.Free.ChooseBasisIndex.fintype A (L ⊗[K] A)
  let b : Module.Basis ι A (L ⊗[K] A) := Module.Free.chooseBasis A (L ⊗[K] A)
  let e : (L ⊗[K] A) ≃ₗ[A] (ι → A) := b.equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let eh : (L ⊗[K] A) ≃ₜ (ι → A) :=
    { toEquiv := e.toEquiv, continuous_toFun := h1, continuous_invFun := h2 }
  exact eh.isInducing.secondCountableTopology

theorem continuous_sigmaTensor (σ : L ≃ₐ[K] L) : Continuous (AutomorphicForm.sigmaTensor K L A σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  exact IsModuleTopology.continuous_of_linearMap
    (TensorProduct.RightActions.AlgebraMap.baseChange K L L A σ.toAlgHom).toLinearMap

theorem continuous_sigmaGL (σ : L ≃ₐ[K] L) : Continuous (AutomorphicForm.sigmaGL K L A σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  refine Continuous.units_map _ ?_
  exact continuous_id.matrix_map (continuous_sigmaTensor K L A σ)

end TensorTopology

section Algebra

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

local notation "sc" => Matrix.GeneralLinearGroup.scalar (Fin 2)

theorem map_scalar {B : Type} [CommRing B] (f : A →+* B) (c : Aˣ) :
    Matrix.GeneralLinearGroup.map f (sc c) = sc (Units.map (f : A →* B) c) := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem scalar_mul_comm {B : Type} [CommRing B] (c : Bˣ) (g : GL (Fin 2) B) : sc c * g = g * sc c := by
  refine Units.ext ?_
  change Matrix.scalar (Fin 2) (c : B) * (g : Matrix (Fin 2) (Fin 2) B) =
    (g : Matrix (Fin 2) (Fin 2) B) * Matrix.scalar (Fin 2) (c : B)
  exact (Matrix.scalar_commute (c : B) (fun r => Commute.all _ r) _).eq

theorem toTensorGL_scalar_mem_center (u : Aˣ) :
    AutomorphicForm.toTensorGL K L A (sc u) ∈ Subgroup.center (GL (Fin 2) (L ⊗[K] A)) := by
  rw [Subgroup.mem_center_iff]
  intro g
  unfold AutomorphicForm.toTensorGL
  rw [map_scalar]
  exact (scalar_mul_comm _ g).symm

theorem sigmaTensor_tmul (l : L) (a : A) :
    AutomorphicForm.sigmaTensor K L A σ (l ⊗ₜ a) = σ l ⊗ₜ a := by
  simp [AutomorphicForm.sigmaTensor]

theorem sigmaTensor_sigmaTensor (hσ : ∀ l : L, σ (σ l) = l) (t : L ⊗[K] A) :
    AutomorphicForm.sigmaTensor K L A σ (AutomorphicForm.sigmaTensor K L A σ t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul l a => rw [sigmaTensor_tmul, sigmaTensor_tmul, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem sigmaGL_sigmaGL (hσ : ∀ l : L, σ (σ l) = l) (g : GL (Fin 2) (L ⊗[K] A)) :
    AutomorphicForm.sigmaGL K L A σ (AutomorphicForm.sigmaGL K L A σ g) = g := by
  ext i j
  simp only [AutomorphicForm.sigmaGL, Matrix.GeneralLinearGroup.map_apply]
  exact sigmaTensor_sigmaTensor K L A σ hσ _

theorem normString_of_finrank_eq_two (h2 : Module.finrank K L = 2) (δ : GL (Fin 2) (L ⊗[K] A)) :
    AutomorphicForm.normString K L A σ δ = δ * AutomorphicForm.sigmaGL K L A σ δ := by
  unfold AutomorphicForm.normString
  rw [h2]
  simp [List.range_succ]

def tw (g y : GL (Fin 2) (L ⊗[K] A)) : GL (Fin 2) (L ⊗[K] A) :=
  g * y * (AutomorphicForm.sigmaGL K L A σ g)⁻¹

theorem tw_one (y : GL (Fin 2) (L ⊗[K] A)) : tw K L A σ 1 y = y := by
  simp [tw]

theorem tw_mul (g h y : GL (Fin 2) (L ⊗[K] A)) :
    tw K L A σ (g * h) y = tw K L A σ g (tw K L A σ h y) := by
  simp only [tw, map_mul, mul_inv_rev, mul_assoc]

theorem tw_inv_eq (x y : GL (Fin 2) (L ⊗[K] A)) :
    tw K L A σ x⁻¹ y = x⁻¹ * y * AutomorphicForm.sigmaGL K L A σ x := by
  simp only [tw, map_inv, inv_inv]

theorem tw_eq_self_iff (t δ : GL (Fin 2) (L ⊗[K] A)) :
    tw K L A σ t δ = δ ↔ t ∈ AutomorphicForm.twistedCentralizer K L A σ δ := by
  rw [AutomorphicForm.mem_sigmaCentralizer_iff]
  rfl

theorem tw_mul_sigmaGL_tw (hσ : ∀ l : L, σ (σ l) = l) (δ : GL (Fin 2) (L ⊗[K] A))
    (hz : δ * AutomorphicForm.sigmaGL K L A σ δ ∈ Subgroup.center (GL (Fin 2) (L ⊗[K] A)))
    (g : GL (Fin 2) (L ⊗[K] A)) :
    tw K L A σ g δ * AutomorphicForm.sigmaGL K L A σ (tw K L A σ g δ) =
      δ * AutomorphicForm.sigmaGL K L A σ δ := by
  set s := AutomorphicForm.sigmaGL K L A σ with hs
  have hss : s (s g) = g := sigmaGL_sigmaGL K L A σ hσ g
  have hcomm : g * (δ * s δ) = (δ * s δ) * g := (Subgroup.mem_center_iff.mp hz g)
  simp only [tw]
  rw [map_mul, map_mul, map_inv, hss]
  calc g * δ * (s g)⁻¹ * (s g * s δ * g⁻¹)
      = g * (δ * s δ) * g⁻¹ := by group
    _ = (δ * s δ) * g * g⁻¹ := by rw [hcomm]
    _ = δ * s δ := by rw [mul_inv_cancel_right]

end Algebra

section Adelic

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

local notation "𝔸" => AdeleRing (𝓞 K) K
local notation "GK" => GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)

theorem sigma_sigma (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (l : L) : σ (σ l) = l := by
  have hcard : Nat.card (L ≃ₐ[K] L) = 2 := (IsGalois.card_aut_eq_finrank K L).trans h2
  have hpow : σ ^ 2 = 1 := by rw [← hcard]; exact pow_card_eq_one'
  have := congrArg (fun τ : L ≃ₐ[K] L => τ l) hpow
  simpa [pow_two, AlgEquiv.mul_apply] using this

variable (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
  (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
  (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
  (hz : δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ δ ∈
    Subgroup.center (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))

def orbSet : Set GK := Set.range fun g : GK => tw K L 𝔸 σ g δ

def fibre : Set GK :=
  {y | y * AutomorphicForm.sigmaGL K L 𝔸 σ y = δ * AutomorphicForm.sigmaGL K L 𝔸 σ δ}

include h2 hgen hz in

theorem orbSet_eq_fibre : orbSet K L σ δ = fibre K L σ δ := by
  ext y
  constructor
  · rintro ⟨g, rfl⟩
    exact tw_mul_sigmaGL_tw K L 𝔸 σ (sigma_sigma K L h2 σ) δ hz g
  · intro hy
    have hδ : AutomorphicForm.normString K L 𝔸 σ δ ∈ Subgroup.center GK := by
      rw [normString_of_finrank_eq_two K L 𝔸 σ h2]; exact hz
    have hN : AutomorphicForm.normString K L 𝔸 σ y = AutomorphicForm.normString K L 𝔸 σ δ := by
      rw [normString_of_finrank_eq_two K L 𝔸 σ h2, normString_of_finrank_eq_two K L 𝔸 σ h2]
      exact hy
    obtain ⟨x, hx⟩ :=
      AutomorphicForm.isSigmaConjugate_adeleRing_of_normString_eq_of_normString_mem_center_of_finrank_eq_two
        K L h2 σ hgen δ y hδ hN
    refine ⟨x⁻¹, ?_⟩
    show tw K L 𝔸 σ x⁻¹ δ = y
    rw [tw_inv_eq, hx]

include h2 hgen hz in

theorem isClosed_orbSet : IsClosed (orbSet K L σ δ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L 𝔸
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L 𝔸
  haveI := AutomorphicForm.t2Space_tensorGL K L 𝔸
  rw [orbSet_eq_fibre K L h2 σ hgen δ hz]
  exact isClosed_eq (continuous_id.mul (continuous_sigmaGL K L 𝔸 σ)) continuous_const

abbrev Orb : Type := ↥(orbSet K L σ δ)

theorem tw_mem_orbSet (g : GK) {y : GK} (hy : y ∈ orbSet K L σ δ) : tw K L 𝔸 σ g y ∈ orbSet K L σ δ := by
  obtain ⟨h, rfl⟩ := hy
  exact ⟨g * h, tw_mul K L 𝔸 σ g h δ⟩

scoped instance instSMulOrb : SMul GK (Orb K L σ δ) :=
  ⟨fun g x => ⟨tw K L 𝔸 σ g x.1, tw_mem_orbSet K L σ δ g x.2⟩⟩

theorem smul_val (g : GK) (x : Orb K L σ δ) : ((g • x : Orb K L σ δ) : GK) = tw K L 𝔸 σ g x.1 := rfl

scoped instance instMulActionOrb : MulAction GK (Orb K L σ δ) where
  one_smul x := Subtype.ext (by rw [smul_val, tw_one])
  mul_smul g h x := Subtype.ext (by rw [smul_val, smul_val, smul_val, tw_mul])

theorem continuous_tw :
    Continuous fun p : GK × GK => tw K L 𝔸 σ p.1 p.2 := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L 𝔸
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L 𝔸
  unfold tw
  exact (continuous_fst.mul continuous_snd).mul ((continuous_sigmaGL K L 𝔸 σ).comp continuous_fst).inv

theorem continuous_pair_val :
    Continuous fun p : GK × Orb K L σ δ => ((p.1, (p.2 : GK)) : GK × GK) :=
  continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)

theorem continuous_tw_comp :
    Continuous ((fun p : GK × GK => tw K L 𝔸 σ p.1 p.2) ∘
      (fun p : GK × Orb K L σ δ => ((p.1, (p.2 : GK)) : GK × GK))) :=
  Continuous.comp (continuous_tw K L σ) (continuous_pair_val K L σ δ)

theorem continuous_tw_val :
    Continuous fun p : GK × Orb K L σ δ => tw K L 𝔸 σ p.1 (p.2 : GK) :=
  continuous_tw_comp K L σ δ

theorem continuous_smul_Orb : Continuous fun p : GK × Orb K L σ δ => p.1 • p.2 :=
  Continuous.subtype_mk (continuous_tw_val K L σ δ) fun p => tw_mem_orbSet K L σ δ p.1 p.2.2

scoped instance instContinuousSMulOrb : ContinuousSMul GK (Orb K L σ δ) := ⟨continuous_smul_Orb K L σ δ⟩

scoped instance instIsPretransitiveOrb : MulAction.IsPretransitive GK (Orb K L σ δ) where
  exists_smul_eq := by
    rintro ⟨_, ⟨a, rfl⟩⟩ ⟨_, ⟨b, rfl⟩⟩
    refine ⟨b * a⁻¹, Subtype.ext ?_⟩
    rw [smul_val]
    show tw K L 𝔸 σ (b * a⁻¹) (tw K L 𝔸 σ a δ) = tw K L 𝔸 σ b δ
    rw [← tw_mul, inv_mul_cancel_right]

def o₁ : Orb K L σ δ := ⟨δ, ⟨1, tw_one K L 𝔸 σ δ⟩⟩

theorem smul_o₁_val (g : GK) : ((g • o₁ K L σ δ : Orb K L σ δ) : GK) = tw K L 𝔸 σ g δ := rfl

theorem sigmaCompactSpace_GK : SigmaCompactSpace GK := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L 𝔸
  haveI := AutomorphicForm.t2Space_tensor K L 𝔸
  haveI := AutomorphicForm.locallyCompactSpace_tensor K L 𝔸
  haveI : SecondCountableTopology 𝔸 := NumberField.AdeleRing.secondCountableTopology K
  haveI := secondCountableTopology_tensor K L 𝔸
  haveI := secondCountableTopology_GL (L ⊗[K] 𝔸)
  haveI := locallyCompactSpace_GL (L ⊗[K] 𝔸)
  exact sigmaCompactSpace_of_locallyCompact_secondCountable

include h2 hgen hz in
theorem locallyCompactSpace_Orb : LocallyCompactSpace (Orb K L σ δ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L 𝔸
  haveI := AutomorphicForm.t2Space_tensor K L 𝔸
  haveI := AutomorphicForm.locallyCompactSpace_tensor K L 𝔸
  haveI := locallyCompactSpace_GL (L ⊗[K] 𝔸)
  exact (isClosed_orbSet K L h2 σ hgen δ hz).isClosedEmbedding_subtypeVal.locallyCompactSpace

include h2 hgen hz in
theorem baireSpace_Orb : BaireSpace (Orb K L σ δ) := by
  haveI := AutomorphicForm.t2Space_tensorGL K L 𝔸
  haveI := locallyCompactSpace_Orb K L h2 σ hgen δ hz
  exact BaireSpace.of_t2Space_locallyCompactSpace

include h2 hgen hz in

theorem isOpenMap_orbit : IsOpenMap fun g : GK => g • o₁ K L σ δ := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L 𝔸
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L 𝔸
  haveI := AutomorphicForm.t2Space_tensorGL K L 𝔸
  haveI := sigmaCompactSpace_GK K L
  haveI := baireSpace_Orb K L h2 σ hgen δ hz
  exact isOpenMap_smul_of_sigmaCompact (o₁ K L σ δ)

theorem surjective_orbit : Function.Surjective fun g : GK => g • o₁ K L σ δ := by
  intro x
  exact MulAction.exists_smul_eq GK (o₁ K L σ δ) x

include h2 hgen hz in
theorem main_of_mem_center (C : Set GK) (hC : IsCompact C) :
    ∃ D : Set GK, IsCompact D ∧
      {x : GK | x⁻¹ * δ * AutomorphicForm.sigmaGL K L 𝔸 σ x ∈ C} ⊆
        ((AutomorphicForm.twistedCentralizer K L 𝔸 σ δ : Subgroup GK) : Set GK) * D := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L 𝔸
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L 𝔸
  haveI := AutomorphicForm.t2Space_tensorGL K L 𝔸
  haveI := AutomorphicForm.t2Space_tensor K L 𝔸
  haveI := AutomorphicForm.locallyCompactSpace_tensor K L 𝔸
  haveI := locallyCompactSpace_GL (L ⊗[K] 𝔸)

  set T : Set (Orb K L σ δ) := Subtype.val ⁻¹' C with hT
  have hTc : IsCompact T :=
    (isClosed_orbSet K L h2 σ hgen δ hz).isClosedEmbedding_subtypeVal.isCompact_preimage hC

  obtain ⟨C₀, hC₀, hTC₀⟩ := exists_isCompact_subset_image (fun g : GK => g • o₁ K L σ δ)
    (isOpenMap_orbit K L h2 σ hgen δ hz) (surjective_orbit K L σ δ) hTc
  refine ⟨C₀⁻¹, hC₀.inv, ?_⟩
  intro x hx

  have hmem : (x⁻¹ • o₁ K L σ δ : Orb K L σ δ) ∈ T := by
    show ((x⁻¹ • o₁ K L σ δ : Orb K L σ δ) : GK) ∈ C
    rw [smul_o₁_val, tw_inv_eq]
    exact hx
  obtain ⟨k₀, hk₀, hk₀x⟩ := hTC₀ hmem

  have hval := congrArg (Subtype.val : Orb K L σ δ → GK) hk₀x
  simp only [] at hval
  rw [smul_o₁_val, smul_o₁_val] at hval
  have hstab : tw K L 𝔸 σ (x * k₀) δ = δ := by
    rw [tw_mul, hval, ← tw_mul, mul_inv_cancel, tw_one]
  refine Set.mem_mul.2 ⟨x * k₀, ?_, k₀⁻¹, Set.inv_mem_inv.mpr hk₀, mul_inv_cancel_right x k₀⟩
  exact (tw_eq_self_iff K L 𝔸 σ (x * k₀) δ).mp hstab

end Adelic

theorem main
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
    (C : Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) (hC : IsCompact C) :
    ∃ D : Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)), IsCompact D ∧
      {x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) |
          x⁻¹ *
              (Matrix.GeneralLinearGroup.map
                  (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
                Matrix.GeneralLinearGroup.scalar (Fin 2) c) *
            AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x ∈ C} ⊆
        ((AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
            (Matrix.GeneralLinearGroup.map
                (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
              Matrix.GeneralLinearGroup.scalar (Fin 2) c) :
            Subgroup (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) :
          Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) * D := by
  set δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) :=
    Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
      Matrix.GeneralLinearGroup.scalar (Fin 2) c with hδ

  have hz : δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ δ ∈
      Subgroup.center (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) := by
    rw [← normString_of_finrank_eq_two K L (AdeleRing (𝓞 K) K) σ h2, hN]
    exact toTensorGL_scalar_mem_center K L (AdeleRing (𝓞 K) K) u
  exact main_of_mem_center K L h2 σ hgen δ hz C hC

end P2mSecondKindProper
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isCompact_setOf_twistedConj_mem_subset_twistedCentralizer_mul_of_forall_ne_scalar_of_finrank_eq_two.P2mSecondKindProper"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isCompact_setOf_twistedConj_mem_subset_twistedCentralizer_mul_of_forall_ne_scalar_of_finrank_eq_two.P2mSecondKindProper"

open NumberField
open scoped TensorProduct TensorProduct.RightActions Pointwise

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (C : Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) (hC : IsCompact C) :
    ∃ D : Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)), IsCompact D ∧
      {x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) |
          x⁻¹ *
              (Matrix.GeneralLinearGroup.map
                  (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
                Matrix.GeneralLinearGroup.scalar (Fin 2) c) *
            AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x ∈ C} ⊆
        ((AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
            (Matrix.GeneralLinearGroup.map
                (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
              Matrix.GeneralLinearGroup.scalar (Fin 2) c) :
            Subgroup (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) :
          Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) * D :=
  P2mSecondKindProper.main K L h2 σ hgen δ₀ c u hN C hC

end S_AutomorphicForm_exists_isCompact_setOf_twistedConj_mem_subset_twistedCentralizer_mul_of_forall_ne_scalar_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_exists_isCompact_setOf_twistedConj_mem_subset_twistedCentralizer_mul_of_forall_ne_scalar_of_finrank_eq_two (solution)
