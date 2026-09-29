-- Prove2me | solution 1 for AutomorphicForm.isFactorizableTestFn_chiDet_mul_of_continuous_of_isOfFinOrder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/90de7c25-db68-55e1-ae4c-4c6d132cb7d8

import Mathlib
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isFactorizableTestFn_chiDet_mul_of_continuous_of_isOfFinOrder

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open scoped Manifold ContDiff

noncomputable section

namespace P2mS28CB

theorem isLocallyConstant_of_continuous_of_finite_range {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T1Space Y] {f : X → Y} (hc : Continuous f) (hfin : (Set.range f).Finite) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro y
  have h : f ⁻¹' {y} = (f ⁻¹' (Set.range f \ {y}))ᶜ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_diff, Set.mem_range_self,
      true_and, not_not]
  rw [h, isOpen_compl_iff]
  exact ((hfin.subset Set.diff_subset).isClosed).preimage hc

theorem finite_range_coe_of_isOfFinOrder {G : Type*} [Group G] (η : G →* ℂˣ) (ho : IsOfFinOrder η) :
    (Set.range (fun x => ((η x : ℂˣ) : ℂ))).Finite := by
  obtain ⟨n, hn, hηn⟩ := (isOfFinOrder_iff_pow_eq_one).mp ho
  refine (Polynomial.nthRoots n (1 : ℂ)).toFinset.finite_toSet.subset ?_
  rintro _ ⟨x, rfl⟩
  change ((η x : ℂˣ) : ℂ) ∈ (((Polynomial.nthRoots n (1 : ℂ)).toFinset) : Set ℂ)
  rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hn, ← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hηn,
    MonoidHom.one_apply, Units.val_one]

theorem isLocallyConstant_coe_of_isOfFinOrder {G : Type*} [Group G] [TopologicalSpace G] (η : G →* ℂˣ)
    (hc : Continuous η) (ho : IsOfFinOrder η) : IsLocallyConstant (fun x => ((η x : ℂˣ) : ℂ)) :=
  isLocallyConstant_of_continuous_of_finite_range (Units.continuous_val.comp hc) (finite_range_coe_of_isOfFinOrder η ho)

theorem isOfFinOrder_comp {G H : Type*} [Group G] [Group H] (η : G →* ℂˣ) (ho : IsOfFinOrder η) (φ : H →* G) :
    IsOfFinOrder (η.comp φ) := by
  obtain ⟨n, hn, hηn⟩ := (isOfFinOrder_iff_pow_eq_one).mp ho
  refine (isOfFinOrder_iff_pow_eq_one).mpr ⟨n, hn, ?_⟩
  ext x
  rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, hηn, MonoidHom.one_apply, MonoidHom.one_apply]

variable (F : Type) [Field F] [NumberField F]

def etaArch (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) : (InfiniteAdeleRing F)ˣ →* ℂˣ :=
  (η.comp (MulEquiv.prodUnits.symm : (InfiniteAdeleRing F)ˣ × (FiniteAdeleRing (𝓞 F) F)ˣ ≃* (AdeleRing (𝓞 F) F)ˣ).toMonoidHom).comp
    (MonoidHom.inl _ _)

def etaFin (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) : (FiniteAdeleRing (𝓞 F) F)ˣ →* ℂˣ :=
  (η.comp (MulEquiv.prodUnits.symm : (InfiniteAdeleRing F)ˣ × (FiniteAdeleRing (𝓞 F) F)ˣ ≃* (AdeleRing (𝓞 F) F)ˣ).toMonoidHom).comp
    (MonoidHom.inr _ _)

theorem eta_eq_etaArch_mul_etaFin (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (u : (AdeleRing (𝓞 F) F)ˣ) :
    η u = etaArch F η (Units.map (MonoidHom.fst _ _) u) * etaFin F η (Units.map (MonoidHom.snd _ _) u) := by
  set s : (InfiniteAdeleRing F)ˣ × (FiniteAdeleRing (𝓞 F) F)ˣ ≃* (AdeleRing (𝓞 F) F)ˣ := MulEquiv.prodUnits.symm with hs
  have hR : etaArch F η (Units.map (MonoidHom.fst _ _) u) * etaFin F η (Units.map (MonoidHom.snd _ _) u) =
      η (s (Units.map (MonoidHom.fst _ _) u, 1)) * η (s (1, Units.map (MonoidHom.snd _ _) u)) := rfl
  rw [hR, ← map_mul η, ← map_mul s, Prod.mk_mul_mk, mul_one, one_mul]
  exact congrArg η (MulEquiv.symm_apply_apply MulEquiv.prodUnits u).symm

theorem isOfFinOrder_etaArch {η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (ho : IsOfFinOrder η) : IsOfFinOrder (etaArch F η) := by
  obtain ⟨n, hn, hηn⟩ := (isOfFinOrder_iff_pow_eq_one).mp ho
  refine (isOfFinOrder_iff_pow_eq_one).mpr ⟨n, hn, MonoidHom.ext fun a => ?_⟩
  rw [MonoidHom.pow_apply, MonoidHom.one_apply]
  show (η _) ^ n = 1
  rw [← MonoidHom.pow_apply, hηn, MonoidHom.one_apply]

theorem isOfFinOrder_etaFin {η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (ho : IsOfFinOrder η) : IsOfFinOrder (etaFin F η) := by
  obtain ⟨n, hn, hηn⟩ := (isOfFinOrder_iff_pow_eq_one).mp ho
  refine (isOfFinOrder_iff_pow_eq_one).mpr ⟨n, hn, MonoidHom.ext fun a => ?_⟩
  rw [MonoidHom.pow_apply, MonoidHom.one_apply]
  show (η _) ^ n = 1
  rw [← MonoidHom.pow_apply, hηn, MonoidHom.one_apply]

theorem continuous_etaArch {η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hc : Continuous η) : Continuous (etaArch F η) := by
  have h1 : Continuous (fun a : (InfiniteAdeleRing F)ˣ => (a, (1 : (FiniteAdeleRing (𝓞 F) F)ˣ))) :=
    continuous_id.prodMk continuous_const
  have h2 : Continuous (MulEquiv.prodUnits.symm : (InfiniteAdeleRing F)ˣ × (FiniteAdeleRing (𝓞 F) F)ˣ ≃* (AdeleRing (𝓞 F) F)ˣ) :=
    (Homeomorph.prodUnits (α := InfiniteAdeleRing F) (β := FiniteAdeleRing (𝓞 F) F)).symm.continuous
  exact hc.comp (h2.comp h1)

theorem continuous_etaFin {η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hc : Continuous η) : Continuous (etaFin F η) := by
  have h1 : Continuous (fun b : (FiniteAdeleRing (𝓞 F) F)ˣ => ((1 : (InfiniteAdeleRing F)ˣ), b)) :=
    continuous_const.prodMk continuous_id
  have h2 : Continuous (MulEquiv.prodUnits.symm : (InfiniteAdeleRing F)ˣ × (FiniteAdeleRing (𝓞 F) F)ˣ ≃* (AdeleRing (𝓞 F) F)ˣ) :=
    (Homeomorph.prodUnits (α := InfiniteAdeleRing F) (β := FiniteAdeleRing (𝓞 F) F)).symm.continuous
  exact hc.comp (h2.comp h1)

theorem chiDet_eq (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) :
    chiDet (𝓞 F) F η g =
      ((etaArch F η (Matrix.GeneralLinearGroup.det (AdelicLevel.glArch (𝓞 F) F g)) : ℂˣ) : ℂ) *
        ((etaFin F η (Matrix.GeneralLinearGroup.det (AdelicLevel.glFin (𝓞 F) F g)) : ℂˣ) : ℂ) := by
  unfold chiDet
  rw [eta_eq_etaArch_mul_etaFin, Units.val_mul]
  have ha := Matrix.GeneralLinearGroup.map_det (AdelicLevel.adeleArch (𝓞 F) F) g
  have hf := Matrix.GeneralLinearGroup.map_det (AdelicLevel.adeleFin (𝓞 F) F) g
  rw [show Matrix.GeneralLinearGroup.map (AdelicLevel.adeleArch (𝓞 F) F) = AdelicLevel.glArch (𝓞 F) F from rfl] at ha
  rw [show Matrix.GeneralLinearGroup.map (AdelicLevel.adeleFin (𝓞 F) F) = AdelicLevel.glFin (𝓞 F) F from rfl] at hf
  rw [ha, hf]
  rfl

theorem isFinTestFactor_mul {c : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ} (hc : IsLocallyConstant c)
    {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ} (hff : IsFinTestFactor F ff) :
    IsFinTestFactor F (fun k => c k * ff k) :=
  ⟨hc.mul hff.1, hff.2.mul_left⟩

theorem continuous_ringEquiv_mixedSpace : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  show Continuous fun x : InfiniteAdeleRing F => InfiniteAdeleRing.ringEquiv_mixedSpace F x
  simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  exact (continuous_pi fun v => (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply _)).prodMk
    (continuous_pi fun v => (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _))

theorem continuous_archEntries : Continuous (archEntries F) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_ringEquiv_mixedSpace F).comp (Units.continuous_val.matrix_elem i j)

theorem injective_archEntries : Function.Injective (archEntries F) := by
  intro g g' h
  apply Units.ext
  ext i j
  have hij := congrFun (congrFun h i) j
  simp only [archEntries_apply] at hij
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective hij

theorem isArchTestFactor_mul {c : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (hc : IsLocallyConstant c)
    {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (hfa : IsArchTestFactor F fa) :
    IsArchTestFactor F (fun k => c k * fa k) := by
  classical
  obtain ⟨⟨Φ, hΦ, hfaΦ⟩, hK⟩ := hfa
  refine ⟨?_, hK.mul_left⟩

  let e : GL (Fin 2) (InfiniteAdeleRing F) → (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) := archEntries F
  have he : e = archEntries F := rfl
  set K : Set (GL (Fin 2) (InfiniteAdeleRing F)) := tsupport fa with hKdef
  have hKc : IsCompact K := hK

  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  set cK : K → ℂ := fun x => c x.1 with hcK
  have hJ : (Set.range cK).Finite := (hc.comp_continuous continuous_subtype_val).range_finite
  set J : Finset ℂ := hJ.toFinset with hJdef

  set Kp : ℂ → Set (GL (Fin 2) (InfiniteAdeleRing F)) := fun ζ => K ∩ c ⁻¹' {ζ} with hKp
  have hKpc : ∀ ζ, IsCompact (Kp ζ) := fun ζ => hKc.inter_right (hc.isClosed_fiber ζ)
  set S : ℂ → Set (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) := fun ζ => e '' Kp ζ with hS
  have hSc : ∀ ζ, IsClosed (S ζ) := fun ζ => ((hKpc ζ).image (continuous_archEntries F)).isClosed
  set T : ℂ → Set (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) := fun ζ => ⋃ ζ' ∈ (J.erase ζ), S ζ' with hT
  have hTc : ∀ ζ, IsClosed (T ζ) := fun ζ => by
    refine Set.Finite.isClosed_biUnion (J.erase ζ).finite_toSet fun ζ' _ => hSc ζ'
  have hdisj : ∀ ζ, Disjoint (T ζ) (S ζ) := by
    intro ζ
    rw [Set.disjoint_left]
    rintro m hm ⟨g, ⟨hgK, hgc⟩, rfl⟩
    simp only [hT, Set.mem_iUnion] at hm
    obtain ⟨ζ', hζ', ⟨g', ⟨hg'K, hg'c⟩, hgg'⟩⟩ := hm
    have : g' = g := injective_archEntries F hgg'
    subst this
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hgc hg'c
    exact (Finset.mem_erase.mp hζ').1 (hg'c.symm.trans hgc)

  have hθ : ∀ ζ : ℂ, ∃ θ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) θ ∧ Set.EqOn θ 0 (T ζ) ∧ Set.EqOn θ 1 (S ζ) := by
    intro ζ
    obtain ⟨f, hf0, hf1, -⟩ := exists_contMDiffMap_zero_one_of_isClosed (n := (⊤ : ℕ∞))
      𝓘(ℝ, Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) (hTc ζ) (hSc ζ) (hdisj ζ)
    exact ⟨f, contMDiff_iff_contDiff.mp f.contMDiff, hf0, hf1⟩
  choose θ hθs hθ0 hθ1 using hθ

  refine ⟨fun m => (∑ ζ ∈ J, ζ * (θ ζ m : ℂ)) * Φ m, ?_, fun g => ?_⟩
  · refine ContDiff.mul (ContDiff.sum fun ζ _ => contDiff_const.mul ?_) hΦ
    exact Complex.ofRealCLM.contDiff.comp (hθs ζ)
  · show c g * fa g = (∑ ζ ∈ J, ζ * (θ ζ (archEntries F g) : ℂ)) * Φ (archEntries F g)
    by_cases hg : fa g = 0
    · rw [hg, mul_zero, ← hfaΦ g, hg, mul_zero]
    · have hgK : g ∈ K := subset_tsupport _ (Function.mem_support.mpr hg)
      have hζ₀ : c g ∈ J := by
        rw [hJdef, Set.Finite.mem_toFinset]
        exact ⟨⟨g, hgK⟩, rfl⟩
      have hgS : e g ∈ S (c g) := ⟨g, ⟨hgK, rfl⟩, rfl⟩
      have hsum : (∑ ζ ∈ J, ζ * (θ ζ (e g) : ℂ)) = c g := by
        rw [Finset.sum_eq_single (c g)]
        · rw [hθ1 (c g) hgS, Pi.one_apply, Complex.ofReal_one, mul_one]
        · intro ζ hζJ hζne
          have hgT : e g ∈ T ζ := by
            simp only [hT, Set.mem_iUnion]
            exact ⟨c g, Finset.mem_erase.mpr ⟨hζne.symm, hζ₀⟩, hgS⟩
          rw [hθ0 ζ hgT, Pi.zero_apply, Complex.ofReal_zero, mul_zero]
        · intro h
          exact absurd hζ₀ h
      rw [← he, hsum, ← hfaΦ g]

end P2mS28CB

end

open P2mS28CB in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hηc : Continuous η) (hηo : IsOfFinOrder η)
    (f : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ) (hf : IsFactorizableTestFn F f) :
    IsFactorizableTestFn F (fun g => chiDet (𝓞 F) F η g * f g) := by
  obtain ⟨fa, ff, hfa, hff, hf⟩ := hf
  refine ⟨fun k => ((etaArch F η (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) * fa k,
    fun k => ((etaFin F η (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) * ff k, ?_, ?_, fun g => ?_⟩
  · refine isArchTestFactor_mul F ?_ hfa
    exact (isLocallyConstant_coe_of_isOfFinOrder (etaArch F η) (continuous_etaArch F hηc)
      (isOfFinOrder_etaArch F hηo)).comp_continuous Matrix.GeneralLinearGroup.continuous_det
  · refine isFinTestFactor_mul F ?_ hff
    exact (isLocallyConstant_coe_of_isOfFinOrder (etaFin F η) (continuous_etaFin F hηc)
      (isOfFinOrder_etaFin F hηo)).comp_continuous Matrix.GeneralLinearGroup.continuous_det
  · show chiDet (𝓞 F) F η g * f g =
      (((etaArch F η (Matrix.GeneralLinearGroup.det (AdelicLevel.glArch (𝓞 F) F g)) : ℂˣ) : ℂ) * fa (AdelicLevel.glArch (𝓞 F) F g)) *
        ((((etaFin F η (Matrix.GeneralLinearGroup.det (AdelicLevel.glFin (𝓞 F) F g)) : ℂˣ) : ℂ) * ff (AdelicLevel.glFin (𝓞 F) F g)))
    rw [hf g, chiDet_eq]
    ring

end S_AutomorphicForm_isFactorizableTestFn_chiDet_mul_of_continuous_of_isOfFinOrder
end P2MW
export P2MW.S_AutomorphicForm_isFactorizableTestFn_chiDet_mul_of_continuous_of_isOfFinOrder (solution)
