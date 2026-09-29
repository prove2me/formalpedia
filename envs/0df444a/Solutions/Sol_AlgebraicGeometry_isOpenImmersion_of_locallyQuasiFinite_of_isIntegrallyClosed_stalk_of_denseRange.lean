-- Prove2me | solution 1 for AlgebraicGeometry.isOpenImmersion_of_locallyQuasiFinite_of_isIntegrallyClosed_stalk_of_denseRange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/ad4bbab4-2378-5841-bf38-91632d02d7ae

import Mathlib
import Theorems.Thm_AlgebraicGeometry_IsIntegral_isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk
import Theorems.Thm_AlgebraicGeometry_isOpen_irreducibleComponent_of_isDomain_stalk
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isOpenImmersion_of_locallyQuasiFinite_of_isIntegrallyClosed_stalk_of_denseRange

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology Opposite

universe u

namespace P2mZmtBir534

section Algebra

theorem bijective_algebraMap_integralClosure {A C E K : Type*} [CommRing A] [CommRing C] [CommRing E]
    [Field K] [Algebra A C] [Algebra A K] [IsFractionRing A K] [IsIntegrallyClosed A]
    (φ : C →+* E) (hφ : Function.Injective φ) (ψ : E →+* K) (hψ : Function.Injective ψ)
    (hcomm : ∀ x : A, ψ (φ (algebraMap A C x)) = algebraMap A K x) :
    Function.Bijective (algebraMap A (integralClosure A C)) := by
  have hcomp : (ψ.comp φ).comp (algebraMap A C) = algebraMap A K := RingHom.ext hcomm
  constructor
  · intro x₁ x₂ h
    apply IsFractionRing.injective A K
    rw [← hcomm, ← hcomm]
    have h' : ((algebraMap A (integralClosure A C) x₁ : integralClosure A C) : C) =
        ((algebraMap A (integralClosure A C) x₂ : integralClosure A C) : C) := by rw [h]
    rw [Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap] at h'
    rw [h']
  · rintro ⟨c, hc⟩
    have hint : IsIntegral A (ψ (φ c)) := by
      obtain ⟨p, hp, hpc⟩ := hc
      refine ⟨p, hp, ?_⟩
      have h1 := congrArg (ψ.comp φ) hpc
      rw [Polynomial.hom_eval₂, hcomp, map_zero] at h1
      exact h1
    obtain ⟨a', ha'⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
    refine ⟨a', Subtype.ext ?_⟩
    rw [Subalgebra.coe_algebraMap]
    apply hφ
    apply hψ
    rw [hcomm, ha']

theorem exists_injective_of_away {A K L : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] [CommRing L] [Algebra A L] (a : A) (ha : a ≠ 0) [IsLocalization.Away a L] :
    ∃ ψ : L →+* K, Function.Injective ψ ∧ ∀ x, ψ (algebraMap A L x) = algebraMap A K x := by
  have hg : ∀ y : Submonoid.powers a, IsUnit (algebraMap A K y) := by
    rintro ⟨_, n, rfl⟩
    rw [isUnit_iff_ne_zero, map_pow]
    exact pow_ne_zero _ (fun h => ha ((IsFractionRing.to_map_eq_zero_iff (K := K)).mp h))
  refine ⟨IsLocalization.lift (M := Submonoid.powers a) hg, ?_, fun x => IsLocalization.lift_eq hg x⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨n, d⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers a) x
  simp only at hx ⊢
  rw [IsLocalization.lift_mk', mul_eq_zero] at hx
  rcases hx with hx | hx
  · rw [IsFractionRing.to_map_eq_zero_iff] at hx
    rw [hx, IsLocalization.mk'_zero]
  · exact absurd hx (Units.ne_zero _)

end Algebra

section Restrict

theorem map_injective_of_subset_closure {X : Scheme.{u}} [IsReduced X] {O O' : X.Opens} (h : O' ≤ O)
    (hd : (O : Set X) ⊆ closure (O' : Set X)) :
    Function.Injective (X.presheaf.map (homOfLE h).op) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 : X.basicOpen ((X.presheaf.map (homOfLE h).op) x) = O' ⊓ X.basicOpen x := X.basicOpen_res x _
  rw [hx, Scheme.basicOpen_zero] at h1
  have h2 : X.basicOpen x = ⊥ := by
    rw [eq_bot_iff]
    intro p hp
    have hpO : p ∈ (O : Set X) := X.basicOpen_le x hp
    have hcl := hd hpO
    rw [mem_closure_iff] at hcl
    obtain ⟨p', hp'1, hp'2⟩ := hcl _ (X.basicOpen x).isOpen hp
    have : p' ∈ (O' ⊓ X.basicOpen x : X.Opens) := ⟨hp'2, hp'1⟩
    rw [← h1] at this
    exact this
  exact (AlgebraicGeometry.basicOpen_eq_bot_iff x).mp h2

end Restrict

section SectionIso

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (s : (V : Scheme.{u}) ⟶ X) (hs : s ≫ f = V.ι)

include hs in
theorem range_s_subset : Set.range s.base ⊆ Set.range (f ⁻¹ᵁ V).ι.base := by
  rintro _ ⟨v, rfl⟩
  rw [Scheme.Opens.range_ι]
  change f (s v) ∈ V
  rw [← Scheme.Hom.comp_apply, hs, Scheme.Opens.ι_apply]
  exact v.2

def sL : (V : Scheme.{u}) ⟶ (f ⁻¹ᵁ V : Scheme.{u}) :=
  IsOpenImmersion.lift (f ⁻¹ᵁ V).ι s (range_s_subset f V s hs)

@[reassoc]
theorem sL_ι : sL f V s hs ≫ (f ⁻¹ᵁ V).ι = s := IsOpenImmersion.lift_fac _ _ _

theorem sL_restrict : sL f V s hs ≫ (f ∣_ V) = 𝟙 _ := by
  rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, sL_ι_assoc, hs, Category.id_comp]

scoped instance isClosedImmersion_sL [IsSeparated f] : IsClosedImmersion (sL f V s hs) := by
  have : IsClosedImmersion (sL f V s hs ≫ (f ∣_ V)) := by rw [sL_restrict]; infer_instance
  exact IsClosedImmersion.of_comp (sL f V s hs) (f ∣_ V)

theorem denseRange_sL (hsd : DenseRange s.base) : DenseRange (sL f V s hs).base := by
  have hemb : IsOpenEmbedding (f ⁻¹ᵁ V).ι.base := (f ⁻¹ᵁ V).ι.isOpenEmbedding
  have h1 : Set.range (sL f V s hs).base = (f ⁻¹ᵁ V).ι.base ⁻¹' Set.range s.base := by
    ext p
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨v, ?_⟩
      rw [← Scheme.Hom.comp_apply, sL_ι]
    · rintro ⟨v, hv⟩
      refine ⟨v, hemb.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, sL_ι]
      exact hv
  rw [DenseRange, h1]
  exact hsd.preimage hemb.isOpenMap

theorem surjective_sL [IsSeparated f] (hsd : DenseRange s.base) : Surjective (sL f V s hs) := by
  refine ⟨fun p => ?_⟩
  have hcl : IsClosed (Set.range (sL f V s hs).base) := (sL f V s hs).isClosedEmbedding.isClosed_range
  have : p ∈ closure (Set.range (sL f V s hs).base) := denseRange_sL f V s hs hsd p
  rw [hcl.closure_eq] at this
  exact this

theorem isIso_sL [IsSeparated f] [IsReduced X] (hsd : DenseRange s.base) : IsIso (sL f V s hs) := by
  haveI := surjective_sL f V s hs hsd
  exact isIso_of_isClosedImmersion_of_surjective _

include hs in

theorem isIso_app_s [IsSeparated f] [IsReduced X] (hsd : DenseRange s.base) (O : X.Opens)
    (hO : O ≤ f ⁻¹ᵁ V) : IsIso (s.app O) := by
  haveI := isIso_sL f V s hs hsd
  have hO' : O ≤ (f ⁻¹ᵁ V).ι.opensRange := by rwa [Scheme.Opens.opensRange_ι]
  haveI : IsIso ((f ⁻¹ᵁ V).ι.app O) := Scheme.Hom.isIso_app _ O hO'
  rw [Scheme.Hom.congr_app (sL_ι f V s hs).symm O, Scheme.Hom.comp_app]
  have i1 : IsIso ((sL f V s hs).app ((f ⁻¹ᵁ V).ι ⁻¹ᵁ O)) := inferInstance
  have i2 : IsIso ((f ⁻¹ᵁ V).ι.app O ≫ (sL f V s hs).app ((f ⁻¹ᵁ V).ι ⁻¹ᵁ O)) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ this i1
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ i2 inferInstance

end SectionIso

section IntegralNbhd

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y))

include hY in
theorem exists_affine_integral_nbhd (y : Y) (O : Y.Opens) (hy : y ∈ O) :
    ∃ W : Y.Opens, IsAffineOpen W ∧ y ∈ W ∧ W ≤ O ∧ IsIntegral (W : Scheme.{u}) := by
  have hopen : IsOpen (irreducibleComponent y) :=
    (AlgebraicGeometry.isOpen_irreducibleComponent_of_isDomain_stalk hY y).1
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWsub⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ irreducibleComponent y ∩ (O : Set Y) from ⟨mem_irreducibleComponent, hy⟩)
    (hopen.inter O.isOpen)
  refine ⟨W, hW, hyW, fun p hp => (hWsub hp).2, ?_⟩
  haveI : ∀ p : Y, _root_.IsReduced (Y.presheaf.stalk p) := fun p => inferInstance
  haveI : IsReduced Y := isReduced_of_isReduced_stalk Y
  have hirr : IsIrreducible ((W : Set Y)) :=
    ⟨⟨y, hyW⟩, isIrreducible_irreducibleComponent.isPreirreducible.open_subset W.isOpen
      (fun p hp => (hWsub hp).1)⟩
  haveI : IrreducibleSpace (W : Scheme.{u}) := isIrreducible_iff_irreducibleSpace.mp hirr
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end IntegralNbhd

section Local

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (s : (V : Scheme.{u}) ⟶ X)

theorem preimage_subset_closure (W D : Y.Opens) (hDW : D ≤ W) (hD : (D : Set Y).Nonempty)
    (hW : IsIrreducible (W : Set Y)) (hs : s ≫ f = V.ι) (hsd : DenseRange s.base) :
    ((f ⁻¹ᵁ W : X.Opens) : Set X) ⊆ closure ((f ⁻¹ᵁ D : X.Opens) : Set X) := by
  intro x hx
  rw [mem_closure_iff]
  intro N hN hxN

  let N' : Set X := N ∩ (f ⁻¹ᵁ W : X.Opens)
  have hN' : IsOpen N' := hN.inter (f ⁻¹ᵁ W).isOpen

  obtain ⟨_, ⟨v, rfl⟩, hvN'⟩ : (Set.range s.base ∩ N').Nonempty := by
    rw [Set.inter_comm]; exact hsd.inter_open_nonempty N' hN' ⟨x, hxN, hx⟩

  let M : Set Y := V.ι.base '' (s.base ⁻¹' N')
  have hMopen : IsOpen M := V.ι.isOpenEmbedding.isOpenMap _ (hN'.preimage s.base.hom.continuous)
  have hMW : M ⊆ (W : Set Y) := by
    rintro _ ⟨v', hv', rfl⟩
    have : f (s v') ∈ W := hv'.2
    rwa [← Scheme.Hom.comp_apply, hs] at this
  have hMne : ((W : Set Y) ∩ M).Nonempty := ⟨V.ι v, hMW ⟨v, hvN', rfl⟩, ⟨v, hvN', rfl⟩⟩
  have hDne : ((W : Set Y) ∩ D).Nonempty := by
    obtain ⟨d, hd⟩ := hD; exact ⟨d, hDW hd, hd⟩
  obtain ⟨_, -, ⟨v', hv'N', rfl⟩, hv'D⟩ := hW.isPreirreducible M D hMopen D.isOpen hMne hDne
  refine ⟨s v', hv'N'.1, ?_⟩
  change f (s v') ∈ D
  rwa [← Scheme.Hom.comp_apply, hs]

variable (hs : s ≫ f = V.ι) (W : Y.Opens) (D : Y.Opens) (hDW : D ≤ W)

def phi : Γ(X, f ⁻¹ᵁ W) ⟶ Γ(V, V.ι ⁻¹ᵁ D) :=
  s.appLE (f ⁻¹ᵁ W) (V.ι ⁻¹ᵁ D) (by
    rw [← Scheme.Hom.comp_preimage, hs]
    exact V.ι.preimage_mono hDW)

theorem app_phi : f.app W ≫ phi f V s hs W D hDW = V.ι.appLE W (V.ι ⁻¹ᵁ D) (V.ι.preimage_mono hDW) := by
  rw [phi, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  simp only [Scheme.Hom.appLE, Scheme.Hom.congr_app hs W, Category.assoc, ← Functor.map_comp]
  rfl

omit hs in
theorem map_app : Y.presheaf.map (homOfLE hDW).op ≫ V.ι.app D =
    V.ι.appLE W (V.ι ⁻¹ᵁ D) (V.ι.preimage_mono hDW) := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE]

omit hs in
theorem isIso_ιapp (hDV : D ≤ V) : IsIso (V.ι.app D) :=
  Scheme.Hom.isIso_app _ D (by rwa [Scheme.Opens.opensRange_ι])

theorem phi_injective [IsSeparated f] [IsReduced X] (hsd : DenseRange s.base) (hDV : D ≤ V)
    (hd : ((f ⁻¹ᵁ W : X.Opens) : Set X) ⊆ closure ((f ⁻¹ᵁ D : X.Opens) : Set X)) :
    Function.Injective (phi f V s hs W D hDW) := by
  have hle : f ⁻¹ᵁ D ≤ f ⁻¹ᵁ W := f.preimage_mono hDW
  have h1 : phi f V s hs W D hDW = X.presheaf.map (homOfLE hle).op ≫ s.appLE (f ⁻¹ᵁ D) (V.ι ⁻¹ᵁ D)
      (by rw [← Scheme.Hom.comp_preimage, hs]) := by
    rw [phi, Scheme.Hom.map_appLE]
  have h2 : s.appLE (f ⁻¹ᵁ D) (V.ι ⁻¹ᵁ D) (by rw [← Scheme.Hom.comp_preimage, hs]) =
      s.app (f ⁻¹ᵁ D) ≫ (V : Scheme.{u}).presheaf.map (homOfLE (by rw [← Scheme.Hom.comp_preimage, hs])).op :=
    rfl
  haveI : IsIso (s.app (f ⁻¹ᵁ D)) := isIso_app_s f V s hs hsd _ (f.preimage_mono hDV)
  haveI : IsIso ((V : Scheme.{u}).presheaf.map
      (homOfLE (show V.ι ⁻¹ᵁ D ≤ s ⁻¹ᵁ f ⁻¹ᵁ D by rw [← Scheme.Hom.comp_preimage, hs])).op) := by
    have heq : V.ι ⁻¹ᵁ D = s ⁻¹ᵁ f ⁻¹ᵁ D := by rw [← Scheme.Hom.comp_preimage, hs]
    have : homOfLE (show V.ι ⁻¹ᵁ D ≤ s ⁻¹ᵁ f ⁻¹ᵁ D by rw [← Scheme.Hom.comp_preimage, hs]) = eqToHom heq :=
      Subsingleton.elim _ _
    rw [this, eqToHom_op]
    infer_instance
  have h3 : Function.Injective (s.appLE (f ⁻¹ᵁ D) (V.ι ⁻¹ᵁ D) (by rw [← Scheme.Hom.comp_preimage, hs])) := by
    rw [h2]
    exact (asIso (s.app (f ⁻¹ᵁ D) ≫ (V : Scheme.{u}).presheaf.map (homOfLE _).op)).commRingCatIsoToRingEquiv.injective
  rw [h1]
  exact h3.comp (map_injective_of_subset_closure hle hd)

end Local

section Main

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [QuasiCompact f] [IsReduced X]
variable (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y))
variable (V : Y.Opens) (hV : Dense (V : Set Y))
variable (s : (V : Scheme.{u}) ⟶ X) (hs : s ≫ f = V.ι) (hsd : DenseRange s.base)

include hY hV hs hsd in

theorem isIso_fromNormalization_app (W : Y.Opens) (hW : IsAffineOpen W) [IsIntegral (W : Scheme.{u})]
    (hWne : ((W : Set Y)).Nonempty) : IsIso (f.fromNormalization.app W) := by
  haveI : IsAffine (W : Scheme.{u}) := hW

  have hst : ∀ x : (W : Scheme.{u}), IsIntegrallyClosed ((W : Scheme.{u}).presheaf.stalk x) := fun x =>
    @IsIntegrallyClosed.of_equiv _ _ _ _ (asIso (W.ι.stalkMap x)).commRingCatIsoToRingEquiv (hY _).2
  have hIC0 : IsIntegrallyClosed Γ(↑W, ⊤) :=
    AlgebraicGeometry.IsIntegral.isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk hst ⊤
      (isAffineOpen_top _)
  haveI hIC : IsIntegrallyClosed Γ(Y, W) :=
    @IsIntegrallyClosed.of_equiv _ _ _ _ W.topIso.commRingCatIsoToRingEquiv hIC0
  haveI hdom : IsDomain Γ(Y, W) := MulEquiv.isDomain Γ(↑W, ⊤) W.topIso.symm.commRingCatIsoToRingEquiv.toMulEquiv

  obtain ⟨y₀, hy₀W, hy₀V⟩ := hV.inter_open_nonempty _ W.isOpen hWne
  obtain ⟨a, haV, hy₀a⟩ := hW.exists_basicOpen_le ⟨y₀, hy₀V⟩ hy₀W
  have ha : a ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hy₀a
    exact hy₀a
  set D := Y.basicOpen a with hD
  have hDW : D ≤ W := Y.basicOpen_le a

  have hWirr : IsIrreducible ((W : Set Y)) :=
    isIrreducible_iff_irreducibleSpace.mpr (by exact (inferInstance : IrreducibleSpace (W : Scheme.{u})))
  have hd := preimage_subset_closure f V s W D hDW ⟨y₀, hy₀a⟩ hWirr hs hsd

  letI := (f.app W).hom.toAlgebra
  have hφ := phi_injective f V s hs W D hDW hsd haV hd
  haveI := hW.isLocalization_basicOpen a
  obtain ⟨ψ₀, hψ₀, hψ₀c⟩ := exists_injective_of_away (A := Γ(Y, W)) (K := FractionRing Γ(Y, W))
    (L := Γ(Y, Y.basicOpen a)) a ha
  haveI hιD : IsIso (V.ι.app D) := isIso_ιapp V D haV
  let ψ : Γ(V, V.ι ⁻¹ᵁ D) →+* FractionRing Γ(Y, W) := ψ₀.comp (inv (V.ι.app D)).hom
  have hψ : Function.Injective ψ :=
    hψ₀.comp (asIso (inv (V.ι.app D))).commRingCatIsoToRingEquiv.injective
  have hcomm : ∀ x : Γ(Y, W), ψ ((phi f V s hs W D hDW).hom (algebraMap Γ(Y, W) Γ(X, f ⁻¹ᵁ W) x)) =
      algebraMap Γ(Y, W) (FractionRing Γ(Y, W)) x := by
    intro x
    have h1 : (phi f V s hs W D hDW).hom (algebraMap Γ(Y, W) Γ(X, f ⁻¹ᵁ W) x) =
        (f.app W ≫ phi f V s hs W D hDW).hom x := rfl
    rw [h1, app_phi, ← map_app V W D hDW]
    change ψ₀ ((Y.presheaf.map (homOfLE hDW).op ≫ V.ι.app D ≫ inv (V.ι.app D)).hom x) = _
    rw [IsIso.hom_inv_id, Category.comp_id]
    exact hψ₀c x
  have hbij := bijective_algebraMap_integralClosure (phi f V s hs W D hDW).hom hφ ψ hψ hcomm
  rw [f.fromNormalization_app hW]
  have : IsIso (CommRingCat.ofHom (algebraMap ↑(Y.presheaf.obj (op W))
      ↥(integralClosure ↑Γ(Y, W) ↑Γ(X, f ⁻¹ᵁ W)))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ this inferInstance

include hY hV hs hsd in
theorem isIso_fromNormalization [IsLocallyNoetherian Y] : IsIso f.fromNormalization := by
  have hdom : ∀ y : Y, IsDomain (Y.presheaf.stalk y) := fun y => (hY y).1
  choose W hW hyW _ hWint using fun y : Y => exists_affine_integral_nbhd hdom y ⊤ trivial
  have hcover : ⨆ y, ((⟨W y, hW y⟩ : Y.affineOpens) : Y.Opens) = ⊤ :=
    top_le_iff.mp fun y _ => Opens.mem_iSup.mpr ⟨y, hyW y⟩
  rw [← MorphismProperty.isomorphisms.iff,
    HasAffineProperty.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
      (fun y => (⟨W y, hW y⟩ : Y.affineOpens)) hcover]
  intro y
  refine ⟨IsAffineHom.isAffine_preimage (W y) (hW y), ?_⟩
  rw [morphismRestrict_appTop]
  haveI := hWint y
  have h1 : IsIso (f.fromNormalization.app ((W y).ι ''ᵁ ⊤)) := by
    rw [Scheme.Opens.ι_image_top]
    exact isIso_fromNormalization_app f hY V hV s hs hsd (W y) (hW y) ⟨y, hyW y⟩
  have h2 : ∀ {O O' : f.normalization.Opens} (e : O = O'),
      IsIso (f.normalization.presheaf.map (eqToHom e).op) := by
    intro O O' e; subst e; simp only [eqToHom_refl, op_id]; infer_instance
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 (h2 _)

include hY hV hs hsd in

theorem isOpenImmersion [IsLocallyNoetherian Y] [LocallyQuasiFinite f] [LocallyOfFiniteType f] :
    IsOpenImmersion f := by
  haveI := isIso_fromNormalization f hY V hV s hs hsd
  rw [← f.toNormalization_fromNormalization]
  infer_instance

end Main

end P2mZmtBir534
p2m_reactivate "P2MW.S_AlgebraicGeometry_isOpenImmersion_of_locallyQuasiFinite_of_isIntegrallyClosed_stalk_of_denseRange.P2mZmtBir534"

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsReduced X] [IsLocallyNoetherian Y]
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y))
    (V : Y.Opens) (hV : Dense (V : Set Y))
    (s : (V : Scheme.{u}) ⟶ X) (hs : s ≫ f = V.ι) (hsd : DenseRange s.base) :
    IsOpenImmersion f :=
  P2mZmtBir534.isOpenImmersion f hY V hV s hs hsd

end
end S_AlgebraicGeometry_isOpenImmersion_of_locallyQuasiFinite_of_isIntegrallyClosed_stalk_of_denseRange
end P2MW
export P2MW.S_AlgebraicGeometry_isOpenImmersion_of_locallyQuasiFinite_of_isIntegrallyClosed_stalk_of_denseRange (solution)
