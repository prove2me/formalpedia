-- Prove2me | solution 1 for AlgebraicGeometry.exists_etale_isPullback_forall_existsUnique_comp_eq_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/0ee8ead1-57e1-5e76-9b27-40dce440fb50

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Etale_existsUnique_comp_eq_of_isNilpotent_ker
import Theorems.Thm_AlgebraicGeometry_Etale_exists_opens_etale_isPullback_of_isClosedImmersion
import Theorems.Thm_AlgebraicGeometry_isPullback_of_iSup_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_etale_isPullback_forall_existsUnique_comp_eq_of_isNilpotent

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

section Bridge
open TopologicalSpace Opposite

namespace S2BRIDGE

theorem ofIdealTop_pow {X : Scheme.{0}} (I : Ideal Γ(X, ⊤)) (n : ℕ) :
    (Scheme.IdealSheafData.ofIdealTop I) ^ n = Scheme.IdealSheafData.ofIdealTop (I ^ n) := by
  ext U
  simp [Ideal.map_pow]

theorem isNilpotent_of_le_ofIdealTop {X : Scheme.{0}} (K : X.IdealSheafData) (I : Ideal Γ(X, ⊤))
    (hKI : K ≤ Scheme.IdealSheafData.ofIdealTop I) (hI : IsNilpotent I) : IsNilpotent K := by
  obtain ⟨n, hn⟩ := hI
  refine ⟨n, le_bot_iff.mp ?_⟩
  calc K ^ n ≤ (Scheme.IdealSheafData.ofIdealTop I) ^ n := pow_le_pow_left' hKI n
    _ = Scheme.IdealSheafData.ofIdealTop (I ^ n) := ofIdealTop_pow I n
    _ = ⊥ := by rw [hn]; ext U; simp

theorem subschemeι_appTop_eq_zero {X : Scheme.{0}} (I : Ideal Γ(X, ⊤)) (x : Γ(X, ⊤)) (hx : x ∈ I) :
    (Scheme.IdealSheafData.ofIdealTop I).subschemeι.appTop x = 0 := by
  set K := Scheme.IdealSheafData.ofIdealTop I
  set Z := K.subscheme

  refine TopCat.Sheaf.eq_of_locally_eq' Z.sheaf (fun U : X.affineOpens => K.subschemeι ⁻¹ᵁ (U : X.Opens)) ⊤
    (fun U => homOfLE le_top) ?_ _ _ fun U => ?_
  · intro z _
    obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (K.subschemeι.base z)) isOpen_univ
    exact Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hzU⟩
  · have e : K.subschemeι.app ⊤ ≫ Z.presheaf.map (homOfLE (le_top : K.subschemeι ⁻¹ᵁ (U : X.Opens) ≤ ⊤)).op =
        X.presheaf.map (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op ≫ K.subschemeι.app U := by
      rw [Scheme.Hom.naturality]; rfl
    have lhs : (K.subschemeι.app ⊤ ≫ Z.presheaf.map (homOfLE (le_top : K.subschemeι ⁻¹ᵁ (U : X.Opens) ≤ ⊤)).op).hom x = 0 := by
      rw [e, CommRingCat.hom_comp, RingHom.comp_apply, ← RingHom.mem_ker, Scheme.IdealSheafData.ker_subschemeι_app]
      simp only [K, Scheme.IdealSheafData.ofIdealTop_ideal]
      exact Ideal.mem_map_of_mem _ hx
    have rhs : (Z.presheaf.map (homOfLE (le_top : K.subschemeι ⁻¹ᵁ (U : X.Opens) ≤ ⊤)).op).hom 0 = 0 := map_zero _
    exact lhs.trans rhs.symm

theorem isNilpotent_ker_pullback_fst (C : Type) [CommRing C] (J : Ideal C) (hJ : IsNilpotent J)
    {W : Scheme.{0}} (g : W ⟶ Spec (CommRingCat.of C)) :
    IsNilpotent (pullback.fst g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).ker := by
  set i : Spec (CommRingCat.of (C ⧸ J)) ⟶ Spec (CommRingCat.of C) := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))

  let ρW : C →+* Γ(W, ⊤) := g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom
  let K : W.IdealSheafData := Scheme.IdealSheafData.ofIdealTop (J.map ρW)
  have hKn : IsNilpotent (J.map ρW) := by
    obtain ⟨n, hn⟩ := hJ; exact ⟨n, by rw [← Ideal.map_pow, hn]; simp⟩

  let ρ₀ : C →+* Γ(K.subscheme, ⊤) := K.subschemeι.appTop.hom.comp ρW
  have hρ₀ : ∀ c ∈ J, ρ₀ c = 0 := fun c hc =>
    subschemeι_appTop_eq_zero (J.map ρW) (ρW c) (Ideal.mem_map_of_mem _ hc)
  let ρ : C ⧸ J →+* Γ(K.subscheme, ⊤) := Ideal.Quotient.lift J ρ₀ hρ₀
  let m' : K.subscheme ⟶ Spec (CommRingCat.of (C ⧸ J)) := K.subscheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ρ)
  have hR : Spec.map (CommRingCat.ofHom ρ) ≫ i = Spec.map (CommRingCat.ofHom ρ₀) := by
    have : ρ.comp (Ideal.Quotient.mk J) = ρ₀ := RingHom.ext fun c => Ideal.Quotient.lift_mk J ρ₀ hρ₀
    rw [← this, CommRingCat.ofHom_comp, Spec.map_comp]
  have hL : K.subschemeι ≫ g = K.subscheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ρ₀) := by
    have nat := Scheme.toSpecΓ_naturality (K.subschemeι ≫ g)
    rw [← SpecMap_ΓSpecIso_hom] at nat
    have e1 : K.subschemeι ≫ g = ((K.subschemeι ≫ g) ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of C)).hom) ≫
        Spec.map (Scheme.ΓSpecIso (CommRingCat.of C)).inv := by
      rw [Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
    rw [e1, nat, Category.assoc, ← Spec.map_comp, Scheme.Hom.comp_appTop]
    rfl
  have w : K.subschemeι ≫ g = m' ≫ i := by
    rw [hL, Category.assoc]
    exact congrArg (K.subscheme.toSpecΓ ≫ ·) hR.symm
  let m : K.subscheme ⟶ pullback g i := pullback.lift K.subschemeι m' w
  have hle : (pullback.fst g i).ker ≤ K := by
    calc (pullback.fst g i).ker ≤ (m ≫ pullback.fst g i).ker := Scheme.Hom.le_ker_comp _ _
      _ = K.subschemeι.ker := by rw [pullback.lift_fst]
      _ = K := K.ker_subschemeι
  exact isNilpotent_of_le_ofIdealTop _ _ hle hKn

theorem isNilpotent_ker_specMap_mk (B : Type) [CommRing B] (I : Ideal B) (hI : IsNilpotent I) :
    IsNilpotent (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker := by
  rw [Scheme.ker_of_isAffine]
  apply isNilpotent_of_le_ofIdealTop _ (I.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom) ?_ ?_
  · apply le_of_eq; congr 1
    ext x
    constructor
    · intro hx
      have hx' : (Scheme.ΓSpecIso (CommRingCat.of (B ⧸ I))).hom ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop x) = 0 := by
        rw [RingHom.mem_ker.mp hx, map_zero]
      rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply] at hx'
      have : x = (Scheme.ΓSpecIso (CommRingCat.of B)).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).hom x) := by
        rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
      rw [this]
      exact Ideal.mem_map_of_mem _ (Ideal.Quotient.eq_zero_iff_mem.mp hx')
    · intro hx
      refine Ideal.map_le_iff_le_comap.mpr (fun b hb => ?_) hx
      rw [Ideal.mem_comap, RingHom.mem_ker, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
        CommRingCat.comp_apply]
      change (Scheme.ΓSpecIso (CommRingCat.of (B ⧸ I))).inv (Ideal.Quotient.mk I b) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hb, map_zero]
  · obtain ⟨n, hn⟩ := hI; exact ⟨n, by rw [← Ideal.map_pow, hn]; simp⟩

end S2BRIDGE

end Bridge

namespace Sigma2

theorem sect {X Y T T₀ : Scheme.{0}} (q : Y ⟶ X) [Etale q] (k : T₀ ⟶ T) [IsClosedImmersion k]
    (hk : IsNilpotent k.ker) (t : T ⟶ X) (s₀ : T₀ ⟶ Y) (hs₀ : s₀ ≫ q = k ≫ t) :
    ∃! s : T ⟶ Y, s ≫ q = t ∧ k ≫ s = s₀ :=
  AlgebraicGeometry.Etale.existsUnique_comp_eq_of_isNilpotent_ker q k hk t s₀ hs₀

theorem locex {X X₀ Y₀ : Scheme.{0}} (i : X₀ ⟶ X) [IsClosedImmersion i] (q₀ : Y₀ ⟶ X₀) [Etale q₀] (y : Y₀) :
    ∃ (V₀ : Y₀.Opens) (_ : y ∈ V₀) (V : Scheme.{0}) (qV : V ⟶ X) (_ : Etale qV) (jV : (V₀ : Scheme.{0}) ⟶ V),
      IsPullback jV (V₀.ι ≫ q₀) qV i :=
  AlgebraicGeometry.Etale.exists_opens_etale_isPullback_of_isClosedImmersion i q₀ y

variable (C : Type) [CommRing C] (J : Ideal C)

noncomputable abbrev i₀ : Spec (CommRingCat.of (C ⧸ J)) ⟶ Spec (CommRingCat.of C) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))

variable {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of C))

noncomputable abbrev X₀ : Scheme.{0} := pullback f (i₀ C J)

private noncomputable abbrev _root_.Sigma2.ι : X₀ C J f ⟶ X := pullback.fst f (i₀ C J)

p2m_export "Sigma2" "ι"
scoped instance isClosedImmersion_i₀ : IsClosedImmersion (i₀ C J) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

scoped instance isClosedImmersion_ι : IsClosedImmersion (ι C J f) :=
  MorphismProperty.pullback_fst _ _ inferInstance

variable {Y₀ : Scheme.{0}} (q₀ : Y₀ ⟶ X₀ C J f)

structure Piece (V : Y₀.Opens) where
  Y : Scheme.{0}
  q : Y ⟶ X
  etale : Etale q
  j : (V : Scheme.{0}) ⟶ Y
  isPullback : IsPullback j (V.ι ≫ q₀) q (ι C J f)

def Liftable (V : Y₀.Opens) : Prop := Nonempty (Piece C J f q₀ V)

theorem loc_exists [Etale q₀] (y : Y₀) : ∃ V : Y₀.Opens, y ∈ V ∧ Liftable C J f q₀ V := by
  obtain ⟨V₀, hy, V, qV, hV, jV, hpb⟩ := locex (ι C J f) q₀ y
  exact ⟨V₀, hy, ⟨⟨V, qV, hV, jV, hpb⟩⟩⟩

private theorem _root_.Sigma2.isNilpotent_ker_pullback_fst (hJ : IsNilpotent J) {W : Scheme.{0}} (g : W ⟶ Spec (CommRingCat.of C)) :
    IsNilpotent (pullback.fst g (i₀ C J)).ker :=
  S2BRIDGE.isNilpotent_ker_pullback_fst C J hJ g

p2m_export "Sigma2" "isNilpotent_ker_pullback_fst"

theorem isNilpotent_ker_j (hJ : IsNilpotent J) {V : Y₀.Opens} (P : Piece C J f q₀ V) :
    IsClosedImmersion P.j ∧ IsNilpotent P.j.ker := by
  refine ⟨MorphismProperty.of_isPullback P.isPullback.flip inferInstance, ?_⟩

  have big : IsPullback P.j ((V.ι ≫ q₀) ≫ pullback.snd f (i₀ C J)) (P.q ≫ f) (i₀ C J) :=
    P.isPullback.paste_vert (IsPullback.of_hasPullback f (i₀ C J))
  have e : P.j = (big.isoIsPullback _ _ (IsPullback.of_hasPullback (P.q ≫ f) (i₀ C J))).hom ≫
      pullback.fst (P.q ≫ f) (i₀ C J) := by
    simp
  rw [e, Scheme.Hom.ker_comp_of_isIso]
  exact isNilpotent_ker_pullback_fst C J hJ (P.q ≫ f)

namespace Piece

variable {C J f q₀}
variable {V : Y₀.Opens} (P : Piece C J f q₀ V)

theorem isDominant_j (hJ : IsNilpotent J) : IsDominant P.j := by
  obtain ⟨hci, n, hn⟩ := isNilpotent_ker_j C J f q₀ hJ P
  haveI := hci
  rw [isDominant_iff, denseRange_iff_closure_range, ← P.j.support_ker,
    ← P.j.ker.support_pow (n + 1) (by simp), pow_succ, hn]
  simp

theorem surjective_j (hJ : IsNilpotent J) : Surjective P.j := by
  haveI := (isNilpotent_ker_j C J f q₀ hJ P).1
  haveI := P.isDominant_j hJ
  exact surjective_of_isDominant_of_isClosed_range P.j P.j.isClosedEmbedding.isClosed_range

theorem isHomeomorph_j (hJ : IsNilpotent J) : IsHomeomorph P.j.base := by
  haveI := (isNilpotent_ker_j C J f q₀ hJ P).1
  haveI := P.surjective_j hJ
  exact isHomeomorph_iff_isEmbedding_surjective.mpr ⟨P.j.isClosedEmbedding.isEmbedding, P.j.surjective⟩

def resOpens (hJ : IsNilpotent J) (V' : Y₀.Opens) : P.Y.Opens :=
  ⟨P.j.base '' ((V.ι ⁻¹ᵁ V' : (V : Scheme.{0}).Opens) : Set (V : Scheme.{0})),
    (P.isHomeomorph_j hJ).isOpenMap _ (V.ι ⁻¹ᵁ V').2⟩

theorem preimage_resOpens (hJ : IsNilpotent J) (V' : Y₀.Opens) : P.j ⁻¹ᵁ (P.resOpens hJ V') = V.ι ⁻¹ᵁ V' := by
  haveI := (isNilpotent_ker_j C J f q₀ hJ P).1
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [← P.j.isClosedEmbedding.injective hyx]
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem range_preimage_ι (hJ : IsNilpotent J) {V' : Y₀.Opens} (h : V' ≤ V) :
    Set.range ((P.j ⁻¹ᵁ (P.resOpens hJ V')).ι ≫ V.ι) = Set.range V'.ι := by
  rw [P.preimage_resOpens hJ V', Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
    Scheme.Opens.range_ι]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx
  · intro hy
    exact ⟨⟨y, h hy⟩, hy, rfl⟩

noncomputable def resIso (hJ : IsNilpotent J) {V' : Y₀.Opens} (h : V' ≤ V) :
    ((P.j ⁻¹ᵁ (P.resOpens hJ V') : (V : Scheme.{0}).Opens) : Scheme.{0}) ≅ (V' : Scheme.{0}) :=
  IsOpenImmersion.isoOfRangeEq ((P.j ⁻¹ᵁ (P.resOpens hJ V')).ι ≫ V.ι) V'.ι (P.range_preimage_ι hJ h)

theorem resIso_hom_ι (hJ : IsNilpotent J) {V' : Y₀.Opens} (h : V' ≤ V) :
    (P.resIso hJ h).hom ≫ V'.ι = (P.j ⁻¹ᵁ (P.resOpens hJ V')).ι ≫ V.ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

theorem resIso_inv_ι (hJ : IsNilpotent J) {V' : Y₀.Opens} (h : V' ≤ V) :
    (P.resIso hJ h).inv ≫ (P.j ⁻¹ᵁ (P.resOpens hJ V')).ι ≫ V.ι = V'.ι :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

noncomputable def restrict (hJ : IsNilpotent J) {V' : Y₀.Opens} (h : V' ≤ V) : Piece C J f q₀ V' where
  Y := (P.resOpens hJ V' : Scheme.{0})
  q := (P.resOpens hJ V').ι ≫ P.q
  etale := by haveI := P.etale; infer_instance
  j := (P.resIso hJ h).inv ≫ (P.j ∣_ P.resOpens hJ V')
  isPullback := by
    have big := (isPullback_morphismRestrict P.j (P.resOpens hJ V')).paste_vert P.isPullback
    refine big.of_iso (P.resIso hJ h) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
    · rw [Iso.refl_hom, Category.comp_id, ← Category.assoc, ← Category.assoc, ← P.resIso_hom_ι hJ h, Category.assoc]
    · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
    · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]

@[scoped simp] theorem restrict_Y (hJ : IsNilpotent J) {V' : Y₀.Opens} (h : V' ≤ V) :
    (P.restrict hJ h).Y = (P.resOpens hJ V' : Scheme.{0}) := rfl
@[scoped simp] theorem restrict_q (hJ : IsNilpotent J) {V' : Y₀.Opens} (h : V' ≤ V) :
    (P.restrict hJ h).q = (P.resOpens hJ V').ι ≫ P.q := rfl

theorem restrict_j_ι (hJ : IsNilpotent J) {V' : Y₀.Opens} (h : V' ≤ V) :
    (P.restrict hJ h).j ≫ (P.resOpens hJ V').ι = Y₀.homOfLE h ≫ P.j := by
  show ((P.resIso hJ h).inv ≫ (P.j ∣_ P.resOpens hJ V')) ≫ (P.resOpens hJ V').ι = Y₀.homOfLE h ≫ P.j
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc]
  congr 1
  rw [← cancel_mono V.ι, Category.assoc, Scheme.homOfLE_ι]
  exact P.resIso_inv_ι hJ h

end Piece
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_etale_isPullback_forall_existsUnique_comp_eq_of_isNilpotent.Sigma2.Piece"

theorem liftable_of_le (hJ : IsNilpotent J) {V V' : Y₀.Opens} (h : V' ≤ V) (hV : Liftable C J f q₀ V) :
    Liftable C J f q₀ V' :=
  ⟨(Classical.choice hV).restrict hJ h⟩

def Idx : Type := {V : Y₀.Opens // Liftable C J f q₀ V}

scoped instance : Preorder (Idx C J f q₀) := Preorder.lift (fun V => V.1)

noncomputable def piece (V : Idx C J f q₀) : Piece C J f q₀ V.1 := Classical.choice V.2

theorem existsUnique_transition (hJ : IsNilpotent J) {V' V : Idx C J f q₀} (h : V' ≤ V) :
    ∃! φ : (piece C J f q₀ V').Y ⟶ (piece C J f q₀ V).Y,
      φ ≫ (piece C J f q₀ V).q = (piece C J f q₀ V').q ∧
      (piece C J f q₀ V').j ≫ φ = Y₀.homOfLE h ≫ (piece C J f q₀ V).j := by
  haveI := (piece C J f q₀ V).etale
  obtain ⟨hci, hnil⟩ := isNilpotent_ker_j C J f q₀ hJ (piece C J f q₀ V')
  haveI := hci
  refine sect (piece C J f q₀ V).q (piece C J f q₀ V').j hnil (piece C J f q₀ V').q
    (Y₀.homOfLE h ≫ (piece C J f q₀ V).j) ?_
  rw [Category.assoc, (piece C J f q₀ V).isPullback.w, (piece C J f q₀ V').isPullback.w,
    ← Scheme.homOfLE_ι Y₀ h]
  simp only [Category.assoc]

theorem transition_spec (hJ : IsNilpotent J) {V' V : Idx C J f q₀} (h : V' ≤ V) :
    (existsUnique_transition C J f q₀ hJ h).choose ≫ (piece C J f q₀ V).q = (piece C J f q₀ V').q ∧
      (piece C J f q₀ V').j ≫ (existsUnique_transition C J f q₀ hJ h).choose = Y₀.homOfLE h ≫ (piece C J f q₀ V).j :=
  (existsUnique_transition C J f q₀ hJ h).choose_spec.1

theorem transition_unique (hJ : IsNilpotent J) {V' V : Idx C J f q₀} (h : V' ≤ V)
    (φ : (piece C J f q₀ V').Y ⟶ (piece C J f q₀ V).Y)
    (h1 : φ ≫ (piece C J f q₀ V).q = (piece C J f q₀ V').q)
    (h2 : (piece C J f q₀ V').j ≫ φ = Y₀.homOfLE h ≫ (piece C J f q₀ V).j) :
    φ = (existsUnique_transition C J f q₀ hJ h).choose :=
  (existsUnique_transition C J f q₀ hJ h).unique ⟨h1, h2⟩ (transition_spec C J f q₀ hJ h)

noncomputable abbrev F (hJ : IsNilpotent J) : Idx C J f q₀ ⥤ Scheme.{0} where
  obj V := (piece C J f q₀ V).Y
  map h := (existsUnique_transition C J f q₀ hJ h.le).choose
  map_id V := by
    symm
    refine transition_unique C J f q₀ hJ le_rfl (𝟙 _) (Category.id_comp _) ?_
    rw [Category.comp_id]
    have : Y₀.homOfLE (le_refl V.1) = 𝟙 _ := by
      rw [← cancel_mono V.1.ι, Scheme.homOfLE_ι, Category.id_comp]
    rw [this, Category.id_comp]
  map_comp {V₁ V₂ V₃} h₁ h₂ := by
    symm
    obtain ⟨a1, a2⟩ := transition_spec C J f q₀ hJ h₁.le
    obtain ⟨b1, b2⟩ := transition_spec C J f q₀ hJ h₂.le
    refine transition_unique C J f q₀ hJ (h₁ ≫ h₂).le _ ?_ ?_
    · rw [Category.assoc, b1, a1]
    · rw [← Category.assoc, a2, Category.assoc, b2, ← Category.assoc]
      congr 1
      rw [← cancel_mono V₃.1.ι, Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι, Scheme.homOfLE_ι]

namespace Piece

variable {C J f q₀}

theorem exists_iso (hJ : IsNilpotent J) {V : Y₀.Opens} (P Q : Piece C J f q₀ V) :
    ∃ e : P.Y ≅ Q.Y, e.hom ≫ Q.q = P.q ∧ P.j ≫ e.hom = Q.j := by
  haveI := P.etale
  haveI := Q.etale
  obtain ⟨hP, hPn⟩ := isNilpotent_ker_j C J f q₀ hJ P
  obtain ⟨hQ, hQn⟩ := isNilpotent_ker_j C J f q₀ hJ Q
  haveI := hP
  haveI := hQ
  have wP := P.isPullback.w
  have wQ := Q.isPullback.w
  obtain ⟨α, ⟨hα1, hα2⟩, -⟩ := sect Q.q P.j hPn P.q Q.j (by rw [wP, wQ])
  obtain ⟨β, ⟨hβ1, hβ2⟩, -⟩ := sect P.q Q.j hQn Q.q P.j (by rw [wP, wQ])
  have hαβ : α ≫ β = 𝟙 _ :=
    (sect P.q P.j hPn P.q P.j rfl).unique
      ⟨by rw [Category.assoc, hβ1, hα1], by rw [← Category.assoc, hα2, hβ2]⟩
      ⟨Category.id_comp _, Category.comp_id _⟩
  have hβα : β ≫ α = 𝟙 _ :=
    (sect Q.q Q.j hQn Q.q Q.j rfl).unique
      ⟨by rw [Category.assoc, hα1, hβ1], by rw [← Category.assoc, hβ2, hα2]⟩
      ⟨Category.id_comp _, Category.comp_id _⟩
  exact ⟨⟨α, β, hαβ, hβα⟩, hα1, hα2⟩

end Piece
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_etale_isPullback_forall_existsUnique_comp_eq_of_isNilpotent.Sigma2.Piece"

theorem F_map_isOpenImmersion (hJ : IsNilpotent J) {V' V : Idx C J f q₀} (h : V' ⟶ V) :
    IsOpenImmersion ((F C J f q₀ hJ).map h) := by
  obtain ⟨e, he1, he2⟩ :=
    Piece.exists_iso hJ (piece C J f q₀ V') ((piece C J f q₀ V).restrict hJ h.le)
  have key : (F C J f q₀ hJ).map h = e.hom ≫ ((piece C J f q₀ V).resOpens hJ V'.1).ι := by
    symm
    refine transition_unique C J f q₀ hJ h.le _ ?_ ?_
    · rw [Category.assoc]
      exact he1
    · rw [← Category.assoc, he2]
      exact (piece C J f q₀ V).restrict_j_ι hJ h.le
  haveI h1 : IsOpenImmersion e.hom := inferInstance
  haveI h2 : IsOpenImmersion ((piece C J f q₀ V).resOpens hJ V'.1).ι := inferInstance
  rw [key]
  exact MorphismProperty.comp_mem @IsOpenImmersion _ _ h1 h2

scoped instance (hJ : IsNilpotent J) {V' V : Idx C J f q₀} (h : V' ⟶ V) : IsOpenImmersion ((F C J f q₀ hJ).map h) :=
  F_map_isOpenImmersion C J f q₀ hJ h

scoped instance (hJ : IsNilpotent J) : ((F C J f q₀ hJ) ⋙ Scheme.forget).IsLocallyDirected := by
  constructor
  intro i j k fi fj xi xj heq

  simp only [Functor.comp_obj, Scheme.forget_obj, Functor.comp_map, Scheme.forget_map] at xi xj heq ⊢
  change ((F C J f q₀ hJ).map fi).base xi = ((F C J f q₀ hJ).map fj).base xj at heq
  haveI := (piece C J f q₀ i).surjective_j hJ
  haveI := (piece C J f q₀ j).surjective_j hJ
  haveI := (isNilpotent_ker_j C J f q₀ hJ (piece C J f q₀ k)).1
  obtain ⟨yi, rfl⟩ := (piece C J f q₀ i).j.surjective xi
  obtain ⟨yj, rfl⟩ := (piece C J f q₀ j).j.surjective xj

  have sq : ∀ {V' V : Idx C J f q₀} (h : V' ⟶ V) (y : ↥(V'.1 : Scheme.{0})),
      ((F C J f q₀ hJ).map h).base ((piece C J f q₀ V').j.base y) =
        (piece C J f q₀ V).j.base ((Y₀.homOfLE h.le).base y) := by
    intro V' V h y
    have := (transition_spec C J f q₀ hJ h.le).2
    have := congrArg (fun φ => φ.base y) this
    simpa only [Scheme.Hom.comp_base, TopCat.comp_app] using this
  rw [sq fi yi, sq fj yj] at heq
  have hy : ((Y₀.homOfLE fi.le).base yi) = ((Y₀.homOfLE fj.le).base yj) :=
    (piece C J f q₀ k).j.isClosedEmbedding.injective heq
  have hy1 : yi.1 = yj.1 := by
    have := congrArg Subtype.val hy
    simpa only [Scheme.homOfLE_apply] using this

  let l : Idx C J f q₀ := ⟨i.1 ⊓ j.1, liftable_of_le C J f q₀ hJ inf_le_left i.2⟩
  have hli : l ≤ i := show i.1 ⊓ j.1 ≤ i.1 from inf_le_left
  have hlj : l ≤ j := show i.1 ⊓ j.1 ≤ j.1 from inf_le_right
  let y : ↥(l.1 : Scheme.{0}) := ⟨yi.1, ⟨yi.2, hy1 ▸ yj.2⟩⟩
  refine ⟨l, homOfLE hli, homOfLE hlj, (piece C J f q₀ l).j.base y, ?_, ?_⟩
  · change ((F C J f q₀ hJ).map (homOfLE hli)).base ((piece C J f q₀ l).j.base y) = (piece C J f q₀ i).j.base yi
    rw [sq]
    congr 1
    exact Subtype.ext (Scheme.homOfLE_apply _ _)
  · change ((F C J f q₀ hJ).map (homOfLE hlj)).base ((piece C J f q₀ l).j.base y) = (piece C J f q₀ j).j.base yj
    rw [sq]
    congr 1
    exact Subtype.ext ((Scheme.homOfLE_apply _ _).trans hy1)

private theorem _root_.Sigma2.isPullback_of_iSup_eq_top {P X Y Z : Scheme.{u}} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    {ι : Type*} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (h : ∀ i, IsPullback (fst ∣_ U i) ((fst ⁻¹ᵁ U i).ι ≫ snd) ((U i).ι ≫ f) g) : IsPullback fst snd f g :=
  AlgebraicGeometry.isPullback_of_iSup_eq_top fst snd f g U hU h

p2m_export "Sigma2" "isPullback_of_iSup_eq_top"

private theorem _root_.Sigma2.isNilpotent_ker_specMap_mk {B : Type} [CommRing B] (I : Ideal B) (hI : IsNilpotent I) :
    IsNilpotent (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker :=
  S2BRIDGE.isNilpotent_ker_specMap_mk B I hI

p2m_export "Sigma2" "isNilpotent_ker_specMap_mk"
section Main

variable (hJ : IsNilpotent J)

noncomputable abbrev Yg : Scheme.{0} := colimit (F C J f q₀ hJ)

noncomputable def qCocone : Cocone (F C J f q₀ hJ) where
  pt := X
  ι := { app := fun V => (piece C J f q₀ V).q
         naturality := fun {V' V} h => by
           simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
           exact (transition_spec C J f q₀ hJ h.le).1 }

noncomputable abbrev qg : Yg C J f q₀ hJ ⟶ X := colimit.desc _ (qCocone C J f q₀ hJ)

@[scoped simp] theorem ι_qg (V : Idx C J f q₀) : colimit.ι (F C J f q₀ hJ) V ≫ qg C J f q₀ hJ = (piece C J f q₀ V).q :=
  colimit.ι_desc _ _

private theorem _root_.Sigma2.iSup_opensRange : ⨆ V : Idx C J f q₀, (colimit.ι (F C J f q₀ hJ) V).opensRange = ⊤ :=
  (Scheme.IsLocallyDirected.openCover (F C J f q₀ hJ)).iSup_opensRange

p2m_export "Sigma2" "iSup_opensRange"
theorem opensRange_ι (V : Idx C J f q₀) :
    (colimit.ι (F C J f q₀ hJ) V).opensRange.ι =
      (colimit.ι (F C J f q₀ hJ) V).isoOpensRange.inv ≫ colimit.ι (F C J f q₀ hJ) V :=
  ((Iso.inv_comp_eq _).2 (Scheme.Hom.isoOpensRange_hom_ι _).symm).symm

theorem etale_qg : Etale (qg C J f q₀ hJ) := by
  refine IsZariskiLocalAtSource.of_iSup_eq_top _ (iSup_opensRange C J f q₀ hJ) fun V => ?_
  rw [opensRange_ι, Category.assoc, ι_qg]
  have h1 : IsOpenImmersion (colimit.ι (F C J f q₀ hJ) V).isoOpensRange.inv := inferInstance
  have h1' : Etale (colimit.ι (F C J f q₀ hJ) V).isoOpensRange.inv := inferInstance
  exact MorphismProperty.comp_mem @Etale _ _ h1' (piece C J f q₀ V).etale

variable [Etale q₀]

noncomputable def coverY₀ : Y₀.OpenCover :=
  Scheme.Cover.mkOfCovers (Idx C J f q₀) (fun V => (V.1 : Scheme.{0})) (fun V => V.1.ι) fun y => by
    obtain ⟨V, hy, hV⟩ := loc_exists C J f q₀ y
    exact ⟨⟨V, hV⟩, ⟨y, hy⟩, rfl⟩

theorem homOfLE_j_ι {u V : Idx C J f q₀} (h : u ≤ V) :
    Y₀.homOfLE h ≫ (piece C J f q₀ V).j ≫ colimit.ι (F C J f q₀ hJ) V =
      (piece C J f q₀ u).j ≫ colimit.ι (F C J f q₀ hJ) u := by
  rw [← Category.assoc, ← (transition_spec C J f q₀ hJ h).2, Category.assoc]
  congr 1
  exact colimit.w (F C J f q₀ hJ) (homOfLE h)

theorem j_compat (V W : Idx C J f q₀) :
    pullback.fst (V.1.ι) (W.1.ι) ≫ ((piece C J f q₀ V).j ≫ colimit.ι (F C J f q₀ hJ) V) =
      pullback.snd (V.1.ι) (W.1.ι) ≫ ((piece C J f q₀ W).j ≫ colimit.ι (F C J f q₀ hJ) W) := by
  let u : Idx C J f q₀ := ⟨V.1 ⊓ W.1, liftable_of_le C J f q₀ hJ inf_le_left V.2⟩
  have hP := isPullback_opens_inf V.1 W.1
  rw [← cancel_epi hP.isoPullback.hom, IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc]
  have hl : u ≤ V := (inf_le_left : V.1 ⊓ W.1 ≤ V.1)
  have hr : u ≤ W := (inf_le_right : V.1 ⊓ W.1 ≤ W.1)
  exact (homOfLE_j_ι C J f q₀ hJ hl).trans (homOfLE_j_ι C J f q₀ hJ hr).symm

noncomputable abbrev jg : Y₀ ⟶ Yg C J f q₀ hJ :=
  (coverY₀ C J f q₀).glueMorphisms (fun V => (piece C J f q₀ V).j ≫ colimit.ι (F C J f q₀ hJ) V)
    (j_compat C J f q₀ hJ)

@[scoped simp] theorem ι_jg (V : Idx C J f q₀) :
    V.1.ι ≫ jg C J f q₀ hJ = (piece C J f q₀ V).j ≫ colimit.ι (F C J f q₀ hJ) V :=
  (coverY₀ C J f q₀).ι_glueMorphisms _ _ V

theorem ι_jg_qg (V : Idx C J f q₀) :
    V.1.ι ≫ (jg C J f q₀ hJ ≫ qg C J f q₀ hJ) = V.1.ι ≫ (q₀ ≫ ι C J f) := by
  have h1 := ι_jg C J f q₀ hJ V
  have h2 := ι_qg C J f q₀ hJ V
  have h3 := (piece C J f q₀ V).isPullback.w
  rw [← Category.assoc, h1, Category.assoc, h2, h3, Category.assoc]

theorem jg_w : jg C J f q₀ hJ ≫ qg C J f q₀ hJ = q₀ ≫ ι C J f :=
  Scheme.Cover.hom_ext (coverY₀ C J f q₀) _ _ fun V => ι_jg_qg C J f q₀ hJ V

theorem F_map_j_apply {V' V : Idx C J f q₀} (h : V' ⟶ V) (y : (V'.1 : Scheme.{0})) :
    (F C J f q₀ hJ).map h ((piece C J f q₀ V').j y) = (piece C J f q₀ V).j (Y₀.homOfLE h.le y) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
  exact congrArg (fun φ : (V'.1 : Scheme.{0}) ⟶ (piece C J f q₀ V).Y => φ y) (transition_spec C J f q₀ hJ h.le).2

theorem jg_apply (V : Idx C J f q₀) (y : Y₀) (hy : y ∈ V.1) :
    jg C J f q₀ hJ y = colimit.ι (F C J f q₀ hJ) V ((piece C J f q₀ V).j ⟨y, hy⟩) := by
  have h := congrArg (fun φ : (V.1 : Scheme.{0}) ⟶ Yg C J f q₀ hJ => φ ⟨y, hy⟩) (ι_jg C J f q₀ hJ V)
  simp only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] at h
  exact h

theorem preimage_jg_opensRange (V : Idx C J f q₀) :
    jg C J f q₀ hJ ⁻¹ᵁ (colimit.ι (F C J f q₀ hJ) V).opensRange = V.1 := by
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz⟩ : ∃ z, colimit.ι (F C J f q₀ hJ) V z = jg C J f q₀ hJ y := hy
    obtain ⟨W₀, hyW, hW⟩ := loc_exists C J f q₀ y
    let W : Idx C J f q₀ := ⟨W₀, hW⟩
    rw [jg_apply C J f q₀ hJ W y hyW] at hz
    obtain ⟨k, fk, fW, x, hxz, hxW⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (F C J f q₀ hJ)).mp hz
    haveI := (piece C J f q₀ k).surjective_j hJ
    haveI := (isNilpotent_ker_j C J f q₀ hJ (piece C J f q₀ W)).1
    obtain ⟨y', rfl⟩ := (piece C J f q₀ k).j.surjective x
    rw [F_map_j_apply C J f q₀ hJ fW y'] at hxW
    have hyy : Y₀.homOfLE fW.le y' = ⟨y, hyW⟩ := (piece C J f q₀ W).j.isClosedEmbedding.injective hxW
    have : (y'.1 : Y₀) = y := by
      obtain ⟨y'', hy''⟩ := y'
      rw [Scheme.homOfLE_apply'] at hyy
      exact congrArg Subtype.val hyy
    rw [← this]
    exact fk.le y'.2
  · intro hy
    show ∃ z, colimit.ι (F C J f q₀ hJ) V z = jg C J f q₀ hJ y
    exact ⟨_, (jg_apply C J f q₀ hJ V y hy).symm⟩

theorem isPullback_jg_local (V : Idx C J f q₀) :
    IsPullback (jg C J f q₀ hJ ∣_ (colimit.ι (F C J f q₀ hJ) V).opensRange)
      ((jg C J f q₀ hJ ⁻¹ᵁ (colimit.ι (F C J f q₀ hJ) V).opensRange).ι ≫ q₀)
      ((colimit.ι (F C J f q₀ hJ) V).opensRange.ι ≫ qg C J f q₀ hJ) (ι C J f) := by
  refine (piece C J f q₀ V).isPullback.of_iso (Y₀.isoOfEq (preimage_jg_opensRange C J f q₀ hJ V).symm)
    (colimit.ι (F C J f q₀ hJ) V).isoOpensRange (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [← cancel_mono (colimit.ι (F C J f q₀ hJ) V).opensRange.ι, Category.assoc, Category.assoc,
      Scheme.Hom.isoOpensRange_hom_ι, morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc, ι_jg]
  · rw [Iso.refl_hom, Category.comp_id, ← Category.assoc, Scheme.isoOfEq_hom_ι]
  · rw [Iso.refl_hom, Category.comp_id, ← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, ι_qg]
  · simp

theorem isPullback_jg : IsPullback (jg C J f q₀ hJ) q₀ (qg C J f q₀ hJ) (ι C J f) := by
  exact isPullback_of_iSup_eq_top _ _ _ _ (fun V => (colimit.ι (F C J f q₀ hJ) V).opensRange)
    (iSup_opensRange C J f q₀ hJ) (isPullback_jg_local C J f q₀ hJ)

theorem lift_clause (B : Type) [CommRing B] [Algebra C B] (t : Spec (CommRingCat.of B) ⟶ X)
    (ht : t ≫ f = Spec.map (CommRingCat.ofHom (algebraMap C B)))
    (s₀ : Spec (CommRingCat.of (B ⧸ J.map (algebraMap C B))) ⟶ Y₀)
    (hs₀ : s₀ ≫ q₀ ≫ ι C J f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map (algebraMap C B)))) ≫ t) :
    ∃! s : Spec (CommRingCat.of B) ⟶ Yg C J f q₀ hJ, s ≫ qg C J f q₀ hJ = t ∧
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map (algebraMap C B)))) ≫ s = s₀ ≫ jg C J f q₀ hJ := by
  haveI := etale_qg C J f q₀ hJ
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map (algebraMap C B))))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hI : IsNilpotent (J.map (algebraMap C B)) := by
    obtain ⟨n, hn⟩ := hJ
    refine ⟨n, ?_⟩
    rw [← Ideal.map_pow, hn]
    simp
  refine sect (qg C J f q₀ hJ) _ (isNilpotent_ker_specMap_mk _ hI) t (s₀ ≫ jg C J f q₀ hJ) ?_
  rw [Category.assoc, jg_w]
  exact hs₀

include hJ in
theorem main :
    ∃ (Y : Scheme.{0}) (q : Y ⟶ X) (_ : Etale q) (j : Y₀ ⟶ Y)
      (_ : IsPullback j q₀ q (ι C J f)),
      ∀ (B : Type) [CommRing B] [Algebra C B] (t : Spec (CommRingCat.of B) ⟶ X),
        t ≫ f = Spec.map (CommRingCat.ofHom (algebraMap C B)) →
        ∀ (s₀ : Spec (CommRingCat.of (B ⧸ J.map (algebraMap C B))) ⟶ Y₀),
          s₀ ≫ q₀ ≫ ι C J f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map (algebraMap C B)))) ≫ t →
          ∃! s : Spec (CommRingCat.of B) ⟶ Y, s ≫ q = t ∧
            Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map (algebraMap C B)))) ≫ s = s₀ ≫ j :=
  ⟨Yg C J f q₀ hJ, qg C J f q₀ hJ, etale_qg C J f q₀ hJ, jg C J f q₀ hJ, isPullback_jg C J f q₀ hJ,
    fun B _ _ t ht s₀ hs₀ => lift_clause C J f q₀ hJ B t ht s₀ hs₀⟩

end Main
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_etale_isPullback_forall_existsUnique_comp_eq_of_isNilpotent.Sigma2.Piece"

end Sigma2
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_etale_isPullback_forall_existsUnique_comp_eq_of_isNilpotent.Sigma2.Piece P2MW.S_AlgebraicGeometry_exists_etale_isPullback_forall_existsUnique_comp_eq_of_isNilpotent.Sigma2"

theorem solution
    (C : Type) [CommRing C] (J : Ideal C) (hJ : IsNilpotent J)
    {X Y₀ : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of C))
    (q₀ : Y₀ ⟶ pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) [Etale q₀] :
    ∃ (Y : Scheme.{0}) (q : Y ⟶ X) (_ : Etale q) (j : Y₀ ⟶ Y)
      (_ : IsPullback j q₀ q (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))),
      ∀ (B : Type) [CommRing B] [Algebra C B] (t : Spec (CommRingCat.of B) ⟶ X),
        t ≫ f = Spec.map (CommRingCat.ofHom (algebraMap C B)) →
        ∀ (s₀ : Spec (CommRingCat.of (B ⧸ J.map (algebraMap C B))) ⟶ Y₀),
          s₀ ≫ q₀ ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) =
            Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map (algebraMap C B)))) ≫ t →
          ∃! s : Spec (CommRingCat.of B) ⟶ Y, s ≫ q = t ∧
            Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map (algebraMap C B)))) ≫ s = s₀ ≫ j :=
  Sigma2.main C J f q₀ hJ

end S_AlgebraicGeometry_exists_etale_isPullback_forall_existsUnique_comp_eq_of_isNilpotent
end P2MW
export P2MW.S_AlgebraicGeometry_exists_etale_isPullback_forall_existsUnique_comp_eq_of_isNilpotent (solution)
