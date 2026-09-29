-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/6065c5ab-c436-5568-9f8e-b0129e866669

import Mathlib
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isAffine_of_isAffine_of_isNoetherianRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.FormalOmega

noncomputable section

namespace FQ22

variable {𝒪 : Type} [CommRing 𝒪] {G : Type} [Group G]

structure Pkg (𝒪 : Type) [CommRing 𝒪] (G : Type) [Group G] where
  M : Scheme.{0}
  X : Scheme.{0}
  fM : M ⟶ Spec (CommRingCat.of 𝒪)
  f : X ⟶ Spec (CommRingCat.of 𝒪)
  ρ : G →* Aut M
  hover : ∀ g : G, (ρ g).hom ≫ fM = fM
  p : M ⟶ X
  hp : p ≫ f = fM
  hρp : ∀ g : G, (ρ g).hom ≫ p = p
  hint : IsIntegralHom p
  haff : IsAffineHom p
  hsurj : Function.Surjective p.base
  hsec : ∀ V : X.Opens, Function.Injective (p.app V)
  hinv : ∀ V : X.Opens, Set.range (p.app V) =
      {s | ∀ g : G, (ρ g).hom.appLE (p ⁻¹ᵁ V) (p ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hρp g]) s = s}
  hlft : LocallyOfFiniteType fM
  hlftX : LocallyOfFiniteType f

theorem injective_map_eqToHom {Y : Scheme.{0}} {A B : Y.Opens} (e : A = B) :
    Function.Injective (Y.presheaf.map (eqToHom e).op) := by
  subst e; simp [Function.injective_id]

theorem surjective_map_eqToHom {Y : Scheme.{0}} {A B : Y.Opens} (e : A = B) :
    Function.Surjective (Y.presheaf.map (eqToHom e).op) := by
  subst e; simp [Function.surjective_id]

theorem appLE_map_eqToHom {Y : Scheme.{0}} (φ : Y ⟶ Y) {A B : Y.Opens} (e : A = B)
    (hA : A ≤ φ ⁻¹ᵁ A) (hB : B ≤ φ ⁻¹ᵁ B) (s : Γ(Y, B)) :
    φ.appLE A A hA (Y.presheaf.map (eqToHom e).op s) = Y.presheaf.map (eqToHom e).op (φ.appLE B B hB s) := by
  subst e; simp

namespace Pkg

variable (P : Pkg 𝒪 G) (U : P.X.Opens)

theorem preimage_le (g : G) : P.p ⁻¹ᵁ U ≤ (P.ρ g).hom ⁻¹ᵁ (P.p ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, P.hρp g]

noncomputable def resHom (g : G) : (↑(P.p ⁻¹ᵁ U) : Scheme.{0}) ⟶ ↑(P.p ⁻¹ᵁ U) :=
  (P.ρ g).hom.resLE (P.p ⁻¹ᵁ U) (P.p ⁻¹ᵁ U) (P.preimage_le U g)

@[reassoc (attr := simp)]
theorem resHom_ι (g : G) : P.resHom U g ≫ (P.p ⁻¹ᵁ U).ι = (P.p ⁻¹ᵁ U).ι ≫ (P.ρ g).hom :=
  Scheme.Hom.resLE_comp_ι _ _

theorem resHom_one : P.resHom U 1 = 𝟙 _ := by
  rw [← cancel_mono (P.p ⁻¹ᵁ U).ι, resHom_ι, map_one, Category.id_comp]
  exact Category.comp_id _

theorem resHom_mul (g h : G) : P.resHom U (g * h) = P.resHom U h ≫ P.resHom U g := by
  rw [← cancel_mono (P.p ⁻¹ᵁ U).ι, resHom_ι, map_mul, Aut.Aut_mul_def, Iso.trans_hom, Category.assoc,
    resHom_ι, resHom_ι_assoc]

@[reducible] noncomputable def resAut (g : G) : Aut (↑(P.p ⁻¹ᵁ U) : Scheme.{0}) where
  hom := P.resHom U g
  inv := P.resHom U g⁻¹
  hom_inv_id := by rw [← resHom_mul, inv_mul_cancel, resHom_one]
  inv_hom_id := by rw [← resHom_mul, mul_inv_cancel, resHom_one]

@[reducible] noncomputable def ρres : G →* Aut (↑(P.p ⁻¹ᵁ U) : Scheme.{0}) where
  toFun := P.resAut U
  map_one' := Iso.ext (P.resHom_one U)
  map_mul' g h := Iso.ext (by
    show P.resHom U (g * h) = (P.resAut U g * P.resAut U h).hom
    rw [Aut.Aut_mul_def, Iso.trans_hom]
    exact P.resHom_mul U g h)

@[scoped simp] theorem ρres_hom (g : G) : (P.ρres U g).hom = P.resHom U g := rfl

theorem hsurj_res : Function.Surjective (P.p ∣_ U).base := by
  rintro ⟨x, hx⟩
  obtain ⟨m, rfl⟩ := P.hsurj x
  exact ⟨⟨m, hx⟩, Subtype.ext (morphismRestrict_base_coe P.p U ⟨m, hx⟩)⟩

theorem hsec_res (V : (↑U : Scheme.{0}).Opens) : Function.Injective ((P.p ∣_ U).app V) := by
  rw [morphismRestrict_app]
  intro a b h
  exact P.hsec _ (injective_map_eqToHom _ h)

theorem hρp_res (g : G) : P.resHom U g ≫ (P.p ∣_ U) = P.p ∣_ U := by
  rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, resHom_ι_assoc, P.hρp]

theorem res_preimage_le (V : (↑U : Scheme.{0}).Opens) (g : G) :
    (P.p ∣_ U) ⁻¹ᵁ V ≤ (P.resHom U g) ⁻¹ᵁ ((P.p ∣_ U) ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, hρp_res]

theorem hinv_res (V : (↑U : Scheme.{0}).Opens) :
    Set.range ((P.p ∣_ U).app V) =
      {s | ∀ g : G, (P.resHom U g).appLE _ _ (P.res_preimage_le U V g) s = s} := by
  have e1 := image_morphismRestrict_preimage P.p U V
  have key : ∀ (g : G) (s₀ : Γ(P.M, P.p ⁻¹ᵁ (U.ι ''ᵁ V))),
      (P.resHom U g).appLE _ _ (P.res_preimage_le U V g) (P.M.presheaf.map (eqToHom e1).op s₀) =
        P.M.presheaf.map (eqToHom e1).op ((P.ρ g).hom.appLE _ _ (P.preimage_le _ g) s₀) := by
    intro g s₀
    unfold resHom
    rw [Scheme.Hom.resLE_appLE]
    exact appLE_map_eqToHom _ e1 _ _ s₀
  ext s
  obtain ⟨s₀, rfl⟩ := surjective_map_eqToHom e1 s
  simp only [Set.mem_setOf_eq, key, Set.mem_range]
  rw [morphismRestrict_app]
  constructor
  · rintro ⟨r, hr⟩ g
    have hr' : P.p.app _ r = s₀ := injective_map_eqToHom e1 hr
    subst hr'
    congr 1
    have hmem := (P.hinv (U.ι ''ᵁ V)).le ⟨r, rfl⟩
    exact hmem g
  · intro h
    have hs₀ : s₀ ∈ Set.range (P.p.app (U.ι ''ᵁ V)) := by
      rw [P.hinv]; intro g; exact injective_map_eqToHom e1 (h g)
    obtain ⟨r, rfl⟩ := hs₀
    exact ⟨r, rfl⟩

@[reducible] noncomputable def restrict : Pkg 𝒪 G where
  M := ↑(P.p ⁻¹ᵁ U)
  X := ↑U
  fM := (P.p ⁻¹ᵁ U).ι ≫ P.fM
  f := U.ι ≫ P.f
  ρ := P.ρres U
  hover g := by show P.resHom U g ≫ _ = _; rw [resHom_ι_assoc, P.hover]
  p := P.p ∣_ U
  hp := by rw [← Category.assoc, morphismRestrict_ι, Category.assoc, P.hp]
  hρp g := P.hρp_res U g
  hint := by haveI := P.hint; infer_instance
  haff := by haveI := P.haff; exact IsZariskiLocalAtTarget.restrict ‹_› U
  hsurj := P.hsurj_res U
  hsec := P.hsec_res U
  hinv := P.hinv_res U
  hlft := by haveI := P.hlft; infer_instance
  hlftX := by haveI := P.hlftX; infer_instance

@[scoped simp] theorem restrict_M : (P.restrict U).M = ↑(P.p ⁻¹ᵁ U) := rfl
@[scoped simp] theorem restrict_X : (P.restrict U).X = ↑U := rfl
@[scoped simp] theorem restrict_fM : (P.restrict U).fM = (P.p ⁻¹ᵁ U).ι ≫ P.fM := rfl
@[scoped simp] theorem restrict_f : (P.restrict U).f = U.ι ≫ P.f := rfl
@[scoped simp] theorem restrict_p : (P.restrict U).p = P.p ∣_ U := rfl
@[scoped simp] theorem restrict_ρ_hom (g : G) : ((P.restrict U).ρ g).hom = P.resHom U g := rfl

end Pkg
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Pkg"

section Fam

variable (π : 𝒪)

abbrev FamMap {X T : Scheme.{0}} (fX : X ⟶ Spec (CommRingCat.of 𝒪)) (t : T ⟶ Spec (CommRingCat.of 𝒪)) : Type 1 :=
  ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
    (Scheme.nilpPoints fX).obj B → (Scheme.nilpPoints t).obj B

variable {π}

def IsNatural {X T : Scheme.{0}} {fX : X ⟶ Spec (CommRingCat.of 𝒪)} {t : T ⟶ Spec (CommRingCat.of 𝒪)}
    (v : FamMap π fX t) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
    (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints fX).obj B),
    v B' hB' ((Scheme.nilpPoints fX).map φ x) = (Scheme.nilpPoints t).map φ (v B hB x)

private def _root_.FQ22.precomp {X Y T : Scheme.{0}} {fX : X ⟶ Spec (CommRingCat.of 𝒪)} {fY : Y ⟶ Spec (CommRingCat.of 𝒪)}
    {t : T ⟶ Spec (CommRingCat.of 𝒪)} (h : X ⟶ Y) (w : h ≫ fY = fX) (v : FamMap π fY t) : FamMap π fX t :=
  fun B _ _ hB x => v B hB ((Scheme.nilpPoints.mapHom fX fY h w).app B x)

p2m_export "FQ22" "precomp"

private def _root_.FQ22.postcomp {X T T' : Scheme.{0}} {fX : X ⟶ Spec (CommRingCat.of 𝒪)} {t : T ⟶ Spec (CommRingCat.of 𝒪)}
    {t' : T' ⟶ Spec (CommRingCat.of 𝒪)} (h : T ⟶ T') (w : h ≫ t' = t) (v : FamMap π fX t) : FamMap π fX t' :=
  fun B _ _ hB x => (Scheme.nilpPoints.mapHom t t' h w).app B (v B hB x)

p2m_export "FQ22" "postcomp"
theorem IsNatural.precomp {X Y T : Scheme.{0}} {fX : X ⟶ Spec (CommRingCat.of 𝒪)} {fY : Y ⟶ Spec (CommRingCat.of 𝒪)}
    {t : T ⟶ Spec (CommRingCat.of 𝒪)} (h : X ⟶ Y) (w : h ≫ fY = fX) {v : FamMap π fY t} (hv : IsNatural v) :
    IsNatural (precomp h w v) := by
  intro B _ _ B' _ _ hB hB' φ x
  unfold FQ22.precomp
  rw [← hv B B' hB hB' φ]
  congr 1

theorem IsNatural.postcomp {X T T' : Scheme.{0}} {fX : X ⟶ Spec (CommRingCat.of 𝒪)} {t : T ⟶ Spec (CommRingCat.of 𝒪)}
    {t' : T' ⟶ Spec (CommRingCat.of 𝒪)} (h : T ⟶ T') (w : h ≫ t' = t) {v : FamMap π fX t} (hv : IsNatural v) :
    IsNatural (postcomp h w v) := by
  intro B _ _ B' _ _ hB hB' φ x
  unfold FQ22.postcomp
  rw [hv B B' hB hB' φ]
  apply Subtype.ext
  simp only [Scheme.nilpPoints_map_val]
  show (Spec.map _ ≫ (v B hB x).1) ≫ h = Spec.map _ ≫ ((v B hB x).1 ≫ h)
  rw [Category.assoc]

structure Fam (P : Pkg 𝒪 G) (π : 𝒪) (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪)) where
  u : FamMap π P.fM t
  nat : IsNatural u
  inv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (g : G)
      (y : (Scheme.nilpPoints P.fM).obj B),
      u B hB ((Scheme.nilpPoints.mapHom P.fM P.fM (P.ρ g).hom (P.hover g)).app B y) = u B hB y

namespace Fam

variable {P : Pkg 𝒪 G} {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of 𝒪)} (F : Fam P π T t)

def Factors (ubar : FamMap π P.f t) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints P.fM).obj B),
    ubar B hB ((Scheme.nilpPoints.mapHom P.fM P.f P.p P.hp).app B y) = F.u B hB y

def Lands (U : P.X.Opens) (W : T.Opens) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (y : (Scheme.nilpPoints (P.restrict U).fM).obj B),
    Set.range (F.u B hB ((Scheme.nilpPoints.mapHom (P.restrict U).fM P.fM (P.p ⁻¹ᵁ U).ι rfl).app B y)).1.base ⊆ (W : Set T)

variable (U : P.X.Opens) (W : T.Opens) (hW : F.Lands U W)

noncomputable def restrictU : FamMap π (P.restrict U).fM (W.ι ≫ t) := fun B _ _ hB y =>
  ⟨IsOpenImmersion.lift W.ι (F.u B hB ((Scheme.nilpPoints.mapHom (P.restrict U).fM P.fM (P.p ⁻¹ᵁ U).ι rfl).app B y)).1
      (by rw [Scheme.Opens.range_ι]; exact hW B hB y), by
    rw [← Category.assoc, IsOpenImmersion.lift_fac]
    exact (F.u B hB _).2⟩

@[scoped simp] theorem restrictU_val_ι {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (y : (Scheme.nilpPoints (P.restrict U).fM).obj B) :
    (F.restrictU U W hW B hB y).1 ≫ W.ι =
      (F.u B hB ((Scheme.nilpPoints.mapHom (P.restrict U).fM P.fM (P.p ⁻¹ᵁ U).ι rfl).app B y)).1 :=
  IsOpenImmersion.lift_fac _ _ _

noncomputable def restrict : Fam (P.restrict U) π (↑W) (W.ι ≫ t) where
  u := F.restrictU U W hW
  nat B _ _ B' _ _ hB hB' φ x := by
    apply Subtype.ext
    rw [← cancel_mono W.ι]
    simp only [Scheme.nilpPoints_map_val, Category.assoc, restrictU_val_ι]
    have := F.nat B B' hB hB' φ ((Scheme.nilpPoints.mapHom (P.restrict U).fM P.fM (P.p ⁻¹ᵁ U).ι rfl).app B x)
    rw [← (Scheme.nilpPoints.mapHom (P.restrict U).fM P.fM (P.p ⁻¹ᵁ U).ι rfl).naturality] at this
    rw [this]
    rfl
  inv B _ _ hB g y := by
    apply Subtype.ext
    rw [← cancel_mono W.ι]
    simp only [restrictU_val_ι]
    have := F.inv B hB g ((Scheme.nilpPoints.mapHom (P.restrict U).fM P.fM (P.p ⁻¹ᵁ U).ι rfl).app B y)
    rw [← this]
    congr 2
    apply Subtype.ext
    show (y.1 ≫ P.resHom U g) ≫ (P.p ⁻¹ᵁ U).ι = (y.1 ≫ (P.p ⁻¹ᵁ U).ι) ≫ (P.ρ g).hom
    have h := P.resHom_ι U g
    exact (Category.assoc _ _ _).trans ((congrArg (fun k => y.1 ≫ k) h).trans (Category.assoc _ _ _).symm)

end Fam
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Pkg P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Fam"

end Fam
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Pkg P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Fam"

section BiAffine

theorem biaffine [IsNoetherianRing 𝒪] [Finite G] (P : Pkg 𝒪 G) (π : 𝒪) {T : Scheme.{0}}
    {t : T ⟶ Spec (CommRingCat.of 𝒪)} (F : Fam P π T t) (hX : IsAffine P.X) (hT : IsAffine T) :
    ∃ ubar : FamMap π P.f t, IsNatural ubar ∧ F.Factors ubar ∧
      ∀ u' : FamMap π P.f t, IsNatural u' → F.Factors u' →
        ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (z : (Scheme.nilpPoints P.f).obj B), u' B hB z = ubar B hB z :=
  AlgebraicGeometry.Scheme.existsUnique_nilpPoints_factor_of_quotient_of_isAffine_of_isAffine_of_isNoetherianRing
    π P.fM P.f P.hlft P.hlftX P.ρ P.hover P.p P.hp P.hρp P.hint P.haff P.hsurj P.hsec P.hinv T t F.u F.nat F.inv
    hX hT

end BiAffine
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Pkg P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Fam"

section Pts

def overHom {R : CommRingCat.{0}} (φ : Spec R ⟶ Spec (CommRingCat.of 𝒪)) : 𝒪 →+* R :=
  (Spec.preimage φ).hom

theorem specMap_overHom {R : CommRingCat.{0}} (φ : Spec R ⟶ Spec (CommRingCat.of 𝒪)) :
    Spec.map (CommRingCat.ofHom (overHom φ)) = φ := by
  unfold overHom; rw [CommRingCat.ofHom_hom]; exact Spec.map_preimage φ

variable {Y : Scheme.{0}} (fY : Y ⟶ Spec (CommRingCat.of 𝒪))

@[reducible] def κAlg (y : Y) : Algebra 𝒪 (Y.residueField y) :=
  (overHom (Y.fromSpecResidueField y ≫ fY)).toAlgebra

theorem κAlg_specMap (y : Y) : letI := κAlg fY y
    Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (Y.residueField y))) = Y.fromSpecResidueField y ≫ fY := by
  letI := κAlg fY y
  exact specMap_overHom _

def κPt (y : Y) : letI := κAlg fY y; (Scheme.nilpPoints fY).obj (Y.residueField y) :=
  letI := κAlg fY y; ⟨Y.fromSpecResidueField y, (κAlg_specMap fY y).symm⟩

variable (π)

def IsNilAt (y : Y) : Prop := letI := κAlg fY y; IsNilpotent (algebraMap 𝒪 (Y.residueField y) π)

theorem isNilAt_iff (y : Y) : IsNilAt fY π y ↔ π ∈ (fY.base y).asIdeal := by
  letI := κAlg fY y
  unfold IsNilAt
  rw [isNilpotent_iff_eq_zero, ← RingHom.mem_ker]
  have h1 : RingHom.ker (algebraMap 𝒪 (Y.residueField y)) =
      ((Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (Y.residueField y)))).base
        (IsLocalRing.closedPoint (Y.residueField y))).asIdeal := by
    rw [Spec.map_apply, PrimeSpectrum.comap_asIdeal, CommRingCat.hom_ofHom, RingHom.ker_eq_comap_bot]
    congr 1
    exact (Ideal.eq_bot_of_prime _).symm
  rw [h1, κAlg_specMap, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply,
    Scheme.fromSpecResidueField_apply]

theorem isClosed_setOf_isNilAt : IsClosed {y : Y | IsNilAt fY π y} := by
  have : {y : Y | IsNilAt fY π y} = fY.base ⁻¹' (PrimeSpectrum.zeroLocus {π}) := by
    ext y
    simp only [Set.mem_setOf_eq, isNilAt_iff, Set.mem_preimage]
    change _ ↔ ({π} : Set 𝒪) ⊆ ((fY.base y).asIdeal : Set 𝒪)
    rw [Set.singleton_subset_iff]; rfl
  rw [this]
  exact (PrimeSpectrum.isClosed_zeroLocus _).preimage fY.base.hom.continuous

variable {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of 𝒪)}

def τ (v : FamMap π fY t) (y : Y) (hy : IsNilAt fY π y) : T :=
  letI := κAlg fY y; (v _ hy (κPt fY y)).1.base (IsLocalRing.closedPoint _)

theorem base_apply_eq_τ_field (v : FamMap π fY t) (hv : IsNatural v) {K : Type} [Field K] [Algebra 𝒪 K]
    (hK : IsNilpotent (algebraMap 𝒪 K π)) (k : (Scheme.nilpPoints fY).obj K)
    (y : Y) (hpt : k.1.base (IsLocalRing.closedPoint K) = y) :
    ∃ hy : IsNilAt fY π y, (v K hK k).1.base (IsLocalRing.closedPoint K) = τ fY π v y hy := by
  subst hpt
  letI := κAlg fY (k.1.base (IsLocalRing.closedPoint K))
  set r := Y.descResidueField (Scheme.stalkClosedPointTo k.1) with hrdef
  have hr : Spec.map r ≫ Y.fromSpecResidueField _ = k.1 :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y k.1
  have hr𝒪 : r.hom.comp (algebraMap 𝒪 _) = algebraMap 𝒪 K := by
    have h1 : Spec.map (CommRingCat.ofHom (r.hom.comp (algebraMap 𝒪 _))) =
        Spec.map (CommRingCat.ofHom (algebraMap 𝒪 K)) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, κAlg_specMap, ← Category.assoc, hr]
      exact k.2
    have h2 := Spec.map_injective h1
    exact congrArg CommRingCat.Hom.hom h2
  let r' : (Y.residueField (k.1.base (IsLocalRing.closedPoint K))) →ₐ[𝒪] K :=
    { toRingHom := r.hom, commutes' := fun o => RingHom.congr_fun hr𝒪 o }
  have hy : IsNilAt fY π (k.1.base (IsLocalRing.closedPoint K)) := by
    unfold IsNilAt
    rw [← IsNilpotent.map_iff r.hom.injective]
    rw [← RingHom.comp_apply, hr𝒪]; exact hK
  refine ⟨hy, ?_⟩
  have hk : k = (Scheme.nilpPoints fY).map r' (κPt fY _) := by
    apply Subtype.ext
    simp only [Scheme.nilpPoints_map_val]
    show k.1 = Spec.map (CommRingCat.ofHom r.hom) ≫ Y.fromSpecResidueField _
    rw [CommRingCat.ofHom_hom, hr]
  have hnat := hv _ K hy hK r' (κPt fY _)
  rw [← hk] at hnat
  rw [hnat]
  simp only [Scheme.nilpPoints_map_val, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
  unfold τ
  congr 1
  exact Subsingleton.elim _ _

theorem exists_algHom_residueField {B : Type} [CommRing B] [Algebra 𝒪 B] (𝔮 : Spec (CommRingCat.of B)) :
    letI := κAlg (Scheme.specOver (𝒪 := 𝒪) B) 𝔮
    ∃ ψ : B →ₐ[𝒪] ((Spec (CommRingCat.of B)).residueField 𝔮),
      Spec.map (CommRingCat.ofHom ψ.toRingHom) = (Spec (CommRingCat.of B)).fromSpecResidueField 𝔮 := by
  letI := κAlg (Scheme.specOver (𝒪 := 𝒪) B) 𝔮
  let ψ₀ : B →+* ((Spec (CommRingCat.of B)).residueField 𝔮) :=
    (Spec.preimage ((Spec (CommRingCat.of B)).fromSpecResidueField 𝔮)).hom
  have hψ₀ : Spec.map (CommRingCat.ofHom ψ₀) = (Spec (CommRingCat.of B)).fromSpecResidueField 𝔮 := by
    simp only [ψ₀, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hψ𝒪 : ψ₀.comp (algebraMap 𝒪 B) = algebraMap 𝒪 _ := by
    have h1 : Spec.map (CommRingCat.ofHom (ψ₀.comp (algebraMap 𝒪 B))) = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 _)) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, hψ₀, κAlg_specMap]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  exact ⟨{ toRingHom := ψ₀, commutes' := fun o => RingHom.congr_fun hψ𝒪 o }, hψ₀⟩

theorem base_apply_eq_τ (v : FamMap π fY t) (hv : IsNatural v) {B : Type} [CommRing B] [Algebra 𝒪 B]
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints fY).obj B) (𝔮 : Spec (CommRingCat.of B)) :
    ∃ hy : IsNilAt fY π (y.1.base 𝔮), (v B hB y).1.base 𝔮 = τ fY π v (y.1.base 𝔮) hy := by
  letI := κAlg (Scheme.specOver (𝒪 := 𝒪) B) 𝔮
  obtain ⟨ψ, hψ⟩ := exists_algHom_residueField (𝒪 := 𝒪) 𝔮
  set K := ((Spec (CommRingCat.of B)).residueField 𝔮)
  have hK : IsNilpotent (algebraMap 𝒪 K π) := by
    rw [← ψ.comp_algebraMap, RingHom.comp_apply]; exact hB.map _
  have hpt : ((Scheme.nilpPoints fY).map ψ y).1.base (IsLocalRing.closedPoint K) = y.1.base 𝔮 := by
    simp only [Scheme.nilpPoints_map_val, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
    rw [hψ, Scheme.fromSpecResidueField_apply]
  obtain ⟨hy, e⟩ := base_apply_eq_τ_field fY π v hv hK ((Scheme.nilpPoints fY).map ψ y) _ hpt
  refine ⟨hy, ?_⟩
  rw [← e, hv B K hB hK ψ y]
  simp only [Scheme.nilpPoints_map_val, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
  rw [hψ, Scheme.fromSpecResidueField_apply]

theorem isNilAt_base {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (y : (Scheme.nilpPoints fY).obj B) (𝔮 : Spec (CommRingCat.of B)) : IsNilAt fY π (y.1.base 𝔮) := by
  rw [isNilAt_iff]
  have : fY.base (y.1.base 𝔮) = (Scheme.specOver (𝒪 := 𝒪) B).base 𝔮 :=
    calc fY.base (y.1.base 𝔮) = (y.1 ≫ fY).base 𝔮 := rfl
    _ = _ := by rw [y.2]
  rw [this, Scheme.specOver, Spec.map_apply, PrimeSpectrum.comap_asIdeal, CommRingCat.hom_ofHom, Ideal.mem_comap]
  obtain ⟨n, hn⟩ := hB
  exact 𝔮.2.mem_of_pow_mem n (by rw [hn]; exact Ideal.zero_mem _)

end Pts
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Pkg P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Fam"

section Orbit

variable (P : Pkg 𝒪 G)

namespace Pkg

def actHom (U : P.X.Opens) (g : G) : Γ(P.M, P.p ⁻¹ᵁ U) →+* Γ(P.M, P.p ⁻¹ᵁ U) :=
  ((P.ρ g).hom.appLE (P.p ⁻¹ᵁ U) (P.p ⁻¹ᵁ U) (P.preimage_le U g)).hom

theorem actHom_mul (U : P.X.Opens) (g h : G) (a : Γ(P.M, P.p ⁻¹ᵁ U)) :
    P.actHom U (g * h) a = P.actHom U h (P.actHom U g a) := by
  unfold actHom
  have e : (P.ρ (g * h)).hom = (P.ρ h).hom ≫ (P.ρ g).hom := by rw [map_mul, Aut.Aut_mul_def, Iso.trans_hom]
  have key : ∀ (φ : P.M ⟶ P.M) (le : P.p ⁻¹ᵁ U ≤ φ ⁻¹ᵁ (P.p ⁻¹ᵁ U)) (hφ : φ = (P.ρ h).hom ≫ (P.ρ g).hom),
      (φ.appLE _ _ le).hom a = ((P.ρ h).hom.appLE _ _ (P.preimage_le U h)).hom
        (((P.ρ g).hom.appLE _ _ (P.preimage_le U g)).hom a) := by
    intro φ le hφ; subst hφ
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  exact key _ _ e

theorem map_homOfLE_apply_of_eq_id {Y : Scheme.{0}} (V : Y.Opens) (le : V ≤ (𝟙 Y) ⁻¹ᵁ V) (a : Γ(Y, V)) :
    (Y.presheaf.map (homOfLE le).op).hom a = a := by
  have h : (homOfLE le : V ⟶ V) = 𝟙 V := Subsingleton.elim _ _
  have h2 : Y.presheaf.map (homOfLE le : V ⟶ V).op = 𝟙 _ := by rw [h, op_id, CategoryTheory.Functor.map_id]
  have h3 := congrArg (fun f => (CommRingCat.Hom.hom f) a) h2
  exact h3

theorem actHom_one (U : P.X.Opens) (a : Γ(P.M, P.p ⁻¹ᵁ U)) : P.actHom U 1 a = a := by
  unfold actHom
  have e : (P.ρ 1).hom = 𝟙 _ := by rw [map_one]; rfl
  have key : ∀ (φ : P.M ⟶ P.M) (hφ : φ = 𝟙 _) (le : P.p ⁻¹ᵁ U ≤ φ ⁻¹ᵁ (P.p ⁻¹ᵁ U)),
      (φ.appLE (P.p ⁻¹ᵁ U) (P.p ⁻¹ᵁ U) le).hom a = a := by
    intro φ hφ le; subst hφ
    simp only [Scheme.Hom.appLE, CommRingCat.comp_apply]
    rw [map_homOfLE_apply_of_eq_id]
    rfl
  exact key _ e _

@[reducible] def act (U : P.X.Opens) : MulSemiringAction G Γ(P.M, P.p ⁻¹ᵁ U) where
  smul g a := P.actHom U g⁻¹ a
  one_smul a := by show P.actHom U 1⁻¹ a = a; rw [inv_one]; exact P.actHom_one U a
  mul_smul g h a := by show P.actHom U (g * h)⁻¹ a = P.actHom U g⁻¹ (P.actHom U h⁻¹ a); rw [mul_inv_rev, actHom_mul]
  smul_zero g := map_zero _
  smul_add g a b := map_add _ a b
  smul_one g := map_one _
  smul_mul g a b := map_mul _ a b

theorem act_smul_def (U : P.X.Opens) (g : G) (a : Γ(P.M, P.p ⁻¹ᵁ U)) :
    letI := P.act U; g • a = P.actHom U g⁻¹ a := rfl

theorem mem_range_iff (U : P.X.Opens) (a : Γ(P.M, P.p ⁻¹ᵁ U)) :
    letI := P.act U; a ∈ Set.range (P.p.app U) ↔ ∀ g : G, g • a = a := by
  letI := P.act U
  rw [P.hinv U]
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h g; exact h g⁻¹
  · intro h g; have := h g⁻¹; rwa [act_smul_def, inv_inv] at this

theorem exists_smul_eq [Finite G] (m m' : P.M) (h : P.p.base m = P.p.base m') :
    ∃ g : G, (P.ρ g).hom.base m = m' := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := P.X) (x := P.p.base m) (U := ⊤) trivial
  haveI := P.haff
  have hV : IsAffineOpen (P.p ⁻¹ᵁ U) := hU.preimage P.p
  have hm : m ∈ P.p ⁻¹ᵁ U := hxU
  have hm' : m' ∈ P.p ⁻¹ᵁ U := by show P.p.base m' ∈ U; rw [← h]; exact hxU

  letI alg : Algebra Γ(P.X, U) Γ(P.M, P.p ⁻¹ᵁ U) := (P.p.app U).hom.toAlgebra
  letI := P.act U
  haveI : SMulCommClass G Γ(P.X, U) Γ(P.M, P.p ⁻¹ᵁ U) := ⟨fun g r a => by
    show P.actHom U g⁻¹ ((P.p.app U).hom r * a) = (P.p.app U).hom r * P.actHom U g⁻¹ a
    rw [map_mul]
    congr 1
    have := (P.mem_range_iff U ((P.p.app U).hom r)).mp ⟨r, rfl⟩ g
    exact this⟩
  haveI : Algebra.IsInvariant Γ(P.X, U) Γ(P.M, P.p ⁻¹ᵁ U) G :=
    ⟨fun a ha => (P.mem_range_iff U a).mpr ha⟩

  let 𝔓 := hV.primeIdealOf ⟨m, hm⟩
  let 𝔓' := hV.primeIdealOf ⟨m', hm'⟩
  have hunder : Ideal.under Γ(P.X, U) 𝔓.asIdeal = Ideal.under Γ(P.X, U) 𝔓'.asIdeal := by
    have e1 := IsAffineOpen.comap_primeIdealOf_appLE (f := P.p) (x := m) U hU (P.p ⁻¹ᵁ U) hV le_rfl hm
    have e2 := IsAffineOpen.comap_primeIdealOf_appLE (f := P.p) (x := m') U hU (P.p ⁻¹ᵁ U) hV le_rfl hm'
    have e3 : hU.primeIdealOf ⟨P.p.base m, le_rfl (a := P.p ⁻¹ᵁ U) hm⟩ = hU.primeIdealOf ⟨P.p.base m', le_rfl (a := P.p ⁻¹ᵁ U) hm'⟩ := by
      congr 1; exact Subtype.ext h
    have e4 : PrimeSpectrum.comap (P.p.appLE U (P.p ⁻¹ᵁ U) le_rfl).hom 𝔓 = PrimeSpectrum.comap (P.p.appLE U (P.p ⁻¹ᵁ U) le_rfl).hom 𝔓' := by
      rw [e1, e2]; exact e3
    have e5 := congrArg PrimeSpectrum.asIdeal e4
    rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal, Scheme.Hom.appLE_eq_app] at e5
    exact e5
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq Γ(P.X, U) Γ(P.M, P.p ⁻¹ᵁ U) G 𝔓.asIdeal 𝔓'.asIdeal hunder

  have hg' : 𝔓' = PrimeSpectrum.comap (P.actHom U g) 𝔓 := by
    apply PrimeSpectrum.ext; ext a
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, hg, Ideal.mem_pointwise_smul_iff_inv_smul_mem,
      act_smul_def, inv_inv]
  refine ⟨g, ?_⟩
  have key := IsAffineOpen.SpecMap_appLE_fromSpec (P.ρ g).hom hV hV (P.preimage_le U g)
  have := congrArg (fun φ => φ.base 𝔓) key
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at this
  rw [IsAffineOpen.fromSpec_primeIdealOf] at this
  rw [← this]
  have : (Spec.map ((P.ρ g).hom.appLE (P.p ⁻¹ᵁ U) (P.p ⁻¹ᵁ U) (P.preimage_le U g))).base 𝔓 = 𝔓' := by
    rw [Spec.map_apply, hg']; rfl
  rw [this, IsAffineOpen.fromSpec_primeIdealOf]

end Pkg
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Pkg P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Fam"

end Orbit
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Pkg P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Fam"

section Good

variable {P : Pkg 𝒪 G} {π : 𝒪} {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of 𝒪)} (F : Fam P π T t)

namespace Fam

theorem isNilAt_iff_isNilAt_p (m : P.M) : IsNilAt P.fM π m ↔ IsNilAt P.f π (P.p.base m) := by
  rw [isNilAt_iff, isNilAt_iff, ← P.hp]; rfl

abbrev τF (m : P.M) (hm : IsNilAt P.fM π m) : T := τ P.fM π F.u m hm

theorem τF_eq_of_p_eq [Finite G] (m m' : P.M) (hm : IsNilAt P.fM π m) (hm' : IsNilAt P.fM π m')
    (h : P.p.base m = P.p.base m') : F.τF m hm = F.τF m' hm' := by
  obtain ⟨g, hg⟩ := P.exists_smul_eq m m' h
  letI := κAlg P.fM m
  let y := (Scheme.nilpPoints.mapHom P.fM P.fM (P.ρ g).hom (P.hover g)).app _ (κPt P.fM m)
  have hpt : y.1.base (IsLocalRing.closedPoint _) = m' := by
    show ((P.M.fromSpecResidueField m) ≫ (P.ρ g).hom).base _ = m'
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, Scheme.fromSpecResidueField_apply, hg]
  obtain ⟨hy, e⟩ := base_apply_eq_τ_field P.fM π F.u F.nat hm y m' hpt
  have e' : (F.u _ hm (κPt P.fM m)).1.base (IsLocalRing.closedPoint _) = τ P.fM π F.u m' hy := by
    rw [← F.inv _ hm g (κPt P.fM m)]; exact e
  exact e'

theorem exists_open_iff (W : T.Opens) :
    ∃ O : P.M.Opens, ∀ (m : P.M) (hm : IsNilAt P.fM π m), F.τF m hm ∈ W ↔ m ∈ O := by

  have loc : ∀ (V : P.M.Opens) (hV : IsAffineOpen V), ∃ O : P.M.Opens, O ≤ V ∧
      ∀ (m : P.M) (hmV : m ∈ V) (hm : IsNilAt P.fM π m), F.τF m hm ∈ W ↔ m ∈ O := by
    intro V hV

    letI algA : Algebra 𝒪 Γ(P.M, V) := (overHom (hV.fromSpec ≫ P.fM)).toAlgebra
    have hA : Spec.map (CommRingCat.ofHom (algebraMap 𝒪 Γ(P.M, V))) = hV.fromSpec ≫ P.fM := specMap_overHom _
    let I : Ideal Γ(P.M, V) := Ideal.span {algebraMap 𝒪 Γ(P.M, V) π}
    let Aπ : Type := Γ(P.M, V) ⧸ I
    have hπ : IsNilpotent (algebraMap 𝒪 Aπ π) := by
      refine ⟨1, ?_⟩
      rw [pow_one]
      exact (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl) :
        Ideal.Quotient.mk I (algebraMap 𝒪 Γ(P.M, V) π) = 0)

    let c₀ : Spec (CommRingCat.of Aπ) ⟶ P.M := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ hV.fromSpec
    have hc₀ : c₀ ≫ P.fM = Scheme.specOver Aπ := by
      show (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ hV.fromSpec) ≫ P.fM = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 Aπ))
      rw [Category.assoc, ← hA, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    let c : (Scheme.nilpPoints P.fM).obj Aπ := ⟨c₀, hc₀⟩

    have hemb : Topology.IsEmbedding c₀.base := by
      have h1 : Topology.IsEmbedding (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).base := by
        have : ⇑(Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).base = PrimeSpectrum.comap (Ideal.Quotient.mk I) := by
          funext q; rfl
        rw [this]
        exact (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _ Ideal.Quotient.mk_surjective).isEmbedding
      have h2 : Topology.IsEmbedding hV.fromSpec.base := hV.fromSpec.isOpenEmbedding.isEmbedding
      exact h2.comp h1
    have hrange : ∀ m : P.M, m ∈ V → IsNilAt P.fM π m → ∃ q, c₀.base q = m := by
      intro m hmV hm
      let 𝔓 := hV.primeIdealOf ⟨m, hmV⟩
      have h𝔓 : algebraMap 𝒪 Γ(P.M, V) π ∈ 𝔓.asIdeal := by
        rw [isNilAt_iff] at hm
        have : P.fM.base m = (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 Γ(P.M, V)))).base 𝔓 := by
          rw [hA, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, IsAffineOpen.fromSpec_primeIdealOf]
        rw [this, Spec.map_apply, PrimeSpectrum.comap_asIdeal, CommRingCat.hom_ofHom, Ideal.mem_comap] at hm
        exact hm
      have : 𝔓 ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) := by
        rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
          PrimeSpectrum.mem_zeroLocus]
        show (I : Set Γ(P.M, V)) ⊆ (𝔓.asIdeal : Set Γ(P.M, V))
        intro a ha
        exact (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h𝔓)) ha
      obtain ⟨q, hq⟩ := this
      refine ⟨q, ?_⟩
      show hV.fromSpec.base ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).base q) = m
      rw [Spec.map_apply, CommRingCat.hom_ofHom, hq, IsAffineOpen.fromSpec_primeIdealOf]

    obtain ⟨O', hO', hO'eq⟩ := hemb.isInducing.isOpen_iff.mp
      (((F.u Aπ hπ c).1.base.hom.continuous).isOpen_preimage _ W.2)
    refine ⟨⟨O', hO'⟩ ⊓ V, inf_le_right, ?_⟩
    intro m hmV hm
    obtain ⟨q, rfl⟩ := hrange m hmV hm
    obtain ⟨hy, e⟩ := base_apply_eq_τ P.fM π F.u F.nat hπ c q
    change τ P.fM π F.u (c₀.base q) hm ∈ W ↔ _
    rw [← e]
    constructor
    · intro hW
      refine ⟨?_, hmV⟩
      show q ∈ c₀.base ⁻¹' O'
      rw [hO'eq]; exact hW
    · rintro ⟨hO, -⟩
      have : q ∈ c₀.base ⁻¹' O' := hO
      rw [hO'eq] at this; exact this

  choose O hO hO' using loc
  refine ⟨⨆ V : P.M.affineOpens, O V.1 V.2, ?_⟩
  intro m hm
  constructor
  · intro hW
    obtain ⟨V, hV, hmV, -⟩ := exists_isAffineOpen_mem_and_subset (X := P.M) (x := m) (U := ⊤) trivial
    have := (hO' V hV m hmV hm).mp hW
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV⟩, this⟩
  · intro hm'
    obtain ⟨V, hmO⟩ := TopologicalSpace.Opens.mem_iSup.mp hm'
    exact (hO' V.1 V.2 m (hO V.1 V.2 hmO) hm).mpr hmO

theorem exists_good [Finite G] (x : P.X) (hx : IsNilAt P.f π x) (N : P.X.Opens) (hxN : x ∈ N) :
    ∃ U : P.X.Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ N ∧ ∃ W : T.Opens, IsAffineOpen W ∧
      ∀ (m : P.M) (hm : IsNilAt P.fM π m), m ∈ P.p ⁻¹ᵁ U → F.τF m hm ∈ W := by
  obtain ⟨m₀, rfl⟩ := P.hsurj x
  have hm₀ : IsNilAt P.fM π m₀ := (isNilAt_iff_isNilAt_p (P := P) (π := π) m₀).mpr hx
  obtain ⟨W, hW, ht₀, -⟩ := exists_isAffineOpen_mem_and_subset (X := T) (x := F.τF m₀ hm₀) (U := ⊤) trivial
  obtain ⟨O, hO⟩ := F.exists_open_iff W
  let S : Set P.M := {m | IsNilAt P.fM π m} ∩ (O : Set P.M)ᶜ
  have hS : IsClosed S := (isClosed_setOf_isNilAt P.fM π).inter (O.2.isClosed_compl)
  haveI : UniversallyClosed P.p := (IsIntegralHom.iff_universallyClosed_and_isAffineHom.mp P.hint).1
  have hpS : IsClosed (P.p.base '' S) := P.p.isClosedMap S hS
  have hxS : P.p.base m₀ ∉ P.p.base '' S := by
    rintro ⟨m, ⟨hm, hmO⟩, hmm⟩
    apply hmO
    exact (hO m hm).mp (by rw [F.τF_eq_of_p_eq m m₀ hm hm₀ hmm]; exact ht₀)
  let N' : P.X.Opens := N ⊓ ⟨(P.p.base '' S)ᶜ, hpS.isOpen_compl⟩
  obtain ⟨U, hU, hxU, hUN'⟩ := exists_isAffineOpen_mem_and_subset (X := P.X) (x := P.p.base m₀) (U := N') ⟨hxN, hxS⟩
  refine ⟨U, hU, hxU, fun y hy => (hUN' hy).1, W, hW, ?_⟩
  intro m hm hmU
  have hmS : m ∉ S := fun h => (hUN' hmU).2 ⟨m, h, rfl⟩
  have hmO : m ∈ O := by
    by_contra h'; exact hmS ⟨hm, h'⟩
  exact (hO m hm).mpr hmO

end Fam
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Pkg P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Fam"

end Good
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Pkg P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Fam"

section Uniq

variable {P : Pkg 𝒪 G} {π : 𝒪} {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of 𝒪)} (F : Fam P π T t)

abbrev pushO {Y : Scheme.{0}} (fY : Y ⟶ Spec (CommRingCat.of 𝒪)) (U : Y.Opens) {B : Type} [CommRing B] [Algebra 𝒪 B]
    (w : (Scheme.nilpPoints (U.ι ≫ fY)).obj B) : (Scheme.nilpPoints fY).obj B :=
  (Scheme.nilpPoints.mapHom (U.ι ≫ fY) fY U.ι rfl).app B w

def liftO {Y : Scheme.{0}} (fY : Y ⟶ Spec (CommRingCat.of 𝒪)) (U : Y.Opens) {B : Type} [CommRing B] [Algebra 𝒪 B]
    (z : (Scheme.nilpPoints fY).obj B) (hz : Set.range z.1.base ⊆ (U : Set Y)) :
    (Scheme.nilpPoints (U.ι ≫ fY)).obj B :=
  ⟨IsOpenImmersion.lift U.ι z.1 (by rw [Scheme.Opens.range_ι]; exact hz), by
    rw [← Category.assoc, IsOpenImmersion.lift_fac]; exact z.2⟩

theorem pushO_liftO {Y : Scheme.{0}} (fY : Y ⟶ Spec (CommRingCat.of 𝒪)) (U : Y.Opens) {B : Type} [CommRing B]
    [Algebra 𝒪 B] (z : (Scheme.nilpPoints fY).obj B) (hz : Set.range z.1.base ⊆ (U : Set Y)) :
    pushO fY U (liftO fY U z hz) = z :=
  Subtype.ext (IsOpenImmersion.lift_fac _ _ _)

private def _root_.FQ22.cores {Y : Scheme.{0}} {fY : Y ⟶ Spec (CommRingCat.of 𝒪)} (v : FamMap π fY t) (W : T.Opens)
    (hW : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints fY).obj B),
      Set.range (v B hB y).1.base ⊆ (W : Set T)) : FamMap π fY (W.ι ≫ t) :=
  fun B _ _ hB y => ⟨IsOpenImmersion.lift W.ι (v B hB y).1 (by rw [Scheme.Opens.range_ι]; exact hW B hB y), by
    rw [← Category.assoc, IsOpenImmersion.lift_fac]; exact (v B hB y).2⟩

p2m_export "FQ22" "cores"
theorem cores_val_ι {Y : Scheme.{0}} {fY : Y ⟶ Spec (CommRingCat.of 𝒪)} (v : FamMap π fY t) (W : T.Opens) (hW)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints fY).obj B) :
    (cores v W hW B hB y).1 ≫ W.ι = (v B hB y).1 :=
  IsOpenImmersion.lift_fac _ _ _

theorem IsNatural.cores {Y : Scheme.{0}} {fY : Y ⟶ Spec (CommRingCat.of 𝒪)} {v : FamMap π fY t} (hv : IsNatural v)
    (W : T.Opens) (hW) : IsNatural (cores v W hW) := by
  intro B _ _ B' _ _ hB hB' φ x
  apply Subtype.ext
  rw [← cancel_mono W.ι]
  simp only [Scheme.nilpPoints_map_val, Category.assoc, cores_val_ι]
  rw [hv B B' hB hB' φ x]
  rfl

theorem exists_algHom_of_over {B : Type} [CommRing B] [Algebra 𝒪 B] {R : CommRingCat.{0}}
    (φ : Spec R ⟶ Spec (CommRingCat.of B)) :
    letI : Algebra 𝒪 R := (overHom (φ ≫ Scheme.specOver (𝒪 := 𝒪) B)).toAlgebra
    ∃ ψ : B →ₐ[𝒪] R, Spec.map (CommRingCat.ofHom ψ.toRingHom) = φ := by
  letI : Algebra 𝒪 R := (overHom (φ ≫ Scheme.specOver (𝒪 := 𝒪) B)).toAlgebra
  let ψ₀ : B →+* R := (Spec.preimage φ).hom
  have hψ₀ : Spec.map (CommRingCat.ofHom ψ₀) = φ := by simp only [ψ₀, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hψ𝒪 : ψ₀.comp (algebraMap 𝒪 B) = algebraMap 𝒪 R := by
    have h1 : Spec.map (CommRingCat.ofHom (ψ₀.comp (algebraMap 𝒪 B))) = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 R)) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, hψ₀]
      exact (specMap_overHom _).symm
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  exact ⟨{ toRingHom := ψ₀, commutes' := fun o => RingHom.congr_fun hψ𝒪 o }, hψ₀⟩

theorem IsNatural.val_comp {Y : Scheme.{0}} {fY : Y ⟶ Spec (CommRingCat.of 𝒪)} {v : FamMap π fY t} (hv : IsNatural v)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (z : (Scheme.nilpPoints fY).obj B)
    {R : CommRingCat.{0}} (φ : Spec R ⟶ Spec (CommRingCat.of B)) :
    letI : Algebra 𝒪 R := (overHom (φ ≫ Scheme.specOver (𝒪 := 𝒪) B)).toAlgebra
    ∃ (hR : IsNilpotent (algebraMap 𝒪 R π)) (z' : (Scheme.nilpPoints fY).obj R),
      z'.1 = φ ≫ z.1 ∧ (v R hR z').1 = φ ≫ (v B hB z).1 := by
  letI : Algebra 𝒪 R := (overHom (φ ≫ Scheme.specOver (𝒪 := 𝒪) B)).toAlgebra
  obtain ⟨ψ, hψ⟩ := exists_algHom_of_over (𝒪 := 𝒪) φ
  have hR : IsNilpotent (algebraMap 𝒪 R π) := by
    rw [← ψ.comp_algebraMap, RingHom.comp_apply]; exact hB.map _
  refine ⟨hR, (Scheme.nilpPoints fY).map ψ z, ?_, ?_⟩
  · simp only [Scheme.nilpPoints_map_val, hψ]
  · rw [hv B R hB hR ψ z]; simp only [Scheme.nilpPoints_map_val, hψ]

namespace Fam

def res (U : P.X.Opens) : Fam (P.restrict U) π T t where
  u := precomp (P.p ⁻¹ᵁ U).ι rfl F.u
  nat := F.nat.precomp _ _
  inv B _ _ hB g y := by
    unfold FQ22.precomp
    have := F.inv B hB g ((Scheme.nilpPoints.mapHom (P.restrict U).fM P.fM (P.p ⁻¹ᵁ U).ι rfl).app B y)
    rw [← this]
    congr 1
    apply Subtype.ext
    show (y.1 ≫ P.resHom U g) ≫ (P.p ⁻¹ᵁ U).ι = (y.1 ≫ (P.p ⁻¹ᵁ U).ι) ≫ (P.ρ g).hom
    have h := P.resHom_ι U g
    exact (Category.assoc _ _ _).trans ((congrArg (fun k => y.1 ≫ k) h).trans (Category.assoc _ _ _).symm)

@[scoped simp] theorem res_u (U : P.X.Opens) {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (y : (Scheme.nilpPoints (P.restrict U).fM).obj B) :
    (F.res U).u B hB y = F.u B hB ((Scheme.nilpPoints.mapHom (P.restrict U).fM P.fM (P.p ⁻¹ᵁ U).ι rfl).app B y) := rfl

def GoodPt (U : P.X.Opens) (W : T.Opens) : Prop :=
  ∀ (m : P.M) (hm : IsNilAt P.fM π m), m ∈ P.p ⁻¹ᵁ U → F.τF m hm ∈ W

theorem lands_of_goodPt {U : P.X.Opens} {W : T.Opens} (h : F.GoodPt U W) : F.Lands U W := by
  intro B _ _ hB y
  rintro _ ⟨𝔮, rfl⟩
  obtain ⟨hy', e⟩ := base_apply_eq_τ P.fM π F.u F.nat hB
    ((Scheme.nilpPoints.mapHom (P.restrict U).fM P.fM (P.p ⁻¹ᵁ U).ι rfl).app B y) 𝔮
  rw [e]
  exact h _ hy' (y.1.base 𝔮).2

theorem τ_eq_τF (u' : FamMap π P.f t) (hu' : IsNatural u') (hf : F.Factors u') (m : P.M) (hm : IsNilAt P.fM π m)
    (x : P.X) (hxm : P.p.base m = x) (hx : IsNilAt P.f π x) : τ P.f π u' x hx = F.τF m hm := by
  letI := κAlg P.fM m
  let y := (Scheme.nilpPoints.mapHom P.fM P.f P.p P.hp).app _ (κPt P.fM m)
  have hpt : y.1.base (IsLocalRing.closedPoint _) = x := by
    show ((P.M.fromSpecResidueField m) ≫ P.p).base _ = x
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, Scheme.fromSpecResidueField_apply, hxm]
  obtain ⟨hx', e⟩ := base_apply_eq_τ_field P.f π u' hu' hm y x hpt
  rw [← e, hf]
  rfl

theorem landsX_of_goodPt {U : P.X.Opens} {W : T.Opens} (h : F.GoodPt U W) (u' : FamMap π P.f t) (hu' : IsNatural u')
    (hf : F.Factors u') : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (w : (Scheme.nilpPoints (P.restrict U).f).obj B), Set.range (u' B hB (pushO P.f U w)).1.base ⊆ (W : Set T) := by
  intro B _ _ hB w
  rintro _ ⟨𝔮, rfl⟩
  obtain ⟨hx, e⟩ := base_apply_eq_τ P.f π u' hu' hB (pushO P.f U w) 𝔮
  rw [e]
  obtain ⟨m, hm⟩ := P.hsurj ((pushO P.f U w).1.base 𝔮)
  have hmnil : IsNilAt P.fM π m := by rw [isNilAt_iff_isNilAt_p (P := P), hm]; exact hx
  rw [F.τ_eq_τF u' hu' hf m hmnil _ hm hx]
  apply h m hmnil
  show P.p.base m ∈ U
  rw [hm]; exact (w.1.base 𝔮).2

theorem eq_on_good [IsNoetherianRing 𝒪] [Finite G] {U : P.X.Opens} {W : T.Opens} (hU : IsAffineOpen U)
    (hW : IsAffineOpen W) (h : F.GoodPt U W) (u₁ u₂ : FamMap π P.f t) (h₁ : IsNatural u₁) (h₂ : IsNatural u₂)
    (f₁ : F.Factors u₁) (f₂ : F.Factors u₂) (B : Type) [CommRing B] [Algebra 𝒪 B]
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (w : (Scheme.nilpPoints (P.restrict U).f).obj B) :
    u₁ B hB (pushO P.f U w) = u₂ B hB (pushO P.f U w) := by

  let v₁ := cores (precomp U.ι rfl u₁) W (F.landsX_of_goodPt h u₁ h₁ f₁)
  let v₂ := cores (precomp U.ι rfl u₂) W (F.landsX_of_goodPt h u₂ h₂ f₂)
  have n₁ : IsNatural v₁ := (h₁.precomp U.ι rfl).cores W _
  have n₂ : IsNatural v₂ := (h₂.precomp U.ι rfl).cores W _
  have fac : ∀ (u' : FamMap π P.f t) (hf : F.Factors u') (hl),
      (F.restrict U W (F.lands_of_goodPt h)).Factors (cores (precomp U.ι rfl u') W hl) := by
    intro u' hf hl C _ _ hC y
    apply Subtype.ext
    rw [← cancel_mono W.ι, cores_val_ι]
    show (u' C hC _).1 = (F.restrictU U W (F.lands_of_goodPt h) C hC y).1 ≫ W.ι
    rw [Fam.restrictU_val_ι, ← hf C hC]
    congr 2
    apply Subtype.ext
    show (y.1 ≫ (P.p ∣_ U)) ≫ U.ι = (y.1 ≫ (P.p ⁻¹ᵁ U).ι) ≫ P.p
    have hh := morphismRestrict_ι P.p U
    exact (Category.assoc _ _ _).trans ((congrArg (fun k => y.1 ≫ k) hh).trans (Category.assoc _ _ _).symm)
  obtain ⟨ubar, -, -, huniq⟩ := biaffine (P.restrict U) π (F.restrict U W (F.lands_of_goodPt h)) hU hW
  have e₁ := huniq v₁ n₁ (fac u₁ f₁ _) B hB w
  have e₂ := huniq v₂ n₂ (fac u₂ f₂ _) B hB w
  apply Subtype.ext
  calc (u₁ B hB (pushO P.f U w)).1 = (v₁ B hB w).1 ≫ W.ι :=
        (cores_val_ι (precomp U.ι rfl u₁) W (F.landsX_of_goodPt h u₁ h₁ f₁) hB w).symm
    _ = (v₂ B hB w).1 ≫ W.ι := by rw [e₁, e₂]
    _ = _ := cores_val_ι (precomp U.ι rfl u₂) W (F.landsX_of_goodPt h u₂ h₂ f₂) hB w

theorem uniq [IsNoetherianRing 𝒪] [Finite G] (u₁ u₂ : FamMap π P.f t) (h₁ : IsNatural u₁) (h₂ : IsNatural u₂)
    (f₁ : F.Factors u₁) (f₂ : F.Factors u₂) (B : Type) [CommRing B] [Algebra 𝒪 B]
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (z : (Scheme.nilpPoints P.f).obj B) : u₁ B hB z = u₂ B hB z := by
  apply Subtype.ext

  let J := { V : (Spec (CommRingCat.of B)).Opens // IsAffineOpen V ∧ ∃ U : P.X.Opens, IsAffineOpen U ∧
    (∃ W : T.Opens, IsAffineOpen W ∧ F.GoodPt U W) ∧ Set.range (V.ι ≫ z.1).base ⊆ (U : Set P.X) }
  have hJ : TopologicalSpace.IsOpenCover (fun j : J => j.1) := by
    apply top_le_iff.mp
    intro 𝔮 _
    have hx : IsNilAt P.f π (z.1.base 𝔮) := isNilAt_base P.f π hB z 𝔮
    obtain ⟨U, hU, hxU, -, W, hW, hgood⟩ := F.exists_good _ hx ⊤ trivial
    obtain ⟨V, hV, h𝔮V, hVsub⟩ := exists_isAffineOpen_mem_and_subset (X := Spec (CommRingCat.of B)) (x := 𝔮)
      (U := z.1 ⁻¹ᵁ U) hxU
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV, U, hU, ⟨W, hW, hgood⟩, ?_⟩, h𝔮V⟩
    rintro _ ⟨q, rfl⟩
    exact hVsub q.2
  refine Scheme.Cover.hom_ext ((Spec (CommRingCat.of B)).openCoverOfIsOpenCover _ hJ) _ _ fun j => ?_
  obtain ⟨V, hV, U, hU, ⟨W, hW, hgood⟩, hVU⟩ := j
  show V.ι ≫ (u₁ B hB z).1 = V.ι ≫ (u₂ B hB z).1
  rw [← cancel_epi hV.isoSpec.inv, ← Category.assoc, ← Category.assoc, hV.isoSpec_inv_ι]
  letI : Algebra 𝒪 (Γ(Spec (CommRingCat.of B), V)) :=
    (overHom (hV.fromSpec ≫ Scheme.specOver (𝒪 := 𝒪) B)).toAlgebra
  obtain ⟨hR, z', hz', e₁⟩ := h₁.val_comp hB z hV.fromSpec
  obtain ⟨hR', z'', hz'', e₂⟩ := h₂.val_comp hB z hV.fromSpec
  rw [← e₁, ← e₂]
  have hzz : z'' = z' := Subtype.ext (hz''.trans hz'.symm)
  rw [hzz]
  have hz'U : Set.range z'.1.base ⊆ (U : Set P.X) := by
    rw [hz']
    rintro _ ⟨q, rfl⟩
    rw [← hV.isoSpec_inv_ι]
    exact hVU ⟨hV.isoSpec.inv.base q, rfl⟩
  rw [← pushO_liftO P.f U z' hz'U]
  exact congrArg Subtype.val (F.eq_on_good hU hW hgood u₁ u₂ h₁ h₂ f₁ f₂ _ hR (liftO P.f U z' hz'U))

end Fam
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Pkg P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Fam"

end Uniq
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Pkg P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Fam"

section Exist

variable {P : Pkg 𝒪 G} {π : 𝒪} {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of 𝒪)} (F : Fam P π T t)

theorem IsNatural.val_comp' {Y : Scheme.{0}} {fY : Y ⟶ Spec (CommRingCat.of 𝒪)} {v : FamMap π fY t} (hv : IsNatural v)
    {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
    (φ : Spec (CommRingCat.of B') ⟶ Spec (CommRingCat.of B)) (hφ : φ ≫ Scheme.specOver (𝒪 := 𝒪) B = Scheme.specOver B')
    (z : (Scheme.nilpPoints fY).obj B) (z' : (Scheme.nilpPoints fY).obj B') (hz' : z'.1 = φ ≫ z.1) :
    (v B' hB' z').1 = φ ≫ (v B hB z).1 := by
  let ψ₀ : B →+* B' := (Spec.preimage φ).hom
  have hψ₀ : Spec.map (CommRingCat.ofHom ψ₀) = φ := by simp only [ψ₀, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hψ𝒪 : ψ₀.comp (algebraMap 𝒪 B) = algebraMap 𝒪 B' := by
    have h1 : Spec.map (CommRingCat.ofHom (ψ₀.comp (algebraMap 𝒪 B))) = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 B')) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, hψ₀]; exact hφ
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  let ψ : B →ₐ[𝒪] B' := { toRingHom := ψ₀, commutes' := fun o => RingHom.congr_fun hψ𝒪 o }
  have hz : z' = (Scheme.nilpPoints fY).map ψ z := by
    apply Subtype.ext; rw [hz']; simp only [Scheme.nilpPoints_map_val]
    show φ ≫ z.1 = Spec.map (CommRingCat.ofHom ψ₀) ≫ z.1
    rw [hψ₀]
  rw [hz, hv B B' hB hB' ψ z]
  simp only [Scheme.nilpPoints_map_val]
  show Spec.map (CommRingCat.ofHom ψ₀) ≫ _ = _
  rw [hψ₀]

namespace Fam

variable [IsNoetherianRing 𝒪] [Finite G]

def chart {U : P.X.Opens} {W : T.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W) (h : F.GoodPt U W) :
    FamMap π (P.restrict U).f t :=
  postcomp W.ι rfl (biaffine (P.restrict U) π (F.restrict U W (F.lands_of_goodPt h)) hU hW).choose

theorem chart_nat {U : P.X.Opens} {W : T.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W) (h : F.GoodPt U W) :
    IsNatural (F.chart hU hW h) :=
  (biaffine (P.restrict U) π (F.restrict U W (F.lands_of_goodPt h)) hU hW).choose_spec.1.postcomp W.ι rfl

theorem chart_factors {U : P.X.Opens} {W : T.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W) (h : F.GoodPt U W) :
    (F.res U).Factors (F.chart hU hW h) := by
  intro B _ _ hB y
  have e := (biaffine (P.restrict U) π (F.restrict U W (F.lands_of_goodPt h)) hU hW).choose_spec.2.1 B hB y
  apply Subtype.ext
  show ((biaffine (P.restrict U) π (F.restrict U W (F.lands_of_goodPt h)) hU hW).choose B hB _).1 ≫ W.ι = _
  rw [e]
  exact F.restrictU_val_ι U W (F.lands_of_goodPt h) hB y

def pushLE {U' U : P.X.Opens} (hle : U' ≤ U) {B : Type} [CommRing B] [Algebra 𝒪 B]
    (w : (Scheme.nilpPoints (P.restrict U').f).obj B) : (Scheme.nilpPoints (P.restrict U).f).obj B :=
  ⟨w.1 ≫ P.X.homOfLE hle, by
    show (w.1 ≫ P.X.homOfLE hle) ≫ U.ι ≫ P.f = _
    have hh : P.X.homOfLE hle ≫ U.ι ≫ P.f = U'.ι ≫ P.f := by rw [← Category.assoc, Scheme.homOfLE_ι]
    exact (Category.assoc _ _ _).trans ((congrArg (fun k => w.1 ≫ k) hh).trans w.2)⟩

omit [IsNoetherianRing 𝒪] [Finite G] in
theorem pushLE_eq {U' U : P.X.Opens} (hle : U' ≤ U) {B : Type} [CommRing B] [Algebra 𝒪 B]
    (w : (Scheme.nilpPoints (P.restrict U').f).obj B) (w₁ : (Scheme.nilpPoints (P.restrict U).f).obj B)
    (hw : w₁.1 ≫ U.ι = w.1 ≫ U'.ι) : w₁ = pushLE hle w := by
  apply Subtype.ext
  rw [← cancel_mono U.ι, hw]
  show _ = (w.1 ≫ P.X.homOfLE hle) ≫ U.ι
  rw [Category.assoc, Scheme.homOfLE_ι]

theorem chart_pushLE_factors {U' U : P.X.Opens} (hle : U' ≤ U) {W : T.Opens} (hU : IsAffineOpen U)
    (hW : IsAffineOpen W) (h : F.GoodPt U W) :
    (F.res U').Factors (fun B _ _ hB w => F.chart hU hW h B hB (pushLE hle w)) := by
  intro B _ _ hB y'

  let y : (Scheme.nilpPoints (P.restrict U).fM).obj B :=
    ⟨y'.1 ≫ P.M.homOfLE (Scheme.Hom.preimage_mono P.p hle), by
      show (y'.1 ≫ P.M.homOfLE _) ≫ (P.p ⁻¹ᵁ U).ι ≫ P.fM = _
      have hh : P.M.homOfLE (Scheme.Hom.preimage_mono P.p hle) ≫ (P.p ⁻¹ᵁ U).ι ≫ P.fM = (P.p ⁻¹ᵁ U').ι ≫ P.fM := by
        rw [← Category.assoc, Scheme.homOfLE_ι]
      exact (Category.assoc _ _ _).trans ((congrArg (fun k => y'.1 ≫ k) hh).trans y'.2)⟩
  have e1 : pushLE hle ((Scheme.nilpPoints.mapHom (P.restrict U').fM (P.restrict U').f (P.restrict U').p
      (P.restrict U').hp).app B y') = (Scheme.nilpPoints.mapHom (P.restrict U).fM (P.restrict U).f (P.restrict U).p
      (P.restrict U).hp).app B y := by
    symm
    apply pushLE_eq hle
    show (y.1 ≫ (P.p ∣_ U)) ≫ U.ι = (y'.1 ≫ (P.p ∣_ U')) ≫ U'.ι
    have h1 := morphismRestrict_ι P.p U
    have h2 := morphismRestrict_ι P.p U'
    calc (y.1 ≫ (P.p ∣_ U)) ≫ U.ι = y.1 ≫ ((P.p ∣_ U) ≫ U.ι) := Category.assoc _ _ _
      _ = y.1 ≫ ((P.p ⁻¹ᵁ U).ι ≫ P.p) := congrArg (fun k => y.1 ≫ k) h1
      _ = (y'.1 ≫ P.M.homOfLE _) ≫ ((P.p ⁻¹ᵁ U).ι ≫ P.p) := rfl
      _ = y'.1 ≫ ((P.p ⁻¹ᵁ U').ι ≫ P.p) := by
          have hh : P.M.homOfLE (Scheme.Hom.preimage_mono P.p hle) ≫ (P.p ⁻¹ᵁ U).ι ≫ P.p = (P.p ⁻¹ᵁ U').ι ≫ P.p := by
            rw [← Category.assoc, Scheme.homOfLE_ι]
          exact (Category.assoc _ _ _).trans (congrArg (fun k => y'.1 ≫ k) hh)
      _ = y'.1 ≫ ((P.p ∣_ U') ≫ U'.ι) := (congrArg (fun k => y'.1 ≫ k) h2).symm
      _ = _ := (Category.assoc _ _ _).symm
  have e2 : (F.res U).u B hB y = (F.res U').u B hB y' := by
    simp only [res_u]
    congr 1
    apply Subtype.ext
    show (y'.1 ≫ P.M.homOfLE _) ≫ (P.p ⁻¹ᵁ U).ι = y'.1 ≫ (P.p ⁻¹ᵁ U').ι
    exact (Category.assoc _ _ _).trans (congrArg (fun k => y'.1 ≫ k) (Scheme.homOfLE_ι _ _))
  show F.chart hU hW h B hB (pushLE hle _) = _
  rw [e1, F.chart_factors hU hW h B hB y, e2]

theorem chart_indep {U₁ U₂ : P.X.Opens} {W₁ W₂ : T.Opens} (hU₁ : IsAffineOpen U₁) (hW₁ : IsAffineOpen W₁)
    (h₁ : F.GoodPt U₁ W₁) (hU₂ : IsAffineOpen U₂) (hW₂ : IsAffineOpen W₂) (h₂ : F.GoodPt U₂ W₂)
    {U' : P.X.Opens} (hle₁ : U' ≤ U₁) (hle₂ : U' ≤ U₂)
    (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (w : (Scheme.nilpPoints (P.restrict U').f).obj B) :
    F.chart hU₁ hW₁ h₁ B hB (pushLE hle₁ w) = F.chart hU₂ hW₂ h₂ B hB (pushLE hle₂ w) :=
  (F.res U').uniq (fun B _ _ hB w => F.chart hU₁ hW₁ h₁ B hB (pushLE hle₁ w))
    (fun B _ _ hB w => F.chart hU₂ hW₂ h₂ B hB (pushLE hle₂ w))
    ((F.chart_nat hU₁ hW₁ h₁).precomp (P.X.homOfLE hle₁)
      (show P.X.homOfLE hle₁ ≫ U₁.ι ≫ P.f = U'.ι ≫ P.f by rw [← Category.assoc, Scheme.homOfLE_ι]))
    ((F.chart_nat hU₂ hW₂ h₂).precomp (P.X.homOfLE hle₂)
      (show P.X.homOfLE hle₂ ≫ U₂.ι ≫ P.f = U'.ι ≫ P.f by rw [← Category.assoc, Scheme.homOfLE_ι]))
    (F.chart_pushLE_factors hle₁ hU₁ hW₁ h₁) (F.chart_pushLE_factors hle₂ hU₂ hW₂ h₂) B hB w

end Fam
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Pkg P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Fam"

end Exist
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Pkg P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Fam"

section Glue

variable {P : Pkg 𝒪 G} {π : 𝒪} {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of 𝒪)} (F : Fam P π T t)
variable [IsNoetherianRing 𝒪] [Finite G]

namespace Fam

section PerB

variable {B : Type} [CommRing B] [Algebra 𝒪 B]

omit F in

@[reducible] def algΓ (V : (Spec (CommRingCat.of B)).Opens) (hV : IsAffineOpen V) :
    Algebra 𝒪 Γ(Spec (CommRingCat.of B), V) :=
  (overHom (hV.fromSpec ≫ Scheme.specOver (𝒪 := 𝒪) B)).toAlgebra

omit [IsNoetherianRing 𝒪] [Finite G] in
theorem algΓ_spec (V : (Spec (CommRingCat.of B)).Opens) (hV : IsAffineOpen V) : letI := algΓ (𝒪 := 𝒪) V hV
    Spec.map (CommRingCat.ofHom (algebraMap 𝒪 Γ(Spec (CommRingCat.of B), V))) = hV.fromSpec ≫ Scheme.specOver B :=
  specMap_overHom _

omit [IsNoetherianRing 𝒪] [Finite G] in
theorem algΓ_nil (hB : IsNilpotent (algebraMap 𝒪 B π)) (V : (Spec (CommRingCat.of B)).Opens) (hV : IsAffineOpen V) : letI := algΓ (𝒪 := 𝒪) V hV
    IsNilpotent (algebraMap 𝒪 Γ(Spec (CommRingCat.of B), V) π) := by
  letI := algΓ (𝒪 := 𝒪) V hV
  obtain ⟨ψ, -⟩ := exists_algHom_of_over (𝒪 := 𝒪) hV.fromSpec
  rw [← ψ.comp_algebraMap, RingHom.comp_apply]; exact hB.map _

omit [IsNoetherianRing 𝒪] [Finite G] in

def resPt (z : (Scheme.nilpPoints P.f).obj B) (V : (Spec (CommRingCat.of B)).Opens) (hV : IsAffineOpen V) : letI := algΓ (𝒪 := 𝒪) V hV
    (Scheme.nilpPoints P.f).obj Γ(Spec (CommRingCat.of B), V) :=
  letI := algΓ (𝒪 := 𝒪) V hV
  ⟨hV.fromSpec ≫ z.1, by rw [Category.assoc, z.2]; exact (algΓ_spec (𝒪 := 𝒪) V hV).symm⟩

omit [IsNoetherianRing 𝒪] [Finite G] in
theorem range_resPt (z : (Scheme.nilpPoints P.f).obj B) (V : (Spec (CommRingCat.of B)).Opens) (hV : IsAffineOpen V) {U : P.X.Opens}
    (hsub : Set.range (V.ι ≫ z.1).base ⊆ (U : Set P.X)) :
    letI := algΓ (𝒪 := 𝒪) V hV; Set.range (resPt (𝒪 := 𝒪) z V hV).1.base ⊆ (U : Set P.X) := by
  rintro _ ⟨q, rfl⟩
  show (hV.fromSpec ≫ z.1).base q ∈ (U : Set P.X)
  rw [← hV.isoSpec_inv_ι]
  exact hsub ⟨hV.isoSpec.inv.base q, rfl⟩

def gOf (hB : IsNilpotent (algebraMap 𝒪 B π)) (z : (Scheme.nilpPoints P.f).obj B)
    (V : (Spec (CommRingCat.of B)).Opens) (hV : IsAffineOpen V) {U : P.X.Opens} {W : T.Opens}
    (hU : IsAffineOpen U) (hW : IsAffineOpen W) (h : F.GoodPt U W)
    (hsub : Set.range (V.ι ≫ z.1).base ⊆ (U : Set P.X)) : (↑V : Scheme.{0}) ⟶ T :=
  letI := algΓ (𝒪 := 𝒪) V hV
  hV.isoSpec.hom ≫ (F.chart hU hW h _ (algΓ_nil (𝒪 := 𝒪) hB V hV)
    (liftO P.f U (resPt (𝒪 := 𝒪) z V hV) (range_resPt (𝒪 := 𝒪) z V hV hsub))).1

theorem gOf_over (hB : IsNilpotent (algebraMap 𝒪 B π)) (z : (Scheme.nilpPoints P.f).obj B)
    (V : (Spec (CommRingCat.of B)).Opens) (hV : IsAffineOpen V) {U : P.X.Opens} {W : T.Opens}
    (hU : IsAffineOpen U) (hW : IsAffineOpen W) (h : F.GoodPt U W)
    (hsub : Set.range (V.ι ≫ z.1).base ⊆ (U : Set P.X)) :
    F.gOf hB z V hV hU hW h hsub ≫ t = V.ι ≫ Scheme.specOver B := by
  letI := algΓ (𝒪 := 𝒪) V hV
  unfold gOf
  rw [Category.assoc, (F.chart hU hW h _ _ _).2]
  have hA := algΓ_spec (𝒪 := 𝒪) V hV
  refine (congrArg (fun k => hV.isoSpec.hom ≫ k) hA).trans ?_
  rw [← Category.assoc, ← hV.isoSpec_inv_ι, Iso.hom_inv_id_assoc]

theorem gOf_indep (hB : IsNilpotent (algebraMap 𝒪 B π)) (z : (Scheme.nilpPoints P.f).obj B)
    (V : (Spec (CommRingCat.of B)).Opens) (hV : IsAffineOpen V)
    {U₁ : P.X.Opens} {W₁ : T.Opens} (hU₁ : IsAffineOpen U₁) (hW₁ : IsAffineOpen W₁) (h₁ : F.GoodPt U₁ W₁)
    (hsub₁ : Set.range (V.ι ≫ z.1).base ⊆ (U₁ : Set P.X))
    {U₂ : P.X.Opens} {W₂ : T.Opens} (hU₂ : IsAffineOpen U₂) (hW₂ : IsAffineOpen W₂) (h₂ : F.GoodPt U₂ W₂)
    (hsub₂ : Set.range (V.ι ≫ z.1).base ⊆ (U₂ : Set P.X)) :
    F.gOf hB z V hV hU₁ hW₁ h₁ hsub₁ = F.gOf hB z V hV hU₂ hW₂ h₂ hsub₂ := by
  letI := algΓ (𝒪 := 𝒪) V hV
  unfold gOf
  congr 2
  have hsub : Set.range (V.ι ≫ z.1).base ⊆ ((U₁ ⊓ U₂ : P.X.Opens) : Set P.X) := fun x hx => ⟨hsub₁ hx, hsub₂ hx⟩
  let w := liftO P.f (U₁ ⊓ U₂) (resPt (𝒪 := 𝒪) z V hV) (range_resPt (𝒪 := 𝒪) z V hV hsub)
  have e₁ : liftO P.f U₁ (resPt (𝒪 := 𝒪) z V hV) (range_resPt (𝒪 := 𝒪) z V hV hsub₁) = pushLE inf_le_left w :=
    pushLE_eq _ _ _ ((IsOpenImmersion.lift_fac _ _ _).trans (IsOpenImmersion.lift_fac _ _ _).symm)
  have e₂ : liftO P.f U₂ (resPt (𝒪 := 𝒪) z V hV) (range_resPt (𝒪 := 𝒪) z V hV hsub₂) = pushLE inf_le_right w :=
    pushLE_eq _ _ _ ((IsOpenImmersion.lift_fac _ _ _).trans (IsOpenImmersion.lift_fac _ _ _).symm)
  rw [e₁, e₂]
  exact F.chart_indep hU₁ hW₁ h₁ hU₂ hW₂ h₂ inf_le_left inf_le_right _ _ w

theorem gOf_comp (hB : IsNilpotent (algebraMap 𝒪 B π)) (z : (Scheme.nilpPoints P.f).obj B)
    (V₁ V₂ : (Spec (CommRingCat.of B)).Opens) (hV₁ : IsAffineOpen V₁) (hV₂ : IsAffineOpen V₂)
    (κ : (↑V₁ : Scheme.{0}) ⟶ ↑V₂) (hκ : κ ≫ V₂.ι = V₁.ι)
    {U : P.X.Opens} {W : T.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W) (h : F.GoodPt U W)
    (hsub₁ : Set.range (V₁.ι ≫ z.1).base ⊆ (U : Set P.X)) (hsub₂ : Set.range (V₂.ι ≫ z.1).base ⊆ (U : Set P.X)) :
    κ ≫ F.gOf hB z V₂ hV₂ hU hW h hsub₂ = F.gOf hB z V₁ hV₁ hU hW h hsub₁ := by
  letI i₁ : Algebra 𝒪 Γ(Spec (CommRingCat.of B), V₁) := algΓ (𝒪 := 𝒪) V₁ hV₁
  letI i₂ : Algebra 𝒪 Γ(Spec (CommRingCat.of B), V₂) := algΓ (𝒪 := 𝒪) V₂ hV₂
  unfold gOf
  rw [← cancel_epi hV₁.isoSpec.inv, Iso.inv_hom_id_assoc, ← Category.assoc, ← Category.assoc]
  let φ := (hV₁.isoSpec.inv ≫ κ) ≫ hV₂.isoSpec.hom
  have hφ' : φ ≫ hV₂.fromSpec = hV₁.fromSpec := by
    simp only [φ, Category.assoc]
    rw [← hV₂.isoSpec_inv_ι, Iso.hom_inv_id_assoc, hκ, hV₁.isoSpec_inv_ι]
  have hφ : φ ≫ Scheme.specOver (𝒪 := 𝒪) (Γ(Spec (CommRingCat.of B), V₂)) =
      Scheme.specOver (𝒪 := 𝒪) (Γ(Spec (CommRingCat.of B), V₁)) :=
    calc φ ≫ Scheme.specOver (𝒪 := 𝒪) (Γ(Spec (CommRingCat.of B), V₂)) = φ ≫ (hV₂.fromSpec ≫ Scheme.specOver B) :=
          congrArg (fun k => φ ≫ k) (algΓ_spec (𝒪 := 𝒪) V₂ hV₂)
      _ = hV₁.fromSpec ≫ Scheme.specOver B := by rw [← Category.assoc, hφ']
      _ = _ := (algΓ_spec (𝒪 := 𝒪) V₁ hV₁).symm
  symm
  refine (F.chart_nat hU hW h).val_comp' (algΓ_nil (𝒪 := 𝒪) hB V₂ hV₂) (algΓ_nil (𝒪 := 𝒪) hB V₁ hV₁)
    φ hφ _ _ ?_
  rw [← cancel_mono U.ι]
  show IsOpenImmersion.lift _ _ _ ≫ U.ι = (φ ≫ IsOpenImmersion.lift _ _ _) ≫ U.ι
  rw [IsOpenImmersion.lift_fac, Category.assoc, IsOpenImmersion.lift_fac]
  show hV₁.fromSpec ≫ z.1 = φ ≫ hV₂.fromSpec ≫ z.1
  rw [← Category.assoc φ, hφ']

@[reducible] def Idx (z : (Scheme.nilpPoints P.f).obj B) : Type := { V : (Spec (CommRingCat.of B)).Opens // IsAffineOpen V ∧ ∃ U : P.X.Opens, ∃ W : T.Opens,
    IsAffineOpen U ∧ IsAffineOpen W ∧ F.GoodPt U W ∧ Set.range (V.ι ≫ z.1).base ⊆ (U : Set P.X) }

omit [IsNoetherianRing 𝒪] in

theorem exists_idx (hB : IsNilpotent (algebraMap 𝒪 B π)) (z : (Scheme.nilpPoints P.f).obj B)
    (O : (Spec (CommRingCat.of B)).Opens) (q : Spec (CommRingCat.of B)) (hq : q ∈ O) :
    ∃ j : F.Idx z, q ∈ j.1 ∧ j.1 ≤ O := by
  have hx : IsNilAt P.f π (z.1.base q) := isNilAt_base P.f π hB z q
  obtain ⟨U, hU, hxU, -, W, hW, hgood⟩ := F.exists_good _ hx ⊤ trivial
  obtain ⟨V, hV, hqV, hVsub⟩ := exists_isAffineOpen_mem_and_subset (X := Spec (CommRingCat.of B)) (x := q)
    (U := z.1 ⁻¹ᵁ U ⊓ O) ⟨hxU, hq⟩
  refine ⟨⟨V, hV, U, W, hU, hW, hgood, ?_⟩, hqV, fun y hy => (hVsub hy).2⟩
  rintro _ ⟨y, rfl⟩
  exact (hVsub y.2).1

theorem idx_isOpenCover (hB : IsNilpotent (algebraMap 𝒪 B π)) (z : (Scheme.nilpPoints P.f).obj B) :
    TopologicalSpace.IsOpenCover (fun j : F.Idx z => j.1) := by
  apply top_le_iff.mp
  intro q _
  obtain ⟨j, hj, -⟩ := F.exists_idx hB z ⊤ q trivial
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨j, hj⟩

def cov (hB : IsNilpotent (algebraMap 𝒪 B π)) (z : (Scheme.nilpPoints P.f).obj B) : (Spec (CommRingCat.of B)).OpenCover :=
  (Spec (CommRingCat.of B)).openCoverOfIsOpenCover (fun j : F.Idx z => j.1) (F.idx_isOpenCover hB z)

scoped instance covPreorder (hB : IsNilpotent (algebraMap 𝒪 B π)) (z : (Scheme.nilpPoints P.f).obj B) :
    Preorder (F.cov hB z).I₀ := inferInstanceAs (Preorder (F.Idx z))

scoped instance covDirected (hB : IsNilpotent (algebraMap 𝒪 B π)) (z : (Scheme.nilpPoints P.f).obj B) :
    (F.cov hB z).LocallyDirected :=
  .ofIsBasisOpensRange (by
    intro i j
    show i.1 ≤ j.1 ↔ (i.1.ι).opensRange ≤ (j.1.ι).opensRange
    rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι]) (by
    rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro O q hq
    obtain ⟨j, hj, hjO⟩ := F.exists_idx hB z O q hq
    exact ⟨j.1, ⟨j, (Scheme.Opens.opensRange_ι _)⟩, hj, hjO⟩)

def piece (hB : IsNilpotent (algebraMap 𝒪 B π)) (z : (Scheme.nilpPoints P.f).obj B) (j : F.Idx z) : (↑j.1 : Scheme.{0}) ⟶ T :=
  F.gOf hB z j.1 j.2.1 j.2.2.choose_spec.choose_spec.1 j.2.2.choose_spec.choose_spec.2.1
    j.2.2.choose_spec.choose_spec.2.2.1 j.2.2.choose_spec.choose_spec.2.2.2

theorem piece_eq (hB : IsNilpotent (algebraMap 𝒪 B π)) (z : (Scheme.nilpPoints P.f).obj B) (j : F.Idx z) {U : P.X.Opens} {W : T.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W)
    (h : F.GoodPt U W) (hsub : Set.range (j.1.ι ≫ z.1).base ⊆ (U : Set P.X)) :
    F.piece hB z j = F.gOf hB z j.1 j.2.1 hU hW h hsub :=
  F.gOf_indep hB z _ _ _ _ _ _ _ _ _ _

theorem piece_compat (hB : IsNilpotent (algebraMap 𝒪 B π)) (z : (Scheme.nilpPoints P.f).obj B) :
    ∀ {i j : (F.cov hB z).I₀} (hij : i ⟶ j), (F.cov hB z).trans hij ≫ F.piece hB z j = F.piece hB z i := by
    intro i j hij
    have hκ : (F.cov hB z).trans hij ≫ j.1.ι = i.1.ι := (F.cov hB z).trans_map hij
    have hle : i.1 ≤ j.1 := by
      have := leOfHom hij; exact this
    obtain ⟨U, W, hU, hW, h, hsubj⟩ := j.2.2
    have hsubi : Set.range (i.1.ι ≫ z.1).base ⊆ (U : Set P.X) := by
      rintro _ ⟨q, rfl⟩
      have hq : (i.1.ι ≫ z.1).base q = (j.1.ι ≫ z.1).base (((F.cov hB z).trans hij).base q) := by
        rw [← hκ]; rfl
      rw [hq]; exact hsubj ⟨_, rfl⟩
    rw [F.piece_eq hB z j hU hW h hsubj, F.piece_eq hB z i hU hW h hsubi]
    exact F.gOf_comp hB z i.1 j.1 i.2.1 j.2.1 _ hκ hU hW h hsubi hsubj

def glued (hB : IsNilpotent (algebraMap 𝒪 B π)) (z : (Scheme.nilpPoints P.f).obj B) : Spec (CommRingCat.of B) ⟶ T :=
  (F.cov hB z).glueMorphismsOfLocallyDirected (F.piece hB z) (F.piece_compat hB z)

theorem ι_glued (hB : IsNilpotent (algebraMap 𝒪 B π)) (z : (Scheme.nilpPoints P.f).obj B) (j : F.Idx z) : j.1.ι ≫ F.glued hB z = F.piece hB z j :=
  (F.cov hB z).map_glueMorphismsOfLocallyDirected (F.piece hB z) (F.piece_compat hB z) j

theorem glued_spec (hB : IsNilpotent (algebraMap 𝒪 B π)) (z : (Scheme.nilpPoints P.f).obj B)
    (V : (Spec (CommRingCat.of B)).Opens) (hV : IsAffineOpen V) {U : P.X.Opens} {W : T.Opens}
    (hU : IsAffineOpen U) (hW : IsAffineOpen W) (h : F.GoodPt U W)
    (hsub : Set.range (V.ι ≫ z.1).base ⊆ (U : Set P.X)) :
    V.ι ≫ F.glued hB z = F.gOf hB z V hV hU hW h hsub := by
  let j : F.Idx z := ⟨V, hV, U, W, hU, hW, h, hsub⟩
  exact (F.ι_glued hB z j).trans (F.piece_eq hB z j hU hW h hsub)

theorem glued_over (hB : IsNilpotent (algebraMap 𝒪 B π)) (z : (Scheme.nilpPoints P.f).obj B) :
    F.glued hB z ≫ t = Scheme.specOver B := by
  apply (F.cov hB z).hom_ext
  intro j
  show j.1.ι ≫ _ = j.1.ι ≫ _
  rw [← Category.assoc, F.ι_glued, piece, F.gOf_over]

end PerB
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Pkg P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Fam"

def ubar : FamMap π P.f t := fun B _ _ hB z => ⟨F.glued hB z, F.glued_over hB z⟩

end Fam
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Pkg P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Fam"

end Glue
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Pkg P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Fam"

section Final

variable {P : Pkg 𝒪 G} {π : 𝒪} {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of 𝒪)} (F : Fam P π T t)
variable [IsNoetherianRing 𝒪] [Finite G]

namespace Fam

theorem gOf_comp₂ {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
    (z : (Scheme.nilpPoints P.f).obj B) (z₂ : (Scheme.nilpPoints P.f).obj B')
    (ψ : Spec (CommRingCat.of B') ⟶ Spec (CommRingCat.of B)) (hψ : ψ ≫ Scheme.specOver (𝒪 := 𝒪) B = Scheme.specOver B')
    (hz₂ : z₂.1 = ψ ≫ z.1)
    (V : (Spec (CommRingCat.of B)).Opens) (hV : IsAffineOpen V) (V₂ : (Spec (CommRingCat.of B')).Opens) (hV₂ : IsAffineOpen V₂)
    (κ : (↑V₂ : Scheme.{0}) ⟶ ↑V) (hκ : κ ≫ V.ι = V₂.ι ≫ ψ)
    {U : P.X.Opens} {W : T.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W) (h : F.GoodPt U W)
    (hsub : Set.range (V.ι ≫ z.1).base ⊆ (U : Set P.X)) (hsub₂ : Set.range (V₂.ι ≫ z₂.1).base ⊆ (U : Set P.X)) :
    κ ≫ F.gOf hB z V hV hU hW h hsub = F.gOf hB' z₂ V₂ hV₂ hU hW h hsub₂ := by
  letI i₁ : Algebra 𝒪 Γ(Spec (CommRingCat.of B'), V₂) := algΓ (𝒪 := 𝒪) V₂ hV₂
  letI i₂ : Algebra 𝒪 Γ(Spec (CommRingCat.of B), V) := algΓ (𝒪 := 𝒪) V hV
  unfold gOf
  rw [← cancel_epi hV₂.isoSpec.inv, Iso.inv_hom_id_assoc, ← Category.assoc, ← Category.assoc]
  let φ := (hV₂.isoSpec.inv ≫ κ) ≫ hV.isoSpec.hom
  have hφ' : φ ≫ hV.fromSpec = hV₂.fromSpec ≫ ψ := by
    simp only [φ, Category.assoc]
    rw [← hV.isoSpec_inv_ι, Iso.hom_inv_id_assoc, hκ, ← Category.assoc, hV₂.isoSpec_inv_ι]
  have hφ : φ ≫ Scheme.specOver (𝒪 := 𝒪) (Γ(Spec (CommRingCat.of B), V)) =
      Scheme.specOver (𝒪 := 𝒪) (Γ(Spec (CommRingCat.of B'), V₂)) :=
    calc φ ≫ Scheme.specOver (𝒪 := 𝒪) (Γ(Spec (CommRingCat.of B), V)) = φ ≫ (hV.fromSpec ≫ Scheme.specOver B) :=
          congrArg (fun k => φ ≫ k) (algΓ_spec (𝒪 := 𝒪) V hV)
      _ = hV₂.fromSpec ≫ ψ ≫ Scheme.specOver B := by rw [← Category.assoc, hφ', Category.assoc]
      _ = hV₂.fromSpec ≫ Scheme.specOver B' := by rw [hψ]
      _ = _ := (algΓ_spec (𝒪 := 𝒪) V₂ hV₂).symm
  symm
  refine (F.chart_nat hU hW h).val_comp' (algΓ_nil (𝒪 := 𝒪) hB V hV) (algΓ_nil (𝒪 := 𝒪) hB' V₂ hV₂)
    φ hφ _ _ ?_
  rw [← cancel_mono U.ι]
  show IsOpenImmersion.lift _ _ _ ≫ U.ι = (φ ≫ IsOpenImmersion.lift _ _ _) ≫ U.ι
  rw [IsOpenImmersion.lift_fac, Category.assoc, IsOpenImmersion.lift_fac]
  show hV₂.fromSpec ≫ z₂.1 = φ ≫ hV.fromSpec ≫ z.1
  rw [← Category.assoc φ, hφ', hz₂, Category.assoc]

theorem ubar_nat : IsNatural F.ubar := by
  intro B _ _ B' _ _ hB hB' φa z
  apply Subtype.ext
  simp only [Scheme.nilpPoints_map_val]
  show F.glued hB' ((Scheme.nilpPoints P.f).map φa z) = Spec.map (CommRingCat.ofHom φa.toRingHom) ≫ F.glued hB z
  set ψ := Spec.map (CommRingCat.ofHom φa.toRingHom) with hψdef
  set z₂ := (Scheme.nilpPoints P.f).map φa z with hz₂def
  have hz₂ : z₂.1 = ψ ≫ z.1 := rfl
  have hψ : ψ ≫ Scheme.specOver (𝒪 := 𝒪) B = Scheme.specOver B' := Scheme.specMap_algHom_comp_specOver φa

  let K := { V₂ : (Spec (CommRingCat.of B')).Opens // IsAffineOpen V₂ ∧ ∃ V : (Spec (CommRingCat.of B)).Opens,
    IsAffineOpen V ∧ (∃ U : P.X.Opens, ∃ W : T.Opens, IsAffineOpen U ∧ IsAffineOpen W ∧ F.GoodPt U W ∧
      Set.range (V.ι ≫ z.1).base ⊆ (U : Set P.X)) ∧ Set.range (V₂.ι ≫ ψ).base ⊆ (V : Set (Spec (CommRingCat.of B))) }
  have hK : TopologicalSpace.IsOpenCover (fun k : K => k.1) := by
    apply top_le_iff.mp
    intro q₂ _
    obtain ⟨j, hj, -⟩ := F.exists_idx hB z ⊤ (ψ.base q₂) trivial
    obtain ⟨V₂, hV₂, hq, hsub⟩ := exists_isAffineOpen_mem_and_subset (X := Spec (CommRingCat.of B')) (x := q₂)
      (U := ψ ⁻¹ᵁ j.1) hj
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V₂, hV₂, j.1, j.2.1, j.2.2, ?_⟩, hq⟩
    rintro _ ⟨y, rfl⟩
    exact hsub y.2
  refine Scheme.Cover.hom_ext ((Spec (CommRingCat.of B')).openCoverOfIsOpenCover _ hK) _ _ fun k => ?_
  obtain ⟨V₂, hV₂, V, hV, ⟨U, W, hU, hW, h, hsub⟩, hVV⟩ := k
  show V₂.ι ≫ F.glued hB' z₂ = V₂.ι ≫ ψ ≫ F.glued hB z
  let κ : (↑V₂ : Scheme.{0}) ⟶ ↑V := IsOpenImmersion.lift V.ι (V₂.ι ≫ ψ) (by rw [Scheme.Opens.range_ι]; exact hVV)
  have hκ : κ ≫ V.ι = V₂.ι ≫ ψ := IsOpenImmersion.lift_fac _ _ _
  have hsub₂ : Set.range (V₂.ι ≫ z₂.1).base ⊆ (U : Set P.X) := by
    rintro _ ⟨q, rfl⟩
    have : (V₂.ι ≫ z₂.1).base q = (V.ι ≫ z.1).base (κ.base q) := by
      rw [hz₂, ← Category.assoc, ← hκ]; rfl
    rw [this]; exact hsub ⟨_, rfl⟩
  rw [F.glued_spec hB' z₂ V₂ hV₂ hU hW h hsub₂, ← Category.assoc, ← hκ, Category.assoc,
    F.glued_spec hB z V hV hU hW h hsub]
  exact (F.gOf_comp₂ hB hB' z z₂ ψ hψ hz₂ V hV V₂ hV₂ κ hκ hU hW h hsub hsub₂).symm

theorem ubar_factors : F.Factors F.ubar := by
  intro B _ _ hB y
  apply Subtype.ext
  set z := (Scheme.nilpPoints.mapHom P.fM P.f P.p P.hp).app B y with hzdef
  show F.glued hB z = (F.u B hB y).1
  apply (F.cov hB z).hom_ext
  intro j
  obtain ⟨U, W, hU, hW, h, hsub⟩ := j.2.2
  show j.1.ι ≫ F.glued hB z = j.1.ι ≫ (F.u B hB y).1
  rw [F.glued_spec hB z j.1 j.2.1 hU hW h hsub]
  letI : Algebra 𝒪 Γ(Spec (CommRingCat.of B), j.1) := algΓ (𝒪 := 𝒪) j.1 j.2.1
  have hnil := algΓ_nil (𝒪 := 𝒪) hB j.1 j.2.1
  unfold gOf
  rw [← cancel_epi j.2.1.isoSpec.inv, Iso.inv_hom_id_assoc, ← Category.assoc, j.2.1.isoSpec_inv_ι]

  let yV : (Scheme.nilpPoints P.fM).obj Γ(Spec (CommRingCat.of B), j.1) :=
    ⟨j.2.1.fromSpec ≫ y.1, by rw [Category.assoc, y.2]; exact (algΓ_spec (𝒪 := 𝒪) j.1 j.2.1).symm⟩
  have hyV : Set.range yV.1.base ⊆ ((P.p ⁻¹ᵁ U) : Set P.M) := by
    rintro _ ⟨q, rfl⟩
    show P.p.base ((j.2.1.fromSpec ≫ y.1).base q) ∈ U
    have : P.p.base ((j.2.1.fromSpec ≫ y.1).base q) = (j.1.ι ≫ z.1).base (j.2.1.isoSpec.inv.base q) := by
      rw [← j.2.1.isoSpec_inv_ι]; rfl
    rw [this]; exact hsub ⟨_, rfl⟩
  let y' : (Scheme.nilpPoints (P.restrict U).fM).obj Γ(Spec (CommRingCat.of B), j.1) :=
    liftO P.fM (P.p ⁻¹ᵁ U) yV hyV
  have e1 : liftO P.f U (resPt (𝒪 := 𝒪) z j.1 j.2.1) (range_resPt (𝒪 := 𝒪) z j.1 j.2.1 hsub) =
      (Scheme.nilpPoints.mapHom (P.restrict U).fM (P.restrict U).f (P.restrict U).p (P.restrict U).hp).app _ y' := by
    apply Subtype.ext
    rw [← cancel_mono U.ι]
    show IsOpenImmersion.lift _ _ _ ≫ U.ι = (IsOpenImmersion.lift _ _ _ ≫ (P.p ∣_ U)) ≫ U.ι
    rw [IsOpenImmersion.lift_fac, Category.assoc, morphismRestrict_ι, ← Category.assoc, IsOpenImmersion.lift_fac]
    rfl
  rw [e1, F.chart_factors hU hW h _ hnil y', res_u]
  have e2 : (Scheme.nilpPoints.mapHom (P.restrict U).fM P.fM (P.p ⁻¹ᵁ U).ι rfl).app _ y' = yV :=
    pushO_liftO P.fM (P.p ⁻¹ᵁ U) yV hyV
  rw [e2]
  exact F.nat.val_comp' hB hnil j.2.1.fromSpec (algΓ_spec (𝒪 := 𝒪) j.1 j.2.1).symm y yV rfl

theorem main : ∃ ubar : FamMap π P.f t, IsNatural ubar ∧ F.Factors ubar ∧
    ∀ u' : FamMap π P.f t, IsNatural u' → F.Factors u' →
      ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
        (z : (Scheme.nilpPoints P.f).obj B), u' B hB z = ubar B hB z :=
  ⟨F.ubar, F.ubar_nat, F.ubar_factors, fun u' h' f' B _ _ hB z =>
    F.uniq u' F.ubar h' F.ubar_nat f' F.ubar_factors B hB z⟩

end Fam
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Pkg P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Fam"

end Final
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Pkg P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Fam"

theorem main_unbundled
    {𝒪 : Type} [CommRing 𝒪] [IsNoetherianRing 𝒪] (π : 𝒪)
    {M X : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪)) (f : X ⟶ Spec (CommRingCat.of 𝒪))
    (hlft : LocallyOfFiniteType fM) (hlftX : LocallyOfFiniteType f)
    {G : Type} [Group G] [Finite G] (ρ : G →* Aut M) (hover : ∀ g : G, (ρ g).hom ≫ fM = fM)
    (p : M ⟶ X) (hp : p ≫ f = fM) (hρp : ∀ g : G, (ρ g).hom ≫ p = p)
    (hint : IsIntegralHom p) (haff : IsAffineHom p) (hsurj : Function.Surjective p.base)
    (hsec : ∀ V : X.Opens, Function.Injective (p.app V))
    (hinv : ∀ V : X.Opens, Set.range (p.app V) =
      {s | ∀ g : G, (ρ g).hom.appLE (p ⁻¹ᵁ V) (p ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hρp g]) s = s})
    (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
    (u : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints fM).obj B → (Scheme.nilpPoints t).obj B)
    (hu_nat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
      (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints fM).obj B), u B' hB' ((Scheme.nilpPoints fM).map φ x) = (Scheme.nilpPoints t).map φ (u B hB x))
    (hu_inv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (g : G) (y : (Scheme.nilpPoints fM).obj B),
      u B hB ((Scheme.nilpPoints.mapHom fM fM (ρ g).hom (hover g)).app B y) = u B hB y) :
    ∃ ubar : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B,
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints f).obj B), ubar B' hB' ((Scheme.nilpPoints f).map φ x) = (Scheme.nilpPoints t).map φ (ubar B hB x)) ∧
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints fM).obj B),
        ubar B hB ((Scheme.nilpPoints.mapHom fM f p hp).app B y) = u B hB y) ∧
      ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B,
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
          (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints f).obj B), u' B' hB' ((Scheme.nilpPoints f).map φ x) = (Scheme.nilpPoints t).map φ (u' B hB x)) →
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints fM).obj B),
          u' B hB ((Scheme.nilpPoints.mapHom fM f p hp).app B y) = u B hB y) →
        ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (z : (Scheme.nilpPoints f).obj B), u' B hB z = ubar B hB z :=
  Fam.main (P := ⟨M, X, fM, f, ρ, hover, p, hp, hρp, hint, haff, hsurj, hsec, hinv, hlft, hlftX⟩)
    (π := π) ⟨u, hu_nat, hu_inv⟩

end FQ22
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Pkg P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Fam P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Pkg P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22.Fam P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing.FQ22"

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsNoetherianRing 𝒪] (π : 𝒪)
    {M X : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪)) (f : X ⟶ Spec (CommRingCat.of 𝒪))
    (hlft : LocallyOfFiniteType fM) (hlftX : LocallyOfFiniteType f)
    {G : Type} [Group G] [Finite G] (ρ : G →* Aut M) (hover : ∀ g : G, (ρ g).hom ≫ fM = fM)
    (p : M ⟶ X) (hp : p ≫ f = fM) (hρp : ∀ g : G, (ρ g).hom ≫ p = p)
    (hint : IsIntegralHom p) (haff : IsAffineHom p) (hsurj : Function.Surjective p.base)
    (hsec : ∀ V : X.Opens, Function.Injective (p.app V))
    (hinv : ∀ V : X.Opens, Set.range (p.app V) =
      {s | ∀ g : G, (ρ g).hom.appLE (p ⁻¹ᵁ V) (p ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hρp g]) s = s})
    (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
    (u : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints fM).obj B → (Scheme.nilpPoints t).obj B)
    (hu_nat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
      (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints fM).obj B), u B' hB' ((Scheme.nilpPoints fM).map φ x) = (Scheme.nilpPoints t).map φ (u B hB x))
    (hu_inv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (g : G) (y : (Scheme.nilpPoints fM).obj B),
      u B hB ((Scheme.nilpPoints.mapHom fM fM (ρ g).hom (hover g)).app B y) = u B hB y) :
    ∃ ubar : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B,
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints f).obj B), ubar B' hB' ((Scheme.nilpPoints f).map φ x) = (Scheme.nilpPoints t).map φ (ubar B hB x)) ∧
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints fM).obj B),
        ubar B hB ((Scheme.nilpPoints.mapHom fM f p hp).app B y) = u B hB y) ∧
      ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B,
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
          (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints f).obj B), u' B' hB' ((Scheme.nilpPoints f).map φ x) = (Scheme.nilpPoints t).map φ (u' B hB x)) →
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints fM).obj B),
          u' B hB ((Scheme.nilpPoints.mapHom fM f p hp).app B y) = u B hB y) →
        ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (z : (Scheme.nilpPoints f).obj B), u' B hB z = ubar B hB z :=
  FQ22.main_unbundled π fM f hlft hlftX ρ hover p hp hρp hint haff hsurj hsec hinv T t u hu_nat hu_inv

end S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing (solution)
