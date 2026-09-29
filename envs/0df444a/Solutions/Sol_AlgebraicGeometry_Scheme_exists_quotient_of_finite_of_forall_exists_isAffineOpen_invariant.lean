-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/e267b16b-0d45-542d-a8f1-0ae91ef02c89

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open scoped Pointwise
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v

namespace P2mKcFinQuot

section SchemeHelpers

variable {X Y : Scheme.{u}}

lemma appLE_congr_hom {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h; rfl

lemma map_eqToHom_op_surjective {U V : X.Opens} (h : U = V) :
    Function.Surjective (X.presheaf.map (eqToHom h).op) := by
  subst h
  simp only [eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
  exact Function.surjective_id

lemma id_appLE (U V : X.Opens) (e : V ≤ U) :
    (𝟙 X : X ⟶ X).appLE U V e = X.presheaf.map (homOfLE e).op := by
  rw [Scheme.Hom.appLE, Scheme.Hom.id_app]; erw [Category.id_comp]; rfl

end SchemeHelpers

section EqualizerShape

p2m_open "CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.WalkingParallelPairHom"

variable (K : WalkingParallelPairᵒᵖ ⥤ CommRingCat.{u})

abbrev lop : (op one : WalkingParallelPairᵒᵖ) ⟶ op zero := Quiver.Hom.op (left : WalkingParallelPair.zero ⟶ one)

abbrev rop : (op one : WalkingParallelPairᵒᵖ) ⟶ op zero := Quiver.Hom.op (right : WalkingParallelPair.zero ⟶ one)

theorem limitπ_one_injective : Function.Injective (limit.π K (op one)) := by
  intro a b h
  refine Concrete.limit_ext K a b fun j => ?_
  obtain ⟨j⟩ := j
  cases j
  · have w := limit.w K lop
    rw [← w]
    simp only [CommRingCat.comp_apply, h]
  · exact h

theorem range_limitπ_one :
    Set.range (limit.π K (op one)) = {s | K.map lop s = K.map rop s} := by
  ext s
  constructor
  · rintro ⟨a, rfl⟩
    have h1 := ConcreteCategory.congr_hom (limit.w K lop) a
    have h2 := ConcreteCategory.congr_hom (limit.w K rop) a
    exact h1.trans h2.symm
  · intro hs
    let σ : ∀ j : WalkingParallelPairᵒᵖ, (K ⋙ forget CommRingCat).obj j
      | ⟨.one⟩ => s
      | ⟨.zero⟩ => K.map lop s
    have hσ : σ ∈ (K ⋙ forget CommRingCat).sections := by
      rintro ⟨j⟩ ⟨j'⟩ ⟨φ⟩
      change WalkingParallelPairHom j' j at φ
      rcases φ with (_ | _ | _)
      · rfl
      · exact hs.symm
      · have : (op (WalkingParallelPairHom.id j) : op j ⟶ op j) = 𝟙 (op j) := rfl
        rw [this, CategoryTheory.Functor.map_id]; rfl
    let E := Types.isLimitEquivSections (isLimitOfPreserves (forget CommRingCat) (limit.isLimit K))
    refine ⟨E.symm ⟨σ, hσ⟩, ?_⟩
    have := Types.isLimitEquivSections_symm_apply
      (isLimitOfPreserves (forget CommRingCat) (limit.isLimit K)) ⟨σ, hσ⟩ (op one)
    exact this

end EqualizerShape

section Setup

variable {X : Scheme.{u}} {G : Type v} [Group G] [Finite G] (ρ : G →* Aut X)

@[nolint unusedArguments]
noncomputable def cop (_ : G →* Aut X) : Scheme.{u} := ∐ fun _ : G => X

noncomputable abbrev copι (g : G) : X ⟶ cop ρ := Sigma.ι (fun _ : G => X) g

noncomputable def actMap : cop ρ ⟶ X := Sigma.desc fun g => (ρ g).hom

noncomputable def prMap : cop ρ ⟶ X := Sigma.desc fun _ => 𝟙 X

@[reassoc (attr := simp)]
lemma ι_actMap (g : G) : copι ρ g ≫ actMap ρ = (ρ g).hom := Sigma.ι_desc _ _

@[reassoc (attr := simp)]
lemma ι_prMap (g : G) : copι ρ g ≫ prMap ρ = 𝟙 X := Sigma.ι_desc _ _

noncomputable abbrev fL : (cop ρ).toLocallyRingedSpace ⟶ X.toLocallyRingedSpace :=
  (actMap ρ).toLRSHom

noncomputable abbrev gL : (cop ρ).toLocallyRingedSpace ⟶ X.toLocallyRingedSpace :=
  (prMap ρ).toLRSHom

noncomputable def QL : LocallyRingedSpace.{u} := LocallyRingedSpace.coequalizer (fL ρ) (gL ρ)

noncomputable def cofork : Cofork (fL ρ) (gL ρ) := LocallyRingedSpace.coequalizerCofork _ _

noncomputable def coforkIsColimit : IsColimit (cofork ρ) :=
  LocallyRingedSpace.coequalizerCoforkIsColimit _ _

noncomputable def πL : X.toLocallyRingedSpace ⟶ QL ρ := (cofork ρ).π

lemma cofork_π : (cofork ρ).π = πL ρ := rfl

lemma πL_toShHom :
    (πL ρ).toShHom = coequalizer.π (fL ρ).toShHom (gL ρ).toShHom := rfl

private lemma _root_.P2mKcFinQuot.condition : fL ρ ≫ πL ρ = gL ρ ≫ πL ρ := (cofork ρ).condition

p2m_export "P2mKcFinQuot" "condition"
lemma act_comp_πL (g : G) : (ρ g).hom.toLRSHom ≫ πL ρ = πL ρ := by
  have h₁ : (copι ρ g).toLRSHom ≫ fL ρ = (ρ g).hom.toLRSHom := by
    rw [← Scheme.Hom.comp_toLRSHom, ι_actMap]
  have h₂ : (copι ρ g).toLRSHom ≫ gL ρ = 𝟙 _ := by
    rw [← Scheme.Hom.comp_toLRSHom, ι_prMap]; rfl
  rw [← h₁, Category.assoc, condition, ← Category.assoc, h₂, Category.id_comp]

lemma act_apply_πL (g : G) (x : X) : (πL ρ).base ((ρ g).hom.base x) = (πL ρ).base x := by
  conv_rhs => rw [← act_comp_πL ρ g]
  rfl

lemma isQuotientMap_πL : Topology.IsQuotientMap (πL ρ).base := by
  have := TopCat.isQuotientMap_of_isColimit_cofork _
    (isColimitCoforkMapOfIsColimit (SheafedSpace.forget _) _
      (coequalizerIsCoequalizer (fL ρ).toShHom (gL ρ).toShHom))
  exact this

lemma πL_surjective : Function.Surjective (πL ρ).base := (isQuotientMap_πL ρ).surjective

lemma isOpen_iff_πL (s : Set (QL ρ)) : IsOpen s ↔ IsOpen ((πL ρ).base ⁻¹' s) :=
  ((isQuotientMap_πL ρ).isOpen_preimage).symm

lemma exists_copι_eq (z : cop ρ) : ∃ (g : G) (x : X), (copι ρ g).base x = z := by
  obtain ⟨g, x, h⟩ := (sigmaOpenCover (fun _ : G => X)).exists_eq z
  exact ⟨g, x, by simp at h; exact h⟩

lemma rel_iff (a b : X) :
    Function.Coequalizer.Rel (actMap ρ).base (prMap ρ).base a b ↔ ∃ g : G, (ρ g).hom.base b = a := by
  constructor
  · rintro ⟨z⟩
    obtain ⟨g, x, rfl⟩ := exists_copι_eq ρ z
    refine ⟨g, ?_⟩
    have h1 : (actMap ρ).base ((copι ρ g).base x) = (ρ g).hom.base x := by
      change (copι ρ g ≫ actMap ρ).base x = _; rw [ι_actMap]
    have h2 : (prMap ρ).base ((copι ρ g).base x) = x := by
      change (copι ρ g ≫ prMap ρ).base x = _; rw [ι_prMap]; rfl
    rw [h1, h2]
  · rintro ⟨g, rfl⟩
    have h1 : (actMap ρ).base ((copι ρ g).base b) = (ρ g).hom.base b := by
      change (copι ρ g ≫ actMap ρ).base b = _; rw [ι_actMap]
    have h2 : (prMap ρ).base ((copι ρ g).base b) = b := by
      change (copι ρ g ≫ prMap ρ).base b = _; rw [ι_prMap]; rfl
    conv_lhs => rw [← h1]
    conv_rhs => rw [← h2]
    exact ⟨_⟩

omit [Finite G] in
lemma act_inv_apply (g : G) (x : X) : (ρ g⁻¹).hom.base ((ρ g).hom.base x) = x := by
  change ((ρ g).hom ≫ (ρ g⁻¹).hom).base x = x
  rw [map_inv, Aut.Aut_inv_def, Iso.symm_hom, Iso.hom_inv_id]
  rfl

omit [Finite G] in
lemma act_mul_apply (g h : G) (x : X) :
    (ρ (g * h)).hom.base x = (ρ g).hom.base ((ρ h).hom.base x) := by
  change _ = ((ρ h).hom ≫ (ρ g).hom).base x
  rw [map_mul, Aut.Aut_mul_def]
  rfl

omit [Finite G] in
lemma act_one_apply (x : X) : (ρ 1).hom.base x = x := by
  rw [map_one]; rfl

lemma eqvGen_rel_iff (a b : X) :
    Relation.EqvGen (Function.Coequalizer.Rel (actMap ρ).base (prMap ρ).base) a b ↔
      ∃ g : G, (ρ g).hom.base a = b := by
  constructor
  · intro h
    induction h with
    | rel a b hab =>
      obtain ⟨g, rfl⟩ := (rel_iff ρ a b).mp hab
      exact ⟨g⁻¹, act_inv_apply ρ g b⟩
    | refl a => exact ⟨1, act_one_apply ρ a⟩
    | symm a b _ ih =>
      obtain ⟨g, rfl⟩ := ih
      exact ⟨g⁻¹, act_inv_apply ρ g a⟩
    | trans a b c _ _ ih₁ ih₂ =>
      obtain ⟨g, rfl⟩ := ih₁
      obtain ⟨g', rfl⟩ := ih₂
      exact ⟨g' * g, act_mul_apply ρ g' g a⟩
  · rintro ⟨g, rfl⟩
    apply Relation.EqvGen.symm
    apply Relation.EqvGen.rel
    exact (rel_iff ρ _ _).mpr ⟨g, rfl⟩

lemma πL_eq_iff (x x' : X) :
    (πL ρ).base x = (πL ρ).base x' ↔ ∃ g : G, (ρ g).hom.base x = x' := by
  constructor
  · intro hxx
    have h₃ := isColimitCoforkMapOfIsColimit (forget TopCat) _
      (isColimitCoforkMapOfIsColimit (SheafedSpace.forget _) _
        (coequalizerIsCoequalizer (fL ρ).toShHom (gL ρ).toShHom))
    have e'' := (mono_iff_injective (h₃.coconePointUniqueUpToIso
      (Types.coequalizerColimit _ _).isColimit).inv).mp inferInstance
    have hfac := h₃.comp_coconePointUniqueUpToIso_inv (Types.coequalizerColimit _ _).2
      WalkingParallelPair.one
    have h1 := ConcreteCategory.congr_hom hfac x
    have h2 := ConcreteCategory.congr_hom hfac x'
    have key : Relation.EqvGen
        (Function.Coequalizer.Rel (actMap ρ).base (prMap ρ).base) x x' := by
      apply Quot.eqvGen_exact
      apply e''
      exact h1.trans (hxx.trans h2.symm)
    exact (eqvGen_rel_iff ρ x x').mp key
  · rintro ⟨g, rfl⟩
    exact (act_apply_πL ρ g x).symm

end Setup

section Sections

variable {X : Scheme.{u}} {G : Type v} [Group G] [Finite G] (ρ : G →* Aut X)

noncomputable abbrev Fps : SheafedSpace CommRingCat.{u} ⥤ PresheafedSpace CommRingCat.{u} :=
  SheafedSpace.forgetToPresheafedSpace

noncomputable abbrev fSh : (cop ρ).toSheafedSpace ⟶ X.toSheafedSpace := (fL ρ).toShHom

noncomputable abbrev gSh : (cop ρ).toSheafedSpace ⟶ X.toSheafedSpace := (gL ρ).toShHom

noncomputable abbrev ιSh (k : G) : X.toSheafedSpace ⟶ (cop ρ).toSheafedSpace :=
  (copι ρ k).toLRSHom.toShHom

noncomputable abbrev aSh (k : G) : X.toSheafedSpace ⟶ X.toSheafedSpace :=
  (ρ k).hom.toLRSHom.toShHom

lemma ιSh_fSh (k : G) : ιSh ρ k ≫ fSh ρ = aSh ρ k := by
  change ((copι ρ k) ≫ actMap ρ).toLRSHom.toShHom = _
  rw [ι_actMap]

lemma ιSh_gSh (k : G) : ιSh ρ k ≫ gSh ρ = 𝟙 _ := by
  change ((copι ρ k) ≫ prMap ρ).toLRSHom.toShHom = _
  rw [ι_prMap]; rfl

noncomputable abbrev CP : PresheafedSpace CommRingCat.{u} :=
  coequalizer (Fps.map (fSh ρ)) (Fps.map (gSh ρ))

noncomputable abbrev πP : Fps.obj X.toSheafedSpace ⟶ CP ρ :=
  coequalizer.π (Fps.map (fSh ρ)) (Fps.map (gSh ρ))

noncomputable abbrev eP : CP ρ ≅ Fps.obj (coequalizer (fSh ρ) (gSh ρ)) :=
  PreservesCoequalizer.iso Fps (fSh ρ) (gSh ρ)

lemma πP_eP : πP ρ ≫ (eP ρ).hom = (πL ρ).toHom := by
  dsimp only [πP, eP]
  rw [PreservesCoequalizer.iso_hom, ι_comp_coequalizerComparison]
  rfl

noncomputable abbrev preP (W : Opens (CP ρ).carrier) : X.Opens :=
  (Opens.map (πP ρ).base).obj W

lemma act_comp_πP (k : G) : Fps.map (aSh ρ k) ≫ πP ρ = πP ρ := by
  have hc := coequalizer.condition (Fps.map (fSh ρ)) (Fps.map (gSh ρ))
  rw [← ιSh_fSh, CategoryTheory.Functor.map_comp, Category.assoc, hc, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    ιSh_gSh, CategoryTheory.Functor.map_id, Category.id_comp]

lemma preP_le (W : Opens (CP ρ).carrier) (k : G) : preP ρ W ≤ (ρ k).hom ⁻¹ᵁ preP ρ W := by
  intro x hx
  have := congrArg (fun φ => φ.base x) (act_comp_πP ρ k)
  simp only [PresheafedSpace.comp_base, TopCat.comp_app] at this
  change (πP ρ).base ((ρ k).hom.base x) ∈ W
  erw [this]
  exact hx

noncomputable abbrev KW (W : Opens (CP ρ).carrier) : WalkingParallelPairᵒᵖ ⥤ CommRingCat.{u} :=
  PresheafedSpace.componentwiseDiagram (parallelPair (Fps.map (fSh ρ)) (Fps.map (gSh ρ))) W

noncomputable abbrev cIso (W : Opens (CP ρ).carrier) :
    (CP ρ).presheaf.obj (op W) ≅ limit (KW ρ W) :=
  PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit
    (parallelPair (Fps.map (fSh ρ)) (Fps.map (gSh ρ))) W

lemma πP_c_app (W : Opens (CP ρ).carrier) :
    (πP ρ).c.app (op W) = (cIso ρ W).hom ≫ limit.π (KW ρ W) (op WalkingParallelPair.one) :=
  (PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit_hom_π _ _ _).symm

lemma πP_app_injective (W : Opens (CP ρ).carrier) :
    Function.Injective ((πP ρ).c.app (op W)) := by
  rw [πP_c_app]
  intro a b h
  exact (ConcreteCategory.bijective_of_isIso (cIso ρ W).hom).injective (limitπ_one_injective _ h)

lemma range_πP_app (W : Opens (CP ρ).carrier) :
    Set.range ((πP ρ).c.app (op W)) = {s | (KW ρ W).map lop s = (KW ρ W).map rop s} := by
  rw [πP_c_app, ← range_limitπ_one]
  ext s
  simp only [Set.mem_range]
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨_, rfl⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (cIso ρ W).hom).surjective b
    exact ⟨a, rfl⟩

noncomputable abbrev ι₀ : Fps.obj (cop ρ).toSheafedSpace ⟶ CP ρ :=
  colimit.ι (parallelPair (Fps.map (fSh ρ)) (Fps.map (gSh ρ))) WalkingParallelPair.zero

noncomputable abbrev preP₀ (W : Opens (CP ρ).carrier) : (cop ρ).Opens :=
  (Opens.map (ι₀ ρ).base).obj W

lemma copι_preimage_preP₀ (W : Opens (CP ρ).carrier) (k : G) :
    copι ρ k ⁻¹ᵁ preP₀ ρ W = preP ρ W := by
  have hw : Fps.map (gSh ρ) ≫ (πP ρ : Fps.obj X.toSheafedSpace ⟶ CP ρ) = ι₀ ρ :=
    colimit.w (parallelPair (Fps.map (fSh ρ)) (Fps.map (gSh ρ))) WalkingParallelPairHom.right
  change (Opens.map (Fps.map (ιSh ρ k) ≫ ι₀ ρ).base).obj W = _
  rw [← hw, ← CategoryTheory.Functor.map_comp_assoc, ιSh_gSh, CategoryTheory.Functor.map_id,
    Category.id_comp]

lemma copι_app_KW_map_lop (W : Opens (CP ρ).carrier) (k : G) (s : Γ(X, preP ρ W)) :
    (copι ρ k).app (preP₀ ρ W) ((KW ρ W).map lop s) =
      (ρ k).hom.appLE (preP ρ W) (copι ρ k ⁻¹ᵁ preP₀ ρ W)
        (by rw [copι_preimage_preP₀]; exact preP_le ρ W k) s := by
  change ((KW ρ W).map lop ≫ (copι ρ k).app (preP₀ ρ W)) s = _
  have : (KW ρ W).map lop ≫ (copι ρ k).app (preP₀ ρ W) =
      (copι ρ k ≫ actMap ρ).appLE (preP ρ W) (copι ρ k ⁻¹ᵁ preP₀ ρ W)
        (by rw [ι_actMap, copι_preimage_preP₀]; exact preP_le ρ W k) := by
    rw [PresheafedSpace.componentwiseDiagram_map]
    change ((actMap ρ).app (preP ρ W) ≫ (cop ρ).presheaf.map (eqToHom _)) ≫
      (copι ρ k).app (preP₀ ρ W) = _
    rw [Category.assoc]
    erw [(copι ρ k).naturality]
    rw [← Category.assoc, ← Scheme.Hom.comp_app, Scheme.Hom.app_eq_appLE]
    erw [Scheme.Hom.appLE_map]
  rw [this, appLE_congr_hom (ι_actMap ρ k)]
  rfl

lemma copι_app_KW_map_rop (W : Opens (CP ρ).carrier) (k : G) (s : Γ(X, preP ρ W)) :
    (copι ρ k).app (preP₀ ρ W) ((KW ρ W).map rop s) =
      X.presheaf.map (homOfLE (by rw [copι_preimage_preP₀])).op s := by
  change ((KW ρ W).map rop ≫ (copι ρ k).app (preP₀ ρ W)) s = _
  have : (KW ρ W).map rop ≫ (copι ρ k).app (preP₀ ρ W) =
      (copι ρ k ≫ prMap ρ).appLE (preP ρ W) (copι ρ k ⁻¹ᵁ preP₀ ρ W)
        (by rw [ι_prMap, copι_preimage_preP₀]; exact le_rfl) := by
    rw [PresheafedSpace.componentwiseDiagram_map]
    change ((prMap ρ).app (preP ρ W) ≫ (cop ρ).presheaf.map (eqToHom _)) ≫
      (copι ρ k).app (preP₀ ρ W) = _
    rw [Category.assoc]
    erw [(copι ρ k).naturality]
    rw [← Category.assoc, ← Scheme.Hom.comp_app, Scheme.Hom.app_eq_appLE]
    erw [Scheme.Hom.appLE_map]
  rw [this, appLE_congr_hom (ι_prMap ρ k), id_appLE]
  rfl

lemma appLE_eq_map_iff_of_eq {f : X ⟶ X} {U V V' : X.Opens} (h : V' = V)
    (e₁ : V' ≤ f ⁻¹ᵁ U) (e₂ : V' ≤ U) (e₁' : V ≤ f ⁻¹ᵁ U) (e₂' : V ≤ U) (s : Γ(X, U)) :
    (f.appLE U V' e₁ s = X.presheaf.map (homOfLE e₂).op s) ↔
      (f.appLE U V e₁' s = X.presheaf.map (homOfLE e₂').op s) := by
  subst h; rfl

lemma map_homOfLE_refl (U : X.Opens) (e : U ≤ U) (s : Γ(X, U)) :
    X.presheaf.map (homOfLE e).op s = s := by
  have : (homOfLE e).op = 𝟙 (op U) := Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id]; rfl

lemma cond_iff (W : Opens (CP ρ).carrier) (s : Γ(X, preP ρ W)) :
    (KW ρ W).map lop s = (KW ρ W).map rop s ↔
      ∀ k : G, (ρ k).hom.appLE (preP ρ W) (preP ρ W) (preP_le ρ W k) s = s := by
  constructor
  · intro h k
    have hk := congrArg ((copι ρ k).app (preP₀ ρ W)) h
    rw [copι_app_KW_map_lop, copι_app_KW_map_rop,
      appLE_eq_map_iff_of_eq (copι_preimage_preP₀ ρ W k) _ _ (preP_le ρ W k) le_rfl,
      map_homOfLE_refl] at hk
    exact hk
  · intro h
    apply Scheme.OpenCover.ext_elem _ _ (sigmaOpenCover (fun _ : G => X))
    intro k
    simp only [sigmaOpenCover_f]
    change (copι ρ k).app (preP₀ ρ W) _ = (copι ρ k).app (preP₀ ρ W) _
    rw [copι_app_KW_map_lop, copι_app_KW_map_rop,
      appLE_eq_map_iff_of_eq (copι_preimage_preP₀ ρ W k) _ _ (preP_le ρ W k) le_rfl,
      map_homOfLE_refl]
    exact h k

noncomputable abbrev preL (V : Opens (QL ρ)) : X.Opens := (Opens.map (πL ρ).base).obj V

lemma preL_le (V : Opens (QL ρ)) (g : G) : preL ρ V ≤ (ρ g).hom ⁻¹ᵁ preL ρ V := by
  intro x hx
  change (πL ρ).base ((ρ g).hom.base x) ∈ V
  rw [act_apply_πL]; exact hx

noncomputable abbrev WV (V : Opens (QL ρ)) : Opens (CP ρ).carrier :=
  (Opens.map (eP ρ).hom.base).obj V

lemma preP_WV (V : Opens (QL ρ)) : preP ρ (WV ρ V) = preL ρ V := by
  change (Opens.map (πP ρ ≫ (eP ρ).hom).base).obj V = _
  rw [πP_eP]
  rfl

lemma πL_c_app (V : Opens (QL ρ)) :
    (πL ρ).c.app (op V) = ((eP ρ).hom.c.app (op V) ≫ (πP ρ).c.app (op (WV ρ V))) ≫
      X.presheaf.map (eqToHom (congrArg op (preP_WV ρ V))) := by
  have hc := PresheafedSpace.congr_app (πP_eP ρ).symm (op V)
  rw [PresheafedSpace.comp_c_app] at hc
  exact hc

scoped instance eP_c_isIso : IsIso (eP ρ).hom.c := PresheafedSpace.c_isIso_of_iso _

scoped instance eP_c_app_isIso (V : Opens (QL ρ)) : IsIso ((eP ρ).hom.c.app (op V)) := by
  exact @NatIso.isIso_app_of_isIso _ _ _ _ _ _ (eP ρ).hom.c (eP_c_isIso ρ)
    (op V : (Opens (Fps.obj (coequalizer (fSh ρ) (gSh ρ))).carrier)ᵒᵖ)

theorem πL_app_injective (V : Opens (QL ρ)) : Function.Injective ((πL ρ).c.app (op V)) := by
  rw [πL_c_app]
  intro a b h
  change X.presheaf.map _ ((πP ρ).c.app _ ((eP ρ).hom.c.app _ a)) =
    X.presheaf.map _ ((πP ρ).c.app _ ((eP ρ).hom.c.app _ b)) at h
  have h1 := (ConcreteCategory.bijective_of_isIso
    (X.presheaf.map (eqToHom (congrArg op (preP_WV ρ V))))).injective h
  have h2 := πP_app_injective ρ _ h1
  exact (ConcreteCategory.bijective_of_isIso ((eP ρ).hom.c.app (op V))).injective h2

omit [Finite G] in
lemma invariant_transport {U₁ U₂ : X.Opens} (h : U₁ = U₂) (h₁ : ∀ g, U₁ ≤ (ρ g).hom ⁻¹ᵁ U₁)
    (h₂ : ∀ g, U₂ ≤ (ρ g).hom ⁻¹ᵁ U₂) (t : Γ(X, U₁)) :
    (∀ g, (ρ g).hom.appLE U₂ U₂ (h₂ g) (X.presheaf.map (eqToHom (congrArg op h)) t) =
        X.presheaf.map (eqToHom (congrArg op h)) t) ↔
      ∀ g, (ρ g).hom.appLE U₁ U₁ (h₁ g) t = t := by
  subst h
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id]
  rfl

theorem range_πL_app (V : Opens (QL ρ)) :
    Set.range ((πL ρ).c.app (op V)) =
      {s | ∀ g : G, (ρ g).hom.appLE (preL ρ V) (preL ρ V) (preL_le ρ V g) s = s} := by
  rw [πL_c_app]
  have hsurj := (ConcreteCategory.bijective_of_isIso ((eP ρ).hom.c.app (op V))).surjective
  ext s
  constructor
  · rintro ⟨a, rfl⟩
    change X.presheaf.map _ ((πP ρ).c.app _ ((eP ρ).hom.c.app _ a)) ∈ _
    have hmem : (πP ρ).c.app _ ((eP ρ).hom.c.app _ a) ∈
        Set.range ((πP ρ).c.app (op (WV ρ V))) := ⟨_, rfl⟩
    rw [range_πP_app] at hmem
    exact (invariant_transport ρ (preP_WV ρ V) (preP_le ρ _) (preL_le ρ V) _).mpr
      ((cond_iff ρ _ _).mp hmem)
  · intro hs
    obtain ⟨t, rfl⟩ : ∃ t : Γ(X, preP ρ (WV ρ V)),
        X.presheaf.map (eqToHom (congrArg op (preP_WV ρ V))) t = s :=
      (ConcreteCategory.bijective_of_isIso
        (X.presheaf.map (eqToHom (congrArg op (preP_WV ρ V))))).surjective s
    have ht := (invariant_transport ρ (preP_WV ρ V) (preP_le ρ _) (preL_le ρ V) t).mp hs
    have ht' : t ∈ Set.range ((πP ρ).c.app (op (WV ρ V))) := by
      rw [range_πP_app]; exact (cond_iff ρ _ _).mpr ht
    obtain ⟨t', rfl⟩ := ht'
    obtain ⟨a, rfl⟩ := hsurj t'
    exact ⟨a, rfl⟩

end Sections

section InvLoc

variable {R S A L : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing L]
  [Algebra R S] [Algebra A L]

theorem isLocalization_away_of_range_eq_fixed
    (ιR : R →+* A) (ιS : S →+* L) (hιR : Function.Injective ιR) (hιS : Function.Injective ιS)
    (hsq : ιS.comp (algebraMap R S) = (algebraMap A L).comp ιR)
    {G : Type*} [Finite G] (σ : G → (A →+* A)) (τ : G → (L →+* L))
    (hστ : ∀ g, (τ g).comp (algebraMap A L) = (algebraMap A L).comp (σ g))
    (hR : Set.range ιR = {a | ∀ g, σ g a = a}) (hS : Set.range ιS = {l | ∀ g, τ g l = l})
    (r : R) [IsLocalization.Away (ιR r) L] :
    IsLocalization.Away r S := by
  classical
  have hsq' : ∀ x : R, ιS (algebraMap R S x) = algebraMap A L (ιR x) :=
    fun x => RingHom.congr_fun hsq x
  have hστ' : ∀ g (a : A), τ g (algebraMap A L a) = algebraMap A L (σ g a) :=
    fun g a => RingHom.congr_fun (hστ g) a
  have hRinv : ∀ (x : R) g, σ g (ιR x) = ιR x := fun x g => by
    have : ιR x ∈ Set.range ιR := ⟨x, rfl⟩
    rw [hR] at this
    exact this g
  have hSinv : ∀ (s : S) g, τ g (ιS s) = ιS s := fun s g => by
    have : ιS s ∈ Set.range ιS := ⟨s, rfl⟩
    rw [hS] at this
    exact this g
  have hτc : ∀ g (n : ℕ), τ g (algebraMap A L (ιR r) ^ n) = algebraMap A L (ιR r) ^ n :=
    fun g n => by rw [← map_pow, hστ', map_pow, hRinv]
  refine (isLocalization_iff (Submonoid.powers r) S).mpr ⟨?_, ?_, ?_⟩
  ·
    rintro ⟨_, n, rfl⟩
    obtain ⟨u, hu⟩ := (IsLocalization.Away.algebraMap_isUnit (S := L) (ιR r)).pow n

    have hinv : ∀ g, τ g (↑u⁻¹ : L) = ↑u⁻¹ := fun g => by
      have h1 : τ g (↑u : L) = ↑u := by rw [hu, hτc]
      have h2 : τ g (↑u : L) * τ g (↑u⁻¹ : L) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      rw [h1] at h2
      calc τ g (↑u⁻¹ : L) = ↑u⁻¹ * (↑u * τ g (↑u⁻¹ : L)) := by
            rw [← mul_assoc, Units.inv_mul, one_mul]
        _ = ↑u⁻¹ := by rw [h2, mul_one]
    have hmem : (↑u⁻¹ : L) ∈ Set.range ιS := by rw [hS]; exact hinv
    obtain ⟨s, hs⟩ := hmem
    refine isUnit_iff_exists_inv.mpr ⟨s, hιS ?_⟩
    rw [map_mul, map_one, hs, map_pow, map_pow, hsq', ← hu, Units.mul_inv]
  ·
    intro s
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers (ιR r)) (ιS s)
    simp only [map_pow] at ha

    have hg : ∀ g, ∃ m : ℕ, ιR r ^ m * σ g a = ιR r ^ m * a := fun g => by
      have : algebraMap A L (σ g a) = algebraMap A L a := by
        rw [← hστ', ← ha, map_mul, hSinv, hτc]
      obtain ⟨⟨_, m, rfl⟩, hm⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (ιR r)) this
      exact ⟨m, hm⟩
    choose m hm using hg
    haveI := Fintype.ofFinite G
    let M : ℕ := Finset.univ.sup m
    have hM : ∀ g, ιR r ^ M * σ g a = ιR r ^ M * a := fun g => by
      have hle : m g ≤ M := Finset.le_sup (Finset.mem_univ g)
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      rw [hk, add_comm, pow_add, mul_assoc, hm g, ← mul_assoc]

    have hinv : (ιR r ^ M * a) ∈ Set.range ιR := by
      rw [hR]
      intro g
      show σ g (ιR r ^ M * a) = ιR r ^ M * a
      rw [map_mul, map_pow, hRinv, hM]
    obtain ⟨r', hr'⟩ := hinv
    refine ⟨⟨r', ⟨r ^ (n + M), _, rfl⟩⟩, hιS ?_⟩
    simp only
    rw [map_mul, map_pow, map_pow, hsq', hsq', hr', map_mul, map_pow, pow_add, ← mul_assoc, ha]
    ring
  ·
    intro x y hxy
    have : algebraMap A L (ιR x) = algebraMap A L (ιR y) := by
      rw [← hsq', ← hsq', hxy]
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (ιR r)) this
    refine ⟨⟨r ^ k, k, rfl⟩, hιR ?_⟩
    simpa only [map_mul, map_pow] using hk

end InvLoc

section InvariantAlgebra

variable {A : Type*} [CommRing A] {G : Type*} [Group G]
  (act : G → (A →+* A)) (act_one : act 1 = RingHom.id A)
  (act_mul : ∀ g h, act (g * h) = (act h).comp (act g))

def invSubring : Subring A where
  carrier := {a | ∀ g, act g a = a}
  mul_mem' ha hb g := by rw [map_mul, ha g, hb g]
  one_mem' g := map_one _
  add_mem' ha hb g := by rw [map_add, ha g, hb g]
  zero_mem' g := map_zero _
  neg_mem' ha g := by rw [map_neg, ha g]

lemma mem_invSubring {a : A} : a ∈ invSubring act ↔ ∀ g, act g a = a := Iff.rfl

include act_one act_mul in

@[reducible] def toAction : MulSemiringAction G A where
  smul g a := act g⁻¹ a
  one_smul a := by show act 1⁻¹ a = a; rw [inv_one, act_one]; rfl
  mul_smul g h a := by show act (g * h)⁻¹ a = act g⁻¹ (act h⁻¹ a); rw [mul_inv_rev, act_mul]; rfl
  smul_zero g := map_zero _
  smul_add g a b := map_add _ _ _
  smul_one g := map_one _
  smul_mul g a b := map_mul _ _ _

include act_one act_mul in
lemma invSubring_eq_fixedPoints :
    letI := toAction act act_one act_mul
    invSubring act = FixedPoints.subring A G := by
  letI := toAction act act_one act_mul
  ext a
  rw [mem_invSubring]
  change _ ↔ a ∈ MulAction.fixedPoints G A
  rw [MulAction.mem_fixedPoints]
  constructor
  · intro h g; exact h g⁻¹
  · intro h g
    have := h g⁻¹
    change act g⁻¹⁻¹ a = a at this
    rwa [inv_inv] at this

include act_one act_mul in

theorem exists_comap_act_eq [Finite G] (P Q : Ideal A) [P.IsPrime] [Q.IsPrime]
    (h : P.comap (invSubring act).subtype = Q.comap (invSubring act).subtype) :
    ∃ g : G, Q = P.comap (act g) := by
  letI := toAction act act_one act_mul
  have hB : invSubring act = FixedPoints.subring A G := invSubring_eq_fixedPoints act act_one act_mul
  let B := FixedPoints.subring A G
  haveI : SMulCommClass G B A :=
    ⟨fun g b a => by
      show g • ((b : A) * a) = (b : A) * (g • a)
      rw [smul_mul', show g • (b : A) = b from b.2 g]⟩
  haveI : Algebra.IsInvariant B A G := ⟨fun a ha => ⟨⟨a, ha⟩, rfl⟩⟩
  have h' : P.under B = Q.under B := by
    ext ⟨b, hb⟩
    have hb' : b ∈ invSubring act := hB ▸ hb
    have := congrArg (fun I : Ideal (invSubring act) => (⟨b, hb'⟩ : invSubring act) ∈ I) h
    simp [Ideal.under, Ideal.mem_comap] at this
    exact this
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq B A G P Q h'
  refine ⟨g, ?_⟩
  rw [hg, Ideal.pointwise_smul_def]
  have : MulSemiringAction.toRingHom G A g = (MulSemiringAction.toRingEquiv G A g : A →+* A) := rfl
  rw [this, Ideal.map_comap_of_equiv]
  ext a
  simp only [Ideal.mem_comap]
  change act g⁻¹⁻¹ a ∈ P ↔ act g a ∈ P
  rw [inv_inv]

include act_one act_mul in

theorem algebra_isIntegral_invSubring [Finite G] : Algebra.IsIntegral (invSubring act) A := by
  letI := toAction act act_one act_mul
  have hB : invSubring act = FixedPoints.subring A G := invSubring_eq_fixedPoints act act_one act_mul
  haveI : Algebra.IsInvariant (FixedPoints.subring A G) A G := ⟨fun a ha => ⟨⟨a, ha⟩, rfl⟩⟩
  have := Algebra.IsInvariant.isIntegral (FixedPoints.subring A G) A G
  rw [hB]
  exact this

include act_one act_mul in
theorem isIntegral_subtype [Finite G] : (invSubring act).subtype.IsIntegral := by
  have := algebra_isIntegral_invSubring act act_one act_mul
  intro a
  exact this.isIntegral a

include act_one act_mul in

theorem exists_prime_comap_eq [Finite G] (q : Ideal (invSubring act)) [q.IsPrime] :
    ∃ P : Ideal A, P.IsPrime ∧ P.comap (invSubring act).subtype = q := by
  haveI := algebra_isIntegral_invSubring act act_one act_mul
  obtain ⟨P, -, hP, hPq⟩ := Ideal.exists_ideal_over_prime_of_isIntegral q (⊥ : Ideal A)
    (by rw [Ideal.comap_bot_of_injective _ Subtype.val_injective]; exact bot_le)
  exact ⟨P, hP, hPq⟩

include act_one act_mul in
theorem isClosedMap_comap_subtype [Finite G] :
    IsClosedMap (PrimeSpectrum.comap (invSubring act).subtype) :=
  PrimeSpectrum.isClosedMap_comap_of_isIntegral _ (isIntegral_subtype act act_one act_mul)

end InvariantAlgebra

section SchemeHelpers2

variable {X Y : Scheme.{u}}

lemma appLE_congr_hom' {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h; rfl

lemma mem_primeIdealOf_iff {U : X.Opens} (hU : IsAffineOpen U) (x : U) (a : Γ(X, U)) :
    a ∈ (hU.primeIdealOf x).asIdeal ↔ x.1 ∉ X.basicOpen a := by
  rw [hU.primeIdealOf_eq_map_closedPoint, Scheme.mem_basicOpen X a x.1 x.2]
  change a ∈ Ideal.comap _ (IsLocalRing.maximalIdeal _) ↔ _
  rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

lemma primeIdealOf_injective {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Injective hU.primeIdealOf := by
  intro x y h
  exact (Scheme.homeoOfIso hU.isoSpec).injective (by simp [Scheme.homeoOfIso_apply] at h ⊢; exact h)

lemma primeIdealOf_fromSpec {U : X.Opens} (hU : IsAffineOpen U) (p : Spec Γ(X, U))
    (hp : hU.fromSpec p ∈ U) : hU.primeIdealOf ⟨hU.fromSpec p, hp⟩ = p := by
  have h1 : (⟨hU.fromSpec p, hp⟩ : U) = hU.isoSpec.inv p := rfl
  rw [IsAffineOpen.primeIdealOf, h1, ← Scheme.Hom.comp_apply, Iso.inv_hom_id]
  rfl

lemma isClosedMap_primeIdealOf {U : X.Opens} (hU : IsAffineOpen U) :
    IsClosedMap hU.primeIdealOf := by
  have : (hU.primeIdealOf : U → _) = Scheme.homeoOfIso hU.isoSpec := by
    ext1 x; rw [Scheme.homeoOfIso_apply]; rfl
  rw [this]
  exact (Scheme.homeoOfIso hU.isoSpec).isClosedMap

end SchemeHelpers2

section Chart

variable {X : Scheme.{u}} {G : Type v} [Group G] [Finite G] (ρ : G →* Aut X)
  {Y : LocallyRingedSpace.{u}} (π : X.toLocallyRingedSpace ⟶ Y)

abbrev pre (V : Opens Y) : X.Opens := (Opens.map π.base).obj V

variable {ρ π} in
lemma pre_le_of_comm (comm : ∀ g, (ρ g).hom.toLRSHom ≫ π = π) (V : Opens Y) (g : G) :
    pre π V ≤ (ρ g).hom ⁻¹ᵁ pre π V := by
  intro x hx
  change π.base ((ρ g).hom.base x) ∈ V
  have := congrArg (fun φ => φ.base x) (comm g)
  simp only [LocallyRingedSpace.comp_base, TopCat.comp_app] at this
  erw [this]
  exact hx

structure IsRingedQuot : Prop where
  comm : ∀ g, (ρ g).hom.toLRSHom ≫ π = π
  surj : Function.Surjective π.base
  isOpen : ∀ s : Set Y, IsOpen (π.base ⁻¹' s) → IsOpen s
  fib : ∀ x x' : X, π.base x = π.base x' → ∃ g : G, (ρ g).hom.base x = x'
  inj : ∀ V : Opens Y, Function.Injective (π.c.app (op V))
  range : ∀ V : Opens Y, Set.range (π.c.app (op V)) =
    {s | ∀ g, (ρ g).hom.appLE (pre π V) (pre π V) (pre_le_of_comm comm V g) s = s}

variable {ρ π} (H : IsRingedQuot ρ π)
include H

lemma IsRingedQuot.apply_act (g : G) (x : X) : π.base ((ρ g).hom.base x) = π.base x := by
  have := congrArg (fun φ => φ.base x) (H.comm g)
  simp only [LocallyRingedSpace.comp_base, TopCat.comp_app] at this
  exact this

lemma IsRingedQuot.pre_act (g : G) (V : Opens Y) : (ρ g).hom ⁻¹ᵁ pre π V = pre π V := by
  ext x
  change π.base ((ρ g).hom.base x) ∈ V ↔ π.base x ∈ V
  rw [H.apply_act]

noncomputable def IsRingedQuot.act (V : Opens Y) (g : G) : Γ(X, pre π V) →+* Γ(X, pre π V) :=
  ((ρ g).hom.appLE (pre π V) (pre π V) (pre_le_of_comm H.comm V g)).hom

lemma IsRingedQuot.act_one (V : Opens Y) : H.act V 1 = RingHom.id _ := by
  have h1 : (ρ 1).hom = 𝟙 X := by rw [map_one]; rfl
  rw [IsRingedQuot.act, appLE_congr_hom' h1]
  rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
  erw [Category.id_comp]
  have : ∀ (i : op ((𝟙 X) ⁻¹ᵁ pre π V) ⟶ op (pre π V)), X.presheaf.map i = 𝟙 _ := fun i => by
    rw [show i = 𝟙 _ from Subsingleton.elim _ _]; exact X.presheaf.map_id _
  rw [this]
  rfl

lemma IsRingedQuot.act_mul (V : Opens Y) (g h : G) :
    H.act V (g * h) = (H.act V h).comp (H.act V g) := by
  have h1 : (ρ (g * h)).hom = (ρ h).hom ≫ (ρ g).hom := by rw [map_mul, Aut.Aut_mul_def]; rfl
  rw [IsRingedQuot.act, appLE_congr_hom' h1, ← Scheme.Hom.appLE_comp_appLE _ _ _ (pre π V)]
  rfl

lemma IsRingedQuot.mem_invSubring_iff (V : Opens Y) (s : Γ(X, pre π V)) :
    s ∈ invSubring (H.act V) ↔ s ∈ Set.range (π.c.app (op V)).hom := by
  rw [H.range V]
  rfl

noncomputable def IsRingedQuot.sectionsEquiv (V : Opens Y) :
    Y.presheaf.obj (op V) ≃+* invSubring (H.act V) :=
  RingEquiv.ofBijective
    ((π.c.app (op V)).hom.codRestrict _ fun r => (H.mem_invSubring_iff V _).mpr ⟨r, rfl⟩)
    ⟨fun a b h => H.inj V (congrArg Subtype.val h), fun ⟨s, hs⟩ => by
      obtain ⟨r, rfl⟩ := (H.mem_invSubring_iff V s).mp hs
      exact ⟨r, rfl⟩⟩

lemma IsRingedQuot.subtype_comp_sectionsEquiv (V : Opens Y) :
    (invSubring (H.act V)).subtype.comp (H.sectionsEquiv V).toRingHom = (π.c.app (op V)).hom := rfl

theorem IsRingedQuot.isIntegral_app (V : Opens Y) : (π.c.app (op V)).hom.IsIntegral := by
  rw [← H.subtype_comp_sectionsEquiv]
  exact RingHom.IsIntegral.trans _ _
    (RingHom.isIntegral_of_surjective _ (H.sectionsEquiv V).surjective)
    (isIntegral_subtype _ (H.act_one V) (H.act_mul V))

end Chart

section ChartDefs

variable {X : Scheme.{u}} {Y : LocallyRingedSpace.{u}} (π : X.toLocallyRingedSpace ⟶ Y) (V : Opens Y)

noncomputable abbrev Zr : LocallyRingedSpace.{u} := Y.restrict V.isOpenEmbedding

noncomputable abbrev V₀ : Opens Y := V.isOpenEmbedding.functor.obj ⊤

lemma V₀_eq : V₀ V = V := Opens.isOpenEmbedding_obj_top V

lemma mem_V₀_iff (y : Y) : y ∈ V₀ V ↔ y ∈ V := by rw [V₀_eq]

lemma isAffineOpen_pre_V₀ (hV : IsAffineOpen (pre π V)) : IsAffineOpen (pre π (V₀ V)) := by
  have : pre π (V₀ V) = pre π V := by rw [V₀_eq]
  rw [this]; exact hV

noncomputable def zOf (u : pre π (V₀ V)) : Zr V :=
  ⟨π.base u.1, (mem_V₀_iff V _).mp u.2⟩

lemma zOf_val (u : pre π (V₀ V)) : (zOf π V u).1 = π.base u.1 := rfl

lemma continuous_zOf : Continuous (zOf π V) :=
  Continuous.subtype_mk (π.base.hom.continuous.comp continuous_subtype_val) _

noncomputable abbrev θ₀ : Y.presheaf.obj (op (V₀ V)) →+* Γ(X, pre π (V₀ V)) :=
  (π.c.app (op (V₀ V))).hom

lemma isUnit_Γgerm_iff (z : Zr V) (r : Y.presheaf.obj (op (V₀ V))) :
    IsUnit ((Zr V).presheaf.Γgerm z r) ↔
      IsUnit (Y.presheaf.germ (V₀ V) z.1 ((mem_V₀_iff V _).mpr z.2) r) := by
  have e := Y.restrictStalkIso_hom_eq_germ_apply V.isOpenEmbedding ⊤ z trivial r
  constructor
  · intro hu
    have := hu.map (Y.restrictStalkIso V.isOpenEmbedding z).hom.hom
    rw [TopCat.Presheaf.Γgerm] at this
    erw [e] at this
    exact this
  · intro hu
    have h2 : (Y.restrictStalkIso V.isOpenEmbedding z).inv.hom
        (Y.presheaf.germ (V₀ V) z.1 ((mem_V₀_iff V _).mpr z.2) r) =
        (Zr V).presheaf.Γgerm z r := by
      erw [← e]
      exact CategoryTheory.Iso.hom_inv_id_apply _ _
    have := hu.map (Y.restrictStalkIso V.isOpenEmbedding z).inv.hom
    exact (congrArg IsUnit h2).mp this

lemma functor_obj_basicOpen (r : Y.presheaf.obj (op (V₀ V))) :
    V.isOpenEmbedding.functor.obj ((Zr V).toRingedSpace.basicOpen
      (show (Zr V).presheaf.obj (op ⊤) from r)) = Y.toRingedSpace.basicOpen r := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' := ((Zr V).toRingedSpace.mem_top_basicOpen _ z).mp hz
    exact (RingedSpace.mem_basicOpen Y.toRingedSpace r _ _).mpr ((isUnit_Γgerm_iff V z r).mp hz')
  · intro hy
    have hyV : y ∈ V := (mem_V₀_iff V y).mp (Y.toRingedSpace.basicOpen_le r hy)
    refine ⟨⟨y, hyV⟩, ?_, rfl⟩
    have := (RingedSpace.mem_basicOpen Y.toRingedSpace r y (Y.toRingedSpace.basicOpen_le r hy)).mp hy
    exact ((Zr V).toRingedSpace.mem_top_basicOpen _ _).mpr ((isUnit_Γgerm_iff V ⟨y, hyV⟩ r).mpr this)

omit V in

lemma isLocalization_away_congr {V' W₁ W₂ : Opens Y} (e : W₁ = W₂) (i₁ : W₁ ⟶ V') (i₂ : W₂ ⟶ V')
    (r : Y.presheaf.obj (op V')) :
    @IsLocalization.Away _ _ r (Y.presheaf.obj (op W₁)) _ (Y.presheaf.map i₁.op).hom.toAlgebra ↔
      @IsLocalization.Away _ _ r (Y.presheaf.obj (op W₂)) _ (Y.presheaf.map i₂.op).hom.toAlgebra := by
  subst e
  obtain rfl : i₁ = i₂ := Subsingleton.elim _ _
  exact Iff.rfl

lemma isUnit_Γgerm_zOf_iff (u : pre π (V₀ V)) (r : Y.presheaf.obj (op (V₀ V))) :
    IsUnit ((Zr V).presheaf.Γgerm (zOf π V u) r) ↔ u.1 ∈ X.basicOpen (θ₀ π V r) := by
  have e := Y.restrictStalkIso_hom_eq_germ_apply V.isOpenEmbedding ⊤ (zOf π V u) trivial r
  have h1 : IsUnit ((Zr V).presheaf.Γgerm (zOf π V u) r) ↔
      IsUnit (Y.presheaf.germ (V₀ V) (π.base u.1) u.2 r) := by
    constructor
    · intro hu
      have := hu.map (Y.restrictStalkIso V.isOpenEmbedding (zOf π V u)).hom.hom
      rw [TopCat.Presheaf.Γgerm] at this
      erw [e] at this
      exact this
    · intro hu
      have h2 : (Y.restrictStalkIso V.isOpenEmbedding (zOf π V u)).inv.hom
          (Y.presheaf.germ (V₀ V) (π.base u.1) u.2 r) =
          (Zr V).presheaf.Γgerm (zOf π V u) r := by
        erw [← e]
        exact CategoryTheory.Iso.hom_inv_id_apply _ _
      have := hu.map (Y.restrictStalkIso V.isOpenEmbedding (zOf π V u)).inv.hom
      exact (congrArg IsUnit h2).mp this
  refine h1.trans ((RingedSpace.mem_basicOpen Y.toRingedSpace r (π.base u.1) u.2).symm.trans ?_)
  change u.1 ∈ (Opens.map π.base).obj (Y.toRingedSpace.basicOpen r) ↔ _
  rw [LocallyRingedSpace.preimage_basicOpen]
  rfl

lemma toΓSpecFun_zOf (hV : IsAffineOpen (pre π V)) (u : pre π (V₀ V)) :
    (Zr V).toΓSpecFun (zOf π V u) =
      PrimeSpectrum.comap (θ₀ π V) ((isAffineOpen_pre_V₀ π V hV).primeIdealOf u) := by
  ext r
  change r ∈ ((Zr V).toΓSpecFun (zOf π V u)).asIdeal ↔
    θ₀ π V r ∈ ((isAffineOpen_pre_V₀ π V hV).primeIdealOf u).asIdeal
  rw [mem_primeIdealOf_iff, ← isUnit_Γgerm_zOf_iff π V u r, ← not_iff_not, not_not]
  exact LocallyRingedSpace.notMem_prime_iff_unit_in_stalk _ r _

end ChartDefs

section Chart2

variable {X : Scheme.{u}} {G : Type v} [Group G] [Finite G] {ρ : G →* Aut X}
  {Y : LocallyRingedSpace.{u}} {π : X.toLocallyRingedSpace ⟶ Y} (H : IsRingedQuot ρ π)
  (V : Opens Y) (hV : IsAffineOpen (pre π V))

include H

omit hV in
lemma IsRingedQuot.zOf_surjective : Function.Surjective (zOf π V) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := H.surj y
  exact ⟨⟨x, (mem_V₀_iff V _).mpr hy⟩, rfl⟩

include hV

lemma IsRingedQuot.hV₀ : IsAffineOpen (pre π (V₀ V)) := isAffineOpen_pre_V₀ π V hV

omit hV in
lemma IsRingedQuot.θ₀_eq :
    θ₀ π V = (invSubring (H.act (V₀ V))).subtype.comp (H.sectionsEquiv (V₀ V)).toRingHom := rfl

omit hV in
lemma IsRingedQuot.comap_θ₀ (p : PrimeSpectrum Γ(X, pre π (V₀ V))) :
    PrimeSpectrum.comap (θ₀ π V) p = PrimeSpectrum.comap (H.sectionsEquiv (V₀ V)).toRingHom
      (PrimeSpectrum.comap (invSubring (H.act (V₀ V))).subtype p) := by
  rw [H.θ₀_eq, PrimeSpectrum.comap_comp_apply]

theorem IsRingedQuot.toΓSpecFun_surjective : Function.Surjective (Zr V).toΓSpecFun := by
  intro q
  let e := H.sectionsEquiv (V₀ V)
  let q' := PrimeSpectrum.comap e.symm.toRingHom q
  obtain ⟨P, hP, hPq⟩ := exists_prime_comap_eq (H.act (V₀ V)) (H.act_one _) (H.act_mul _)
    q'.asIdeal
  let p : PrimeSpectrum Γ(X, pre π (V₀ V)) := ⟨P, hP⟩
  have hu : ((H.hV₀ V hV).fromSpec).base p ∈ pre π (V₀ V) := by
    have := Set.mem_range_self (f := ((H.hV₀ V hV).fromSpec).base) p
    rwa [(H.hV₀ V hV).range_fromSpec] at this
  refine ⟨zOf π V ⟨_, hu⟩, ?_⟩
  rw [toΓSpecFun_zOf π V hV, primeIdealOf_fromSpec, H.comap_θ₀]
  have hp : PrimeSpectrum.comap (invSubring (H.act (V₀ V))).subtype p = q' :=
    PrimeSpectrum.ext hPq
  rw [hp, ← PrimeSpectrum.comap_comp_apply, RingEquiv.symm_toRingHom_comp_toRingHom,
    PrimeSpectrum.comap_id]

theorem IsRingedQuot.toΓSpecFun_injective : Function.Injective (Zr V).toΓSpecFun := by
  intro z₁ z₂ h
  obtain ⟨u₁, rfl⟩ := H.zOf_surjective V z₁
  obtain ⟨u₂, rfl⟩ := H.zOf_surjective V z₂
  rw [toΓSpecFun_zOf π V hV, toΓSpecFun_zOf π V hV, H.comap_θ₀, H.comap_θ₀] at h
  have h' := PrimeSpectrum.comap_injective_of_surjective _
    (H.sectionsEquiv (V₀ V)).surjective h
  have h'' : ((H.hV₀ V hV).primeIdealOf u₁).asIdeal.comap (invSubring (H.act (V₀ V))).subtype =
      ((H.hV₀ V hV).primeIdealOf u₂).asIdeal.comap (invSubring (H.act (V₀ V))).subtype := by
    have := congrArg PrimeSpectrum.asIdeal h'
    simpa only [PrimeSpectrum.comap_asIdeal] using this
  obtain ⟨g, hg⟩ := exists_comap_act_eq (H.act (V₀ V)) (H.act_one _) (H.act_mul _) _ _ h''
  have key := IsAffineOpen.comap_primeIdealOf_appLE (f := (ρ g).hom) (pre π (V₀ V)) (H.hV₀ V hV)
    (pre π (V₀ V)) (H.hV₀ V hV) (pre_le_of_comm H.comm _ g) u₁.2
  have hu₂ : (H.hV₀ V hV).primeIdealOf u₂ =
      (H.hV₀ V hV).primeIdealOf ⟨(ρ g).hom.base u₁.1, pre_le_of_comm H.comm _ g u₁.2⟩ := by
    rw [← key]
    ext1
    exact hg
  have hu := congrArg Subtype.val (primeIdealOf_injective _ hu₂)
  apply Subtype.ext
  simp only [zOf_val]
  rw [hu, H.apply_act]

theorem IsRingedQuot.isClosedMap_toΓSpecFun : IsClosedMap (Zr V).toΓSpecFun := by
  intro C hC
  have hS : IsClosed (zOf π V ⁻¹' C) := hC.preimage (continuous_zOf π V)
  have himg : (Zr V).toΓSpecFun '' C =
      (PrimeSpectrum.comap (θ₀ π V) ∘ (H.hV₀ V hV).primeIdealOf) '' (zOf π V ⁻¹' C) := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨u, rfl⟩ := H.zOf_surjective V z
      exact ⟨u, hz, (toΓSpecFun_zOf π V hV u).symm⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨zOf π V u, hu, toΓSpecFun_zOf π V hV u⟩
  have hθ : PrimeSpectrum.comap (θ₀ π V) =
      PrimeSpectrum.comap (H.sectionsEquiv (V₀ V)).toRingHom ∘
        PrimeSpectrum.comap (invSubring (H.act (V₀ V))).subtype := by
    rw [H.θ₀_eq]; exact PrimeSpectrum.comap_comp _ _
  rw [himg, Set.image_comp, hθ, Set.image_comp]
  refine (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _
    (H.sectionsEquiv (V₀ V)).surjective).isClosedMap _ ?_
  refine isClosedMap_comap_subtype _ (H.act_one _) (H.act_mul _) _ ?_
  exact isClosedMap_primeIdealOf _ _ hS

theorem IsRingedQuot.isHomeomorph_toΓSpecFun : IsHomeomorph (Zr V).toΓSpecFun :=
  isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap (Zr V).toΓSpec_continuous
      (H.toΓSpecFun_injective V hV) (H.isClosedMap_toΓSpecFun V hV)).isEmbedding,
      H.toΓSpecFun_surjective V hV⟩

theorem IsRingedQuot.isIso_toΓSpec_base : IsIso (Zr V).toΓSpec.base := by
  have e : (Zr V).toΓSpec.base =
      (TopCat.isoOfHomeo ((H.isHomeomorph_toΓSpecFun V hV).homeomorph _)).hom := by
    ext x; rfl
  rw [e]; infer_instance

theorem IsRingedQuot.isLocalization_basicOpen (r : Y.presheaf.obj (op (V₀ V))) :
    @IsLocalization.Away _ _ r (Y.presheaf.obj (op (Y.toRingedSpace.basicOpen r))) _
      (Y.presheaf.map (homOfLE (Y.toRingedSpace.basicOpen_le r)).op).hom.toAlgebra := by
  set Wb : Opens Y := Y.toRingedSpace.basicOpen r
  have hWb : Wb ≤ V₀ V := Y.toRingedSpace.basicOpen_le r
  letI : Algebra (Y.presheaf.obj (op (V₀ V))) (Y.presheaf.obj (op Wb)) :=
    (Y.presheaf.map (homOfLE hWb).op).hom.toAlgebra
  have hpre : pre π Wb ≤ pre π (V₀ V) := fun x hx => hWb hx
  letI : Algebra Γ(X, pre π (V₀ V)) Γ(X, pre π Wb) := (X.presheaf.map (homOfLE hpre).op).hom.toAlgebra
  haveI : IsLocalization.Away (θ₀ π V r) Γ(X, pre π Wb) :=
    (H.hV₀ V hV).isLocalization_of_eq_basicOpen _ (homOfLE hpre)
      (LocallyRingedSpace.preimage_basicOpen π r)
  refine isLocalization_away_of_range_eq_fixed (A := Γ(X, pre π (V₀ V))) (L := Γ(X, pre π Wb))
    (θ₀ π V) (π.c.app (op Wb)).hom (H.inj _) (H.inj _)
    ?_ (H.act (V₀ V)) (H.act Wb) ?_ (H.range _) (H.range _) r
  · refine RingHom.ext fun x => ?_
    have h' := ConcreteCategory.congr_hom (π.c.naturality (homOfLE hWb).op) x
    have hj : X.presheaf.map ((Opens.map π.base).map (homOfLE hWb)).op =
        X.presheaf.map (homOfLE hpre).op := by
      congr 1
    change (π.c.app (op Wb)).hom (Y.presheaf.map (homOfLE hWb).op x) =
      X.presheaf.map (homOfLE hpre).op ((π.c.app (op (V₀ V))).hom x)
    rw [← hj]
    exact h'
  · intro g
    change ((ρ g).hom.appLE (pre π Wb) (pre π Wb) _).hom.comp (X.presheaf.map (homOfLE hpre).op).hom =
      (X.presheaf.map (homOfLE hpre).op).hom.comp ((ρ g).hom.appLE _ _ _).hom
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem IsRingedQuot.isLocalization_toΓSpecMapBasicOpen (r : LocallyRingedSpace.Γ.obj (op (Zr V))) :
    @IsLocalization.Away _ _ r ((Zr V).presheaf.obj (op ((Zr V).toΓSpecMapBasicOpen r))) _
      ((Zr V).toToΓSpecMapBasicOpen r).hom.toAlgebra := by
  have e : V.isOpenEmbedding.functor.obj ((Zr V).toΓSpecMapBasicOpen r) =
      Y.toRingedSpace.basicOpen (show Y.presheaf.obj (op (V₀ V)) from r) := by
    rw [LocallyRingedSpace.toΓSpecMapBasicOpen_eq]
    exact functor_obj_basicOpen V r
  have := isLocalization_away_congr (Y := Y) e
    (V.isOpenEmbedding.functor.map ((Zr V).toΓSpecMapBasicOpen r).leTop)
    (homOfLE (Y.toRingedSpace.basicOpen_le _)) r
  exact this.mpr (H.isLocalization_basicOpen V hV r)

theorem IsRingedQuot.isIso_toΓSpecCApp (r : LocallyRingedSpace.Γ.obj (op (Zr V))) :
    IsIso ((Zr V).toΓSpecCApp r) := by
  letI : Algebra (LocallyRingedSpace.Γ.obj (op (Zr V)))
      ((Zr V).presheaf.obj (op ((Zr V).toΓSpecMapBasicOpen r))) :=
    ((Zr V).toToΓSpecMapBasicOpen r).hom.toAlgebra
  have inst := H.isLocalization_toΓSpecMapBasicOpen V hV r
  let e := @IsLocalization.algEquiv _ _ (Submonoid.powers r)
    ((Spec.structureSheaf (LocallyRingedSpace.Γ.obj (op (Zr V)))).obj.obj
      (op (PrimeSpectrum.basicOpen r))) _ _ (StructureSheaf.IsLocalization.to_basicOpen _ r)
    ((Zr V).presheaf.obj (op ((Zr V).toΓSpecMapBasicOpen r))) _ _ inst
  have heq : (Zr V).toΓSpecCApp r = CommRingCat.ofHom e.toRingEquiv.toRingHom := by
    symm
    apply ((Zr V).toΓSpecCApp_iff r _).mp
    ext x
    change e (algebraMap _ _ x) = _
    rw [e.commutes]
    rfl
  rw [heq]
  exact (e.toRingEquiv.toCommRingCatIso).isIso_hom

theorem IsRingedQuot.isIso_toΓSpec_c : IsIso (Zr V).toΓSpec.c := by
  change IsIso (Zr V).toΓSpecSheafedSpace.hom.c
  haveI : ∀ r, IsIso ((Zr V).toΓSpecCBasicOpens.app r) := fun r => by
    rw [LocallyRingedSpace.toΓSpecCBasicOpens_app]; exact H.isIso_toΓSpecCApp V hV r.unop
  have hiso : IsIso (Zr V).toΓSpecCBasicOpens := NatIso.isIso_of_isIso_app _
  let F := Spec.structureSheaf (LocallyRingedSpace.Γ.obj (op (Zr V)))
  let P := (TopCat.Sheaf.pushforward _ (Zr V).toΓSpecBase).obj (Zr V).𝒪
  let γ := @CategoryTheory.inv _ _ _ _ ((Zr V).toΓSpecCBasicOpens) hiso
  have hγ₁ : (Zr V).toΓSpecCBasicOpens ≫ γ = 𝟙 _ := @IsIso.hom_inv_id _ _ _ _ _ hiso
  have hγ₂ : γ ≫ (Zr V).toΓSpecCBasicOpens = 𝟙 _ := @IsIso.inv_hom_id _ _ _ _ _ hiso
  let β : P.1 ⟶ F.1 := TopCat.Sheaf.restrictHomEquivHom P.1 F PrimeSpectrum.isBasis_basic_opens γ
  refine ⟨β, ?_, ?_⟩
  · refine TopCat.Sheaf.hom_ext _ F PrimeSpectrum.isBasis_basic_opens fun r => ?_
    change (Zr V).toΓSpecSheafedSpace.hom.c.app _ ≫ β.app _ = 𝟙 _
    erw [LocallyRingedSpace.toΓSpecSheafedSpace_app_eq, TopCat.Sheaf.extend_hom_app]
    have := congrArg (fun φ => φ.app (op r)) hγ₁
    exact this
  · refine TopCat.Sheaf.hom_ext _ P PrimeSpectrum.isBasis_basic_opens fun r => ?_
    change β.app _ ≫ (Zr V).toΓSpecSheafedSpace.hom.c.app _ = 𝟙 _
    erw [LocallyRingedSpace.toΓSpecSheafedSpace_app_eq, TopCat.Sheaf.extend_hom_app]
    have := congrArg (fun φ => φ.app (op r)) hγ₂
    exact this

theorem IsRingedQuot.isIso_toΓSpec : IsIso (Zr V).toΓSpec := by
  haveI h1 : IsIso (Zr V).toΓSpecSheafedSpace.hom := by
    haveI : IsIso (Zr V).toΓSpecSheafedSpace.hom.base := H.isIso_toΓSpec_base V hV
    haveI : IsIso (Zr V).toΓSpecSheafedSpace.hom.c := H.isIso_toΓSpec_c V hV
    exact PresheafedSpace.isIso_of_components _
  haveI h2 : IsIso (Zr V).toΓSpecSheafedSpace :=
    @isIso_of_reflects_iso _ _ _ _ _ _ _ SheafedSpace.forgetToPresheafedSpace h1 _
  exact @isIso_of_reflects_iso _ _ _ _ _ _ _ LocallyRingedSpace.forgetToSheafedSpace h2 _

end Chart2

section Assembly

variable {X : Scheme.{u}} {G : Type v} [Group G] [Finite G] (ρ : G →* Aut X)

theorem isRingedQuot_πL : IsRingedQuot ρ (πL ρ) where
  comm := act_comp_πL ρ
  surj := πL_surjective ρ
  isOpen s hs := (isOpen_iff_πL ρ s).mpr hs
  fib x x' h := (πL_eq_iff ρ x x').mp h
  inj := πL_app_injective ρ
  range V := range_πL_app ρ V

lemma preimage_image_eq (U : X.Opens) (hGU : ∀ g : G, (ρ g).hom ⁻¹ᵁ U = U) :
    (πL ρ).base ⁻¹' ((πL ρ).base '' (U : Set X)) = U := by
  ext x
  constructor
  · rintro ⟨u, hu, hux⟩
    obtain ⟨g, rfl⟩ := (πL_eq_iff ρ u x).mp hux
    have : u ∈ (ρ g).hom ⁻¹ᵁ U := by rw [hGU]; exact hu
    exact this
  · intro hx
    exact ⟨x, hx, rfl⟩

noncomputable def imOpen (U : X.Opens) (hGU : ∀ g : G, (ρ g).hom ⁻¹ᵁ U = U) : Opens (QL ρ) :=
  ⟨(πL ρ).base '' (U : Set X),
    (isOpen_iff_πL ρ _).mpr ((congrArg IsOpen (preimage_image_eq ρ U hGU)).mpr U.2)⟩

lemma pre_imOpen (U : X.Opens) (hGU : ∀ g : G, (ρ g).hom ⁻¹ᵁ U = U) :
    pre (πL ρ) (imOpen ρ U hGU) = U :=
  Opens.ext (preimage_image_eq ρ U hGU)

variable (hadm : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ g : G, (ρ g).hom ⁻¹ᵁ U = U)

noncomputable def Q : Scheme.{u} where
  toLocallyRingedSpace := QL ρ
  local_affine y := by
    obtain ⟨x, rfl⟩ := πL_surjective ρ y
    obtain ⟨U, hU, hxU, hGU⟩ := hadm x
    have hV : IsAffineOpen (pre (πL ρ) (imOpen ρ U hGU)) := by rw [pre_imOpen]; exact hU
    have hy : (πL ρ).base x ∈ imOpen ρ U hGU := ⟨x, hxU, rfl⟩
    have hiso := (isRingedQuot_πL ρ).isIso_toΓSpec (imOpen ρ U hGU) hV
    exact ⟨⟨imOpen ρ U hGU, hy⟩, _, ⟨@asIso _ _ _ _ (Zr (imOpen ρ U hGU)).toΓSpec hiso⟩⟩

noncomputable def πQ : X ⟶ Q ρ hadm := ⟨πL ρ⟩

lemma πQ_toLRSHom : (πQ ρ hadm).toLRSHom = πL ρ := rfl

lemma act_comp_πQ (g : G) : (ρ g).hom ≫ πQ ρ hadm = πQ ρ hadm :=
  Scheme.Hom.ext' (act_comp_πL ρ g)

lemma isAffineOpen_imOpen (U : X.Opens) (hU : IsAffineOpen U) (hGU : ∀ g : G, (ρ g).hom ⁻¹ᵁ U = U) :
    IsAffineOpen (X := Q ρ hadm) (imOpen ρ U hGU) := by
  let V : (Q ρ hadm).Opens := imOpen ρ U hGU
  have hV : IsAffineOpen (pre (πL ρ) V) := by
    change IsAffineOpen (pre (πL ρ) (imOpen ρ U hGU)); rw [pre_imOpen]; exact hU
  have hiso := (isRingedQuot_πL ρ).isIso_toΓSpec V hV
  let e := @asIso _ _ _ _ (Zr (Y := QL ρ) V).toΓSpec hiso
  let R := LocallyRingedSpace.Γ.obj (op (Zr (Y := QL ρ) V))
  haveI i1 : LocallyRingedSpace.IsOpenImmersion e.inv := inferInstance
  haveI i2 : LocallyRingedSpace.IsOpenImmersion ((QL ρ).ofRestrict V.isOpenEmbedding) :=
    inferInstance
  let sf : Spec R ⟶ Q ρ hadm := ⟨e.inv ≫ (QL ρ).ofRestrict V.isOpenEmbedding⟩
  haveI : IsOpenImmersion sf := @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ e.inv i1 _ i2
  have hrange : sf.opensRange = V := by
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      exact (e.inv.base p).2
    · intro hy
      refine ⟨e.hom.base ⟨y, hy⟩, ?_⟩
      have := congrArg (fun φ => (φ.base ⟨y, hy⟩ : Zr (Y := QL ρ) V).1) e.hom_inv_id
      exact this
  have := isAffineOpen_opensRange sf
  rwa [hrange] at this

theorem isIntegralHom_πQ : IsIntegralHom (πQ ρ hadm) := by
  classical
  have hadm' := hadm
  choose U hU hxU hGU using hadm'
  let W : X → (Q ρ hadm).affineOpens := fun x => ⟨imOpen ρ (U x) (hGU x),
    isAffineOpen_imOpen ρ hadm (U x) (hU x) (hGU x)⟩
  have hW : ⨆ x, (W x : (Q ρ hadm).Opens) = ⊤ := by
    refine top_le_iff.mp fun y _ => ?_
    obtain ⟨x, rfl⟩ := πL_surjective ρ y
    exact Opens.mem_iSup.mpr ⟨x, x, hxU x, rfl⟩
  refine HasAffineProperty.of_iSup_eq_top (P := @IsIntegralHom) W hW fun x => ⟨?_, ?_⟩
  · change IsAffineOpen ((πQ ρ hadm) ⁻¹ᵁ imOpen ρ (U x) (hGU x))
    have : (πQ ρ hadm) ⁻¹ᵁ imOpen ρ (U x) (hGU x) = U x := pre_imOpen ρ (U x) (hGU x)
    rw [this]; exact hU x
  · change (Scheme.Hom.appTop (πQ ρ hadm ∣_ _)).hom.IsIntegral
    rw [morphismRestrict_appTop]
    erw [CommRingCat.hom_comp]
    refine RingHom.IsIntegral.trans _ _ ((isRingedQuot_πL ρ).isIntegral_app _)
      (RingHom.isIntegral_of_surjective _ (map_eqToHom_op_surjective _))

theorem existsUnique_desc {T : Scheme.{u}} (f : X ⟶ T) (hf : ∀ g : G, (ρ g).hom ≫ f = f) :
    ∃! f' : Q ρ hadm ⟶ T, πQ ρ hadm ≫ f' = f := by
  have w : actMap ρ ≫ f = prMap ρ ≫ f := by
    refine Sigma.hom_ext _ _ fun g => ?_
    change copι ρ g ≫ actMap ρ ≫ f = copι ρ g ≫ prMap ρ ≫ f
    rw [ι_actMap_assoc, ι_prMap_assoc, hf]
  have wL : fL ρ ≫ f.toLRSHom = gL ρ ≫ f.toLRSHom := congrArg Scheme.Hom.toLRSHom w
  let f'L : QL ρ ⟶ T.toLocallyRingedSpace := (coforkIsColimit ρ).desc (Cofork.ofπ f.toLRSHom wL)
  have hfac : πL ρ ≫ f'L = f.toLRSHom := (coforkIsColimit ρ).fac _ WalkingParallelPair.one
  refine ⟨⟨f'L⟩, Scheme.Hom.ext' hfac, fun f'' hf'' => Scheme.Hom.ext' ?_⟩
  refine Cofork.IsColimit.hom_ext (coforkIsColimit ρ) ?_
  rw [cofork_π]
  exact (congrArg Scheme.Hom.toLRSHom hf'').trans hfac.symm

end Assembly

end P2mKcFinQuot
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant.P2mKcFinQuot"

open P2mKcFinQuot in
theorem solution
    {X : Scheme.{u}} {G : Type v} [Group G] [Finite G] (ρ : G →* Aut X)
    (hadm : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ g : G, (ρ g).hom ⁻¹ᵁ U = U) :
    ∃ (Y : Scheme.{u}) (π : X ⟶ Y) (hπ : ∀ g : G, (ρ g).hom ≫ π = π),
      IsIntegralHom π ∧ IsAffineHom π ∧ Function.Surjective π.base ∧
      (∀ x x' : X, π.base x = π.base x' ↔ ∃ g : G, (ρ g).hom.base x = x') ∧
      (∀ V : Y.Opens, Function.Injective (π.app V)) ∧
      (∀ V : Y.Opens, Set.range (π.app V) =
        {s | ∀ g : G, (ρ g).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V)
          (by rw [← Scheme.Hom.comp_preimage, hπ g]) s = s}) ∧
      (∀ U : X.Opens, IsAffineOpen U → (∀ g : G, (ρ g).hom ⁻¹ᵁ U = U) →
        ∃ V : Y.Opens, IsAffineOpen V ∧ π ⁻¹ᵁ V = U) ∧
      (∀ (T : Scheme.{u}) (f : X ⟶ T), (∀ g : G, (ρ g).hom ≫ f = f) →
        ∃! f' : Y ⟶ T, π ≫ f' = f) := by
  haveI := isIntegralHom_πQ ρ hadm
  refine ⟨Q ρ hadm, πQ ρ hadm, act_comp_πQ ρ hadm, this, inferInstance, πL_surjective ρ,
    πL_eq_iff ρ, πL_app_injective ρ, range_πL_app ρ, fun U hU hGU => ?_,
    fun T f hf => existsUnique_desc ρ hadm f hf⟩
  exact ⟨imOpen ρ U hGU, isAffineOpen_imOpen ρ hadm U hU hGU, pre_imOpen ρ U hGU⟩

end S_AlgebraicGeometry_Scheme_exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant (solution)
