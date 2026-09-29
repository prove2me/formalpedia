-- Prove2me | Definitions.Def_AlgebraicCurve_CurveModelTransport
-- name    : AlgebraicCurve_CurveModelTransport
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/4f638446-c9e4-5768-ac93-f1f87465d5dc
-- title:
--   Transport of a curve model along a scheme isomorphism
-- statement:
--   Two things are defined. First, for integral schemes $X,Y$ and an isomorphism $e : X \cong Y$, the induced map on function fields. Since an open immersion carries generic point to generic point, $e.\mathrm{inv}$ sends $\mathrm{genericPoint}\,Y$ to $\mathrm{genericPoint}\,X$ and $e.\mathrm{hom}$ sends $\mathrm{genericPoint}\,X$ to $\mathrm{genericPoint}\,Y$; `functionFieldHomOfIso e` is the specialisation map of $X$'s structure presheaf along that equality followed by the stalk map of $e.\mathrm{inv}$ at $\mathrm{genericPoint}\,Y$, a morphism $X.\mathrm{functionField} \to Y.\mathrm{functionField}$ which is an isomorphism, and `functionFieldIsoOfIso e` is the corresponding ring equivalence $K(X) \simeq K(Y)$. Accompanying compatibilities: the square relating $\mathrm{Spec}$ of this map with the canonical morphisms $\operatorname{Spec} \mathcal O_{X,\eta_X} \to X$ and $\operatorname{Spec}\mathcal O_{Y,\eta_Y} \to Y$ (in two forms, via $e.\mathrm{inv}$ and via $e.\mathrm{hom}$); compatibility with germs at the generic point and with stalk specialisation maps at arbitrary points, hence the identity $\mathrm{functionFieldIsoOfIso}\,e\,(\iota(s)) = \iota(e.\mathrm{inv}.\mathrm{stalkMap}_y\,s)$ for $s \in \mathcal O_{X, e.\mathrm{inv}(y)}$; and compatibility with `baseToFunctionField` for structure morphisms $c_X, c_Y$ to $\operatorname{Spec} K$ satisfying $e.\mathrm{hom}$ followed by $c_Y$ equals $c_X$.
--
--   Second, for a field extension $L/K$, a model $\mathrm{Mdl} : \mathrm{CurveModel}\,K\,L$, a morphism $c : C \to \operatorname{Spec} K$ and an isomorphism $e : \mathrm{Mdl}.C \cong C$ with $e.\mathrm{hom}$ followed by $c$ equal to $\mathrm{Mdl}.\mathrm{toBase}$, `transport` is the curve model with underlying scheme $C$ and structure morphism $c$: integrality transfers along $e.\mathrm{hom}$, properness and smoothness of relative dimension $1$ from the factorisation $c = e.\mathrm{inv}$ followed by $\mathrm{Mdl}.\mathrm{toBase}$, function-field identification $L \simeq K(\mathrm{Mdl}.C) \simeq K(C)$, place assignment $x \mapsto \mathrm{Mdl}.\mathrm{placeOfPoint}(e.\mathrm{inv}(x))$ via the bijection `closedPointsEquivOfIso` of closed points induced by $e.\mathrm{inv}$ (bijectivity being the composite of two bijections), the stalk-range condition, and the property that every finite set of points lies in an affine open, obtained from preimages of affine opens under $e.\mathrm{inv}$. The underlying scheme and structure morphism, and the formulae for the function-field equivalence, its inverse, and the place of a closed point, hold definitionally; under $[\mathrm{IsAlgClosed}\,K]$, the point–place bijection of the transported model at a section $x$ of $c$ agrees with that of $\mathrm{Mdl}$ at $x$ followed by $e.\mathrm{inv}$.
--
--   **Relation to Mathlib.** Built on Mathlib's `Scheme.functionField`, `genericPoint`, `closedPoints`, stalk and germ maps, `IsProper` and `SmoothOfRelativeDimension`; the `CurveModel` structure packaging a smooth proper model of $L/K$ together with a bijection between closed points and places is the project's own.
--
--   **Where it is used.** The transported model lets results proved about an abstract smooth proper model of a function field be applied verbatim to a concrete $K$-scheme that happens to be isomorphic to it, with the underlying scheme and structure morphism preserved on the nose; this is used where a curve arises as a component of a fibre identified by an isomorphism with a known model, such as the Igusa components of the special fibre of a modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_CurveModelTransport.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace AlgebraicCurve

section FunctionFieldIso

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

theorem inv_base_genericPoint (e : X ≅ Y) : e.inv.base (genericPoint Y) = genericPoint X :=
  genericPoint_eq_of_isOpenImmersion e.inv

theorem hom_base_genericPoint (e : X ≅ Y) : e.hom.base (genericPoint X) = genericPoint Y :=
  genericPoint_eq_of_isOpenImmersion e.hom

def functionFieldHomOfIso (e : X ≅ Y) : X.functionField ⟶ Y.functionField :=
  X.presheaf.stalkSpecializes (specializes_of_eq (inv_base_genericPoint e)) ≫ e.inv.stalkMap (genericPoint Y)

private theorem isIso_stalkSpecializes_of_eq {Z : Scheme.{u}} {x y : Z} (h : x = y) :
    IsIso (Z.presheaf.stalkSpecializes (specializes_of_eq h)) := by
  subst h
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  infer_instance

instance isIso_functionFieldHomOfIso (e : X ≅ Y) : IsIso (functionFieldHomOfIso e) := by
  haveI := isIso_stalkSpecializes_of_eq (inv_base_genericPoint e)
  exact IsIso.comp_isIso

def functionFieldIsoOfIso (e : X ≅ Y) : X.functionField ≃+* Y.functionField :=
  (asIso (functionFieldHomOfIso e)).commRingCatIsoToRingEquiv

theorem functionFieldIsoOfIso_apply (e : X ≅ Y) (z : X.functionField) :
    functionFieldIsoOfIso e z = (functionFieldHomOfIso e).hom z := rfl

theorem ofHom_functionFieldIsoOfIso (e : X ≅ Y) :
    CommRingCat.ofHom (functionFieldIsoOfIso e).toRingHom = functionFieldHomOfIso e :=
  CommRingCat.hom_ext (RingHom.ext fun _ => rfl)

theorem fromSpecStalk_comp_inv_eq_specMap_functionFieldIsoOfIso (e : X ≅ Y) :
    Y.fromSpecStalk (genericPoint Y) ≫ e.inv =
      Spec.map (CommRingCat.ofHom (functionFieldIsoOfIso e).toRingHom) ≫ X.fromSpecStalk (genericPoint X) := by
  rw [ofHom_functionFieldIsoOfIso, functionFieldHomOfIso, Spec.map_comp, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk]

theorem fromSpecStalk_eq_specMap_functionFieldIsoOfIso_comp_hom (e : X ≅ Y) :
    Y.fromSpecStalk (genericPoint Y) =
      Spec.map (CommRingCat.ofHom (functionFieldIsoOfIso e).toRingHom) ≫ X.fromSpecStalk (genericPoint X) ≫ e.hom := by
  rw [← Category.assoc, ← fromSpecStalk_comp_inv_eq_specMap_functionFieldIsoOfIso, Category.assoc, e.inv_hom_id,
    Category.comp_id]

theorem germ_comp_functionFieldHomOfIso (e : X ≅ Y) :
    X.presheaf.germ ⊤ (genericPoint X) trivial ≫ functionFieldHomOfIso e =
      e.inv.appTop ≫ Y.presheaf.germ ⊤ (genericPoint Y) trivial := by
  rw [functionFieldHomOfIso, ← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes]
  exact Scheme.Hom.germ_stalkMap e.inv ⊤ (genericPoint Y) trivial

theorem stalkToFunctionField_comp_functionFieldHomOfIso (e : X ≅ Y) (y : Y) :
    X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes (Set.mem_univ (e.inv.base y))) ≫
        functionFieldHomOfIso e =
      e.inv.stalkMap y ≫ Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes (Set.mem_univ y)) := by
  rw [functionFieldHomOfIso, ← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
  exact Scheme.Hom.stalkSpecializes_stalkMap e.inv (genericPoint Y) y ((genericPoint_spec Y).specializes (Set.mem_univ y))

theorem functionFieldIsoOfIso_algebraMap_stalk (e : X ≅ Y) (y : Y) (s : X.presheaf.stalk (e.inv.base y)) :
    functionFieldIsoOfIso e (algebraMap (X.presheaf.stalk (e.inv.base y)) X.functionField s) =
      algebraMap (Y.presheaf.stalk y) Y.functionField (e.inv.stalkMap y s) := by
  have h := stalkToFunctionField_comp_functionFieldHomOfIso e y
  have h' := congrArg (fun φ => φ.hom s) h
  simp only [CategoryTheory.comp_apply] at h'
  exact h'

theorem functionFieldIsoOfIso_baseToFunctionField {K : Type u} [Field K]
    (cX : X ⟶ Spec (CommRingCat.of K)) (cY : Y ⟶ Spec (CommRingCat.of K)) (e : X ≅ Y) (he : e.hom ≫ cY = cX) (a : K) :
    functionFieldIsoOfIso e (baseToFunctionField cX a) = baseToFunctionField cY a := by
  have hc : cY = e.inv ≫ cX := by rw [← he, e.inv_hom_id_assoc]
  have h2 : cX.appTop ≫ e.inv.appTop = cY.appTop := by rw [← Scheme.Hom.comp_appTop, ← hc]
  rw [functionFieldIsoOfIso_apply]
  change (X.presheaf.germ ⊤ (genericPoint X) trivial ≫ functionFieldHomOfIso e).hom
      (cX.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) =
    (Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom (cY.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))
  rw [germ_comp_functionFieldHomOfIso]
  change (Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom
      ((cX.appTop ≫ e.inv.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) = _
  rw [h2]

end FunctionFieldIso

namespace CurveModel

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

section ClosedPoints

variable {X Y : Scheme.{u}}

private theorem mem_closedPoints_of_iso {Z W : Scheme.{u}} (f : Z ⟶ W) [IsIso f] {z : Z} (hz : z ∈ closedPoints Z) :
    f.base z ∈ closedPoints W := by
  have h : IsClosed (f.base '' {z}) := f.isClosedEmbedding.isClosedMap _ hz
  rwa [Set.image_singleton] at h

def closedPointsEquivOfIso (e : X ≅ Y) : closedPoints Y ≃ closedPoints X where
  toFun y := ⟨e.inv.base y.1, mem_closedPoints_of_iso e.inv y.2⟩
  invFun x := ⟨e.hom.base x.1, mem_closedPoints_of_iso e.hom x.2⟩
  left_inv y := Subtype.ext (by
    show (e.inv ≫ e.hom).base y.1 = y.1
    rw [e.inv_hom_id]; rfl)
  right_inv x := Subtype.ext (by
    show (e.hom ≫ e.inv).base x.1 = x.1
    rw [e.hom_inv_id]; rfl)

@[simp] theorem closedPointsEquivOfIso_apply_coe (e : X ≅ Y) (y : closedPoints Y) :
    ((closedPointsEquivOfIso e y : closedPoints X) : X) = e.inv.base y.1 := rfl

end ClosedPoints

section Transport

variable (Mdl : CurveModel K L) {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K)) (e : Mdl.C ≅ C)
  (he : e.hom ≫ c = Mdl.toBase)

include he in
private theorem toBase_eq : c = e.inv ≫ Mdl.toBase := by rw [← he, e.inv_hom_id_assoc]

include Mdl e in

private theorem isIntegral_of_iso : IsIntegral C := IsIntegral.of_isIso e.hom

include he in

private theorem isProper_of_iso : IsProper c := by
  rw [toBase_eq Mdl c e he]; infer_instance

include he in

private theorem smooth_of_iso : SmoothOfRelativeDimension 1 c := by
  rw [toBase_eq Mdl c e he]
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (e.inv ≫ Mdl.toBase))

private theorem range_stalk_eq_of_iso (x : closedPoints C) :
    letI := isIntegral_of_iso Mdl e
    (((Mdl.ffEquiv.trans (functionFieldIsoOfIso e)).symm : C.functionField ≃+* L).toRingHom.comp
        (algebraMap (C.presheaf.stalk x.1) C.functionField)).range =
      (Mdl.placeOfPoint (closedPointsEquivOfIso e x)).toValuationSubring.toSubring := by
  letI := isIntegral_of_iso Mdl e
  rw [← Mdl.range_stalk_eq (closedPointsEquivOfIso e x)]
  show _ = ((Mdl.ffEquiv.symm : Mdl.C.functionField ≃+* L).toRingHom.comp
    (algebraMap (Mdl.C.presheaf.stalk (e.inv.base x.1)) Mdl.C.functionField)).range

  have hsurj : Function.Surjective (e.inv.stalkMap x.1).hom :=
    (asIso (e.inv.stalkMap x.1)).commRingCatIsoToRingEquiv.surjective
  ext z
  simp only [RingHom.mem_range, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom]
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨s, rfl⟩ := hsurj t
    refine ⟨s, ?_⟩
    rw [RingEquiv.symm_trans_apply, ← functionFieldIsoOfIso_algebraMap_stalk, RingEquiv.symm_apply_apply]
  · rintro ⟨s, rfl⟩
    refine ⟨(e.inv.stalkMap x.1).hom s, ?_⟩
    rw [RingEquiv.symm_trans_apply, ← functionFieldIsoOfIso_algebraMap_stalk, RingEquiv.symm_apply_apply]

def transport : CurveModel K L :=
  letI := isIntegral_of_iso Mdl e
  { C := C
    toBase := c
    isIntegral := isIntegral_of_iso Mdl e
    isProper := isProper_of_iso Mdl c e he
    smooth := smooth_of_iso Mdl c e he
    ffEquiv := Mdl.ffEquiv.trans (functionFieldIsoOfIso e)
    ffEquiv_algebraMap := fun a => by
      rw [RingEquiv.trans_apply, Mdl.ffEquiv_algebraMap]
      exact functionFieldIsoOfIso_baseToFunctionField Mdl.toBase c e he a
    placeOfPoint := fun x => Mdl.placeOfPoint (closedPointsEquivOfIso e x)
    placeOfPoint_bijective := Mdl.placeOfPoint_bijective.comp (closedPointsEquivOfIso e).bijective
    range_stalk_eq := range_stalk_eq_of_iso Mdl e
    finset_subset_affineOpen := fun F => by
      classical
      obtain ⟨U, hU, hFU⟩ := Mdl.finset_subset_affineOpen (F.image e.inv.base)
      exact ⟨e.inv ⁻¹ᵁ U, hU.preimage_of_isIso e.inv, fun x hx => hFU _ (Finset.mem_image_of_mem _ hx)⟩ }

@[simp] theorem transport_C : (Mdl.transport c e he).C = C := rfl

@[simp] theorem transport_toBase : (Mdl.transport c e he).toBase = c := rfl

theorem transport_ffEquiv :
    (Mdl.transport c e he).ffEquiv =
      (letI := isIntegral_of_iso Mdl e; Mdl.ffEquiv.trans (functionFieldIsoOfIso e)) := rfl

theorem transport_ffEquiv_apply (f : L) :
    (Mdl.transport c e he).ffEquiv f = (letI := isIntegral_of_iso Mdl e; functionFieldIsoOfIso e (Mdl.ffEquiv f)) := rfl

theorem transport_ffEquiv_symm_apply (z : (Mdl.transport c e he).C.functionField) :
    (Mdl.transport c e he).ffEquiv.symm z =
      (letI := isIntegral_of_iso Mdl e; Mdl.ffEquiv.symm ((functionFieldIsoOfIso e).symm z)) := rfl

theorem transport_placeOfPoint (x : closedPoints C) :
    (Mdl.transport c e he).placeOfPoint x = Mdl.placeOfPoint (closedPointsEquivOfIso e x) := rfl

theorem transport_placeOfPoint' (x : closedPoints C) :
    (Mdl.transport c e he).placeOfPoint x =
      Mdl.placeOfPoint ⟨e.inv.base x.1, (closedPointsEquivOfIso e x).2⟩ := rfl

theorem transport_pointEquivPlace [IsAlgClosed K]
    (x : {q : Spec (CommRingCat.of K) ⟶ C // q ≫ c = 𝟙 _}) :
    (Mdl.transport c e he).pointEquivPlace x =
      Mdl.pointEquivPlace ⟨x.1 ≫ e.inv, by rw [Category.assoc, ← toBase_eq Mdl c e he, x.2]⟩ := by
  rw [pointEquivPlace_apply, pointEquivPlace_apply, transport_placeOfPoint]
  congr 1

end Transport

end CurveModel

end AlgebraicCurve

end


