-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_etaleFrame_presentation_of_zariski_sections
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-19T16:34:45.217762+00:00
-- url     : https://prove2.me/submissions/f341b1cb-c587-4c8b-9a8d-bce78018fc95

import Definitions.Def_AlgebraicGeometry_EtaleFrameTorsorCompletion

section
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open PhilipponTorsorSectionFibers PhilipponEtaleFrameTorsor

namespace PhilipponEtaleTorsorZariskiLocal
universe u

abbrev openObject {X : Scheme.{u}} (U : X.Opens) : X.Etale := Scheme.Etale.mk U.ι

end PhilipponEtaleTorsorZariskiLocal
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open PhilipponTorsorSectionFibers PhilipponEtaleTorsorZariskiLocal

namespace PhilipponZariskiTorsorCoordinates
universe u
variable {X : Scheme.{u}}

/-- Open subsets form a diagram in the small étale site by open immersions. -/
def opensToEtale (X : Scheme.{u}) : X.Opens ⥤ X.Etale where
  obj := openObject
  map f := MorphismProperty.Over.homMk (X.homOfLE (leOfHom f))
    (X.homOfLE_ι (leOfHom f))
  map_id U := MorphismProperty.Over.Hom.ext (X.homOfLE_rfl U)
  map_comp f g := MorphismProperty.Over.Hom.ext
    (X.homOfLE_homOfLE (leOfHom f) (leOfHom g)).symm

theorem topIso_inv_natural {U V : X.Opens} (f : V ⟶ U) :
    U.topIso.inv ≫ (X.homOfLE (leOfHom f)).appTop = X.presheaf.map f.op ≫ V.topIso.inv := by
  rw [Scheme.homOfLE_appTop, Scheme.Opens.topIso_inv, Scheme.Opens.topIso_inv,
    ← X.presheaf.map_comp, ← X.presheaf.map_comp]
  congr 1

/-- Sections of the given torsor evaluated on open subschemes. -/
abbrev sections (A : Torsor (PhilipponKummerSequence.units X)) : X.Opensᵒᵖ ⥤ Type u :=
  (opensToEtale X).op ⋙ A.D.P

/-- The ratio of two torsor sections expressed in the sections of the
structure sheaf over the corresponding open subset. -/
def ratio (A : Torsor (PhilipponKummerSequence.units X)) (U : X.Opens)
    (q p : (sections A).obj (op U)) : (Γ(X, U))ˣ :=
  Units.map U.topIso.hom.hom.toMonoidHom (Additive.toMul (A.D.diff (op (openObject U)) q p))

theorem ratio_mul (A : Torsor (PhilipponKummerSequence.units X)) (U : X.Opens)
    (r q p : (sections A).obj (op U)) : ratio A U r q * ratio A U q p = ratio A U r p := by
  rw [ratio, ratio, ratio, ← map_mul]
  exact congrArg (fun a => Units.map U.topIso.hom.hom.toMonoidHom (Additive.toMul a))
    (A.D.diff_add_diff (op (openObject U)) r q p)

theorem ratio_self (A : Torsor (PhilipponKummerSequence.units X)) (U : X.Opens)
    (p : (sections A).obj (op U)) : ratio A U p p = 1 := by
  have h := ratio_mul A U p p p
  exact mul_left_cancel (h.trans (mul_one _).symm)

theorem ratio_restrict (A : Torsor (PhilipponKummerSequence.units X)) {U V : X.Opens}
    (f : V ⟶ U) (q p : (sections A).obj (op U)) :
    Units.map (X.presheaf.map f.op).hom.toMonoidHom (ratio A U q p) =
      ratio A V ((sections A).map f.op q) ((sections A).map f.op p) := by
  let g := (opensToEtale X).map f
  let a : (Γ(U, ⊤))ˣ := Additive.toMul (A.D.diff (op (openObject U)) q p)
  have hmap : Units.map g.left.appTop.hom.toMonoidHom a =
      Additive.toMul (A.D.diff (op (openObject V)) (A.D.P.map g.op q) (A.D.P.map g.op p)) :=
    congrArg Additive.toMul (A.D.map_diff g.op q p)
  change Units.map (X.presheaf.map f.op).hom.toMonoidHom (Units.map U.topIso.hom.hom.toMonoidHom a) =
    Units.map V.topIso.hom.hom.toMonoidHom
      (Additive.toMul (A.D.diff (op (openObject V)) (A.D.P.map g.op q) (A.D.P.map g.op p)))
  have hnat : U.topIso.hom ≫ X.presheaf.map f.op = g.left.appTop ≫ V.topIso.hom := by
    change U.topIso.hom ≫ X.presheaf.map f.op =
      (X.homOfLE (leOfHom f)).appTop ≫ V.topIso.hom
    rw [← Iso.eq_inv_comp, ← Category.assoc, topIso_inv_natural f, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  exact (Units.ext (ConcreteCategory.congr_hom hnat a.val)).trans
    (congrArg (Units.map V.topIso.hom.hom.toMonoidHom) hmap)

end PhilipponZariskiTorsorCoordinates
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open PhilipponTorsorSectionFibers PhilipponZariskiTorsorCoordinates

namespace PhilipponZariskiFrameGluingData
universe u
variable {X : Scheme.{u}} {I : Type u}
variable {A : Torsor (PhilipponKummerSequence.units X)}

/-- A collection of Zariski-local sections of a units torsor. -/
structure ChartFamily (A : Torsor (PhilipponKummerSequence.units X)) (I : Type u) where
  U : I → X.Opens
  s : ∀ i, (sections A).obj (op (U i))

abbrev res {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom

theorem res_res {U V W : X.Opens} (h : W ≤ V) (k : V ≤ U) (a : Γ(X, U)) :
    res h (res k a) = res (h.trans k) a := by
  exact (ConcreteCategory.congr_hom (X.presheaf.map_comp (homOfLE k).op (homOfLE h).op) a).symm

theorem res_self (U : X.Opens) (a : Γ(X, U)) : res (le_refl U) a = a := by
  exact ConcreteCategory.congr_hom (X.presheaf.map_id (op U)) a

namespace ChartFamily

variable (C : ChartFamily A I)

/-- The transition on an open contained in two of the charts, taking the
ratio of the second chart's section to the first one's section. -/
def changeUnit {V : X.Opens} {i j : I} (hi : V ≤ C.U i) (hj : V ≤ C.U j) : (Γ(X, V))ˣ :=
  ratio A V ((sections A).map (homOfLE hj).op (C.s j))
    ((sections A).map (homOfLE hi).op (C.s i))

theorem changeUnit_mul {V : X.Opens} {i j k : I}
    (hi : V ≤ C.U i) (hj : V ≤ C.U j) (hk : V ≤ C.U k) :
    C.changeUnit hi hj * C.changeUnit hj hk = C.changeUnit hi hk :=
  (mul_comm _ _).trans (ratio_mul A V _ _ _)

theorem changeUnit_self {V : X.Opens} {i : I} (hi : V ≤ C.U i) :
    C.changeUnit hi hi = 1 := ratio_self A V _

theorem changeUnit_restrict {W V : X.Opens} {i j : I}
    (e : W ≤ V) (hi : V ≤ C.U i) (hj : V ≤ C.U j) :
    Units.map (res e).toMonoidHom (C.changeUnit hi hj) =
      C.changeUnit (e.trans hi) (e.trans hj) := by
  rw [changeUnit, ratio_restrict, ← Functor.map_comp_apply, ← Functor.map_comp_apply]
  rfl

abbrev Piece (V : X.Opens) (i : I) : X.Opens := V ⊓ C.U i

abbrev Overlap (V : X.Opens) (i j : I) : X.Opens := C.Piece V i ⊓ C.Piece V j

abbrev PieceModule (V : X.Opens) (i : I) : ModuleCat.{u} Γ(X, V) :=
  (ModuleCat.restrictScalars (res (inf_le_left : C.Piece V i ≤ V))).obj
    (ModuleCat.of Γ(X, C.Piece V i) Γ(X, C.Piece V i))

abbrev Coordinates (V : X.Opens) := ∀ i : I, C.PieceModule V i

def Matches (V : X.Opens) (a : C.Coordinates V) : Prop :=
  ∀ i j : I,
    res (inf_le_left : C.Overlap V i j ≤ C.Piece V i) (a i) =
      (C.changeUnit ((inf_le_left : C.Overlap V i j ≤ C.Piece V i).trans inf_le_right)
        ((inf_le_right : C.Overlap V i j ≤ C.Piece V j).trans inf_le_right)).val *
      res (inf_le_right : C.Overlap V i j ≤ C.Piece V j) (a j)

abbrev mulAt (V : X.Opens) (a b : Γ(X, V)) : Γ(X, V) := a * b

/-- Matching local coordinates form a module over functions on the open. -/
def matching (V : X.Opens) : Submodule Γ(X, V) (C.Coordinates V) where
  carrier := C.Matches V
  zero_mem' i j := by
    change res (inf_le_left : C.Overlap V i j ≤ C.Piece V i) 0 = _ *
      res (inf_le_right : C.Overlap V i j ≤ C.Piece V j) 0
    rw [map_zero, map_zero, mul_zero]
  add_mem' {a b} ha hb i j := by
    change res (inf_le_left : C.Overlap V i j ≤ C.Piece V i) (a i + b i) = _ *
      res (inf_le_right : C.Overlap V i j ≤ C.Piece V j) (a j + b j)
    rw [map_add, map_add, mul_add, ha i j, hb i j]
  smul_mem' r a ha i j := by
    change res (inf_le_left : C.Overlap V i j ≤ C.Piece V i)
      (mulAt (C.Piece V i) (res (inf_le_left : C.Piece V i ≤ V) r) (a i)) = _ *
      res (inf_le_right : C.Overlap V i j ≤ C.Piece V j)
        (mulAt (C.Piece V j) (res (inf_le_left : C.Piece V j ≤ V) r) (a j))
    unfold mulAt
    rw [map_mul, map_mul, res_res, res_res, ha i j, mul_left_comm]

/-- A matching family restricts by restricting each of its coordinates. -/
def restrict {V W : X.Opens} (h : W ≤ V) (a : C.matching V) : C.matching W := by
  let hPiece (i : I) : C.Piece W i ≤ C.Piece V i := inf_le_inf_right _ h
  let b : C.Coordinates W := fun i => res (hPiece i) (a.val i)
  refine ⟨b, fun i j => ?_⟩
  let ei : C.Overlap W i j ≤ C.Piece W i := inf_le_left
  let ej : C.Overlap W i j ≤ C.Piece W j := inf_le_right
  let di : C.Overlap V i j ≤ C.Piece V i := inf_le_left
  let dj : C.Overlap V i j ≤ C.Piece V j := inf_le_right
  let p : C.Overlap W i j ≤ C.Overlap V i j := inf_le_inf (hPiece i) (hPiece j)
  have hv := congrArg (res p) (a.property i j)
  have hu : res p (C.changeUnit (di.trans inf_le_right) (dj.trans inf_le_right)).val =
      (C.changeUnit (ei.trans inf_le_right) (ej.trans inf_le_right)).val :=
    congrArg Units.val (C.changeUnit_restrict p (di.trans inf_le_right) (dj.trans inf_le_right))
  change res ei (res (hPiece i) (a.val i)) =
    (C.changeUnit (ei.trans inf_le_right) (ej.trans inf_le_right)).val *
      res ej (res (hPiece j) (a.val j))
  change res p (res di (a.val i)) =
    res p ((C.changeUnit (di.trans inf_le_right) (dj.trans inf_le_right)).val *
      res dj (a.val j)) at hv
  rw [map_mul, hu, res_res, res_res] at hv
  rw [res_res, res_res]
  exact hv

theorem restrict_id (V : X.Opens) (a : C.matching V) : C.restrict (le_refl V) a = a := by
  apply Subtype.ext
  funext i
  exact res_self _ _

theorem restrict_restrict {U V W : X.Opens} (h : W ≤ V) (k : V ≤ U) (a : C.matching U) :
    C.restrict h (C.restrict k a) = C.restrict (h.trans k) a := by
  apply Subtype.ext
  funext i
  exact res_res _ _ _

end ChartFamily
end PhilipponZariskiFrameGluingData
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open PhilipponTorsorSectionFibers PhilipponZariskiFrameGluingData

namespace PhilipponZariskiFrameGluingData.ChartFamily
universe u
variable {X : Scheme.{u}} {I : Type u}
variable {A : Torsor (PhilipponKummerSequence.units X)}
variable (C : ChartFamily A I) {V : X.Opens} {i : I}

/-- On an open contained in a chart, the chart's own coordinate is a section
over the whole open. -/
def evaluate (h : V ≤ C.U i) (a : C.matching V) : Γ(X, V) := res (le_inf le_rfl h) (a.val i)

/-- Extend one coordinate to all the charts by the transition units. -/
def extend (h : V ≤ C.U i) (a : Γ(X, V)) : C.matching V := by
  let p (j : I) : C.Piece V j ≤ V := inf_le_left
  let q (j : I) : C.Piece V j ≤ C.U j := inf_le_right
  let b : C.Coordinates V := fun j =>
    mulAt (C.Piece V j) (C.changeUnit (q j) ((p j).trans h)).val (res (p j) a)
  refine ⟨b, fun j k => ?_⟩
  let ej : C.Overlap V j k ≤ C.Piece V j := inf_le_left
  let ek : C.Overlap V j k ≤ C.Piece V k := inf_le_right
  let dj : C.Overlap V j k ≤ C.U j := ej.trans (q j)
  let dk : C.Overlap V j k ≤ C.U k := ek.trans (q k)
  let di : C.Overlap V j k ≤ C.U i := (ej.trans (p j)).trans h
  have hj : res ej (C.changeUnit (q j) ((p j).trans h)).val = (C.changeUnit dj di).val :=
    congrArg Units.val (C.changeUnit_restrict ej (q j) ((p j).trans h))
  have hk : res ek (C.changeUnit (q k) ((p k).trans h)).val = (C.changeUnit dk di).val :=
    congrArg Units.val (C.changeUnit_restrict ek (q k) ((p k).trans h))
  have he : (C.changeUnit dj dk).val * (C.changeUnit dk di).val = (C.changeUnit dj di).val :=
    congrArg Units.val (C.changeUnit_mul dj dk di)
  change res ej (mulAt _ (C.changeUnit (q j) ((p j).trans h)).val (res (p j) a)) =
    (C.changeUnit dj dk).val *
      res ek (mulAt _ (C.changeUnit (q k) ((p k).trans h)).val (res (p k) a))
  unfold mulAt
  rw [map_mul, map_mul, hj, hk, res_res, res_res, ← mul_assoc, he]

theorem evaluate_extend (h : V ≤ C.U i) (a : Γ(X, V)) : C.evaluate h (C.extend h a) = a := by
  let k : C.Piece V i ≤ V := inf_le_left
  change res (le_inf le_rfl h) (mulAt _
    (C.changeUnit (inf_le_right : C.Piece V i ≤ C.U i) (k.trans h)).val (res k a)) = a
  rw [C.changeUnit_self (inf_le_right : C.Piece V i ≤ C.U i)]
  change res (le_inf le_rfl h) (1 * res k a) = a
  rw [one_mul, res_res, res_self]

theorem extend_evaluate (h : V ≤ C.U i) (a : C.matching V) : C.extend h (C.evaluate h a) = a := by
  apply Subtype.ext
  funext j
  let ej : C.Overlap V j i ≤ C.Piece V j := inf_le_left
  let ei : C.Overlap V j i ≤ C.Piece V i := inf_le_right
  let e : C.Piece V j ≤ C.Overlap V j i := le_inf le_rfl
    (le_inf inf_le_left (inf_le_left.trans h))
  let hj : C.Piece V j ≤ C.U j := inf_le_right
  let hi : C.Piece V j ≤ C.U i := inf_le_left.trans h
  have ha := congrArg (res e) (a.property j i)
  change res e (res ej (a.val j)) =
    res e ((C.changeUnit (ej.trans inf_le_right) (ei.trans inf_le_right)).val *
      res ei (a.val i)) at ha
  have hh : res e (C.changeUnit (ej.trans inf_le_right) (ei.trans inf_le_right)).val =
      (C.changeUnit hj hi).val :=
    congrArg Units.val (C.changeUnit_restrict e (ej.trans inf_le_right) (ei.trans inf_le_right))
  rw [map_mul, hh, res_res, res_res, res_self] at ha
  change mulAt _ (C.changeUnit hj hi).val (res inf_le_left (res (le_inf le_rfl h) (a.val i))) = a.val j
  rw [res_res]
  exact ha.symm

/-- Changing the chart multiplies the coordinate by the transition unit. -/
theorem evaluate_extend_other {j : I} (hi : V ≤ C.U i) (hj : V ≤ C.U j) (a : Γ(X, V)) :
    C.evaluate hi (C.extend hj a) = (C.changeUnit hi hj).val * a := by
  let k : C.Piece V i ≤ V := inf_le_left
  let e : V ≤ C.Piece V i := le_inf le_rfl hi
  let g : C.Piece V i ≤ C.U i := inf_le_right
  have he : res e (C.changeUnit g (k.trans hj)).val = (C.changeUnit hi hj).val :=
    congrArg Units.val (C.changeUnit_restrict e g (k.trans hj))
  change res e (mulAt _ (C.changeUnit g (k.trans hj)).val (res k a)) = _
  unfold mulAt
  rw [map_mul, he, res_res, res_self]

theorem evaluate_change {j : I} (hi : V ≤ C.U i) (hj : V ≤ C.U j) (a : C.matching V) :
    C.evaluate hi a = (C.changeUnit hi hj).val * C.evaluate hj a :=
  (congrArg (C.evaluate hi) (C.extend_evaluate hj a)).symm.trans
    (C.evaluate_extend_other hi hj (C.evaluate hj a))

end PhilipponZariskiFrameGluingData.ChartFamily
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open PhilipponTorsorSectionFibers PhilipponZariskiFrameGluingData

namespace PhilipponZariskiFrameGluingData.ChartFamily
universe u
variable {X : Scheme.{u}} {I : Type u}
variable {A : Torsor (PhilipponKummerSequence.units X)}
variable (C : ChartFamily A I)

theorem restrict_apply {V W : X.Opens} (e : W ≤ V) (a : C.matching V) (j : I) :
    (C.restrict e a).val j = res (inf_le_inf_right (C.U j) e) (a.val j) := rfl

theorem restrict_add {V W : X.Opens} (e : W ≤ V) (a b : C.matching V) :
    C.restrict e (a + b) = C.restrict e a + C.restrict e b := by
  apply Subtype.ext
  funext j
  exact map_add (res (inf_le_inf_right (C.U j) e)) (a.val j) (b.val j)

theorem restrict_smul {V W : X.Opens} (e : W ≤ V) (r : Γ(X, V)) (a : C.matching V) :
    C.restrict e (r • a) = res e r • C.restrict e a := by
  apply Subtype.ext
  funext j
  let k : C.Piece W j ≤ C.Piece V j := inf_le_inf_right _ e
  let h : C.Piece V j ≤ V := inf_le_left
  let g : C.Piece W j ≤ W := inf_le_left
  change res k (mulAt _ (res h r) (a.val j)) =
    mulAt _ (res g (res e r)) (res k (a.val j))
  unfold mulAt
  rw [map_mul, res_res, res_res]

/-- Compatible chart coordinates form a presheaf of modules over the
Zariski structure sheaf. -/
def presheafOfModules : PresheafOfModules.{u} X.ringCatSheaf.obj where
  obj V := ModuleCat.of Γ(X, V.unop) (C.matching V.unop)
  map {V W} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map f).hom).obj
      (ModuleCat.of Γ(X, W.unop) (C.matching W.unop)))
    { toFun := C.restrict (leOfHom f.unop)
      map_add' := C.restrict_add (leOfHom f.unop)
      map_smul' := C.restrict_smul (leOfHom f.unop) }
  map_id V := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact C.restrict_id V.unop a
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (C.restrict_restrict (leOfHom g.unop) (leOfHom f.unop) a).symm

abbrev asTypes : X.Opensᵒᵖ ⥤ Type u :=
  C.presheafOfModules.presheaf ⋙ forget AddCommGrpCat

theorem types_map_apply {V W : X.Opens} (f : W ⟶ V) (a : C.matching V) :
    C.asTypes.map f.op a = C.restrict (leOfHom f) a := rfl

theorem evaluate_restrict {V W : X.Opens} {i : I} (h : V ≤ C.U i) (e : W ≤ V)
    (a : C.matching V) : C.evaluate (e.trans h) (C.restrict e a) = res e (C.evaluate h a) := by
  change res (le_inf le_rfl (e.trans h))
    (res (inf_le_inf_right (C.U i) e) (a.val i)) = res e (res (le_inf le_rfl h) (a.val i))
  rw [res_res, res_res]

end PhilipponZariskiFrameGluingData.ChartFamily
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open PhilipponTorsorSectionFibers PhilipponZariskiFrameGluingData

namespace PhilipponZariskiFrameGluingData.ChartFamily
universe u
variable {X : Scheme.{u}} {I : Type u}
variable {A : Torsor (PhilipponKummerSequence.units X)}
variable (C : ChartFamily A I)

private abbrev O (X : Scheme.{u}) : X.Opensᵒᵖ ⥤ Type u := X.presheaf ⋙ forget CommRingCat

private theorem isSheaf_O (X : Scheme.{u}) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (O X) :=
  Presheaf.isSheaf_comp_of_isSheaf _ _ _ X.sheaf.property

private theorem evaluate_restrict_piece {V W : X.Opens} {i : I} (e : W ≤ V) (h : W ≤ C.U i)
    (a : C.matching V) : C.evaluate h (C.restrict e a) = res (le_inf e h) (a.val i) := by
  change res (le_inf le_rfl h) (res (inf_le_inf_right (C.U i) e) (a.val i)) = _
  rw [res_res]

private theorem exists_coordinate {V : X.Opens} (S : Sieve V)
    (hS : S ∈ Opens.grothendieckTopology X V)
    (a : S.arrows.FamilyOfElements C.asTypes) (ha : a.Compatible) (i : I) :
    ∃ b : Γ(X, C.Piece V i), ∀ (W : X.Opens) (e : W ≤ C.Piece V i)
      (he : S (homOfLE (e.trans inf_le_left))),
      res e b = C.evaluate (e.trans inf_le_right) (a (homOfLE (e.trans inf_le_left)) he) := by
  let ι : C.Piece V i ⟶ V := homOfLE inf_le_left
  let b : (S.pullback ι).arrows.FamilyOfElements (O X) := fun _ g hg =>
    C.evaluate ((leOfHom g).trans inf_le_right) (a (g ≫ ι) hg)
  have hb : b.Compatible := by
    apply (Presieve.compatible_iff_sieveCompatible b).mpr
    intro W W' f g hf
    have h := ha.to_sieveCompatible (f ≫ ι) g hf
    rw [C.types_map_apply] at h
    change C.evaluate ((leOfHom (g ≫ f)).trans inf_le_right)
      (a ((g ≫ f) ≫ ι) (by simpa only [Category.assoc] using S.downward_closed hf g)) =
      res (leOfHom g) (C.evaluate ((leOfHom f).trans inf_le_right) (a (f ≫ ι) hf))
    rw [Category.assoc, h]
    exact C.evaluate_restrict ((leOfHom f).trans inf_le_right) (leOfHom g) (a (f ≫ ι) hf)
  obtain ⟨t, ht, _⟩ := (isSheaf_O X).isSheafFor _
    ((Opens.grothendieckTopology X).pullback_stable ι hS) b hb
  refine ⟨t, fun W e he => ?_⟩
  exact ht (homOfLE e) he

/-- Compatible coordinates are a sheaf because the coordinates glue on each
chart and the transition equations can be tested locally. -/
theorem isSheaf_types : Presheaf.IsSheaf (Opens.grothendieckTopology X) C.asTypes := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro V S hS a ha
  choose b hb using fun i => C.exists_coordinate S hS a ha i
  have hmatch : C.Matches V b := by
    intro i j
    let ei : C.Overlap V i j ≤ C.Piece V i := inf_le_left
    let ej : C.Overlap V i j ≤ C.Piece V j := inf_le_right
    let ι : C.Overlap V i j ⟶ V := homOfLE (ei.trans inf_le_left)
    apply ((isSheaf_O X).isSheafFor _
      ((Opens.grothendieckTopology X).pullback_stable ι hS)).isSeparatedFor.ext
    intro W f hf
    let e := leOfHom f
    let hi : W ≤ C.U i := (e.trans ei).trans inf_le_right
    let hj : W ≤ C.U j := (e.trans ej).trans inf_le_right
    have hu : res e (C.changeUnit (ei.trans inf_le_right) (ej.trans inf_le_right)).val =
        (C.changeUnit hi hj).val :=
      congrArg Units.val (C.changeUnit_restrict e (ei.trans inf_le_right) (ej.trans inf_le_right))
    change res e (res ei (b i)) = res e
      ((C.changeUnit (ei.trans inf_le_right) (ej.trans inf_le_right)).val * res ej (b j))
    rw [map_mul, hu, res_res, res_res, hb i W (e.trans ei) hf, hb j W (e.trans ej) hf]
    exact C.evaluate_change hi hj (a (f ≫ ι) hf)
  let t : C.matching V := ⟨b, hmatch⟩
  have hglue : a.IsAmalgamation t := by
    intro W f hf
    apply Subtype.ext
    funext i
    let e : C.Piece W i ≤ C.Piece V i := inf_le_inf_right _ (leOfHom f)
    let k : C.Piece W i ⟶ W := homOfLE inf_le_left
    let h := S.downward_closed hf k
    have hc := ha.to_sieveCompatible f k hf
    rw [C.types_map_apply] at hc
    change res e (b i) = (a f hf).val i
    rw [hb i _ e h, show homOfLE (e.trans inf_le_left) = k ≫ f from Subsingleton.elim _ _, hc,
      C.evaluate_restrict_piece]
    exact res_self _ _
  refine ⟨t, hglue, ?_⟩
  intro y hy
  apply Subtype.ext
  funext i
  let ι : C.Piece V i ⟶ V := homOfLE inf_le_left
  apply ((isSheaf_O X).isSheafFor _
    ((Opens.grothendieckTopology X).pullback_stable ι hS)).isSeparatedFor.ext
  intro W f hf
  have hy' := congrArg (C.evaluate ((leOfHom f).trans (inf_le_right : C.Piece V i ≤ C.U i)))
    (hy (f ≫ ι) hf)
  have ht' := congrArg (C.evaluate ((leOfHom f).trans (inf_le_right : C.Piece V i ≤ C.U i)))
    (hglue (f ≫ ι) hf)
  rw [C.types_map_apply, C.evaluate_restrict_piece] at hy' ht'
  exact hy'.trans ht'.symm

/-- The sheaf of modules given by the chart transition functions. -/
def gluedModule : X.Modules where
  val := C.presheafOfModules
  isSheaf := (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget AddCommGrpCat)).2 C.isSheaf_types

end PhilipponZariskiFrameGluingData.ChartFamily
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 950000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open PhilipponTorsorSectionFibers PhilipponZariskiFrameGluingData
open PhilipponEtaleFrameSections PhilipponFrameUnits PhilipponEtaleTorsorZariskiLocal

namespace PhilipponZariskiFrameGluingData.ChartFamily
universe u
variable {X : Scheme.{u}} {I : Type u}
variable {A : Torsor (PhilipponKummerSequence.units X)}
variable (C : ChartFamily A I)

theorem evaluate_add {V : X.Opens} {i : I} (h : V ≤ C.U i) (a b : C.matching V) :
    C.evaluate h (a + b) = C.evaluate h a + C.evaluate h b :=
  map_add (res (le_inf le_rfl h)) (a.val i) (b.val i)

theorem evaluate_smul {V : X.Opens} {i : I} (h : V ≤ C.U i) (r : Γ(X, V)) (a : C.matching V) :
    C.evaluate h (r • a) = r * C.evaluate h a := by
  let k : C.Piece V i ≤ V := inf_le_left
  let e : V ≤ C.Piece V i := le_inf le_rfl h
  change res e (mulAt _ (res k r) (a.val i)) = mulAt V r (res e (a.val i))
  unfold mulAt
  rw [map_mul, res_res, res_self]

private def evaluateOn (i : I) (W : (C.U i).toScheme.Opens) :
    Γ(C.gluedModule.restrict (C.U i).ι, W) ≃+
      (Γ((C.U i).toScheme, W) : Type u) where
  toFun := C.evaluate ((C.U i).ι_image_le W)
  invFun := C.extend ((C.U i).ι_image_le W)
  left_inv := C.extend_evaluate ((C.U i).ι_image_le W)
  right_inv := C.evaluate_extend ((C.U i).ι_image_le W)
  map_add' := C.evaluate_add ((C.U i).ι_image_le W)

/-- Reading the coordinate of the chosen chart trivializes the restriction
of the glued module to that chart. -/
def coordinateIso (i : I) : C.gluedModule.restrict (C.U i).ι ≅ trivial ((C.U i).toScheme) := by
  let U := C.U i
  refine (SheafOfModules.fullyFaithfulForget ((C.U i).toScheme.ringCatSheaf)).preimageIso
    (PresheafOfModules.isoMk (fun W => ?_) ?_)
  · refine ModuleCat.isoMk (C.evaluateOn i W.unop).toAddCommGrpIso ?_
    intro r
    apply ConcreteCategory.hom_ext
    intro a
    let h := U.ι_image_le W.unop
    let r' : Γ(U.toScheme, W.unop) := r
    let a' : Γ(C.gluedModule.restrict U.ι, W.unop) := a
    let v : C.matching (U.ι ''ᵁ W.unop) := a
    have hs := Scheme.Modules.smul_restrictAppIso_hom_apply U.ι C.gluedModule W.unop r' a'
    change r' • a' = (U.ι.appIso W.unop).inv r' • v at hs
    change mulAt (U.ι ''ᵁ W.unop) r' (C.evaluate h v) = C.evaluate h (r' • a')
    rw [hs, Scheme.Opens.ι_appIso, Iso.refl_inv]
    exact (C.evaluate_smul h r' v).symm
  · intro V W f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    let k := U.ι.image_mono (leOfHom f.unop)
    change C.evaluate (U.ι_image_le W.unop) (C.restrict k a) =
      res k (C.evaluate (U.ι_image_le V.unop) a)
    exact C.evaluate_restrict (U.ι_image_le V.unop) k a

theorem coordinateIso_apply (i : I) (W : (C.U i).toScheme.Opens)
    (a : Γ(C.gluedModule.restrict (C.U i).ι, W)) :
    (C.coordinateIso i).hom.app W a = C.evaluate ((C.U i).ι_image_le W) a := rfl

theorem invertible (hC : ∀ x : X, ∃ i : I, x ∈ C.U i) :
    Scheme.Modules.IsInvertible C.gluedModule where
  exists_trivialization x := by
    obtain ⟨i, hi⟩ := hC x
    exact ⟨C.U i, hi, ⟨((Scheme.Modules.restrictFunctorIsoPullback (C.U i).ι).app
      C.gluedModule).symm ≪≫ C.coordinateIso i⟩⟩

def chartFrame (i : I) : Frame C.gluedModule (openObject (C.U i)) :=
  (C.coordinateIso i).symm ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback (C.U i).ι).app C.gluedModule

end PhilipponZariskiFrameGluingData.ChartFamily
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

namespace PhilipponPullbackSectionMaps
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The map on sections given by the unit of inverse and direct image. -/
abbrev onSections (M : Y.Modules) (U : Y.Opens) :
    Γ(M, U) ⟶ Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ U) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U

theorem onSections_smul (M : Y.Modules) (U : Y.Opens) (r : Γ(Y, U)) (a : Γ(M, U)) :
    onSections f M U (r • a) = f.app U r • onSections f M U a :=
  Scheme.Modules.Hom.app_smul ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) r a

/-- The section map of an open immersion is an isomorphism over an open
contained in its image. -/
theorem onSections_isIso [IsOpenImmersion f] (M : Y.Modules) (U : Y.Opens) (hU : U ≤ f.opensRange) :
    IsIso (onSections f M U) := by
  let e := Scheme.Modules.restrictFunctorIsoPullback f
  have h := Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction f) M
  have h' := congrArg (fun a => Scheme.Modules.Hom.app a U) h
  change ((Scheme.Modules.restrictAdjunction f).unit.app M).app U ≫ (e.hom.app M).app (f ⁻¹ᵁ U) =
    onSections f M U at h'
  have hEq : f ''ᵁ (f ⁻¹ᵁ U) = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    exact inf_eq_right.mpr hU
  have heq : (homOfLE (f.image_preimage_le U)) = eqToHom hEq := Subsingleton.elim _ _
  have hi : IsIso (((Scheme.Modules.restrictAdjunction f).unit.app M).app U) := by
    rw [Scheme.Modules.restrictAdjunction_unit_app_app, heq]
    infer_instance
  rw [← h']
  infer_instance

theorem onSections_naturality {M N : Y.Modules} (a : M ⟶ N) (U : Y.Opens) :
    a.app U ≫ onSections f N U =
      onSections f M U ≫ ((Scheme.Modules.pullback f).map a).app (f ⁻¹ᵁ U) := by
  have h := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality a
  exact congrArg (fun k => Scheme.Modules.Hom.app k U) h

theorem onSections_restrict (M : Y.Modules) {U V : Y.Opens} (i : V ⟶ U) :
    M.presheaf.map i.op ≫ onSections f M V = onSections f M U ≫
      ((Scheme.Modules.pullback f).obj M).presheaf.map
        ((TopologicalSpace.Opens.map f.base).map i).op :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).mapPresheaf.naturality i.op

/-- The section maps for successive pullbacks agree with the composite
via the canonical comparison of pullback functors. -/
theorem onSections_comp {Z : Scheme.{u}} (g : Z ⟶ X) (M : Y.Modules) (U : Y.Opens) :
    onSections (g ≫ f) M U = onSections f M U ≫
      onSections g ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U) ≫
      ((Scheme.Modules.pullbackComp g f).hom.app M).app ((g ≫ f) ⁻¹ᵁ U) := by
  let F := Scheme.Modules.pullback f
  let adjF := Scheme.Modules.pullbackPushforwardAdjunction f
  let adjG := Scheme.Modules.pullbackPushforwardAdjunction g
  let adjC := Scheme.Modules.pullbackPushforwardAdjunction (g ≫ f)
  let P := Scheme.Modules.pushforward (g ≫ f)
  let e := (Scheme.Modules.pullbackComp g f).app M
  have h := unit_conjugateEquiv (adjF.comp adjG) adjC (Scheme.Modules.pullbackComp g f).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  change (adjF.comp adjG).unit.app M ≫ (Scheme.Modules.pushforwardComp g f).hom.app
      ((F ⋙ Scheme.Modules.pullback g).obj M) = adjC.unit.app M ≫ P.map e.inv at h
  have h' := congrArg (fun k => k ≫ P.map e.hom) h
  simp only [Category.assoc] at h'
  rw [← P.map_comp, Iso.inv_hom_id, P.map_id] at h'
  have hh := congrArg (fun k => Scheme.Modules.Hom.app k U)
    (h'.trans (Category.comp_id (adjC.unit.app M)))
  rw [Adjunction.comp_unit_app] at hh
  let c := (e.hom).app ((g ≫ f) ⁻¹ᵁ U)
  let a := onSections f M U
  let b := onSections g ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U)
  simp only [adjC, adjF, adjG, F, P, e, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforward_map_app,
    Category.assoc] at hh
  change a ≫ b ≫ 𝟙 _ ≫ c = onSections (g ≫ f) M U at hh
  exact hh.symm.trans (congrArg (fun k => a ≫ b ≫ k) (Category.id_comp c))

end PhilipponPullbackSectionMaps
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory
open PhilipponFrameUnits PhilipponFramePullback PhilipponPullbackSectionMaps

namespace PhilipponFrameCoordinateRestriction
universe u
variable {X Y Z : Scheme.{u}}

private theorem unit_map (g : Z ⟶ Y) (U : Y.Opens) (s : Γ(Y, U)) :
    (unitIso g).hom.app (g ⁻¹ᵁ U) (onSections g (trivial Y) U s) = g.app U s := by
  let a := Scheme.Modules.pullbackPushforwardAdjunction g
  have h : a.homEquiv (trivial Y) (trivial Z) (unitIso g).hom =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  rw [a.homEquiv_unit] at h
  exact ConcreteCategory.congr_hom (congrArg (fun t => Scheme.Modules.Hom.app t U) h) s

def restrictCoordinate (f : Y ⟶ X) (g : Z ⟶ Y) {M : X.Modules}
    (v : (Scheme.Modules.pullback f).obj M ⟶ trivial Y) :
    (Scheme.Modules.pullback (g ≫ f)).obj M ⟶ trivial Z :=
  (Scheme.Modules.pullbackComp g f).inv.app M ≫
    (Scheme.Modules.pullback g).map v ≫ (unitIso g).hom

/-- Coordinates of a pulled-back section restrict by the map of
structure sheaves. -/
theorem coordinate_restrict_section (f : Y ⟶ X) (g : Z ⟶ Y) {M : X.Modules}
    (v : (Scheme.Modules.pullback f).obj M ⟶ trivial Y) (U : X.Opens) (s : Γ(M, U)) :
    (restrictCoordinate f g v).app ((g ≫ f) ⁻¹ᵁ U)
        (onSections (g ≫ f) M U s) =
      g.app (f ⁻¹ᵁ U) (v.app (f ⁻¹ᵁ U) (onSections f M U s)) := by
  let W := (g ≫ f) ⁻¹ᵁ U
  let c := (Scheme.Modules.pullbackComp g f).app M
  have hc : c.hom.app W ≫ c.inv.app W = 𝟙 _ :=
    congrArg (fun t => Scheme.Modules.Hom.app t W) c.hom_inv_id
  have hs := onSections_comp f g M U
  have h : onSections (g ≫ f) M U ≫ (restrictCoordinate f g v).app W =
      onSections f M U ≫ v.app (f ⁻¹ᵁ U) ≫
        onSections g (trivial Y) (f ⁻¹ᵁ U) ≫ (unitIso g).hom.app W := by
    change onSections (g ≫ f) M U ≫ (restrictCoordinate f g v).app W = _
    rw [hs]
    change (onSections f M U ≫ onSections g ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U) ≫
        c.hom.app W) ≫ (restrictCoordinate f g v).app W = _
    simp only [restrictCoordinate, Scheme.Modules.Hom.comp_app, Category.assoc]
    change onSections f M U ≫ onSections g ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U) ≫
        c.hom.app W ≫ c.inv.app W ≫ _ = _
    rw [← Category.assoc (c.hom.app W), hc, Category.id_comp]
    erw [← reassoc_of% (onSections_naturality g v (f ⁻¹ᵁ U))]
  have hh := ConcreteCategory.congr_hom h s
  exact hh.trans (unit_map g (f ⁻¹ᵁ U) (v.app (f ⁻¹ᵁ U) (onSections f M U s)))

/-- Coordinate restriction with the composite identified with the given map. -/
theorem coordinate_restrict_section_of_eq (f : Y ⟶ X) (g : Z ⟶ Y) {k : Z ⟶ X}
    (h : g ≫ f = k) {M : X.Modules} (v : (Scheme.Modules.pullback f).obj M ⟶ trivial Y)
    (U : X.Opens) (s : Γ(M, U)) :
    ((Scheme.Modules.pullbackCongr h).inv.app M ≫ restrictCoordinate f g v).app (k ⁻¹ᵁ U)
        (onSections k M U s) =
      Z.presheaf.map (eqToHom (congrArg (fun a : Z ⟶ X => a ⁻¹ᵁ U) h.symm)).op
        (g.app (f ⁻¹ᵁ U) (v.app (f ⁻¹ᵁ U) (onSections f M U s))) := by
  subst k
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp, eqToHom_refl, op_id]
  exact (coordinate_restrict_section f g v U s).trans
    (ConcreteCategory.congr_hom (Z.presheaf.map_id (Opposite.op ((g ≫ f) ⁻¹ᵁ U))) _).symm

theorem coordinate_restrict_top_of_eq (f : Y ⟶ X) (g : Z ⟶ Y) {k : Z ⟶ X}
    (h : g ≫ f = k) {M : X.Modules} (v : (Scheme.Modules.pullback f).obj M ⟶ trivial Y)
    (s : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackCongr h).inv.app M ≫ restrictCoordinate f g v).app ⊤
        (onSections k M ⊤ s) =
      g.appTop (v.app ⊤ (onSections f M ⊤ s)) := by
  subst k
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp]
  with_unfolding_all
    exact coordinate_restrict_section f g v ⊤ s

end PhilipponFrameCoordinateRestriction
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory
open PhilipponEtaleFrameSections PhilipponFramePullback PhilipponPullbackSectionMaps
open PhilipponFrameCoordinateRestriction

namespace PhilipponEtaleFrameCoordinateRestriction
universe u
variable {X : Scheme.{u}} {M : X.Modules} {U V : X.Etale}

theorem restrict_inv (f : V ⟶ U) (p : Frame M U) :
    (restrict M f p).inv =
      (Scheme.Modules.pullbackCongr (MorphismProperty.Over.w f)).inv.app M ≫
        restrictCoordinate U.hom f.left p.inv := by
  simp only [restrict, pullFrame, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv,
    Iso.app_inv, Category.assoc, restrictCoordinate]

theorem restrict_inv_section (f : V ⟶ U) (p : Frame M U) (s : Γ(M, ⊤)) :
    (restrict M f p).inv.app ⊤ (onSections V.hom M ⊤ s) =
      f.left.appTop (p.inv.app ⊤ (onSections U.hom M ⊤ s)) := by
  rw [restrict_inv f p]
  exact coordinate_restrict_top_of_eq U.hom f.left (MorphismProperty.Over.w f) p.inv s

/-- Express the restriction formula in arbitrary scalar coordinates on
the global functions of the two charts. -/
theorem scalar_restricted_coordinate {S D : Type u} (f : V ⟶ U) (p : Frame M U) (s : Γ(M, ⊤))
    (d : Γ(V.left, ⊤) → D) (c : Γ(U.left, ⊤) → S) (i : S → D)
    (h : ∀ w : Γ(U.left, ⊤), d (f.left.appTop w) = i (c w))
    (x : S) (hx : c (p.inv.app ⊤ (onSections U.hom M ⊤ s)) = x) :
    d ((restrict M f p).inv.app ⊤ (onSections V.hom M ⊤ s)) = i x :=
  (congrArg d (restrict_inv_section f p s)).trans ((h _).trans (congrArg i hx))

/-- The frame-coordinate formula over an arbitrary open of the base. -/
theorem restrict_inv_section_on (f : V ⟶ U) (p : Frame M U) (W : X.Opens) (s : Γ(M, W)) :
    (restrict M f p).inv.app (V.hom ⁻¹ᵁ W) (onSections V.hom M W s) =
      V.left.presheaf.map (eqToHom (congrArg (fun a : V.left ⟶ X => a ⁻¹ᵁ W)
        (MorphismProperty.Over.w f).symm)).op
        (f.left.app (U.hom ⁻¹ᵁ W) (p.inv.app (U.hom ⁻¹ᵁ W) (onSections U.hom M W s))) := by
  rw [restrict_inv f p]
  exact coordinate_restrict_section_of_eq U.hom f.left (MorphismProperty.Over.w f) p.inv W s

theorem restrict_inv_section_of_coordinate (f : V ⟶ U) (p : Frame M U) (W : X.Opens)
    (s : Γ(M, W)) (a : Γ(X, W))
    (h : p.inv.app (U.hom ⁻¹ᵁ W) (onSections U.hom M W s) = U.hom.app W a) :
    (restrict M f p).inv.app (V.hom ⁻¹ᵁ W) (onSections V.hom M W s) = V.hom.app W a := by
  rw [restrict_inv_section_on f p W s, h]
  exact (ConcreteCategory.congr_hom
    (Scheme.Hom.congr_app (MorphismProperty.Over.w f).symm W) a).symm

end PhilipponEtaleFrameCoordinateRestriction
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open PhilipponTorsorSectionFibers PhilipponZariskiFrameGluingData
open PhilipponEtaleFrameSections PhilipponFrameUnits PhilipponEtaleTorsorZariskiLocal
open PhilipponZariskiTorsorCoordinates PhilipponPullbackSectionMaps

namespace PhilipponZariskiFrameTransition
universe u

theorem unit_of_coordinates {Y : Scheme.{u}} {L : Y.Modules}
    (p q : trivial Y ≅ L) {W : Y.Opens} (hW : W = ⊤)
    (z : Γ(L, W)) (a : (Γ(Y, ⊤))ˣ)
    (hp : p.inv.app W z = (1 : Γ(Y, W)))
    (hq : q.inv.app W z = Y.presheaf.map (eqToHom hW).op a.val) :
    differenceEquiv Y q p = a := by
  subst W
  apply Units.ext
  change q.inv.app ⊤ (p.hom.app ⊤ (1 : Γ(Y, ⊤))) = a.val
  have hz : p.hom.app ⊤ (p.inv.app ⊤ z) = z :=
    ConcreteCategory.congr_hom (congrArg (fun m : L ⟶ L => m.app ⊤) p.inv_hom_id) z
  rw [← hp, hz]
  calc
    _ = _ := hq
    _ = _ := ConcreteCategory.congr_hom (Y.presheaf.map_id (op (⊤ : Y.Opens))) a.val

theorem app_topIso {X : Scheme.{u}} (V : X.Opens) (a : Γ(V.toScheme, ⊤)) :
    V.ι.app V (V.topIso.hom a) = V.toScheme.presheaf.map (eqToHom V.ι_preimage_self).op a := by
  have h : V.topIso.hom ≫ V.ι.app V = V.toScheme.presheaf.map (eqToHom V.ι_preimage_self).op := by
    rw [Scheme.Opens.topIso_hom, Scheme.Opens.ι_app_self, Scheme.Opens.toScheme_presheaf_map,
      ← X.presheaf.map_comp]
    congr 1
  exact ConcreteCategory.congr_hom h a

end PhilipponZariskiFrameTransition

namespace PhilipponZariskiFrameGluingData.ChartFamily
universe u
variable {X : Scheme.{u}} {I : Type u}
variable {A : Torsor (PhilipponKummerSequence.units X)}
variable (C : ChartFamily A I)

/-- The inverse of the chart frame acts on the pullback of a local section
by pulling back its chart coordinate. -/
theorem chart_coordinate {V : X.Opens} {i : I} (h : V ≤ C.U i) (z : C.matching V) :
    (C.chartFrame i).inv.app ((C.U i).ι ⁻¹ᵁ V)
      (onSections (C.U i).ι C.gluedModule V z) = (C.U i).ι.app V (C.evaluate h z) := by
  let f := (C.U i).ι
  let W := f ⁻¹ᵁ V
  let M := C.gluedModule
  let e := (Scheme.Modules.restrictFunctorIsoPullback f).app M
  let η := ((Scheme.Modules.restrictAdjunction f).unit.app M).app V
  have hη : η ≫ e.hom.app W = onSections f M V :=
    congrArg (fun a => Scheme.Modules.Hom.app a V)
      (Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction f)
        (Scheme.Modules.pullbackPushforwardAdjunction f) M)
  have he : e.hom.app W ≫ e.inv.app W = 𝟙 _ :=
    congrArg (fun a => Scheme.Modules.Hom.app a W) e.hom_inv_id
  have hcoord : (e.hom.app W ≫ (C.chartFrame i).inv.app W) = (C.coordinateIso i).hom.app W := by
    change e.hom.app W ≫ e.inv.app W ≫ (C.coordinateIso i).hom.app W = _
    rw [← Category.assoc, he, Category.id_comp]
  change ((onSections f M V) ≫ (C.chartFrame i).inv.app W) z = _
  rw [← hη, Category.assoc, hcoord, comp_apply]
  have hres : η z = C.restrict (f.image_preimage_le V) z :=
    ConcreteCategory.congr_hom (Scheme.Modules.restrictAdjunction_unit_app_app f M V) z
  exact (C.coordinateIso_apply i W (η z)).trans
    ((congrArg (C.evaluate ((C.U i).ι_image_le W)) hres).trans
      (C.evaluate_restrict h (f.image_preimage_le V) z))

/-- The chart coordinate pulled back to an intervening open subscheme. -/
theorem restricted_chart_coordinate {V : X.Opens} {i : I} (h : V ≤ C.U i)
    (z : C.matching V) :
    (PhilipponEtaleFrameSections.restrict C.gluedModule ((opensToEtale X).map (homOfLE h)) (C.chartFrame i)).inv.app
      (V.ι ⁻¹ᵁ V) (onSections V.ι C.gluedModule V z) = V.ι.app V (C.evaluate h z) := by
  exact PhilipponEtaleFrameCoordinateRestriction.restrict_inv_section_of_coordinate
    ((opensToEtale X).map (homOfLE h)) (C.chartFrame i) V z (C.evaluate h z) (C.chart_coordinate h z)

/-- On an open contained in two charts, the chart frames have precisely
the transition unit of the prescribed torsor sections. -/
theorem chart_difference {V : X.Opens} {i j : I} (hi : V ≤ C.U i) (hj : V ≤ C.U j) :
    diff C.gluedModule (openObject V)
        (PhilipponEtaleFrameSections.restrict C.gluedModule ((opensToEtale X).map (homOfLE hi)) (C.chartFrame i))
        (PhilipponEtaleFrameSections.restrict C.gluedModule ((opensToEtale X).map (homOfLE hj)) (C.chartFrame j)) =
      A.D.diff (op (openObject V)) ((sections A).map (homOfLE hi).op (C.s i))
        ((sections A).map (homOfLE hj).op (C.s j)) := by
  let p := PhilipponEtaleFrameSections.restrict C.gluedModule ((opensToEtale X).map (homOfLE hi)) (C.chartFrame i)
  let q := PhilipponEtaleFrameSections.restrict C.gluedModule ((opensToEtale X).map (homOfLE hj)) (C.chartFrame j)
  let a : (Γ(V.toScheme, ⊤))ˣ := Additive.toMul
    (A.D.diff (op (openObject V)) ((sections A).map (homOfLE hi).op (C.s i))
      ((sections A).map (homOfLE hj).op (C.s j)))
  change Additive.ofMul (differenceEquiv V.toScheme q p) = Additive.ofMul a
  apply congrArg Additive.ofMul
  let z := C.extend hi (1 : Γ(X, V))
  refine PhilipponZariskiFrameTransition.unit_of_coordinates p q V.ι_preimage_self
    (onSections V.ι C.gluedModule V z) a ?_ ?_
  · exact (C.restricted_chart_coordinate hi z).trans
      ((congrArg (V.ι.app V) (C.evaluate_extend hi (1 : Γ(X, V)))).trans (map_one (V.ι.app V).hom))
  · calc
      _ = V.ι.app V (C.evaluate hj z) := C.restricted_chart_coordinate hj z
      _ = V.ι.app V (V.topIso.hom a.val) := by
        apply congrArg (V.ι.app V)
        exact (C.evaluate_extend_other hj hi (1 : Γ(X, V))).trans (mul_one _)
      _ = _ := PhilipponZariskiFrameTransition.app_topIso V a.val

end PhilipponZariskiFrameGluingData.ChartFamily
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory Opposite
open PhilipponTorsorPresheafDifference PhilipponTorsorInvariantDescent
open PhilipponTorsorSectionFibers PhilipponTorsorFiberComparison PhilipponPresheafTorsorCompletion

namespace PhilipponTorsorMorphismExtension
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

theorem isLocallyInjective {P Q : Cᵒᵖ ⥤ Type w} (f : P ⟶ Q)
    (h : ∀ U, Nonempty (P.obj U) → Function.Bijective (f.app U)) :
    Presheaf.IsLocallyInjective J f := by
  apply Presheaf.isLocallyInjective_of_injective J f
  intro U p q he
  exact (h U ⟨p⟩).injective he

theorem isLocallySurjective {P Q : Cᵒᵖ ⥤ Type w} (f : P ⟶ Q)
    (hlocal : ∀ U, presence P U ∈ J U)
    (h : ∀ U, Nonempty (P.obj U) → Function.Bijective (f.app U)) :
    Presheaf.IsLocallySurjective J f where
  imageSieve_mem {U} s := by
    refine J.superset_covering ?_ (hlocal U)
    intro V g hv
    exact (h (op V) hv).surjective (Q.map g.op s)

theorem equivalent_of_map {G : Sheaf J AddCommGrpCat.{w}} {A B : Torsor G}
    (f : A.D.P ⟶ B.D.P)
    (hf : ∀ (U : Cᵒᵖ) (p q : A.D.P.obj U), B.D.diff U (f.app U p) (f.app U q) = A.D.diff U p q) :
    Equivalent A B := by
  have hb (U : Cᵒᵖ) : Nonempty (A.D.P.obj U) → Function.Bijective (f.app U) := by
    rintro ⟨p⟩
    exact bijective_of_section (D := A.D) (E := B.D) f U p (A.diff_bijective U p)
      (B.diff_bijective U (f.app U p)) (fun q => hf U q p)
  let A' : Sheaf J (Type w) := ⟨A.D.P, A.isSheaf⟩
  let B' : Sheaf J (Type w) := ⟨B.D.P, B.isSheaf⟩
  let φ : A' ⟶ B' := ⟨f⟩
  let : IsIso φ := (Sheaf.isLocallyBijective_iff_isIso (A := Type w) φ).mp
    ⟨isLocallyInjective f hb, isLocallySurjective f A.locally_nonempty hb⟩
  exact ⟨(sheafToPresheaf J (Type w)).mapIso (asIso φ), hf⟩

variable [J.WEqualsLocallyBijective (Type w)]

/-- A map preserving differences extends along a locally bijective
comparison of section presheaves. -/
theorem exists_extension {G : Sheaf J AddCommGrpCat.{w}} {D E : Difference G.obj}
    {B : Torsor G} (η : D.P ⟶ E.P)
    (hlocal : ∀ U, presence D.P U ∈ J U)
    (hb : ∀ U, Nonempty (D.P.obj U) → Function.Bijective (η.app U))
    (hη : ∀ (U : Cᵒᵖ) (p q : D.P.obj U), E.diff U (η.app U p) (η.app U q) = D.diff U p q)
    (k : D.P ⟶ B.D.P)
    (hk : ∀ (U : Cᵒᵖ) (p q : D.P.obj U), B.D.diff U (k.app U p) (k.app U q) = D.diff U p q) :
    ∃ f : E.P ⟶ B.D.P,
      ∀ (U : Cᵒᵖ) (p q : E.P.obj U), B.D.diff U (f.app U p) (f.app U q) = E.diff U p q := by
  have hw : J.W η := (J.W_iff_isLocallyBijective η).mpr
    ⟨isLocallyInjective η hb, isLocallySurjective η hlocal hb⟩
  obtain ⟨f, hf⟩ := (hw B.D.P B.isSheaf).surjective k
  refine ⟨f, fun U x y => ?_⟩
  let G' : Sheaf J (Type w) := (sheafCompose J (forget AddCommGrpCat.{w})).obj G
  apply (G'.property.isSheafFor _ (hlocal U.unop)).isSeparatedFor.ext
  intro V g hv
  obtain ⟨p, hp⟩ := (hb (op V) hv).surjective (E.P.map g.op x)
  obtain ⟨q, hq⟩ := (hb (op V) hv).surjective (E.P.map g.op y)
  change G.obj.map g.op (B.D.diff U (f.app U x) (f.app U y)) =
    G.obj.map g.op (E.diff U x y)
  have he (t : D.P.obj (op V)) : f.app (op V) (η.app (op V) t) = k.app (op V) t :=
    ConcreteCategory.congr_hom (NatTrans.congr_app hf (op V)) t
  rw [B.D.map_diff, E.map_diff, ← NatTrans.naturality_apply f g.op x,
    ← NatTrans.naturality_apply f g.op y, ← hp, ← hq, he p, he q, hk, hη]

/-- An equivariant map on locally available sections extends to the
associated torsor and determines an equivariant isomorphism. -/
theorem equivalent_of_local_map {G : Sheaf J AddCommGrpCat.{w}} {A B : Torsor G}
    {D : Difference G.obj} (η : D.P ⟶ A.D.P)
    (hlocal : ∀ U, presence D.P U ∈ J U)
    (hb : ∀ U, Nonempty (D.P.obj U) → Function.Bijective (η.app U))
    (hη : ∀ (U : Cᵒᵖ) (p q : D.P.obj U), A.D.diff U (η.app U p) (η.app U q) = D.diff U p q)
    (k : D.P ⟶ B.D.P)
    (hk : ∀ (U : Cᵒᵖ) (p q : D.P.obj U), B.D.diff U (k.app U p) (k.app U q) = D.diff U p q) :
    Equivalent A B := by
  obtain ⟨f, hf⟩ := exists_extension η hlocal hb hη k hk
  exact equivalent_of_map f hf

end PhilipponTorsorMorphismExtension
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory Opposite
open PhilipponTorsorPresheafDifference PhilipponTorsorInvariantDescent
open PhilipponTorsorSectionFibers PhilipponTorsorFiberComparison

namespace PhilipponTorsorCoverComparison
universe u v w z
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J AddCommGrpCat.{w}} {I : Type z} (E : I → C)

private abbrev Anchor (U : C) := Σ i : I, U ⟶ E i

private def Anchor.restrict {U V : C} (a : Anchor E U) (f : V ⟶ U) : Anchor E V :=
  ⟨a.1, f ≫ a.2⟩

/-- Arrows whose source admits a map to a member of the cover. -/
def hitsFamily (U : C) : Sieve U where
  arrows V _ := Nonempty (Anchor E V)
  downward_closed h f := h.map (Anchor.restrict E · f)

variable {E} {A B : Torsor G}
variable (s : ∀ i, A.D.P.obj (op (E i))) (t : ∀ i, B.D.P.obj (op (E i)))

private def atAnchor {U : C} (a : Anchor E U) (x : A.D.P.obj (op U)) : B.D.P.obj (op U) :=
  (B.diff_bijective (op U) (B.D.P.map a.2.op (t a.1))).surjective
    (A.D.diff (op U) x (A.D.P.map a.2.op (s a.1))) |>.choose

private theorem atAnchor_diff {U : C} (a : Anchor E U) (x : A.D.P.obj (op U)) :
    B.D.diff (op U) (atAnchor s t a x) (B.D.P.map a.2.op (t a.1)) =
      A.D.diff (op U) x (A.D.P.map a.2.op (s a.1)) :=
  (B.diff_bijective (op U) (B.D.P.map a.2.op (t a.1))).surjective
    (A.D.diff (op U) x (A.D.P.map a.2.op (s a.1))) |>.choose_spec

private theorem atAnchor_restrict {U V : C} (a : Anchor E U) (f : V ⟶ U) (x : A.D.P.obj (op U)) :
    atAnchor s t (Anchor.restrict E a f) (A.D.P.map f.op x) = B.D.P.map f.op (atAnchor s t a x) := by
  apply (B.diff_bijective (op V) (B.D.P.map (f ≫ a.2).op (t a.1))).injective
  change B.D.diff (op V) (atAnchor s t (Anchor.restrict E a f) (A.D.P.map f.op x))
      (B.D.P.map (f ≫ a.2).op (t a.1)) =
    B.D.diff (op V) (B.D.P.map f.op (atAnchor s t a x)) (B.D.P.map (f ≫ a.2).op (t a.1))
  rw [show B.D.P.map (f ≫ a.2).op (t a.1) =
    B.D.P.map (Anchor.restrict E a f).2.op (t (Anchor.restrict E a f).1) from rfl, atAnchor_diff]
  simp only [Anchor.restrict, op_comp, Functor.map_comp_apply, ← A.D.map_diff, ← B.D.map_diff, atAnchor_diff]

variable (h : ∀ (U : C) (i j : I) (a : U ⟶ E i) (b : U ⟶ E j),
  A.D.diff (op U) (A.D.P.map a.op (s i)) (A.D.P.map b.op (s j)) =
    B.D.diff (op U) (B.D.P.map a.op (t i)) (B.D.P.map b.op (t j)))

include h in
private theorem atAnchor_agree {U : C} (a b : Anchor E U) (x : A.D.P.obj (op U)) :
    atAnchor s t a x = atAnchor s t b x := by
  apply (B.diff_bijective (op U) (B.D.P.map b.2.op (t b.1))).injective
  change B.D.diff (op U) (atAnchor s t a x) (B.D.P.map b.2.op (t b.1)) =
    B.D.diff (op U) (atAnchor s t b x) (B.D.P.map b.2.op (t b.1))
  rw [← B.D.diff_add_diff (op U) (atAnchor s t a x) (B.D.P.map a.2.op (t a.1)),
    atAnchor_diff, atAnchor_diff, ← h U a.1 b.1 a.2 b.2, A.D.diff_add_diff]

private def restricted : Difference G.obj where
  P :=
    { obj U := {x : A.D.P.obj U // Nonempty (Anchor E U.unop)}
      map f := ↾fun x => ⟨A.D.P.map f x.val, x.property.map (Anchor.restrict E · f.unop)⟩
      map_id U := by
        apply ConcreteCategory.hom_ext
        intro x
        exact Subtype.ext (by simp)
      map_comp f g := by
        apply ConcreteCategory.hom_ext
        intro x
        exact Subtype.ext (by simp) }
  diff U x y := A.D.diff U x.val y.val
  diff_add_diff U x y z := A.D.diff_add_diff U x.val y.val z.val
  map_diff f x y := A.D.map_diff f x.val y.val

private def forgetAnchor : (restricted (E := E) (A := A)).P ⟶ A.D.P where
  app _ := ↾Subtype.val
  naturality _ _ _ := rfl

private def compare : (restricted (E := E) (A := A)).P ⟶ B.D.P where
  app _ := ↾fun x => atAnchor s t x.property.some x.val
  naturality U V f := by
    apply ConcreteCategory.hom_ext
    intro x
    let y := (restricted (E := E) (A := A)).P.map f x
    change atAnchor s t y.property.some (A.D.P.map f x.val) =
      B.D.P.map f (atAnchor s t x.property.some x.val)
    exact (atAnchor_agree s t h y.property.some (Anchor.restrict E x.property.some f.unop) _).trans
      (atAnchor_restrict s t x.property.some f.unop x.val)

include h in
/-- Matching transitions on a covering family identify the given torsors. -/
theorem equivalent_of_family [J.WEqualsLocallyBijective (Type w)]
    (hc : ∀ U, hitsFamily E U ∈ J U) : Equivalent A B := by
  refine PhilipponTorsorMorphismExtension.equivalent_of_local_map
    (D := restricted (E := E) (A := A)) forgetAnchor (fun U => ?_) (fun U hu => ?_)
    (fun _ _ _ => rfl) (compare s t h) (fun U x y => ?_)
  · apply J.superset_covering _ (J.intersection_covering (A.locally_nonempty U) (hc U))
    rintro V _ ⟨⟨x⟩, ha⟩
    exact ⟨⟨x, ha⟩⟩
  · obtain ⟨x⟩ := hu
    exact ⟨fun _ _ h => Subtype.ext h, fun y => ⟨⟨y, x.property⟩, rfl⟩⟩
  · let a := x.property.some
    change B.D.diff U (atAnchor s t a x.val) (atAnchor s t y.property.some y.val) =
      A.D.diff U x.val y.val
    rw [atAnchor_agree s t h y.property.some a y.val]
    apply add_right_cancel (b := B.D.diff U (atAnchor s t a y.val) (B.D.P.map a.2.op (t a.1)))
    rw [B.D.diff_add_diff, atAnchor_diff, atAnchor_diff, A.D.diff_add_diff]

end PhilipponTorsorCoverComparison
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open PhilipponTorsorSectionFibers PhilipponTorsorFiberComparison
open PhilipponEtaleFrameTorsor PhilipponEtaleFramePresheaf PhilipponEtaleFrameSections

namespace PhilipponFramePresentationTransport
universe u
variable {X : Scheme.{u}} {M : X.Modules}

/-- An equivariant identification transports a comparison from frames to
the specified target torsor. -/
theorem exists_presentation (P : Presentation M)
    (A : Torsor (PhilipponKummerSequence.units X)) (h : Equivalent P.torsor A) :
    ∃ Q : Presentation M, Q.torsor = A := by
  obtain ⟨e, he⟩ := h
  let η : presheaf M ⟶ A.D.P := P.frames ≫ e.hom
  have hd (U : X.Etaleᵒᵖ) (p q : Frame M U.unop) :
      A.D.diff U (η.app U p) (η.app U q) = diff M U.unop p q :=
    (he U _ _).trans (P.diff_eq U p q)
  have hb (U : X.Etaleᵒᵖ) (hU : Nonempty (Frame M U.unop)) :
      Function.Bijective (η.app U) :=
    (ConcreteCategory.bijective_of_isIso (e.hom.app U)).comp (P.bijective U hU)
  exact ⟨⟨A, η, hd, hb⟩, rfl⟩

end PhilipponFramePresentationTransport
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1250000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open PhilipponTorsorSectionFibers PhilipponTorsorFiberComparison PhilipponTorsorCoverComparison
open PhilipponZariskiFrameGluingData PhilipponZariskiTorsorCoordinates
open PhilipponEtaleTorsorZariskiLocal PhilipponEtaleFrameSections PhilipponEtaleFrameTorsor

namespace PhilipponZariskiFrameGluingData.ChartFamily
universe u
variable {X : Scheme.{u}} {I : Type u}
variable {A : Torsor (PhilipponKummerSequence.units X)}
variable (C : ChartFamily A I)

theorem hitsFamily_cover (hC : ∀ x : X, ∃ i : I, x ∈ C.U i) (W : X.Etale) :
    hitsFamily (fun i => openObject (C.U i)) W ∈ X.smallEtaleTopology W := by
  let V (i : I) := W.hom ⁻¹ᵁ C.U i
  let E (i : I) : X.Etale := Scheme.Etale.mk ((V i).ι ≫ W.hom)
  let f (i : I) : E i ⟶ W := MorphismProperty.Over.homMk (V i).ι rfl
  let g (i : I) : E i ⟶ openObject (C.U i) :=
    MorphismProperty.Over.homMk (W.hom ∣_ (C.U i)) (morphismRestrict_ι W.hom (C.U i))
  have hf : Sieve.ofArrows E f ∈ X.smallEtaleTopology W := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff f).mpr
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨i, hi⟩ := hC (W.hom x)
    exact ⟨i, ⟨x, hi⟩, rfl⟩
  apply X.smallEtaleTopology.superset_covering _ hf
  apply (Sieve.generate_le_iff _ _).mpr
  rintro _ _ ⟨i⟩
  exact ⟨⟨i, g i⟩⟩

private theorem factor_overlap {U V : X.Opens} {W : X.Etale}
    (a : W ⟶ openObject U) (b : W ⟶ openObject V) :
    ∃ k : W ⟶ openObject (U ⊓ V),
      k ≫ (opensToEtale X).map (homOfLE (inf_le_left : U ⊓ V ≤ U)) = a ∧
      k ≫ (opensToEtale X).map (homOfLE (inf_le_right : U ⊓ V ≤ V)) = b := by
  have h (P : X.Opens) (f : W ⟶ openObject P) : Set.range W.hom ⊆ (P : Set X) := by
    rintro y ⟨x, rfl⟩
    have he := (Scheme.Hom.comp_apply f.left P.ι x).symm.trans
      (congrArg (fun m : W.left ⟶ X => m x) (MorphismProperty.Over.w f))
    exact he ▸ (f.left x).property
  let g : W.left ⟶ (U ⊓ V).toScheme := IsOpenImmersion.lift (U ⊓ V).ι W.hom
    (fun y hy => ⟨⟨y, h U a hy, h V b hy⟩, rfl⟩)
  have hg : g ≫ (U ⊓ V).ι = W.hom := IsOpenImmersion.lift_fac _ _ _
  let k : W ⟶ openObject (U ⊓ V) := MorphismProperty.Over.homMk g hg
  have hk (P : X.Opens) (e : U ⊓ V ≤ P) (f : W ⟶ openObject P) :
      k ≫ (opensToEtale X).map (homOfLE e) = f := by
    apply MorphismProperty.Over.Hom.ext
    change g ≫ X.homOfLE e = f.left
    apply (cancel_mono P.ι).mp
    rw [Category.assoc, X.homOfLE_ι, hg]
    exact (MorphismProperty.Over.w f).symm
  exact ⟨k, hk U inf_le_left a, hk V inf_le_right b⟩

theorem chart_difference_etale (W : X.Etale) (i j : I)
    (a : W ⟶ openObject (C.U i)) (b : W ⟶ openObject (C.U j)) :
    diff C.gluedModule W (PhilipponEtaleFrameSections.restrict C.gluedModule a (C.chartFrame i))
        (PhilipponEtaleFrameSections.restrict C.gluedModule b (C.chartFrame j)) =
      A.D.diff (op W) (A.D.P.map a.op (C.s i)) (A.D.P.map b.op (C.s j)) := by
  obtain ⟨k, ha, hb⟩ := factor_overlap a b
  let U := C.U i ⊓ C.U j
  let l : openObject U ⟶ openObject (C.U i) := (opensToEtale X).map (homOfLE inf_le_left)
  let r : openObject U ⟶ openObject (C.U j) := (opensToEtale X).map (homOfLE inf_le_right)
  have h := congrArg ((PhilipponKummerSequence.units X).obj.map k.op)
    (C.chart_difference (V := U) (i := i) (j := j) inf_le_left inf_le_right)
  change (PhilipponKummerSequence.units X).obj.map k.op
    (diff C.gluedModule (openObject U) (PhilipponEtaleFrameSections.restrict C.gluedModule l (C.chartFrame i))
      (PhilipponEtaleFrameSections.restrict C.gluedModule r (C.chartFrame j))) =
    (PhilipponKummerSequence.units X).obj.map k.op
      (A.D.diff (op (openObject U)) (A.D.P.map l.op (C.s i)) (A.D.P.map r.op (C.s j))) at h
  rw [diff_restrict, A.D.map_diff, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
    ← op_comp, ← op_comp] at h
  have h₁ : PhilipponEtaleFrameSections.restrict C.gluedModule k (PhilipponEtaleFrameSections.restrict C.gluedModule l (C.chartFrame i)) =
      PhilipponEtaleFrameSections.restrict C.gluedModule a (C.chartFrame i) := by
    change (PhilipponEtaleFramePresheaf.presheaf C.gluedModule).map k.op
      ((PhilipponEtaleFramePresheaf.presheaf C.gluedModule).map l.op (C.chartFrame i)) = _
    rw [← Functor.map_comp_apply, ← op_comp]
    exact congrArg (fun f => PhilipponEtaleFrameSections.restrict C.gluedModule f (C.chartFrame i)) ha
  have h₂ : PhilipponEtaleFrameSections.restrict C.gluedModule k (PhilipponEtaleFrameSections.restrict C.gluedModule r (C.chartFrame j)) =
      PhilipponEtaleFrameSections.restrict C.gluedModule b (C.chartFrame j) := by
    change (PhilipponEtaleFramePresheaf.presheaf C.gluedModule).map k.op
      ((PhilipponEtaleFramePresheaf.presheaf C.gluedModule).map r.op (C.chartFrame j)) = _
    rw [← Functor.map_comp_apply, ← op_comp]
    exact congrArg (fun f => PhilipponEtaleFrameSections.restrict C.gluedModule f (C.chartFrame j)) hb
  rw [h₁, h₂] at h
  exact h.trans (congrArg₂ (A.D.diff (op W))
    (congrArg (fun f => A.D.P.map f.op (C.s i)) ha)
    (congrArg (fun f => A.D.P.map f.op (C.s j)) hb))

theorem presents (hC : ∀ x : X, ∃ i : I, x ∈ C.U i) :
    ∃ P : Presentation C.gluedModule, P.torsor = A := by
  obtain ⟨P⟩ := nonempty_presentation C.gluedModule (C.invertible hC)
  let t (i : I) := P.frames.app (op (openObject (C.U i))) (C.chartFrame i)
  have h : Equivalent P.torsor A := by
    refine equivalent_of_family t C.s (fun W i j a b => ?_) (C.hitsFamily_cover hC)
    have ha : P.torsor.D.P.map a.op (t i) = P.frames.app (op W)
        (PhilipponEtaleFrameSections.restrict C.gluedModule a (C.chartFrame i)) :=
      (NatTrans.naturality_apply P.frames a.op (C.chartFrame i)).symm
    have hb : P.torsor.D.P.map b.op (t j) = P.frames.app (op W)
        (PhilipponEtaleFrameSections.restrict C.gluedModule b (C.chartFrame j)) :=
      (NatTrans.naturality_apply P.frames b.op (C.chartFrame j)).symm
    rw [ha, hb, P.diff_eq]
    exact C.chart_difference_etale W i j a b
  exact PhilipponFramePresentationTransport.exists_presentation P A h

end PhilipponZariskiFrameGluingData.ChartFamily

universe u

/-- A Zariski-locally trivial units torsor is the frame torsor of a line bundle. -/
theorem PhilipponZariskiTorsorEffectivity.exists_presentation {X : Scheme.{u}}
    (A : Torsor (PhilipponKummerSequence.units X))
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ Nonempty (A.D.P.obj (op (openObject U)))) :
    ∃ (M : X.Modules) (_ : Scheme.Modules.IsInvertible M) (P : Presentation M), P.torsor = A := by
  choose U hx s using h
  let C : ChartFamily A X := ⟨U, fun x => (s x).some⟩
  have hC (x : X) : ∃ i : X, x ∈ C.U i := ⟨x, hx x⟩
  obtain ⟨P, hP⟩ := C.presents hC
  exact ⟨C.gluedModule, C.invertible hC, P, hP⟩
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MonoidalCategory
open PhilipponTorsorSectionFibers PhilipponEtaleFrameTorsor PhilipponEtaleFrameSections
open PhilipponTensorFrames
universe u
open Opposite

theorem solution (X : Scheme.{u}) (A : Torsor (PhilipponKummerSequence.units X))
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (A.D.P.obj (op (Scheme.Etale.mk U.ι)))) :
    ∃ (M : X.Modules) (_ : Scheme.Modules.IsInvertible M)
      (P : Presentation M), P.torsor = A := by
  exact PhilipponZariskiTorsorEffectivity.exists_presentation A h

#print axioms solution
