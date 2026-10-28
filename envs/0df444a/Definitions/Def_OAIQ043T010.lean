-- Prove2me | Definitions.Def_OAIQ043T010
-- name    : OAIQ043T010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T10:06:23.849235+00:00
-- url     : https://prove2.me/theorems/49025b2f-c7b5-48bf-8b34-ad4f22726279
-- title:
--   Definitions bundle OAIQ043T010 of the split of OpenAI, Thomason Model Structures in Every Strict Higher Dimension (result family 317)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Thomason.main` and `OAI.Thomason.nerveDetection_allDimensions`, carved from OpenAI's openai/math development (OpenAI, *Thomason Model Structures in Every Strict Higher Dimension (result family 317)*, OpenAI Math Release, September 25, 2026, result family 317, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 445 declarations of OpenAI's Lean: 131 definitions, 9 inductive types or structures, 1 instance and 304 theorems. The definitions and types are `OAI.Thomason.DirectedComplex.CylinderTables.cross`, `OAI.Thomason.DirectedComplex.CylinderTables.crossingProfile`, `OAI.Thomason.DirectedComplex.CylinderTables.label`, `OAI.Thomason.DirectedComplex.CylinderTables.leftProfile`, `OAI.Thomason.DirectedComplex.CylinderTables.leftProfileRow`, `OAI.Thomason.DirectedComplex.CylinderTables.profileEdge`, `OAI.Thomason.DirectedComplex.CylinderTables.project`, `OAI.Thomason.DirectedComplex.CylinderTables.rightProfile`, `OAI.Thomason.DirectedComplex.CylinderTables.rightProfileRow`, `OAI.Thomason.DirectedComplex.CylinderTables.side`, `OAI.Thomason.DirectedComplex.CylinderTables.tableSandwich`, `OAI.Thomason.DirectedComplex.CylinderTables.twoLeft`, `OAI.Thomason.DirectedComplex.CylinderTables.twoMiddle`, `OAI.Thomason.DirectedComplex.CylinderTables.twoRight`, `OAI.Thomason.DirectedComplex.RankedAtoms`, `OAI.Thomason.DirectedComplex.RankedAtoms.AtomPasting`, `OAI.Thomason.DirectedComplex.RankedAtoms.AtomPath`, `OAI.Thomason.DirectedComplex.RankedAtoms.BoundedPasting`, `OAI.Thomason.DirectedComplex.RankedAtoms.HasAdjacentExchange`, `OAI.Thomason.DirectedComplex.RankedAtoms.OrderedWhisker`, `OAI.Thomason.DirectedComplex.RankedAtoms.TopGenerator`, `OAI.Thomason.DirectedComplex.RankedAtoms.TopPasting`, `OAI.Thomason.DirectedComplex.RankedAtoms.WhiskerFaithful`, `OAI.Thomason.DirectedComplex.RankedAtoms.basis`, `OAI.Thomason.DirectedComplex.RankedAtoms.cut`, `OAI.Thomason.DirectedComplex.RankedAtoms.mass`, `OAI.Thomason.DirectedComplex.RankedAtoms.orderRank`, `OAI.Thomason.DirectedComplex.RankedAtoms.rankedAtomsDecidableEq`, `OAI.Thomason.DirectedComplex.RankedAtoms.transport`, `OAI.Thomason.DirectedComplex.cylinderFunctor`, `OAI.Thomason.GlobeComplex.fromSimplexOne`, `OAI.Thomason.GlobeComplex.fromSimplexZero`, `OAI.Thomason.GlobeComplex.simplexOneFunctor`, `OAI.Thomason.GlobeComplex.simplexOneIso`, `OAI.Thomason.GlobeComplex.simplexZeroIso`, `OAI.Thomason.GlobeComplex.toSimplexOne`, `OAI.Thomason.GlobeComplex.toSimplexZero`, `OAI.Thomason.GlobeComplex.topOneArrow`, `OAI.Thomason.GrayRecursive.CellWeight`, `OAI.Thomason.GrayRecursive.CellWeight.hom` and 100 more.
--
--   **Sources.** They come from these modules of lean/OAI/CategoryTheory/Thomason, in whole or in part: `Thomason_BoundedCylinders`, `Thomason_CylinderAssociativity`, `Thomason_CylinderFaces`, `Thomason_CylinderInterchange`, `Thomason_CylinderProfiles`, `Thomason_CylinderWeights`, `Thomason_EdgeComparison`, `Thomason_FiniteGluing`, `Thomason_GlobularGeneration`, `Thomason_IntervalCategories`, `Thomason_LayeredWhiskers`, `Thomason_PartialPrisms`, `Thomason_PastingInterchange`, `Thomason_RankedAtoms`, `Thomason_RankedExchange`, `Thomason_RectangleComposition`, `Thomason_StandardComparison`, `Thomason_StationaryCylinders`, `Thomason_TopSequences`.
--
--   **Imports.** It imports the published bundle `Def_ThomasonModelStructures`; the bundles `OAIQ043T008` and `OAIQ043T009` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ043T012`.
-- source:
--   OpenAI, Thomason Model Structures in Every Strict Higher Dimension (result family 317), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 317; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Thomason-Model-Structures-in-Every-Strict-Higher-Dimension-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/CategoryTheory/Thomason at commit adc7f12

import Mathlib
import Definitions.Def_ThomasonModelStructures
import Definitions.Def_OAIQ043T008
import Definitions.Def_OAIQ043T009

section
-- module Solutions.OAIQ043_TH.Thomason_PartialPrisms
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partial Prisms. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.PartialHom
open Table OmegaCategory
variable {K : DirectedComplex.{u}} {L : DirectedComplex.{v}} {n : ℕ}

lemma ofHom_table (f : Hom K L) (x : Table K) :
    (ofHom f n).table x = truncate n false (f.table x) := by
  ext p b
  simp only [table,ofHom,truncate_row,Hom.table]

lemma ofHom_image (f : Hom K L) (x : Table K) :
    (ofHom f n).image x = (truncationUnit n L.nu).map (f.table x) := by
  change (truncationUnit n L.nu).map ((ofHom f n).table x) = _
  rw [ofHom_table]
  exact ((truncationUnit n L.nu).map_source n (f.table x)).trans
    ((truncation n L.nu).property _)

end Thomason.DirectedComplex.PartialHom

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_GlobularGeneration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Globular Generation. -/

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open DirectedComplex DirectedComplex.Table GlobeComplex

lemma generated (n : ℕ) (P : Table (K.{u} n) → Prop)
    (hend : ∀ a x, P (atEnd a x)) (hvertical : ∀ x, P (verticalTable x))
    (hcomp : ∀ k s t (h : truncate k true s = truncate k false t),
      P s → P t → P (DirectedComplex.Table.comp k s t h)) : ∀ x, P x := by
  induction n with
  | zero =>
    intro x
    rcases table_zero_cases x with ⟨a,he⟩ | he
    · rw [he]; exact hend a (project x)
    · rw [he]; exact hvertical (topTable 0)
  | succ n ih =>
    intro x
    rcases table_cases x with ⟨a,he⟩ | ⟨a,he⟩ | hd
    · rw [he]; exact hend a (project x)
    · rw [he]; exact hvertical _
    · rw [← up_down x hd]
      apply ih (fun y => P (up y))
      · intro a y
        cases a
        · rw [up_endpoint_false]
          exact hcomp 0 _ _ _ (hvertical _) (hend true _)
        · rw [up_endpoint_true]
          exact hcomp 0 _ _ _ (hend false _) (hvertical _)
      · intro y
        rw [up_vertical]
        exact hvertical _
      · intro k s t h hs ht
        rw [up_comp s t h (up_composable h)]
        exact hcomp (k+1) _ _ _ hs ht

end Thomason.GrayRecursive

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_RectangleComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rectangle Composition. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory
open CategoryTheory

def homCompose {X : OmegaCategory.{u}} {Y : OmegaCategory.{v}} {a b c : Y.Cell}
    (F : Functor X (Y.homCategory a b)) (G : Functor X (Y.homCategory b c)) :
    Functor X (Y.homCategory a c) where
  map x := ⟨Y.join 0 (F.map x).val (G.map x).val, by
    have h := (F.map x).property.2.trans (G.map x).property.1.symm
    exact ⟨(Y.join_source_le 0 0 _ _ le_rfl h).trans (F.map x).property.1,
      (Y.join_target_le 0 0 _ _ le_rfl h).trans (G.map x).property.2⟩⟩
  map_source k x := Subtype.ext (by
    have h := (F.map x).property.2.trans (G.map x).property.1.symm
    change Y.join 0 (F.map (X.source k x)).val (G.map (X.source k x)).val =
      Y.source (k+1) (Y.join 0 (F.map x).val (G.map x).val)
    rw [F.map_source, G.map_source, Y.join_source_gt (k+1) 0 _ _ (by omega) h]
    rfl)
  map_target k x := Subtype.ext (by
    have h := (F.map x).property.2.trans (G.map x).property.1.symm
    change Y.join 0 (F.map (X.target k x)).val (G.map (X.target k x)).val =
      Y.target (k+1) (Y.join 0 (F.map x).val (G.map x).val)
    rw [F.map_target, G.map_target, Y.join_target_gt (k+1) 0 _ _ (by omega) h]
    rfl)
  map_comp k x y h h' := Subtype.ext (by
    have hfx := F.map_composable h
    have hgx := G.map_composable h
    have h₁ := (F.map x).property.2.trans (G.map x).property.1.symm
    have h₂ := (F.map y).property.2.trans (G.map y).property.1.symm
    change Y.join 0 (F.map (X.comp k x y h)).val (G.map (X.comp k x y h)).val =
      Y.comp (k+1) _ _ _
    rw [F.map_comp _ _ _ h hfx, G.map_comp _ _ _ h hgx]
    change Y.join 0 (Y.comp (k+1) _ _ (congrArg Subtype.val hfx))
      (Y.comp (k+1) _ _ (congrArg Subtype.val hgx)) = Y.comp (k+1) _ _ _
    rw [← Y.join_eq (k+1) _ _ (congrArg Subtype.val hfx),
      ← Y.join_eq (k+1) _ _ (congrArg Subtype.val hgx)]
    exact (Y.join_interchange 0 (k+1) (by omega) _ _ _ _
      (congrArg Subtype.val hfx) (congrArg Subtype.val hgx) h₁ h₂).trans
      (Y.join_eq (k+1) _ _ _))

@[simp] lemma homCompose_map {X : OmegaCategory.{u}} {Y : OmegaCategory.{v}} {a b c : Y.Cell}
    (F : Functor X (Y.homCategory a b)) (G : Functor X (Y.homCategory b c)) (x : X.Cell) :
    ((homCompose F G).map x).val = Y.join 0 (F.map x).val (G.map x).val := rfl

def constantAt (X : OmegaCategory.{u}) {Y : OmegaCategory.{v}} (a : Y.Cell)
    (ha : Y.source 0 a = a) : Functor X Y where
  map _ := a
  map_source k _ := (Y.source_fixed_upwards (Nat.zero_le k) ha).symm
  map_target k _ := (Y.target_eq_self_of_source_eq_self
    (Y.source_fixed_upwards (Nat.zero_le k) ha)).symm
  map_comp k _ _ _ h' := (Y.comp_of_left_source_fixed k a a h'
    (Y.source_fixed_upwards (Nat.zero_le _) ha)).symm

def constantHom (X : OmegaCategory.{u}) {Y : OmegaCategory.{v}} {a b : Y.Cell}
    (f : Y.Cell) (hf : Y.source 1 f = f) (hs : Y.source 0 f = a) (ht : Y.target 0 f = b) :
    Functor X (Y.homCategory a b) := constantAt X ⟨f,hs,ht⟩ (Subtype.ext hf)

def homCast {X : OmegaCategory.{u}} {Y : OmegaCategory.{v}} {a b c d : Y.Cell}
    (F : Functor X (Y.homCategory a b)) (hac : a = c) (hbd : b = d) :
    Functor X (Y.homCategory c d) where
  map x := ⟨(F.map x).val, (F.map x).property.1.trans hac, (F.map x).property.2.trans hbd⟩
  map_source k x := Subtype.ext (congrArg (fun z : (Y.homCategory a b).Cell => z.val) (F.map_source k x))
  map_target k x := Subtype.ext (congrArg (fun z : (Y.homCategory a b).Cell => z.val) (F.map_target k x))
  map_comp k x y h _ := Subtype.ext
    (congrArg (fun z : (Y.homCategory a b).Cell => z.val) (F.map_comp k x y h (F.map_composable h)))

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex

lemma globe_zero_unique (x : Table (complex.{u} 0)) : x = topTable 0 := by
  obtain ⟨p,a,hp,he⟩ := table_classification x
  have hp0 : p = 0 := by omega
  subst p
  rw [he, ← face_nu]
  exact (complex 0).nu.face_of_fixed (topTable_bounded 0) le_rfl a

lemma globe_one_cases (x : Table (complex.{u} 1)) :
    (∃ a, x = vertex 0 a) ∨ x = topTable 1 := by
  rcases globe_succ_cases 0 x with h | ⟨x,rfl⟩
  · exact Or.inl h
  · right
    rw [globe_zero_unique x, suspendTable_top]

def zeroCylinderMap : OmegaCategory.Functor (complex.{u} 1).nu (K.{u} 0).nu :=
  GlobeComplex.lift (verticalTable (topTable 0))
    (vertical_fixed _ (topTable_bounded 0))

@[simp] lemma zeroCylinderMap_top :
    zeroCylinderMap.{u}.map (topTable 1) = verticalTable (topTable 0) :=
  lift_top _ _

@[simp] lemma zeroCylinderMap_vertex (a : Bool) :
    zeroCylinderMap.{u}.map (vertex 0 a) = atEnd a (topTable 0) := by
  rw [vertex, ← face_nu]
  erw [zeroCylinderMap.map_face, zeroCylinderMap_top]
  have hf : (K.{u} 0).nu.face 0 a (verticalTable (topTable 0)) =
      truncate 0 a (verticalTable (topTable 0)) := by cases a <;> rfl
  rw [hf]
  apply DirectedComplex.Table.ext
  funext p b
  cases p with
  | zero => cases a <;> simp [truncate_row, verticalTable, verticalRow,
      atEnd, Hom.table, cylinderEndpoint, cylinderEndpointMap, topTable, topRow_eq]
  | succ p => cases a <;> simp [truncate_row, atEnd, Hom.table,
      cylinderEndpoint, cylinderEndpointMap, topTable, topRow_gt _ _ _ (show 0 < p+1 by omega)] <;> rfl

lemma zeroCylinderMap_bijective : Function.Bijective zeroCylinderMap.{u}.map := by
  constructor
  · intro s t h
    have hs := congrArg (fun x => intervalLabel x false) h
    have ht := congrArg (fun x => intervalLabel x true) h
    rcases globe_one_cases s with ⟨a,rfl⟩ | rfl <;>
      rcases globe_one_cases t with ⟨b,rfl⟩ | rfl
    · simp only [zeroCylinderMap_vertex, intervalLabel_end] at hs ht
      have hab : a = b := by cases a <;> cases b <;> simp_all
      rw [hab]
    · exfalso
      cases a
      · simp only [zeroCylinderMap_vertex, zeroCylinderMap_top, intervalLabel_end,
          intervalLabel_vertical, Bool.false_eq_true, ite_false, ite_true, zero_ne_one] at ht
      · simp only [zeroCylinderMap_vertex, zeroCylinderMap_top, intervalLabel_end,
          intervalLabel_vertical, Bool.false_eq_true, ite_false, ite_true, one_ne_zero] at hs
    · exfalso
      cases b
      · simp only [zeroCylinderMap_vertex, zeroCylinderMap_top, intervalLabel_end,
          intervalLabel_vertical, Bool.false_eq_true, ite_false, ite_true, one_ne_zero] at ht
      · simp only [zeroCylinderMap_vertex, zeroCylinderMap_top, intervalLabel_end,
          intervalLabel_vertical, Bool.false_eq_true, ite_false, ite_true, zero_ne_one] at hs
    · rfl
  · intro t
    rcases table_zero_cases t with ⟨a,he⟩ | he
    · exact ⟨vertex 0 a, (zeroCylinderMap_vertex a).trans
        ((congrArg (atEnd a) (globe_zero_unique (project t))).symm.trans he.symm)⟩
    · exact ⟨topTable 1, zeroCylinderMap_top.trans he.symm⟩

def zeroCylinderIso : (complex.{u} 1).nu ≅ (K.{u} 0).nu :=
  OmegaCategory.isoOfBijective zeroCylinderMap zeroCylinderMap_bijective

def zeroCylinderLift {Y : OmegaCategory.{v}} (y : Y.Cell) (hy : Y.source 1 y = y) :
    OmegaCategory.Functor (K.{u} 0).nu Y :=
  OmegaCategory.Functor.comp zeroCylinderIso.inv (GlobeComplex.lift y hy)

@[simp] lemma zeroCylinderLift_vertical {Y : OmegaCategory.{v}} (y : Y.Cell)
    (hy : Y.source 1 y = y) :
    (zeroCylinderLift.{u,v} y hy).map (verticalTable (topTable 0)) = y := by
  have hi : zeroCylinderIso.{u}.inv.map (verticalTable (topTable 0)) = topTable 1 := by
    rw [← zeroCylinderMap_top]
    exact congrArg (fun F : OmegaCategory.Functor (complex 1).nu (complex 1).nu =>
      F.map (topTable 1)) zeroCylinderIso.hom_inv_id
  change (GlobeComplex.lift y hy).map _ = y
  rw [hi, lift_top]

@[simp] lemma zeroCylinderLift_endpoint {Y : OmegaCategory.{v}} (y : Y.Cell)
    (hy : Y.source 1 y = y) (a : Bool) (x : Table (complex.{u} 0)) :
    (zeroCylinderLift y hy).map (atEnd a x) = Y.face 0 a y := by
  rw [globe_zero_unique x]
  have hi : zeroCylinderIso.{u}.inv.map (atEnd a (topTable 0)) = vertex 0 a := by
    rw [← zeroCylinderMap_vertex]
    exact congrArg (fun F : OmegaCategory.Functor (complex 1).nu (complex 1).nu =>
      F.map (vertex 0 a)) zeroCylinderIso.hom_inv_id
  change (GlobeComplex.lift y hy).map _ = _
  rw [hi]
  rw [vertex, ← face_nu]
  erw [(GlobeComplex.lift y hy).map_face, lift_top]

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

def IntervalMatching {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) : Prop :=
  ∀ x, F.map (atEnd true x) = G.map (atEnd false x)

structure IntervalComposition (n : ℕ) where
  compose : ∀ {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y), IntervalMatching F G →
    OmegaCategory.Functor (K.{u} n).nu Y
  endpoint : ∀ {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : IntervalMatching F G) (a : Bool) x,
    (compose F G h).map (atEnd a x) = if a then G.map (atEnd true x) else F.map (atEnd false x)

namespace RectangleDiagram
variable {n : ℕ} {Y : OmegaCategory.{v}}
    (D E : RectangleDiagram.{u,v} n Y)
    (h : ∀ x, (D.ends true).map x = (E.ends false).map x)

include h in
lemma seam_edge (a : Bool) : Y.target 0 (D.edge a) = Y.source 0 (E.edge a) :=
  (D.edge_target a).trans ((h _).trans (E.edge_source a).symm)

lemma edge_end_matching (D : RectangleDiagram.{u,v} n Y) (x : Table (complex.{u} n)) :
    Y.target 0 (D.edge false) = Y.source 0 ((D.ends true).map (suspendTable x)) := by
  erw [D.edge_target, ← (D.ends true).map_source]
  exact congrArg (D.ends true).map (suspend_truncate_zero false x).symm

lemma end_edge_matching (D : RectangleDiagram.{u,v} n Y) (x : Table (complex.{u} n)) :
    Y.target 0 ((D.ends false).map (suspendTable x)) = Y.source 0 (D.edge true) := by
  erw [D.edge_source, ← (D.ends false).map_target]
  exact congrArg (D.ends false).map (suspend_truncate_zero true x)

def concatDiagonalOne : OmegaCategory.Functor (K.{u} n).nu
    (Y.homCategory ((D.ends false).map (vertex n false)) ((E.ends true).map (vertex n true))) :=
  homCompose (constantHom (K n).nu (D.edge false) (D.edge_fixed false)
    (D.edge_source false) ((D.edge_target false).trans (h _))) E.diagonal

def concatDiagonalTwo : OmegaCategory.Functor (K.{u} n).nu
    (Y.homCategory ((D.ends false).map (vertex n false)) ((E.ends true).map (vertex n true))) :=
  homCompose D.diagonal (constantHom (K n).nu (E.edge true) (E.edge_fixed true)
    ((E.edge_source true).trans (h _).symm) (E.edge_target true))

lemma concatDiagonal_matching : IntervalMatching (D.concatDiagonalOne E h) (D.concatDiagonalTwo E h) := by
  intro x
  apply Subtype.ext
  change Y.join 0 (D.edge false) (E.diagonal.map (atEnd true x)).val =
    Y.join 0 (D.diagonal.map (atEnd false x)).val (E.edge true)
  erw [E.right, D.left, h]
  exact (Y.join_assoc 0 _ _ _ (by
    erw [← h]
    exact D.edge_end_matching x) (E.end_edge_matching x)).symm

def concat (I : IntervalComposition.{u,v} n) : RectangleDiagram.{u,v} n Y where
  ends a := if a then E.ends true else D.ends false
  edge a := Y.join 0 (D.edge a) (E.edge a)
  edge_fixed a := by
    rw [Y.join_source_gt 1 0 _ _ (by omega) (D.seam_edge E h a), D.edge_fixed, E.edge_fixed]
  edge_source a := by
    exact (Y.join_source_le 0 0 _ _ le_rfl (D.seam_edge E h a)).trans (D.edge_source a)
  edge_target a := by
    exact (Y.join_target_le 0 0 _ _ le_rfl (D.seam_edge E h a)).trans (E.edge_target a)
  diagonal := I.compose (D.concatDiagonalOne E h) (D.concatDiagonalTwo E h) (D.concatDiagonal_matching E h)
  left x := by
    have he := congrArg Subtype.val (I.endpoint (D.concatDiagonalOne E h)
      (D.concatDiagonalTwo E h) (D.concatDiagonal_matching E h) false x)
    simp only [Bool.false_eq_true, ite_false] at he
    change _ = Y.join 0 (Y.join 0 (D.edge false) (E.edge false)) ((E.ends true).map (suspendTable x))
    rw [he]
    change Y.join 0 (D.edge false) (E.diagonal.map (atEnd false x)).val = _
    rw [E.left]
    exact (Y.join_assoc 0 _ _ _ (D.seam_edge E h false) (E.edge_end_matching x)).symm
  right x := by
    have he := congrArg Subtype.val (I.endpoint (D.concatDiagonalOne E h)
      (D.concatDiagonalTwo E h) (D.concatDiagonal_matching E h) true x)
    simp only [ite_true] at he
    change _ = Y.join 0 ((D.ends false).map (suspendTable x)) (Y.join 0 (D.edge true) (E.edge true))
    rw [he]
    change Y.join 0 (D.diagonal.map (atEnd true x)).val (E.edge true) = _
    rw [D.right]
    exact Y.join_assoc 0 _ _ _ (D.end_edge_matching x) (D.seam_edge E h true)

end RectangleDiagram

namespace IntervalComposition

def zero : IntervalComposition.{u,v} 0 where
  compose {Y} F G h :=
    zeroCylinderLift (Y.join 0 (F.map (verticalTable (topTable 0))) (G.map (verticalTable (topTable 0)))) (by
      have hm : Y.target 0 (F.map (verticalTable (topTable 0))) =
          Y.source 0 (G.map (verticalTable (topTable 0))) := by
        erw [← F.map_target, ← G.map_source]
        have ht := zeroCylinderMap.map_target 0 (topTable 1)
        have hs := zeroCylinderMap.map_source 0 (topTable 1)
        change zeroCylinderMap.map (vertex 0 true) = _ at ht
        change zeroCylinderMap.map (vertex 0 false) = _ at hs
        rw [zeroCylinderMap_vertex, zeroCylinderMap_top] at ht hs
        rw [← ht, ← hs]
        exact h _
      erw [Y.join_source_gt 1 0 _ _ (by omega) hm, ← F.map_source, ← G.map_source]
      change Y.join 0 (F.map (truncate 1 false (verticalTable (topTable 0))))
        (G.map (truncate 1 false (verticalTable (topTable 0)))) = _
      rw [vertical_fixed _ (topTable_bounded 0)])
  endpoint {Y} F G h a x := by
    rw [zeroCylinderLift_endpoint]
    have ht := zeroCylinderMap.map_target 0 (topTable 1)
    have hs := zeroCylinderMap.map_source 0 (topTable 1)
    change zeroCylinderMap.map (vertex 0 true) = _ at ht
    change zeroCylinderMap.map (vertex 0 false) = _ at hs
    rw [zeroCylinderMap_vertex, zeroCylinderMap_top] at ht hs
    have hm : Y.target 0 (F.map (verticalTable (topTable 0))) =
        Y.source 0 (G.map (verticalTable (topTable 0))) := by
      erw [← F.map_target, ← G.map_source]
      rw [← ht, ← hs]; exact h _
    rw [globe_zero_unique x]
    cases a
    · change Y.source 0 _ = _
      erw [Y.join_source_le 0 0 _ _ le_rfl hm, ← F.map_source]
      exact congrArg F.map hs.symm
    · change Y.target 0 _ = _
      erw [Y.join_target_le 0 0 _ _ le_rfl hm, ← G.map_target]
      exact congrArg G.map ht.symm

def succ {n : ℕ} (I : IntervalComposition.{u,v} n) : IntervalComposition.{u,v} (n+1) where
  compose F G h := ((rectangleDiagramOfFunctor F).concat (rectangleDiagramOfFunctor G) h I).lift
  endpoint F G h a x := by
    rw [RectangleDiagram.lift_endpoint]
    cases a <;> rfl

end IntervalComposition

def intervalComposition : (n : ℕ) → IntervalComposition.{u,v} n
  | 0 => IntervalComposition.zero
  | n+1 => (intervalComposition n).succ

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

namespace RectangleDiagram
variable {n : ℕ} {Y : OmegaCategory.{v}} {Z : OmegaCategory.{w}}

def map (D : RectangleDiagram.{u,v} n Y) (P : OmegaCategory.Functor Y Z) :
    RectangleDiagram.{u,w} n Z where
  ends a := OmegaCategory.Functor.comp (D.ends a) P
  edge a := P.map (D.edge a)
  edge_fixed a := by rw [← P.map_source, D.edge_fixed]
  edge_source a := by rw [← P.map_source, D.edge_source]; rfl
  edge_target a := by rw [← P.map_target, D.edge_target]; rfl
  diagonal := OmegaCategory.Functor.comp D.diagonal
    (P.homMap ((D.ends false).map (vertex n false)) ((D.ends true).map (vertex n true)))
  left x := by
    change P.map (D.diagonal.map (atEnd false x)).val = _
    rw [D.left, P.map_join _ _ _ (D.edge_end_matching x)]
    rfl
  right x := by
    change P.map (D.diagonal.map (atEnd true x)).val = _
    rw [D.right, P.map_join _ _ _ (D.end_edge_matching x)]
    rfl

variable (D E : RectangleDiagram.{u,v} n Y)
    (h : ∀ x, (D.ends true).map x = (E.ends false).map x) (P : OmegaCategory.Functor Y Z)

lemma map_concatDiagonalOne :
    OmegaCategory.Functor.comp (D.concatDiagonalOne E h)
      (P.homMap ((D.ends false).map (vertex n false)) ((E.ends true).map (vertex n true))) =
    (D.map P).concatDiagonalOne (E.map P) (fun x => congrArg P.map (h x)) := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change P.map (Y.join 0 (D.edge false) (E.diagonal.map x).val) =
    Z.join 0 (P.map (D.edge false)) (P.map (E.diagonal.map x).val)
  exact P.map_join 0 _ _ ((D.edge_target false).trans ((h _).trans (E.diagonal.map x).property.1.symm))

lemma map_concatDiagonalTwo :
    OmegaCategory.Functor.comp (D.concatDiagonalTwo E h)
      (P.homMap ((D.ends false).map (vertex n false)) ((E.ends true).map (vertex n true))) =
    (D.map P).concatDiagonalTwo (E.map P) (fun x => congrArg P.map (h x)) := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change P.map (Y.join 0 (D.diagonal.map x).val (E.edge true)) =
    Z.join 0 (P.map (D.diagonal.map x).val) (P.map (E.edge true))
  exact P.map_join 0 _ _ ((D.diagonal.map x).property.2.trans ((h _).trans (E.edge_source true).symm))

end RectangleDiagram

abbrev concatInterval {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : IntervalMatching F G) :=
  (intervalComposition n).compose F G h

@[simp] lemma concatInterval_endpoint {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : IntervalMatching F G) (a : Bool) x :
    (concatInterval F G h).map (atEnd a x) = if a then G.map (atEnd true x) else F.map (atEnd false x) :=
  (intervalComposition n).endpoint F G h a x

@[simp] lemma concatInterval_zero_vertical {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} 0).nu Y) (h : IntervalMatching F G) :
    (concatInterval F G h).map (verticalTable (topTable 0)) =
      Y.join 0 (F.map (verticalTable (topTable 0))) (G.map (verticalTable (topTable 0))) :=
  zeroCylinderLift_vertical _ _

@[simp] lemma concatInterval_succ_edge {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y) (h : IntervalMatching F G) (a : Bool) :
    (concatInterval F G h).map (verticalTable (vertex n a)) =
      Y.join 0 (F.map (verticalTable (vertex n a))) (G.map (verticalTable (vertex n a))) :=
  RectangleDiagram.lift_edge _ a

lemma concatInterval_succ_up {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y) (h : IntervalMatching F G) (x : Table (K.{u} n)) :
    (concatInterval F G h).map (up x) =
      ((concatInterval ((rectangleDiagramOfFunctor F).concatDiagonalOne (rectangleDiagramOfFunctor G) h)
        ((rectangleDiagramOfFunctor F).concatDiagonalTwo (rectangleDiagramOfFunctor G) h)
        ((rectangleDiagramOfFunctor F).concatDiagonal_matching (rectangleDiagramOfFunctor G) h)).map x).val :=
  RectangleDiagram.lift_up _ x

lemma zero_interval_seam {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} 0).nu Y) (h : IntervalMatching F G) :
    Y.target 0 (F.map (verticalTable (topTable 0))) = Y.source 0 (G.map (verticalTable (topTable 0))) := by
  erw [← F.map_target, ← G.map_source]
  have ht := zeroCylinderMap.map_target 0 (topTable 1)
  have hs := zeroCylinderMap.map_source 0 (topTable 1)
  change zeroCylinderMap.map (vertex 0 true) = _ at ht
  change zeroCylinderMap.map (vertex 0 false) = _ at hs
  rw [zeroCylinderMap_vertex, zeroCylinderMap_top] at ht hs
  rw [← ht, ← hs]
  exact h _

lemma concatInterval_natural (n : ℕ) {Y : OmegaCategory.{v}} {Z : OmegaCategory.{w}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : IntervalMatching F G)
    (P : OmegaCategory.Functor Y Z) :
    OmegaCategory.Functor.comp (concatInterval F G h) P =
      concatInterval (OmegaCategory.Functor.comp F P) (OmegaCategory.Functor.comp G P)
        (fun x => congrArg P.map (h x)) := by
  induction n generalizing Y Z with
  | zero =>
    apply OmegaCategory.Functor.ext
    funext x
    rcases table_zero_cases x with ⟨a,he⟩ | he
    · rw [he]
      change P.map ((concatInterval F G h).map (atEnd a (project x))) = _
      erw [concatInterval_endpoint, concatInterval_endpoint]
      cases a <;> rfl
    · rw [he]
      change P.map ((concatInterval F G h).map (verticalTable (topTable 0))) = _
      erw [concatInterval_zero_vertical, concatInterval_zero_vertical]
      exact P.map_join 0 _ _ (zero_interval_seam F G h)
  | succ n ih =>
    apply functor_ext_rectangle
    · intro a x
      change P.map ((concatInterval F G h).map (atEnd a x)) = _
      erw [concatInterval_endpoint, concatInterval_endpoint]
      cases a <;> rfl
    · intro a
      change P.map ((concatInterval F G h).map (verticalTable (vertex n a))) = _
      erw [concatInterval_succ_edge, concatInterval_succ_edge]
      exact P.map_join 0 _ _ ((rectangleDiagramOfFunctor F).seam_edge (rectangleDiagramOfFunctor G) h a)
    · intro x
      change P.map ((concatInterval F G h).map (up x)) = _
      erw [concatInterval_succ_up, concatInterval_succ_up]
      let D := rectangleDiagramOfFunctor F
      let E := rectangleDiagramOfFunctor G
      have hh := ih (D.concatDiagonalOne E h) (D.concatDiagonalTwo E h)
        (D.concatDiagonal_matching E h)
        (P.homMap ((D.ends false).map (vertex n false)) ((E.ends true).map (vertex n true)))
      simp only [D.map_concatDiagonalOne E h P, D.map_concatDiagonalTwo E h P] at hh
      exact congrArg (fun U => (U.map x).val) hh

end Thomason.GrayRecursive

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_CylinderFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cylinder Faces. -/

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma suspend_comp {n k : ℕ} (x y : Table (complex.{u} n))
    (h : truncate k true x = truncate k false y)
    (h' : truncate (k+1) true (suspendTable x) = truncate (k+1) false (suspendTable y)) :
    suspendTable (DirectedComplex.Table.comp k x y h) =
      DirectedComplex.Table.comp (k+1) (suspendTable x) (suspendTable y) h' := by
  ext p b
  cases p with
  | zero => simp
  | succ p =>
    simp only [suspendTable_succ, comp_row, Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff]
    erw [apply_ite (shiftDown n p).symm, apply_ite (shiftDown n p).symm,
      apply_ite (shiftDown n p).symm, map_add]
    rfl

def globeHom (n : ℕ) : OmegaCategory.Functor (complex.{u} n).nu
    ((complex.{u} (n+1)).nu.homCategory (vertex n false) (vertex n true)) where
  map x := ⟨suspendTable x, suspend_truncate_zero false x, suspend_truncate_zero true x⟩
  map_source k x := Subtype.ext (suspendTable_truncate x k false)
  map_target k x := Subtype.ext (suspendTable_truncate x k true)
  map_comp k x y h h' := Subtype.ext (suspend_comp (k := k) x y h (congrArg Subtype.val h'))

def globeHomMap {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (complex.{u} (n+1)).nu Y) :
    OmegaCategory.Functor (complex.{u} n).nu
      (Y.homCategory (F.map (vertex n false)) (F.map (vertex n true))) :=
  OmegaCategory.Functor.comp (globeHom n) (F.homMap (vertex n false) (vertex n true))

lemma globe_horizontal_match {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex.{u} (n+1)).nu Y)
    (h : F.map (vertex n true) = G.map (vertex n false)) :
    Y.target 0 (F.map (topTable (n+1))) = Y.source 0 (G.map (topTable (n+1))) := by
  erw [← F.map_target, ← G.map_source]
  exact h

lemma globe_horizontal_fixed {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex.{u} (n+1)).nu Y)
    (h : F.map (vertex n true) = G.map (vertex n false)) :
    Y.source (n+1) (Y.join 0 (F.map (topTable (n+1))) (G.map (topTable (n+1)))) =
      Y.join 0 (F.map (topTable (n+1))) (G.map (topTable (n+1))) := by
  erw [Y.join_source_gt (n+1) 0 _ _ (by omega) (globe_horizontal_match F G h), ← F.map_source, ← G.map_source]
  change Y.join 0 (F.map (truncate (n+1) false (topTable (n+1))))
    (G.map (truncate (n+1) false (topTable (n+1)))) = _
  rw [topTable_bounded]

def globeHorizontal {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex.{u} (n+1)).nu Y)
    (h : F.map (vertex n true) = G.map (vertex n false)) :
    OmegaCategory.Functor (complex.{u} (n+1)).nu Y :=
  GlobeComplex.lift _ (globe_horizontal_fixed F G h)

@[simp] lemma globeHorizontal_vertex {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex.{u} (n+1)).nu Y)
    (h : F.map (vertex n true) = G.map (vertex n false)) (a : Bool) :
    (globeHorizontal F G h).map (vertex n a) = if a then G.map (vertex n true) else F.map (vertex n false) := by
  erw [vertex, ← face_nu, (globeHorizontal F G h).map_face]
  have ht : (globeHorizontal F G h).map (topTable (n+1)) =
      Y.join 0 (F.map (topTable (n+1))) (G.map (topTable (n+1))) := lift_top _ _
  rw [ht]
  cases a
  · change Y.source 0 _ = _
    erw [Y.join_source_le 0 0 _ _ le_rfl (globe_horizontal_match F G h), ← F.map_source]; rfl
  · change Y.target 0 _ = _
    erw [Y.join_target_le 0 0 _ _ le_rfl (globe_horizontal_match F G h), ← G.map_target]; rfl

@[simp] lemma globeHorizontal_suspend {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex.{u} (n+1)).nu Y)
    (h : F.map (vertex n true) = G.map (vertex n false)) (x : Table (complex.{u} n)) :
    (globeHorizontal F G h).map (suspendTable x) =
      Y.join 0 (F.map (suspendTable x)) (G.map (suspendTable x)) := by
  obtain ⟨p,a,hp,he⟩ := table_classification x
  erw [he, suspendTable_eq_face, ← face_nu, (globeHorizontal F G h).map_face, F.map_face, G.map_face]
  have ht : (globeHorizontal F G h).map (topTable (n+1)) =
      Y.join 0 (F.map (topTable (n+1))) (G.map (topTable (n+1))) := lift_top _ _
  rw [ht]
  cases a
  · exact Y.join_source_gt (p+1) 0 _ _ (by omega) (globe_horizontal_match F G h)
  · exact Y.join_target_gt (p+1) 0 _ _ (by omega) (globe_horizontal_match F G h)

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

namespace RectangleDiagram
variable {n : ℕ} {Y : OmegaCategory.{v}}
    (D E : RectangleDiagram.{u,v} n Y) (h : D.edge true = E.edge false)

include h in
lemma horizontal_seam (a : Bool) :
    (D.ends a).map (vertex n true) = (E.ends a).map (vertex n false) := by
  cases a
  · rw [← D.edge_source, h, E.edge_source]
  · rw [← D.edge_target, h, E.edge_target]

def horizontalDiagonalOne : OmegaCategory.Functor (K.{u} n).nu
    (Y.homCategory ((D.ends false).map (vertex n false)) ((E.ends true).map (vertex n true))) :=
  homCompose D.diagonal (homCast
    (OmegaCategory.Functor.comp (complex n).cylinderProjection.nu (globeHomMap (E.ends true)))
    (D.horizontal_seam E h true).symm rfl)

def horizontalDiagonalTwo : OmegaCategory.Functor (K.{u} n).nu
    (Y.homCategory ((D.ends false).map (vertex n false)) ((E.ends true).map (vertex n true))) :=
  homCompose (homCast
    (OmegaCategory.Functor.comp (complex n).cylinderProjection.nu (globeHomMap (D.ends false)))
    rfl (D.horizontal_seam E h false)) E.diagonal

lemma horizontalDiagonalOne_map (x : Table (K.{u} n)) :
    ((D.horizontalDiagonalOne E h).map x).val =
      Y.join 0 (D.diagonal.map x).val ((E.ends true).map (suspendTable (project x))) := rfl
lemma horizontalDiagonalTwo_map (x : Table (K.{u} n)) :
    ((D.horizontalDiagonalTwo E h).map x).val =
      Y.join 0 ((D.ends false).map (suspendTable (project x))) (E.diagonal.map x).val := rfl

lemma horizontalDiagonal_matching : IntervalMatching (D.horizontalDiagonalOne E h) (D.horizontalDiagonalTwo E h) := by
  intro x
  apply Subtype.ext
  rw [D.horizontalDiagonalOne_map E h, D.horizontalDiagonalTwo_map E h, project_end, project_end, D.right, E.left, h]
  exact Y.join_assoc 0 _ _ _ (by rw [← h]; exact D.end_edge_matching x) (E.edge_end_matching x)

include h in
lemma horizontal_source_match (x : Table (complex.{u} n)) (a : Bool) :
    Y.target 0 ((D.ends a).map (suspendTable x)) = Y.source 0 ((E.ends a).map (suspendTable x)) := by
  erw [← (D.ends a).map_target, ← (E.ends a).map_source]
  change (D.ends a).map (truncate 0 true (suspendTable x)) =
    (E.ends a).map (truncate 0 false (suspendTable x))
  rw [suspend_truncate_zero, suspend_truncate_zero]
  exact D.horizontal_seam E h a

def horizontal : RectangleDiagram.{u,v} n Y where
  ends a := globeHorizontal (D.ends a) (E.ends a) (D.horizontal_seam E h a)
  edge a := if a then E.edge true else D.edge false
  edge_fixed a := by cases a <;> simp only [Bool.false_eq_true, ite_false, ite_true]; exact D.edge_fixed false; exact E.edge_fixed true
  edge_source a := by
    rw [globeHorizontal_vertex]
    cases a
    · exact D.edge_source false
    · exact E.edge_source true
  edge_target a := by
    rw [globeHorizontal_vertex]
    cases a
    · exact D.edge_target false
    · exact E.edge_target true
  diagonal := homCast (concatInterval (D.horizontalDiagonalOne E h) (D.horizontalDiagonalTwo E h)
    (D.horizontalDiagonal_matching E h))
    (by simp)
    (by simp)
  left x := by
    change ((concatInterval (D.horizontalDiagonalOne E h) (D.horizontalDiagonalTwo E h)
      (D.horizontalDiagonal_matching E h)).map (atEnd false x)).val = _
    rw [concatInterval_endpoint]
    simp only [Bool.false_eq_true, ite_false]
    rw [D.horizontalDiagonalOne_map E h, project_end, D.left, globeHorizontal_suspend]
    exact Y.join_assoc 0 _ _ _ (D.edge_end_matching x) (D.horizontal_source_match E h x true)
  right x := by
    change ((concatInterval (D.horizontalDiagonalOne E h) (D.horizontalDiagonalTwo E h)
      (D.horizontalDiagonal_matching E h)).map (atEnd true x)).val = _
    rw [concatInterval_endpoint]
    simp only [ite_true]
    rw [D.horizontalDiagonalTwo_map E h, project_end, E.right, globeHorizontal_suspend]
    exact (Y.join_assoc 0 _ _ _ (D.horizontal_source_match E h x false) (E.end_edge_matching x)).symm

end RectangleDiagram

def horizontalCylinder {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y)
    (h : F.map (verticalTable (vertex n true)) = G.map (verticalTable (vertex n false))) :
    OmegaCategory.Functor (K.{u} (n+1)).nu Y :=
  ((rectangleDiagramOfFunctor F).horizontal (rectangleDiagramOfFunctor G) h).lift

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma globeHorizontal_natural {n : ℕ} {Y : OmegaCategory.{v}} {Z : OmegaCategory.{w}}
    (F G : OmegaCategory.Functor (complex.{u} (n+1)).nu Y)
    (h : F.map (vertex n true) = G.map (vertex n false)) (P : OmegaCategory.Functor Y Z) :
    OmegaCategory.Functor.comp (globeHorizontal F G h) P =
    globeHorizontal (OmegaCategory.Functor.comp F P) (OmegaCategory.Functor.comp G P)
      (congrArg P.map h) := by
  apply GlobeComplex.functor_ext
  change P.map ((globeHorizontal F G h).map (topTable (n+1))) = _
  rw [show (globeHorizontal F G h).map (topTable (n+1)) =
    Y.join 0 (F.map (topTable (n+1))) (G.map (topTable (n+1))) from lift_top _ _,
    show (globeHorizontal (OmegaCategory.Functor.comp F P) (OmegaCategory.Functor.comp G P)
      (congrArg P.map h)).map (topTable (n+1)) = _ from lift_top _ _]
  exact P.map_join 0 _ _ (globe_horizontal_match F G h)

namespace RectangleDiagram
variable {n : ℕ} {Y : OmegaCategory.{v}} {Z : OmegaCategory.{w}}
    (D E : RectangleDiagram.{u,v} n Y) (h : D.edge true = E.edge false)
    (P : OmegaCategory.Functor Y Z)

lemma map_horizontalDiagonalOne :
    OmegaCategory.Functor.comp (D.horizontalDiagonalOne E h)
      (P.homMap ((D.ends false).map (vertex n false)) ((E.ends true).map (vertex n true))) =
    (D.map P).horizontalDiagonalOne (E.map P) (congrArg P.map h) := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change P.map (Y.join 0 (D.diagonal.map x).val ((E.ends true).map (suspendTable (project x)))) =
    Z.join 0 (P.map (D.diagonal.map x).val) (P.map ((E.ends true).map (suspendTable (project x))))
  apply P.map_join
  erw [(D.diagonal.map x).property.2, D.horizontal_seam E h true, ← (E.ends true).map_source]
  exact congrArg (E.ends true).map (suspend_truncate_zero false (project x)).symm

lemma map_horizontalDiagonalTwo :
    OmegaCategory.Functor.comp (D.horizontalDiagonalTwo E h)
      (P.homMap ((D.ends false).map (vertex n false)) ((E.ends true).map (vertex n true))) =
    (D.map P).horizontalDiagonalTwo (E.map P) (congrArg P.map h) := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change P.map (Y.join 0 ((D.ends false).map (suspendTable (project x))) (E.diagonal.map x).val) =
    Z.join 0 (P.map ((D.ends false).map (suspendTable (project x)))) (P.map (E.diagonal.map x).val)
  apply P.map_join
  erw [(E.diagonal.map x).property.1, ← D.horizontal_seam E h false, ← (D.ends false).map_target]
  exact congrArg (D.ends false).map (suspend_truncate_zero true (project x))

lemma horizontal_lift_map :
    OmegaCategory.Functor.comp (D.horizontal E h).lift P =
      ((D.map P).horizontal (E.map P) (congrArg P.map h)).lift := by
  apply functor_ext_rectangle
  · intro a x
    change P.map ((D.horizontal E h).lift.map (atEnd a x)) = _
    rw [lift_endpoint, lift_endpoint]
    exact congrArg (fun U => U.map x)
      (globeHorizontal_natural (D.ends a) (E.ends a) (D.horizontal_seam E h a) P)
  · intro a
    change P.map ((D.horizontal E h).lift.map (verticalTable (vertex n a))) = _
    rw [lift_edge, lift_edge]
    cases a <;> rfl
  · intro x
    change P.map ((D.horizontal E h).lift.map (up x)) = _
    rw [lift_up, lift_up]
    have hh := concatInterval_natural n (D.horizontalDiagonalOne E h)
      (D.horizontalDiagonalTwo E h) (D.horizontalDiagonal_matching E h)
      (P.homMap ((D.ends false).map (vertex n false)) ((E.ends true).map (vertex n true)))
    simp only [D.map_horizontalDiagonalOne E h P, D.map_horizontalDiagonalTwo E h P] at hh
    exact congrArg (fun U => (U.map x).val) hh

end RectangleDiagram

lemma horizontalCylinder_natural {n : ℕ} {Y : OmegaCategory.{v}} {Z : OmegaCategory.{w}}
    (F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y)
    (h : F.map (verticalTable (vertex n true)) = G.map (verticalTable (vertex n false)))
    (P : OmegaCategory.Functor Y Z) :
    OmegaCategory.Functor.comp (horizontalCylinder F G h) P =
      horizontalCylinder (OmegaCategory.Functor.comp F P) (OmegaCategory.Functor.comp G P)
        (congrArg P.map h) :=
  (rectangleDiagramOfFunctor F).horizontal_lift_map (rectangleDiagramOfFunctor G) h P

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

@[simp] lemma project_up {n : ℕ} (x : Table (K.{u} n)) :
    project (up x) = suspendTable (project x) := by
  ext p b
  cases p with
  | zero =>
    cases b <;> simp [up, upRow, diagonalRow, suspendTable_zero,
      project, Hom.table, cylinderProjection, cylinderProjectionMap]
  | succ p =>
    cases p with
    | zero =>
      simp only [project_row, sideRow, up, upRow, suspendTable_succ]
      erw [map_add]
      exact add_comm _ _
    | succ p =>
      simp only [project_row, sideRow, up, upRow, suspendTable_succ]
      erw [map_add]
      exact add_comm _ _

@[simp] lemma project_zero_vertical :
    project (verticalTable (topTable.{u} 0)) = topTable 0 :=
  globe_zero_unique _

def constantInterval {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (complex.{u} n).nu Y) :
    OmegaCategory.Functor (K.{u} n).nu Y :=
  OmegaCategory.Functor.comp (complex n).cylinderProjection.nu F

@[simp] lemma constantInterval_map {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (complex.{u} n).nu Y) (x : Table (K.{u} n)) :
    (constantInterval F).map x = F.map (project x) := rfl

@[simp] lemma constantInterval_endpoint {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (complex.{u} n).nu Y) (a : Bool) (x : Table (complex.{u} n)) :
    (constantInterval F).map (atEnd a x) = F.map x := by
  rw [constantInterval_map, project_end]

@[simp] lemma constantInterval_edge {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (complex.{u} (n+1)).nu Y) (a : Bool) :
    (constantInterval F).map (verticalTable (vertex n a)) = F.map (vertex n a) := by
  rw [constantInterval_map, project_vertical_vertex]

@[simp] lemma constantInterval_up {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (complex.{u} (n+1)).nu Y) (x : Table (K.{u} n)) :
    (constantInterval F).map (up x) = F.map (suspendTable (project x)) := by
  rw [constantInterval_map, project_up]

lemma constantInterval_matching {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (complex.{u} n).nu Y) :
    IntervalMatching (constantInterval F) (constantInterval F) := by
  intro x
  rw [constantInterval_endpoint, constantInterval_endpoint]

lemma constantInterval_ends {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (complex.{u} (n+1)).nu Y) (a : Bool) :
    (rectangleDiagramOfFunctor (constantInterval F)).ends a = F := by
  apply OmegaCategory.Functor.ext
  funext x
  exact constantInterval_endpoint F a x

lemma constantInterval_concatDiagonalOne {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (complex.{u} (n+1)).nu Y) :
    (rectangleDiagramOfFunctor (constantInterval F)).concatDiagonalOne
      (rectangleDiagramOfFunctor (constantInterval F)) (constantInterval_matching F) =
    homCast (constantInterval (globeHomMap F))
      (constantInterval_endpoint F false (vertex n false)).symm
      (constantInterval_endpoint F true (vertex n true)).symm := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change Y.join 0 ((constantInterval F).map (verticalTable (vertex n false)))
    ((constantInterval F).map (up x)) = F.map (suspendTable (project x))
  erw [constantInterval_edge, constantInterval_up]
  apply Y.join_left_unit
  · erw [← F.map_source]
    exact congrArg F.map (vertex_truncate n 0 false false)
  · erw [← F.map_target, ← F.map_source]
    exact congrArg F.map ((vertex_truncate n 0 false true).trans
      (suspend_truncate_zero false (project x)).symm)

lemma constantInterval_concatDiagonalTwo {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (complex.{u} (n+1)).nu Y) :
    (rectangleDiagramOfFunctor (constantInterval F)).concatDiagonalTwo
      (rectangleDiagramOfFunctor (constantInterval F)) (constantInterval_matching F) =
    homCast (constantInterval (globeHomMap F))
      (constantInterval_endpoint F false (vertex n false)).symm
      (constantInterval_endpoint F true (vertex n true)).symm := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change Y.join 0 ((constantInterval F).map (up x))
    ((constantInterval F).map (verticalTable (vertex n true))) = F.map (suspendTable (project x))
  erw [constantInterval_edge, constantInterval_up]
  apply Y.join_right_unit
  · erw [← F.map_source]
    exact congrArg F.map (vertex_truncate n 0 true false)
  · erw [← F.map_target, ← F.map_source]
    exact congrArg F.map ((suspend_truncate_zero true (project x)).trans
      (vertex_truncate n 0 true false).symm)

lemma homCast_constantInterval {n : ℕ} {Y : OmegaCategory.{v}} {a b c d : Y.Cell}
    (F : OmegaCategory.Functor (complex.{u} n).nu (Y.homCategory a b))
    (hac : a = c) (hbd : b = d) :
    homCast (constantInterval F) hac hbd = constantInterval (homCast F hac hbd) := rfl

lemma concatInterval_constant (n : ℕ) {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (complex.{u} n).nu Y) :
    concatInterval (constantInterval F) (constantInterval F) (constantInterval_matching F) =
      constantInterval F := by
  induction n generalizing Y with
  | zero =>
    apply OmegaCategory.Functor.ext
    funext x
    rcases table_zero_cases x with ⟨a,he⟩ | he
    · rw [he, concatInterval_endpoint]
      cases a <;> simp
    · rw [he, concatInterval_zero_vertical, constantInterval_map, project_zero_vertical]
      apply Y.join_left_unit
      · erw [← F.map_source]
        exact congrArg F.map (topTable_bounded 0)
      · erw [← F.map_target, ← F.map_source]
        exact congrArg F.map (show truncate 0 true (topTable 0) = truncate 0 false (topTable 0) by
          rw [globe_zero_unique (truncate 0 true _), globe_zero_unique (truncate 0 false _)])
  | succ n ih =>
    apply functor_ext_rectangle
    · intro a x
      rw [concatInterval_endpoint]
      cases a <;> simp
    · intro a
      rw [concatInterval_succ_edge, constantInterval_edge]
      apply Y.join_left_unit
      · erw [← F.map_source]; exact congrArg F.map (vertex_truncate n 0 a false)
      · erw [← F.map_target, ← F.map_source]
        exact congrArg F.map ((vertex_truncate n 0 a true).trans (vertex_truncate n 0 a false).symm)
    · intro x
      rw [concatInterval_succ_up]
      simp only [constantInterval_concatDiagonalOne, constantInterval_concatDiagonalTwo,
        homCast_constantInterval]
      erw [ih]
      exact (constantInterval_up F x).symm

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

def globeHorizontalHom {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex.{u} (n+1)).nu Y)
    (h : F.map (vertex n true) = G.map (vertex n false)) :
    OmegaCategory.Functor (complex.{u} n).nu
      (Y.homCategory (F.map (vertex n false)) (G.map (vertex n true))) :=
  homCompose (globeHomMap F) (homCast (globeHomMap G) h.symm rfl)

lemma constantInterval_horizontal_match {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex.{u} (n+1)).nu Y)
    (h : F.map (vertex n true) = G.map (vertex n false)) :
    (constantInterval F).map (verticalTable (vertex n true)) =
      (constantInterval G).map (verticalTable (vertex n false)) := by
  rw [constantInterval_edge, constantInterval_edge, h]

lemma constantInterval_horizontalDiagonalOne {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex.{u} (n+1)).nu Y)
    (h : F.map (vertex n true) = G.map (vertex n false)) :
    (rectangleDiagramOfFunctor (constantInterval F)).horizontalDiagonalOne
      (rectangleDiagramOfFunctor (constantInterval G)) (constantInterval_horizontal_match F G h) =
    constantInterval (homCast (globeHorizontalHom F G h)
      (constantInterval_endpoint F false (vertex n false)).symm
      (constantInterval_endpoint G true (vertex n true)).symm) := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change Y.join 0 ((constantInterval F).map (up x))
    ((constantInterval G).map (atEnd true (suspendTable (project x)))) =
      Y.join 0 (F.map (suspendTable (project x))) (G.map (suspendTable (project x)))
  erw [constantInterval_up, constantInterval_endpoint]

lemma constantInterval_horizontalDiagonalTwo {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex.{u} (n+1)).nu Y)
    (h : F.map (vertex n true) = G.map (vertex n false)) :
    (rectangleDiagramOfFunctor (constantInterval F)).horizontalDiagonalTwo
      (rectangleDiagramOfFunctor (constantInterval G)) (constantInterval_horizontal_match F G h) =
    constantInterval (homCast (globeHorizontalHom F G h)
      (constantInterval_endpoint F false (vertex n false)).symm
      (constantInterval_endpoint G true (vertex n true)).symm) := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change Y.join 0 ((constantInterval F).map (atEnd false (suspendTable (project x))))
    ((constantInterval G).map (up x)) =
      Y.join 0 (F.map (suspendTable (project x))) (G.map (suspendTable (project x)))
  erw [constantInterval_up, constantInterval_endpoint]

lemma horizontalCylinder_endpoint {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y)
    (h : F.map (verticalTable (vertex n true)) = G.map (verticalTable (vertex n false)))
    (a : Bool) (x : Table (complex.{u} (n+1))) :
    (horizontalCylinder F G h).map (atEnd a x) =
      (globeHorizontal ((rectangleDiagramOfFunctor F).ends a) ((rectangleDiagramOfFunctor G).ends a)
        ((rectangleDiagramOfFunctor F).horizontal_seam (rectangleDiagramOfFunctor G) h a)).map x :=
  RectangleDiagram.lift_endpoint _ a x

lemma horizontalCylinder_edge {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y)
    (h : F.map (verticalTable (vertex n true)) = G.map (verticalTable (vertex n false)))
    (a : Bool) :
    (horizontalCylinder F G h).map (verticalTable (vertex n a)) =
      if a then G.map (verticalTable (vertex n true)) else F.map (verticalTable (vertex n false)) :=
  RectangleDiagram.lift_edge _ a

lemma horizontalCylinder_up {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y)
    (h : F.map (verticalTable (vertex n true)) = G.map (verticalTable (vertex n false)))
    (x : Table (K.{u} n)) :
    (horizontalCylinder F G h).map (up x) =
      ((concatInterval ((rectangleDiagramOfFunctor F).horizontalDiagonalOne (rectangleDiagramOfFunctor G) h)
      ((rectangleDiagramOfFunctor F).horizontalDiagonalTwo (rectangleDiagramOfFunctor G) h)
      ((rectangleDiagramOfFunctor F).horizontalDiagonal_matching (rectangleDiagramOfFunctor G) h)).map x).val :=
  RectangleDiagram.lift_up _ x

lemma horizontalCylinder_constant {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex.{u} (n+1)).nu Y)
    (h : F.map (vertex n true) = G.map (vertex n false)) :
    horizontalCylinder (constantInterval F) (constantInterval G) (constantInterval_horizontal_match F G h) =
      constantInterval (globeHorizontal F G h) := by
  apply functor_ext_rectangle
  · intro a x
    rw [horizontalCylinder_endpoint, constantInterval_endpoint]
    simp only [constantInterval_ends]
  · intro a
    simp only [horizontalCylinder_edge, constantInterval_edge, globeHorizontal_vertex]
  · intro x
    rw [horizontalCylinder_up]
    simp only [constantInterval_horizontalDiagonalOne F G h, constantInterval_horizontalDiagonalTwo F G h]
    erw [concatInterval_constant, constantInterval_up, globeHorizontal_suspend]
    rfl

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma faceMap_vertex (n k : ℕ) (b a : Bool) :
    (faceMap.{u} (n+1) (k+1) b).nu.map (vertex k a) = vertex n a := by
  erw [vertex, ← face_nu, OmegaCategory.Functor.map_face, faceMap_top]
  rw [face_nu]
  change truncate 0 a (truncate (k+1) b (topTable (n+1))) = vertex n a
  rw [truncate_truncate, ite_eq_left (show 0 < k+1 by omega)]
  rfl

lemma faceMap_suspend (n k : ℕ) (b : Bool) (x : Table (complex.{u} k)) :
    (faceMap.{u} (n+1) (k+1) b).nu.map (suspendTable x) =
      suspendTable ((faceMap.{u} n k b).nu.map x) := by
  obtain ⟨p,a,hp,he⟩ := table_classification x
  rw [he, suspendTable_eq_face]
  erw [← face_nu (k+1) (p+1) a (topTable (k+1)), OmegaCategory.Functor.map_face, faceMap_top, face_nu]
  erw [← face_nu k p a (topTable k), OmegaCategory.Functor.map_face, faceMap_top, face_nu]
  change truncate (p+1) a (truncate (k+1) b (topTable (n+1))) =
    suspendTable (truncate p a (truncate k b (topTable n)))
  rw [suspendTable_truncate, suspendTable_eq_face]

lemma cylinderHom_atEnd {n m : ℕ} (f : DirectedComplex.Hom (complex.{u} n) (complex.{u} m))
    (a : Bool) (x : Table (complex.{u} n)) :
    f.cylinder.nu.map (atEnd a x) = atEnd a (f.nu.map x) := by
  have h := congrArg (fun g => g.nu.map x) (f.cylinder_endpoint a)
  exact h

lemma tensorFace_edge (n k : ℕ) (b a : Bool) :
    (faceMap.{u} (n+1) (k+1) b).cylinder.nu.map (verticalTable (vertex k a)) =
      verticalTable (vertex n a) := by
  rw [verticalTable_natural, faceMap_vertex]

lemma tensorFace_up (n k : ℕ) (b : Bool) (x : Table (K.{u} k)) :
    (faceMap.{u} (n+1) (k+1) b).cylinder.nu.map (up x) =
      up ((faceMap.{u} n k b).cylinder.nu.map x) := by
  apply generated k (fun x => (faceMap.{u} (n+1) (k+1) b).cylinder.nu.map (up x) =
    up ((faceMap.{u} n k b).cylinder.nu.map x))
  · intro a y
    cases a
    · rw [up_endpoint_false]
      change (faceMap (n+1) (k+1) b).cylinder.table _ = _
      rw [(faceMap.{u} (n+1) (k+1) b).cylinder.table_comp _ _ _ _
        ((faceMap.{u} (n+1) (k+1) b).cylinder.nu.map_composable (up_endpoint_left_matching y))]
      change DirectedComplex.Table.comp 0
        ((faceMap (n+1) (k+1) b).cylinder.nu.map _)
        ((faceMap (n+1) (k+1) b).cylinder.nu.map _) _ = _
      simp only [tensorFace_edge, cylinderHom_atEnd, faceMap_suspend]
      erw [up_endpoint_false]
    · rw [up_endpoint_true]
      change (faceMap (n+1) (k+1) b).cylinder.table _ = _
      rw [(faceMap.{u} (n+1) (k+1) b).cylinder.table_comp _ _ _ _
        ((faceMap.{u} (n+1) (k+1) b).cylinder.nu.map_composable (up_endpoint_right_matching y))]
      change DirectedComplex.Table.comp 0
        ((faceMap (n+1) (k+1) b).cylinder.nu.map _)
        ((faceMap (n+1) (k+1) b).cylinder.nu.map _) _ = _
      simp only [tensorFace_edge, cylinderHom_atEnd, faceMap_suspend]
      erw [up_endpoint_true]
  · intro y
    erw [up_vertical, verticalTable_natural, faceMap_suspend, verticalTable_natural, up_vertical]
  · intro l s t h hs ht
    rw [up_comp s t h (up_composable h)]
    change (faceMap (n+1) (k+1) b).cylinder.table _ = up ((faceMap n k b).cylinder.table _)
    rw [(faceMap.{u} (n+1) (k+1) b).cylinder.table_comp _ _ _ _
      ((faceMap.{u} (n+1) (k+1) b).cylinder.nu.map_composable (up_composable h))]
    have h' := (faceMap.{u} n k b).cylinder.nu.map_composable h
    rw [(faceMap.{u} n k b).cylinder.table_comp _ _ _ h h']
    change DirectedComplex.Table.comp (l+1) _ _ _ = up (DirectedComplex.Table.comp l _ _ h')
    rw [up_comp _ _ h' (up_composable h')]
    change DirectedComplex.Table.comp (l+1)
      ((faceMap (n+1) (k+1) b).cylinder.nu.map (up s))
      ((faceMap (n+1) (k+1) b).cylinder.nu.map (up t)) _ = _
    simp only [hs, ht]

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

def rectangleDiagramOfTop {n : ℕ} {Y : OmegaCategory.{v}}
    (ends : Bool → OmegaCategory.Functor (complex.{u} (n+1)).nu Y)
    (edge : Bool → Y.Cell)
    (ef : ∀ a, Y.source 1 (edge a) = edge a)
    (es : ∀ a, Y.source 0 (edge a) = (ends false).map (vertex n a))
    (et : ∀ a, Y.target 0 (edge a) = (ends true).map (vertex n a))
    (diag : OmegaCategory.Functor (K.{u} n).nu
      (Y.homCategory ((ends false).map (vertex n false)) ((ends true).map (vertex n true))))
    (hl : (diag.map (atEnd false (topTable n))).val =
      Y.join 0 (edge false) ((ends true).map (topTable (n+1))))
    (hr : (diag.map (atEnd true (topTable n))).val =
      Y.join 0 ((ends false).map (topTable (n+1))) (edge true)) :
    RectangleDiagram.{u,v} n Y where
  ends := ends
  edge := edge
  edge_fixed := ef
  edge_source := es
  edge_target := et
  diagonal := diag
  left x := by
    let A := OmegaCategory.Functor.comp ((complex n).cylinderEndpoint false).nu diag
    let B := homCompose (constantHom (complex.{u} n).nu (edge false)
      (ef false) (es false) (et false)) (globeHomMap (ends true))
    have h : A = B := by
      apply GlobeComplex.functor_ext
      apply Subtype.ext
      change (diag.map (atEnd false (topTable n))).val =
        Y.join 0 (edge false) ((ends true).map (suspendTable (topTable n)))
      rw [suspendTable_top]
      exact hl
    exact congrArg (fun F => (F.map x).val) h
  right x := by
    let A := OmegaCategory.Functor.comp ((complex n).cylinderEndpoint true).nu diag
    let B := homCompose (globeHomMap (ends false))
      (constantHom (complex.{u} n).nu (edge true) (ef true) (es true) (et true))
    have h : A = B := by
      apply GlobeComplex.functor_ext
      apply Subtype.ext
      change (diag.map (atEnd true (topTable n))).val =
        Y.join 0 ((ends false).map (suspendTable (topTable n))) (edge true)
      rw [suspendTable_top]
      exact hr
    exact congrArg (fun F => (F.map x).val) h

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

def FaceMatching {n : ℕ} (k : ℕ) {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) : Prop :=
  ∀ x : Table (K.{u} k),
    F.map ((faceMap n k true).cylinder.nu.map x) =
      G.map ((faceMap n k false).cylinder.nu.map x)

def globeComposite {n k : ℕ} (hk : k < n) {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex.{u} n).nu Y)
    (h : Y.target k (F.map (topTable n)) = Y.source k (G.map (topTable n))) :
    OmegaCategory.Functor (complex.{u} n).nu Y :=
  GlobeComplex.lift (Y.join k (F.map (topTable n)) (G.map (topTable n))) (by
    erw [Y.join_source_gt n k _ _ hk h, ← F.map_source, ← G.map_source]
    change Y.join k (F.map (truncate n false (topTable n)))
      (G.map (truncate n false (topTable n))) = _
    rw [topTable_bounded])

@[simp] lemma globeComposite_top {n k : ℕ} (hk : k < n) {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex.{u} n).nu Y)
    (h : Y.target k (F.map (topTable n)) = Y.source k (G.map (topTable n))) :
    (globeComposite hk F G h).map (topTable n) =
      Y.join k (F.map (topTable n)) (G.map (topTable n)) := lift_top _ _

lemma globeMatching_vertex {n k : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex.{u} (n+1)).nu Y)
    (h : Y.target (k+1) (F.map (topTable (n+1))) =
      Y.source (k+1) (G.map (topTable (n+1)))) (a : Bool) :
    F.map (vertex n a) = G.map (vertex n a) := by
  have h' := congrArg (Y.face 0 a) h
  cases a
  · change Y.source 0 _ = Y.source 0 _ at h'
    simp only [Y.source_target, ite_eq_left (show 0 < k+1 by omega), Y.source_source,
      min_eq_left (show 0 ≤ k+1 by omega)] at h'
    erw [← F.map_source, ← G.map_source] at h'
    exact h'
  · change Y.target 0 _ = Y.target 0 _ at h'
    simp only [Y.target_source, ite_eq_left (show 0 < k+1 by omega), Y.target_target,
      min_eq_left (show 0 ≤ k+1 by omega)] at h'
    erw [← F.map_target, ← G.map_target] at h'
    exact h'

lemma globeComposite_vertex {n k : ℕ} (hk : k < n) {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex.{u} (n+1)).nu Y)
    (h : Y.target (k+1) (F.map (topTable (n+1))) =
      Y.source (k+1) (G.map (topTable (n+1)))) (a : Bool) :
    (globeComposite (Nat.add_lt_add_right hk 1) F G h).map (vertex n a) = F.map (vertex n a) := by
  erw [vertex, ← face_nu, OmegaCategory.Functor.map_face, globeComposite_top]
  cases a
  · change Y.source 0 _ = _
    erw [Y.join_source_le 0 (k+1) _ _ (Nat.zero_le _) h, ← F.map_source]
    rfl
  · change Y.target 0 _ = _
    erw [Y.join_target_le 0 (k+1) _ _ (Nat.zero_le _) h, ← G.map_target]
    exact (globeMatching_vertex F G h true).symm

lemma globeComposite_natural {n k : ℕ} (hk : k < n) {Y : OmegaCategory.{v}} {Z : OmegaCategory.{w}}
    (F G : OmegaCategory.Functor (complex.{u} n).nu Y)
    (h : Y.target k (F.map (topTable n)) = Y.source k (G.map (topTable n)))
    (P : OmegaCategory.Functor Y Z) :
    OmegaCategory.Functor.comp (globeComposite hk F G h) P =
      globeComposite hk (OmegaCategory.Functor.comp F P) (OmegaCategory.Functor.comp G P)
        (P.map_composable h) := by
  apply GlobeComplex.functor_ext
  change P.map ((globeComposite hk F G h).map (topTable n)) = _
  erw [globeComposite_top, globeComposite_top, P.map_join _ _ _ h]
  rfl

lemma FaceMatching.ends {n k : ℕ} {Y : OmegaCategory.{v}}
    {F G : OmegaCategory.Functor (K.{u} n).nu Y} (h : FaceMatching k F G) (a : Bool) :
    Y.target k (F.map (atEnd a (topTable n))) =
      Y.source k (G.map (atEnd a (topTable n))) := by
  have h' := h (atEnd a (topTable k))
  rw [cylinderHom_atEnd, cylinderHom_atEnd, faceMap_top, faceMap_top] at h'
  erw [← F.map_target, ← G.map_source]
  change F.map (truncate k true (atEnd a (topTable n))) =
    G.map (truncate k false (atEnd a (topTable n)))
  simpa only [atEnd_truncate] using h'

lemma FaceMatching.edges {n k : ℕ} {Y : OmegaCategory.{v}}
    {F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y} (h : FaceMatching (k+1) F G) (a : Bool) :
    F.map (verticalTable (vertex n a)) = G.map (verticalTable (vertex n a)) := by
  have h' := h (verticalTable (vertex k a))
  simpa only [tensorFace_edge] using h'

lemma FaceMatching.vertices {n k : ℕ} {Y : OmegaCategory.{v}}
    {F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y} (h : FaceMatching (k+1) F G) (a b : Bool) :
    F.map (atEnd a (vertex n b)) = G.map (atEnd a (vertex n b)) := by
  have h' := h (atEnd a (vertex k b))
  simpa only [cylinderHom_atEnd, faceMap_vertex] using h'

lemma FaceMatching.natural {n k : ℕ} {Y : OmegaCategory.{v}} {Z : OmegaCategory.{w}}
    {F G : OmegaCategory.Functor (K.{u} n).nu Y} (h : FaceMatching k F G)
    (P : OmegaCategory.Functor Y Z) :
    FaceMatching k (OmegaCategory.Functor.comp F P) (OmegaCategory.Functor.comp G P) :=
  fun x => congrArg P.map (h x)

end Thomason.GrayRecursive

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_CylinderAssociativity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cylinder Associativity. -/

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma hom_join_val {Y : OmegaCategory.{v}} {a b : Y.Cell} (k : ℕ)
    (x y : (Y.homCategory a b).Cell)
    (h : (Y.homCategory a b).target k x = (Y.homCategory a b).source k y) :
    ((Y.homCategory a b).join k x y).val = Y.join (k+1) x.val y.val := by
  rw [(Y.homCategory a b).join_eq k x y h, Y.join_eq (k+1) _ _ (congrArg Subtype.val h)]
  rfl

structure CylinderComposition (n k : ℕ) where
  compose : {Y : OmegaCategory.{v}} →
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) → FaceMatching k F G →
      OmegaCategory.Functor (K.{u} n).nu Y
  endpoint_top : ∀ {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : FaceMatching k F G) (a : Bool),
    (compose F G h).map (atEnd a (topTable n)) =
      Y.join k (F.map (atEnd a (topTable n))) (G.map (atEnd a (topTable n)))

lemma CylinderComposition.endpoint {n k : ℕ} (C : CylinderComposition.{u,v} n k)
    (hk : k < n) {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : FaceMatching k F G)
    (a : Bool) (x : Table (complex.{u} n)) :
    (C.compose F G h).map (atEnd a x) =
      (globeComposite hk
        (OmegaCategory.Functor.comp ((complex n).cylinderEndpoint a).nu F)
        (OmegaCategory.Functor.comp ((complex n).cylinderEndpoint a).nu G) (h.ends a)).map x := by
  have he : OmegaCategory.Functor.comp ((complex n).cylinderEndpoint a).nu (C.compose F G h) =
      globeComposite hk
        (OmegaCategory.Functor.comp ((complex n).cylinderEndpoint a).nu F)
        (OmegaCategory.Functor.comp ((complex n).cylinderEndpoint a).nu G) (h.ends a) := by
    apply GlobeComplex.functor_ext
    erw [globeComposite_top]
    exact C.endpoint_top F G h a
  exact congrArg (fun A => A.map x) he

lemma zeroFaceMatching_seam {n : ℕ} {Y : OmegaCategory.{v}}
    {F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y} (h : FaceMatching 0 F G) :
    F.map (verticalTable (vertex n true)) = G.map (verticalTable (vertex n false)) := by
  have h' := h (verticalTable (topTable 0))
  simpa only [verticalTable_natural, faceMap_top, vertex] using h'

def cylinderCompositionZero (n : ℕ) : CylinderComposition.{u,v} (n+1) 0 where
  compose F G h := horizontalCylinder F G (zeroFaceMatching_seam h)
  endpoint_top F G h a := by
    rw [horizontalCylinder_endpoint]
    exact lift_top _ _

namespace CylinderComposition
variable {n k : ℕ} (C : CylinderComposition.{u,v} n k) (hk : k < n)
    {Y : OmegaCategory.{v}} (F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y)
    (h : FaceMatching (k+1) F G)

def secondDiagonal : OmegaCategory.Functor (K.{u} n).nu
    (Y.homCategory (F.map (atEnd false (vertex n false))) (F.map (atEnd true (vertex n true)))) :=
  homCast (rectangleDiagramOfFunctor G).diagonal (h.vertices false false).symm (h.vertices true true).symm

lemma diagonal_matching : FaceMatching k (rectangleDiagramOfFunctor F).diagonal (secondDiagonal F G h) := by
  intro x
  apply Subtype.ext
  change F.map (up ((faceMap n k true).cylinder.nu.map x)) =
    G.map (up ((faceMap n k false).cylinder.nu.map x))
  rw [← tensorFace_up, ← tensorFace_up]
  exact h (up x)

def positiveEnds (a : Bool) : OmegaCategory.Functor (complex.{u} (n+1)).nu Y :=
  globeComposite (Nat.add_lt_add_right hk 1) ((rectangleDiagramOfFunctor F).ends a)
    ((rectangleDiagramOfFunctor G).ends a) (h.ends a)

lemma positiveEnds_vertex (a b : Bool) :
    (positiveEnds hk F G h a).map (vertex n b) = F.map (atEnd a (vertex n b)) :=
  globeComposite_vertex hk _ _ _ b

def positiveDiagram : RectangleDiagram.{u,v} n Y :=
  rectangleDiagramOfTop (positiveEnds hk F G h)
    (rectangleDiagramOfFunctor F).edge (rectangleDiagramOfFunctor F).edge_fixed
    (fun a => ((rectangleDiagramOfFunctor F).edge_source a).trans (positiveEnds_vertex hk F G h false a).symm)
    (fun a => ((rectangleDiagramOfFunctor F).edge_target a).trans (positiveEnds_vertex hk F G h true a).symm)
    (homCast (C.compose (rectangleDiagramOfFunctor F).diagonal (secondDiagonal F G h)
      (diagonal_matching F G h))
      (positiveEnds_vertex hk F G h false false).symm (positiveEnds_vertex hk F G h true true).symm)
    (by
      change ((C.compose (rectangleDiagramOfFunctor F).diagonal (secondDiagonal F G h)
        (diagonal_matching F G h)).map (atEnd false (topTable n))).val = _
      erw [C.endpoint_top, hom_join_val _ _ _ ((diagonal_matching F G h).ends false)]
      change Y.join (k+1) ((rectangleDiagramOfFunctor F).diagonal.map (atEnd false (topTable n))).val
        ((rectangleDiagramOfFunctor G).diagonal.map (atEnd false (topTable n))).val = _
      rw [(rectangleDiagramOfFunctor F).left, (rectangleDiagramOfFunctor G).left, suspendTable_top]
      change Y.join (k+1) (Y.join 0 _ _) (Y.join 0 _ _) =
        Y.join 0 ((rectangleDiagramOfFunctor F).edge false)
          ((globeComposite _ _ _ _).map (topTable (n+1)))
      erw [globeComposite_top]
      have hedge : (rectangleDiagramOfFunctor G).edge false = (rectangleDiagramOfFunctor F).edge false :=
        (h.edges false).symm
      rw [hedge]
      exact (Y.join_whisker_left 0 (k+1) (by omega) _ _ _
        (Y.source_fixed_upwards (show 1 ≤ k+1 by omega) ((rectangleDiagramOfFunctor F).edge_fixed false))
        (h.ends true) (by
          have hh := (rectangleDiagramOfFunctor F).edge_end_matching (topTable n)
          rw [suspendTable_top] at hh
          exact hh)
        (by
          rw [← hedge]
          have hh := (rectangleDiagramOfFunctor G).edge_end_matching (topTable n)
          rw [suspendTable_top] at hh
          exact hh)).symm)
    (by
      change ((C.compose (rectangleDiagramOfFunctor F).diagonal (secondDiagonal F G h)
        (diagonal_matching F G h)).map (atEnd true (topTable n))).val = _
      erw [C.endpoint_top, hom_join_val _ _ _ ((diagonal_matching F G h).ends true)]
      change Y.join (k+1) ((rectangleDiagramOfFunctor F).diagonal.map (atEnd true (topTable n))).val
        ((rectangleDiagramOfFunctor G).diagonal.map (atEnd true (topTable n))).val = _
      rw [(rectangleDiagramOfFunctor F).right, (rectangleDiagramOfFunctor G).right, suspendTable_top]
      change Y.join (k+1) (Y.join 0 _ _) (Y.join 0 _ _) =
        Y.join 0 ((globeComposite _ _ _ _).map (topTable (n+1)))
          ((rectangleDiagramOfFunctor F).edge true)
      erw [globeComposite_top]
      have hedge : (rectangleDiagramOfFunctor G).edge true = (rectangleDiagramOfFunctor F).edge true :=
        (h.edges true).symm
      rw [hedge]
      exact (Y.join_whisker_right 0 (k+1) (by omega) _ _ _
        (Y.source_fixed_upwards (show 1 ≤ k+1 by omega) ((rectangleDiagramOfFunctor F).edge_fixed true))
        (h.ends false) (by
          have hh := (rectangleDiagramOfFunctor F).end_edge_matching (topTable n)
          rw [suspendTable_top] at hh
          exact hh)
        (by
          rw [← hedge]
          have hh := (rectangleDiagramOfFunctor G).end_edge_matching (topTable n)
          rw [suspendTable_top] at hh
          exact hh)).symm)

def succ : CylinderComposition.{u,v} (n+1) (k+1) where
  compose F G h := (C.positiveDiagram hk F G h).lift
  endpoint_top F G h a := by
    erw [RectangleDiagram.lift_endpoint]
    change (globeComposite (Nat.add_lt_add_right hk 1) _ _ (h.ends a)).map (topTable (n+1)) = _
    erw [globeComposite_top]
    rfl

end CylinderComposition

def cylinderComposition (n k : ℕ) (hk : k < n) : CylinderComposition.{u,v} n k :=
  match n, k with
  | 0, _ => False.elim (by omega)
  | n+1, 0 => cylinderCompositionZero n
  | n+1, k+1 => (cylinderComposition n k (by omega)).succ (by omega)

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

abbrev pasteCylinder {n k : ℕ} (hk : k < n) {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : FaceMatching k F G) :=
  (cylinderComposition n k hk).compose F G h

lemma pasteCylinder_endpoint_top {n k : ℕ} (hk : k < n) {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : FaceMatching k F G) (a : Bool) :
    (pasteCylinder hk F G h).map (atEnd a (topTable n)) =
      Y.join k (F.map (atEnd a (topTable n))) (G.map (atEnd a (topTable n))) :=
  (cylinderComposition n k hk).endpoint_top F G h a

lemma pasteCylinder_endpoint {n k : ℕ} (hk : k < n) {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : FaceMatching k F G)
    (a : Bool) (x : Table (complex.{u} n)) :
    (pasteCylinder hk F G h).map (atEnd a x) =
      (globeComposite hk
        (OmegaCategory.Functor.comp ((complex n).cylinderEndpoint a).nu F)
        (OmegaCategory.Functor.comp ((complex n).cylinderEndpoint a).nu G) (h.ends a)).map x :=
  (cylinderComposition n k hk).endpoint hk F G h a x

lemma pasteCylinder_zero {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y) (h : FaceMatching 0 F G) :
    pasteCylinder (show 0 < n+1 by omega) F G h =
      horizontalCylinder F G (zeroFaceMatching_seam h) := rfl

lemma pasteCylinder_succ_edge {n k : ℕ} (hk : k < n) {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y) (h : FaceMatching (k+1) F G) (a : Bool) :
    (pasteCylinder (Nat.add_lt_add_right hk 1) F G h).map (verticalTable (vertex n a)) =
      F.map (verticalTable (vertex n a)) := RectangleDiagram.lift_edge _ _

lemma pasteCylinder_succ_up {n k : ℕ} (hk : k < n) {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y) (h : FaceMatching (k+1) F G)
    (x : Table (K.{u} n)) :
    (pasteCylinder (Nat.add_lt_add_right hk 1) F G h).map (up x) =
      ((pasteCylinder hk (rectangleDiagramOfFunctor F).diagonal (CylinderComposition.secondDiagonal F G h)
        (CylinderComposition.diagonal_matching F G h)).map x).val := RectangleDiagram.lift_up _ _

lemma pasteCylinder_natural (n k : ℕ) (hk : k < n) {Y : OmegaCategory.{v}} {Z : OmegaCategory.{w}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : FaceMatching k F G)
    (P : OmegaCategory.Functor Y Z) :
    OmegaCategory.Functor.comp (pasteCylinder hk F G h) P =
      pasteCylinder hk (OmegaCategory.Functor.comp F P) (OmegaCategory.Functor.comp G P) (h.natural P) := by
  induction k generalizing n Y Z with
  | zero =>
    cases n with
    | zero => omega
    | succ n =>
      rw [pasteCylinder_zero, pasteCylinder_zero]
      exact horizontalCylinder_natural F G _ P
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      have hk' : k < n := by omega
      apply functor_ext_rectangle
      · intro a x
        change P.map ((pasteCylinder hk F G h).map (atEnd a x)) = _
        rw [pasteCylinder_endpoint, pasteCylinder_endpoint]
        exact congrArg (fun U => U.map x) (globeComposite_natural hk
          (OmegaCategory.Functor.comp ((complex (n+1)).cylinderEndpoint a).nu F)
          (OmegaCategory.Functor.comp ((complex (n+1)).cylinderEndpoint a).nu G) (h.ends a) P)
      · intro a
        change P.map ((pasteCylinder hk F G h).map (verticalTable (vertex n a))) = _
        rw [pasteCylinder_succ_edge hk', pasteCylinder_succ_edge hk']
        rfl
      · intro x
        change P.map ((pasteCylinder hk F G h).map (up x)) = _
        rw [pasteCylinder_succ_up hk', pasteCylinder_succ_up hk']
        have he := ih n hk' (rectangleDiagramOfFunctor F).diagonal
          (CylinderComposition.secondDiagonal F G h) (CylinderComposition.diagonal_matching F G h)
          (P.homMap (F.map (atEnd false (vertex n false))) (F.map (atEnd true (vertex n true))))
        exact congrArg (fun U => (U.map x).val) he

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma globeSuspended_ext {n : ℕ} {Y : OmegaCategory.{v}} {a b : Y.Cell}
    (A : OmegaCategory.Functor (complex.{u} n).nu (Y.homCategory a b))
    (B : OmegaCategory.Functor (complex.{u} (n+1)).nu Y)
    (h : (A.map (topTable n)).val = B.map (topTable (n+1))) (x : Table (complex.{u} n)) :
    (A.map x).val = B.map (suspendTable x) := by
  obtain ⟨p,c,hp,he⟩ := table_classification x
  rw [he, suspendTable_eq_face]
  erw [← face_nu n p c (topTable n), A.map_face,
    ← face_nu (n+1) (p+1) c (topTable (n+1)), B.map_face]
  cases c
  · change Y.source (p+1) (A.map (topTable n)).val = Y.source (p+1) (B.map (topTable (n+1)))
    rw [h]
  · change Y.target (p+1) (A.map (topTable n)).val = Y.target (p+1) (B.map (topTable (n+1)))
    rw [h]

lemma constantInterval_faceMatching {n k : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex.{u} n).nu Y)
    (h : Y.target k (F.map (topTable n)) = Y.source k (G.map (topTable n))) :
    FaceMatching k (constantInterval F) (constantInterval G) := by
  have he : OmegaCategory.Functor.comp (faceMap n k true).nu F =
      OmegaCategory.Functor.comp (faceMap n k false).nu G := by
    apply GlobeComplex.functor_ext
    change F.map ((faceMap n k true).nu.map (topTable k)) =
      G.map ((faceMap n k false).nu.map (topTable k))
    rw [faceMap_top, faceMap_top]
    exact (F.map_target k (topTable n)).trans (h.trans (G.map_source k (topTable n)).symm)
  intro x
  have h₀ := congrArg (fun U => U.nu.map x) (faceMap.{u} n k true).cylinder_projection
  have h₁ := congrArg (fun U => U.nu.map x) (faceMap.{u} n k false).cylinder_projection
  change project ((faceMap n k true).cylinder.nu.map x) = (faceMap n k true).nu.map (project x) at h₀
  change project ((faceMap n k false).cylinder.nu.map x) = (faceMap n k false).nu.map (project x) at h₁
  erw [constantInterval_map F, constantInterval_map G, h₀, h₁]
  exact congrArg (fun U => U.map (project x)) he

lemma pasteCylinder_constant (n k : ℕ) (hk : k < n) {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex.{u} n).nu Y)
    (h : Y.target k (F.map (topTable n)) = Y.source k (G.map (topTable n))) :
    pasteCylinder hk (constantInterval F) (constantInterval G) (constantInterval_faceMatching F G h) =
      constantInterval (globeComposite hk F G h) := by
  induction k generalizing n Y with
  | zero =>
    cases n with
    | zero => omega
    | succ n =>
      have h' : F.map (vertex n true) = G.map (vertex n false) := by
        erw [← F.map_target, ← G.map_source] at h
        exact h
      rw [pasteCylinder_zero, horizontalCylinder_constant F G h']
      rfl
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      have hk' : k < n := by omega
      let hc := constantInterval_faceMatching F G h
      apply functor_ext_rectangle
      · intro a x
        rw [pasteCylinder_endpoint, constantInterval_endpoint]
        have hF : OmegaCategory.Functor.comp ((complex (n+1)).cylinderEndpoint a).nu (constantInterval F) = F :=
          constantInterval_ends F a
        have hG : OmegaCategory.Functor.comp ((complex (n+1)).cylinderEndpoint a).nu (constantInterval G) = G :=
          constantInterval_ends G a
        simp only [hF, hG]
      · intro a
        rw [pasteCylinder_succ_edge hk', constantInterval_edge, constantInterval_edge]
        exact (globeComposite_vertex hk' F G h a).symm
      · intro x
        rw [pasteCylinder_succ_up hk', constantInterval_up]
        let A := homCast (globeHomMap F)
          (constantInterval_endpoint F false (vertex n false)).symm
          (constantInterval_endpoint F true (vertex n true)).symm
        let B := homCast (globeHomMap G)
          ((globeMatching_vertex F G h false).symm.trans (constantInterval_endpoint F false (vertex n false)).symm)
          ((globeMatching_vertex F G h true).symm.trans (constantInterval_endpoint F true (vertex n true)).symm)
        have hA : (rectangleDiagramOfFunctor (constantInterval F)).diagonal = constantInterval A := by
          apply OmegaCategory.Functor.ext
          funext y
          apply Subtype.ext
          exact constantInterval_up F y
        have hB : CylinderComposition.secondDiagonal (constantInterval F) (constantInterval G) hc =
            constantInterval B := by
          apply OmegaCategory.Functor.ext
          funext y
          apply Subtype.ext
          exact constantInterval_up G y
        have hAB : (Y.homCategory ((constantInterval F).map (atEnd false (vertex n false)))
            ((constantInterval F).map (atEnd true (vertex n true)))).target k (A.map (topTable n)) =
            (Y.homCategory ((constantInterval F).map (atEnd false (vertex n false)))
            ((constantInterval F).map (atEnd true (vertex n true)))).source k (B.map (topTable n)) := by
          apply Subtype.ext
          change Y.target (k+1) (F.map (suspendTable (topTable n))) =
            Y.source (k+1) (G.map (suspendTable (topTable n)))
          rw [suspendTable_top]
          exact h
        simp only [hA, hB]
        erw [ih n hk' A B hAB]
        rw [constantInterval_map]
        apply globeSuspended_ext _ (globeComposite hk F G h)
        rw [globeComposite_top, hom_join_val _ _ _ hAB, globeComposite_top]
        change Y.join (k+1) (F.map (suspendTable (topTable n))) (G.map (suspendTable (topTable n))) = _
        rw [suspendTable_top]

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory Limits DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

namespace RectangleDiagram
@[ext] lemma ext {n : ℕ} {Y : OmegaCategory.{v}} {D E : RectangleDiagram.{u,v} n Y}
    (he : D.ends = E.ends) (hv : D.edge = E.edge)
    (hd : ∀ x, (D.diagonal.map x).val = (E.diagonal.map x).val) : D = E := by
  cases D
  cases E
  cases he
  cases hv
  congr 1
  apply OmegaCategory.Functor.ext
  funext x
  exact Subtype.ext (hd x)

@[simp] lemma ofFunctor_lift {n : ℕ} {Y : OmegaCategory.{v}} (D : RectangleDiagram.{u,v} n Y) :
    rectangleDiagramOfFunctor D.lift = D := by
  apply ext
  · funext a
    apply OmegaCategory.Functor.ext
    funext x
    exact D.lift_endpoint a x
  · funext a
    exact D.lift_edge a
  · intro x
    exact D.lift_up x
end RectangleDiagram

namespace IntervalMatching
variable {n : ℕ} {Y : OmegaCategory.{v}} {F G H : OmegaCategory.Functor (K.{u} n).nu Y}
lemma concat_left (h : IntervalMatching F G) (i : IntervalMatching G H) :
    IntervalMatching (concatInterval F G h) H := by
  intro x
  rw [concatInterval_endpoint]
  exact i x
lemma concat_right (h : IntervalMatching F G) (i : IntervalMatching G H) :
    IntervalMatching F (concatInterval G H i) := by
  intro x
  rw [concatInterval_endpoint]
  exact h x
end IntervalMatching

abbrev pairFunctor {X Y Z : OmegaCategory.{u}} (F : X ⟶ Y) (G : X ⟶ Z) :
    X ⟶ Y ⨯ Z := prod.lift F G

lemma concatInterval_pair {n : ℕ} {Y Z : OmegaCategory.{u}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : IntervalMatching F G)
    (F' G' : OmegaCategory.Functor (K.{u} n).nu Z) (h' : IntervalMatching F' G')
    (H : IntervalMatching (pairFunctor F F') (pairFunctor G G')) :
    concatInterval (pairFunctor F F') (pairFunctor G G') H =
      pairFunctor (concatInterval F G h) (concatInterval F' G' h') := by
  apply @prod.hom_ext OmegaCategory.{u} _ ((K n).nu) Y Z _
  · change OmegaCategory.Functor.comp (concatInterval _ _ H) (prod.fst : Y ⨯ Z ⟶ Y) = _
    rw [concatInterval_natural]
    change concatInterval ((pairFunctor F F') ≫ prod.fst) ((pairFunctor G G') ≫ prod.fst) _ = _
    simp only [pairFunctor, prod.lift_fst]
  · change OmegaCategory.Functor.comp (concatInterval _ _ H) (prod.snd : Y ⨯ Z ⟶ Z) = _
    rw [concatInterval_natural]
    change concatInterval ((pairFunctor F F') ≫ prod.snd) ((pairFunctor G G') ≫ prod.snd) _ = _
    simp only [pairFunctor, prod.lift_snd]

lemma IntervalMatching.pair {n : ℕ} {Y Z : OmegaCategory.{u}}
    {F G : OmegaCategory.Functor (K.{u} n).nu Y} (h : IntervalMatching F G)
    {F' G' : OmegaCategory.Functor (K.{u} n).nu Z} (h' : IntervalMatching F' G') :
    IntervalMatching (pairFunctor F F') (pairFunctor G G') := by
  have he : ((complex n).cylinderEndpoint true).nu ≫ pairFunctor F F' =
      ((complex n).cylinderEndpoint false).nu ≫ pairFunctor G G' := by
    apply prod.hom_ext <;> simp only [Category.assoc, pairFunctor, prod.lift_fst, prod.lift_snd]
    · exact OmegaCategory.Functor.ext (funext h)
    · exact OmegaCategory.Functor.ext (funext h')
  exact fun x => congrArg (fun f => f.map x) he

lemma concatInterval_homCompose {n : ℕ} {Y : OmegaCategory.{u}} {a b c : Y.Cell}
    (F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory a b)) (h : IntervalMatching F G)
    (F' G' : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory b c)) (h' : IntervalMatching F' G') :
    concatInterval (homCompose F F') (homCompose G G')
      (fun x => by apply Subtype.ext
                   change Y.join 0 (F.map (atEnd true x)).val (F'.map (atEnd true x)).val = _
                   rw [h x, h' x]; rfl) =
      homCompose (concatInterval F G h) (concatInterval F' G' h') := by
  let P : (Y.homCategory a b ⨯ Y.homCategory b c) ⟶ Y.homCategory a c :=
    homCompose (prod.fst : (Y.homCategory a b ⨯ Y.homCategory b c) ⟶ _) (prod.snd : (Y.homCategory a b ⨯ Y.homCategory b c) ⟶ _)
  have hp (A : (K.{u} n).nu ⟶ Y.homCategory a b)
      (B : (K.{u} n).nu ⟶ Y.homCategory b c) :
      pairFunctor A B ≫ P = homCompose A B := by
    apply OmegaCategory.Functor.ext
    funext x
    apply Subtype.ext
    change Y.join 0 ((pairFunctor A B ≫ prod.fst).map x).val
      ((pairFunctor A B ≫ prod.snd).map x).val = _
    change Y.join 0 ((prod.lift A B ≫ prod.fst).map x).val ((prod.lift A B ≫ prod.snd).map x).val = _
    rw [prod.lift_fst, prod.lift_snd]
    rfl
  have he := concatInterval_natural n (pairFunctor F F') (pairFunctor G G') (h.pair h') P
  change concatInterval _ _ _ ≫ P = concatInterval (pairFunctor F F' ≫ P) (pairFunctor G G' ≫ P) _ at he
  simp only [concatInterval_pair F G h F' G' h', hp] at he
  exact he.symm

lemma IntervalMatching.constantAt {n : ℕ} {Y : OmegaCategory.{v}} (a : Y.Cell)
    (ha : Y.source 0 a = a) :
    IntervalMatching (constantAt (K.{u} n).nu a ha) (constantAt (K.{u} n).nu a ha) :=
  fun _ => rfl

@[simp] lemma concatInterval_constantAt {n : ℕ} {Y : OmegaCategory.{v}} (a : Y.Cell)
    (ha : Y.source 0 a = a) (h : IntervalMatching (constantAt (K.{u} n).nu a ha) (constantAt (K.{u} n).nu a ha)) :
    concatInterval (constantAt (K.{u} n).nu a ha) (constantAt (K.{u} n).nu a ha) h =
      constantAt (K.{u} n).nu a ha :=
  concatInterval_constant n (constantAt (complex n).nu a ha)

lemma concatInterval_val_congr {n : ℕ} {Y : OmegaCategory.{v}} {a b c d : Y.Cell}
    (F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory a b)) (h : IntervalMatching F G)
    (F' G' : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory c d)) (h' : IntervalMatching F' G')
    (he : ∀ x, (F.map x).val = (F'.map x).val)
    (hf : ∀ x, (G.map x).val = (G'.map x).val) (x : Table (K.{u} n)) :
    ((concatInterval F G h).map x).val = ((concatInterval F' G' h').map x).val := by
  have hac : a = c := (F.map x).property.1.symm.trans
    ((congrArg (Y.source 0) (he x)).trans (F'.map x).property.1)
  have hbd : b = d := (F.map x).property.2.symm.trans
    ((congrArg (Y.target 0) (he x)).trans (F'.map x).property.2)
  subst c d
  have hF : F = F' := OmegaCategory.Functor.ext (funext (fun z => Subtype.ext (he z)))
  have hG : G = G' := OmegaCategory.Functor.ext (funext (fun z => Subtype.ext (hf z)))
  subst F' G'
  rfl

lemma concatInterval_homCompose_left {n : ℕ} {Y : OmegaCategory.{u}} {a b c : Y.Cell}
    (f : Y.Cell) (hf : Y.source 1 f = f) (hs : Y.source 0 f = a) (ht : Y.target 0 f = b)
    (F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory b c)) (h : IntervalMatching F G)
    (h' : IntervalMatching (homCompose (constantHom (K n).nu f hf hs ht) F)
      (homCompose (constantHom (K n).nu f hf hs ht) G)) :
    concatInterval (homCompose (constantHom (K n).nu f hf hs ht) F)
      (homCompose (constantHom (K n).nu f hf hs ht) G) h' =
      homCompose (constantHom (K n).nu f hf hs ht) (concatInterval F G h) := by
  have e := concatInterval_homCompose (constantHom (K n).nu f hf hs ht)
    (constantHom (K n).nu f hf hs ht) (IntervalMatching.constantAt (Y := Y.homCategory a b) ⟨f, hs, ht⟩ (Subtype.ext hf)) F G h
  exact e.trans (congrArg (fun A => homCompose A (concatInterval F G h))
    (concatInterval_constantAt (Y := Y.homCategory a b) ⟨f, hs, ht⟩ (Subtype.ext hf) _))

lemma concatInterval_homCompose_right {n : ℕ} {Y : OmegaCategory.{u}} {a b c : Y.Cell}
    (F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory a b)) (h : IntervalMatching F G)
    (f : Y.Cell) (hf : Y.source 1 f = f) (hs : Y.source 0 f = b) (ht : Y.target 0 f = c)
    (h' : IntervalMatching (homCompose F (constantHom (K n).nu f hf hs ht))
      (homCompose G (constantHom (K n).nu f hf hs ht))) :
    concatInterval (homCompose F (constantHom (K n).nu f hf hs ht))
      (homCompose G (constantHom (K n).nu f hf hs ht)) h' =
      homCompose (concatInterval F G h) (constantHom (K n).nu f hf hs ht) := by
  have e := concatInterval_homCompose F G h (constantHom (K n).nu f hf hs ht)
    (constantHom (K n).nu f hf hs ht) (IntervalMatching.constantAt (Y := Y.homCategory b c) ⟨f, hs, ht⟩ (Subtype.ext hf))
  exact e.trans (congrArg (fun B => homCompose (concatInterval F G h) B)
    (concatInterval_constantAt (Y := Y.homCategory b c) ⟨f, hs, ht⟩ (Subtype.ext hf) _))

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

def IntervalAssociative (n : ℕ) : Prop :=
  ∀ {Y : OmegaCategory.{u}} (F G H : OmegaCategory.Functor (K.{u} n).nu Y)
    (h : IntervalMatching F G) (i : IntervalMatching G H),
    concatInterval (concatInterval F G h) H (h.concat_left i) =
      concatInterval F (concatInterval G H i) (h.concat_right i)

namespace RectangleDiagram
variable {n : ℕ} {Y : OmegaCategory.{u}}
    (D E S : RectangleDiagram.{u,u} n Y)
    (h : ∀ x, (D.ends true).map x = (E.ends false).map x)
    (i : ∀ x, (E.ends true).map x = (S.ends false).map x)

def assocLeft : OmegaCategory.Functor (K.{u} n).nu
    (Y.homCategory ((D.ends false).map (vertex n false)) ((E.ends false).map (vertex n false))) :=
  constantHom _ (D.edge false) (D.edge_fixed false) (D.edge_source false)
    ((D.edge_target false).trans (h _))

def assocRight : OmegaCategory.Functor (K.{u} n).nu
    (Y.homCategory ((E.ends true).map (vertex n true)) ((S.ends true).map (vertex n true))) :=
  constantHom _ (S.edge true) (S.edge_fixed true)
    ((S.edge_source true).trans (i _).symm) (S.edge_target true)

def assocA := homCompose (D.assocLeft E h) (E.concatDiagonalOne S i)
def assocB := homCompose (D.assocLeft E h) (E.concatDiagonalTwo S i)
def assocC := homCompose (D.concatDiagonalTwo E h) (E.assocRight S i)

lemma assocB_map (x : Table (K.{u} n)) :
    ((D.assocB E S h i).map x).val =
      ((homCompose (D.concatDiagonalOne E h) (E.assocRight S i)).map x).val := by
  change Y.join 0 (D.edge false) (Y.join 0 (E.diagonal.map x).val (S.edge true)) =
    Y.join 0 (Y.join 0 (D.edge false) (E.diagonal.map x).val) (S.edge true)
  exact (Y.join_assoc 0 _ _ _
    ((D.edge_target false).trans ((h _).trans (E.diagonal.map x).property.1.symm))
    ((E.diagonal.map x).property.2.trans ((i _).trans (S.edge_source true).symm))).symm

lemma assocAB : IntervalMatching (D.assocA E S h i) (D.assocB E S h i) := by
  intro x
  apply Subtype.ext
  change Y.join 0 (D.edge false) ((E.concatDiagonalOne S i).map (atEnd true x)).val =
    Y.join 0 (D.edge false) ((E.concatDiagonalTwo S i).map (atEnd false x)).val
  rw [E.concatDiagonal_matching S i x]

lemma assocBC : IntervalMatching (D.assocB E S h i) (D.assocC E S h i) := by
  intro x
  apply Subtype.ext
  rw [D.assocB_map E S h i]
  change Y.join 0 ((D.concatDiagonalOne E h).map (atEnd true x)).val (S.edge true) =
    Y.join 0 ((D.concatDiagonalTwo E h).map (atEnd false x)).val (S.edge true)
  rw [D.concatDiagonal_matching E h x]

lemma concat_one_assoc :
    (D.concat E h (intervalComposition n)).concatDiagonalOne S i = D.assocA E S h i := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change Y.join 0 (Y.join 0 (D.edge false) (E.edge false)) (S.diagonal.map x).val =
    Y.join 0 (D.edge false) (Y.join 0 (E.edge false) (S.diagonal.map x).val)
  exact Y.join_assoc 0 _ _ _ (D.seam_edge E h false)
    ((E.edge_target false).trans ((i _).trans (S.diagonal.map x).property.1.symm))

lemma concat_two_assoc :
    (D.concat E h (intervalComposition n)).concatDiagonalTwo S i =
      concatInterval (D.assocB E S h i) (D.assocC E S h i) (D.assocBC E S h i) := by
  have hb : D.assocB E S h i = homCompose (D.concatDiagonalOne E h) (E.assocRight S i) :=
    OmegaCategory.Functor.ext (funext (fun x => Subtype.ext (D.assocB_map E S h i x)))
  have hm : IntervalMatching (homCompose (D.concatDiagonalOne E h) (E.assocRight S i))
      (homCompose (D.concatDiagonalTwo E h) (E.assocRight S i)) := by
    simpa only [assocC, ← hb] using D.assocBC E S h i
  have he := concatInterval_homCompose_right
    (D.concatDiagonalOne E h) (D.concatDiagonalTwo E h) (D.concatDiagonal_matching E h)
    (S.edge true) (S.edge_fixed true) ((S.edge_source true).trans (i _).symm) (S.edge_target true) hm
  simp only [show constantHom (K n).nu (S.edge true) (S.edge_fixed true)
    ((S.edge_source true).trans (i _).symm) (S.edge_target true) = E.assocRight S i from rfl, ← hb] at he
  exact he.symm

lemma concat_one_assoc' :
    D.concatDiagonalOne (E.concat S i (intervalComposition n)) h =
      concatInterval (D.assocA E S h i) (D.assocB E S h i) (D.assocAB E S h i) := by
  exact (concatInterval_homCompose_left
    (D.edge false) (D.edge_fixed false) (D.edge_source false) ((D.edge_target false).trans (h _))
    (E.concatDiagonalOne S i) (E.concatDiagonalTwo S i) (E.concatDiagonal_matching S i)
    (D.assocAB E S h i)).symm

lemma concat_two_assoc' :
    D.concatDiagonalTwo (E.concat S i (intervalComposition n)) h = D.assocC E S h i := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change Y.join 0 (D.diagonal.map x).val (Y.join 0 (E.edge true) (S.edge true)) =
    Y.join 0 (Y.join 0 (D.diagonal.map x).val (E.edge true)) (S.edge true)
  exact (Y.join_assoc 0 _ _ _
    ((D.diagonal.map x).property.2.trans ((h _).trans (E.edge_source true).symm))
    (E.seam_edge S i true)).symm

lemma concat_assoc (ih : IntervalAssociative.{u} n) :
    (D.concat E h (intervalComposition n)).concat S i (intervalComposition n) =
      D.concat (E.concat S i (intervalComposition n)) h (intervalComposition n) := by
  apply RectangleDiagram.ext
  · funext a
    cases a <;> rfl
  · funext a
    exact Y.join_assoc 0 _ _ _ (D.seam_edge E h a) (E.seam_edge S i a)
  · intro x
    change ((concatInterval ((D.concat E h (intervalComposition n)).concatDiagonalOne S i)
      ((D.concat E h (intervalComposition n)).concatDiagonalTwo S i) _).map x).val =
      ((concatInterval (D.concatDiagonalOne (E.concat S i (intervalComposition n)) h)
        (D.concatDiagonalTwo (E.concat S i (intervalComposition n)) h) _).map x).val
    simp only [concat_one_assoc, concat_two_assoc, concat_one_assoc', concat_two_assoc']
    exact congrArg (fun F => (F.map x).val)
      (ih (D.assocA E S h i) (D.assocB E S h i) (D.assocC E S h i)
        (D.assocAB E S h i) (D.assocBC E S h i)).symm

end RectangleDiagram

lemma concatInterval_associative (n : ℕ) : IntervalAssociative.{u} n := by
  induction n with
  | zero =>
    intro Y F G H h i
    apply OmegaCategory.Functor.ext
    funext x
    rcases table_zero_cases x with ⟨a,he⟩ | he
    · rw [he]
      simp only [concatInterval_endpoint]
      cases a <;> rfl
    · rw [he]
      simp only [concatInterval_zero_vertical]
      exact Y.join_assoc 0 _ _ _ (zero_interval_seam F G h) (zero_interval_seam G H i)
  | succ n ih =>
    intro Y F G H h i
    have he := (rectangleDiagramOfFunctor F).concat_assoc (rectangleDiagramOfFunctor G)
      (rectangleDiagramOfFunctor H) h i ih
    change (((rectangleDiagramOfFunctor (concatInterval F G h)).concat
      (rectangleDiagramOfFunctor H) _ (intervalComposition n)).lift) =
      (((rectangleDiagramOfFunctor F).concat (rectangleDiagramOfFunctor (concatInterval G H i))
        _ (intervalComposition n)).lift)
    simp only [show concatInterval F G h = ((rectangleDiagramOfFunctor F).concat
      (rectangleDiagramOfFunctor G) h (intervalComposition n)).lift from rfl,
      show concatInterval G H i = ((rectangleDiagramOfFunctor G).concat
        (rectangleDiagramOfFunctor H) i (intervalComposition n)).lift from rfl,
      RectangleDiagram.ofFunctor_lift]
    exact congrArg RectangleDiagram.lift he
end Thomason.GrayRecursive

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_StationaryCylinders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stationary Cylinders. -/

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

def endGlobe {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) (a : Bool) :
    OmegaCategory.Functor (complex.{u} n).nu Y :=
  OmegaCategory.Functor.comp ((complex n).cylinderEndpoint a).nu F

@[simp] lemma endGlobe_map {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) (a : Bool) (x : Table (complex.{u} n)) :
    (endGlobe F a).map x = F.map (atEnd a x) := rfl

lemma stationary_left_matching {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) :
    IntervalMatching (constantInterval (endGlobe F false)) F := by
  intro x
  exact constantInterval_endpoint _ _ _

lemma stationary_right_matching {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) :
    IntervalMatching F (constantInterval (endGlobe F true)) := by
  intro x
  exact (constantInterval_endpoint (endGlobe F true) false x).symm

def IntervalUnits (n : ℕ) : Prop :=
  ∀ {Y : OmegaCategory.{v}} (F : OmegaCategory.Functor (K.{u} n).nu Y),
    concatInterval (constantInterval (endGlobe F false)) F (stationary_left_matching F) = F ∧
    concatInterval F (constantInterval (endGlobe F true)) (stationary_right_matching F) = F

lemma zero_vertical_source {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} 0).nu Y) :
    Y.source 0 (F.map (verticalTable (topTable 0))) = F.map (atEnd false (topTable 0)) := by
  have h := zeroCylinderMap.map_source 0 (topTable.{u} 1)
  change zeroCylinderMap.map (vertex 0 false) = _ at h
  rw [zeroCylinderMap_vertex, zeroCylinderMap_top] at h
  exact (F.map_source _ _).symm.trans (congrArg F.map h.symm)
lemma zero_vertical_target {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} 0).nu Y) :
    Y.target 0 (F.map (verticalTable (topTable 0))) = F.map (atEnd true (topTable 0)) := by
  have h := zeroCylinderMap.map_target 0 (topTable.{u} 1)
  change zeroCylinderMap.map (vertex 0 true) = _ at h
  rw [zeroCylinderMap_vertex, zeroCylinderMap_top] at h
  exact (F.map_target _ _).symm.trans (congrArg F.map h.symm)

namespace RectangleDiagram
variable {n : ℕ} {Y : OmegaCategory.{v}} (D : RectangleDiagram.{u,v} n Y)
lemma vertex_fixed (a b : Bool) :
    Y.source 0 ((D.ends a).map (vertex n b)) = (D.ends a).map (vertex n b) := by
  erw [← (D.ends a).map_source]
  exact congrArg (D.ends a).map (vertex_truncate n 0 b false)

lemma vertex_target_fixed (a b : Bool) :
    Y.target 0 ((D.ends a).map (vertex n b)) = (D.ends a).map (vertex n b) :=
  Y.target_eq_self_of_source_eq_self (D.vertex_fixed a b)
end RectangleDiagram

lemma concatInterval_units (n : ℕ) : IntervalUnits.{u,v} n := by
  induction n with
  | zero =>
    intro Y F
    constructor
    · apply OmegaCategory.Functor.ext
      funext x
      rcases table_zero_cases x with ⟨a,he⟩ | he
      · rw [he, concatInterval_endpoint]
        cases a <;> simp
      · rw [he, concatInterval_zero_vertical, constantInterval_map, project_zero_vertical,
          endGlobe_map, ← zero_vertical_source]
        exact Y.join_left_unit 0 _ _ (Y.source_source_self 0 _) (Y.target_source_self 0 _)
    · apply OmegaCategory.Functor.ext
      funext x
      rcases table_zero_cases x with ⟨a,he⟩ | he
      · rw [he, concatInterval_endpoint]
        cases a <;> simp
      · rw [he, concatInterval_zero_vertical, constantInterval_map, project_zero_vertical,
          endGlobe_map, ← zero_vertical_target]
        exact Y.join_right_unit 0 _ _ (Y.source_target_self 0 _) (Y.source_target_self 0 _).symm
  | succ n ih =>
    intro Y F
    let D := rectangleDiagramOfFunctor F
    constructor
    · apply functor_ext_rectangle
      · intro a x
        rw [concatInterval_endpoint]
        cases a <;> simp
      · intro a
        rw [concatInterval_succ_edge, constantInterval_edge]
        change Y.join 0 ((D.ends false).map (vertex n a)) (D.edge a) = D.edge a
        apply Y.join_left_unit 0 _ _ (D.vertex_fixed false a)
        rw [D.vertex_target_fixed]
        exact (D.edge_source a).symm
      · intro x
        rw [concatInterval_succ_up]
        let E := rectangleDiagramOfFunctor (constantInterval (endGlobe F false))
        have hA (t : Table (K.{u} n)) :
            ((E.concatDiagonalOne D (stationary_left_matching F)).map t).val = (D.diagonal.map t).val := by
          change Y.join 0 ((constantInterval (endGlobe F false)).map (verticalTable (vertex n false)))
            (D.diagonal.map t).val = _
          rw [constantInterval_edge]
          change Y.join 0 ((D.ends false).map (vertex n false)) (D.diagonal.map t).val = _
          apply Y.join_left_unit 0 _ _ (D.vertex_fixed false false)
          rw [D.vertex_target_fixed]
          exact (D.diagonal.map t).property.1.symm
        have hB (t : Table (K.{u} n)) :
            ((E.concatDiagonalTwo D (stationary_left_matching F)).map t).val =
              ((constantInterval (endGlobe D.diagonal true)).map t).val := by
          change Y.join 0 ((constantInterval (endGlobe F false)).map (up t)) (D.edge true) =
            (D.diagonal.map (atEnd true (project t))).val
          rw [constantInterval_up, D.right]
          rfl
        have he := concatInterval_val_congr
          (E.concatDiagonalOne D (stationary_left_matching F))
          (E.concatDiagonalTwo D (stationary_left_matching F))
          (E.concatDiagonal_matching D (stationary_left_matching F))
          D.diagonal (constantInterval (endGlobe D.diagonal true))
          (stationary_right_matching D.diagonal) hA hB x
        exact he.trans (congrArg (fun A => (A.map x).val) (ih D.diagonal).2)
    · apply functor_ext_rectangle
      · intro a x
        rw [concatInterval_endpoint]
        cases a <;> simp
      · intro a
        rw [concatInterval_succ_edge, constantInterval_edge]
        change Y.join 0 (D.edge a) ((D.ends true).map (vertex n a)) = D.edge a
        exact Y.join_right_unit 0 _ _ (D.vertex_fixed true a)
          ((D.edge_target a).trans (D.vertex_fixed true a).symm)
      · intro x
        rw [concatInterval_succ_up]
        let E := rectangleDiagramOfFunctor (constantInterval (endGlobe F true))
        have hA (t : Table (K.{u} n)) :
            ((D.concatDiagonalOne E (stationary_right_matching F)).map t).val =
              ((constantInterval (endGlobe D.diagonal false)).map t).val := by
          change Y.join 0 (D.edge false) ((constantInterval (endGlobe F true)).map (up t)) =
            (D.diagonal.map (atEnd false (project t))).val
          rw [constantInterval_up, D.left]
          rfl
        have hB (t : Table (K.{u} n)) :
            ((D.concatDiagonalTwo E (stationary_right_matching F)).map t).val = (D.diagonal.map t).val := by
          change Y.join 0 (D.diagonal.map t).val
            ((constantInterval (endGlobe F true)).map (verticalTable (vertex n true))) = _
          rw [constantInterval_edge]
          change Y.join 0 (D.diagonal.map t).val ((D.ends true).map (vertex n true)) = _
          exact Y.join_right_unit 0 _ _ (D.vertex_fixed true true)
            ((D.diagonal.map t).property.2.trans (D.vertex_fixed true true).symm)
        have he := concatInterval_val_congr
          (D.concatDiagonalOne E (stationary_right_matching F))
          (D.concatDiagonalTwo E (stationary_right_matching F))
          (D.concatDiagonal_matching E (stationary_right_matching F))
          (constantInterval (endGlobe D.diagonal false)) D.diagonal
          (stationary_left_matching D.diagonal) hA hB x
        exact he.trans (congrArg (fun A => (A.map x).val) (ih D.diagonal).1)

lemma concatInterval_left_unit {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) :
    concatInterval (constantInterval (endGlobe F false)) F (stationary_left_matching F) = F :=
  (concatInterval_units n F).1
end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma concatInterval_homCompose_stationary_left {n : ℕ} {Y : OmegaCategory.{u}} {a b c : Y.Cell}
    (P : OmegaCategory.Functor (complex.{u} n).nu (Y.homCategory a b))
    (F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory b c)) (h : IntervalMatching F G)
    (h' : IntervalMatching (homCompose (constantInterval P) F) (homCompose (constantInterval P) G)) :
    concatInterval (homCompose (constantInterval P) F) (homCompose (constantInterval P) G) h' =
      homCompose (constantInterval P) (concatInterval F G h) := by
  have e := concatInterval_homCompose (constantInterval P) (constantInterval P)
    (constantInterval_matching P) F G h
  exact e.trans (congrArg (fun A => homCompose A (concatInterval F G h)) (concatInterval_constant n P))

lemma concatInterval_homCompose_stationary_right {n : ℕ} {Y : OmegaCategory.{u}} {a b c : Y.Cell}
    (F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory a b)) (h : IntervalMatching F G)
    (P : OmegaCategory.Functor (complex.{u} n).nu (Y.homCategory b c))
    (h' : IntervalMatching (homCompose F (constantInterval P)) (homCompose G (constantInterval P))) :
    concatInterval (homCompose F (constantInterval P)) (homCompose G (constantInterval P)) h' =
      homCompose (concatInterval F G h) (constantInterval P) := by
  have e := concatInterval_homCompose F G h (constantInterval P) (constantInterval P)
    (constantInterval_matching P)
  exact e.trans (congrArg (fun B => homCompose (concatInterval F G h) B) (concatInterval_constant n P))

namespace RectangleDiagram
variable {n : ℕ} {Y : OmegaCategory.{u}}
    (D E S : RectangleDiagram.{u,u} n Y) (h : D.edge true = E.edge false) (i : E.edge true = S.edge false)

namespace HorizontalAssociativity

def beforeGlobe : OmegaCategory.Functor (complex.{u} n).nu
    (Y.homCategory ((D.ends false).map (vertex n false)) ((E.ends false).map (vertex n false))) :=
  homCast (globeHomMap (D.ends false)) rfl (D.horizontal_seam E h false)

def suffix : OmegaCategory.Functor (complex.{u} n).nu
    (Y.homCategory ((E.ends true).map (vertex n true)) ((S.ends true).map (vertex n true))) :=
  homCast (globeHomMap (S.ends true)) (E.horizontal_seam S i true).symm rfl

def A := homCompose (D.horizontalDiagonalOne E h) (constantInterval (suffix E S i))
def B := homCompose (D.horizontalDiagonalTwo E h) (constantInterval (suffix E S i))
def C := homCompose (constantInterval (beforeGlobe D E h)) (E.horizontalDiagonalTwo S i)

lemma B_map (x : Table (K.{u} n)) :
    ((B D E S h i).map x).val =
      ((homCompose (constantInterval (beforeGlobe D E h)) (E.horizontalDiagonalOne S i)).map x).val := by
  change Y.join 0 (Y.join 0 ((D.ends false).map (suspendTable (project x))) (E.diagonal.map x).val)
    ((S.ends true).map (suspendTable (project x))) =
      Y.join 0 ((D.ends false).map (suspendTable (project x)))
        (Y.join 0 (E.diagonal.map x).val ((S.ends true).map (suspendTable (project x))))
  apply Y.join_assoc 0
  · erw [← (D.ends false).map_target]
    change (D.ends false).map (truncate 0 true (suspendTable (project x))) = _
    rw [suspend_truncate_zero, D.horizontal_seam E h]
    exact (E.diagonal.map x).property.1.symm
  · erw [← (S.ends true).map_source]
    change _ = (S.ends true).map (truncate 0 false (suspendTable (project x)))
    rw [suspend_truncate_zero, ← E.horizontal_seam S i]
    exact (E.diagonal.map x).property.2

lemma AB : IntervalMatching (A D E S h i) (B D E S h i) := by
  intro x
  apply Subtype.ext
  change Y.join 0 ((D.horizontalDiagonalOne E h).map (atEnd true x)).val
    ((constantInterval (suffix E S i)).map (atEnd true x)).val =
      Y.join 0 ((D.horizontalDiagonalTwo E h).map (atEnd false x)).val
        ((constantInterval (suffix E S i)).map (atEnd false x)).val
  rw [D.horizontalDiagonal_matching E h x, constantInterval_endpoint, constantInterval_endpoint]

lemma BC : IntervalMatching (B D E S h i) (C D E S h i) := by
  intro x
  apply Subtype.ext
  rw [B_map]
  change Y.join 0 ((constantInterval (beforeGlobe D E h)).map (atEnd true x)).val
    ((E.horizontalDiagonalOne S i).map (atEnd true x)).val =
      Y.join 0 ((constantInterval (beforeGlobe D E h)).map (atEnd false x)).val
        ((E.horizontalDiagonalTwo S i).map (atEnd false x)).val
  rw [E.horizontalDiagonal_matching S i x, constantInterval_endpoint, constantInterval_endpoint]

lemma left_one_map (x : Table (K.{u} n)) :
    (((D.horizontal E h).horizontalDiagonalOne S i).map x).val =
      ((concatInterval (A D E S h i) (B D E S h i) (AB D E S h i)).map x).val := by
  have he := concatInterval_homCompose_stationary_right
    (D.horizontalDiagonalOne E h) (D.horizontalDiagonalTwo E h) (D.horizontalDiagonal_matching E h)
    (suffix E S i) (AB D E S h i)
  exact (congrArg (fun Q => (Q.map x).val) he).symm

lemma left_two_map (x : Table (K.{u} n)) :
    (((D.horizontal E h).horizontalDiagonalTwo S i).map x).val = ((C D E S h i).map x).val := by
  erw [horizontalDiagonalTwo_map]
  simp only [horizontal, globeHorizontal_suspend]
  change Y.join 0 (Y.join 0 ((D.ends false).map (suspendTable (project x)))
    ((E.ends false).map (suspendTable (project x)))) (S.diagonal.map x).val =
      Y.join 0 ((D.ends false).map (suspendTable (project x)))
        (Y.join 0 ((E.ends false).map (suspendTable (project x))) (S.diagonal.map x).val)
  apply Y.join_assoc 0 _ _ _ (D.horizontal_source_match E h (project x) false)
  erw [← (E.ends false).map_target]
  change (E.ends false).map (truncate 0 true (suspendTable (project x))) = _
  rw [suspend_truncate_zero, E.horizontal_seam S i false]
  exact (S.diagonal.map x).property.1.symm

lemma right_one_map (x : Table (K.{u} n)) :
    ((D.horizontalDiagonalOne (E.horizontal S i) h).map x).val = ((A D E S h i).map x).val := by
  erw [horizontalDiagonalOne_map]
  simp only [horizontal, globeHorizontal_suspend]
  change Y.join 0 (D.diagonal.map x).val
    (Y.join 0 ((E.ends true).map (suspendTable (project x))) ((S.ends true).map (suspendTable (project x)))) =
      Y.join 0 (Y.join 0 (D.diagonal.map x).val ((E.ends true).map (suspendTable (project x))))
        ((S.ends true).map (suspendTable (project x)))
  symm
  apply Y.join_assoc 0 _ _ _ _ (E.horizontal_source_match S i (project x) true)
  erw [← (E.ends true).map_source]
  change _ = (E.ends true).map (truncate 0 false (suspendTable (project x)))
  rw [suspend_truncate_zero, ← D.horizontal_seam E h true]
  exact (D.diagonal.map x).property.2

lemma right_two_map (x : Table (K.{u} n)) :
    ((D.horizontalDiagonalTwo (E.horizontal S i) h).map x).val =
      ((concatInterval (B D E S h i) (C D E S h i) (BC D E S h i)).map x).val := by
  have hb : B D E S h i = homCompose (constantInterval (beforeGlobe D E h)) (E.horizontalDiagonalOne S i) :=
    OmegaCategory.Functor.ext (funext (fun x => Subtype.ext (B_map D E S h i x)))
  have hm : IntervalMatching
      (homCompose (constantInterval (beforeGlobe D E h)) (E.horizontalDiagonalOne S i))
      (homCompose (constantInterval (beforeGlobe D E h)) (E.horizontalDiagonalTwo S i)) := by
    simpa only [C, ← hb] using BC D E S h i
  have he := concatInterval_homCompose_stationary_left (beforeGlobe D E h)
    (E.horizontalDiagonalOne S i) (E.horizontalDiagonalTwo S i) (E.horizontalDiagonal_matching S i) hm
  simp only [← hb] at he
  exact (congrArg (fun Q => (Q.map x).val) he).symm

end HorizontalAssociativity

lemma horizontal_associative :
    (D.horizontal E h).horizontal S i = D.horizontal (E.horizontal S i) h := by
  apply RectangleDiagram.ext
  · funext a
    apply GlobeComplex.functor_ext
    simp only [horizontal, globeHorizontal, lift_top]
    exact Y.join_assoc 0 _ _ _ (globe_horizontal_match _ _ (D.horizontal_seam E h a))
      (globe_horizontal_match _ _ (E.horizontal_seam S i a))
  · funext a
    cases a <;> rfl
  · intro x
    open HorizontalAssociativity in
    have hl := concatInterval_val_congr
      ((D.horizontal E h).horizontalDiagonalOne S i)
      ((D.horizontal E h).horizontalDiagonalTwo S i)
      ((D.horizontal E h).horizontalDiagonal_matching S i)
      (concatInterval (A D E S h i) (B D E S h i) (AB D E S h i))
      (C D E S h i) ((AB D E S h i).concat_left (BC D E S h i))
      (left_one_map D E S h i) (left_two_map D E S h i) x
    open HorizontalAssociativity in
    have hr := concatInterval_val_congr
      (D.horizontalDiagonalOne (E.horizontal S i) h)
      (D.horizontalDiagonalTwo (E.horizontal S i) h)
      (D.horizontalDiagonal_matching (E.horizontal S i) h)
      (A D E S h i)
      (concatInterval (B D E S h i) (C D E S h i) (BC D E S h i))
      ((AB D E S h i).concat_right (BC D E S h i))
      (right_one_map D E S h i) (right_two_map D E S h i) x
    open HorizontalAssociativity in
    have he := concatInterval_associative n (A D E S h i) (B D E S h i) (C D E S h i)
      (AB D E S h i) (BC D E S h i)
    exact hl.trans ((congrArg (fun Q => (Q.map x).val) he).trans hr.symm)

end RectangleDiagram

lemma horizontalCylinder_associative {n : ℕ} {Y : OmegaCategory.{u}}
    (F G H : OmegaCategory.Functor (K.{u} (n+1)).nu Y)
    (h : F.map (verticalTable (vertex n true)) = G.map (verticalTable (vertex n false)))
    (i : G.map (verticalTable (vertex n true)) = H.map (verticalTable (vertex n false)))
    (h' : (horizontalCylinder F G h).map (verticalTable (vertex n true)) = H.map (verticalTable (vertex n false)))
    (i' : F.map (verticalTable (vertex n true)) = (horizontalCylinder G H i).map (verticalTable (vertex n false))) :
    horizontalCylinder (horizontalCylinder F G h) H h' = horizontalCylinder F (horizontalCylinder G H i) i' := by
  unfold horizontalCylinder
  simp only [RectangleDiagram.ofFunctor_lift]
  exact congrArg RectangleDiagram.lift
    ((rectangleDiagramOfFunctor F).horizontal_associative (rectangleDiagramOfFunctor G)
      (rectangleDiagramOfFunctor H) h i)
end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma pasteCylinder_val_congr {n k : ℕ} (hk : k < n) {Y : OmegaCategory.{v}}
    {a b c d : Y.Cell}
    (F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory a b)) (h : FaceMatching k F G)
    (F' G' : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory c d)) (h' : FaceMatching k F' G')
    (he : ∀ x, (F.map x).val = (F'.map x).val)
    (hf : ∀ x, (G.map x).val = (G'.map x).val) (x : Table (K.{u} n)) :
    ((pasteCylinder hk F G h).map x).val = ((pasteCylinder hk F' G' h').map x).val := by
  have hac : a = c := (F.map x).property.1.symm.trans
    ((congrArg (Y.source 0) (he x)).trans (F'.map x).property.1)
  have hbd : b = d := (F.map x).property.2.symm.trans
    ((congrArg (Y.target 0) (he x)).trans (F'.map x).property.2)
  subst c d
  have hF : F = F' := OmegaCategory.Functor.ext (funext (fun z => Subtype.ext (he z)))
  have hG : G = G' := OmegaCategory.Functor.ext (funext (fun z => Subtype.ext (hf z)))
  subst F' G'
  rfl

lemma pasteCylinder_associative (n k : ℕ) (hk : k < n) {Y : OmegaCategory.{u}}
    (F G H : OmegaCategory.Functor (K.{u} n).nu Y)
    (h : FaceMatching k F G) (i : FaceMatching k G H)
    (h' : FaceMatching k (pasteCylinder hk F G h) H)
    (i' : FaceMatching k F (pasteCylinder hk G H i)) :
    pasteCylinder hk (pasteCylinder hk F G h) H h' =
      pasteCylinder hk F (pasteCylinder hk G H i) i' := by
  induction k generalizing n Y with
  | zero =>
    cases n with
    | zero => omega
    | succ n =>
      simp only [pasteCylinder_zero]
      exact horizontalCylinder_associative F G H (zeroFaceMatching_seam h)
        (zeroFaceMatching_seam i) (zeroFaceMatching_seam h') (zeroFaceMatching_seam i')
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      have hk' : k < n := by omega
      let A := (rectangleDiagramOfFunctor F).diagonal
      let B := CylinderComposition.secondDiagonal F G h
      let C := homCast (rectangleDiagramOfFunctor H).diagonal
        ((h.vertices false false).trans (i.vertices false false)).symm
        ((h.vertices true true).trans (i.vertices true true)).symm
      have hab : FaceMatching k A B := CylinderComposition.diagonal_matching F G h
      have hbc : FaceMatching k B C := by
        intro x
        apply Subtype.ext
        change G.map (up ((faceMap n k true).cylinder.nu.map x)) =
          H.map (up ((faceMap n k false).cylinder.nu.map x))
        rw [← tensorFace_up, ← tensorFace_up]
        exact i (up x)
      have hbc_map (x : Table (K.{u} n)) :
          ((pasteCylinder hk' B C hbc).map x).val =
            (pasteCylinder hk G H i).map (up x) := by
        rw [pasteCylinder_succ_up hk']
        exact pasteCylinder_val_congr hk' B C hbc
          (rectangleDiagramOfFunctor G).diagonal (CylinderComposition.secondDiagonal G H i)
          (CylinderComposition.diagonal_matching G H i) (fun _ => rfl) (fun _ => rfl) x
      have habc : FaceMatching k (pasteCylinder hk' A B hab) C := by
        intro x
        apply Subtype.ext
        change ((pasteCylinder hk' A B hab).map ((faceMap n k true).cylinder.nu.map x)).val =
          H.map (up ((faceMap n k false).cylinder.nu.map x))
        erw [← pasteCylinder_succ_up hk' F G h, ← tensorFace_up, ← tensorFace_up]
        exact h' (up x)
      have habc' : FaceMatching k A (pasteCylinder hk' B C hbc) := by
        intro x
        apply Subtype.ext
        change F.map (up ((faceMap n k true).cylinder.nu.map x)) = _
        erw [hbc_map, ← tensorFace_up, ← tensorFace_up]
        exact i' (up x)
      have hassoc := ih n hk' A B C hab hbc habc habc'
      apply functor_ext_rectangle
      · intro a x
        have he : OmegaCategory.Functor.comp ((complex (n+1)).cylinderEndpoint a).nu
            (pasteCylinder hk (pasteCylinder hk F G h) H h') =
            OmegaCategory.Functor.comp ((complex (n+1)).cylinderEndpoint a).nu
              (pasteCylinder hk F (pasteCylinder hk G H i) i') := by
          apply GlobeComplex.functor_ext
          change (pasteCylinder hk (pasteCylinder hk F G h) H h').map (atEnd a (topTable (n+1))) =
            (pasteCylinder hk F (pasteCylinder hk G H i) i').map (atEnd a (topTable (n+1)))
          simp only [pasteCylinder_endpoint_top]
          exact Y.join_assoc (k+1) _ _ _ (h.ends a) (i.ends a)
        exact congrArg (fun P => P.map x) he
      · intro a
        rw [pasteCylinder_succ_edge hk', pasteCylinder_succ_edge hk', pasteCylinder_succ_edge hk']
      · intro x
        rw [pasteCylinder_succ_up hk', pasteCylinder_succ_up hk']
        have hl := pasteCylinder_val_congr hk'
          (rectangleDiagramOfFunctor (pasteCylinder hk F G h)).diagonal
          (CylinderComposition.secondDiagonal (pasteCylinder hk F G h) H h')
          (CylinderComposition.diagonal_matching (pasteCylinder hk F G h) H h')
          (pasteCylinder hk' A B hab) C habc
          (fun z => pasteCylinder_succ_up hk' F G h z) (fun _ => rfl) x
        have hr := pasteCylinder_val_congr hk'
          (rectangleDiagramOfFunctor F).diagonal
          (CylinderComposition.secondDiagonal F (pasteCylinder hk G H i) i')
          (CylinderComposition.diagonal_matching F (pasteCylinder hk G H i) i')
          A (pasteCylinder hk' B C hbc) habc' (fun _ => rfl) (fun z => (hbc_map z).symm) x
        exact hl.trans ((congrArg (fun P => (P.map x).val) hassoc).trans hr.symm)
end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

def restrictCylinder {n : ℕ} (m : ℕ) (b : Bool) {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) : OmegaCategory.Functor (K.{u} m).nu Y :=
  OmegaCategory.Functor.comp (faceMap n m b).cylinder.nu F

@[simp] lemma restrictCylinder_endpoint {n m : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) (b a : Bool) (x : Table (complex.{u} m)) :
    (restrictCylinder m b F).map (atEnd a x) = F.map (atEnd a ((faceMap n m b).nu.map x)) :=
  congrArg F.map (cylinderHom_atEnd _ a x)

@[simp] lemma restrictCylinder_edge {n m : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} (n+1)).nu Y) (b a : Bool) :
    (restrictCylinder (m+1) b F).map (verticalTable (vertex m a)) =
      F.map (verticalTable (vertex n a)) := congrArg F.map (tensorFace_edge n m b a)

@[simp] lemma restrictCylinder_up {n m : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} (n+1)).nu Y) (b : Bool) (x : Table (K.{u} m)) :
    (restrictCylinder (m+1) b F).map (up x) =
      F.map (up ((faceMap n m b).cylinder.nu.map x)) := congrArg F.map (tensorFace_up n m b x)

@[simp] lemma restrictCylinder_self {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) (b : Bool) : restrictCylinder n b F = F := by
  unfold restrictCylinder
  rw [faceMap_self]
  apply OmegaCategory.Functor.ext
  funext x
  change F.map ((DirectedComplex.Hom.id _).cylinder.nu.map x) = F.map x
  rw [DirectedComplex.Hom.cylinder_id]
  rfl

lemma IntervalMatching.restrict {n : ℕ} {Y : OmegaCategory.{v}}
    {F G : OmegaCategory.Functor (K.{u} n).nu Y} (h : IntervalMatching F G) (m : ℕ) (b : Bool) :
    IntervalMatching (restrictCylinder m b F) (restrictCylinder m b G) := by
  intro x
  simp only [restrictCylinder_endpoint]
  exact h _

lemma concatInterval_face (n m : ℕ) (hm : m ≤ n) {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : IntervalMatching F G) (b : Bool) :
    restrictCylinder m b (concatInterval F G h) =
      concatInterval (restrictCylinder m b F) (restrictCylinder m b G) (h.restrict m b) := by
  induction m generalizing n Y with
  | zero =>
    cases n with
    | zero => simp only [restrictCylinder_self]
    | succ n =>
      apply OmegaCategory.Functor.ext
      funext x
      rcases table_zero_cases x with ⟨a,he⟩ | he
      · erw [he, restrictCylinder_endpoint, concatInterval_endpoint, concatInterval_endpoint]
        cases a <;> simp only [Bool.false_eq_true, ite_false, ite_true, restrictCylinder_endpoint]
      · rw [he]
        change (concatInterval F G h).map ((faceMap (n+1) 0 b).cylinder.nu.map (verticalTable (topTable 0))) = _
        rw [verticalTable_natural, faceMap_top]
        change (concatInterval F G h).map (verticalTable (vertex n b)) = _
        rw [concatInterval_succ_edge, concatInterval_zero_vertical]
        change _ = Y.join 0
          (F.map ((faceMap (n+1) 0 b).cylinder.nu.map (verticalTable (topTable 0))))
          (G.map ((faceMap (n+1) 0 b).cylinder.nu.map (verticalTable (topTable 0))))
        rw [verticalTable_natural, faceMap_top]
        rfl
  | succ m ih =>
    cases n with
    | zero => omega
    | succ n =>
      apply functor_ext_rectangle
      · intro a x
        erw [restrictCylinder_endpoint, concatInterval_endpoint, concatInterval_endpoint]
        cases a <;> simp only [Bool.false_eq_true, ite_false, ite_true, restrictCylinder_endpoint]
      · intro a
        simp only [restrictCylinder_edge, concatInterval_succ_edge]
      · intro x
        erw [restrictCylinder_up, concatInterval_succ_up, concatInterval_succ_up]
        let D := rectangleDiagramOfFunctor F
        let E := rectangleDiagramOfFunctor G
        have he := ih n (by omega) (D.concatDiagonalOne E h) (D.concatDiagonalTwo E h)
          (D.concatDiagonal_matching E h)
        have hl := congrArg (fun P => (P.map x).val) he
        refine hl.trans (concatInterval_val_congr
          (restrictCylinder m b (D.concatDiagonalOne E h))
          (restrictCylinder m b (D.concatDiagonalTwo E h)) _
          ((rectangleDiagramOfFunctor (restrictCylinder (m+1) b F)).concatDiagonalOne
            (rectangleDiagramOfFunctor (restrictCylinder (m+1) b G)) (h.restrict (m+1) b))
          ((rectangleDiagramOfFunctor (restrictCylinder (m+1) b F)).concatDiagonalTwo
            (rectangleDiagramOfFunctor (restrictCylinder (m+1) b G)) (h.restrict (m+1) b)) _ ?_ ?_ x)
        · intro z
          change Y.join 0 (F.map (verticalTable (vertex n false)))
            (G.map (up ((faceMap n m b).cylinder.nu.map z))) =
              Y.join 0 ((restrictCylinder (m+1) b F).map (verticalTable (vertex m false)))
                ((restrictCylinder (m+1) b G).map (up z))
          erw [restrictCylinder_edge, restrictCylinder_up]
        · intro z
          change Y.join 0 (F.map (up ((faceMap n m b).cylinder.nu.map z)))
            (G.map (verticalTable (vertex n true))) =
              Y.join 0 ((restrictCylinder (m+1) b F).map (up z))
                ((restrictCylinder (m+1) b G).map (verticalTable (vertex m true)))
          erw [restrictCylinder_up, restrictCylinder_edge]

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma restrictCylinder_endpoint_top {n m : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) (b a : Bool) :
    (restrictCylinder m b F).map (atEnd a (topTable m)) =
      Y.face m b (F.map (atEnd a (topTable n))) := by
  rw [restrictCylinder_endpoint, faceMap_top, ← atEnd_truncate]
  cases b
  · exact F.map_source m (atEnd a (topTable n))
  · exact F.map_target m (atEnd a (topTable n))

lemma restrictCylinder_zero_vertical {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} (n+1)).nu Y) (b : Bool) :
    (restrictCylinder 0 b F).map (verticalTable (topTable 0)) =
      F.map (verticalTable (vertex n b)) := by
  change F.map ((faceMap (n+1) 0 b).cylinder.nu.map (verticalTable (topTable 0))) = _
  rw [verticalTable_natural, faceMap_top]
  rfl

lemma pasteCylinder_zero_edge {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y) (h : FaceMatching 0 F G) (b : Bool) :
    (pasteCylinder (show 0 < n+1 by omega) F G h).map (verticalTable (vertex n b)) =
      if b then G.map (verticalTable (vertex n true)) else F.map (verticalTable (vertex n false)) :=
  RectangleDiagram.lift_edge _ _

lemma pasteCylinder_zero_up {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y) (h : FaceMatching 0 F G) (x : Table (K.{u} n)) :
    (pasteCylinder (show 0 < n+1 by omega) F G h).map (up x) =
      ((concatInterval
        ((rectangleDiagramOfFunctor F).horizontalDiagonalOne (rectangleDiagramOfFunctor G) (zeroFaceMatching_seam h))
        ((rectangleDiagramOfFunctor F).horizontalDiagonalTwo (rectangleDiagramOfFunctor G) (zeroFaceMatching_seam h))
        ((rectangleDiagramOfFunctor F).horizontalDiagonal_matching (rectangleDiagramOfFunctor G) (zeroFaceMatching_seam h))).map x).val :=
  RectangleDiagram.lift_up _ _

end Thomason.GrayRecursive

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_CylinderInterchange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cylinder Interchange. -/

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma tensorFace_tensorFace (n k j : ℕ) (hjk : j < k) (a b : Bool)
    (x : Table (K.{u} j)) :
    (faceMap n k b).cylinder.nu.map ((faceMap k j a).cylinder.nu.map x) =
      (faceMap n j a).cylinder.nu.map x := by
  have he := congrArg (fun f => f.cylinder.nu.map x) (faceMap_faceMap n k j hjk a b)
  rw [DirectedComplex.Hom.cylinder_comp] at he
  exact he

lemma restrictCylinder_restrict {n k j : ℕ} (hjk : j < k)
    {Y : OmegaCategory.{v}} (F : OmegaCategory.Functor (K.{u} n).nu Y) (a b : Bool) :
    restrictCylinder j a (restrictCylinder k b F) = restrictCylinder j a F := by
  apply OmegaCategory.Functor.ext
  funext x
  exact congrArg F.map (tensorFace_tensorFace n k j hjk a b x)

lemma FaceMatching.restrict {n k i : ℕ} (hki : k < i)
    {Y : OmegaCategory.{v}} {F G : OmegaCategory.Functor (K.{u} n).nu Y}
    (h : FaceMatching k F G) (b : Bool) :
    FaceMatching k (restrictCylinder i b F) (restrictCylinder i b G) := by
  intro x
  change F.map ((faceMap n i b).cylinder.nu.map ((faceMap i k true).cylinder.nu.map x)) =
    G.map ((faceMap n i b).cylinder.nu.map ((faceMap i k false).cylinder.nu.map x))
  rw [tensorFace_tensorFace n i k hki true b, tensorFace_tensorFace n i k hki false b]
  exact h x

lemma tensorFace_project (n m : ℕ) (b : Bool) (x : Table (K.{u} m)) :
    project ((faceMap n m b).cylinder.nu.map x) = (faceMap n m b).nu.map (project x) := by
  exact congrArg (fun f => f.nu.map x) (DirectedComplex.Hom.cylinder_projection (faceMap n m b))

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma intervalLabel_natural {n m : ℕ} (f : Hom (complex.{u} n) (complex.{u} m))
    (x : Table (K.{u} n)) (b : Bool) :
    intervalLabel (f.cylinder.nu.map x) b = intervalLabel x b := by
  exact f.map_augmentation ((x.row 0 b).2)

lemma tensorFace_zero_up (n : ℕ) (b : Bool) (x : Table (K.{u} n)) :
    (faceMap 0 (n+1) b).cylinder.nu.map (up x) = verticalTable (topTable 0) := by
  rcases table_zero_cases ((faceMap 0 (n+1) b).cylinder.nu.map (up x)) with ⟨a,he⟩ | he
  · have hs := congrArg (fun t => intervalLabel t false) he
    have ht := congrArg (fun t => intervalLabel t true) he
    simp only [intervalLabel_natural, intervalLabel_up, intervalLabel_end] at hs ht
    cases a <;> simp_all
  · exact he

def faceIdentityCylinder {n : ℕ} (k : ℕ) (b : Bool) {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) : OmegaCategory.Functor (K.{u} n).nu Y :=
  restrictCylinder n false (restrictCylinder k b F)

lemma faceIdentityCylinder_endpoint_top {n k : ℕ} (hk : k ≤ n)
    {Y : OmegaCategory.{v}} (F : OmegaCategory.Functor (K.{u} n).nu Y) (b a : Bool) :
    (faceIdentityCylinder k b F).map (atEnd a (topTable n)) =
      Y.face k b (F.map (atEnd a (topTable n))) := by
  unfold faceIdentityCylinder
  rw [restrictCylinder_endpoint_top, restrictCylinder_endpoint_top]
  cases b
  · exact Y.source_source n k _ |>.trans (congrArg (fun j => Y.source j _) (min_eq_right hk))
  · change Y.source n (Y.target k _) = Y.target k _
    rw [Y.source_target, ite_eq_right (by omega)]

lemma faceIdentityCylinder_succ_edge {n k : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} (n+1)).nu Y) (b a : Bool) :
    (faceIdentityCylinder (k+1) b F).map (verticalTable (vertex n a)) =
      F.map (verticalTable (vertex n a)) := by
  simp only [faceIdentityCylinder, restrictCylinder_edge]

lemma faceIdentityCylinder_succ_up {n k : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} (n+1)).nu Y) (b : Bool) (x : Table (K.{u} n)) :
    (faceIdentityCylinder (k+1) b F).map (up x) =
      ((faceIdentityCylinder k b (rectangleDiagramOfFunctor F).diagonal).map x).val := by
  simp only [faceIdentityCylinder, restrictCylinder_up]
  erw [restrictCylinder_up]
  rfl

lemma faceIdentityCylinder_zero_edge {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} (n+1)).nu Y) (b a : Bool) :
    (faceIdentityCylinder 0 b F).map (verticalTable (vertex n a)) =
      F.map (verticalTable (vertex n b)) := by
  change (restrictCylinder 0 b F).map ((faceMap 0 (n+1) false).cylinder.nu.map (verticalTable (vertex n a))) = _
  rw [verticalTable_natural, globe_zero_unique ((faceMap 0 (n+1) false).nu.map (vertex n a))]
  exact restrictCylinder_zero_vertical F b

lemma faceIdentityCylinder_zero_up {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} (n+1)).nu Y) (b : Bool) (x : Table (K.{u} n)) :
    (faceIdentityCylinder 0 b F).map (up x) = F.map (verticalTable (vertex n b)) := by
  change (restrictCylinder 0 b F).map ((faceMap 0 (n+1) false).cylinder.nu.map (up x)) = _
  rw [tensorFace_zero_up]
  exact restrictCylinder_zero_vertical F b

lemma faceIdentityCylinder_zero_endpoint {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} (n+1)).nu Y) (b a : Bool) (x : Table (complex.{u} (n+1))) :
    (faceIdentityCylinder 0 b F).map (atEnd a x) = F.map (atEnd a (vertex n b)) := by
  change (restrictCylinder 0 b F).map ((faceMap 0 (n+1) false).cylinder.nu.map (atEnd a x)) = _
  rw [cylinderHom_atEnd, globe_zero_unique ((faceMap 0 (n+1) false).nu.map x), restrictCylinder_endpoint, faceMap_top]
  rfl

lemma faceIdentityCylinder_left_matching {n k : ℕ} (hk : k < n)
    {Y : OmegaCategory.{v}} (F : OmegaCategory.Functor (K.{u} n).nu Y) :
    FaceMatching k (faceIdentityCylinder k false F) F := by
  have he : restrictCylinder k true (faceIdentityCylinder k false F) = restrictCylinder k false F := by
    unfold faceIdentityCylinder
    rw [restrictCylinder_restrict hk, restrictCylinder_self]
  intro x
  exact congrArg (fun P => P.map x) he

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma pasteCylinder_left_unit (n k : ℕ) (hk : k < n) {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) :
    pasteCylinder hk (faceIdentityCylinder k false F) F (faceIdentityCylinder_left_matching hk F) = F := by
  induction k generalizing n Y with
  | zero =>
    cases n with
    | zero => omega
    | succ n =>
      let D := rectangleDiagramOfFunctor F
      apply functor_ext_rectangle
      · intro a x
        have he : endGlobe (pasteCylinder hk (faceIdentityCylinder 0 false F) F
            (faceIdentityCylinder_left_matching hk F)) a = endGlobe F a := by
          apply GlobeComplex.functor_ext
          change (pasteCylinder hk (faceIdentityCylinder 0 false F) F
            (faceIdentityCylinder_left_matching hk F)).map (atEnd a (topTable (n+1))) =
              F.map (atEnd a (topTable (n+1)))
          rw [pasteCylinder_endpoint_top, faceIdentityCylinder_endpoint_top (by omega)]
          exact Y.join_left_unit 0 _ _ (Y.source_source_self 0 _) (Y.target_source_self 0 _)
        exact congrArg (fun P => P.map x) he
      · intro a
        rw [pasteCylinder_zero_edge]
        cases a <;> simp only [Bool.false_eq_true, ite_false, ite_true, faceIdentityCylinder_zero_edge]
      · intro x
        rw [pasteCylinder_zero_up]
        refine (concatInterval_val_congr _ _ _ (constantInterval (endGlobe D.diagonal false))
          D.diagonal (stationary_left_matching D.diagonal) ?_ ?_ x).trans (congrArg (fun P => (P.map x).val) (concatInterval_left_unit D.diagonal))
        · intro z
          change Y.join 0 ((faceIdentityCylinder 0 false F).map (up z))
            (F.map (atEnd true (suspendTable (project z)))) =
              (D.diagonal.map (atEnd false (project z))).val
          erw [faceIdentityCylinder_zero_up, D.left]
          rfl
        · intro z
          change Y.join 0 ((faceIdentityCylinder 0 false F).map (atEnd false (suspendTable (project z))))
            (F.map (up z)) = (D.diagonal.map z).val
          rw [faceIdentityCylinder_zero_endpoint]
          apply Y.join_left_unit 0 _ _ (D.vertex_fixed false false)
          rw [D.vertex_target_fixed false false]
          exact (D.diagonal.map z).property.1.symm
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      have hk' : k < n := by omega
      let D := rectangleDiagramOfFunctor F
      apply functor_ext_rectangle
      · intro a x
        have he : endGlobe (pasteCylinder hk (faceIdentityCylinder (k+1) false F) F
            (faceIdentityCylinder_left_matching hk F)) a = endGlobe F a := by
          apply GlobeComplex.functor_ext
          change (pasteCylinder hk (faceIdentityCylinder (k+1) false F) F
            (faceIdentityCylinder_left_matching hk F)).map (atEnd a (topTable (n+1))) =
              F.map (atEnd a (topTable (n+1)))
          rw [pasteCylinder_endpoint_top, faceIdentityCylinder_endpoint_top (by omega)]
          exact Y.join_left_unit (k+1) _ _ (Y.source_source_self (k+1) _) (Y.target_source_self (k+1) _)
        exact congrArg (fun P => P.map x) he
      · intro a
        rw [pasteCylinder_succ_edge hk', faceIdentityCylinder_succ_edge]
      · intro x
        rw [pasteCylinder_succ_up hk']
        refine (pasteCylinder_val_congr hk' _ _ _ (faceIdentityCylinder k false D.diagonal)
          D.diagonal (faceIdentityCylinder_left_matching hk' D.diagonal) ?_ ?_ x).trans (congrArg (fun P => (P.map x).val) (ih n hk' D.diagonal))
        · intro z
          exact faceIdentityCylinder_succ_up F false z
        · intro z
          rfl

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory Limits DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma FaceMatching.pair {n k : ℕ} {Y Z : OmegaCategory.{u}}
    {F G : OmegaCategory.Functor (K.{u} n).nu Y} (h : FaceMatching k F G)
    {F' G' : OmegaCategory.Functor (K.{u} n).nu Z} (h' : FaceMatching k F' G') :
    FaceMatching k (pairFunctor F F') (pairFunctor G G') := by
  have he : (faceMap n k true).cylinder.nu ≫ pairFunctor F F' =
      (faceMap n k false).cylinder.nu ≫ pairFunctor G G' := by
    apply prod.hom_ext <;> simp only [Category.assoc, pairFunctor, prod.lift_fst, prod.lift_snd]
    · exact OmegaCategory.Functor.ext (funext h)
    · exact OmegaCategory.Functor.ext (funext h')
  exact fun x => congrArg (fun f => f.map x) he

lemma pasteCylinder_pair {n k : ℕ} (hk : k < n) {Y Z : OmegaCategory.{u}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : FaceMatching k F G)
    (F' G' : OmegaCategory.Functor (K.{u} n).nu Z) (h' : FaceMatching k F' G')
    (H : FaceMatching k (pairFunctor F F') (pairFunctor G G')) :
    pasteCylinder hk (pairFunctor F F') (pairFunctor G G') H =
      pairFunctor (pasteCylinder hk F G h) (pasteCylinder hk F' G' h') := by
  apply @prod.hom_ext OmegaCategory.{u} _ ((K n).nu) Y Z _
  · change OmegaCategory.Functor.comp (pasteCylinder hk _ _ H) (prod.fst : Y ⨯ Z ⟶ Y) = _
    rw [pasteCylinder_natural]
    change pasteCylinder hk ((pairFunctor F F') ≫ prod.fst) ((pairFunctor G G') ≫ prod.fst) _ = _
    simp only [pairFunctor, prod.lift_fst]
  · change OmegaCategory.Functor.comp (pasteCylinder hk _ _ H) (prod.snd : Y ⨯ Z ⟶ Z) = _
    rw [pasteCylinder_natural]
    change pasteCylinder hk ((pairFunctor F F') ≫ prod.snd) ((pairFunctor G G') ≫ prod.snd) _ = _
    simp only [pairFunctor, prod.lift_snd]

lemma FaceMatching.homCompose {n k : ℕ} {Y : OmegaCategory.{v}} {a b c : Y.Cell}
    {F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory a b)} (h : FaceMatching k F G)
    {F' G' : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory b c)} (h' : FaceMatching k F' G') :
    FaceMatching k (OmegaCategory.homCompose F F') (OmegaCategory.homCompose G G') := by
  intro x
  apply Subtype.ext
  change Y.join 0 (F.map ((faceMap n k true).cylinder.nu.map x)).val
    (F'.map ((faceMap n k true).cylinder.nu.map x)).val = _
  rw [h x, h' x]
  rfl

lemma pasteCylinder_homCompose {n k : ℕ} (hk : k < n) {Y : OmegaCategory.{u}} {a b c : Y.Cell}
    (F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory a b)) (h : FaceMatching k F G)
    (F' G' : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory b c)) (h' : FaceMatching k F' G') :
    pasteCylinder hk (homCompose F F') (homCompose G G') (h.homCompose h') =
      homCompose (pasteCylinder hk F G h) (pasteCylinder hk F' G' h') := by
  let P : (Y.homCategory a b ⨯ Y.homCategory b c) ⟶ Y.homCategory a c :=
    homCompose (prod.fst : (Y.homCategory a b ⨯ Y.homCategory b c) ⟶ _) (prod.snd : (Y.homCategory a b ⨯ Y.homCategory b c) ⟶ _)
  have hp (A : (K.{u} n).nu ⟶ Y.homCategory a b)
      (B : (K.{u} n).nu ⟶ Y.homCategory b c) :
      pairFunctor A B ≫ P = homCompose A B := by
    apply OmegaCategory.Functor.ext
    funext x
    apply Subtype.ext
    change Y.join 0 ((pairFunctor A B ≫ prod.fst).map x).val
      ((pairFunctor A B ≫ prod.snd).map x).val = _
    change Y.join 0 ((prod.lift A B ≫ prod.fst).map x).val ((prod.lift A B ≫ prod.snd).map x).val = _
    rw [prod.lift_fst, prod.lift_snd]
    rfl
  have he := pasteCylinder_natural n k hk (pairFunctor F F') (pairFunctor G G') (h.pair h') P
  change pasteCylinder hk _ _ _ ≫ P = pasteCylinder hk (pairFunctor F F' ≫ P) (pairFunctor G G' ≫ P) _ at he
  simp only [pasteCylinder_pair hk F G h F' G' h', hp] at he
  exact he.symm

lemma FaceMatching.constantAt {n k : ℕ} {Y : OmegaCategory.{v}} (a : Y.Cell)
    (ha : Y.source 0 a = a) :
    FaceMatching k (constantAt (K.{u} n).nu a ha) (constantAt (K.{u} n).nu a ha) :=
  fun _ => rfl

@[simp] lemma pasteCylinder_constantAt {n k : ℕ} (hk : k < n) {Y : OmegaCategory.{v}} (a : Y.Cell)
    (ha : Y.source 0 a = a) (h : FaceMatching k (constantAt (K.{u} n).nu a ha) (constantAt (K.{u} n).nu a ha)) :
    pasteCylinder hk (constantAt (K.{u} n).nu a ha) (constantAt (K.{u} n).nu a ha) h =
      constantAt (K.{u} n).nu a ha := by
  have he : faceIdentityCylinder k false (constantAt (K.{u} n).nu a ha) =
      constantAt (K.{u} n).nu a ha := rfl
  simpa only [he] using pasteCylinder_left_unit n k hk (constantAt (K.{u} n).nu a ha)

lemma pasteCylinder_homCompose_left {n k : ℕ} (hk : k < n) {Y : OmegaCategory.{u}} {a b c : Y.Cell}
    (f : Y.Cell) (hf : Y.source 1 f = f) (hs : Y.source 0 f = a) (ht : Y.target 0 f = b)
    (F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory b c)) (h : FaceMatching k F G)
    (h' : FaceMatching k (homCompose (constantHom (K n).nu f hf hs ht) F)
      (homCompose (constantHom (K n).nu f hf hs ht) G)) :
    pasteCylinder hk (homCompose (constantHom (K n).nu f hf hs ht) F)
      (homCompose (constantHom (K n).nu f hf hs ht) G) h' =
      homCompose (constantHom (K n).nu f hf hs ht) (pasteCylinder hk F G h) := by
  have e := pasteCylinder_homCompose hk (constantHom (K n).nu f hf hs ht)
    (constantHom (K n).nu f hf hs ht) (FaceMatching.constantAt (k := k) (Y := Y.homCategory a b) ⟨f, hs, ht⟩ (Subtype.ext hf)) F G h
  exact e.trans (congrArg (fun A => homCompose A (pasteCylinder hk F G h))
    (pasteCylinder_constantAt hk (Y := Y.homCategory a b) ⟨f, hs, ht⟩ (Subtype.ext hf) _))

lemma pasteCylinder_homCompose_right {n k : ℕ} (hk : k < n) {Y : OmegaCategory.{u}} {a b c : Y.Cell}
    (F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory a b)) (h : FaceMatching k F G)
    (f : Y.Cell) (hf : Y.source 1 f = f) (hs : Y.source 0 f = b) (ht : Y.target 0 f = c)
    (h' : FaceMatching k (homCompose F (constantHom (K n).nu f hf hs ht))
      (homCompose G (constantHom (K n).nu f hf hs ht))) :
    pasteCylinder hk (homCompose F (constantHom (K n).nu f hf hs ht))
      (homCompose G (constantHom (K n).nu f hf hs ht)) h' =
      homCompose (pasteCylinder hk F G h) (constantHom (K n).nu f hf hs ht) := by
  have e := pasteCylinder_homCompose hk F G h (constantHom (K n).nu f hf hs ht)
    (constantHom (K n).nu f hf hs ht) (FaceMatching.constantAt (k := k) (Y := Y.homCategory b c) ⟨f, hs, ht⟩ (Subtype.ext hf))
  exact e.trans (congrArg (fun B => homCompose (pasteCylinder hk F G h) B)
    (pasteCylinder_constantAt hk (Y := Y.homCategory b c) ⟨f, hs, ht⟩ (Subtype.ext hf) _))

lemma FaceMatching.concat {n k : ℕ} (hk : k ≤ n) {Y : OmegaCategory.{v}}
    {F G F' G' : OmegaCategory.Functor (K.{u} n).nu Y}
    (h : FaceMatching k F G) (i : FaceMatching k F' G')
    (t : IntervalMatching F F') (t' : IntervalMatching G G') :
    FaceMatching k (concatInterval F F' t) (concatInterval G G' t') := by
  have he : restrictCylinder k true (concatInterval F F' t) =
      restrictCylinder k false (concatInterval G G' t') := by
    rw [concatInterval_face n k hk, concatInterval_face n k hk]
    have eh : restrictCylinder k true F = restrictCylinder k false G := OmegaCategory.Functor.ext (funext h)
    have ei : restrictCylinder k true F' = restrictCylinder k false G' := OmegaCategory.Functor.ext (funext i)
    simp only [eh, ei]
  exact fun x => congrArg (fun f => f.map x) he

lemma IntervalMatching.paste {n k : ℕ} (hk : k < n) {Y : OmegaCategory.{v}}
    {F G F' G' : OmegaCategory.Functor (K.{u} n).nu Y}
    (h : IntervalMatching F F') (i : IntervalMatching G G')
    (t : FaceMatching k F G) (t' : FaceMatching k F' G') :
    IntervalMatching (pasteCylinder hk F G t) (pasteCylinder hk F' G' t') := by
  have he : endGlobe (pasteCylinder hk F G t) true = endGlobe (pasteCylinder hk F' G' t') false := by
    apply GlobeComplex.functor_ext
    change (pasteCylinder hk F G t).map (atEnd true (topTable n)) =
      (pasteCylinder hk F' G' t').map (atEnd false (topTable n))
    rw [pasteCylinder_endpoint_top, pasteCylinder_endpoint_top, h, i]
  exact fun x => congrArg (fun f => f.map x) he

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma IntervalMatching.homCompose {n : ℕ} {Y : OmegaCategory.{v}} {a b c : Y.Cell}
    {F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory a b)} (h : IntervalMatching F G)
    {F' G' : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory b c)} (h' : IntervalMatching F' G') :
    IntervalMatching (OmegaCategory.homCompose F F') (OmegaCategory.homCompose G G') := by
  intro x
  apply Subtype.ext
  change Y.join 0 (F.map (atEnd true x)).val (F'.map (atEnd true x)).val = _
  rw [h x, h' x]
  rfl

lemma IntervalMatching.of_val {n : ℕ} {Y : OmegaCategory.{v}} {a b c d : Y.Cell}
    (F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory a b))
    (F' G' : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory c d))
    (h : IntervalMatching F' G')
    (he : ∀ x, (F.map x).val = (F'.map x).val)
    (hf : ∀ x, (G.map x).val = (G'.map x).val) : IntervalMatching F G := by
  intro x
  apply Subtype.ext
  erw [he, hf]
  exact congrArg Subtype.val (h x)

end Thomason.GrayRecursive

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_PastingInterchange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pasting Interchange. -/

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

namespace RectangleDiagram
namespace MixedZero
variable {n : ℕ} {Y : OmegaCategory.{u}}
    (D E S T : RectangleDiagram.{u,u} n Y)
    (e : D.edge true = E.edge false) (j : S.edge true = T.edge false)
    (h : ∀ x, (D.ends true).map x = (S.ends false).map x)
    (i : ∀ x, (E.ends true).map x = (T.ends false).map x)

abbrev left := D.assocLeft S h
abbrev right := E.assocRight T i
abbrev before := HorizontalAssociativity.beforeGlobe D E e
abbrev suffix := HorizontalAssociativity.suffix S T j

def midRight : OmegaCategory.Functor (K.{u} n).nu
    (Y.homCategory ((D.ends true).map (vertex n true)) ((T.ends true).map (vertex n true))) :=
  homCast T.diagonal ((h _).trans (S.horizontal_seam T j false)).symm rfl

def A := homCompose (left D S h) (S.horizontalDiagonalOne T j)
def B := homCompose (constantInterval (endGlobe D.diagonal false)) (midRight D S T j h)
def C := homCompose D.diagonal (constantInterval (endGlobe (midRight D S T j h) true))
def B' := homCompose D.diagonal (constantInterval (endGlobe (midRight D S T j h) false))
def C' := homCompose (constantInterval (endGlobe D.diagonal true)) (midRight D S T j h)
def Z := homCompose (D.horizontalDiagonalTwo E e) (right E T i)

lemma B_eq :
    B D S T j h = homCompose (left D S h) (S.horizontalDiagonalTwo T j) := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change Y.join 0 (D.diagonal.map (atEnd false (project x))).val (T.diagonal.map x).val =
    Y.join 0 (D.edge false) (Y.join 0 ((S.ends false).map (suspendTable (project x))) (T.diagonal.map x).val)
  erw [D.left, h]
  apply Y.join_assoc 0
  · erw [← h]
    exact D.edge_end_matching _
  · erw [← (S.ends false).map_target]
    change (S.ends false).map (truncate 0 true (suspendTable (project x))) = _
    rw [suspend_truncate_zero, S.horizontal_seam T j]
    exact (T.diagonal.map x).property.1.symm

lemma C_eq :
    C D S T j h = homCompose (D.horizontalDiagonalOne E e) (right E T i) := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change Y.join 0 (D.diagonal.map x).val (T.diagonal.map (atEnd true (project x))).val =
    Y.join 0 (Y.join 0 (D.diagonal.map x).val ((E.ends true).map (suspendTable (project x)))) (T.edge true)
  erw [T.right, ← i]
  symm
  apply Y.join_assoc 0
  · erw [← (E.ends true).map_source]
    change _ = (E.ends true).map (truncate 0 false (suspendTable (project x)))
    rw [suspend_truncate_zero, ← D.horizontal_seam E e]
    exact (D.diagonal.map x).property.2
  · erw [i]
    exact T.end_edge_matching _

lemma B'_eq :
    B' D S T j h = homCompose (D.concatDiagonalTwo S h) (constantInterval (suffix S T j)) := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change Y.join 0 (D.diagonal.map x).val (T.diagonal.map (atEnd false (project x))).val =
    Y.join 0 (Y.join 0 (D.diagonal.map x).val (S.edge true)) ((T.ends true).map (suspendTable (project x)))
  rw [T.left, ← j]
  symm
  apply Y.join_assoc 0
  · erw [(S.edge_source true), ← h]
    exact (D.diagonal.map x).property.2
  · rw [j]
    exact T.edge_end_matching _

lemma C'_eq :
    C' D S T j h = homCompose (constantInterval (before D E e)) (E.concatDiagonalOne T i) := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change Y.join 0 (D.diagonal.map (atEnd true (project x))).val (T.diagonal.map x).val =
    Y.join 0 ((D.ends false).map (suspendTable (project x))) (Y.join 0 (E.edge false) (T.diagonal.map x).val)
  rw [D.right, e]
  apply Y.join_assoc 0
  · rw [← e]
    exact D.end_edge_matching _
  · erw [E.edge_target, i]
    exact (T.diagonal.map x).property.1.symm

lemma A_eq :
    A D S T j h = homCompose (D.concatDiagonalOne S h) (constantInterval (suffix S T j)) := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change Y.join 0 (D.edge false) (Y.join 0 (S.diagonal.map x).val ((T.ends true).map (suspendTable (project x)))) =
    Y.join 0 (Y.join 0 (D.edge false) (S.diagonal.map x).val) ((T.ends true).map (suspendTable (project x)))
  symm
  apply Y.join_assoc 0
  · erw [D.edge_target, h]
    exact (S.diagonal.map x).property.1.symm
  · erw [← (T.ends true).map_source]
    change _ = (T.ends true).map (truncate 0 false (suspendTable (project x)))
    rw [suspend_truncate_zero, ← S.horizontal_seam T j]
    exact (S.diagonal.map x).property.2

lemma AB : IntervalMatching (A D S T j h) (B D S T j h) := by
  rw [B_eq]
  exact (show IntervalMatching (left D S h) (left D S h) from fun _ => rfl).homCompose (S.horizontalDiagonal_matching T j)

lemma BC : IntervalMatching (B D S T j h) (C D S T j h) :=
  (stationary_left_matching D.diagonal).homCompose (stationary_right_matching (midRight D S T j h))

lemma CZ : IntervalMatching (C D S T j h) (Z D E T e i) := by
  rw [C_eq D E S T e j h i]
  exact (D.horizontalDiagonal_matching E e).homCompose (show IntervalMatching (right E T i) (right E T i) from fun _ => rfl)

lemma AB' : IntervalMatching (A D S T j h) (B' D S T j h) := by
  rw [A_eq, B'_eq]
  exact (D.concatDiagonal_matching S h).homCompose (constantInterval_matching (suffix S T j))

lemma BC' : IntervalMatching (B' D S T j h) (C' D S T j h) :=
  (stationary_right_matching D.diagonal).homCompose (stationary_left_matching (midRight D S T j h))

end MixedZero

end RectangleDiagram

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

namespace MixedPositive
variable {n k : ℕ} {Y : OmegaCategory.{u}}
    (F G F' G' : OmegaCategory.Functor (K.{u} (n+1)).nu Y)
    (e : FaceMatching (k+1) F G) (j : FaceMatching (k+1) F' G')
    (h : IntervalMatching F F') (i : IntervalMatching G G')

abbrev A := (rectangleDiagramOfFunctor F).concatDiagonalOne (rectangleDiagramOfFunctor F') h
abbrev B := (rectangleDiagramOfFunctor F).concatDiagonalTwo (rectangleDiagramOfFunctor F') h
abbrev C := homCompose ((rectangleDiagramOfFunctor F).assocLeft (rectangleDiagramOfFunctor F') h)
  (CylinderComposition.secondDiagonal F' G' j)
abbrev Z := homCompose (CylinderComposition.secondDiagonal F G e)
  ((rectangleDiagramOfFunctor F).assocRight (rectangleDiagramOfFunctor F') h)

lemma AC : FaceMatching k (A F F' h) (C F F' G' j h) :=
  (show FaceMatching k ((rectangleDiagramOfFunctor F).assocLeft (rectangleDiagramOfFunctor F') h)
    ((rectangleDiagramOfFunctor F).assocLeft (rectangleDiagramOfFunctor F') h) from fun _ => rfl).homCompose
      (CylinderComposition.diagonal_matching F' G' j)

lemma BZ : FaceMatching k (B F F' h) (Z F G F' e h) :=
  (CylinderComposition.diagonal_matching F G e).homCompose
    (show FaceMatching k ((rectangleDiagramOfFunctor F).assocRight (rectangleDiagramOfFunctor F') h)
      ((rectangleDiagramOfFunctor F).assocRight (rectangleDiagramOfFunctor F') h) from fun _ => rfl)

lemma AB : IntervalMatching (A F F' h) (B F F' h) :=
  (rectangleDiagramOfFunctor F).concatDiagonal_matching (rectangleDiagramOfFunctor F') h

include e in
lemma C_map (x : Table (K.{u} n)) :
    ((C F F' G' j h).map x).val =
      (((rectangleDiagramOfFunctor G).concatDiagonalOne (rectangleDiagramOfFunctor G') i).map x).val := by
  change Y.join 0 (F.map (verticalTable (vertex n false))) (G'.map (up x)) =
    Y.join 0 (G.map (verticalTable (vertex n false))) (G'.map (up x))
  rw [e.edges false]

include j in
lemma Z_map (x : Table (K.{u} n)) :
    ((Z F G F' e h).map x).val =
      (((rectangleDiagramOfFunctor G).concatDiagonalTwo (rectangleDiagramOfFunctor G') i).map x).val := by
  change Y.join 0 (G.map (up x)) (F'.map (verticalTable (vertex n true))) =
    Y.join 0 (G.map (up x)) (G'.map (verticalTable (vertex n true)))
  rw [j.edges true]

include i in
lemma CZ : IntervalMatching (C F F' G' j h) (Z F G F' e h) :=
  IntervalMatching.of_val _ _ _ _
    ((rectangleDiagramOfFunctor G).concatDiagonal_matching (rectangleDiagramOfFunctor G') i)
    (C_map F G F' G' e j h i) (Z_map F G F' G' e j h i)

lemma left_one_map (hk : k < n)
    (hh : IntervalMatching (pasteCylinder (Nat.add_lt_add_right hk 1) F G e)
      (pasteCylinder (Nat.add_lt_add_right hk 1) F' G' j))
    (x : Table (K.{u} n)) :
    (((rectangleDiagramOfFunctor (pasteCylinder (Nat.add_lt_add_right hk 1) F G e)).concatDiagonalOne
      (rectangleDiagramOfFunctor (pasteCylinder (Nat.add_lt_add_right hk 1) F' G' j)) hh).map x).val =
      ((pasteCylinder hk (A F F' h) (C F F' G' j h) (AC F F' G' j h)).map x).val := by
  let D := rectangleDiagramOfFunctor F
  let S := rectangleDiagramOfFunctor F'
  have he := pasteCylinder_homCompose_left hk (D.edge false) (D.edge_fixed false)
    (D.edge_source false) ((D.edge_target false).trans (h _))
    S.diagonal (CylinderComposition.secondDiagonal F' G' j)
    (CylinderComposition.diagonal_matching F' G' j) (AC F F' G' j h)
  change Y.join 0 ((pasteCylinder (Nat.add_lt_add_right hk 1) F G e).map (verticalTable (vertex n false)))
    ((pasteCylinder (Nat.add_lt_add_right hk 1) F' G' j).map (up x)) = _
  rw [pasteCylinder_succ_edge hk, pasteCylinder_succ_up hk]
  exact (congrArg (fun Q => (Q.map x).val) he).symm

lemma left_two_map (hk : k < n)
    (hh : IntervalMatching (pasteCylinder (Nat.add_lt_add_right hk 1) F G e)
      (pasteCylinder (Nat.add_lt_add_right hk 1) F' G' j))
    (x : Table (K.{u} n)) :
    (((rectangleDiagramOfFunctor (pasteCylinder (Nat.add_lt_add_right hk 1) F G e)).concatDiagonalTwo
      (rectangleDiagramOfFunctor (pasteCylinder (Nat.add_lt_add_right hk 1) F' G' j)) hh).map x).val =
      ((pasteCylinder hk (B F F' h) (Z F G F' e h) (BZ F G F' e h)).map x).val := by
  let D := rectangleDiagramOfFunctor F
  let S := rectangleDiagramOfFunctor F'
  have he := pasteCylinder_homCompose_right hk D.diagonal (CylinderComposition.secondDiagonal F G e)
    (CylinderComposition.diagonal_matching F G e) (S.edge true) (S.edge_fixed true)
      ((S.edge_source true).trans (h _).symm) (S.edge_target true) (BZ F G F' e h)
  change Y.join 0 ((pasteCylinder (Nat.add_lt_add_right hk 1) F G e).map (up x))
    ((pasteCylinder (Nat.add_lt_add_right hk 1) F' G' j).map (verticalTable (vertex n true))) = _
  rw [pasteCylinder_succ_edge hk, pasteCylinder_succ_up hk]
  exact (congrArg (fun Q => (Q.map x).val) he).symm

end MixedPositive

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma FaceMatching.of_val {n k : ℕ} {Y : OmegaCategory.{u}} {a b c d : Y.Cell}
    (F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory a b))
    (F' G' : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory c d))
    (h : FaceMatching k F' G')
    (he : ∀ x, (F.map x).val = (F'.map x).val)
    (hf : ∀ x, (G.map x).val = (G'.map x).val) : FaceMatching k F G := by
  intro x
  apply Subtype.ext
  rw [he, hf]
  exact congrArg Subtype.val (h x)

lemma pasteCylinder_homCompose_stationary_right {n k : ℕ} (hk : k < n)
    {Y : OmegaCategory.{u}} {a b c : Y.Cell}
    (F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory a b)) (h : FaceMatching k F G)
    (P Q : OmegaCategory.Functor (complex.{u} n).nu (Y.homCategory b c))
    (hPQ : (Y.homCategory b c).target k (P.map (topTable n)) = (Y.homCategory b c).source k (Q.map (topTable n)))
    (h' : FaceMatching k (homCompose F (constantInterval P)) (homCompose G (constantInterval Q))) :
    pasteCylinder hk (homCompose F (constantInterval P)) (homCompose G (constantInterval Q)) h' =
      homCompose (pasteCylinder hk F G h) (constantInterval (globeComposite hk P Q hPQ)) := by
  have he := pasteCylinder_homCompose hk F G h (constantInterval P) (constantInterval Q)
    (constantInterval_faceMatching P Q hPQ)
  rw [pasteCylinder_constant n k hk P Q hPQ] at he
  exact he

lemma pasteCylinder_homCompose_stationary_left {n k : ℕ} (hk : k < n)
    {Y : OmegaCategory.{u}} {a b c : Y.Cell}
    (P Q : OmegaCategory.Functor (complex.{u} n).nu (Y.homCategory a b))
    (hPQ : (Y.homCategory a b).target k (P.map (topTable n)) = (Y.homCategory a b).source k (Q.map (topTable n)))
    (F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory b c)) (h : FaceMatching k F G)
    (h' : FaceMatching k (homCompose (constantInterval P) F) (homCompose (constantInterval Q) G)) :
    pasteCylinder hk (homCompose (constantInterval P) F) (homCompose (constantInterval Q) G) h' =
      homCompose (constantInterval (globeComposite hk P Q hPQ)) (pasteCylinder hk F G h) := by
  have he := pasteCylinder_homCompose hk (constantInterval P) (constantInterval Q)
    (constantInterval_faceMatching P Q hPQ) F G h
  rw [pasteCylinder_constant n k hk P Q hPQ] at he
  exact he

lemma globeComposite_endpoint_val {n k : ℕ} (hk : k < n)
    {Y : OmegaCategory.{u}} {a c : Y.Cell}
    (P Q : OmegaCategory.Functor (complex.{u} n).nu (Y.homCategory a c))
    (hPQ : (Y.homCategory a c).target k (P.map (topTable n)) = (Y.homCategory a c).source k (Q.map (topTable n)))
    (F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y) (h : FaceMatching (k+1) F G) (b : Bool)
    (hP : (P.map (topTable n)).val = F.map (atEnd b (topTable (n+1))))
    (hQ : (Q.map (topTable n)).val = G.map (atEnd b (topTable (n+1))))
    (x : Table (complex.{u} n)) :
    ((globeComposite hk P Q hPQ).map x).val =
      (pasteCylinder (Nat.add_lt_add_right hk 1) F G h).map (atEnd b (suspendTable x)) := by
  apply globeSuspended_ext _ (endGlobe (pasteCylinder (Nat.add_lt_add_right hk 1) F G h) b)
  rw [globeComposite_top, hom_join_val _ _ _ hPQ, hP, hQ]
  exact (pasteCylinder_endpoint_top (Nat.add_lt_add_right hk 1) F G h b).symm

namespace ZeroInterchange
variable {n k : ℕ} {Y : OmegaCategory.{u}}
    (F G F' G' : OmegaCategory.Functor (K.{u} (n+1)).nu Y)
    (e : FaceMatching 0 F G) (j : FaceMatching 0 F' G')
    (h : FaceMatching (k+1) F F') (i : FaceMatching (k+1) G G')

abbrev D := rectangleDiagramOfFunctor F
abbrev E := rectangleDiagramOfFunctor G
abbrev S := rectangleDiagramOfFunctor F'
abbrev T := rectangleDiagramOfFunctor G'

abbrev suffix := RectangleDiagram.HorizontalAssociativity.suffix (D F) (E G) (zeroFaceMatching_seam e)

def suffix' : OmegaCategory.Functor (complex.{u} n).nu
    (Y.homCategory (F.map (atEnd true (vertex n true))) (G.map (atEnd true (vertex n true)))) :=
  homCast (globeHomMap ((T G').ends true))
    ((i.vertices true false).symm.trans ((D F).horizontal_seam (E G) (zeroFaceMatching_seam e) true).symm)
    (i.vertices true true).symm

lemma suffix_matching :
    (Y.homCategory (F.map (atEnd true (vertex n true))) (G.map (atEnd true (vertex n true)))).target k
      ((suffix F G e).map (topTable n)) =
    (Y.homCategory (F.map (atEnd true (vertex n true))) (G.map (atEnd true (vertex n true)))).source k
      ((suffix' F G G' e i).map (topTable n)) := by
  apply Subtype.ext
  change Y.target (k+1) (G.map (atEnd true (suspendTable (topTable n)))) =
    Y.source (k+1) (G'.map (atEnd true (suspendTable (topTable n))))
  rw [suspendTable_top]
  exact i.ends true

abbrev before := RectangleDiagram.HorizontalAssociativity.beforeGlobe (D F) (E G) (zeroFaceMatching_seam e)

def before' : OmegaCategory.Functor (complex.{u} n).nu
    (Y.homCategory (F.map (atEnd false (vertex n false))) (G.map (atEnd false (vertex n false)))) :=
  homCast (globeHomMap ((S F').ends false)) (h.vertices false false).symm
    ((h.vertices false true).symm.trans ((D F).horizontal_seam (E G) (zeroFaceMatching_seam e) false))

lemma before_matching :
    (Y.homCategory (F.map (atEnd false (vertex n false))) (G.map (atEnd false (vertex n false)))).target k
      ((before F G e).map (topTable n)) =
    (Y.homCategory (F.map (atEnd false (vertex n false))) (G.map (atEnd false (vertex n false)))).source k
      ((before' F G F' e h).map (topTable n)) := by
  apply Subtype.ext
  change Y.target (k+1) (F.map (atEnd false (suspendTable (topTable n)))) =
    Y.source (k+1) (F'.map (atEnd false (suspendTable (topTable n))))
  rw [suspendTable_top]
  exact h.ends false

abbrev A := homCompose (D F).diagonal (constantInterval (suffix F G e))
abbrev C := homCompose (CylinderComposition.secondDiagonal F F' h) (constantInterval (suffix' F G G' e i))
abbrev B := homCompose (constantInterval (before F G e)) (E G).diagonal
abbrev Z := homCompose (constantInterval (before' F G F' e h)) (CylinderComposition.secondDiagonal G G' i)

lemma AC : FaceMatching k (A F G e) (C F G F' G' e h i) :=
  (CylinderComposition.diagonal_matching F F' h).homCompose
    (constantInterval_faceMatching _ _ (suffix_matching F G G' e i))

lemma BZ : FaceMatching k (B F G e) (Z F G F' G' e h i) :=
  (constantInterval_faceMatching _ _ (before_matching F G F' e h)).homCompose
    (CylinderComposition.diagonal_matching G G' i)

lemma AB : IntervalMatching (A F G e) (B F G e) :=
  (D F).horizontalDiagonal_matching (E G) (zeroFaceMatching_seam e)

include j in
lemma CZ : IntervalMatching (C F G F' G' e h i) (Z F G F' G' e h i) :=
  IntervalMatching.of_val _ _ _ _
    ((S F').horizontalDiagonal_matching (T G') (zeroFaceMatching_seam j)) (fun _ => rfl) (fun _ => rfl)

lemma paste_one_map (hk : k < n)
    (ee : FaceMatching 0 (pasteCylinder (Nat.add_lt_add_right hk 1) F F' h)
      (pasteCylinder (Nat.add_lt_add_right hk 1) G G' i)) (x : Table (K.{u} n)) :
    ((pasteCylinder hk (A F G e) (C F G F' G' e h i) (AC F G F' G' e h i)).map x).val =
    (((rectangleDiagramOfFunctor (pasteCylinder (Nat.add_lt_add_right hk 1) F F' h)).horizontalDiagonalOne
      (rectangleDiagramOfFunctor (pasteCylinder (Nat.add_lt_add_right hk 1) G G' i)) (zeroFaceMatching_seam ee)).map x).val := by
  have he := pasteCylinder_homCompose_stationary_right hk
    (D F).diagonal (CylinderComposition.secondDiagonal F F' h) (CylinderComposition.diagonal_matching F F' h)
    (suffix F G e) (suffix' F G G' e i) (suffix_matching F G G' e i) (AC F G F' G' e h i)
  erw [he]
  change Y.join 0 ((pasteCylinder hk (D F).diagonal _ _).map x).val
    ((globeComposite hk (suffix F G e) (suffix' F G G' e i) (suffix_matching F G G' e i)).map (project x)).val =
      Y.join 0 ((pasteCylinder (Nat.add_lt_add_right hk 1) F F' h).map (up x))
        ((pasteCylinder (Nat.add_lt_add_right hk 1) G G' i).map (atEnd true (suspendTable (project x))))
  rw [pasteCylinder_succ_up hk]
  congr 1
  apply globeComposite_endpoint_val hk _ _ _ G G' i true
  · exact congrArg (fun z => G.map (atEnd true z)) (suspendTable_top n)
  · exact congrArg (fun z => G'.map (atEnd true z)) (suspendTable_top n)

lemma paste_two_map (hk : k < n)
    (ee : FaceMatching 0 (pasteCylinder (Nat.add_lt_add_right hk 1) F F' h)
      (pasteCylinder (Nat.add_lt_add_right hk 1) G G' i)) (x : Table (K.{u} n)) :
    ((pasteCylinder hk (B F G e) (Z F G F' G' e h i) (BZ F G F' G' e h i)).map x).val =
    (((rectangleDiagramOfFunctor (pasteCylinder (Nat.add_lt_add_right hk 1) F F' h)).horizontalDiagonalTwo
      (rectangleDiagramOfFunctor (pasteCylinder (Nat.add_lt_add_right hk 1) G G' i)) (zeroFaceMatching_seam ee)).map x).val := by
  have he := pasteCylinder_homCompose_stationary_left hk
    (before F G e) (before' F G F' e h) (before_matching F G F' e h)
    (E G).diagonal (CylinderComposition.secondDiagonal G G' i) (CylinderComposition.diagonal_matching G G' i)
    (BZ F G F' G' e h i)
  erw [he]
  change Y.join 0 ((globeComposite hk (before F G e) (before' F G F' e h) (before_matching F G F' e h)).map (project x)).val
    ((pasteCylinder hk (E G).diagonal _ _).map x).val =
      Y.join 0 ((pasteCylinder (Nat.add_lt_add_right hk 1) F F' h).map (atEnd false (suspendTable (project x))))
        ((pasteCylinder (Nat.add_lt_add_right hk 1) G G' i).map (up x))
  rw [pasteCylinder_succ_up hk]
  congr 1
  apply globeComposite_endpoint_val hk _ _ _ F F' h false
  · exact congrArg (fun z => F.map (atEnd false z)) (suspendTable_top n)
  · exact congrArg (fun z => F'.map (atEnd false z)) (suspendTable_top n)

end ZeroInterchange

end Thomason.GrayRecursive

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_IntervalCategories
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interval Categories. -/

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

namespace PositiveInterchange
variable {n k l : ℕ} {Y : OmegaCategory.{u}}
    (F G F' G' : OmegaCategory.Functor (K.{u} (n+1)).nu Y)
    (e : FaceMatching (k+1) F G) (j : FaceMatching (k+1) F' G')
    (h : FaceMatching (l+1) F F') (i : FaceMatching (l+1) G G')

abbrev A := (rectangleDiagramOfFunctor F).diagonal
abbrev B := CylinderComposition.secondDiagonal F G e
abbrev C := CylinderComposition.secondDiagonal F F' h

def Z : OmegaCategory.Functor (K.{u} n).nu
    (Y.homCategory (F.map (atEnd false (vertex n false))) (F.map (atEnd true (vertex n true)))) :=
  homCast (rectangleDiagramOfFunctor G').diagonal
    ((e.vertices false false).trans (i.vertices false false)).symm
    ((e.vertices true true).trans (i.vertices true true)).symm

abbrev AB : FaceMatching k (A F) (B F G e) := CylinderComposition.diagonal_matching F G e
abbrev AC : FaceMatching l (A F) (C F F' h) := CylinderComposition.diagonal_matching F F' h

lemma BZ : FaceMatching l (B F G e) (Z F G G' e i) :=
  FaceMatching.of_val _ _ _ _ (CylinderComposition.diagonal_matching G G' i) (fun _ => rfl) (fun _ => rfl)

include j in
lemma CZ : FaceMatching k (C F F' h) (Z F G G' e i) :=
  FaceMatching.of_val _ _ _ _ (CylinderComposition.diagonal_matching F' G' j) (fun _ => rfl) (fun _ => rfl)

lemma BZ_map (hl : l < n) (x : Table (K.{u} n)) :
    ((pasteCylinder hl (B F G e) (Z F G G' e i) (BZ F G G' e i)).map x).val =
      (pasteCylinder (Nat.add_lt_add_right hl 1) G G' i).map (up x) := by
  rw [pasteCylinder_succ_up hl]
  apply pasteCylinder_val_congr <;> intro w <;> rfl

include j in
lemma CZ_map (hk : k < n) (x : Table (K.{u} n)) :
    ((pasteCylinder hk (C F F' h) (Z F G G' e i) (CZ F G F' G' e j h i)).map x).val =
      (pasteCylinder (Nat.add_lt_add_right hk 1) F' G' j).map (up x) := by
  rw [pasteCylinder_succ_up hk]
  apply pasteCylinder_val_congr <;> intro w <;> rfl

lemma outer_e (hl : l < n)
    (ee : FaceMatching (k+1) (pasteCylinder (Nat.add_lt_add_right hl 1) F F' h)
      (pasteCylinder (Nat.add_lt_add_right hl 1) G G' i)) :
    FaceMatching k (pasteCylinder hl (A F) (C F F' h) (AC F F' h))
      (pasteCylinder hl (B F G e) (Z F G G' e i) (BZ F G G' e i)) :=
  FaceMatching.of_val _ _ _ _ (CylinderComposition.diagonal_matching _ _ ee)
    (fun x => (pasteCylinder_succ_up hl F F' h x).symm) (BZ_map F G G' e i hl)

lemma outer_h (hk : k < n)
    (hh : FaceMatching (l+1) (pasteCylinder (Nat.add_lt_add_right hk 1) F G e)
      (pasteCylinder (Nat.add_lt_add_right hk 1) F' G' j)) :
    FaceMatching l (pasteCylinder hk (A F) (B F G e) (AB F G e))
      (pasteCylinder hk (C F F' h) (Z F G G' e i) (CZ F G F' G' e j h i)) :=
  FaceMatching.of_val _ _ _ _ (CylinderComposition.diagonal_matching _ _ hh)
    (fun x => (pasteCylinder_succ_up hk F G e x).symm) (CZ_map F G F' G' e j h i hk)

end PositiveInterchange

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma restrictCylinder_from_zero_endpoint {m : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} 0).nu Y) (b a : Bool) (x : Table (complex.{u} m)) :
    (restrictCylinder m b F).map (atEnd a x) = F.map (atEnd a (topTable 0)) := by
  rw [restrictCylinder_endpoint, globe_zero_unique ((faceMap 0 m b).nu.map x)]

lemma restrictCylinder_from_zero_edge {m : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} 0).nu Y) (b a : Bool) :
    (restrictCylinder (m+1) b F).map (verticalTable (vertex m a)) = F.map (verticalTable (topTable 0)) := by
  change F.map ((faceMap 0 (m+1) b).cylinder.nu.map (verticalTable (vertex m a))) = _
  rw [verticalTable_natural, globe_zero_unique ((faceMap 0 (m+1) b).nu.map (vertex m a))]

lemma restrictCylinder_from_zero_up {m : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} 0).nu Y) (b : Bool) (x : Table (K.{u} m)) :
    (restrictCylinder (m+1) b F).map (up x) = F.map (verticalTable (topTable 0)) := by
  change F.map ((faceMap 0 (m+1) b).cylinder.nu.map (up x)) = _
  rw [tensorFace_zero_up]

lemma concatInterval_map_of_const {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : IntervalMatching F G) (y : Y.Cell)
    (he : ∀ x, F.map x = y) (hf : ∀ x, G.map x = y) (x : Table (K.{u} n)) :
    (concatInterval F G h).map x = y := by
  have hy : Y.source 0 y = y := by
    erw [← he x, ← F.map_source, he, he]
  have hF : F = constantAt (K n).nu y hy := OmegaCategory.Functor.ext (funext he)
  have hG : G = constantAt (K n).nu y hy := OmegaCategory.Functor.ext (funext hf)
  subst F G
  rw [concatInterval_constantAt]
  rfl

lemma concatInterval_const_val {n : ℕ} {Y : OmegaCategory.{v}} {a b : Y.Cell}
    (F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory a b)) (h : IntervalMatching F G) (y : Y.Cell)
    (he : ∀ x, (F.map x).val = y) (hf : ∀ x, (G.map x).val = y) (x : Table (K.{u} n)) :
    ((concatInterval F G h).map x).val = y := by
  let z := F.map (atEnd false (topTable n))
  have hF (w) : F.map w = z := Subtype.ext ((he w).trans (he _).symm)
  have hG (w) : G.map w = z := Subtype.ext ((hf w).trans (he _).symm)
  exact (congrArg Subtype.val (concatInterval_map_of_const F G h z hF hG x)).trans (he _)

lemma concatInterval_restrict (n m : ℕ) {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : IntervalMatching F G) (b : Bool) :
    restrictCylinder m b (concatInterval F G h) =
      concatInterval (restrictCylinder m b F) (restrictCylinder m b G) (h.restrict m b) := by
  induction m generalizing n Y with
  | zero =>
    cases n with
    | zero => simp only [restrictCylinder_self]
    | succ n =>
      apply OmegaCategory.Functor.ext
      funext x
      rcases table_zero_cases x with ⟨a,he⟩ | he
      · erw [he, restrictCylinder_endpoint, concatInterval_endpoint, concatInterval_endpoint]
        cases a <;> simp only [Bool.false_eq_true, ite_false, ite_true, restrictCylinder_endpoint]
      · rw [he]
        change (concatInterval F G h).map ((faceMap (n+1) 0 b).cylinder.nu.map (verticalTable (topTable 0))) = _
        rw [verticalTable_natural, faceMap_top]
        change (concatInterval F G h).map (verticalTable (vertex n b)) = _
        rw [concatInterval_succ_edge, concatInterval_zero_vertical]
        change _ = Y.join 0
          (F.map ((faceMap (n+1) 0 b).cylinder.nu.map (verticalTable (topTable 0))))
          (G.map ((faceMap (n+1) 0 b).cylinder.nu.map (verticalTable (topTable 0))))
        rw [verticalTable_natural, faceMap_top]
        rfl
  | succ m ih =>
    cases n with
    | zero =>
      apply functor_ext_rectangle
      · intro a x
        rw [restrictCylinder_from_zero_endpoint, concatInterval_endpoint, concatInterval_endpoint]
        cases a <;> simp only [Bool.false_eq_true, ite_false, ite_true, restrictCylinder_from_zero_endpoint]
      · intro a
        rw [restrictCylinder_from_zero_edge, concatInterval_zero_vertical, concatInterval_succ_edge,
          restrictCylinder_from_zero_edge, restrictCylinder_from_zero_edge]
      · intro x
        rw [restrictCylinder_from_zero_up, concatInterval_zero_vertical, concatInterval_succ_up]
        symm
        apply concatInterval_const_val
        · intro z
          change Y.join 0 ((restrictCylinder (m+1) b F).map (verticalTable (vertex m false)))
            ((restrictCylinder (m+1) b G).map (up z)) = _
          erw [restrictCylinder_from_zero_edge, restrictCylinder_from_zero_up]
        · intro z
          change Y.join 0 ((restrictCylinder (m+1) b F).map (up z))
            ((restrictCylinder (m+1) b G).map (verticalTable (vertex m true))) = _
          erw [restrictCylinder_from_zero_up, restrictCylinder_from_zero_edge]
    | succ n =>
      apply functor_ext_rectangle
      · intro a x
        erw [restrictCylinder_endpoint, concatInterval_endpoint, concatInterval_endpoint]
        cases a <;> simp only [Bool.false_eq_true, ite_false, ite_true, restrictCylinder_endpoint]
      · intro a
        simp only [restrictCylinder_edge, concatInterval_succ_edge]
      · intro x
        erw [restrictCylinder_up, concatInterval_succ_up, concatInterval_succ_up]
        let D := rectangleDiagramOfFunctor F
        let E := rectangleDiagramOfFunctor G
        have he := ih n (D.concatDiagonalOne E h) (D.concatDiagonalTwo E h)
          (D.concatDiagonal_matching E h)
        have hl := congrArg (fun P => (P.map x).val) he
        refine hl.trans (concatInterval_val_congr
          (restrictCylinder m b (D.concatDiagonalOne E h))
          (restrictCylinder m b (D.concatDiagonalTwo E h)) _
          ((rectangleDiagramOfFunctor (restrictCylinder (m+1) b F)).concatDiagonalOne
            (rectangleDiagramOfFunctor (restrictCylinder (m+1) b G)) (h.restrict (m+1) b))
          ((rectangleDiagramOfFunctor (restrictCylinder (m+1) b F)).concatDiagonalTwo
            (rectangleDiagramOfFunctor (restrictCylinder (m+1) b G)) (h.restrict (m+1) b)) _ ?_ ?_ x)
        · intro z
          change Y.join 0 (F.map (verticalTable (vertex n false)))
            (G.map (up ((faceMap n m b).cylinder.nu.map z))) =
              Y.join 0 ((restrictCylinder (m+1) b F).map (verticalTable (vertex m false)))
                ((restrictCylinder (m+1) b G).map (up z))
          erw [restrictCylinder_edge, restrictCylinder_up]
        · intro z
          change Y.join 0 (F.map (up ((faceMap n m b).cylinder.nu.map z)))
            (G.map (verticalTable (vertex n true))) =
              Y.join 0 ((restrictCylinder (m+1) b F).map (up z))
                ((restrictCylinder (m+1) b G).map (verticalTable (vertex m true)))
          erw [restrictCylinder_up, restrictCylinder_edge]

lemma pasteCylinder_restrict_gt (n k i : ℕ) (hk : k < n) (hki : k < i)
    {Y : OmegaCategory.{v}} (F G : OmegaCategory.Functor (K.{u} n).nu Y)
    (h : FaceMatching k F G) (b : Bool) :
    restrictCylinder i b (pasteCylinder hk F G h) =
      pasteCylinder hki (restrictCylinder i b F) (restrictCylinder i b G) (h.restrict hki b) := by
  induction k generalizing n i Y with
  | zero =>
    cases n with
    | zero => omega
    | succ n =>
      cases i with
      | zero => omega
      | succ i =>
        apply functor_ext_rectangle
        · intro a x
          have he : endGlobe (restrictCylinder (i+1) b (pasteCylinder hk F G h)) a =
              endGlobe (pasteCylinder hki (restrictCylinder (i+1) b F)
                (restrictCylinder (i+1) b G) (h.restrict hki b)) a := by
            apply GlobeComplex.functor_ext
            change (restrictCylinder (i+1) b (pasteCylinder hk F G h)).map (atEnd a (topTable (i+1))) =
              (pasteCylinder hki (restrictCylinder (i+1) b F)
                (restrictCylinder (i+1) b G) (h.restrict hki b)).map (atEnd a (topTable (i+1)))
            rw [restrictCylinder_endpoint_top, pasteCylinder_endpoint_top, pasteCylinder_endpoint_top,
              restrictCylinder_endpoint_top, restrictCylinder_endpoint_top]
            cases b
            · exact Y.join_source_gt (i+1) 0 _ _ hki (h.ends a)
            · exact Y.join_target_gt (i+1) 0 _ _ hki (h.ends a)
          exact congrArg (fun P => P.map x) he
        · intro a
          rw [restrictCylinder_edge, pasteCylinder_zero_edge, pasteCylinder_zero_edge]
          cases a <;> simp only [Bool.false_eq_true, ite_false, ite_true, restrictCylinder_edge]
        · intro x
          erw [restrictCylinder_up, pasteCylinder_zero_up, pasteCylinder_zero_up]
          let D := rectangleDiagramOfFunctor F
          let E := rectangleDiagramOfFunctor G
          have he := concatInterval_restrict n i (D.horizontalDiagonalOne E (zeroFaceMatching_seam h))
            (D.horizontalDiagonalTwo E (zeroFaceMatching_seam h))
            (D.horizontalDiagonal_matching E (zeroFaceMatching_seam h)) b
          have hv := congrArg (fun P => (P.map x).val) he
          refine hv.trans (concatInterval_val_congr _ _ _ _ _ _ ?_ ?_ x)
          · intro z
            change Y.join 0 (F.map (up ((faceMap n i b).cylinder.nu.map z)))
              (G.map (atEnd true (suspendTable (project ((faceMap n i b).cylinder.nu.map z))))) =
                Y.join 0 ((restrictCylinder (i+1) b F).map (up z))
                  ((restrictCylinder (i+1) b G).map (atEnd true (suspendTable (project z))))
            erw [restrictCylinder_up, restrictCylinder_endpoint, faceMap_suspend, tensorFace_project]
          · intro z
            change Y.join 0 (F.map (atEnd false (suspendTable (project ((faceMap n i b).cylinder.nu.map z)))))
              (G.map (up ((faceMap n i b).cylinder.nu.map z))) =
                Y.join 0 ((restrictCylinder (i+1) b F).map (atEnd false (suspendTable (project z))))
                  ((restrictCylinder (i+1) b G).map (up z))
            erw [restrictCylinder_endpoint, faceMap_suspend, restrictCylinder_up, tensorFace_project]
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      cases i with
      | zero => omega
      | succ i =>
        have hk' : k < n := by omega
        have hki' : k < i := by omega
        apply functor_ext_rectangle
        · intro a x
          have he : endGlobe (restrictCylinder (i+1) b (pasteCylinder hk F G h)) a =
              endGlobe (pasteCylinder hki (restrictCylinder (i+1) b F)
                (restrictCylinder (i+1) b G) (h.restrict hki b)) a := by
            apply GlobeComplex.functor_ext
            change (restrictCylinder (i+1) b (pasteCylinder hk F G h)).map (atEnd a (topTable (i+1))) =
              (pasteCylinder hki (restrictCylinder (i+1) b F)
                (restrictCylinder (i+1) b G) (h.restrict hki b)).map (atEnd a (topTable (i+1)))
            rw [restrictCylinder_endpoint_top, pasteCylinder_endpoint_top, pasteCylinder_endpoint_top,
              restrictCylinder_endpoint_top, restrictCylinder_endpoint_top]
            cases b
            · exact Y.join_source_gt (i+1) (k+1) _ _ hki (h.ends a)
            · exact Y.join_target_gt (i+1) (k+1) _ _ hki (h.ends a)
          exact congrArg (fun P => P.map x) he
        · intro a
          rw [restrictCylinder_edge, pasteCylinder_succ_edge hk', pasteCylinder_succ_edge hki',
            restrictCylinder_edge]
        · intro x
          erw [restrictCylinder_up, pasteCylinder_succ_up hk', pasteCylinder_succ_up hki']
          have he := ih n i hk' hki' (rectangleDiagramOfFunctor F).diagonal
            (CylinderComposition.secondDiagonal F G h) (CylinderComposition.diagonal_matching F G h)
          have hv := congrArg (fun P => (P.map x).val) he
          refine hv.trans (pasteCylinder_val_congr hki' _ _ _ _ _ _ ?_ ?_ x)
          · intro z
            change F.map (up ((faceMap n i b).cylinder.nu.map z)) = (restrictCylinder (i+1) b F).map (up z)
            exact (restrictCylinder_up F b z).symm
          · intro z
            change G.map (up ((faceMap n i b).cylinder.nu.map z)) = (restrictCylinder (i+1) b G).map (up z)
            exact (restrictCylinder_up G b z).symm
end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

namespace GlobeComplex
lemma faceMap_above (n m : ℕ) (hnm : n ≤ m) (b : Bool) :
    faceMap.{u} n m b = faceMap n m false := by
  apply hom_ext
  rw [faceMap_top, faceMap_top]
  rw [← face_nu, ← face_nu]
  change (complex n).nu.face m b (topTable n) = (complex n).nu.source m (topTable n)
  rw [(complex n).nu.face_of_fixed (topTable_bounded n) hnm b,
    (complex n).nu.source_fixed_upwards hnm (topTable_bounded n)]

lemma faceMap_faceMap_above (n m j : ℕ) (hnm : n ≤ m) (a b : Bool) :
    Hom.comp (faceMap.{u} m j a) (faceMap n m b) = faceMap n j a := by
  apply hom_ext
  change (faceMap n m b).nu.map ((faceMap m j a).nu.map (topTable j)) = _
  rw [faceMap_top]
  change (faceMap n m b).table (truncate j a (topTable m)) = _
  rw [Hom.table_truncate]
  change truncate j a ((faceMap n m b).nu.map (topTable m)) = _
  rw [faceMap_top, faceMap_top]
  have ht : truncate m b (topTable n) = topTable n := by
    rw [← face_nu]
    exact (complex n).nu.face_of_fixed (topTable_bounded n) hnm b
  rw [ht]
end GlobeComplex

namespace GrayRecursive

lemma restrictCylinder_restrict_above {n m j : ℕ} (h : n ≤ m) {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) (a b : Bool) :
    restrictCylinder j a (restrictCylinder m b F) = restrictCylinder j a F := by
  apply OmegaCategory.Functor.ext
  funext x
  change F.map ((faceMap n m b).cylinder.nu.map ((faceMap m j a).cylinder.nu.map x)) = _
  have hc := congrArg (fun f => f.cylinder.nu.map x) (faceMap_faceMap_above n m j h a b)
  rw [Hom.cylinder_comp] at hc
  exact congrArg F.map hc

end GrayRecursive
end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

variable (Y : OmegaCategory.{u})

def Cell := {f : ∀ n, OmegaCategory.Functor (K.{u} n).nu Y //
  ∃ N, ∀ n, f n = restrictCylinder n false (f N)}

variable {Y}

def ofMap {n : ℕ} (F : OmegaCategory.Functor (K.{u} n).nu Y) : Cell Y :=
  ⟨fun m => restrictCylinder m false F, n, fun m => by dsimp only; rw [restrictCylinder_self]⟩

def eval (n : ℕ) (x : Cell Y) : OmegaCategory.Functor (K.{u} n).nu Y := x.val n

@[simp] lemma eval_ofMap {n m : ℕ} (F : OmegaCategory.Functor (K.{u} n).nu Y) :
    eval m (ofMap F) = restrictCylinder m false F := rfl

@[simp] lemma eval_ofMap_self {n : ℕ} (F : OmegaCategory.Functor (K.{u} n).nu Y) :
    eval n (ofMap F) = F := restrictCylinder_self F false

lemma ofMap_injective (n : ℕ) : Function.Injective (@ofMap Y n) := by
  intro F G h
  have he := congrArg (eval n) h
  simpa only [eval_ofMap_self] using he

lemma ofMap_raise {n m : ℕ} (h : n ≤ m) (F : OmegaCategory.Functor (K.{u} n).nu Y) :
    ofMap (restrictCylinder m false F) = ofMap F := by
  apply Subtype.ext
  funext j
  exact restrictCylinder_restrict_above h F false false

def Bounded (n : ℕ) (x : Cell Y) : Prop := ofMap (eval n x) = x

lemma ofMap_bounded {n : ℕ} (F : OmegaCategory.Functor (K.{u} n).nu Y) :
    Bounded n (ofMap F) := by simp only [Bounded, eval_ofMap_self]

lemma bounded_exists (x : Cell Y) : ∃ N, Bounded N x := by
  obtain ⟨N,hN⟩ := x.property
  exact ⟨N, Subtype.ext (funext fun n => (hN n).symm)⟩

def bound (x : Cell Y) : ℕ := (bounded_exists x).choose

lemma bounded_bound (x : Cell Y) : Bounded (bound x) x := (bounded_exists x).choose_spec

lemma eval_eq_restrict {n : ℕ} {x : Cell Y} (h : Bounded n x) (m : ℕ) :
    eval m x = restrictCylinder m false (eval n x) := by
  exact (congrArg (eval m) h).symm

lemma Bounded.mono {n m : ℕ} {x : Cell Y} (h : Bounded n x) (hnm : n ≤ m) :
    Bounded m x := by
  change ofMap (eval m x) = x
  rw [eval_eq_restrict h m, ofMap_raise hnm]
  exact h

def face (m : ℕ) (b : Bool) (x : Cell Y) : Cell Y :=
  ofMap (restrictCylinder m b (eval (bound x) x))

lemma face_eq_of_bounded {n : ℕ} {x : Cell Y} (h : Bounded n x) (m : ℕ) (b : Bool) :
    face m b x = ofMap (restrictCylinder m b (eval n x)) := by
  let N := max n (bound x)
  have hn : n ≤ N := le_max_left _ _
  have hb : bound x ≤ N := le_max_right _ _
  have he : restrictCylinder m b (eval (bound x) x) = restrictCylinder m b (eval n x) := by
    calc
      _ = restrictCylinder m b (eval N x) := by
        rw [eval_eq_restrict (bounded_bound x) N, restrictCylinder_restrict_above hb]
      _ = _ := by rw [eval_eq_restrict h N, restrictCylinder_restrict_above hn]
  exact congrArg ofMap he

@[simp] lemma face_ofMap {n : ℕ} (F : OmegaCategory.Functor (K.{u} n).nu Y)
    (m : ℕ) (b : Bool) : face m b (ofMap F) = ofMap (restrictCylinder m b F) := by
  rw [face_eq_of_bounded (ofMap_bounded F), eval_ofMap_self]

lemma face_matching {n k : ℕ} {F G : OmegaCategory.Functor (K.{u} n).nu Y}
    (h : face k true (ofMap F) = face k false (ofMap G)) : FaceMatching k F G := by
  have he := (ofMap_injective k) (by simpa only [face_ofMap] using h)
  exact fun x => congrArg (fun P => P.map x) he

end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

variable {Y : OmegaCategory.{u}}

lemma matching_eval {k n : ℕ} {x y : Cell Y} (hx : Bounded n x) (hy : Bounded n y)
    (h : face k true x = face k false y) : FaceMatching k (eval n x) (eval n y) := by
  apply face_matching
  change ofMap (eval n x) = x at hx
  change ofMap (eval n y) = y at hy
  simpa only [hx,hy] using h

def composeAt (k n : ℕ) (hk : k < n) (x y : Cell Y) (hx : Bounded n x) (hy : Bounded n y)
    (h : face k true x = face k false y) : Cell Y :=
  ofMap (pasteCylinder hk (eval n x) (eval n y) (matching_eval hx hy h))

lemma ofMap_paste_raise {k n m : ℕ} (hk : k < n) (hnm : n ≤ m)
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : FaceMatching k F G) :
    ofMap (pasteCylinder hk F G h) = ofMap
      (pasteCylinder (Nat.lt_of_lt_of_le hk hnm) (restrictCylinder m false F) (restrictCylinder m false G)
        (h.restrict (Nat.lt_of_lt_of_le hk hnm) false)) := by
  rw [← pasteCylinder_restrict_gt n k m hk (Nat.lt_of_lt_of_le hk hnm), ofMap_raise hnm]

lemma composeAt_mono {k n m : ℕ} (hk : k < n) (hnm : n ≤ m)
    (x y : Cell Y) (hx : Bounded n x) (hy : Bounded n y)
    (h : face k true x = face k false y) :
    composeAt k n hk x y hx hy h = composeAt k m (Nat.lt_of_lt_of_le hk hnm) x y
      (hx.mono hnm) (hy.mono hnm) h := by
  unfold composeAt
  rw [ofMap_paste_raise hk hnm]
  congr 1
  have ex := eval_eq_restrict hx m
  have ey := eval_eq_restrict hy m
  simp only [ex,ey]

lemma composeAt_independent {k n m : ℕ} (hkn : k < n) (hkm : k < m)
    (x y : Cell Y) (hx : Bounded n x) (hy : Bounded n y)
    (hx' : Bounded m x) (hy' : Bounded m y)
    (h : face k true x = face k false y) :
    composeAt k n hkn x y hx hy h = composeAt k m hkm x y hx' hy' h := by
  rw [composeAt_mono hkn (le_max_left n m), composeAt_mono hkm (le_max_right n m)]

def comp (k : ℕ) (x y : Cell Y) (h : face k true x = face k false y) : Cell Y :=
  let N := max (k+1) (max (bound x) (bound y))
  composeAt k N (by omega) x y
    ((bounded_bound x).mono (by omega)) ((bounded_bound y).mono (by omega)) h

lemma comp_eq_composeAt {k n : ℕ} (hk : k < n) (x y : Cell Y)
    (hx : Bounded n x) (hy : Bounded n y) (h : face k true x = face k false y) :
    comp k x y h = composeAt k n hk x y hx hy h :=
  composeAt_independent (by omega) hk x y
    ((bounded_bound x).mono (by omega)) ((bounded_bound y).mono (by omega)) hx hy h

lemma comp_ofMap {k n : ℕ} (hk : k < n)
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : face k true (ofMap F) = face k false (ofMap G)) :
    comp k (ofMap F) (ofMap G) h = ofMap (pasteCylinder hk F G (face_matching h)) := by
  rw [comp_eq_composeAt hk _ _ (ofMap_bounded F) (ofMap_bounded G)]
  unfold composeAt
  simp only [eval_ofMap_self]

end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {Y : OmegaCategory.{u}}

lemma comp_assoc (k : ℕ) (x y z : Cell Y)
    (hxy : face k true x = face k false y) (hyz : face k true y = face k false z)
    (hxy_z : face k true (comp k x y hxy) = face k false z)
    (hx_yz : face k true x = face k false (comp k y z hyz)) :
    comp k (comp k x y hxy) z hxy_z = comp k x (comp k y z hyz) hx_yz := by
  let N := max (k+1) (max (bound x) (max (bound y) (bound z)))
  have hk : k < N := by omega
  have hx : Bounded N x := (bounded_bound x).mono (by omega)
  have hy : Bounded N y := (bounded_bound y).mono (by omega)
  have hz : Bounded N z := (bounded_bound z).mono (by omega)
  clear_value N
  obtain ⟨F,rfl⟩ : ∃ F : OmegaCategory.Functor (K.{u} N).nu Y, ofMap F = x := ⟨_,hx⟩
  obtain ⟨G,rfl⟩ : ∃ G : OmegaCategory.Functor (K.{u} N).nu Y, ofMap G = y := ⟨_,hy⟩
  obtain ⟨H,rfl⟩ : ∃ H : OmegaCategory.Functor (K.{u} N).nu Y, ofMap H = z := ⟨_,hz⟩
  simp only [comp_ofMap hk] at hxy_z hx_yz ⊢
  congr 1
  apply pasteCylinder_associative

end Thomason.GrayRecursive.IntervalHom

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_CylinderWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cylinder Weights. -/

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {Y Z W : OmegaCategory.{u}}

lemma restrictCylinder_post {n m : ℕ} (F : OmegaCategory.Functor (K.{u} n).nu Y)
    (P : OmegaCategory.Functor Y Z) (b : Bool) :
    restrictCylinder m b (OmegaCategory.Functor.comp F P) =
      OmegaCategory.Functor.comp (restrictCylinder m b F) P := rfl

def mapCell (P : OmegaCategory.Functor Y Z) (x : Cell Y) : Cell Z :=
  ⟨fun n => OmegaCategory.Functor.comp (eval n x) P, bound x, fun n => by
    change OmegaCategory.Functor.comp (eval n x) P =
      restrictCylinder n false (OmegaCategory.Functor.comp (eval (bound x) x) P)
    rw [eval_eq_restrict (bounded_bound x) n, restrictCylinder_post]⟩

@[simp] lemma eval_mapCell (P : OmegaCategory.Functor Y Z) (x : Cell Y) (n : ℕ) :
    eval n (mapCell P x) = OmegaCategory.Functor.comp (eval n x) P := rfl

@[simp] lemma mapCell_ofMap (P : OmegaCategory.Functor Y Z) {n : ℕ}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) :
    mapCell P (ofMap F) = ofMap (OmegaCategory.Functor.comp F P) := rfl

end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {X Y Z : OmegaCategory.{u}}

lemma endpointTop_bounded {n : ℕ} (F : OmegaCategory.Functor (K.{u} n).nu Y) (a : Bool) :
    Y.source n (F.map (atEnd a (topTable n))) = F.map (atEnd a (topTable n)) := by
  erw [← F.map_source]
  congr 1
  exact (atEnd_truncate a false (topTable n) n).trans (congrArg (atEnd a) (topTable_bounded n))

def endpointCell (a : Bool) (x : Cell Y) : Y.Cell :=
  (eval (bound x) x).map (atEnd a (topTable (bound x)))

lemma endpointCell_of_bounded {n : ℕ} {x : Cell Y} (hx : Bounded n x) (a : Bool) :
    endpointCell a x = (eval n x).map (atEnd a (topTable n)) := by
  let N := max n (bound x)
  have he (m : ℕ) (hm : Bounded m x) (hmN : m ≤ N) :
      (eval N x).map (atEnd a (topTable N)) = (eval m x).map (atEnd a (topTable m)) := by
    rw [eval_eq_restrict hm N, restrictCylinder_endpoint_top]
    exact Y.source_fixed_upwards hmN (endpointTop_bounded (eval m x) a)
  exact (he (bound x) (bounded_bound x) (le_max_right _ _)).symm.trans (he n hx (le_max_left _ _))

@[simp] lemma endpointCell_ofMap {n : ℕ} (F : OmegaCategory.Functor (K.{u} n).nu Y) (a : Bool) :
    endpointCell a (ofMap F) = F.map (atEnd a (topTable n)) := by
  rw [endpointCell_of_bounded (ofMap_bounded F), eval_ofMap_self]

lemma endpointCell_face (a : Bool) (x : Cell Y) (k : ℕ) (b : Bool) :
    endpointCell a (face k b x) = Y.face k b (endpointCell a x) := by
  obtain ⟨n,hn⟩ := bounded_exists x
  obtain ⟨F,rfl⟩ : ∃ F : OmegaCategory.Functor (K.{u} n).nu Y, ofMap F = x := ⟨_,hn⟩
  rw [face_ofMap, endpointCell_ofMap, endpointCell_ofMap, restrictCylinder_endpoint_top]

lemma endpointCell_comp (a : Bool) (x y : Cell Y) (k : ℕ) (h : face k true x = face k false y)
    (h' : Y.target k (endpointCell a x) = Y.source k (endpointCell a y)) :
    endpointCell a (comp k x y h) = Y.comp k (endpointCell a x) (endpointCell a y) h' := by
  let N := max (k+1) (max (bound x) (bound y))
  have hk : k < N := by omega
  have hx : Bounded N x := (bounded_bound x).mono (by omega)
  have hy : Bounded N y := (bounded_bound y).mono (by omega)
  clear_value N
  obtain ⟨F,rfl⟩ : ∃ F : OmegaCategory.Functor (K.{u} N).nu Y, ofMap F = x := ⟨_,hx⟩
  obtain ⟨G,rfl⟩ : ∃ G : OmegaCategory.Functor (K.{u} N).nu Y, ofMap G = y := ⟨_,hy⟩
  simp only [comp_ofMap hk, endpointCell_ofMap] at h' ⊢
  rw [pasteCylinder_endpoint_top, Y.join_eq k _ _ h']

end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

structure CellWeight (Y : OmegaCategory.{v}) (d : ℕ) (A : Type w) [AddCommMonoid A] where
  apply : Y.Cell → A
  add : ∀ k, k < d → ∀ x y, Y.target k x = Y.source k y →
    apply (Y.join k x y) = apply x + apply y
  vanish : ∀ k, k < d → ∀ x, Y.source k x = x → apply x = 0

namespace CellWeight
variable {Y : OmegaCategory.{v}} {A : Type w} [AddCommMonoid A]
instance instCoeFunForallCell {d : ℕ} : CoeFun (CellWeight Y d A) (fun _ => Y.Cell → A) := ⟨apply⟩

def hom {d : ℕ} (q : CellWeight Y (d+1) A) (a b : Y.Cell) :
    CellWeight (Y.homCategory a b) d A where
  apply x := q x.val
  add k hk x y h := by
    rw [hom_join_val k x y h]
    exact q.add (k+1) (by omega) x.val y.val (congrArg Subtype.val h)
  vanish k hk x h := q.vanish (k+1) (by omega) x.val (congrArg Subtype.val h)

def row (M : DirectedComplex.{v}) (d : ℕ) (b : Bool) : CellWeight M.nu d (M.Chain d) where
  apply x := x.row d b
  add k hk x y h := by
    rw [M.nu.join_eq k x y h]
    change (DirectedComplex.Table.comp k x y h).row d b = _
    erw [comp_row]
    simp only [show ¬d < k by omega, show d ≠ k by omega, ite_false]
  vanish k hk x h := row_above_fixed x h hk b
end CellWeight

end Thomason.GrayRecursive

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_StandardComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Standard Comparison. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex
open CategoryTheory

def cylinderFunctor : DirectedComplex.{u} ⥤ DirectedComplex.{u} where
  obj := cylinder
  map := Hom.cylinder
  map_id _ := Hom.cylinder_id
  map_comp f g := Hom.cylinder_comp f g

end Thomason.DirectedComplex

end

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory DirectedComplex NormalizedChains

def raisedOrientalChain (N : ℕ) {K : DirectedComplex.{v}}
    (F : OmegaCategory.Functor (complex (ULift.{u} (Fin (N+1)))).nu K.nu) :
    Hom (complex (ULift.{u} (Fin (N+1)))) K :=
  Hom.comp (complexMap (orderULiftDown (Fin (N+1))))
    (orientalChain N (OmegaCategory.Functor.comp
      (complexMap (orderULiftUp (Fin (N+1)))).nu F))

lemma raisedOrientalChain_nu (N : ℕ) {K : DirectedComplex.{v}}
    (F : OmegaCategory.Functor (complex (ULift.{u} (Fin (N+1)))).nu K.nu) :
    (raisedOrientalChain N F).nu = F := by
  have he : Hom.comp (complexMap (orderULiftDown (Fin (N+1))))
      (complexMap (orderULiftUp (Fin (N+1)))) =
      Hom.id (complex (ULift.{u} (Fin (N+1)))) := by
    rw [← complexMap_comp, orderULiftDown_up, complexMap_id]
  apply OmegaCategory.Functor.ext
  funext x
  change (orientalChain N _).nu.map
    ((complexMap (orderULiftDown (Fin (N+1)))).nu.map x) = _
  rw [orientalChain_nu]
  change F.map (((Hom.comp (complexMap (orderULiftDown (Fin (N+1))))
    (complexMap (orderULiftUp (Fin (N+1))))).nu.map x)) = F.map x
  rw [he]
  rfl

lemma raisedOrientalChain_of_nu (N : ℕ) {K : DirectedComplex.{v}}
    (f : Hom (complex (ULift.{u} (Fin (N+1)))) K) :
    raisedOrientalChain N f.nu = f := by
  unfold raisedOrientalChain
  change Hom.comp (complexMap (orderULiftDown (Fin (N+1))))
    (orientalChain N (Hom.comp (complexMap (orderULiftUp (Fin (N+1)))) f).nu) = f
  rw [orientalChain_of_nu]
  change Hom.comp (Hom.comp (complexMap (orderULiftDown (Fin (N+1))))
    (complexMap (orderULiftUp (Fin (N+1))))) f = f
  rw [← complexMap_comp, orderULiftDown_up, complexMap_id]
  rfl

lemma raisedOriental_nu_injective {N : ℕ} {K : DirectedComplex.{v}}
    {f g : Hom (complex (ULift.{u} (Fin (N+1)))) K} (h : f.nu = g.nu) : f = g := by
  simpa only [raisedOrientalChain_of_nu] using congrArg (raisedOrientalChain N) h

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains
open CategoryTheory DirectedComplex DirectedComplex.Table

lemma table_truncated_of_card_le {P : Type u} [LinearOrder P] [Fintype P]
    {n : ℕ} (h : Fintype.card P ≤ n+1) : (complex P).nu.IsTruncated n := by
  intro x
  apply dimension_of_rows_above_zero
  intro p hp b
  apply Subtype.ext
  exact grade_eq_zero_of_card_lt (E := P) (k := p+1) (x.row p b).property (by omega)

lemma edgeTable_bounded {P : Type u} [PartialOrder P] (a b : P) (h : a ≤ b) :
    truncate 1 false (edgeTable a b h) = edgeTable a b h := by
  apply dimension_of_rows_above_zero
  intro p hp e
  cases p with
  | zero => omega
  | succ p => cases p with
    | zero => omega
    | succ p => rfl

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.GlobeComplex
open CategoryTheory DirectedComplex DirectedComplex.Table

def topOneArrow : OmegaCategory.OneHom (complex.{u} 1).nu
    ((complex.{u} 1).nu.sourceObject (topTable 1))
    ((complex.{u} 1).nu.targetObject (topTable 1)) :=
  ⟨topTable 1, topTable_bounded 1, rfl, rfl⟩

def simplexOneFunctor : OmegaCategory.Functor (NormalizedChains.complex (Fin 2)).nu
    (complex.{u} 1).nu :=
  NormalizedChains.ordinalDiagramFunctor (ComposableArrows.mk₁ topOneArrow)

lemma simplexOneFunctor_edge :
    simplexOneFunctor.{u}.map (NormalizedChains.edgeTable 0 1 (by decide)) = topTable 1 := by
  unfold simplexOneFunctor NormalizedChains.ordinalDiagramFunctor
  change (complex 1).nu.oneSkeletonEvaluation.map
    ((OmegaCategory.ofCategoryMap (ComposableArrows.mk₁ topOneArrow)).map
      (NormalizedChains.tableEndpoints.map (NormalizedChains.edgeTable 0 1 (by decide)))) = _
  rw [NormalizedChains.tableEndpoints_edge]
  rfl

lemma simplexOneFunctor_vertex (b : Fin 2) :
    simplexOneFunctor.{u}.map (NormalizedChains.vertexTable b) =
      truncate 0 (decide (b = 1)) (topTable 1) := by
  unfold simplexOneFunctor NormalizedChains.ordinalDiagramFunctor
  change (complex 1).nu.oneSkeletonEvaluation.map
    ((OmegaCategory.ofCategoryMap (ComposableArrows.mk₁ topOneArrow)).map
      (NormalizedChains.tableEndpoints.map (NormalizedChains.vertexTable b))) = _
  rw [NormalizedChains.tableEndpoints_vertex]
  fin_cases b <;> rfl

def toSimplexOne : Hom (complex.{u} 1)
    (NormalizedChains.complex (ULift.{u} (Fin 2))) :=
  tableMap 1 (NormalizedChains.edgeTable ⟨0⟩ ⟨1⟩ (by decide))

def fromSimplexOne : Hom (NormalizedChains.complex (ULift.{u} (Fin 2)))
    (complex.{u} 1) :=
  Hom.comp (NormalizedChains.complexMap (NormalizedChains.orderULiftDown (Fin 2)))
    (orientalChain 1 simplexOneFunctor)

lemma toSimplexOne_top : toSimplexOne.{u}.nu.map (topTable 1) =
    NormalizedChains.edgeTable ⟨0⟩ ⟨1⟩ (by decide) := by
  rw [toSimplexOne, tableMap_nu_top, NormalizedChains.edgeTable_bounded]

lemma fromSimplexOne_edge : fromSimplexOne.{u}.nu.map
    (NormalizedChains.edgeTable ⟨0⟩ ⟨1⟩ (by decide)) = topTable 1 := by
  change (orientalChain 1 simplexOneFunctor).nu.map
    ((NormalizedChains.complexMap (NormalizedChains.orderULiftDown (Fin 2))).nu.map _) = _
  erw [NormalizedChains.complexMap_edge, orientalChain_nu]
  exact simplexOneFunctor_edge

lemma to_fromSimplexOne : Hom.comp toSimplexOne.{u} fromSimplexOne = Hom.id (complex 1) := by
  apply hom_ext
  change fromSimplexOne.nu.map (toSimplexOne.nu.map (topTable 1)) = topTable 1
  rw [toSimplexOne_top, fromSimplexOne_edge]

lemma fromSimplexOne_vertex (b : Fin 2) :
    fromSimplexOne.{u}.nu.map (NormalizedChains.vertexTable ⟨b⟩) =
      truncate 0 (decide (b = 1)) (topTable 1) := by
  change (orientalChain 1 simplexOneFunctor).nu.map
    ((NormalizedChains.complexMap (NormalizedChains.orderULiftDown (Fin 2))).nu.map _) = _
  erw [NormalizedChains.complexMap_vertex, orientalChain_nu]
  exact simplexOneFunctor_vertex b

lemma toSimplexOne_face (b : Bool) :
    toSimplexOne.{u}.nu.map (truncate 0 b (topTable 1)) =
      NormalizedChains.vertexTable ⟨if b then 1 else 0⟩ := by
  have h := toSimplexOne.{u}.nu.map_face 0 b (topTable 1)
  rw [face_nu, toSimplexOne_top] at h
  cases b
  · exact h.trans (NormalizedChains.edgeTable_source _ _ _)
  · exact h.trans (NormalizedChains.edgeTable_target _ _ _)

lemma from_toSimplexOne : Hom.comp fromSimplexOne.{u} toSimplexOne =
    Hom.id (NormalizedChains.complex (ULift.{u} (Fin 2))) := by
  apply raisedOriental_nu_injective (N := 1)
  apply OmegaCategory.Functor.ext
  funext x
  change toSimplexOne.nu.map (fromSimplexOne.nu.map x) = x
  have hdim : (NormalizedChains.complex (ULift.{u} (Fin 2))).nu.IsTruncated 1 :=
    NormalizedChains.table_truncated_of_card_le (by simp)
  have hx := NormalizedChains.map_table_eq_edge hdim
    (OmegaCategory.Functor.id _) x
  change x = NormalizedChains.edgeTable (NormalizedChains.tableStart x)
    (NormalizedChains.tableFinish x) (NormalizedChains.tableStart_le_finish x) at hx
  have hedge : ∀ (a b : ULift.{u} (Fin 2)) (h : a ≤ b),
      toSimplexOne.nu.map (fromSimplexOne.nu.map (NormalizedChains.edgeTable a b h)) =
        NormalizedChains.edgeTable a b h := by
    rintro ⟨a⟩ ⟨b⟩ hab
    fin_cases a <;> fin_cases b
    · rw [NormalizedChains.edgeTable_diagonal, fromSimplexOne_vertex, toSimplexOne_face]
      rfl
    · exact (congrArg toSimplexOne.nu.map fromSimplexOne_edge).trans toSimplexOne_top
    · exact False.elim (by simp at hab)
    · rw [NormalizedChains.edgeTable_diagonal, fromSimplexOne_vertex, toSimplexOne_face]
      rfl
  rw [hx]
  exact hedge _ _ _

def simplexOneIso : complex.{u} 1 ≅ NormalizedChains.complex (ULift.{u} (Fin 2)) where
  hom := toSimplexOne
  inv := fromSimplexOne
  hom_inv_id := to_fromSimplexOne
  inv_hom_id := from_toSimplexOne

end Thomason.GlobeComplex

end

noncomputable section
universe u v w z


namespace Thomason.GlobeComplex
open CategoryTheory DirectedComplex DirectedComplex.Table

def toSimplexZero : Hom (complex.{u} 0)
    (NormalizedChains.complex (ULift.{u} (Fin 1))) :=
  tableMap 0 (NormalizedChains.vertexTable ⟨0⟩)

def fromSimplexZero : Hom (NormalizedChains.complex (ULift.{u} (Fin 1)))
    (complex.{u} 0) :=
  raisedOrientalChain 0 (OmegaCategory.constantAt _ (topTable 0) (topTable_bounded 0))

lemma fromSimplexZero_nu (x : (NormalizedChains.complex (ULift.{u} (Fin 1))).nu.Cell) :
    fromSimplexZero.{u}.nu.map x = topTable 0 := by
  unfold fromSimplexZero
  rw [raisedOrientalChain_nu]
  rfl

lemma toSimplexZero_top : toSimplexZero.{u}.nu.map (topTable 0) =
    NormalizedChains.vertexTable ⟨0⟩ := by
  rw [toSimplexZero, tableMap_nu_top]
  exact NormalizedChains.vertexTable_source _

lemma simplexZero_table_unique (x : (NormalizedChains.complex (ULift.{u} (Fin 1))).nu.Cell) :
    x = NormalizedChains.vertexTable ⟨0⟩ := by
  have hdim : (NormalizedChains.complex (ULift.{u} (Fin 1))).nu.IsTruncated 1 :=
    NormalizedChains.table_truncated_of_card_le (by simp)
  have hx := NormalizedChains.map_table_eq_edge hdim
    (OmegaCategory.Functor.id _) x
  change x = NormalizedChains.edgeTable (NormalizedChains.tableStart x)
    (NormalizedChains.tableFinish x) (NormalizedChains.tableStart_le_finish x) at hx
  have hs : NormalizedChains.tableStart x = (⟨0⟩ : ULift.{u} (Fin 1)) := Subsingleton.elim _ _
  have ht : NormalizedChains.tableFinish x = (⟨0⟩ : ULift.{u} (Fin 1)) := Subsingleton.elim _ _
  simp only [hs, ht, NormalizedChains.edgeTable_diagonal] at hx
  exact hx

lemma to_fromSimplexZero : Hom.comp toSimplexZero.{u} fromSimplexZero = Hom.id (complex 0) := by
  apply hom_ext
  change fromSimplexZero.nu.map (toSimplexZero.nu.map (topTable 0)) = topTable 0
  exact fromSimplexZero_nu _

lemma from_toSimplexZero : Hom.comp fromSimplexZero.{u} toSimplexZero =
    Hom.id (NormalizedChains.complex (ULift.{u} (Fin 1))) := by
  apply raisedOriental_nu_injective (N := 0)
  apply OmegaCategory.Functor.ext
  funext x
  change toSimplexZero.nu.map (fromSimplexZero.nu.map x) = x
  rw [fromSimplexZero_nu, toSimplexZero_top, simplexZero_table_unique x]

def simplexZeroIso : complex.{u} 0 ≅ NormalizedChains.complex (ULift.{u} (Fin 1)) where
  hom := toSimplexZero
  inv := fromSimplexZero
  hom_inv_id := to_fromSimplexZero
  inv_hom_id := from_toSimplexZero

end Thomason.GlobeComplex

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_CylinderProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cylinder Profiles. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex

namespace CylinderTables
open Table
variable {M : DirectedComplex.{u}}

def side (t : Table M.cylinder) (a : Bool) : (p : ℕ) → Bool → M.Chain p
  | 0, b => if a then (t.row 0 b).2 else (t.row 0 b).1
  | p+1, b => if a then (t.row (p+1) b).2.1 else (t.row (p+1) b).1

def cross (t : Table M.cylinder) (p : ℕ) (b : Bool) : M.Chain p :=
  (t.row (p+1) b).2.2

def project (t : Table M.cylinder) : Table M := M.cylinderProjection.table t

def label (t : Table M.cylinder) (b : Bool) : ℤ := M.augmentation (side t true 0 b)

lemma side_positive (t : Table M.cylinder) (a : Bool) (p : ℕ) (b : Bool) :
    side t a p b ∈ M.positive p := by
  cases p with
  | zero => cases a; exact (t.positive 0 b).1; exact (t.positive 0 b).2
  | succ p => cases a; exact (t.positive (p+1) b).1; exact (t.positive (p+1) b).2.1

lemma cross_positive (t : Table M.cylinder) (p : ℕ) (b : Bool) :
    cross t p b ∈ M.positive p := (t.positive (p+1) b).2.2

lemma cross_boundary (t : Table M.cylinder) (p : ℕ) (b : Bool) :
    M.d p (cross t (p+1) b) = cross t p true - cross t p false :=
  congrArg (fun x : M.cylinder.Chain (p+1) => x.2.2) (t.boundary (p+1) b)

lemma left_boundary (t : Table M.cylinder) (p : ℕ) (b : Bool) :
    M.d p (side t false (p+1) b) - (-1 : ℤ)^p • cross t p b =
      side t false p true - side t false p false := by
  cases p with
  | zero => simpa [side,cross,cylinderDifferential] using congrArg Prod.fst (t.boundary 0 b)
  | succ p => exact congrArg Prod.fst (t.boundary (p+1) b)

lemma right_boundary (t : Table M.cylinder) (p : ℕ) (b : Bool) :
    M.d p (side t true (p+1) b) + (-1 : ℤ)^p • cross t p b =
      side t true p true - side t true p false := by
  cases p with
  | zero => simpa [side,cross,cylinderDifferential] using congrArg Prod.snd (t.boundary 0 b)
  | succ p => exact congrArg (fun x : M.cylinder.Chain (p+1) => x.2.1) (t.boundary (p+1) b)

lemma augmentation_sides (t : Table M.cylinder) (b : Bool) :
    M.augmentation (side t false 0 b) + M.augmentation (side t true 0 b) = 1 :=
  t.augmentation b

lemma augmentation_cross (t : Table M.cylinder) (b : Bool) :
    M.augmentation (cross t 0 b) = label t true - label t false := by
  have h := congrArg M.augmentation (right_boundary t 0 b)
  simpa only [map_add,map_smul,pow_zero,one_smul,M.augmentation_d,zero_add,map_sub,label] using h

variable (hM : PositiveAcyclic M)
include hM

omit hM in
lemma crossing_augmentation (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1) (b : Bool) :
    M.augmentation (cross t 0 b) = 1 := by rw [augmentation_cross,hs,ht,sub_zero]

lemma crossing_starts_ends (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1) :
    side t true 0 false = 0 ∧ side t false 0 true = 0 := by
  constructor
  · exact hM.augmentation_zero _ (side_positive t true 0 false) hs
  · apply hM.augmentation_zero _ (side_positive t false 0 true)
    have h := augmentation_sides t true
    change M.augmentation (side t false 0 true) + label t true = 1 at h
    omega

end CylinderTables
end Thomason.DirectedComplex

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.CylinderTables
open Table
variable {M : DirectedComplex.{u}}

lemma side_of_row_zero (t : Table M.cylinder) (a : Bool) (p : ℕ) (b : Bool)
    (h : t.row p b = 0) : side t a p b = 0 := by
  cases p with
  | zero => cases a; exact congrArg Prod.fst h; exact congrArg Prod.snd h
  | succ p => cases a; exact congrArg Prod.fst h; exact congrArg (fun x => x.2.1) h

lemma cross_of_row_zero (t : Table M.cylinder) (p : ℕ) (b : Bool)
    (h : t.row (p+1) b = 0) : cross t p b = 0 := congrArg (fun x => x.2.2) h

def crossingProfile (t : Table M.cylinder) (hs : label t false = 0) (ht : label t true = 1) :
    Table M where
  row := cross t
  positive := cross_positive t
  boundary := cross_boundary t
  augmentation := crossing_augmentation t hs ht
  bounded := by
    obtain ⟨n,hn⟩ := t.bounded
    exact ⟨n,fun p hp b => cross_of_row_zero t p b (hn (p+1) (by omega) b)⟩

def leftProfileRow (t : Table M.cylinder) (p : ℕ) (b : Bool) : M.Chain p :=
  side t false p b + if Even p then (if b then cross t p b else 0) else (if b then 0 else cross t p b)

def rightProfileRow (t : Table M.cylinder) (p : ℕ) (b : Bool) : M.Chain p :=
  side t true p b + if Even p then (if b then 0 else cross t p b) else (if b then cross t p b else 0)

lemma left_d (t : Table M.cylinder) (p : ℕ) (b : Bool) :
    M.d p (side t false (p+1) b) = side t false p true - side t false p false + (-1 : ℤ)^p • cross t p b :=
  eq_add_of_sub_eq (left_boundary t p b)

lemma right_d (t : Table M.cylinder) (p : ℕ) (b : Bool) :
    M.d p (side t true (p+1) b) = side t true p true - side t true p false - (-1 : ℤ)^p • cross t p b :=
  eq_sub_of_add_eq (right_boundary t p b)

lemma leftProfileRow_boundary (t : Table M.cylinder) (p : ℕ) (b : Bool) :
    M.d p (leftProfileRow t (p+1) b) = leftProfileRow t p true - leftProfileRow t p false := by
  unfold leftProfileRow
  simp only [Nat.even_add_one]
  by_cases hp : Even p <;> cases b <;>
    simp only [hp,not_true_eq_false,not_false_eq_true,ite_true,ite_false,Bool.false_eq_true,
      map_add,map_zero,left_d,cross_boundary,neg_one_pow_eq_ite,one_smul,neg_smul] <;> abel

lemma rightProfileRow_boundary (t : Table M.cylinder) (p : ℕ) (b : Bool) :
    M.d p (rightProfileRow t (p+1) b) = rightProfileRow t p true - rightProfileRow t p false := by
  unfold rightProfileRow
  simp only [Nat.even_add_one]
  by_cases hp : Even p <;> cases b <;>
    simp only [hp,not_true_eq_false,not_false_eq_true,ite_true,ite_false,Bool.false_eq_true,
      map_add,map_zero,right_d,cross_boundary,neg_one_pow_eq_ite,one_smul,neg_smul] <;> abel

def leftProfile (t : Table M.cylinder) (hs : label t false = 0) (ht : label t true = 1) : Table M where
  row := leftProfileRow t
  positive p b := by
    apply (M.positive p).add_mem (side_positive t false p b)
    split_ifs <;> first | exact cross_positive t p b | exact (M.positive p).zero_mem
  boundary := leftProfileRow_boundary t
  augmentation b := by
    have h := augmentation_sides t b
    have hc := crossing_augmentation t hs ht b
    cases b <;>
      simp only [leftProfileRow,Even.zero,ite_true,Bool.false_eq_true,ite_false,map_add,map_zero]
    · change M.augmentation (side t false 0 false) + label t false = 1 at h
      omega
    · change M.augmentation (side t false 0 true) + label t true = 1 at h
      omega
  bounded := by
    obtain ⟨n,hn⟩ := t.bounded
    refine ⟨n,fun p hp b => ?_⟩
    have ha := side_of_row_zero t false p b (hn p hp b)
    have hc := cross_of_row_zero t p b (hn (p+1) (by omega) b)
    simp only [leftProfileRow,ha,hc,ite_self,add_zero]

def rightProfile (t : Table M.cylinder) (hs : label t false = 0) (ht : label t true = 1) : Table M where
  row := rightProfileRow t
  positive p b := by
    apply (M.positive p).add_mem (side_positive t true p b)
    split_ifs <;> first | exact cross_positive t p b | exact (M.positive p).zero_mem
  boundary := rightProfileRow_boundary t
  augmentation b := by
    have hc := crossing_augmentation t hs ht b
    cases b <;>
      simp only [rightProfileRow,Even.zero,ite_true,Bool.false_eq_true,ite_false,map_add,map_zero]
    · change M.augmentation (side t true 0 false) = 0 at hs
      omega
    · simpa only [label,add_zero] using ht
  bounded := by
    obtain ⟨n,hn⟩ := t.bounded
    refine ⟨n,fun p hp b => ?_⟩
    have ha := side_of_row_zero t true p b (hn p hp b)
    have hc := cross_of_row_zero t p b (hn (p+1) (by omega) b)
    simp only [rightProfileRow,ha,hc,ite_self,add_zero]

end Thomason.DirectedComplex.CylinderTables

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_EdgeComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Edge Comparison. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.CylinderTables
open Table
variable {M : DirectedComplex.{u}}

lemma crossingProfile_bounded {n : ℕ} (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1)
    (hb : truncate (n+1) false t = t) :
    truncate n false (crossingProfile t hs ht) = crossingProfile t hs ht := by
  apply dimension_of_rows_above_zero
  intro p hp b
  exact cross_of_row_zero t p b (row_above_fixed t hb (by omega) b)

lemma leftProfile_bounded {n : ℕ} (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1)
    (hb : truncate n false t = t) :
    truncate n false (leftProfile t hs ht) = leftProfile t hs ht := by
  apply dimension_of_rows_above_zero
  intro p hp b
  change leftProfileRow t p b = 0
  have ha := side_of_row_zero t false p b (row_above_fixed t hb hp b)
  have hc := cross_of_row_zero t p b (row_above_fixed t hb (by omega) b)
  simp only [leftProfileRow,ha,hc,ite_self,add_zero]

lemma rightProfile_bounded {n : ℕ} (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1)
    (hb : truncate n false t = t) :
    truncate n false (rightProfile t hs ht) = rightProfile t hs ht := by
  apply dimension_of_rows_above_zero
  intro p hp b
  change rightProfileRow t p b = 0
  have ha := side_of_row_zero t true p b (row_above_fixed t hb hp b)
  have hc := cross_of_row_zero t p b (row_above_fixed t hb (by omega) b)
  simp only [rightProfileRow,ha,hc,ite_self,add_zero]

lemma object_rows_equal (c : Table M) (hc : truncate 0 false c = c) (a b : Bool) :
    c.row 0 a = c.row 0 b := by
  have h (e : Bool) : c.row 0 false = c.row 0 e := by
    simpa only [truncate_top_row] using congrArg (fun x : Table M => x.row 0 e) hc
  exact (h a).symm.trans (h b)

lemma vertical_object_face (c : Table M) (hc : truncate 0 false c = c) (a : Bool) :
    truncate 0 a (verticalTable c) = (M.cylinderEndpoint a).table c := by
  ext p b
  change (truncate 0 a (verticalTable c)).row p b = M.cylinderEndpointMap a p (c.row p b)
  cases p with
  | zero =>
    rw [truncate_top_row]
    change verticalRow c 0 a = M.cylinderEndpointMap a 0 (c.row 0 b)
    cases a <;> simp only [verticalRow,Bool.false_eq_true,ite_false,ite_true,
      object_rows_equal c hc _ b] <;> rfl
  | succ p =>
    rw [truncate_row]
    simp only [show ¬p+1 < 0 by omega,show p+1 ≠ 0 by omega,ite_false,
      row_above_fixed c hc (by omega : 0 < p+1),map_zero]

lemma crossing_edge_left_target (hM : PositiveAcyclic M) (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1) (hb : truncate 1 false t = t) :
    truncate 0 true (leftProfile t hs ht) = crossingProfile t hs ht := by
  have hz := (crossing_starts_ends hM t hs ht).2
  have hc := crossingProfile_bounded t hs ht hb
  ext p b
  cases p with
  | zero =>
    rw [truncate_top_row]
    change leftProfileRow t 0 true = (crossingProfile t hs ht).row 0 b
    simp only [leftProfileRow, Even.zero, ite_true, hz, zero_add]
    exact object_rows_equal (crossingProfile t hs ht) hc true b
  | succ p =>
    rw [truncate_row]
    simp only [show ¬p+1 < 0 by omega,show p+1 ≠ 0 by omega,ite_false,
      row_above_fixed _ hc (by omega : 0 < p+1)]

lemma crossing_edge_right_source (hM : PositiveAcyclic M) (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1) (hb : truncate 1 false t = t) :
    truncate 0 false (rightProfile t hs ht) = crossingProfile t hs ht := by
  have hz := (crossing_starts_ends hM t hs ht).1
  have hc := crossingProfile_bounded t hs ht hb
  ext p b
  cases p with
  | zero =>
    rw [truncate_top_row]
    change rightProfileRow t 0 false = (crossingProfile t hs ht).row 0 b
    simp only [rightProfileRow, Even.zero, ite_true, Bool.false_eq_true, ite_false, hz, zero_add]
    exact object_rows_equal (crossingProfile t hs ht) hc false b
  | succ p =>
    rw [truncate_row]
    simp only [show ¬p+1 < 0 by omega,show p+1 ≠ 0 by omega,ite_false,
      row_above_fixed _ hc (by omega : 0 < p+1)]

lemma crossing_edge_matching_left (hM : PositiveAcyclic M) (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1) (hb : truncate 1 false t = t) :
    truncate 0 true ((M.cylinderEndpoint false).table (leftProfile t hs ht)) =
      truncate 0 false (verticalTable (crossingProfile t hs ht)) := by
  rw [vertical_object_face _ (crossingProfile_bounded t hs ht hb), ← Hom.table_truncate,
    crossing_edge_left_target hM t hs ht hb]

lemma crossing_edge_matching_right (hM : PositiveAcyclic M) (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1) (hb : truncate 1 false t = t) :
    truncate 0 true (comp 0 ((M.cylinderEndpoint false).table (leftProfile t hs ht))
      (verticalTable (crossingProfile t hs ht)) (crossing_edge_matching_left hM t hs ht hb)) =
      truncate 0 false ((M.cylinderEndpoint true).table (rightProfile t hs ht)) := by
  rw [target_comp_le 0 0 le_rfl, vertical_object_face _ (crossingProfile_bounded t hs ht hb),
    ← Hom.table_truncate,crossing_edge_right_source hM t hs ht hb]

end Thomason.DirectedComplex.CylinderTables

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {M : DirectedComplex.{u}}

lemma table_join_zero_row_succ (x y : Table M)
    (h : truncate 0 true x = truncate 0 false y) (p : ℕ) (b : Bool) :
    (M.nu.join 0 x y).row (p+1) b = x.row (p+1) b + y.row (p+1) b := by
  rw [M.nu.join_eq 0 x y h]
  change (DirectedComplex.Table.comp 0 x y h).row (p+1) b = _
  simp only [comp_row, Nat.not_lt_zero, Nat.add_one_ne_zero, ite_false]

lemma table_join_zero_row_zero (x y : Table M)
    (h : truncate 0 true x = truncate 0 false y) (b : Bool) :
    (M.nu.join 0 x y).row 0 b = if b then y.row 0 true else x.row 0 false := by
  rw [M.nu.join_eq 0 x y h]
  rfl

end Thomason.GrayRecursive.IntervalHom

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_BoundedCylinders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded Cylinders. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.CylinderTables
open Table
variable {M : DirectedComplex.{u}}

lemma truncate_zero_ext (x y : Table M) (a b : Bool)
    (h : x.row 0 a = y.row 0 b) : truncate 0 a x = truncate 0 b y := by
  ext p e
  cases p with
  | zero => exact h
  | succ p => rfl

lemma truncate_one_ext (x y : Table M) (a b : Bool)
    (h₀ : ∀ e, x.row 0 e = y.row 0 e) (h₁ : x.row 1 a = y.row 1 b) :
    truncate 1 a x = truncate 1 b y := by
  ext p e
  cases p with
  | zero => exact h₀ e
  | succ p => cases p with
    | zero => exact h₁
    | succ p => rfl

def tableSandwich (l c r : Table M) : Table M.cylinder :=
  M.cylinder.nu.join 0
    (M.cylinder.nu.join 0 ((M.cylinderEndpoint false).table l) (verticalTable c))
    ((M.cylinderEndpoint true).table r)

lemma tableSandwich_match_left (l c : Table M) (hl : l.row 0 true = c.row 0 false) :
    truncate 0 true ((M.cylinderEndpoint false).table l) = truncate 0 false (verticalTable c) := by
  apply truncate_zero_ext
  change (l.row 0 true, 0) = (c.row 0 false, 0)
  rw [hl]

lemma tableSandwich_match_right (l c r : Table M)
    (hl : l.row 0 true = c.row 0 false) (hr : r.row 0 false = c.row 0 true) :
    truncate 0 true (M.cylinder.nu.join 0 ((M.cylinderEndpoint false).table l) (verticalTable c)) =
      truncate 0 false ((M.cylinderEndpoint true).table r) := by
  apply (M.cylinder.nu.join_target_le 0 0 _ _ le_rfl (tableSandwich_match_left l c hl)).trans
  apply truncate_zero_ext
  change (0, c.row 0 true) = (0, r.row 0 false)
  rw [hr]

lemma tableSandwich_zero (l c r : Table M)
    (hl : l.row 0 true = c.row 0 false) (hr : r.row 0 false = c.row 0 true) (b : Bool) :
    (tableSandwich l c r).row 0 b = if b then (0,r.row 0 true) else (l.row 0 false,0) := by
  unfold tableSandwich
  rw [GrayRecursive.IntervalHom.table_join_zero_row_zero _ _ (tableSandwich_match_right l c r hl hr),
      GrayRecursive.IntervalHom.table_join_zero_row_zero _ _ (tableSandwich_match_left l c hl)]
  cases b <;> rfl

lemma tableSandwich_succ (l c r : Table M)
    (hl : l.row 0 true = c.row 0 false) (hr : r.row 0 false = c.row 0 true)
    (p : ℕ) (b : Bool) :
    (tableSandwich l c r).row (p+1) b =
      M.cylinderEndpointMap false (p+1) (l.row (p+1) b) + verticalRow c (p+1) b +
      M.cylinderEndpointMap true (p+1) (r.row (p+1) b) := by
  unfold tableSandwich
  rw [GrayRecursive.IntervalHom.table_join_zero_row_succ _ _ (tableSandwich_match_right l c r hl hr),
      GrayRecursive.IntervalHom.table_join_zero_row_succ _ _ (tableSandwich_match_left l c hl)]
  rfl

lemma crossingProfile_face_zero (t : Table M.cylinder) (hs : label t false = 0)
    (ht : label t true = 1) (b : Bool) :
    (crossingProfile t hs ht).row 0 b = cross t 0 b := rfl

lemma profile_left_zero (hM : PositiveAcyclic M) (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1) (b : Bool) :
    (leftProfile t hs ht).row 0 b = if b then cross t 0 true else side t false 0 false := by
  obtain ⟨_,htgt⟩ := crossing_starts_ends hM t hs ht
  cases b <;> simp only [leftProfile, leftProfileRow, Even.zero, Bool.false_eq_true,
    ite_false, ite_true, add_zero, htgt, zero_add]

lemma profile_right_zero (hM : PositiveAcyclic M) (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1) (b : Bool) :
    (rightProfile t hs ht).row 0 b = if b then side t true 0 true else cross t 0 false := by
  obtain ⟨hsrc,_⟩ := crossing_starts_ends hM t hs ht
  cases b <;> simp only [rightProfile, rightProfileRow, Even.zero, Bool.false_eq_true,
    ite_false, ite_true, add_zero, hsrc, zero_add]

def profileEdge (t : Table M.cylinder) (hs : label t false = 0) (ht : label t true = 1)
    (a b : Bool) : Table M :=
  if a then rightProfile (truncate 1 b t) hs ht else leftProfile (truncate 1 b t) hs ht

lemma profileEdge_bounded (t : Table M.cylinder) (hs : label t false = 0) (ht : label t true = 1)
    (a b : Bool) : truncate 1 false (profileEdge t hs ht a b) = profileEdge t hs ht a b := by
  have h : truncate 1 false (truncate 1 b t) = truncate 1 b t := by simp only [truncate_truncate, lt_self_iff_false, ite_false]
  cases a
  · exact leftProfile_bounded (truncate 1 b t) hs ht h
  · exact rightProfile_bounded (truncate 1 b t) hs ht h

lemma profileEdge_zero (hM : PositiveAcyclic M) (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1) (a b e : Bool) :
    (profileEdge t hs ht a b).row 0 e =
      if a then (if e then side t true 0 true else cross t 0 b)
      else (if e then cross t 0 b else side t false 0 false) := by
  cases a
  · change (leftProfile (truncate 1 b t) hs ht).row 0 e = _
    erw [profile_left_zero hM]
    cases e <;> rfl
  · change (rightProfile (truncate 1 b t) hs ht).row 0 e = _
    erw [profile_right_zero hM]
    cases e <;> rfl

lemma profileEdge_one (t : Table M.cylinder) (hs : label t false = 0) (ht : label t true = 1)
    (a b e : Bool) : (profileEdge t hs ht a b).row 1 e = side t a 1 b := by
  cases a <;> cases e <;>
    change _ + (0 : M.Chain 1) = _ <;> exact add_zero _

section TwoCell
variable (hM : PositiveAcyclic M) (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1)

def twoRight : Table M.cylinder := tableSandwich (profileEdge t hs ht false false)
  (truncate 0 false (crossingProfile t hs ht)) (rightProfile t hs ht)

def twoMiddle : Table M.cylinder := tableSandwich (profileEdge t hs ht false false)
  (crossingProfile t hs ht) (profileEdge t hs ht true true)

def twoLeft : Table M.cylinder := tableSandwich (leftProfile t hs ht)
  (truncate 0 true (crossingProfile t hs ht)) (profileEdge t hs ht true true)

include hM

lemma twoRight_matches :
    (profileEdge t hs ht false false).row 0 true = (truncate 0 false (crossingProfile t hs ht)).row 0 false ∧
    (rightProfile t hs ht).row 0 false = (truncate 0 false (crossingProfile t hs ht)).row 0 true := by
  simp only [profileEdge_zero hM, profile_right_zero hM, Bool.false_eq_true, ite_false, ite_true,
    truncate_top_row, crossingProfile_face_zero, and_self]

lemma twoMiddle_matches :
    (profileEdge t hs ht false false).row 0 true = (crossingProfile t hs ht).row 0 false ∧
    (profileEdge t hs ht true true).row 0 false = (crossingProfile t hs ht).row 0 true := by
  simp only [profileEdge_zero hM, Bool.false_eq_true, ite_false, ite_true,
    crossingProfile_face_zero, and_self]

lemma twoLeft_matches :
    (leftProfile t hs ht).row 0 true = (truncate 0 true (crossingProfile t hs ht)).row 0 false ∧
    (profileEdge t hs ht true true).row 0 false = (truncate 0 true (crossingProfile t hs ht)).row 0 true := by
  simp only [profile_left_zero hM, profileEdge_zero hM, Bool.false_eq_true, ite_false, ite_true,
    truncate_top_row, crossingProfile_face_zero, and_self]

lemma twoRight_zero (b : Bool) : (twoRight t hs ht).row 0 b = t.row 0 b := by
  obtain ⟨hsrc, htgt⟩ := crossing_starts_ends hM t hs ht
  rw [twoRight, tableSandwich_zero _ _ _ (twoRight_matches hM t hs ht).1 (twoRight_matches hM t hs ht).2,
    profile_right_zero hM, profileEdge_zero hM]
  cases b
  · exact Prod.ext rfl hsrc.symm
  · exact Prod.ext htgt.symm rfl

lemma twoMiddle_zero (b : Bool) : (twoMiddle t hs ht).row 0 b = t.row 0 b := by
  obtain ⟨hsrc, htgt⟩ := crossing_starts_ends hM t hs ht
  rw [twoMiddle, tableSandwich_zero _ _ _ (twoMiddle_matches hM t hs ht).1 (twoMiddle_matches hM t hs ht).2,
    profileEdge_zero hM, profileEdge_zero hM]
  cases b
  · exact Prod.ext rfl hsrc.symm
  · exact Prod.ext htgt.symm rfl

lemma twoLeft_zero (b : Bool) : (twoLeft t hs ht).row 0 b = t.row 0 b := by
  obtain ⟨hsrc, htgt⟩ := crossing_starts_ends hM t hs ht
  rw [twoLeft, tableSandwich_zero _ _ _ (twoLeft_matches hM t hs ht).1 (twoLeft_matches hM t hs ht).2,
    profileEdge_zero hM, profile_left_zero hM]
  cases b
  · exact Prod.ext rfl hsrc.symm
  · exact Prod.ext htgt.symm rfl

lemma twoRight_one (b : Bool) : (twoRight t hs ht).row 1 b =
    (side t false 1 false,
      side t true 1 b + (if b then cross t 1 true else 0), cross t 0 false) := by
  rw [twoRight, tableSandwich_succ _ _ _ (twoRight_matches hM t hs ht).1 (twoRight_matches hM t hs ht).2,
    profileEdge_one]
  cases b <;>
    simp [verticalRow, truncate_row, rightProfile, rightProfileRow, crossingProfile,
      cylinderEndpointMap]

lemma twoMiddle_one (b : Bool) : (twoMiddle t hs ht).row 1 b =
    (side t false 1 false + (if b then cross t 1 true else 0),
      (if b then 0 else cross t 1 false) + side t true 1 true, cross t 0 b) := by
  rw [twoMiddle, tableSandwich_succ _ _ _ (twoMiddle_matches hM t hs ht).1 (twoMiddle_matches hM t hs ht).2,
    profileEdge_one, profileEdge_one]
  cases b <;> simp [verticalRow, crossingProfile, cylinderEndpointMap]

lemma twoLeft_one (b : Bool) : (twoLeft t hs ht).row 1 b =
    (side t false 1 b + (if b then 0 else cross t 1 false), side t true 1 true, cross t 0 true) := by
  rw [twoLeft, tableSandwich_succ _ _ _ (twoLeft_matches hM t hs ht).1 (twoLeft_matches hM t hs ht).2,
    profileEdge_one]
  cases b <;>
    simp [verticalRow, truncate_row, leftProfile, leftProfileRow, crossingProfile,
      cylinderEndpointMap]

variable (hb : truncate 2 false t = t)
include hb

lemma twoRightMiddle_match : truncate 1 true (twoRight t hs ht) = truncate 1 false (twoMiddle t hs ht) := by
  have he : cross t 1 false = cross t 1 true :=
    congrArg (fun z => z.2.2) (row_top_fixed t hb)
  apply truncate_one_ext
  · intro e
    rw [twoRight_zero hM t hs ht, twoMiddle_zero hM t hs ht]
  · rw [twoRight_one hM t hs ht, twoMiddle_one hM t hs ht]
    simp only [ite_true, Bool.false_eq_true, ite_false, add_zero, he, add_comm]

lemma twoMiddleLeft_match : truncate 1 true (twoMiddle t hs ht) = truncate 1 false (twoLeft t hs ht) := by
  have he : cross t 1 false = cross t 1 true :=
    congrArg (fun z => z.2.2) (row_top_fixed t hb)
  apply truncate_one_ext
  · intro e
    rw [twoMiddle_zero hM t hs ht, twoLeft_zero hM t hs ht]
  · rw [twoMiddle_one hM t hs ht, twoLeft_one hM t hs ht]
    simp only [ite_true, Bool.false_eq_true, ite_false, zero_add, he]

lemma twoRightMiddleLeft_match : truncate 1 true
    (comp 1 (twoRight t hs ht) (twoMiddle t hs ht) (twoRightMiddle_match hM t hs ht hb)) =
      truncate 1 false (twoLeft t hs ht) := by
  rw [target_comp_le 1 1 le_rfl]
  exact twoMiddleLeft_match hM t hs ht hb

end TwoCell
end Thomason.DirectedComplex.CylinderTables

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_RankedAtoms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ranked Atoms. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex
open Table

structure RankedAtoms (K : DirectedComplex.{u}) where
  Index : Type v
  finite : Fintype Index
  dim : Index → ℕ
  rank : Index → ℤ
  atom : Index → Table K
  bounded : ∀ b, truncate (dim b) false (atom b) = atom b
  coefficient : (b : Index) → (p : ℕ) → K.Chain p →+ ℤ
  homogeneous : ∀ b p x, coefficient b p x ≠ 0 → dim b = p
  ext : ∀ p (x y : K.Chain p), (∀ b, coefficient b p x = coefficient b p y) → x = y
  positive : ∀ p x, x ∈ K.positive p ↔ ∀ b, 0 ≤ coefficient b p x
  top : ∀ b c e, coefficient c (dim b) ((atom b).row (dim b) e) =
    (by classical exact if b = c then 1 else 0)
  ranked : ∀ b p, p < dim b → ∀ e c,
    coefficient c p ((atom b).row p e) ≠ 0 →
    if e then rank c < rank b else rank b < rank c

attribute [instance] RankedAtoms.finite
namespace RankedAtoms
variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
open scoped Classical
include A
local instance rankedAtomsDecidableEq : DecidableEq A.Index := Classical.decEq _

def basis (p : ℕ) (b : A.Index) : K.Chain p :=
  if h : A.dim b = p then h ▸ (A.atom b).row (A.dim b) false else 0

def mass (p : ℕ) : K.Chain p →+ ℤ := ∑ b, A.coefficient b p

inductive TopPasting (n : ℕ) : Table K → Prop
  | identity x : truncate n false x = x → TopPasting n x
  | basis (x : Table K) (b : A.Index) : truncate (n+1) false x = x →
      A.dim b = n+1 → x.row (n+1) false = A.basis (n+1) b → TopPasting n x
  | compose x y (h : truncate n true x = truncate n false y) :
      TopPasting n x → TopPasting n y → TopPasting n (comp n x y h)

def cut (p : ℕ) (z : K.Chain p) (P : A.Index → Prop) : K.Chain p :=
  ∑ b, if P b then A.coefficient b p z • A.basis p b else 0

inductive AtomPasting : Table K → Prop
  | atom (b : A.Index) : AtomPasting (A.atom b)
  | compose (k : ℕ) (x y) (h : truncate k true x = truncate k false y) :
      AtomPasting x → AtomPasting y → AtomPasting (comp k x y h)

end RankedAtoms
end Thomason.DirectedComplex

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_FiniteGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Gluing. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.RankedAtoms
open Table OmegaCategory CategoryTheory
variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
include A

inductive BoundedPasting (n : ℕ) : Table K → Prop
  | atom (b : A.Index) : A.dim b ≤ n → BoundedPasting n (A.atom b)
  | compose (k : ℕ) (hk : k < n) (x y)
      (h : truncate k true x = truncate k false y) :
      BoundedPasting n x → BoundedPasting n y → BoundedPasting n (comp k x y h)

end Thomason.DirectedComplex.RankedAtoms

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.RankedAtoms
open Table
variable {K : DirectedComplex.{u}} {L : DirectedComplex.{w}}

def transport (A : RankedAtoms.{u,v} K) (f : Hom K L) (g : Hom L K)
    (hfg : Hom.comp f g = Hom.id K) (hgf : Hom.comp g f = Hom.id L) :
    RankedAtoms.{w,v} L where
  Index := A.Index
  finite := A.finite
  dim := A.dim
  rank := A.rank
  atom b := f.table (A.atom b)
  bounded b := by rw [← Hom.table_truncate,A.bounded]
  coefficient b p := (A.coefficient b p).comp (g.map p)
  homogeneous b p x := A.homogeneous b p (g.map p x)
  ext p x y he := by
    have hh : g.map p x = g.map p y := A.ext p _ _ he
    have hi (z : L.Chain p) : f.map p (g.map p z) = z :=
      congrArg (fun h : Hom L L => h.map p z) hgf
    exact (hi x).symm.trans ((congrArg (f.map p) hh).trans (hi y))
  positive p x := by
    constructor
    · intro hx
      exact (A.positive p _).mp (g.map_positive p x hx)
    · intro hx
      have hh := f.map_positive p _ ((A.positive p _).mpr hx)
      change f.map p (g.map p x) ∈ _ at hh
      have hi : f.map p (g.map p x) = x := congrArg (fun h : Hom L L => h.map p x) hgf
      rwa [hi] at hh
  top b c e := by
    change A.coefficient c (A.dim b) (g.map _ (f.map _ ((A.atom b).row (A.dim b) e))) = _
    have hi (z : K.Chain (A.dim b)) : g.map _ (f.map _ z) = z :=
      congrArg (fun h : Hom K K => h.map (A.dim b) z) hfg
    rw [hi,A.top]
  ranked b p hp e c hc := by
    change A.coefficient c p (g.map _ (f.map _ ((A.atom b).row p e))) ≠ 0 at hc
    have hi (z : K.Chain p) : g.map _ (f.map _ z) = z :=
      congrArg (fun h : Hom K K => h.map p z) hfg
    rw [hi] at hc
    exact A.ranked b p hp e c hc

end Thomason.DirectedComplex.RankedAtoms

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_TopSequences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Top Sequences. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

variable (C : OmegaCategory.{u}) (n : ℕ) (G : C.Cell → Prop)

inductive Whisker : C.Cell → Prop
  | generator (x) : G x → C.source (n+1) x = x → Whisker x
  | left (k : ℕ) (hk : k < n) (a x)
      (ha : C.source n a = a) (h : C.target k a = C.source k x) :
      Whisker x → Whisker (C.join k a x)
  | right (k : ℕ) (hk : k < n) (x a)
      (ha : C.source n a = a) (h : C.target k x = C.source k a) :
      Whisker x → Whisker (C.join k x a)

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.RankedAtoms
open Table OmegaCategory

variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
variable {C : OmegaCategory.{w}} (F : OmegaCategory.Functor C K.nu)

def TopGenerator (n : ℕ) (x : C.Cell) : Prop :=
  ∃ b : A.Index, A.dim b = n+1 ∧ F.map x = A.atom b

end Thomason.DirectedComplex.RankedAtoms

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_LayeredWhiskers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Layered Whiskers. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

variable (C : OmegaCategory.{u})

def LayeredWhisker (G : C.Cell → Prop) : ℕ → C.Cell → Prop
  | 0, x => G x
  | n+1, x => ∃ l m r : C.Cell,
      C.source (n+1) l = l ∧ C.source (n+1) r = r ∧
      LayeredWhisker G n m ∧ C.target n l = C.source n m ∧
      C.target n m = C.source n r ∧ x = C.join n (C.join n l m) r

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex
open OmegaCategory

namespace RankedAtoms
open Table
variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
variable {C : OmegaCategory.{w}} (F : OmegaCategory.Functor C K.nu)

def OrderedWhisker (b : A.Index) : ℕ → C.Cell → Prop
  | 0, x => F.map x = A.atom b
  | n+1, x => ∃ l m r : C.Cell,
      C.source (n+1) l = l ∧ C.source (n+1) r = r ∧
      OrderedWhisker b n m ∧ C.target n l = C.source n m ∧
      C.target n m = C.source n r ∧
      (∀ c, A.coefficient c (n+1) ((F.map l).row (n+1) false) ≠ 0 → A.rank b < A.rank c) ∧
      (∀ c, A.coefficient c (n+1) ((F.map r).row (n+1) false) ≠ 0 → ¬ A.rank b < A.rank c) ∧
      x = C.join n (C.join n l m) r

end RankedAtoms
end Thomason.DirectedComplex

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_RankedExchange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ranked Exchange. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.RankedAtoms
open Table OmegaCategory

variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
variable {C : OmegaCategory.{w}} (F : OmegaCategory.Functor C K.nu)

inductive AtomPath (n : ℕ) : List A.Index → C.Cell → Prop
  | nil (x) (hx : C.source n x = x) : AtomPath n [] x
  | cons (b : A.Index) (hb : A.dim b = n+1) (x y : C.Cell) (bs)
      (hx : C.Whisker n (A.TopGenerator F n) x)
      (ht : (F.map x).row (n+1) false = A.basis (n+1) b)
      (h : C.target n x = C.source n y) :
      AtomPath n bs y → AtomPath n (b::bs) (C.join n x y)

end Thomason.DirectedComplex.RankedAtoms

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.RankedAtoms
open Table OmegaCategory

variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)

def orderRank (b : A.Index) : ℤ :=
  (Fintype.card A.Index : ℤ) * A.rank b + (Fintype.equivFin A.Index b).val

end Thomason.DirectedComplex.RankedAtoms

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.RankedAtoms
open Table OmegaCategory

variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
variable {C : OmegaCategory.{w}} (F : OmegaCategory.Functor C K.nu)

def WhiskerFaithful (n : ℕ) : Prop :=
  ∀ x y : C.Cell, C.Whisker n (A.TopGenerator F n) x →
    C.Whisker n (A.TopGenerator F n) y → F.map x = F.map y → x = y

def HasAdjacentExchange (n : ℕ) : Prop :=
  ∀ (b c : A.Index), A.dim b = n+1 → A.dim c = n+1 →
    A.orderRank b < A.orderRank c →
    ∀ (x y : C.Cell), C.Whisker n (A.TopGenerator F n) x →
      C.Whisker n (A.TopGenerator F n) y →
      (F.map x).row (n+1) false = A.basis (n+1) b →
      (F.map y).row (n+1) false = A.basis (n+1) c →
      C.target n x = C.source n y →
      ∃ x' y' : C.Cell,
        C.Whisker n (A.TopGenerator F n) x' ∧
        C.Whisker n (A.TopGenerator F n) y' ∧
        (F.map x').row (n+1) false = A.basis (n+1) c ∧
        (F.map y').row (n+1) false = A.basis (n+1) b ∧
        C.target n x' = C.source n y' ∧ C.join n x y = C.join n x' y'

end Thomason.DirectedComplex.RankedAtoms

end

end OAI
end


