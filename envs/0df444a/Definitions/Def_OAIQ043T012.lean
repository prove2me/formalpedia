-- Prove2me | Definitions.Def_OAIQ043T012
-- name    : OAIQ043T012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T10:13:14.115989+00:00
-- url     : https://prove2.me/theorems/8625f7d6-b872-43fc-9e86-8dc7f01c7ce0
-- title:
--   Definitions bundle OAIQ043T012 of the split of OpenAI, Thomason Model Structures in Every Strict Higher Dimension (result family 317)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Thomason.main` and `OAI.Thomason.nerveDetection_allDimensions`, carved from OpenAI's openai/math development (OpenAI, *Thomason Model Structures in Every Strict Higher Dimension (result family 317)*, OpenAI Math Release, September 25, 2026, result family 317, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 202 declarations of OpenAI's Lean: 61 definitions, 5 inductive types or structures, 3 instances and 133 theorems. The definitions and types are `OAI.Thomason.GrayRecursive.IntervalHom.AtomicLayers`, `OAI.Thomason.GrayRecursive.IntervalHom.AtomicLayers.subcategory`, `OAI.Thomason.GrayRecursive.IntervalHom.CrossingSquare`, `OAI.Thomason.GrayRecursive.IntervalHom.CrossingSquare.comp`, `OAI.Thomason.GrayRecursive.IntervalHom.CrossingSquare.entry`, `OAI.Thomason.GrayRecursive.IntervalHom.CrossingSquare.exit`, `OAI.Thomason.GrayRecursive.IntervalHom.CrossingSquare.first`, `OAI.Thomason.GrayRecursive.IntervalHom.CrossingSquare.last`, `OAI.Thomason.GrayRecursive.IntervalHom.CrossingSquare.map`, `OAI.Thomason.GrayRecursive.IntervalHom.CrossingSquare.middle`, `OAI.Thomason.GrayRecursive.IntervalHom.CrossingSquare.ofTable`, `OAI.Thomason.GrayRecursive.IntervalHom.CrossingSquare.value`, `OAI.Thomason.GrayRecursive.IntervalHom.CrossingSquare.whiskerLeft`, `OAI.Thomason.GrayRecursive.IntervalHom.CrossingSquare.whiskerRight`, `OAI.Thomason.GrayRecursive.IntervalHom.EdgeNormal`, `OAI.Thomason.GrayRecursive.IntervalHom.SquareNormal`, `OAI.Thomason.GrayRecursive.IntervalHom.TensorGenerator`, `OAI.Thomason.GrayRecursive.IntervalHom.TwoLiftable`, `OAI.Thomason.GrayRecursive.IntervalHom.chainComparison`, `OAI.Thomason.GrayRecursive.IntervalHom.chainDiagram`, `OAI.Thomason.GrayRecursive.IntervalHom.constantCell`, `OAI.Thomason.GrayRecursive.IntervalHom.constantFunctor`, `OAI.Thomason.GrayRecursive.IntervalHom.crossingEdge`, `OAI.Thomason.GrayRecursive.IntervalHom.crossingEdgeLift`, `OAI.Thomason.GrayRecursive.IntervalHom.curry`, `OAI.Thomason.GrayRecursive.IntervalHom.cylinderSubcategory`, `OAI.Thomason.GrayRecursive.IntervalHom.endpointFunctor`, `OAI.Thomason.GrayRecursive.IntervalHom.functor`, `OAI.Thomason.GrayRecursive.IntervalHom.generatorCylinder`, `OAI.Thomason.GrayRecursive.IntervalHom.globeDiagram`, `OAI.Thomason.GrayRecursive.IntervalHom.globeTensorHom`, `OAI.Thomason.GrayRecursive.IntervalHom.globeTensorInv`, `OAI.Thomason.GrayRecursive.IntervalHom.globeTensorIso`, `OAI.Thomason.GrayRecursive.IntervalHom.homEquiv`, `OAI.Thomason.GrayRecursive.IntervalHom.intervalExtensionOfSimplexIsIso`, `OAI.Thomason.GrayRecursive.IntervalHom.mapFunctor`, `OAI.Thomason.GrayRecursive.IntervalHom.omegaCategory`, `OAI.Thomason.GrayRecursive.IntervalHom.tableCell`, `OAI.Thomason.GrayRecursive.IntervalHom.tensorAdjunction`, `OAI.Thomason.GrayRecursive.IntervalHom.tensorEndpoint` and 26 more.
--
--   **Sources.** They come from these modules of lean/OAI/CategoryTheory/Thomason, in whole or in part: `Thomason_BoundedCylinders`, `Thomason_CylinderInterchange`, `Thomason_CylinderProfiles`, `Thomason_CylinderWeights`, `Thomason_EdgeComparison`, `Thomason_FiniteGluing`, `Thomason_IntervalCategories`, `Thomason_PartialPrisms`, `Thomason_PastingInterchange`, `Thomason_PrismBasis`, `Thomason_ProperTransfer`, `Thomason_RankedAtoms`, `Thomason_StandardComparison`, `Thomason_StationaryCylinders`, `Thomason_TopSequences`, `Thomason_TwoCellComparison`, `Thomason_TwoCellExchange`.
--
--   **Imports.** It imports the published bundle `Def_ThomasonModelStructures`; the bundles `OAIQ043T010` and `OAIQ043T011` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.Thomason.GrayRecursive.IntervalHom.chainComparison_poset_twocells_bijective`; the proofs of `OAI.Thomason.GrayRecursive.IntervalHom.chainComparison_poset_twocells_bijective` and `OAI.Thomason.main`.
-- source:
--   OpenAI, Thomason Model Structures in Every Strict Higher Dimension (result family 317), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 317; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Thomason-Model-Structures-in-Every-Strict-Higher-Dimension-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/CategoryTheory/Thomason at commit adc7f12

import Mathlib
import Definitions.Def_ThomasonModelStructures
import Definitions.Def_OAIQ043T010
import Definitions.Def_OAIQ043T011

section
-- module Solutions.OAIQ043_TH.Thomason_PartialPrisms
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.GrayRecursive.CellWeight.instCoeFunForallCell _root_.OAI.Thomason.OneCat.oneUnitCatIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partial Prisms. -/

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory Opposite Simplicial MonoidalCategory DirectedComplex NormalizedChains OmegaCategory

lemma finiteTableCut_const_one {n N : ℕ} (hn : 0<n) (P : Type u) [PartialOrder P]
    (F : OmegaCategory.Functor (Oriental N) (truncation n (complex P).nu).val) :
    finiteTableCut hn F (OrderHom.const _ (1 : Fin 2)) =
      OmegaCategory.Functor.comp
        (complexMap (PartialNormalized.homVertexOrderHom (liftedPartial F) hn)).nu
        (truncationUnit n (complex P).nu) := by
  apply OmegaCategory.Functor.ext
  funext x
  change (PartialNormalized.cutHom (liftedPartial F) hn (OrderHom.const _ (1 : Fin 2))).image x = _
  erw [PartialNormalized.cutHom_const_one,PartialHom.ofHom_image]
  rfl

noncomputable def finiteTableNerveCutHomotopy (n : ℕ) (hn : 0<n) (P : Type u) [PartialOrder P] :
    SSet.Homotopy (𝟙 (streetNerve (truncation n (complex P).nu).val))
      (finiteTableNerveVertexMap n hn P ≫ finitePosetTableNerveMap n P) where
  h := finiteTableNerveCutCylinder n hn P
  h₀ := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro F
    exact finiteTableCut_const_zero hn P F
  h₁ := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro F
    exact finiteTableCut_const_one hn P F
  rel := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨x,hx⟩,θ⟩
    exact False.elim hx

lemma finiteTableNerveVertexMap_weakEquivalence (n : ℕ) (hn : 0<n) (P : Type u) [PartialOrder P] :
    simplicialWeakEquivalences (finiteTableNerveVertexMap n hn P) :=
  simplicialWeakEquivalence_of_simplicial_retract _ (finitePosetTableNerveMap n P)
    (finitePosetTableNerveMap_vertex n hn P) (finiteTableNerveCutHomotopy n hn P)

lemma finitePosetTableNerveMap_weakEquivalence (n : ℕ) (hn : 0<n) (P : Type u) [PartialOrder P] :
    simplicialWeakEquivalences (finitePosetTableNerveMap n P) := by
  apply simplicialWeakEquivalences.of_postcomp _ (finiteTableNerveVertexMap n hn P)
    (finiteTableNerveVertexMap_weakEquivalence n hn P)
  rw [finitePosetTableNerveMap_vertex]
  exact simplicialWeakEquivalences.id_mem _

theorem posetCategorificationFiniteUnit_weakEquivalence (n : ℕ) (hn : 1 ≤ n)
    (P : Type u) [PartialOrder P] :
    simplicialWeakEquivalences
      ((categorificationFiniteAdjunction n).unit.app (CategoryTheory.nerve P)) := by
  have : IsIso (streetNerveMap ((truncationFunctor n).map (posetCategorificationTableMap P))) := by
    change IsIso ((streetNerveFinite n).map ((truncationFunctor n).map (posetCategorificationTableMap P)))
    infer_instance
  apply simplicialWeakEquivalences.of_postcomp _
    (streetNerveMap ((truncationFunctor n).map (posetCategorificationTableMap P)))
    (simplicialWeakEquivalences.of_isIso _)
  erw [posetCategorificationFiniteUnit_tableMap]
  exact finitePosetTableNerveMap_weakEquivalence n hn P

end Thomason

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_ProperTransfer
attribute [-instance] _root_.OAI.Thomason.GrayRecursive.CellWeight.instCoeFunForallCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Proper Transfer. -/

noncomputable section
universe u v w z


namespace Thomason.AbstractTransfer.Boundaries
open CategoryTheory Limits Simplicial PartialOrder KanLocal
open AttachmentComparison (upward)
open HornAttachments
open AbstractTransfer
open BoundaryProperness (PosetAttachment sumData)
attribute [-instance] CategoryTheory.Sigma.sigma

end Thomason.AbstractTransfer.Boundaries

end

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory Limits AbstractTransfer
attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

theorem finitePosetComparison (T : RightIntervalExtension.{u}) (n : ℕ) (hn : 1 ≤ n) :
    PosetComparison (categorificationFinite.{u} n) (streetNerveFinite n)
      (categorificationFiniteAdjunction n) := by
  let := T.rightAdjoint
  exact {
    unit_weak := posetCategorificationFiniteUnit_weakEquivalence n hn
    attachment_mono := AttachmentComparison.finite_nerve_attachment_mono n hn
    comparison := AttachmentComparison.gray_comparison_local T
      T.tensor.rightAdjoint (Adjunction.ofIsLeftAdjoint T.tensor) n hn }

def finiteEndpointOfGray (T : RightIntervalExtension.{u}) (n : ℕ) (hn : 1 ≤ n) :
    ExactModelEndpoint (thomasonLeftFinite.{u} n) (thomasonRightFinite n)
      (thomasonFiniteAdjunction n) := by
  letI : MorphismProperty.IsCardinalForSmallObjectArgument
      (hornImages (L (categorificationFinite.{u} n))) Cardinal.aleph0.{u} := thomasonHornFinite_smallCardinal n
  letI : MorphismProperty.IsCardinalForSmallObjectArgument
      (boundaryImages (L (categorificationFinite.{u} n))) Cardinal.aleph0.{u} := thomasonBoundaryFinite_smallCardinal n
  exact AbstractTransfer.exactEndpoint (finitePosetComparison T n hn)

end Thomason

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_StationaryCylinders
attribute [-instance] _root_.OAI.Thomason.GrayRecursive.CellWeight.instCoeFunForallCell
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

lemma concatInterval_right_unit {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) :
    concatInterval F (constantInterval (endGlobe F true)) (stationary_right_matching F) = F :=
  (concatInterval_units n F).2
end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma functor_ext_zero_cylinder {Y : OmegaCategory.{v}}
    {F G : OmegaCategory.Functor (K.{u} 0).nu Y}
    (h : F.map (verticalTable (topTable 0)) = G.map (verticalTable (topTable 0))) : F = G := by
  have he : OmegaCategory.Functor.comp zeroCylinderMap F = OmegaCategory.Functor.comp zeroCylinderMap G := by
    apply GlobeComplex.functor_ext
    change F.map (zeroCylinderMap.map (topTable 1)) = G.map (zeroCylinderMap.map (topTable 1))
    simpa only [zeroCylinderMap_top] using h
  apply OmegaCategory.Functor.ext
  funext x
  obtain ⟨z,rfl⟩ := zeroCylinderMap_bijective.surjective x
  exact congrArg (fun P => P.map z) he

lemma pasteCylinder_lower_face (n k i : ℕ) (hk : k < n) (hi : i ≤ k)
    {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : FaceMatching k F G) (b : Bool) :
    restrictCylinder i b (pasteCylinder hk F G h) = restrictCylinder i b (if b then G else F) := by
  induction k generalizing n i Y with
  | zero =>
    have hi0 : i = 0 := by omega
    subst i
    cases n with
    | zero => omega
    | succ n =>
      apply functor_ext_zero_cylinder
      rw [restrictCylinder_zero_vertical, pasteCylinder_zero_edge]
      cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true, restrictCylinder_zero_vertical]
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      have hk' : k < n := by omega
      cases i with
      | zero =>
        apply functor_ext_zero_cylinder
        rw [restrictCylinder_zero_vertical, pasteCylinder_succ_edge hk']
        cases b
        · exact (restrictCylinder_zero_vertical F false).symm
        · rw [restrictCylinder_zero_vertical]
          exact h.edges true
      | succ i =>
        apply functor_ext_rectangle
        · intro a x
          have he : OmegaCategory.Functor.comp ((complex (i+1)).cylinderEndpoint a).nu
              (restrictCylinder (i+1) b (pasteCylinder hk F G h)) =
              OmegaCategory.Functor.comp ((complex (i+1)).cylinderEndpoint a).nu
                (restrictCylinder (i+1) b (if b then G else F)) := by
            apply GlobeComplex.functor_ext
            change (restrictCylinder (i+1) b (pasteCylinder hk F G h)).map (atEnd a (topTable (i+1))) =
              (restrictCylinder (i+1) b (if b then G else F)).map (atEnd a (topTable (i+1)))
            rw [restrictCylinder_endpoint_top, pasteCylinder_endpoint_top, restrictCylinder_endpoint_top]
            cases b
            · exact Y.join_source_le (i+1) (k+1) _ _ hi (h.ends a)
            · exact Y.join_target_le (i+1) (k+1) _ _ hi (h.ends a)
          exact congrArg (fun P => P.map x) he
        · intro a
          rw [restrictCylinder_edge, pasteCylinder_succ_edge hk']
          cases b
          · exact (restrictCylinder_edge F false a).symm
          · rw [restrictCylinder_edge]
            exact h.edges a
        · intro x
          erw [restrictCylinder_up, pasteCylinder_succ_up hk']
          have he := ih n i hk' (by omega) (rectangleDiagramOfFunctor F).diagonal
            (CylinderComposition.secondDiagonal F G h) (CylinderComposition.diagonal_matching F G h)
          have hev := congrArg (fun P => (P.map x).val) he
          refine hev.trans ?_
          cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true, restrictCylinder_up]
          all_goals rfl

end Thomason.GrayRecursive

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_CylinderInterchange
attribute [-instance] _root_.OAI.Thomason.GrayRecursive.CellWeight.instCoeFunForallCell
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

lemma faceIdentityCylinder_right_matching {n k : ℕ} (hk : k < n)
    {Y : OmegaCategory.{v}} (F : OmegaCategory.Functor (K.{u} n).nu Y) :
    FaceMatching k F (faceIdentityCylinder k true F) := by
  have he : restrictCylinder k false (faceIdentityCylinder k true F) = restrictCylinder k true F := by
    unfold faceIdentityCylinder
    rw [restrictCylinder_restrict hk, restrictCylinder_self]
  intro x
  exact (congrArg (fun P => P.map x) he).symm

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma pasteCylinder_right_unit (n k : ℕ) (hk : k < n) {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) :
    pasteCylinder hk F (faceIdentityCylinder k true F) (faceIdentityCylinder_right_matching hk F) = F := by
  induction k generalizing n Y with
  | zero =>
    cases n with
    | zero => omega
    | succ n =>
      let D := rectangleDiagramOfFunctor F
      apply functor_ext_rectangle
      · intro a x
        have he : endGlobe (pasteCylinder hk F (faceIdentityCylinder 0 true F)
            (faceIdentityCylinder_right_matching hk F)) a = endGlobe F a := by
          apply GlobeComplex.functor_ext
          change (pasteCylinder hk F (faceIdentityCylinder 0 true F)
            (faceIdentityCylinder_right_matching hk F)).map (atEnd a (topTable (n+1))) =
              F.map (atEnd a (topTable (n+1)))
          rw [pasteCylinder_endpoint_top, faceIdentityCylinder_endpoint_top (by omega)]
          exact Y.join_right_unit 0 _ _ (Y.source_target_self 0 _) (Y.source_target_self 0 _).symm
        exact congrArg (fun P => P.map x) he
      · intro a
        rw [pasteCylinder_zero_edge]
        cases a <;> simp only [Bool.false_eq_true, ite_false, ite_true, faceIdentityCylinder_zero_edge]
      · intro x
        rw [pasteCylinder_zero_up]
        refine (concatInterval_val_congr _ _ _ D.diagonal
          (constantInterval (endGlobe D.diagonal true)) (stationary_right_matching D.diagonal) ?_ ?_ x).trans (congrArg (fun P => (P.map x).val) (concatInterval_right_unit D.diagonal))
        · intro z
          change Y.join 0 (F.map (up z))
            ((faceIdentityCylinder 0 true F).map (atEnd true (suspendTable (project z)))) =
              (D.diagonal.map z).val
          rw [faceIdentityCylinder_zero_endpoint]
          apply Y.join_right_unit 0 _ _ (D.vertex_fixed true true)
          exact (D.diagonal.map z).property.2.trans (D.vertex_fixed true true).symm
        · intro z
          change Y.join 0 (F.map (atEnd false (suspendTable (project z))))
            ((faceIdentityCylinder 0 true F).map (up z)) =
              (D.diagonal.map (atEnd true (project z))).val
          erw [faceIdentityCylinder_zero_up, D.right]
          rfl
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      have hk' : k < n := by omega
      let D := rectangleDiagramOfFunctor F
      apply functor_ext_rectangle
      · intro a x
        have he : endGlobe (pasteCylinder hk F (faceIdentityCylinder (k+1) true F)
            (faceIdentityCylinder_right_matching hk F)) a = endGlobe F a := by
          apply GlobeComplex.functor_ext
          change (pasteCylinder hk F (faceIdentityCylinder (k+1) true F)
            (faceIdentityCylinder_right_matching hk F)).map (atEnd a (topTable (n+1))) =
              F.map (atEnd a (topTable (n+1)))
          rw [pasteCylinder_endpoint_top, faceIdentityCylinder_endpoint_top (by omega)]
          exact Y.join_right_unit (k+1) _ _ (Y.source_target_self (k+1) _) (Y.source_target_self (k+1) _).symm
        exact congrArg (fun P => P.map x) he
      · intro a
        rw [pasteCylinder_succ_edge hk']
      · intro x
        rw [pasteCylinder_succ_up hk']
        refine (pasteCylinder_val_congr hk' _ _ _ D.diagonal (faceIdentityCylinder k true D.diagonal)
          (faceIdentityCylinder_right_matching hk' D.diagonal) ?_ ?_ x).trans (congrArg (fun P => (P.map x).val) (ih n hk' D.diagonal))
        · intro z
          rfl
        · intro z
          exact faceIdentityCylinder_succ_up F true z
end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma concatInterval_shuffle_left {n : ℕ} {Y : OmegaCategory.{u}} {a b c : Y.Cell}
    (F : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory a b))
    (G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory b c)) :
    concatInterval (homCompose (constantInterval (endGlobe F false)) G)
      (homCompose F (constantInterval (endGlobe G true)))
      ((stationary_left_matching F).homCompose (stationary_right_matching G)) = homCompose F G := by
  rw [concatInterval_homCompose _ _ (stationary_left_matching F) _ _ (stationary_right_matching G),
    concatInterval_left_unit, concatInterval_right_unit]

lemma concatInterval_shuffle_right {n : ℕ} {Y : OmegaCategory.{u}} {a b c : Y.Cell}
    (F : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory a b))
    (G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory b c)) :
    concatInterval (homCompose F (constantInterval (endGlobe G false)))
      (homCompose (constantInterval (endGlobe F true)) G)
      ((stationary_right_matching F).homCompose (stationary_left_matching G)) = homCompose F G := by
  rw [concatInterval_homCompose _ _ (stationary_right_matching F) _ _ (stationary_left_matching G),
    concatInterval_right_unit, concatInterval_left_unit]

lemma concatInterval_four {n : ℕ} {Y : OmegaCategory.{u}}
    (A B C D : OmegaCategory.Functor (K.{u} n).nu Y)
    (h : IntervalMatching A B) (i : IntervalMatching B C) (j : IntervalMatching C D) :
    concatInterval (concatInterval A B h) (concatInterval C D j) (h.concat_left (i.concat_right j)) =
      concatInterval A (concatInterval (concatInterval B C i) D (i.concat_left j))
        ((h.concat_right i).concat_right (i.concat_left j)) := by
  rw [concatInterval_associative]
  congr 1
  exact (concatInterval_associative n B C D i j).symm

end Thomason.GrayRecursive

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_PastingInterchange
attribute [-instance] _root_.OAI.Thomason.GrayRecursive.CellWeight.instCoeFunForallCell
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

lemma Z_eq :
    Z D E T e i = homCompose (constantInterval (before D E e)) (E.concatDiagonalTwo T i) := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change Y.join 0 (Y.join 0 ((D.ends false).map (suspendTable (project x))) (E.diagonal.map x).val) (T.edge true) =
    Y.join 0 ((D.ends false).map (suspendTable (project x))) (Y.join 0 (E.diagonal.map x).val (T.edge true))
  apply Y.join_assoc 0
  · erw [← (D.ends false).map_target]
    change (D.ends false).map (truncate 0 true (suspendTable (project x))) = _
    rw [suspend_truncate_zero, D.horizontal_seam E e]
    exact (E.diagonal.map x).property.1.symm
  · erw [T.edge_source, ← i]
    exact (E.diagonal.map x).property.2

lemma CZ' : IntervalMatching (C' D S T j h) (Z D E T e i) := by
  rw [C'_eq D E S T e j h i, Z_eq]
  exact (constantInterval_matching (before D E e)).homCompose (E.concatDiagonal_matching T i)

lemma left_one_map
    (hh : ∀ x, ((D.horizontal E e).ends true).map x = ((S.horizontal T j).ends false).map x)
    (x : Table (K.{u} n)) :
    (((D.horizontal E e).concatDiagonalOne (S.horizontal T j) hh).map x).val =
      ((concatInterval (A D S T j h) (B D S T j h) (AB D S T j h)).map x).val := by
  have hm : IntervalMatching
      (homCompose (left D S h) (S.horizontalDiagonalOne T j))
      (homCompose (left D S h) (S.horizontalDiagonalTwo T j)) := by
    simpa only [A, B_eq] using AB D S T j h
  have he := concatInterval_homCompose_left (D.edge false) (D.edge_fixed false)
    (D.edge_source false) ((D.edge_target false).trans (h _))
    (S.horizontalDiagonalOne T j) (S.horizontalDiagonalTwo T j) (S.horizontalDiagonal_matching T j) hm
  simp only [show constantHom (K n).nu (D.edge false) (D.edge_fixed false) (D.edge_source false)
    ((D.edge_target false).trans (h _)) = left D S h from rfl, ← B_eq] at he
  exact (congrArg (fun Q => (Q.map x).val) he).symm

lemma left_two_map
    (hh : ∀ x, ((D.horizontal E e).ends true).map x = ((S.horizontal T j).ends false).map x)
    (x : Table (K.{u} n)) :
    (((D.horizontal E e).concatDiagonalTwo (S.horizontal T j) hh).map x).val =
      ((concatInterval (C D S T j h) (Z D E T e i) (CZ D E S T e j h i)).map x).val := by
  have hm : IntervalMatching
      (homCompose (D.horizontalDiagonalOne E e) (right E T i))
      (homCompose (D.horizontalDiagonalTwo E e) (right E T i)) := by
    simpa only [Z, C_eq D E S T e j h i] using CZ D E S T e j h i
  have he := concatInterval_homCompose_right
    (D.horizontalDiagonalOne E e) (D.horizontalDiagonalTwo E e) (D.horizontalDiagonal_matching E e)
    (T.edge true) (T.edge_fixed true) ((T.edge_source true).trans (i _).symm) (T.edge_target true) hm
  simp only [show constantHom (K n).nu (T.edge true) (T.edge_fixed true)
    ((T.edge_source true).trans (i _).symm) (T.edge_target true) = right E T i from rfl,
    ← C_eq D E S T e j h i] at he
  exact (congrArg (fun Q => (Q.map x).val) he).symm

lemma right_one_map
    (ee : (D.concat S h (intervalComposition n)).edge true = (E.concat T i (intervalComposition n)).edge false)
    (x : Table (K.{u} n)) :
    (((D.concat S h (intervalComposition n)).horizontalDiagonalOne (E.concat T i (intervalComposition n)) ee).map x).val =
      ((concatInterval (A D S T j h) (B' D S T j h) (AB' D S T j h)).map x).val := by
  have hm : IntervalMatching
      (homCompose (D.concatDiagonalOne S h) (constantInterval (suffix S T j)))
      (homCompose (D.concatDiagonalTwo S h) (constantInterval (suffix S T j))) := by
    simpa only [A_eq, B'_eq] using AB' D S T j h
  have he := concatInterval_homCompose_stationary_right
    (D.concatDiagonalOne S h) (D.concatDiagonalTwo S h) (D.concatDiagonal_matching S h) (suffix S T j) hm
  simp only [← A_eq, ← B'_eq] at he
  exact (congrArg (fun Q => (Q.map x).val) he).symm

lemma right_two_map
    (ee : (D.concat S h (intervalComposition n)).edge true = (E.concat T i (intervalComposition n)).edge false)
    (x : Table (K.{u} n)) :
    (((D.concat S h (intervalComposition n)).horizontalDiagonalTwo (E.concat T i (intervalComposition n)) ee).map x).val =
      ((concatInterval (C' D S T j h) (Z D E T e i) (CZ' D E S T e j h i)).map x).val := by
  have hm : IntervalMatching
      (homCompose (constantInterval (before D E e)) (E.concatDiagonalOne T i))
      (homCompose (constantInterval (before D E e)) (E.concatDiagonalTwo T i)) := by
    simpa only [C'_eq D E S T e j h i, Z_eq] using CZ' D E S T e j h i
  have he := concatInterval_homCompose_stationary_left (before D E e)
    (E.concatDiagonalOne T i) (E.concatDiagonalTwo T i) (E.concatDiagonal_matching T i) hm
  simp only [← C'_eq D E S T e j h i, ← Z_eq] at he
  exact (congrArg (fun Q => (Q.map x).val) he).symm

end MixedZero

lemma concat_horizontal {n : ℕ} {Y : OmegaCategory.{u}}
    (D E S T : RectangleDiagram.{u,u} n Y)
    (e : D.edge true = E.edge false) (j : S.edge true = T.edge false)
    (h : ∀ x, (D.ends true).map x = (S.ends false).map x)
    (i : ∀ x, (E.ends true).map x = (T.ends false).map x)
    (hh : ∀ x, ((D.horizontal E e).ends true).map x = ((S.horizontal T j).ends false).map x)
    (ee : (D.concat S h (intervalComposition n)).edge true = (E.concat T i (intervalComposition n)).edge false) :
    (D.horizontal E e).concat (S.horizontal T j) hh (intervalComposition n) =
      (D.concat S h (intervalComposition n)).horizontal (E.concat T i (intervalComposition n)) ee := by
  apply RectangleDiagram.ext
  · funext a
    cases a <;> rfl
  · funext a
    cases a <;> rfl
  · intro x
    open MixedZero in
    have hl := concatInterval_val_congr
      ((D.horizontal E e).concatDiagonalOne (S.horizontal T j) hh)
      ((D.horizontal E e).concatDiagonalTwo (S.horizontal T j) hh)
      ((D.horizontal E e).concatDiagonal_matching (S.horizontal T j) hh)
      (concatInterval (A D S T j h) (B D S T j h) (AB D S T j h))
      (concatInterval (C D S T j h) (Z D E T e i) (CZ D E S T e j h i))
      ((AB D S T j h).concat_left ((BC D S T j h).concat_right (CZ D E S T e j h i)))
      (left_one_map D E S T e j h hh) (left_two_map D E S T e j h i hh) x
    open MixedZero in
    have hr := concatInterval_val_congr
      ((D.concat S h (intervalComposition n)).horizontalDiagonalOne (E.concat T i (intervalComposition n)) ee)
      ((D.concat S h (intervalComposition n)).horizontalDiagonalTwo (E.concat T i (intervalComposition n)) ee)
      ((D.concat S h (intervalComposition n)).horizontalDiagonal_matching (E.concat T i (intervalComposition n)) ee)
      (concatInterval (A D S T j h) (B' D S T j h) (AB' D S T j h))
      (concatInterval (C' D S T j h) (Z D E T e i) (CZ' D E S T e j h i))
      ((AB' D S T j h).concat_left ((BC' D S T j h).concat_right (CZ' D E S T e j h i)))
      (right_one_map D E S T j h i ee) (right_two_map D E S T e j h i ee) x
    open MixedZero in
    have hfl := concatInterval_four (A D S T j h) (B D S T j h) (C D S T j h) (Z D E T e i)
      (AB D S T j h) (BC D S T j h) (CZ D E S T e j h i)
    open MixedZero in
    have hfr := concatInterval_four (A D S T j h) (B' D S T j h) (C' D S T j h) (Z D E T e i)
      (AB' D S T j h) (BC' D S T j h) (CZ' D E S T e j h i)
    open MixedZero in
    have hele : concatInterval (B D S T j h) (C D S T j h) (BC D S T j h) =
        homCompose D.diagonal (midRight D S T j h) := concatInterval_shuffle_left _ _
    open MixedZero in
    have here : concatInterval (B' D S T j h) (C' D S T j h) (BC' D S T j h) =
        homCompose D.diagonal (midRight D S T j h) := concatInterval_shuffle_right _ _
    simp only [hele] at hfl
    simp only [here] at hfr
    exact hl.trans ((congrArg (fun Q => (Q.map x).val) (hfl.trans hfr.symm)).trans hr.symm)

end RectangleDiagram

lemma concatInterval_horizontal {n : ℕ} {Y : OmegaCategory.{u}}
    (F G F' G' : OmegaCategory.Functor (K.{u} (n+1)).nu Y)
    (e : F.map (verticalTable (vertex n true)) = G.map (verticalTable (vertex n false)))
    (j : F'.map (verticalTable (vertex n true)) = G'.map (verticalTable (vertex n false)))
    (h : IntervalMatching F F') (i : IntervalMatching G G')
    (hh : IntervalMatching (horizontalCylinder F G e) (horizontalCylinder F' G' j))
    (ee : (concatInterval F F' h).map (verticalTable (vertex n true)) =
      (concatInterval G G' i).map (verticalTable (vertex n false))) :
    concatInterval (horizontalCylinder F G e) (horizontalCylinder F' G' j) hh =
      horizontalCylinder (concatInterval F F' h) (concatInterval G G' i) ee := by
  unfold horizontalCylinder
  change (((rectangleDiagramOfFunctor (((rectangleDiagramOfFunctor F).horizontal
    (rectangleDiagramOfFunctor G) e).lift)).concat
    (rectangleDiagramOfFunctor (((rectangleDiagramOfFunctor F').horizontal
      (rectangleDiagramOfFunctor G') j).lift)) _ (intervalComposition n)).lift) =
      ((rectangleDiagramOfFunctor (((rectangleDiagramOfFunctor F).concat
        (rectangleDiagramOfFunctor F') h (intervalComposition n)).lift)).horizontal
        (rectangleDiagramOfFunctor (((rectangleDiagramOfFunctor G).concat
          (rectangleDiagramOfFunctor G') i (intervalComposition n)).lift)) _).lift
  simp only [RectangleDiagram.ofFunctor_lift]
  exact congrArg RectangleDiagram.lift
    ((rectangleDiagramOfFunctor F).concat_horizontal (rectangleDiagramOfFunctor G)
      (rectangleDiagramOfFunctor F') (rectangleDiagramOfFunctor G') e j h i _ _)

lemma concatInterval_paste_zero {n : ℕ} {Y : OmegaCategory.{u}}
    (F G F' G' : OmegaCategory.Functor (K.{u} (n+1)).nu Y)
    (e : FaceMatching 0 F G) (j : FaceMatching 0 F' G')
    (h : IntervalMatching F F') (i : IntervalMatching G G') :
    concatInterval (pasteCylinder (show 0<n+1 by omega) F G e)
      (pasteCylinder (show 0<n+1 by omega) F' G' j) (h.paste (by omega) i e j) =
      pasteCylinder (show 0<n+1 by omega) (concatInterval F F' h) (concatInterval G G' i)
        (e.concat (by omega) j h i) := by
  simp only [pasteCylinder_zero]
  exact concatInterval_horizontal F G F' G' (zeroFaceMatching_seam e) (zeroFaceMatching_seam j) h i _ _
end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma concatInterval_paste (n k : ℕ) (hk : k < n) {Y : OmegaCategory.{u}}
    (F G F' G' : OmegaCategory.Functor (K.{u} n).nu Y)
    (e : FaceMatching k F G) (j : FaceMatching k F' G')
    (h : IntervalMatching F F') (i : IntervalMatching G G') :
    concatInterval (pasteCylinder hk F G e) (pasteCylinder hk F' G' j) (h.paste hk i e j) =
      pasteCylinder hk (concatInterval F F' h) (concatInterval G G' i) (e.concat (Nat.le_of_lt hk) j h i) := by
  induction k generalizing n Y with
  | zero =>
    cases n with
    | zero => omega
    | succ n => exact concatInterval_paste_zero F G F' G' e j h i
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      have hk' : k < n := by omega
      apply functor_ext_rectangle
      · intro a x
        have he : endGlobe (concatInterval (pasteCylinder hk F G e) (pasteCylinder hk F' G' j)
            (h.paste hk i e j)) a = endGlobe (pasteCylinder hk (concatInterval F F' h)
            (concatInterval G G' i) (e.concat (Nat.le_of_lt hk) j h i)) a := by
          apply GlobeComplex.functor_ext
          change (concatInterval (pasteCylinder hk F G e) (pasteCylinder hk F' G' j)
            (h.paste hk i e j)).map (atEnd a (topTable (n+1))) =
              (pasteCylinder hk (concatInterval F F' h) (concatInterval G G' i)
                (e.concat (Nat.le_of_lt hk) j h i)).map (atEnd a (topTable (n+1)))
          cases a <;> simp only [concatInterval_endpoint, Bool.false_eq_true, ite_false, ite_true, pasteCylinder_endpoint_top]
        exact congrArg (fun Q => Q.map x) he
      · intro a
        rw [concatInterval_succ_edge, pasteCylinder_succ_edge hk', pasteCylinder_succ_edge hk',
          pasteCylinder_succ_edge hk', concatInterval_succ_edge]
      · intro x
        rw [concatInterval_succ_up, pasteCylinder_succ_up hk']
        open MixedPositive in
        have hl := concatInterval_val_congr
          ((rectangleDiagramOfFunctor (pasteCylinder hk F G e)).concatDiagonalOne
            (rectangleDiagramOfFunctor (pasteCylinder hk F' G' j)) (h.paste hk i e j))
          ((rectangleDiagramOfFunctor (pasteCylinder hk F G e)).concatDiagonalTwo
            (rectangleDiagramOfFunctor (pasteCylinder hk F' G' j)) (h.paste hk i e j))
          ((rectangleDiagramOfFunctor (pasteCylinder hk F G e)).concatDiagonal_matching
            (rectangleDiagramOfFunctor (pasteCylinder hk F' G' j)) (h.paste hk i e j))
          (pasteCylinder hk' (A F F' h) (C F F' G' j h) (AC F F' G' j h))
          (pasteCylinder hk' (B F F' h) (Z F G F' e h) (BZ F G F' e h))
          ((AB F F' h).paste hk' (CZ F G F' G' e j h i) (AC F F' G' j h) (BZ F G F' e h))
          (left_one_map F G F' G' e j h hk' (h.paste hk i e j))
          (left_two_map F G F' G' e j h hk' (h.paste hk i e j)) x
        open MixedPositive in
        have hi := ih n hk' (A F F' h) (C F F' G' j h) (B F F' h) (Z F G F' e h)
          (AC F F' G' j h) (BZ F G F' e h) (AB F F' h) (CZ F G F' G' e j h i)
        refine hl.trans ((congrArg (fun Q => (Q.map x).val) hi).trans ?_)
        apply pasteCylinder_val_congr hk'
        · intro z
          exact (concatInterval_succ_up F F' h z).symm
        · intro z
          change ((concatInterval (MixedPositive.C F F' G' j h) (MixedPositive.Z F G F' e h)
            (MixedPositive.CZ F G F' G' e j h i)).map z).val = (concatInterval G G' i).map (up z)
          erw [concatInterval_succ_up]
          open MixedPositive in
          exact concatInterval_val_congr _ _ _ _ _ _
            (C_map F G F' G' e j h i) (Z_map F G F' G' e j h i) z
end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma pasteCylinder_interchange_zero {n k : ℕ} (hk : k < n) {Y : OmegaCategory.{u}}
    (F G F' G' : OmegaCategory.Functor (K.{u} (n+1)).nu Y)
    (e : FaceMatching 0 F G) (j : FaceMatching 0 F' G')
    (h : FaceMatching (k+1) F F') (i : FaceMatching (k+1) G G')
    (ee : FaceMatching 0 (pasteCylinder (Nat.add_lt_add_right hk 1) F F' h)
      (pasteCylinder (Nat.add_lt_add_right hk 1) G G' i))
    (hh : FaceMatching (k+1) (pasteCylinder (show 0<n+1 by omega) F G e)
      (pasteCylinder (show 0<n+1 by omega) F' G' j)) :
    pasteCylinder (show 0<n+1 by omega) (pasteCylinder (Nat.add_lt_add_right hk 1) F F' h)
      (pasteCylinder (Nat.add_lt_add_right hk 1) G G' i) ee =
    pasteCylinder (Nat.add_lt_add_right hk 1) (pasteCylinder (show 0<n+1 by omega) F G e)
      (pasteCylinder (show 0<n+1 by omega) F' G' j) hh := by
  apply functor_ext_rectangle
  · intro a x
    have he : endGlobe (pasteCylinder (show 0<n+1 by omega)
        (pasteCylinder (Nat.add_lt_add_right hk 1) F F' h)
        (pasteCylinder (Nat.add_lt_add_right hk 1) G G' i) ee) a =
      endGlobe (pasteCylinder (Nat.add_lt_add_right hk 1)
        (pasteCylinder (show 0<n+1 by omega) F G e)
        (pasteCylinder (show 0<n+1 by omega) F' G' j) hh) a := by
      apply GlobeComplex.functor_ext
      change (pasteCylinder (by omega) _ _ ee).map (atEnd a (topTable (n+1))) =
        (pasteCylinder (by omega) _ _ hh).map (atEnd a (topTable (n+1)))
      simp only [pasteCylinder_endpoint_top]
      exact Y.join_interchange 0 (k+1) (by omega) _ _ _ _
        (h.ends a) (i.ends a) (e.ends a) (j.ends a)
    exact congrArg (fun Q => Q.map x) he
  · intro a
    rw [pasteCylinder_zero_edge, pasteCylinder_succ_edge hk]
    cases a <;> simp only [Bool.false_eq_true, ite_false, ite_true, pasteCylinder_succ_edge hk,
      pasteCylinder_zero_edge]
  · intro x
    rw [pasteCylinder_zero_up, pasteCylinder_succ_up hk]
    open ZeroInterchange in
    have hl := concatInterval_val_congr
      ((rectangleDiagramOfFunctor (pasteCylinder (Nat.add_lt_add_right hk 1) F F' h)).horizontalDiagonalOne
        (rectangleDiagramOfFunctor (pasteCylinder (Nat.add_lt_add_right hk 1) G G' i)) (zeroFaceMatching_seam ee))
      ((rectangleDiagramOfFunctor (pasteCylinder (Nat.add_lt_add_right hk 1) F F' h)).horizontalDiagonalTwo
        (rectangleDiagramOfFunctor (pasteCylinder (Nat.add_lt_add_right hk 1) G G' i)) (zeroFaceMatching_seam ee))
      ((rectangleDiagramOfFunctor (pasteCylinder (Nat.add_lt_add_right hk 1) F F' h)).horizontalDiagonal_matching
        (rectangleDiagramOfFunctor (pasteCylinder (Nat.add_lt_add_right hk 1) G G' i)) (zeroFaceMatching_seam ee))
      (pasteCylinder hk (A F G e) (C F G F' G' e h i) (AC F G F' G' e h i))
      (pasteCylinder hk (B F G e) (Z F G F' G' e h i) (BZ F G F' G' e h i))
      ((AB F G e).paste hk (CZ F G F' G' e j h i) (AC F G F' G' e h i) (BZ F G F' G' e h i))
      (fun z => (paste_one_map F G F' G' e h i hk ee z).symm)
      (fun z => (paste_two_map F G F' G' e h i hk ee z).symm) x
    open ZeroInterchange in
    have hi := concatInterval_paste n k hk (A F G e) (C F G F' G' e h i)
      (B F G e) (Z F G F' G' e h i) (AC F G F' G' e h i) (BZ F G F' G' e h i)
      (AB F G e) (CZ F G F' G' e j h i)
    refine hl.trans ((congrArg (fun Q => (Q.map x).val) hi).trans ?_)
    apply pasteCylinder_val_congr hk
    · intro z
      exact (pasteCylinder_zero_up F G e z).symm
    · intro z
      change ((concatInterval (ZeroInterchange.C F G F' G' e h i)
        (ZeroInterchange.Z F G F' G' e h i) (ZeroInterchange.CZ F G F' G' e j h i)).map z).val =
          (pasteCylinder (show 0<n+1 by omega) F' G' j).map (up z)
      erw [pasteCylinder_zero_up]
      apply concatInterval_val_congr <;> intro w <;> rfl
end Thomason.GrayRecursive

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_IntervalCategories
attribute [-instance] _root_.OAI.Thomason.GrayRecursive.CellWeight.instCoeFunForallCell
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

lemma pasteCylinder_interchange (n k l : ℕ) (hkl : k < l) (hl : l < n)
    {Y : OmegaCategory.{u}}
    (F G F' G' : OmegaCategory.Functor (K.{u} n).nu Y)
    (e : FaceMatching k F G) (j : FaceMatching k F' G')
    (h : FaceMatching l F F') (i : FaceMatching l G G')
    (ee : FaceMatching k (pasteCylinder hl F F' h) (pasteCylinder hl G G' i))
    (hh : FaceMatching l (pasteCylinder (Nat.lt_trans hkl hl) F G e)
      (pasteCylinder (Nat.lt_trans hkl hl) F' G' j)) :
    pasteCylinder (Nat.lt_trans hkl hl) (pasteCylinder hl F F' h) (pasteCylinder hl G G' i) ee =
      pasteCylinder hl (pasteCylinder (Nat.lt_trans hkl hl) F G e)
        (pasteCylinder (Nat.lt_trans hkl hl) F' G' j) hh := by
  induction k generalizing n l Y with
  | zero =>
    cases n with
    | zero => omega
    | succ n =>
      cases l with
      | zero => omega
      | succ l => exact pasteCylinder_interchange_zero (by omega) F G F' G' e j h i ee hh
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      cases l with
      | zero => omega
      | succ l =>
        have hkl' : k < l := by omega
        have hl' : l < n := by omega
        have hk' : k < n := by omega
        apply functor_ext_rectangle
        · intro a x
          have he : endGlobe (pasteCylinder (Nat.lt_trans hkl hl)
              (pasteCylinder hl F F' h) (pasteCylinder hl G G' i) ee) a =
            endGlobe (pasteCylinder hl (pasteCylinder (Nat.lt_trans hkl hl) F G e)
              (pasteCylinder (Nat.lt_trans hkl hl) F' G' j) hh) a := by
            apply GlobeComplex.functor_ext
            change (pasteCylinder (by omega) _ _ ee).map (atEnd a (topTable (n+1))) =
              (pasteCylinder (by omega) _ _ hh).map (atEnd a (topTable (n+1)))
            simp only [pasteCylinder_endpoint_top]
            exact Y.join_interchange (k+1) (l+1) hkl _ _ _ _
              (h.ends a) (i.ends a) (e.ends a) (j.ends a)
          exact congrArg (fun Q => Q.map x) he
        · intro a
          simp only [pasteCylinder_succ_edge hk', pasteCylinder_succ_edge hl']
        · intro x
          rw [pasteCylinder_succ_up hk', pasteCylinder_succ_up hl']
          open PositiveInterchange in
          have hlhs := pasteCylinder_val_congr hk'
            (rectangleDiagramOfFunctor (pasteCylinder hl F F' h)).diagonal
            (CylinderComposition.secondDiagonal (pasteCylinder hl F F' h) (pasteCylinder hl G G' i) ee)
            (CylinderComposition.diagonal_matching _ _ ee)
            (pasteCylinder hl' (A F) (C F F' h) (AC F F' h))
            (pasteCylinder hl' (B F G e) (Z F G G' e i) (BZ F G G' e i))
            (outer_e F G F' G' e h i hl' ee)
            (fun z => pasteCylinder_succ_up hl' F F' h z) (fun z => (BZ_map F G G' e i hl' z).symm) x
          open PositiveInterchange in
          have hrhs := pasteCylinder_val_congr hl'
            (rectangleDiagramOfFunctor (pasteCylinder (Nat.lt_trans hkl hl) F G e)).diagonal
            (CylinderComposition.secondDiagonal (pasteCylinder (Nat.lt_trans hkl hl) F G e)
              (pasteCylinder (Nat.lt_trans hkl hl) F' G' j) hh)
            (CylinderComposition.diagonal_matching _ _ hh)
            (pasteCylinder hk' (A F) (B F G e) (AB F G e))
            (pasteCylinder hk' (C F F' h) (Z F G G' e i) (CZ F G F' G' e j h i))
            (outer_h F G F' G' e j h i hk' hh)
            (fun z => pasteCylinder_succ_up hk' F G e z) (fun z => (CZ_map F G F' G' e j h i hk' z).symm) x
          open PositiveInterchange in
          have hi := ih n l hkl' hl' (A F) (B F G e) (C F F' h) (Z F G G' e i)
            (AB F G e) (CZ F G F' G' e j h i) (AC F F' h) (BZ F G G' e i)
            (outer_e F G F' G' e h i hl' ee) (outer_h F G F' G' e j h i hk' hh)
          exact hlhs.trans ((congrArg (fun Q => (Q.map x).val) hi).trans hrhs.symm)
end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

namespace GrayRecursive
lemma restrictCylinder_above {n m : ℕ} (h : n ≤ m) {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) (b : Bool) :
    restrictCylinder m b F = restrictCylinder m false F := by
  unfold restrictCylinder
  rw [faceMap_above n m h b]

end GrayRecursive
end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

variable (Y : OmegaCategory.{u})

variable {Y}

lemma cell_ext {n : ℕ} {x y : Cell Y} (hx : Bounded n x) (hy : Bounded n y)
    (he : eval n x = eval n y) : x = y := by
  rw [← hx, ← hy, he]

lemma face_face (x : Cell Y) (i j : ℕ) (a b : Bool) :
    face i a (face j b x) = if i < j then face i a x else face j b x := by
  rw [← bounded_bound x, face_ofMap, face_ofMap]
  by_cases hij : i < j
  · rw [ite_eq_left hij, restrictCylinder_restrict hij, face_ofMap]
  · rw [ite_eq_right hij, restrictCylinder_above (by omega), ofMap_raise (by omega)]

lemma fixed_face {n : ℕ} {x : Cell Y} (h : Bounded n x) (b : Bool) : face n b x = x := by
  rw [face_eq_of_bounded h, restrictCylinder_self]
  exact h

lemma face_bound (x : Cell Y) (b : Bool) : face (bound x) b x = x := fixed_face (bounded_bound x) b

lemma face_represent {n k : ℕ} (hk : k ≤ n) (F : OmegaCategory.Functor (K.{u} n).nu Y)
    (b : Bool) : face k b (ofMap F) = ofMap (faceIdentityCylinder k b F) := by
  rw [face_ofMap]
  exact (ofMap_raise hk _).symm

end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

variable {Y : OmegaCategory.{u}}

lemma face_comp_le (i k : ℕ) (hik : i ≤ k) (x y : Cell Y)
    (h : face k true x = face k false y) (b : Bool) :
    face i b (comp k x y h) = face i b (if b then y else x) := by
  let N := max (k+1) (max (bound x) (bound y))
  have hk : k < N := by omega
  have hx : Bounded N x := (bounded_bound x).mono (by omega)
  have hy : Bounded N y := (bounded_bound y).mono (by omega)
  clear_value N
  obtain ⟨F,rfl⟩ : ∃ F : OmegaCategory.Functor (K.{u} N).nu Y, ofMap F = x := ⟨_,hx⟩
  obtain ⟨G,rfl⟩ : ∃ G : OmegaCategory.Functor (K.{u} N).nu Y, ofMap G = y := ⟨_,hy⟩
  rw [comp_ofMap hk, face_ofMap, pasteCylinder_lower_face N k i hk hik]
  cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true, face_ofMap]

lemma face_comp_gt (i k : ℕ) (hki : k < i) (x y : Cell Y)
    (h : face k true x = face k false y) (b : Bool)
    (hs : face k true (face i b x) = face k false (face i b y)) :
    face i b (comp k x y h) = comp k (face i b x) (face i b y) hs := by
  let N := max (k+1) (max (bound x) (bound y))
  have hk : k < N := by omega
  have hx : Bounded N x := (bounded_bound x).mono (by omega)
  have hy : Bounded N y := (bounded_bound y).mono (by omega)
  clear_value N
  obtain ⟨F,rfl⟩ : ∃ F : OmegaCategory.Functor (K.{u} N).nu Y, ofMap F = x := ⟨_,hx⟩
  obtain ⟨G,rfl⟩ : ∃ G : OmegaCategory.Functor (K.{u} N).nu Y, ofMap G = y := ⟨_,hy⟩
  simp only [face_ofMap] at hs ⊢
  rw [comp_ofMap hk, face_ofMap, pasteCylinder_restrict_gt N k i hk hki, comp_ofMap hki]
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {Y : OmegaCategory.{u}}

lemma comp_left_unit (k : ℕ) (x : Cell Y) (h : face k true (face k false x) = face k false x) :
    comp k (face k false x) x h = x := by
  let N := max (k+1) (bound x)
  have hk : k < N := by omega
  have hx : Bounded N x := (bounded_bound x).mono (by omega)
  clear_value N
  obtain ⟨F,rfl⟩ : ∃ F : OmegaCategory.Functor (K.{u} N).nu Y, ofMap F = x := ⟨_,hx⟩
  simp only [face_represent (Nat.le_of_lt hk)] at h ⊢
  rw [comp_ofMap hk, pasteCylinder_left_unit]

lemma comp_right_unit (k : ℕ) (x : Cell Y) (h : face k true x = face k false (face k true x)) :
    comp k x (face k true x) h = x := by
  let N := max (k+1) (bound x)
  have hk : k < N := by omega
  have hx : Bounded N x := (bounded_bound x).mono (by omega)
  clear_value N
  obtain ⟨F,rfl⟩ : ∃ F : OmegaCategory.Functor (K.{u} N).nu Y, ofMap F = x := ⟨_,hx⟩
  simp only [face_represent (Nat.le_of_lt hk)] at h ⊢
  rw [comp_ofMap hk, pasteCylinder_right_unit]

lemma comp_interchange (k l : ℕ) (hkl : k < l) (a b c d : Cell Y)
    (hab : face l true a = face l false b) (hcd : face l true c = face l false d)
    (hac : face k true a = face k false c) (hbd : face k true b = face k false d)
    (hab_cd : face k true (comp l a b hab) = face k false (comp l c d hcd))
    (hac_bd : face l true (comp k a c hac) = face l false (comp k b d hbd)) :
    comp k (comp l a b hab) (comp l c d hcd) hab_cd =
      comp l (comp k a c hac) (comp k b d hbd) hac_bd := by
  let N := max (l+1) (max (bound a) (max (bound b) (max (bound c) (bound d))))
  have hl : l < N := by omega
  have hk : k < N := by omega
  have ha : Bounded N a := (bounded_bound a).mono (by omega)
  have hb : Bounded N b := (bounded_bound b).mono (by omega)
  have hc : Bounded N c := (bounded_bound c).mono (by omega)
  have hd : Bounded N d := (bounded_bound d).mono (by omega)
  clear_value N
  obtain ⟨A,rfl⟩ : ∃ A : OmegaCategory.Functor (K.{u} N).nu Y, ofMap A = a := ⟨_,ha⟩
  obtain ⟨B,rfl⟩ : ∃ B : OmegaCategory.Functor (K.{u} N).nu Y, ofMap B = b := ⟨_,hb⟩
  obtain ⟨C,rfl⟩ : ∃ C : OmegaCategory.Functor (K.{u} N).nu Y, ofMap C = c := ⟨_,hc⟩
  obtain ⟨D,rfl⟩ : ∃ D : OmegaCategory.Functor (K.{u} N).nu Y, ofMap D = d := ⟨_,hd⟩
  simp only [comp_ofMap hk, comp_ofMap hl] at hab_cd hac_bd ⊢
  congr 1
  apply pasteCylinder_interchange N k l hkl hl

def omegaCategory (Y : OmegaCategory.{u}) : OmegaCategory.{u} where
  Cell := Cell Y
  source k x := face k false x
  target k x := face k true x
  source_source i j x := by
    rw [face_face]
    split
    · rename_i h
      rw [min_eq_left (le_of_lt h)]
    · rename_i h
      rw [min_eq_right (by omega)]
  target_target i j x := by
    rw [face_face]
    split
    · rename_i h
      rw [min_eq_left (le_of_lt h)]
    · rename_i h
      rw [min_eq_right (by omega)]
  source_target i j x := face_face x i j false true
  target_source i j x := face_face x i j true false
  comp := comp
  source_comp_le i k hik x y h := face_comp_le i k hik x y h false
  target_comp_le i k hik x y h := face_comp_le i k hik x y h true
  source_comp_gt i k hki x y h hs := face_comp_gt i k hki x y h false hs
  target_comp_gt i k hki x y h ht := face_comp_gt i k hki x y h true ht
  unit_left := comp_left_unit
  unit_right := comp_right_unit
  assoc := comp_assoc
  interchange := comp_interchange
  finite_dimension x := ⟨bound x, face_bound x false⟩
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

lemma face_false (n : ℕ) (x : Cell Y) : face n false x = ofMap (eval n x) := by
  unfold face
  rw [eval_eq_restrict (bounded_bound x) n]

lemma bounded_iff_fixed (n : ℕ) (x : Cell Y) : Bounded n x ↔ (omegaCategory Y).source n x = x := by
  change ofMap (eval n x) = x ↔ face n false x = x
  rw [face_false]

lemma mapCell_face (P : OmegaCategory.Functor Y Z) (x : Cell Y) (k : ℕ) (b : Bool) :
    mapCell P (face k b x) = face k b (mapCell P x) := by
  obtain ⟨n,hn⟩ := bounded_exists x
  obtain ⟨F,rfl⟩ : ∃ F : OmegaCategory.Functor (K.{u} n).nu Y, ofMap F = x := ⟨_,hn⟩
  simp only [face_ofMap, mapCell_ofMap, restrictCylinder_post]

lemma mapCell_comp (P : OmegaCategory.Functor Y Z) (x y : Cell Y) (k : ℕ)
    (h : face k true x = face k false y) (h' : face k true (mapCell P x) = face k false (mapCell P y)) :
    mapCell P (comp k x y h) = comp k (mapCell P x) (mapCell P y) h' := by
  let N := max (k+1) (max (bound x) (bound y))
  have hk : k < N := by omega
  have hx : Bounded N x := (bounded_bound x).mono (by omega)
  have hy : Bounded N y := (bounded_bound y).mono (by omega)
  clear_value N
  obtain ⟨F,rfl⟩ : ∃ F : OmegaCategory.Functor (K.{u} N).nu Y, ofMap F = x := ⟨_,hx⟩
  obtain ⟨G,rfl⟩ : ∃ G : OmegaCategory.Functor (K.{u} N).nu Y, ofMap G = y := ⟨_,hy⟩
  simp only [mapCell_ofMap, comp_ofMap hk]
  congr 1
  exact pasteCylinder_natural N k hk _ _ _ P

def mapFunctor (P : OmegaCategory.Functor Y Z) : OmegaCategory.Functor (omegaCategory Y) (omegaCategory Z) where
  map := mapCell P
  map_source k x := mapCell_face P x k false
  map_target k x := mapCell_face P x k true
  map_comp k x y h h' := mapCell_comp P x y k h h'

def functor : OmegaCategory.{u} ⥤ OmegaCategory.{u} where
  obj := omegaCategory
  map := mapFunctor
  map_id _ := rfl
  map_comp _ _ := rfl

end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma presentation_separates (P : OmegaCategory.Presentation.{u})
    {x y : Cell P.category}
    (h : ∀ (Y : OmegaCategory.{u}) (I : P.Interpretation Y),
      mapCell (P.lift Y I) x = mapCell (P.lift Y I) y) : x = y := by
  let N := max (bound x) (bound y)
  apply cell_ext ((bounded_bound x).mono (le_max_left _ _)) ((bounded_bound y).mono (le_max_right _ _))
  apply OmegaCategory.Functor.ext
  funext z
  apply P.cells_ext
  intro Y I
  exact congrArg (fun c => (eval N c).map z) (h Y I)

def TensorGenerator (X : OmegaCategory.{u}) := Σ n : ℕ, X.Cells n × (K.{u} n).nu.Cell

def tensorPresentation (X : OmegaCategory.{u}) : OmegaCategory.Presentation.{u} where
  Generator := TensorGenerator X
  dimension g := ((K g.1).nu.finite_dimension g.2.2).choose
  relations Y f := ∃ F : OmegaCategory.Functor X (omegaCategory Y),
    ∀ n (x : X.Cells n) (z : (K.{u} n).nu.Cell), f ⟨n,x,z⟩ = (eval n (F.map x.val)).map z

variable {X Y : OmegaCategory.{u}}

lemma functor_cell_bounded (F : OmegaCategory.Functor X (omegaCategory Y)) {n : ℕ} (x : X.Cells n) :
    Bounded n (F.map x.val) := by
  apply (bounded_iff_fixed n _).mpr
  rw [← F.map_source, x.property]

def tensorInterpretation (F : OmegaCategory.Functor X (omegaCategory Y)) :
    (tensorPresentation X).Interpretation Y where
  map g := (eval g.1 (F.map g.2.1.val)).map g.2.2
  bounded g := by
    change TensorGenerator X at g
    change Y.source ((K g.1).nu.finite_dimension g.2.2).choose ((eval g.1 (F.map g.2.1.val)).map g.2.2) = _
    rw [← OmegaCategory.Functor.map_source, ((K g.1).nu.finite_dimension g.2.2).choose_spec]
  satisfies := ⟨F, fun _ _ _ => rfl⟩

def generatorCylinder (n : ℕ) (x : X.Cells n) :
    OmegaCategory.Functor (K.{u} n).nu (tensorPresentation X).category where
  map z := (tensorPresentation X).generator ⟨n,x,z⟩
  map_source k z := by
    apply (tensorPresentation X).cells_ext
    intro Y I
    obtain ⟨F,hF⟩ := I.satisfies
    simp only [Presentation.evaluate_source]
    erw [Presentation.evaluate_generator, Presentation.evaluate_generator, hF, hF]
    exact (eval n (F.map x.val)).map_source k z
  map_target k z := by
    apply (tensorPresentation X).cells_ext
    intro Y I
    obtain ⟨F,hF⟩ := I.satisfies
    simp only [Presentation.evaluate_target]
    erw [Presentation.evaluate_generator, Presentation.evaluate_generator, hF, hF]
    exact (eval n (F.map x.val)).map_target k z
  map_comp k z w h h' := by
    apply (tensorPresentation X).cells_ext
    intro Y I
    obtain ⟨F,hF⟩ := I.satisfies
    simp only [Presentation.evaluate_comp]
    change I.map ⟨n,x,(K n).nu.comp k z w h⟩ =
      Y.comp k (I.map ⟨n,x,z⟩) (I.map ⟨n,x,w⟩) _
    simp only [hF n x]
    apply (eval n (F.map x.val)).map_comp

lemma generatorCylinder_interpretation (I : (tensorPresentation X).Interpretation Y)
    (F : OmegaCategory.Functor X (omegaCategory Y))
    (hF : ∀ n (x : X.Cells n) (z : (K.{u} n).nu.Cell), I.map ⟨n,x,z⟩ = (eval n (F.map x.val)).map z)
    (n : ℕ) (x : X.Cells n) :
    OmegaCategory.Functor.comp (generatorCylinder n x) ((tensorPresentation X).lift Y I) =
      eval n (F.map x.val) := OmegaCategory.Functor.ext (funext (hF n x))

lemma ofMap_generator_image (I : (tensorPresentation X).Interpretation Y)
    (F : OmegaCategory.Functor X (omegaCategory Y))
    (hF : ∀ n (x : X.Cells n) (z : (K.{u} n).nu.Cell), I.map ⟨n,x,z⟩ = (eval n (F.map x.val)).map z)
    (n : ℕ) (x : X.Cells n) :
    mapCell ((tensorPresentation X).lift Y I) (ofMap (generatorCylinder n x)) = F.map x.val := by
  rw [mapCell_ofMap, generatorCylinder_interpretation I F hF n x]
  exact functor_cell_bounded F x

def tensorUnitCell (x : X.Cell) : Cell (tensorPresentation X).category :=
  ofMap (generatorCylinder (X.finite_dimension x).choose ⟨x,(X.finite_dimension x).choose_spec⟩)

lemma tensorUnitCell_image (I : (tensorPresentation X).Interpretation Y)
    (F : OmegaCategory.Functor X (omegaCategory Y))
    (hF : ∀ n (x : X.Cells n) (z : (K.{u} n).nu.Cell), I.map ⟨n,x,z⟩ = (eval n (F.map x.val)).map z)
    (x : X.Cell) :
    mapCell ((tensorPresentation X).lift Y I) (tensorUnitCell x) = F.map x :=
  ofMap_generator_image I F hF _ _

lemma tensorUnitCell_of_bounded (n : ℕ) (x : X.Cells n) :
    tensorUnitCell x.val = ofMap (generatorCylinder n x) := by
  apply presentation_separates
  intro Y I
  obtain ⟨F,hF⟩ := I.satisfies
  rw [tensorUnitCell_image I F hF, ofMap_generator_image I F hF]

lemma tensorUnitCell_source (k : ℕ) (x : X.Cell) :
    tensorUnitCell (X.source k x) = (omegaCategory (tensorPresentation X).category).source k (tensorUnitCell x) := by
  apply presentation_separates
  intro Y I
  obtain ⟨F,hF⟩ := I.satisfies
  rw [tensorUnitCell_image I F hF]
  change F.map (X.source k x) = mapCell ((tensorPresentation X).lift Y I) (face k false (tensorUnitCell x))
  rw [mapCell_face, tensorUnitCell_image I F hF]
  exact F.map_source k x

lemma tensorUnitCell_target (k : ℕ) (x : X.Cell) :
    tensorUnitCell (X.target k x) = (omegaCategory (tensorPresentation X).category).target k (tensorUnitCell x) := by
  apply presentation_separates
  intro Y I
  obtain ⟨F,hF⟩ := I.satisfies
  rw [tensorUnitCell_image I F hF]
  change F.map (X.target k x) = mapCell ((tensorPresentation X).lift Y I) (face k true (tensorUnitCell x))
  rw [mapCell_face, tensorUnitCell_image I F hF]
  exact F.map_target k x

lemma tensorUnitCell_comp (k : ℕ) (x y : X.Cell) (h : X.target k x = X.source k y)
    (h' : (omegaCategory (tensorPresentation X).category).target k (tensorUnitCell x) =
      (omegaCategory (tensorPresentation X).category).source k (tensorUnitCell y)) :
    tensorUnitCell (X.comp k x y h) = (omegaCategory (tensorPresentation X).category).comp k
      (tensorUnitCell x) (tensorUnitCell y) h' := by
  apply presentation_separates
  intro Y I
  obtain ⟨F,hF⟩ := I.satisfies
  rw [tensorUnitCell_image I F hF]
  change F.map (X.comp k x y h) =
    (mapFunctor ((tensorPresentation X).lift Y I)).map
      ((omegaCategory (tensorPresentation X).category).comp k (tensorUnitCell x) (tensorUnitCell y) h')
  rw [(mapFunctor ((tensorPresentation X).lift Y I)).map_comp k _ _ h'
    ((mapFunctor ((tensorPresentation X).lift Y I)).map_composable h')]
  change F.map (X.comp k x y h) = (omegaCategory Y).comp k
    (mapCell ((tensorPresentation X).lift Y I) (tensorUnitCell x))
    (mapCell ((tensorPresentation X).lift Y I) (tensorUnitCell y)) _
  simp only [tensorUnitCell_image I F hF]
  apply F.map_comp

def tensorUnit (X : OmegaCategory.{u}) :
    OmegaCategory.Functor X (omegaCategory (tensorPresentation X).category) where
  map := tensorUnitCell
  map_source := tensorUnitCell_source
  map_target := tensorUnitCell_target
  map_comp := tensorUnitCell_comp
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {X Y Z : OmegaCategory.{u}}

def uncurry (F : OmegaCategory.Functor X (omegaCategory Y)) :
    OmegaCategory.Functor (tensorPresentation X).category Y :=
  (tensorPresentation X).lift Y (tensorInterpretation F)

def curry (F : OmegaCategory.Functor (tensorPresentation X).category Y) :
    OmegaCategory.Functor X (omegaCategory Y) :=
  OmegaCategory.Functor.comp (tensorUnit X) (mapFunctor F)

lemma curry_uncurry (F : OmegaCategory.Functor X (omegaCategory Y)) : curry (uncurry F) = F := by
  apply OmegaCategory.Functor.ext
  funext x
  exact tensorUnitCell_image (tensorInterpretation F) F (fun _ _ _ => rfl) x

lemma curry_eval (F : OmegaCategory.Functor (tensorPresentation X).category Y)
    (n : ℕ) (x : X.Cells n) (z : (K.{u} n).nu.Cell) :
    (eval n ((curry F).map x.val)).map z = F.map ((tensorPresentation X).generator ⟨n,x,z⟩) := by
  change (eval n (mapCell F (tensorUnitCell x.val))).map z = _
  rw [tensorUnitCell_of_bounded n x, mapCell_ofMap, eval_ofMap_self]
  rfl

lemma uncurry_curry (F : OmegaCategory.Functor (tensorPresentation X).category Y) : uncurry (curry F) = F := by
  apply (tensorPresentation X).functor_ext
  intro ⟨n,x,z⟩
  exact curry_eval F n x z

def homEquiv (X Y : OmegaCategory.{u}) :
    ((tensorPresentation X).category ⟶ Y) ≃ (X ⟶ functor.obj Y) where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

lemma homEquiv_natural (X Y Z : OmegaCategory.{u}) (P : Y ⟶ Z) (F : (tensorPresentation X).category ⟶ Y) :
    homEquiv X Z (F ≫ P) = homEquiv X Y F ≫ functor.map P := rfl

def tensorFunctor : OmegaCategory.{u} ⥤ OmegaCategory.{u} :=
  Adjunction.leftAdjointOfEquiv homEquiv homEquiv_natural

def tensorAdjunction : tensorFunctor.{u} ⊣ functor :=
  Adjunction.adjunctionOfEquivLeft homEquiv homEquiv_natural

instance tensorFunctor_isLeftAdjoint : tensorFunctor.{u}.IsLeftAdjoint := ⟨functor, ⟨tensorAdjunction⟩⟩
instance tensorFunctor_preservesColimits : Limits.PreservesColimitsOfSize.{u,u} tensorFunctor.{u} :=
  tensorAdjunction.leftAdjoint_preservesColimits

lemma tensorFunctor_map_generator (P : X ⟶ Y) (n : ℕ) (x : X.Cells n) (z : (K.{u} n).nu.Cell) :
    (tensorFunctor.map P).map ((tensorPresentation X).generator ⟨n,x,z⟩) =
      (tensorPresentation Y).generator ⟨n,⟨P.map x.val, by rw [← P.map_source, x.property]⟩,z⟩ := by
  change (eval n (tensorUnitCell (P.map x.val))).map z = _
  rw [tensorUnitCell_of_bounded n ⟨P.map x.val, by rw [← P.map_source, x.property]⟩, eval_ofMap_self]
  rfl
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {X Y Z : OmegaCategory.{u}}

def endpointFunctor (a : Bool) (Y : OmegaCategory.{u}) : OmegaCategory.Functor (omegaCategory Y) Y where
  map := endpointCell a
  map_source k x := endpointCell_face a x k false
  map_target k x := endpointCell_face a x k true
  map_comp k x y h h' := endpointCell_comp a x y k h h'

def tensorEndpoint (a : Bool) : 𝟭 OmegaCategory.{u} ⟶ tensorFunctor.{u} where
  app X := OmegaCategory.Functor.comp (tensorUnit X) (endpointFunctor a (tensorFunctor.obj X))
  naturality X Y P := by
    apply OmegaCategory.Functor.ext
    funext x
    obtain ⟨n,hn⟩ := X.finite_dimension x
    change endpointCell a (tensorUnitCell (P.map x)) = (tensorFunctor.map P).map (endpointCell a (tensorUnitCell x))
    erw [tensorUnitCell_of_bounded n ⟨x,hn⟩, tensorUnitCell_of_bounded n ⟨P.map x, by rw [← P.map_source,hn]⟩,
      endpointCell_ofMap, endpointCell_ofMap]
    exact (tensorFunctor_map_generator P n ⟨x,hn⟩ (atEnd a (topTable n))).symm

lemma tensorEndpoint_bounded (a : Bool) (X : OmegaCategory.{u}) (n : ℕ) (x : X.Cells n) :
    ((tensorEndpoint a).app X).map x.val = (tensorPresentation X).generator ⟨n,x,atEnd a (topTable n)⟩ := by
  change endpointCell a (tensorUnitCell x.val) = _
  rw [tensorUnitCell_of_bounded n x, endpointCell_ofMap]
  rfl
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {X Y Z : OmegaCategory.{u}}

lemma constantInterval_restrict {n k : ℕ} (F : OmegaCategory.Functor (complex.{u} n).nu Y) (b : Bool) :
    restrictCylinder k b (constantInterval F) =
      constantInterval (OmegaCategory.Functor.comp (faceMap n k b).nu F) := by
  apply OmegaCategory.Functor.ext
  funext z
  exact congrArg F.map (congrArg (fun P => P.nu.map z) (faceMap.{u} n k b).cylinder_projection)

lemma lift_face (x : Y.Cell) {n : ℕ} (hx : Y.source n x = x) (k : ℕ) (b : Bool) :
    OmegaCategory.Functor.comp (faceMap.{u} n k b).nu (lift x hx) =
      lift (Y.face k b x) (by cases b <;> simp [OmegaCategory.face]) := by
  apply GlobeComplex.functor_ext
  change (lift x hx).map ((faceMap n k b).nu.map (topTable k)) = _
  rw [faceMap_top, lift_top]
  exact evaluate_face x hx k b

lemma constant_bound_mono (x : Y.Cell) {n m : ℕ} (hn : Y.source n x = x) (hm : Y.source m x = x)
    (hnm : n ≤ m) :
    ofMap (constantInterval (lift.{u,u} x hn)) = ofMap (constantInterval (lift x hm)) := by
  rw [← ofMap_raise hnm (constantInterval (lift x hn)), constantInterval_restrict]
  apply congrArg (fun F : OmegaCategory.Functor (complex.{u} m).nu Y => ofMap (constantInterval F))
  apply GlobeComplex.functor_ext
  change (lift x hn).map ((faceMap n m false).nu.map (topTable m)) = _
  rw [faceMap_top, lift_top]
  exact (evaluate_face x hn m false).trans hm

lemma constant_bound_independent (x : Y.Cell) {n m : ℕ} (hn : Y.source n x = x) (hm : Y.source m x = x) :
    ofMap (constantInterval (lift.{u,u} x hn)) = ofMap (constantInterval (lift x hm)) := by
  have hnm := Y.source_fixed_upwards (le_max_left n m) hn
  rw [constant_bound_mono x hn hnm (le_max_left n m), constant_bound_mono x hm hnm (le_max_right n m)]

def constantCell (x : Y.Cell) : Cell Y :=
  ofMap (constantInterval (lift x (Y.finite_dimension x).choose_spec))

lemma constantCell_of_bounded (n : ℕ) (x : Y.Cell) (hx : Y.source n x = x) :
    constantCell x = ofMap (constantInterval (lift.{u,u} x hx)) :=
  constant_bound_independent x _ hx

lemma constantCell_face (x : Y.Cell) (k : ℕ) (b : Bool) :
    constantCell (Y.face k b x) = face k b (constantCell x) := by
  obtain ⟨n,hn⟩ := Y.finite_dimension x
  have hface : Y.source k (Y.face k b x) = Y.face k b x := by cases b <;> simp [OmegaCategory.face]
  rw [constantCell_of_bounded n x hn, face_ofMap, constantInterval_restrict, lift_face,
    constantCell_of_bounded k (Y.face k b x) hface]

lemma constantCell_comp (x y : Y.Cell) (k : ℕ) (h : Y.target k x = Y.source k y)
    (h' : face k true (constantCell x) = face k false (constantCell y)) :
    constantCell (Y.comp k x y h) = comp k (constantCell x) (constantCell y) h' := by
  obtain ⟨m,hm⟩ := Y.finite_dimension x
  obtain ⟨l,hl⟩ := Y.finite_dimension y
  let N := max (k+1) (max m l)
  have hk : k < N := by omega
  have hx : Y.source N x = x := Y.source_fixed_upwards (by omega : m ≤ N) hm
  have hy : Y.source N y = y := Y.source_fixed_upwards (by omega : l ≤ N) hl
  have hxy : Y.source N (Y.comp k x y h) = Y.comp k x y h := by
    rw [Y.source_comp_gt N k hk x y h (Y.source_composable hk h)]
    simp only [hx,hy]
  simp only [constantCell_of_bounded N x hx, constantCell_of_bounded N y hy] at h' ⊢
  rw [constantCell_of_bounded N (Y.comp k x y h) hxy, comp_ofMap hk]
  have hw : Y.target k ((lift.{u,u} x hx).map (topTable N)) =
      Y.source k ((lift.{u,u} y hy).map (topTable N)) := by simpa only [lift_top] using h
  rw [pasteCylinder_constant N k hk _ _ hw]
  congr 2
  apply GlobeComplex.functor_ext
  rw [lift_top, globeComposite_top, lift_top, lift_top, Y.join_eq k x y h]

def constantFunctor (Y : OmegaCategory.{u}) : OmegaCategory.Functor Y (omegaCategory Y) where
  map := constantCell
  map_source k x := constantCell_face x k false
  map_target k x := constantCell_face x k true
  map_comp k x y h h' := constantCell_comp x y k h h'

lemma constantCell_map (P : OmegaCategory.Functor Y Z) (x : Y.Cell) :
    constantCell (P.map x) = mapCell P (constantCell x) := by
  obtain ⟨n,hn⟩ := Y.finite_dimension x
  have hp : Z.source n (P.map x) = P.map x := by rw [← P.map_source,hn]
  rw [constantCell_of_bounded n x hn, constantCell_of_bounded n (P.map x) hp, mapCell_ofMap]
  apply congrArg ofMap
  have he : lift.{u,u} (P.map x) hp = OmegaCategory.Functor.comp (lift x hn) P := by
    apply GlobeComplex.functor_ext
    change _ = P.map ((lift x hn).map (topTable n))
    rw [lift_top,lift_top]
  rw [he]
  rfl

def tensorProjection : tensorFunctor.{u} ⟶ 𝟭 OmegaCategory.{u} where
  app X := uncurry (constantFunctor X)
  naturality X Y P := by
    apply (tensorPresentation X).functor_ext
    intro ⟨n,x,z⟩
    change ((uncurry (constantFunctor Y)).map ((tensorFunctor.map P).map
      ((tensorPresentation X).generator ⟨n,x,z⟩))) =
      P.map ((uncurry (constantFunctor X)).map ((tensorPresentation X).generator ⟨n,x,z⟩))
    rw [tensorFunctor_map_generator]
    change (eval n (constantCell (P.map x.val))).map z = P.map ((eval n (constantCell x.val)).map z)
    rw [constantCell_map,eval_mapCell]
    rfl

lemma tensorProjection_generator (X : OmegaCategory.{u}) (n : ℕ) (x : X.Cells n) (z : (K.{u} n).nu.Cell) :
    (tensorProjection.app X).map ((tensorPresentation X).generator ⟨n,x,z⟩) =
      (lift.{u,u} x.val x.property).map (project z) := by
  change (eval n (constantCell x.val)).map z = _
  rw [constantCell_of_bounded n x.val x.property, eval_ofMap_self]
  rfl

lemma tensorEndpoint_projection (a : Bool) : tensorEndpoint.{u} a ≫ tensorProjection = 𝟙 (𝟭 OmegaCategory.{u}) := by
  ext X
  apply OmegaCategory.Functor.ext
  funext x
  obtain ⟨n,hn⟩ := X.finite_dimension x
  change (tensorProjection.app X).map (((tensorEndpoint a).app X).map x) = x
  erw [tensorEndpoint_bounded a X n ⟨x,hn⟩,tensorProjection_generator, project_end, lift_top]
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

def globeDiagram (n : ℕ) : OmegaCategory.Functor (complex.{u} n).nu (omegaCategory (K.{u} n).nu) :=
  lift (ofMap (OmegaCategory.Functor.id (K.{u} n).nu))
    ((bounded_iff_fixed n _).mp (ofMap_bounded _))

lemma globeDiagram_top (n : ℕ) :
    (globeDiagram.{u} n).map (topTable n) = ofMap (OmegaCategory.Functor.id (K.{u} n).nu) :=
  lift_top _ _

lemma globeDiagram_face (m p : ℕ) (b : Bool) :
    (globeDiagram.{u} m).map (truncate p b (topTable m)) = ofMap (faceMap m p b).cylinder.nu := by
  erw [← face_nu, (globeDiagram m).map_face, globeDiagram_top]
  cases b <;> exact face_ofMap _ _ _

lemma globeDiagram_map (n m : ℕ) (a : Hom (complex.{u} n) (complex.{u} m)) :
    (globeDiagram m).map (a.nu.map (topTable n)) = ofMap a.cylinder.nu := by
  let t := a.nu.map (topTable n)
  have ht : truncate n false t = t := by
    exact (a.nu.map_source n (topTable n)).symm.trans (congrArg a.nu.map (topTable_bounded n))
  have hb : Bounded n ((globeDiagram m).map t) := by
    apply (bounded_iff_fixed n _).mpr
    exact ((globeDiagram m).map_source n t).symm.trans (congrArg (globeDiagram m).map ht)
  rw [← hb]
  apply congrArg ofMap
  obtain ⟨p,b,_,he⟩ := table_classification t
  have ha : a = Hom.comp (faceMap.{u} p n false) (faceMap m p b) := by
    apply GlobeComplex.hom_ext
    change t = (faceMap m p b).nu.map ((faceMap p n false).nu.map (topTable n))
    rw [faceMap_top]
    change t = (faceMap m p b).table (truncate n false (topTable p))
    rw [Hom.table_truncate]
    change t = truncate n false ((faceMap m p b).nu.map (topTable p))
    rw [faceMap_top,← he,ht]
  rw [he,globeDiagram_face,eval_ofMap,ha,Hom.cylinder_comp]
  rfl

def globeTensorHom (n : ℕ) : tensorFunctor.obj (complex.{u} n).nu ⟶ (K.{u} n).nu :=
  uncurry (globeDiagram n)

def globeTensorInv (n : ℕ) : (K.{u} n).nu ⟶ tensorFunctor.obj (complex.{u} n).nu :=
  generatorCylinder n ⟨topTable n,topTable_bounded n⟩

lemma globeTensorHom_generator (n k : ℕ) (x : (complex.{u} n).nu.Cells k) (z : (K.{u} k).nu.Cell) :
    (globeTensorHom n).map ((tensorPresentation (complex.{u} n).nu).generator ⟨k,x,z⟩) =
      (eval k ((globeDiagram n).map x.val)).map z := rfl

lemma globeTensorHom_inv (n : ℕ) : globeTensorHom.{u} n ≫ globeTensorInv n = 𝟙 _ := by
  apply (homEquiv (complex.{u} n).nu (tensorFunctor.obj (complex n).nu)).injective
  erw [homEquiv_natural]
  change OmegaCategory.Functor.comp (curry (uncurry (globeDiagram n))) (mapFunctor (globeTensorInv n)) =
    curry (𝟙 (tensorFunctor.obj (complex n).nu))
  rw [curry_uncurry]
  apply GlobeComplex.functor_ext
  change mapCell (globeTensorInv n) ((globeDiagram n).map (topTable n)) = tensorUnitCell (topTable n)
  rw [globeDiagram_top,mapCell_ofMap]
  rw [tensorUnitCell_of_bounded (X := (complex n).nu) n ⟨topTable.{u} n,topTable_bounded n⟩]
  rfl

lemma globeTensorInv_hom (n : ℕ) : globeTensorInv.{u} n ≫ globeTensorHom n = 𝟙 _ := by
  apply OmegaCategory.Functor.ext
  funext z
  change (eval n ((globeDiagram n).map (topTable n))).map z = z
  rw [globeDiagram_top,eval_ofMap_self]
  rfl

def globeTensorIso (n : ℕ) : tensorFunctor.obj (complex.{u} n).nu ≅ (complex.{u} n).cylinder.nu where
  hom := globeTensorHom n
  inv := globeTensorInv n
  hom_inv_id := globeTensorHom_inv n
  inv_hom_id := globeTensorInv_hom n

lemma globeTensorIso_natural (n m : ℕ) (a : Hom (complex.{u} n) (complex.{u} m)) :
    tensorFunctor.map a.nu ≫ (globeTensorIso m).hom = (globeTensorIso n).hom ≫ a.cylinder.nu := by
  apply (homEquiv (complex.{u} n).nu (K.{u} m).nu).injective
  have hl : homEquiv (complex.{u} n).nu (K.{u} m).nu (tensorFunctor.map a.nu ≫ (globeTensorIso m).hom) =
      a.nu ≫ globeDiagram m := by
    change tensorAdjunction.homEquiv _ _ (tensorFunctor.map a.nu ≫ (globeTensorIso m).hom) = _
    rw [tensorAdjunction.homEquiv_naturality_left]
    change OmegaCategory.Functor.comp a.nu (curry (uncurry (globeDiagram m))) = _
    rw [curry_uncurry]
    rfl
  erw [hl,homEquiv_natural]
  change OmegaCategory.Functor.comp a.nu (globeDiagram m) =
    OmegaCategory.Functor.comp (curry (uncurry (globeDiagram n))) (mapFunctor a.cylinder.nu)
  rw [curry_uncurry]
  apply GlobeComplex.functor_ext
  change (globeDiagram m).map (a.nu.map (topTable n)) = mapCell a.cylinder.nu ((globeDiagram n).map (topTable n))
  rw [globeDiagram_map,globeDiagram_top,mapCell_ofMap]
  rfl

lemma globeTensorIso_endpoint (n : ℕ) (b : Bool) :
    (tensorEndpoint b).app (complex.{u} n).nu ≫ (globeTensorIso n).hom =
      ((complex n).cylinderEndpoint b).nu := by
  apply GlobeComplex.functor_ext
  change (globeTensorHom n).map (((tensorEndpoint b).app (complex n).nu).map (topTable n)) = _
  erw [tensorEndpoint_bounded b (complex n).nu n ⟨topTable n,topTable_bounded n⟩,
    globeTensorHom_generator,globeDiagram_top,eval_ofMap_self]
  rfl

lemma globeTensorIso_projection (n : ℕ) :
    (globeTensorIso.{u} n).hom ≫ (complex n).cylinderProjection.nu = tensorProjection.app (complex n).nu := by
  apply (homEquiv (complex.{u} n).nu (complex n).nu).injective
  erw [homEquiv_natural]
  change OmegaCategory.Functor.comp (curry (uncurry (globeDiagram n))) (mapFunctor (complex n).cylinderProjection.nu) =
    curry (uncurry (constantFunctor (complex n).nu))
  rw [curry_uncurry,curry_uncurry]
  apply GlobeComplex.functor_ext
  change mapCell (complex n).cylinderProjection.nu ((globeDiagram n).map (topTable n)) = constantCell (topTable n)
  rw [globeDiagram_top,mapCell_ofMap]
  rw [constantCell_of_bounded (Y := (complex n).nu) n (topTable.{u} n) (topTable_bounded n)]
  apply congrArg ofMap
  have he : lift.{u,u} (topTable n) (topTable_bounded n) = OmegaCategory.Functor.id (complex n).nu := by
    apply GlobeComplex.functor_ext
    exact lift_top _ _
  rw [he]
  rfl
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma concatInterval_weight (n : ℕ) {Y : OmegaCategory.{v}} {A : Type w} [AddCommMonoid A]
    (q : CellWeight Y (n+1) A)
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : IntervalMatching F G) :
    q ((concatInterval F G h).map (verticalTable (topTable n))) =
      q (F.map (verticalTable (topTable n))) + q (G.map (verticalTable (topTable n))) := by
  induction n generalizing Y with
  | zero =>
    rw [concatInterval_zero_vertical]
    exact q.add 0 (by omega) _ _ (zero_interval_seam F G h)
  | succ n ih =>
    rw [← suspendTable_top n, ← up_vertical, concatInterval_succ_up]
    let D := rectangleDiagramOfFunctor F
    let E := rectangleDiagramOfFunctor G
    let x := verticalTable (topTable.{u} n)
    have hw := ih (q.hom ((D.ends false).map (vertex n false)) ((E.ends true).map (vertex n true)))
      (D.concatDiagonalOne E h) (D.concatDiagonalTwo E h) (D.concatDiagonal_matching E h)
    change q _ = q _ + q _ at hw
    rw [hw]
    change q (Y.join 0 (D.edge false) (E.diagonal.map x).val) +
        q (Y.join 0 (D.diagonal.map x).val (E.edge true)) = _
    rw [q.add 0 (by omega) _ _ ((D.edge_target false).trans ((h _).trans (E.diagonal.map x).property.1.symm)),
      q.add 0 (by omega) _ _ ((D.diagonal.map x).property.2.trans ((h _).trans (E.edge_source true).symm)),
      q.vanish 1 (by omega) _ (D.edge_fixed false), q.vanish 1 (by omega) _ (E.edge_fixed true),
      zero_add, add_zero]
    exact add_comm _ _

lemma horizontalCylinder_weight {n : ℕ} {Y : OmegaCategory.{v}} {A : Type w} [AddCommMonoid A]
    (q : CellWeight Y (n+1+1) A)
    (F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y)
    (h : F.map (verticalTable (vertex n true)) = G.map (verticalTable (vertex n false))) :
    q ((horizontalCylinder F G h).map (verticalTable (topTable (n+1)))) =
      q (F.map (verticalTable (topTable (n+1)))) + q (G.map (verticalTable (topTable (n+1)))) := by
  rw [← suspendTable_top n, ← up_vertical]
  change q (((rectangleDiagramOfFunctor F).horizontal (rectangleDiagramOfFunctor G) h).lift.map _) = _
  rw [RectangleDiagram.lift_up]
  let D := rectangleDiagramOfFunctor F
  let E := rectangleDiagramOfFunctor G
  let x := verticalTable (topTable.{u} n)
  have hw := concatInterval_weight n
    (q.hom ((D.ends false).map (vertex n false)) ((E.ends true).map (vertex n true)))
    (D.horizontalDiagonalOne E h) (D.horizontalDiagonalTwo E h) (D.horizontalDiagonal_matching E h)
  change q _ = q _ + q _ at hw
  change q ((concatInterval (D.horizontalDiagonalOne E h) (D.horizontalDiagonalTwo E h)
    (D.horizontalDiagonal_matching E h)).map x).val = _
  rw [hw]
  change q (Y.join 0 (D.diagonal.map x).val ((E.ends true).map (suspendTable (project x)))) +
    q (Y.join 0 ((D.ends false).map (suspendTable (project x))) (E.diagonal.map x).val) = _
  have hb (a : Bool) (R : RectangleDiagram.{u,v} n Y) :
      Y.source (n+1) ((R.ends a).map (suspendTable (project x))) =
        (R.ends a).map (suspendTable (project x)) := by
    erw [← (R.ends a).map_source]
    exact congrArg (R.ends a).map (dimension_of_rows_above_zero _
      (fun p hp b => chain_zero hp _))
  rw [q.add 0 (by omega) _ _ ((D.diagonal.map x).property.2.trans (by
      erw [← (E.ends true).map_source]
      change _ = (E.ends true).map (truncate 0 false (suspendTable (project x)))
      rw [suspend_truncate_zero]
      exact D.horizontal_seam E h true)),
    q.add 0 (by omega) _ _ ((by
      erw [← (D.ends false).map_target]
      change (D.ends false).map (truncate 0 true (suspendTable (project x))) = _
      rw [suspend_truncate_zero]
      exact (D.horizontal_seam E h false).trans (E.diagonal.map x).property.1.symm)),
    q.vanish (n+1) (by omega) _ (hb true E), q.vanish (n+1) (by omega) _ (hb false D),
    add_zero, zero_add]
  rfl

lemma pasteCylinder_weight (n k : ℕ) (hk : k < n)
    {Y : OmegaCategory.{v}} {A : Type w} [AddCommMonoid A]
    (q : CellWeight Y (n+1) A)
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : FaceMatching k F G) :
    q ((pasteCylinder hk F G h).map (verticalTable (topTable n))) =
      q (F.map (verticalTable (topTable n))) + q (G.map (verticalTable (topTable n))) := by
  induction k generalizing n Y with
  | zero =>
    cases n with
    | zero => omega
    | succ n =>
      rw [pasteCylinder_zero]
      exact horizontalCylinder_weight q F G _
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      have hk' : k < n := by omega
      rw [← suspendTable_top n, ← up_vertical, pasteCylinder_succ_up hk']
      exact ih n hk' (q.hom _ _) (rectangleDiagramOfFunctor F).diagonal
        (CylinderComposition.secondDiagonal F G h) (CylinderComposition.diagonal_matching F G h)
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


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma table_functor_ext {n : ℕ} {M : DirectedComplex.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu M.nu)
    (hend : ∀ a x, F.map (atEnd a x) = G.map (atEnd a x))
    (hvert : ∀ r a b,
      (F.map (verticalTable (truncate r a (topTable n)))).row (r+1) b =
      (G.map (verticalTable (truncate r a (topTable n)))).row (r+1) b) : F = G := by
  have he (p : ℕ) (x : Table (K.{u} n)) (hx : truncate p false x = x) :
      ∀ b, (F.map x).row p b = (G.map x).row p b := by
    apply generated_bounded n p (fun z => ∀ b, (F.map z).row p b = (G.map z).row p b)
      (fun a x hx b => congrArg (fun z : Table M => z.row p b) (hend a x)) ?_ ?_ x hx
    · intro r hr t ht b
      obtain ⟨d,a,_,hdr,ht'⟩ := bounded_table_classification t ht
      have hb : truncate d false t = t := by rw [ht']; simp only [truncate_truncate,lt_self_iff_false,ite_false]
      have hF : truncate (d+1) false (F.map (verticalTable t)) = F.map (verticalTable t) :=
        (F.map_source (d+1) _).symm.trans (congrArg F.map (vertical_fixed t hb))
      have hG : truncate (d+1) false (G.map (verticalTable t)) = G.map (verticalTable t) :=
        (G.map_source (d+1) _).symm.trans (congrArg G.map (vertical_fixed t hb))
      by_cases hp : d+1 < p
      · rw [row_above_fixed _ hF hp, row_above_fixed _ hG hp]
      · have hp' : p = d+1 := by omega
        rw [hp',ht']
        exact hvert d a b
    · intro l s t h hs ht b
      have hf := F.map_comp l s t h (F.map_composable h)
      have hg := G.map_comp l s t h (G.map_composable h)
      change F.map (DirectedComplex.Table.comp l s t h) = DirectedComplex.Table.comp l _ _ (F.map_composable h) at hf
      change G.map (DirectedComplex.Table.comp l s t h) = DirectedComplex.Table.comp l _ _ (G.map_composable h) at hg
      erw [hf,hg,comp_row,comp_row]
      split_ifs <;> simp only [hs,ht]
  apply OmegaCategory.Functor.ext
  funext x
  change Table (K.{u} n) at x
  apply DirectedComplex.Table.ext
  funext p b
  have h := he p (truncate p b x) (by simp only [truncate_truncate,lt_self_iff_false,ite_false]) false
  have hf : F.map (truncate p b x) = truncate p b (F.map x) := by
    cases b <;> first | exact F.map_source p x | exact F.map_target p x
  have hg : G.map (truncate p b x) = truncate p b (G.map x) := by
    cases b <;> first | exact G.map_source p x | exact G.map_target p x
  rw [hf,hg] at h
  erw [truncate_row,truncate_row] at h
  simpa only [lt_self_iff_false,ite_false,ite_true] using h

def tableCylinder {M : DirectedComplex.{v}} (n : ℕ) (t : Table M) :
    OmegaCategory.Functor (K.{u} n).nu M.cylinder.nu := (tableMap n t).cylinder.nu

lemma tableCylinder_endpoint {M : DirectedComplex.{v}} (n : ℕ) (t : Table M)
    (a : Bool) (x : Table (complex.{u} n)) :
    (tableCylinder n t).map (atEnd a x) = (M.cylinderEndpoint a).nu.map ((tableMap n t).nu.map x) := by
  exact congrArg (fun h => h.nu.map x) (Hom.cylinder_endpoint (tableMap n t) a)

lemma tableCylinder_endpoint_top {M : DirectedComplex.{v}} (n : ℕ) (t : Table M) (a : Bool) :
    (tableCylinder.{u,v} n t).map (atEnd a (topTable n)) = (M.cylinderEndpoint a).nu.map (truncate n false t) := by
  rw [tableCylinder_endpoint, tableMap_nu_top]

lemma tableCylinder_vertical {M : DirectedComplex.{v}} (n : ℕ) (t : Table M) :
    (tableCylinder.{u,v} n t).map (verticalTable (topTable n)) = verticalTable (truncate n false t) :=
  (verticalTable_natural (tableMap n t) (topTable n)).trans (congrArg verticalTable (tableMap_nu_top n t))

lemma tableCylinder_restrict {M : DirectedComplex.{v}} (n : ℕ) (t : Table M)
    (ht : truncate n false t = t) (i : ℕ) (b : Bool) :
    restrictCylinder i b (tableCylinder.{u,v} n t) = tableCylinder i (truncate i b t) := by
  have he : Hom.comp (faceMap.{u} n i b) (tableMap.{u,v} n t) = tableMap i (truncate i b t) := by
    apply GlobeComplex.hom_ext
    change (tableMap n t).nu.map ((faceMap n i b).nu.map (topTable i)) = _
    erw [faceMap_top, ← face_nu, OmegaCategory.Functor.map_face, tableMap_nu_top, ht]
    rw [tableMap_nu_top]
    cases b <;> change truncate i _ t = truncate i false (truncate i _ t)
    all_goals simp only [truncate_truncate,lt_self_iff_false,ite_false]
  change (Hom.comp (faceMap n i b).cylinder (tableMap n t).cylinder).nu = _
  rw [← Hom.cylinder_comp,he]
  rfl

lemma tableCylinder_matching {M : DirectedComplex.{v}} {n k : ℕ} {x y : Table M}
    (hx : truncate n false x = x) (hy : truncate n false y = y)
    (h : truncate k true x = truncate k false y) :
    FaceMatching k (tableCylinder.{u,v} n x) (tableCylinder n y) := by
  intro z
  have he : restrictCylinder k true (tableCylinder.{u,v} n x) =
      restrictCylinder k false (tableCylinder.{u,v} n y) := by
    rw [tableCylinder_restrict n x hx, tableCylinder_restrict n y hy,h]
  exact congrArg (fun P => P.map z) he

lemma vertical_top_row {M : DirectedComplex.{v}} {n : ℕ} (x : Table M)
    (hx : truncate n false x = x) (b : Bool) :
    (verticalTable x).row (n+1) b = (0,0,x.row n false) := by
  have h₀ := row_above_fixed x hx (by omega : n < n+1)
  have h₁ : x.row n true = x.row n false := by
    have he := congrArg (fun t : Table M => t.row n true) hx
    simpa only [truncate_row, lt_self_iff_false, ite_false, ite_true] using he.symm
  cases b <;> simp [verticalTable,verticalRow,h₀,h₁]

lemma table_comp_bounded {M : DirectedComplex.{v}} {n k : ℕ} (hk : k < n)
    (x y : Table M) (hx : truncate n false x = x) (hy : truncate n false y = y)
    (h : truncate k true x = truncate k false y) :
    truncate n false (DirectedComplex.Table.comp k x y h) = DirectedComplex.Table.comp k x y h := by
  apply fixed_of_rows_zero
  intro p hp b
  rw [comp_row]
  simp only [show ¬p < k by omega, show p ≠ k by omega, ite_false,
    row_above_fixed x hx hp, row_above_fixed y hy hp, add_zero]

lemma restrictCylinder_vertical_top {n i : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) (b : Bool) :
    (restrictCylinder i b F).map (verticalTable (topTable i)) =
      F.map (verticalTable (truncate i b (topTable n))) := by
  change F.map ((faceMap n i b).cylinder.nu.map (verticalTable (topTable i))) = _
  rw [verticalTable_natural,faceMap_top]

lemma tableCylinder_comp {M : DirectedComplex.{v}} {n k : ℕ} (hk : k < n)
    (x y : Table M) (hx : truncate n false x = x) (hy : truncate n false y = y)
    (h : truncate k true x = truncate k false y) :
    pasteCylinder hk (tableCylinder.{u,v} n x) (tableCylinder n y) (tableCylinder_matching hx hy h) =
      tableCylinder n (DirectedComplex.Table.comp k x y h) := by
  have hz := table_comp_bounded hk x y hx hy h
  apply table_functor_ext
  · intro a t
    have he : endGlobe (pasteCylinder hk (tableCylinder.{u,v} n x) (tableCylinder n y)
        (tableCylinder_matching hx hy h)) a =
        endGlobe (tableCylinder n (DirectedComplex.Table.comp k x y h)) a := by
      apply GlobeComplex.functor_ext
      change (pasteCylinder hk _ _ _).map (atEnd a (topTable n)) = _
      rw [pasteCylinder_endpoint_top,tableCylinder_endpoint_top,tableCylinder_endpoint_top,hx,hy]
      change M.cylinder.nu.join k ((M.cylinderEndpoint a).nu.map x) ((M.cylinderEndpoint a).nu.map y) =
        (tableCylinder n (DirectedComplex.Table.comp k x y h)).map (atEnd a (topTable n))
      rw [tableCylinder_endpoint_top,hz, ← (M.cylinderEndpoint a).nu.map_join k x y h, M.nu.join_eq k x y h]
      rfl
    exact congrArg (fun P => P.map t) he
  · intro r a b
    rw [← restrictCylinder_vertical_top, ← restrictCylinder_vertical_top]
    by_cases hr : r ≤ k
    · rw [pasteCylinder_lower_face n k r hk hr]
      cases a <;> simp only [Bool.false_eq_true,ite_false,ite_true]
      · rw [tableCylinder_restrict _ _ hx,tableCylinder_restrict _ _ hz,source_comp_le r k hr]
      · rw [tableCylinder_restrict _ _ hy,tableCylinder_restrict _ _ hz,target_comp_le r k hr]
    · have hkr : k < r := by omega
      rw [pasteCylinder_restrict_gt n k r hk hkr]
      have hw := pasteCylinder_weight r k hkr (CellWeight.row M.cylinder (r+1) b)
        (restrictCylinder r a (tableCylinder.{u,v} n x))
        (restrictCylinder r a (tableCylinder.{u,v} n y)) ((tableCylinder_matching hx hy h).restrict hkr a)
      change ((pasteCylinder hkr (restrictCylinder r a (tableCylinder.{u,v} n x))
        (restrictCylinder r a (tableCylinder.{u,v} n y))
        ((tableCylinder_matching hx hy h).restrict hkr a)).map (verticalTable (topTable r))).row (r+1) b =
        ((restrictCylinder r a (tableCylinder.{u,v} n x)).map (verticalTable (topTable r))).row (r+1) b +
        ((restrictCylinder r a (tableCylinder.{u,v} n y)).map (verticalTable (topTable r))).row (r+1) b at hw
      rw [hw,tableCylinder_restrict _ _ hx,tableCylinder_restrict _ _ hy,tableCylinder_restrict _ _ hz,
        tableCylinder_vertical,tableCylinder_vertical,tableCylinder_vertical]
      have hfix (z : Table M) : truncate r false (truncate r a z) = truncate r a z := by
        simp only [truncate_truncate,lt_self_iff_false,ite_false]
      rw [hfix,hfix,hfix,vertical_top_row _ (hfix x),vertical_top_row _ (hfix y),
        vertical_top_row _ (hfix (DirectedComplex.Table.comp k x y h))]
      simp only [truncate_row,lt_self_iff_false,ite_false,ite_true,comp_row,
        show ¬r < k by omega, show r ≠ k by omega, Prod.mk_add_mk, zero_add]
end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

variable {M N : DirectedComplex.{u}}

def tableCell (x : Table M) : Cell M.cylinder.nu :=
  ofMap (tableCylinder (M.nu.finite_dimension x).choose x)

lemma tableCell_of_bounded (n : ℕ) (x : Table M) (hx : truncate n false x = x) :
    tableCell x = ofMap (tableCylinder n x) := by
  apply Subtype.ext
  funext j
  change restrictCylinder j false (tableCylinder (M.nu.finite_dimension x).choose x) =
    restrictCylinder j false (tableCylinder n x)
  rw [tableCylinder_restrict _ _ (M.nu.finite_dimension x).choose_spec,
    tableCylinder_restrict _ _ hx]

lemma tableCell_face (i : ℕ) (b : Bool) (x : Table M) :
    tableCell (truncate i b x) = face i b (tableCell x) := by
  obtain ⟨n,hn⟩ := M.nu.finite_dimension x
  rw [tableCell_of_bounded n x hn,face_ofMap,tableCylinder_restrict n x hn,
    tableCell_of_bounded i (truncate i b x) (by simp only [truncate_truncate,lt_self_iff_false,ite_false])]

lemma tableCell_comp (k : ℕ) (x y : Table M) (h : truncate k true x = truncate k false y)
    (h' : face k true (tableCell x) = face k false (tableCell y)) :
    tableCell (DirectedComplex.Table.comp k x y h) = comp k (tableCell x) (tableCell y) h' := by
  obtain ⟨n₁,h₁⟩ := M.nu.finite_dimension x
  obtain ⟨n₂,h₂⟩ := M.nu.finite_dimension y
  let n := max (k+1) (max n₁ n₂)
  have hk : k < n := by omega
  have hx : truncate n false x = x := M.nu.source_fixed_upwards (by omega) h₁
  have hy : truncate n false y = y := M.nu.source_fixed_upwards (by omega) h₂
  clear_value n
  simp only [tableCell_of_bounded n x hx,tableCell_of_bounded n y hy] at h' ⊢
  rw [comp_ofMap hk]
  rw [tableCell_of_bounded n _ (table_comp_bounded hk x y hx hy h)]
  exact congrArg ofMap (tableCylinder_comp hk x y hx hy h).symm

def chainDiagram (M : DirectedComplex.{u}) : M.nu ⟶ omegaCategory M.cylinder.nu where
  map := tableCell
  map_source k x := tableCell_face k false x
  map_target k x := tableCell_face k true x
  map_comp k x y h h' := tableCell_comp k x y h h'

lemma tableCylinder_map (a : Hom M N) (n : ℕ) (x : Table M) :
    OmegaCategory.Functor.comp (tableCylinder n x) a.cylinder.nu = tableCylinder n (a.nu.map x) := by
  have he : Hom.comp (tableMap n x) a = tableMap n (a.nu.map x) := by
    apply GlobeComplex.hom_ext
    change a.nu.map ((tableMap n x).nu.map (topTable n)) = _
    erw [tableMap_nu_top,tableMap_nu_top]
    exact a.nu.map_source n x
  change (Hom.comp (tableMap n x).cylinder a.cylinder).nu = _
  rw [← Hom.cylinder_comp,he]
  rfl

def chainComparison (M : DirectedComplex.{u}) : tensorFunctor.obj M.nu ⟶ M.cylinder.nu :=
  uncurry (chainDiagram M)

lemma chainComparison_generator (M : DirectedComplex.{u}) (n : ℕ) (x : M.nu.Cells n) (z : (K.{u} n).nu.Cell) :
    (chainComparison M).map ((tensorPresentation M.nu).generator ⟨n,x,z⟩) = (tableCylinder n x.val).map z := by
  change (eval n (tableCell x.val)).map z = _
  rw [tableCell_of_bounded n x.val x.property,eval_ofMap_self]

lemma chainComparison_natural (a : Hom M N) :
    tensorFunctor.map a.nu ≫ chainComparison N = chainComparison M ≫ a.cylinder.nu := by
  apply (tensorPresentation M.nu).functor_ext
  intro ⟨n,x,z⟩
  change (chainComparison N).map ((tensorFunctor.map a.nu).map ((tensorPresentation M.nu).generator ⟨n,x,z⟩)) =
    a.cylinder.nu.map ((chainComparison M).map ((tensorPresentation M.nu).generator ⟨n,x,z⟩))
  erw [tensorFunctor_map_generator,chainComparison_generator,chainComparison_generator]
  exact congrArg (fun P => P.map z) (tableCylinder_map a n x.val).symm

lemma chainComparison_endpoint (M : DirectedComplex.{u}) (b : Bool) :
    (tensorEndpoint b).app M.nu ≫ chainComparison M = (M.cylinderEndpoint b).nu := by
  apply OmegaCategory.Functor.ext
  funext x
  obtain ⟨n,hn⟩ := M.nu.finite_dimension x
  change (chainComparison M).map (((tensorEndpoint b).app M.nu).map x) = _
  erw [tensorEndpoint_bounded b M.nu n ⟨x,hn⟩,chainComparison_generator,
    tableCylinder_endpoint_top]
  exact congrArg (M.cylinderEndpoint b).nu.map hn

lemma chainComparison_projection (M : DirectedComplex.{u}) :
    chainComparison M ≫ M.cylinderProjection.nu = tensorProjection.app M.nu := by
  apply (tensorPresentation M.nu).functor_ext
  intro ⟨n,x,z⟩
  change M.cylinderProjection.nu.map ((chainComparison M).map ((tensorPresentation M.nu).generator ⟨n,x,z⟩)) = _
  rw [chainComparison_generator,tensorProjection_generator]
  have he := congrArg (fun a => a.nu.map z) (Hom.cylinder_projection (tableMap n x.val))
  change M.cylinderProjection.nu.map ((tableCylinder n x.val).map z) = (tableMap n x.val).nu.map (project z) at he
  rw [he,tableMap_nu x.val x.property]

end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

def intervalExtensionOfSimplexIsIso
    (h : ∀ (P : Type u) [LinearOrder P] [Finite P],
      IsIso (chainComparison (NormalizedChains.complex P))) : RightIntervalExtension.{u} where
  tensor := tensorFunctor
  endpoint := tensorEndpoint
  projection := tensorProjection
  endpoint_projection := tensorEndpoint_projection
  cocontinuous := tensorFunctor_preservesColimits
  rightAdjoint := tensorFunctor_isLeftAdjoint
  simplex P _ _ := by
    letI := h P
    exact asIso (chainComparison (NormalizedChains.complex P))
  simplex_natural _ _ _ _ _ _ a := chainComparison_natural a
  simplex_endpoint P _ _ b := chainComparison_endpoint (NormalizedChains.complex P) b
  simplex_projection P _ _ := chainComparison_projection (NormalizedChains.complex P)
  globe := globeTensorIso
  globe_natural := globeTensorIso_natural
  globe_endpoint := globeTensorIso_endpoint
  globe_projection := globeTensorIso_projection

end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex

instance chainComparison_empty_isIso (P : Type u) [PartialOrder P] [IsEmpty P] :
    IsIso (chainComparison (NormalizedChains.complex P)) := by
  have : IsEmpty (NormalizedChains.complex P).nu.Cell :=
    ⟨fun x => isEmptyElim (NormalizedChains.PosetTables.tableStart x)⟩
  have : IsEmpty (NormalizedChains.complex P).cylinder.nu.Cell :=
    ⟨fun x => isEmptyElim ((NormalizedChains.complex P).cylinderProjection.nu.map x)⟩
  exact Limits.isIso_of_isInitial
    ((emptyOmegaIsInitial (NormalizedChains.complex P).nu).isInitialObj tensorFunctor _)
    (emptyOmegaIsInitial (NormalizedChains.complex P).cylinder.nu) _

end Thomason.GrayRecursive.IntervalHom

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


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

variable {X Y : OmegaCategory.{u}}

def tensorParameter (X : OmegaCategory.{u}) : tensorFunctor.obj X ⟶ (K.{u} 0).nu :=
  tensorFunctor.map (constantAt X (topTable 0) (topTable_bounded 0)) ≫ (globeTensorIso 0).hom

def tensorLabel (t : (tensorFunctor.obj X).Cell) (b : Bool) : ℤ :=
  intervalLabel ((tensorParameter X).map t) b

end Thomason.GrayRecursive.IntervalHom

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


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

variable {X Y : OmegaCategory.{u}} {M : DirectedComplex.{u}}

def verticalObject (c : X.Objects) : (tensorFunctor.obj X).Cell :=
  (generatorCylinder 0 c).map (verticalTable (topTable 0))

lemma composite_bounded (C : OmegaCategory.{u}) {n k : ℕ} (hkn : k < n)
    (x y : C.Cell) (hx : C.source n x = x) (hy : C.source n y = y)
    (h : C.target k x = C.source k y) : C.source n (C.join k x y) = C.join k x y := by
  rw [C.join_source_gt n k x y hkn h,hx,hy]

def crossingEdge (l : X.Cell) (c : X.Objects) (r : X.Cell) : (tensorFunctor.obj X).Cell :=
  (tensorFunctor.obj X).join 0
    ((tensorFunctor.obj X).join 0 (((tensorEndpoint false).app X).map l) (verticalObject c))
    (((tensorEndpoint true).app X).map r)

def crossingEdgeLift (t : Table M.cylinder) (hs : CylinderTables.label t false = 0)
    (ht : CylinderTables.label t true = 1) (hb : truncate 1 false t = t) :
    (tensorFunctor.obj M.nu).Cell :=
  crossingEdge (CylinderTables.leftProfile t hs ht)
    ⟨CylinderTables.crossingProfile t hs ht, CylinderTables.crossingProfile_bounded t hs ht hb⟩
    (CylinderTables.rightProfile t hs ht)

end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {X Y : OmegaCategory.{u}}

inductive EdgeNormal (X : OmegaCategory.{u}) : (tensorFunctor.obj X).Cell → Prop
  | endpoint (a : Bool) (x : X.Cell) (hx : X.source 1 x = x) :
      EdgeNormal X (((tensorEndpoint a).app X).map x)
  | crossing (l : X.Cell) (c : X.Objects) (r : X.Cell)
      (hl : X.target 0 l = c.val) (hr : X.source 0 r = c.val)
      (hdl : X.source 1 l = l) (hdr : X.source 1 r = r) :
      EdgeNormal X (crossingEdge l c r)

end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {X : OmegaCategory.{u}}

lemma endpoint_source (a : Bool) (k : ℕ) (x : X.Cell) :
    (tensorFunctor.obj X).source k (((tensorEndpoint a).app X).map x) =
      ((tensorEndpoint a).app X).map (X.source k x) := (((tensorEndpoint a).app X).map_source k x).symm

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


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table OmegaCategory
open CylinderTables
variable {M : DirectedComplex.{u}}

def TwoLiftable (t : Table M.cylinder) : Prop :=
  ∃ x : (tensorFunctor.obj M.nu).Cell,
    (tensorFunctor.obj M.nu).source 2 x = x ∧ (chainComparison M).map x = t

end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

variable {X Y : OmegaCategory.{u}} {M : DirectedComplex.{u}}

def verticalCell (n : ℕ) (x : X.Cells n) : (tensorFunctor.obj X).Cell :=
  (generatorCylinder n x).map (verticalTable (topTable n))

lemma verticalCell_bounded (n : ℕ) (x : X.Cells n) :
    (tensorFunctor.obj X).source (n+1) (verticalCell n x) = verticalCell n x := by
  unfold verticalCell
  erw [← (generatorCylinder n x).map_source]
  change (generatorCylinder n x).map (truncate (n+1) false (verticalTable (topTable n))) = _
  rw [vertical_fixed _ (topTable_bounded n)]

lemma tensorUnitCell_face (k : ℕ) (a : Bool) (x : X.Cell) :
    tensorUnitCell (X.face k a x) = face k a (tensorUnitCell x) := by
  cases a
  · exact tensorUnitCell_source k x
  · exact tensorUnitCell_target k x

lemma generatorCylinder_matching {n k : ℕ} (x y : X.Cells n)
    (h : X.target k x.val = X.source k y.val) :
    FaceMatching k (generatorCylinder n x) (generatorCylinder n y) := by
  apply face_matching
  rw [← tensorUnitCell_of_bounded n x, ← tensorUnitCell_of_bounded n y,
    ← tensorUnitCell_face k true, ← tensorUnitCell_face k false]
  exact congrArg tensorUnitCell h

end Thomason.GrayRecursive.IntervalHom

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_TwoCellExchange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two Cell Exchange. -/

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

variable {X : OmegaCategory.{u}}

structure CrossingSquare (X : OmegaCategory.{u}) where
  left : X.Cells 1
  cross : X.Cells 1
  right : X.Cells 1
  left₂ : X.Cells 2
  right₂ : X.Cells 2
  lc : X.target 0 left.val = X.source 0 cross.val
  cr : X.target 0 cross.val = X.source 0 right.val
  left_source : X.source 1 left₂.val = X.join 0 left.val cross.val
  right_target : X.target 1 right₂.val = X.join 0 cross.val right.val

namespace CrossingSquare
variable (D : CrossingSquare X)

abbrev entry : X.Objects := ⟨X.source 0 D.cross.val, X.source_source_self 0 D.cross.val⟩
abbrev exit : X.Objects := ⟨X.target 0 D.cross.val, X.source_target_self 0 D.cross.val⟩

lemma left₂_source_zero : X.source 0 D.left₂.val = X.source 0 D.left.val := by
  have h := congrArg (X.source 0) D.left_source
  rw [X.source_source, min_eq_left (by omega : 0 ≤ 1),
    X.join_source_le 0 0 _ _ le_rfl D.lc] at h
  exact h

lemma left₂_target_zero : X.target 0 D.left₂.val = D.exit.val := by
  have h := congrArg (X.target 0) D.left_source
  rw [X.target_source, ite_eq_left (by omega : 0 < 1),
    X.join_target_le 0 0 _ _ le_rfl D.lc] at h
  exact h

lemma right₂_source_zero : X.source 0 D.right₂.val = D.entry.val := by
  have h := congrArg (X.source 0) D.right_target
  rw [X.source_target, ite_eq_left (by omega : 0 < 1),
    X.join_source_le 0 0 _ _ le_rfl D.cr] at h
  exact h

lemma right₂_target_zero : X.target 0 D.right₂.val = X.target 0 D.right.val := by
  have h := congrArg (X.target 0) D.right_target
  rw [X.target_target, min_eq_left (by omega : 0 ≤ 1),
    X.join_target_le 0 0 _ _ le_rfl D.cr] at h
  exact h

def middle : (tensorFunctor.obj X).Cell :=
  (tensorFunctor.obj X).join 0
    ((tensorFunctor.obj X).join 0 (((tensorEndpoint false).app X).map D.left.val)
      (verticalCell 1 D.cross)) (((tensorEndpoint true).app X).map D.right.val)

def first : (tensorFunctor.obj X).Cell := crossingEdge D.left.val D.entry D.right₂.val

def last : (tensorFunctor.obj X).Cell := crossingEdge D.left₂.val D.exit D.right.val

def value : (tensorFunctor.obj X).Cell :=
  (tensorFunctor.obj X).join 1 ((tensorFunctor.obj X).join 1 D.first D.middle) D.last

end CrossingSquare
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
open CylinderTables

variable {M : DirectedComplex.{u}}
namespace CrossingSquare

def ofTable (hM : PositiveAcyclic M) (t : M.cylinder.nu.Cells 2)
    (hs : label t.val false = 0) (ht : label t.val true = 1) : CrossingSquare M.nu where
  left := ⟨profileEdge t.val hs ht false false, profileEdge_bounded _ _ _ _ _⟩
  cross := ⟨crossingProfile t.val hs ht, crossingProfile_bounded _ _ _ t.property⟩
  right := ⟨profileEdge t.val hs ht true true, profileEdge_bounded _ _ _ _ _⟩
  left₂ := ⟨leftProfile t.val hs ht, leftProfile_bounded _ _ _ t.property⟩
  right₂ := ⟨rightProfile t.val hs ht, rightProfile_bounded _ _ _ t.property⟩
  lc := truncate_zero_ext _ _ _ _ (twoMiddle_matches hM t.val hs ht).1
  cr := (truncate_zero_ext _ _ _ _ (twoMiddle_matches hM t.val hs ht).2).symm
  left_source := by
    apply ext_source_top (M.nu.source_source_self 1 _) (composite_bounded M.nu (by omega : 0 < 1)
      _ _ (profileEdge_bounded _ _ _ _ _) (crossingProfile_bounded _ _ _ t.property)
      (truncate_zero_ext _ _ _ _ (twoMiddle_matches hM t.val hs ht).1))
    · change truncate 0 false (truncate 1 false _) = M.nu.source 0 (M.nu.join 0 _ _)
      rw [M.nu.join_source_le 0 0 _ _ le_rfl
        (truncate_zero_ext _ _ _ _ (twoMiddle_matches hM t.val hs ht).1)]
      apply truncate_zero_ext
      change (leftProfile t.val hs ht).row 0 false = (profileEdge t.val hs ht false false).row 0 false
      erw [profile_left_zero hM]
    · erw [table_join_zero_row_succ _ _
        (truncate_zero_ext _ _ _ _ (twoMiddle_matches hM t.val hs ht).1),
        profileEdge_one]
      change side t.val false 1 false + CylinderTables.cross t.val 1 false =
        side t.val false 1 false + CylinderTables.cross t.val 1 false
      rfl
  right_target := by
    apply ext_source_top (M.nu.source_target_self 1 _) (composite_bounded M.nu (by omega : 0 < 1)
      _ _ (crossingProfile_bounded _ _ _ t.property) (profileEdge_bounded _ _ _ _ _)
      (truncate_zero_ext _ _ _ _ (twoMiddle_matches hM t.val hs ht).2).symm)
    · change truncate 0 false (truncate 1 true _) = M.nu.source 0 (M.nu.join 0 _ _)
      rw [M.nu.join_source_le 0 0 _ _ le_rfl
        (truncate_zero_ext _ _ _ _ (twoMiddle_matches hM t.val hs ht).2).symm]
      apply truncate_zero_ext
      change (rightProfile t.val hs ht).row 0 false = (crossingProfile t.val hs ht).row 0 false
      erw [profile_right_zero hM]
      simp only [Bool.false_eq_true, ite_false]
      rfl
    · erw [table_join_zero_row_succ _ _
        (truncate_zero_ext _ _ _ _ (twoMiddle_matches hM t.val hs ht).2).symm,
        profileEdge_one]
      change side t.val true 1 true + CylinderTables.cross t.val 1 true =
        CylinderTables.cross t.val 1 false + side t.val true 1 true
      have hc : CylinderTables.cross t.val 1 false = CylinderTables.cross t.val 1 true :=
        row_top_fixed _ (crossingProfile_bounded t.val hs ht t.property)
      rw [hc]
      exact add_comm _ _

end CrossingSquare
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

variable {X : OmegaCategory.{u}}

def whiskeredVertical (l : X.Cell) (c : X.Cells 1) (r : X.Cell) : (tensorFunctor.obj X).Cell :=
  (tensorFunctor.obj X).join 0
    ((tensorFunctor.obj X).join 0 (((tensorEndpoint false).app X).map l) (verticalCell 1 c))
    (((tensorEndpoint true).app X).map r)

end Thomason.GrayRecursive.IntervalHom

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_TwoCellComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two Cell Comparison. -/

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {X : OmegaCategory.{u}}
namespace CrossingSquare

variable (D E : CrossingSquare X)
variable (hl : X.target 1 D.left₂.val = E.left.val)
variable (hc : D.exit.val = E.entry.val)
variable (hr : D.right.val = X.source 1 E.right₂.val)

include hc in
lemma comp_left_match : X.target 0 D.left₂.val = X.source 0 E.cross.val :=
  D.left₂_target_zero.trans hc

include hc in
lemma comp_right_match : X.target 0 D.cross.val = X.source 0 E.right₂.val :=
  hc.trans E.right₂_source_zero.symm

include hl hc in
lemma comp_left₂_match :
    X.target 1 (X.join 0 D.left₂.val E.cross.val) = X.source 1 E.left₂.val := by
  rw [X.join_target_gt 1 0 _ _ (by omega) (D.comp_left_match E hc),
    hl, X.target_eq_self_of_source_eq_self E.cross.property, E.left_source]

include hc hr in
lemma comp_right₂_match :
    X.target 1 D.right₂.val = X.source 1 (X.join 0 D.cross.val E.right₂.val) := by
  rw [X.join_source_gt 1 0 _ _ (by omega) (D.comp_right_match E hc),
    D.cross.property, D.right_target, hr]

include hc in
lemma comp_lc : X.target 0 D.left.val = X.source 0 (X.join 0 D.cross.val E.cross.val) := by
  rw [X.join_source_le 0 0 _ _ le_rfl hc]; exact D.lc

include hc in
lemma comp_cr : X.target 0 (X.join 0 D.cross.val E.cross.val) = X.source 0 E.right.val := by
  rw [X.join_target_le 0 0 _ _ le_rfl hc]; exact E.cr

def comp : CrossingSquare X where
  left := D.left
  cross := ⟨X.join 0 D.cross.val E.cross.val,
    composite_bounded X (by omega : 0 < 1) _ _ D.cross.property E.cross.property hc⟩
  right := E.right
  left₂ := ⟨X.join 1 (X.join 0 D.left₂.val E.cross.val) E.left₂.val,
    composite_bounded X (by omega : 1 < 2) _ _
      (composite_bounded X (by omega : 0 < 2) _ _ D.left₂.property
        (X.source_fixed_upwards (by omega : 1 ≤ 2) E.cross.property) (D.comp_left_match E hc))
      E.left₂.property (D.comp_left₂_match E hl hc)⟩
  right₂ := ⟨X.join 1 D.right₂.val (X.join 0 D.cross.val E.right₂.val),
    composite_bounded X (by omega : 1 < 2) _ _ D.right₂.property
      (composite_bounded X (by omega : 0 < 2) _ _
        (X.source_fixed_upwards (by omega : 1 ≤ 2) D.cross.property) E.right₂.property
          (D.comp_right_match E hc))
      (D.comp_right₂_match E hc hr)⟩
  lc := D.comp_lc E hc
  cr := D.comp_cr E hc
  left_source := by
    rw [X.join_source_le 1 1 _ _ le_rfl (D.comp_left₂_match E hl hc),
      X.join_source_gt 1 0 _ _ (by omega) (D.comp_left_match E hc),
      D.left_source, E.cross.property, X.join_assoc 0 _ _ _ D.lc hc]
  right_target := by
    rw [X.join_target_le 1 1 _ _ le_rfl (D.comp_right₂_match E hc hr),
      X.join_target_gt 1 0 _ _ (by omega) (D.comp_right_match E hc),
      X.target_eq_self_of_source_eq_self D.cross.property, E.right_target,
      X.join_assoc 0 _ _ _ hc E.cr]

end CrossingSquare
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {X : OmegaCategory.{u}}

namespace CrossingSquare
variable (D : CrossingSquare X)

variable (a : X.Cells 2) (h : X.target 0 a.val = X.source 0 D.left.val)

include h in
lemma whisker_left_match : X.target 0 a.val = X.source 0 D.left₂.val :=
  h.trans D.left₂_source_zero.symm

include h in
lemma whisker_left_source_match : X.target 0 (X.source 1 a.val) = X.source 0 D.left.val := by
  rw [X.target_source, ite_eq_left (by omega : 0 < 1)]; exact h

def whiskerLeft : CrossingSquare X where
  left := ⟨X.join 0 (X.source 1 a.val) D.left.val,
    composite_bounded X (by omega : 0 < 1) _ _ (X.source_source_self 1 a.val) D.left.property
      (D.whisker_left_source_match a h)⟩
  cross := D.cross
  right := D.right
  left₂ := ⟨X.join 0 a.val D.left₂.val,
    composite_bounded X (by omega : 0 < 2) _ _ a.property D.left₂.property
      (D.whisker_left_match a h)⟩
  right₂ := D.right₂
  lc := by
    rw [X.join_target_le 0 0 _ _ le_rfl (D.whisker_left_source_match a h)]
    exact D.lc
  cr := D.cr
  left_source := by
    rw [X.join_source_gt 1 0 _ _ (by omega) (D.whisker_left_match a h),
      D.left_source, X.join_assoc 0 _ _ _ (D.whisker_left_source_match a h) D.lc]
  right_target := D.right_target

variable (hr : X.target 0 D.right.val = X.source 0 a.val)

include hr in
lemma whisker_right_match : X.target 0 D.right₂.val = X.source 0 a.val :=
  D.right₂_target_zero.trans hr

include hr in
lemma whisker_right_target_match : X.target 0 D.right.val = X.source 0 (X.target 1 a.val) := by
  rw [X.source_target, ite_eq_left (by omega : 0 < 1)]; exact hr

def whiskerRight : CrossingSquare X where
  left := D.left
  cross := D.cross
  right := ⟨X.join 0 D.right.val (X.target 1 a.val),
    composite_bounded X (by omega : 0 < 1) _ _ D.right.property (X.source_target_self 1 a.val)
      (D.whisker_right_target_match a hr)⟩
  left₂ := D.left₂
  right₂ := ⟨X.join 0 D.right₂.val a.val,
    composite_bounded X (by omega : 0 < 2) _ _ D.right₂.property a.property
      (D.whisker_right_match a hr)⟩
  lc := D.lc
  cr := by
    rw [X.join_source_le 0 0 _ _ le_rfl (D.whisker_right_target_match a hr)]
    exact D.cr
  left_source := D.left_source
  right_target := by
    rw [X.join_target_gt 1 0 _ _ (by omega) (D.whisker_right_match a hr),
      D.right_target, X.join_assoc 0 _ _ _ D.cr (D.whisker_right_target_match a hr)]

end CrossingSquare
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {X Y : OmegaCategory.{u}}

namespace CrossingSquare

def map (D : CrossingSquare X) (F : X ⟶ Y) : CrossingSquare Y where
  left := F.onCells 1 D.left
  cross := F.onCells 1 D.cross
  right := F.onCells 1 D.right
  left₂ := F.onCells 2 D.left₂
  right₂ := F.onCells 2 D.right₂
  lc := by change Y.target 0 (F.map _) = Y.source 0 (F.map _)
           rw [← F.map_target, ← F.map_source, D.lc]
  cr := by change Y.target 0 (F.map _) = Y.source 0 (F.map _)
           rw [← F.map_target, ← F.map_source, D.cr]
  left_source := by
    change Y.source 1 (F.map D.left₂.val) = Y.join 0 (F.map D.left.val) (F.map D.cross.val)
    rw [← F.map_source, D.left_source, F.map_join 0 _ _ D.lc]
  right_target := by
    change Y.target 1 (F.map D.right₂.val) = Y.join 0 (F.map D.cross.val) (F.map D.right.val)
    rw [← F.map_target, D.right_target, F.map_join 0 _ _ D.cr]

end CrossingSquare

inductive SquareNormal (X : OmegaCategory.{u}) : (tensorFunctor.obj X).Cell → Prop
  | endpoint (a : Bool) (x : X.Cell) (hx : X.source 2 x = x) :
      SquareNormal X (((tensorEndpoint a).app X).map x)
  | crossing (D : CrossingSquare X) : SquareNormal X D.value

end Thomason.GrayRecursive.IntervalHom

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_PrismBasis
attribute [-instance] _root_.OAI.Thomason.NormalizedChains.Prism.Basis.finite _root_.OAI.Thomason.NormalizedChains.Prism.Word.finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prism Basis. -/

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains.Prism
open DirectedComplex DirectedComplex.Table

namespace Word
variable {N : ℕ}

def atom (w : Word N) : Table (complex (Fin (N+1))) := by
  obtain ⟨⟨l,h⟩,hne⟩ := w
  cases l with
  | nil => exact False.elim (hne rfl)
  | cons a l => exact (simplexAtom a l (h.imp le_of_lt)).table

lemma atom_dim (w : Word N) : truncate w.dim false w.atom = w.atom := by
  obtain ⟨⟨l,h⟩,hne⟩ := w
  cases l with
  | nil => exact False.elim (hne rfl)
  | cons a l => exact (simplexAtom a l (h.imp le_of_lt)).dimension

lemma atom_top (w : Word N) (b : Bool) :
    (w.atom.row w.dim b).val = Finsupp.single w.val 1 := by
  obtain ⟨⟨l,h⟩,hne⟩ := w
  cases l with
  | nil => exact False.elim (hne rfl)
  | cons a l =>
    exact ((simplexAtom a l (h.imp le_of_lt)).top b).trans (bracket_of_pairwise h)

lemma atom_rank (w : Word N) (p : ℕ) (hp : p < w.dim) (b : Bool)
    (v : Word N) (hv : (w.atom.row p b).val v.val ≠ 0) :
    if b then v.rank < w.rank else w.rank < v.rank := by
  obtain ⟨⟨l,h⟩,hne⟩ := w
  cases l with
  | nil => exact False.elim (hne rfl)
  | cons a l => exact simplexAtom_rank a l h p hp b v.val hv

lemma atom_top_support (w v : Word N) (b : Bool)
    (h : (w.atom.row w.dim b).val v.val ≠ 0) : v = w := by
  rw [w.atom_top b] at h
  by_contra he
  have hne : w.val ≠ v.val := fun e => he (Subtype.ext e.symm)
  exact h (Finsupp.single_eq_of_ne (Ne.symm hne))

end Word

namespace Basis
variable {N : ℕ}

def atom : Basis N → Table (complex (Fin (N+1))).cylinder
  | .endpoint a w => ((complex (Fin (N+1))).cylinderEndpoint a).table w.atom
  | .vertical w => verticalTable w.atom

def coefficient (b : Basis N) (p : ℕ) :
    (complex (Fin (N+1))).cylinder.Chain p →+ ℤ where
  toFun x := match b, p, x with
    | .endpoint a w, 0, x => if a then x.2.val w.val else x.1.val w.val
    | .endpoint a w, _+1, x => if a then x.2.1.val w.val else x.1.val w.val
    | .vertical _, 0, _ => 0
    | .vertical w, _+1, x => x.2.2.val w.val
  map_zero' := by cases b <;> cases p <;> simp <;> rfl
  map_add' x y := by
    cases b with
    | endpoint a w => cases p <;> cases a <;> rfl
    | vertical w => cases p <;> rfl

lemma coefficient_nonneg (b : Basis N) (p : ℕ)
    (x : (complex (Fin (N+1))).cylinder.Chain p)
    (hx : x ∈ (complex (Fin (N+1))).cylinder.positive p) :
    0 ≤ b.coefficient p x := by
  cases b with
  | endpoint a w =>
    cases p with
    | zero => cases a; exact hx.1 w.val; exact hx.2 w.val
    | succ p => cases a; exact hx.1 w.val; exact hx.2.1 w.val
  | vertical w =>
    cases p with
    | zero => exact le_rfl
    | succ p => exact hx.2.2 w.val

lemma coefficient_endpoint (b : Basis N) (p : ℕ) (a : Bool)
    (x : (complex (Fin (N+1))).Chain p) :
    b.coefficient p (((complex (Fin (N+1))).cylinderEndpoint a).map p x) =
      match b with
      | .endpoint a' w => if a = a' then x.val w.val else 0
      | .vertical _ => 0 := by
  cases b with
  | endpoint a' w => cases p <;> cases a <;> cases a' <;> rfl
  | vertical w => cases p <;> cases a <;> rfl

lemma atom_bounded (b : Basis N) : truncate b.dim false b.atom = b.atom := by
  cases b with
  | endpoint a w =>
    change truncate w.dim false (((complex (Fin (N+1))).cylinderEndpoint a).table w.atom) = _
    rw [← Hom.table_truncate,w.atom_dim]
    rfl
  | vertical w => exact GrayRecursive.vertical_fixed _ w.atom_dim

lemma coefficient_vertical_endpoint (p : ℕ) (a b : Bool) (w : Word N)
    (x : Table (complex (Fin (N+1)))) :
    (endpoint a w).coefficient p ((verticalTable x).row p b) =
      if a = boundarySide p b then (x.row p b).val w.val else 0 := by
  cases p with
  | zero => cases a <;> cases b <;> rfl
  | succ p =>
    by_cases hp : Even (p+1) <;> cases a <;> cases b <;>
      simp [coefficient,verticalTable,verticalRow,boundarySide,hp] <;> rfl

lemma coefficient_vertical_vertical (p : ℕ) (b : Bool) (w : Word N)
    (x : Table (complex (Fin (N+1)))) :
    (vertical w).coefficient (p+1) ((verticalTable x).row (p+1) b) =
      (x.row p b).val w.val := by
  by_cases hp : Even (p+1) <;> cases b <;>
    simp [coefficient,verticalTable,verticalRow,hp]

attribute [local instance] OAI.Thomason.NormalizedChains.Prism.Basis.instDecidableEq
lemma atom_top_coefficient (b c : Basis N) (e : Bool) :
    c.coefficient b.dim (b.atom.row b.dim e) = if b = c then 1 else 0 := by
  classical
  cases b with
  | endpoint a w =>
    change c.coefficient w.dim ((((complex (Fin (N+1))).cylinderEndpoint a).table w.atom).row w.dim e) = _
    rw [Hom.table_row,coefficient_endpoint]
    cases c with
    | endpoint a' v =>
      rw [w.atom_top e]
      by_cases ha : a = a'
      · subst a'
        by_cases hw : w = v
        · subst v; simp
        · have hv : w.val ≠ v.val := fun h => hw (Subtype.ext h)
          simp [hw,Ne.symm hv]
      · simp [ha]
    | vertical v => simp
  | vertical w =>
    change c.coefficient (w.dim+1) ((verticalTable w.atom).row (w.dim+1) e) = _
    cases c with
    | endpoint a v =>
      rw [coefficient_vertical_endpoint, row_above_fixed w.atom w.atom_dim (by omega : w.dim < w.dim+1)]
      simp
      intro _
      rfl
    | vertical v =>
      rw [coefficient_vertical_vertical,w.atom_top e]
      by_cases hw : w = v
      · subst v; simp
      · have hv : w.val ≠ v.val := fun h => hw (Subtype.ext h)
        simp [hw,Ne.symm hv]

theorem atom_rank (b : Basis N) (p : ℕ) (hp : p < b.dim) (e : Bool)
    (c : Basis N) (hc : c.coefficient p (b.atom.row p e) ≠ 0) :
    if e then c.rank < b.rank else b.rank < c.rank := by
  cases b with
  | endpoint a w =>
    change c.coefficient p ((((complex (Fin (N+1))).cylinderEndpoint a).table w.atom).row p e) ≠ 0 at hc
    rw [Hom.table_row,coefficient_endpoint] at hc
    cases c with
    | vertical v => exact False.elim (hc rfl)
    | endpoint a' v =>
      change (if a = a' then (w.atom.row p e).val v.val else 0) ≠ 0 at hc
      by_cases ha : a = a'
      · subst a'
        rw [ite_eq_left rfl] at hc
        have hr := w.atom_rank p hp e v hc
        have hw := endpointOffset_bounds w.dim a
        have hv := endpointOffset_bounds v.dim a
        cases e <;> simp only [Bool.false_eq_true,ite_false,ite_true,rank] at hr ⊢ <;> omega
      · exact False.elim (hc (ite_eq_right ha))
  | vertical w =>
    cases c with
    | endpoint a v =>
      change (endpoint a v).coefficient p ((verticalTable w.atom).row p e) ≠ 0 at hc
      rw [coefficient_vertical_endpoint] at hc
      by_cases ha : a = boundarySide p e
      · rw [ite_eq_left ha] at hc
        by_cases hlt : p < w.dim
        · have hr := w.atom_rank p hlt e v hc
          have hv := endpointOffset_bounds v.dim a
          cases e <;> simp only [Bool.false_eq_true,ite_false,ite_true,rank] at hr ⊢ <;> omega
        · have he : p = w.dim := by change p < w.dim+1 at hp; omega
          subst p
          have he := w.atom_top_support v e hc
          subst v
          rw [ha]
          simp only [rank,endpointOffset_boundarySide]
          cases e <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
      · exact False.elim (hc (ite_eq_right ha))
    | vertical v =>
      cases p with
      | zero => exact False.elim (hc rfl)
      | succ p =>
        change (vertical v).coefficient (p+1) ((verticalTable w.atom).row (p+1) e) ≠ 0 at hc
        rw [coefficient_vertical_vertical] at hc
        have hlt : p < w.dim := by change p+1 < w.dim+1 at hp; omega
        have hr := w.atom_rank p hlt e v hc
        cases e <;> simp only [Bool.false_eq_true,ite_false,ite_true,rank] at hr ⊢ <;> omega

end Basis
end Thomason.NormalizedChains.Prism

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

attribute [instance] RankedAtoms.finite
end Thomason.DirectedComplex

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains.Prism
open DirectedComplex DirectedComplex.Table

namespace Word
variable {N p : ℕ}

lemma empty_coefficient (x : (complex (Fin (N+1))).Chain p)
    (w : NormalizedChains.Word (Fin (N+1))) (hw : w.val = []) : x.val w = 0 := by
  by_contra hn
  have h := (mem_grade_iff (p+1) x.val).mp x.property w hn
  simp [hw] at h

lemma chain_ext (x y : (complex (Fin (N+1))).Chain p)
    (h : ∀ w : Word N, x.val w.val = y.val w.val) : x = y := by
  apply Subtype.ext
  apply Finsupp.ext
  intro w
  by_cases hw : w.val = []
  · rw [empty_coefficient x w hw,empty_coefficient y w hw]
  · exact h ⟨w,hw⟩

lemma chain_positive (x : (complex (Fin (N+1))).Chain p) :
    x ∈ (complex (Fin (N+1))).positive p ↔ ∀ w : Word N, 0 ≤ x.val w.val := by
  constructor
  · intro hx w
    exact hx w.val
  · intro hx w
    by_cases hw : w.val = []
    · rw [empty_coefficient x w hw]
    · exact hx ⟨w,hw⟩
end Word

namespace Basis
variable {N : ℕ}

lemma coefficient_homogeneous (b : Basis N) (p : ℕ)
    (x : (complex (Fin (N+1))).cylinder.Chain p) (hx : b.coefficient p x ≠ 0) : b.dim = p := by
  cases b with
  | endpoint a w =>
    cases p with
    | zero =>
      cases a
      · exact Word.dim_eq_of_coefficient x.1 w hx
      · exact Word.dim_eq_of_coefficient x.2 w hx
    | succ p =>
      cases a
      · exact Word.dim_eq_of_coefficient x.1 w hx
      · exact Word.dim_eq_of_coefficient x.2.1 w hx
  | vertical w =>
    cases p with
    | zero => exact False.elim (hx rfl)
    | succ p =>
      have h := Word.dim_eq_of_coefficient x.2.2 w hx
      change w.dim+1 = p+1
      omega

lemma coefficient_ext (p : ℕ) (x y : (complex (Fin (N+1))).cylinder.Chain p)
    (h : ∀ b : Basis N, b.coefficient p x = b.coefficient p y) : x = y := by
  cases p with
  | zero =>
    apply Prod.ext
    · apply Word.chain_ext
      intro w
      exact h (.endpoint false w)
    · apply Word.chain_ext
      intro w
      exact h (.endpoint true w)
  | succ p =>
    apply Prod.ext
    · apply Word.chain_ext
      intro w
      exact h (.endpoint false w)
    · apply Prod.ext
      · apply Word.chain_ext
        intro w
        exact h (.endpoint true w)
      · apply Word.chain_ext
        intro w
        exact h (.vertical w)

lemma positive_iff (p : ℕ) (x : (complex (Fin (N+1))).cylinder.Chain p) :
    x ∈ (complex (Fin (N+1))).cylinder.positive p ↔ ∀ b : Basis N, 0 ≤ b.coefficient p x := by
  constructor
  · exact fun hx b => b.coefficient_nonneg p x hx
  · intro hx
    cases p with
    | zero =>
      exact ⟨(Word.chain_positive x.1).mpr (fun w => hx (.endpoint false w)),
        (Word.chain_positive x.2).mpr (fun w => hx (.endpoint true w))⟩
    | succ p =>
      exact ⟨(Word.chain_positive x.1).mpr (fun w => hx (.endpoint false w)),
        (Word.chain_positive x.2.1).mpr (fun w => hx (.endpoint true w)),
        (Word.chain_positive x.2.2).mpr (fun w => hx (.vertical w))⟩

def rankedAtoms (N : ℕ) : RankedAtoms (complex (Fin (N+1))).cylinder where
  Index := Basis N
  finite := Fintype.ofFinite (Basis N)
  dim := Basis.dim
  rank := Basis.rank
  atom := Basis.atom
  bounded := Basis.atom_bounded
  coefficient := Basis.coefficient
  homogeneous := Basis.coefficient_homogeneous
  ext := Basis.coefficient_ext
  positive := Basis.positive_iff
  top := Basis.atom_top_coefficient
  ranked := Basis.atom_rank

end Basis
end Thomason.NormalizedChains.Prism

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


namespace Thomason.NormalizedChains
open DirectedComplex

namespace Prism.Basis

def ofOrderIso {N : ℕ} {P : Type u} [LinearOrder P] (e : Fin (N+1) ≃o P) :
    RankedAtoms (complex P).cylinder :=
  (rankedAtoms N).transport (complexMap (e : Fin (N+1) →o P)).cylinder
    (complexMap (e.symm : P →o Fin (N+1))).cylinder
    (by rw [← Hom.cylinder_comp,complexMap_orderIso_inverse,Hom.cylinder_id])
    (by rw [← Hom.cylinder_comp, ← Hom.cylinder_id];
        congr 1; exact complexMap_orderIso_inverse e.symm)

end Prism.Basis
end Thomason.NormalizedChains

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
open CategoryTheory

namespace Functor
variable {X : OmegaCategory.{u}} {Y : OmegaCategory.{v}}

def injectiveImage (F : Functor X Y) (hF : Function.Injective F.map) : Subcategory Y where
  carrier := Set.range F.map
  source_mem k := by
    rintro x ⟨a,rfl⟩
    exact ⟨X.source k a,F.map_source k a⟩
  target_mem k := by
    rintro x ⟨a,rfl⟩
    exact ⟨X.target k a,F.map_target k a⟩
  comp_mem k := by
    rintro x y h ⟨a,rfl⟩ ⟨b,rfl⟩
    have hab : X.target k a = X.source k b := hF (by
      rw [F.map_target,F.map_source]; exact h)
    exact ⟨X.comp k a b hab,F.map_comp k a b hab h⟩

end Functor
namespace Subcategory
variable {X : OmegaCategory.{u}} {Y : OmegaCategory.{v}}

def preimage (S : Subcategory Y) (F : Functor X Y) : Subcategory X where
  carrier := F.map ⁻¹' S.carrier
  source_mem k := by
    intro x hx
    change F.map (X.source k x) ∈ S.carrier
    rw [F.map_source]
    exact S.source_mem k hx
  target_mem k := by
    intro x hx
    change F.map (X.target k x) ∈ S.carrier
    rw [F.map_target]
    exact S.target_mem k hx
  comp_mem k := by
    intro x y h hx hy
    change F.map (X.comp k x y h) ∈ S.carrier
    rw [F.map_comp k x y h (F.map_composable h)]
    exact S.comp_mem k _ hx hy

end Subcategory
end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {X Y : OmegaCategory.{u}}

lemma mapCell_injective (F : X ⟶ Y) (hF : Function.Injective F.map) :
    Function.Injective (mapCell F) := by
  intro x y h
  apply Subtype.ext
  funext n
  apply OmegaCategory.Functor.ext
  funext z
  apply hF
  exact congrArg (fun c => (eval n c).map z) h

def cylinderSubcategory (S : Subcategory (tensorFunctor.obj X)) : Subcategory X :=
  (OmegaCategory.Functor.injectiveImage (mapFunctor S.inclusion)
    (mapCell_injective S.inclusion S.inclusion_injective)).preimage (tensorUnit X)

end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains.Prism.Word
open DirectedComplex DirectedComplex.Table

def coefficient {N : ℕ} (w : Word N) (p : ℕ) :
    (complex (Fin (N+1))).Chain p →+ ℤ where
  toFun x := x.val w.val
  map_add' _ _ := rfl
  map_zero' := rfl

def rankedAtoms (N : ℕ) : RankedAtoms (complex (Fin (N+1))) where
  Index := Word N
  finite := Fintype.ofFinite (Word N)
  dim := Word.dim
  rank := Word.rank
  atom := Word.atom
  bounded := Word.atom_dim
  coefficient := Word.coefficient
  homogeneous _ _ _ := Word.dim_eq_of_coefficient _ _
  ext _ := Word.chain_ext
  positive _ := Word.chain_positive
  top b c e := by
    classical
    change (b.atom.row b.dim e).val c.val = _
    rw [b.atom_top e]
    by_cases h : b = c
    · subst c; simp
    · rw [ite_eq_right h,Finsupp.single_eq_of_ne (fun he => h (Subtype.ext he.symm))]
  ranked := Word.atom_rank

def ofOrderIso {N : ℕ} {P : Type u} [LinearOrder P] (e : Fin (N+1) ≃o P) :
    RankedAtoms (complex P) :=
  (rankedAtoms N).transport (complexMap (e : Fin (N+1) →o P))
    (complexMap (e.symm : P →o Fin (N+1)))
    (complexMap_orderIso_inverse e) (complexMap_orderIso_inverse e.symm)
end Thomason.NormalizedChains.Prism.Word

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex Table OmegaCategory GlobeComplex
variable {M : DirectedComplex.{u}} (A : RankedAtoms.{u,v} M)

inductive AtomicLayers (n : ℕ) : (tensorFunctor.obj M.nu).Cell → Prop
  | endpoint (a : Bool) (b : A.Index) (hb : A.dim b ≤ n) :
      AtomicLayers n (((tensorEndpoint a).app M.nu).map (A.atom b))
  | vertical (b : A.Index) (hb : A.dim b < n) :
      AtomicLayers n (verticalCell (A.dim b) ⟨A.atom b,A.bounded b⟩)
  | lower (k : ℕ) (hk : k < n) (z : (tensorFunctor.obj M.nu).Cell)
      (hz : (tensorFunctor.obj M.nu).source k z = z) : AtomicLayers n z
  | compose (k : ℕ) (hk : k < n) (x y)
      (h : (tensorFunctor.obj M.nu).target k x = (tensorFunctor.obj M.nu).source k y) :
      AtomicLayers n x → AtomicLayers n y →
        AtomicLayers n ((tensorFunctor.obj M.nu).comp k x y h)

namespace AtomicLayers
variable {A} {n : ℕ}

lemma bounded {z : (tensorFunctor.obj M.nu).Cell} (h : AtomicLayers A n z) :
    (tensorFunctor.obj M.nu).source n z = z := by
  induction h with
  | endpoint a b hb =>
    erw [endpoint_source]
    exact congrArg ((tensorEndpoint a).app M.nu).map
      (M.nu.source_fixed_upwards hb (A.bounded b))
  | vertical b hb =>
    exact (tensorFunctor.obj M.nu).source_fixed_upwards (by omega : A.dim b+1 ≤ n)
      (verticalCell_bounded _ _)
  | lower k hk z hz => exact (tensorFunctor.obj M.nu).source_fixed_upwards hk.le hz
  | compose k hk x y h hx hy ihx ihy =>
    erw [(tensorFunctor.obj M.nu).source_comp_gt n k hk _ _ _
      ((tensorFunctor.obj M.nu).source_composable hk h)]
    exact (tensorFunctor.obj M.nu).comp_congr_cells k _ _ ihx ihy

def subcategory (A : RankedAtoms.{u,v} M) (n : ℕ) :
    Subcategory (tensorFunctor.obj M.nu) where
  carrier := {z | AtomicLayers A n z}
  source_mem k := by
    intro z hz
    change AtomicLayers A n ((tensorFunctor.obj M.nu).source k z)
    by_cases hk : k < n
    · exact .lower k hk _ ((tensorFunctor.obj M.nu).source_source_self k z)
    · rw [(tensorFunctor.obj M.nu).source_fixed_upwards (by omega : n ≤ k) hz.bounded]
      exact hz
  target_mem k := by
    intro z hz
    change AtomicLayers A n ((tensorFunctor.obj M.nu).target k z)
    by_cases hk : k < n
    · exact .lower k hk _ ((tensorFunctor.obj M.nu).source_target_self k z)
    · rw [(tensorFunctor.obj M.nu).target_eq_self_of_source_eq_self
        ((tensorFunctor.obj M.nu).source_fixed_upwards (by omega : n ≤ k) hz.bounded)]
      exact hz
  comp_mem k := by
    intro x y h hx hy
    change AtomicLayers A n ((tensorFunctor.obj M.nu).comp k x y h)
    by_cases hk : k < n
    · exact .compose k hk x y h hx hy
    · rw [(tensorFunctor.obj M.nu).comp_of_left_source_fixed k x y h
        ((tensorFunctor.obj M.nu).source_fixed_upwards (by omega : n ≤ k) hx.bounded)]
      exact hy

end AtomicLayers

end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

variable (C : OmegaCategory.{u}) (n : ℕ) (G : C.Cell → Prop)

inductive TopSequence : C.Cell → Prop
  | lower (x) : C.source n x = x → TopSequence x
  | single (x) : C.Whisker n G x → TopSequence x
  | compose (x y) (h : C.target n x = C.source n y) :
      TopSequence x → TopSequence y → TopSequence (C.join n x y)

end Thomason.OmegaCategory

end

end OAI
end


