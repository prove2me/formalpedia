-- Prove2me | Definitions.Def_OAIQ043T002
-- name    : OAIQ043T002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T09:43:37.473678+00:00
-- url     : https://prove2.me/theorems/eb605683-82ab-48b7-ad68-bf064a24ecd3
-- title:
--   Definitions bundle OAIQ043T002 of the split of OpenAI, Thomason Model Structures in Every Strict Higher Dimension (result family 317)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Thomason.main` and `OAI.Thomason.nerveDetection_allDimensions`, carved from OpenAI's openai/math development (OpenAI, *Thomason Model Structures in Every Strict Higher Dimension (result family 317)*, OpenAI Math Release, September 25, 2026, result family 317, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 710 declarations of OpenAI's Lean: 249 definitions, 3 inductive types or structures, 35 instances and 423 theorems. The definitions and types are `OAI.Thomason.AttachmentComparison.inc`, `OAI.Thomason.AttachmentComparison.posetObj`, `OAI.Thomason.AttachmentComparison.sb`, `OAI.Thomason.Attachments.IsPosetFiniteAttachmentPiece`, `OAI.Thomason.Attachments.IsPosetFiniteNewPiece`, `OAI.Thomason.Attachments.constantFiniteLabel`, `OAI.Thomason.Attachments.fullFinite`, `OAI.Thomason.Attachments.fullFiniteInclusion`, `OAI.Thomason.Attachments.minFiniteLabel`, `OAI.Thomason.DirectedComplex.Table.extendTop`, `OAI.Thomason.DirectedComplex.Table.extensionRow`, `OAI.Thomason.DirectedComplex.Table.removeContext`, `OAI.Thomason.DirectedComplex.Table.removeContextRow`, `OAI.Thomason.DirectedComplex.lambdaCounitMap`, `OAI.Thomason.DirectedComplex.lambdaCounitRaw`, `OAI.Thomason.GeometricRecognition.Mesh.evaluate`, `OAI.Thomason.GeometricRecognition.Mesh.levelHomeomorph`, `OAI.Thomason.GeometricRecognition.Mesh.levelVertices`, `OAI.Thomason.GeometricRecognition.PolyPoint.ChainIndex.faceReal`, `OAI.Thomason.GeometricRecognition.PolyPoint.ChainIndex.inclusion`, `OAI.Thomason.GeometricRecognition.PolyPoint.carrierHomotopy`, `OAI.Thomason.GeometricRecognition.PolyPoint.imageChain`, `OAI.Thomason.GeometricRecognition.PolyPoint.imageIndex`, `OAI.Thomason.GeometricRecognition.PolyPoint.imageOrdinal`, `OAI.Thomason.GeometricRecognition.PolyPoint.orientedMap`, `OAI.Thomason.GeometricRecognition.PosetAttachment.right`, `OAI.Thomason.GeometricRecognition.Posetal.CC`, `OAI.Thomason.GeometricRecognition.lastBarycentricHomotopy`, `OAI.Thomason.GeometricRecognition.levelMap`, `OAI.Thomason.GeometricRecognition.nerveRealizationHomeomorph`, `OAI.Thomason.GeometricRecognition.polyCocone`, `OAI.Thomason.GeometricRecognition.polyRealize`, `OAI.Thomason.GeometricRecognition.polyToRealization`, `OAI.Thomason.GeometricRecognition.polyToRealizationHom`, `OAI.Thomason.GeometricRecognition.realizationToPoly`, `OAI.Thomason.GeometricRecognition.realizeSimplex`, `OAI.Thomason.HornAttachments.flagRetraction`, `OAI.Thomason.HornAttachments.oldFlagsIso`, `OAI.Thomason.HornAttachments.simplexFaces`, `OAI.Thomason.HornAttachments.upwardToMeeting` and 212 more.
--
--   **Sources.** They come from these modules of lean/OAI/CategoryTheory/Thomason, in whole or in part: `StdSimplexTopCompat`, `Thomason_AlexanderWhitney`, `Thomason_BarycentricMesh`, `Thomason_BoundaryQuotients`, `Thomason_CoherentGluing`, `Thomason_CubicalGeometry`, `Thomason_CubicalRecognition`, `Thomason_ExtensionAnodyne`, `Thomason_FiberComparisons`, `Thomason_FilteredColimits`, `Thomason_FiniteAttachments`, `Thomason_Generators`, `Thomason_Globes`, `Thomason_GlobularComplexes`, `Thomason_HornRealization`, `Thomason_KanTowers`, `Thomason_LabelledFibers`, `Thomason_Linearization`, `Thomason_ModelClasses`, `Thomason_OrientalCounit`, `Thomason_PartialPrisms`, `Thomason_Polyhedra`, `Thomason_PosetComparison`, `Thomason_PosetalColimits`, `Thomason_PosetalReduction`, `Thomason_Presentations`, `Thomason_RelativeContiguity`, `Thomason_RelativeRepresentation`, `Thomason_SieveAttachments`, `Thomason_SimplexAtoms`, `Thomason_SimplexColimits`, `Thomason_SimplexRanks`, `Thomason_SimplicialApproximation`, `Thomason_SkeletalCategories`, `Thomason_StrictCategories`, `Thomason_SubdividedUnit`, `Thomason_SubdivisionFaces`, `Thomason_SubdivisionMaps`, `Thomason_SubdivisionNerves`, `Thomason_SubdivisionWeak`.
--
--   **Imports.** It imports the published bundle `Def_ThomasonModelStructures`; the bundles `OAIQ043T000` and `OAIQ043T001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ043T004` and `OAIQ043T005`.
-- source:
--   OpenAI, Thomason Model Structures in Every Strict Higher Dimension (result family 317), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 317; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Thomason-Model-Structures-in-Every-Strict-Higher-Dimension-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/CategoryTheory/Thomason at commit adc7f12

import Mathlib
import Definitions.Def_ThomasonModelStructures
import Definitions.Def_OAIQ043T000
import Definitions.Def_OAIQ043T001

section
-- module Solutions.OAIQ043_TH.StdSimplexTopCompat
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.KanQuillen.boundary_small _root_.OAI.Thomason.KanQuillen.boundary_smallCardinal _root_.OAI.Thomason.KanQuillen.boundary_smallObject _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits _root_.OAI.isProbabilityMeasure_map_fst _root_.OAI.isProbabilityMeasure_map_measurableEquiv _root_.OAI.isProbabilityMeasure_map_snd _root_.OAI.isProbabilityMeasure_map_subtype_val
open CategoryTheory Simplicial

noncomputable section

/-! ## Part 3: `SimplexCategory.toTopHomeoD`, `toTopHomeo` with the structure `Convexity.StdSimplex` -/

/-- `d13f23b`'s `SimplexCategory.toTopHomeo`: the realization of `Δ[n]` is homeomorphic to
`Convexity.StdSimplex ℝ (Fin (n.len + 1))`. -/
noncomputable def SimplexCategory.toTopHomeoD (n : SimplexCategory) :
    ↑(SSet.toTop.obj (SSet.stdSimplex.obj n)) ≃ₜ Convexity.StdSimplex ℝ (Fin (n.len + 1)) :=
  n.toTopHomeo.trans (OAI.SStd.homeoStdSimplex _)

theorem SimplexCategory.toTopHomeoD_naturality_apply {n m : SimplexCategory} (f : n ⟶ m)
    (x : ↑(SSet.toTop.obj (SSet.stdSimplex.obj n))) :
    m.toTopHomeoD ((ConcreteCategory.hom (SSet.toTop.map (SSet.stdSimplex.map f))) x) =
      Convexity.StdSimplex.map (⇑(ConcreteCategory.hom f)) (n.toTopHomeoD x) := by
  apply Convexity.StdSimplex.ext
  ext k
  simp only [SimplexCategory.toTopHomeoD, Homeomorph.trans_apply,
    SimplexCategory.toTopHomeo_naturality_apply]
  simp [OAI.SStd.homeoStdSimplex, OAI.SStd.equivStdSimplex, OAI.SStd.toStdSimplex,
    OAI.SStd.weights, Convexity.StdSimplex.weights_map, Finsupp.mapDomain, Finsupp.sum_fintype,
    Finsupp.single_apply]
  change (FunOnFinite.linearMap ℝ ℝ _ (n.toTopHomeo x).1) k = _
  rw [FunOnFinite.linearMap_apply_apply, Finset.sum_filter]
end
end

section
-- module Solutions.OAIQ043_TH.Thomason_StrictCategories
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.KanQuillen.boundary_small _root_.OAI.Thomason.KanQuillen.boundary_smallCardinal _root_.OAI.Thomason.KanQuillen.boundary_smallObject _root_.OAI.Thomason.OmegaCategory.objects_preservesColimits _root_.OAI.Thomason.OmegaCategory.zeroFiber_preservesColimits _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict Categories. -/

noncomputable section
universe u v w z


namespace Thomason


namespace OmegaCategory

variable (C : OmegaCategory.{u})


lemma source_composable {k i : ℕ} (hki : k < i) {x y : C.Cell}
    (h : C.target k x = C.source k y) :
    C.target k (C.source i x) = C.source k (C.source i y) := by
  rw [C.target_source, ite_eq_left hki, C.source_source, min_eq_left (le_of_lt hki)]
  exact h

lemma target_composable {k i : ℕ} (hki : k < i) {x y : C.Cell}
    (h : C.target k x = C.source k y) :
    C.target k (C.target i x) = C.source k (C.target i y) := by
  rw [C.target_target, min_eq_left (le_of_lt hki), C.source_target, ite_eq_left hki]
  exact h


end OmegaCategory
end Thomason

end

noncomputable section
universe u v w z


namespace Thomason


attribute [instance] DirectedComplex.group

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex

attribute [instance] cylinderChainGroup

end Thomason.DirectedComplex

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_Presentations
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.KanQuillen.boundary_small _root_.OAI.Thomason.KanQuillen.boundary_smallCardinal _root_.OAI.Thomason.KanQuillen.boundary_smallObject _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Presentations. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory


namespace Presentation

variable (P : Presentation.{u})


@[simp] lemma evaluate_comp (C : OmegaCategory.{u}) (I : P.Interpretation C) (k : ℕ)
    (x y : P.Cells) (h : P.target k x = P.source k y) :
    P.evaluate C I (P.comp k x y h) =
      C.comp k (P.evaluate C I x) (P.evaluate C I y) (P.evaluate_composable C I k x y h) := by
  induction x using Quotient.inductionOn with | h x =>
    induction y using Quotient.inductionOn with | h y =>
      have hm : P.Equiv (.target k x.val) (.source k y.val) := Quotient.exact h
      change (P.compTerm k x y).val.eval C I.map = _
      have hm' : C.target k (x.val.eval C I.map) = C.source k (y.val.eval C I.map) := hm C I
      simp only [compTerm, dite_eq_left hm, CellTerm.eval, CellTerm.composeOrLeft, dite_eq_left hm']
      rfl

end Presentation
end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory.Presentation

variable (P : Presentation.{u})


@[simp] lemma lift_generator (C : OmegaCategory.{u}) (I : P.Interpretation C) (g : P.Generator) :
    (P.lift C I).map (P.generator g) = I.map g := rfl

lemma mk_comp (k : ℕ) (x y : P.ValidTerm)
    (h : P.Equiv (.target k x.val) (.source k y.val))
    (h' : P.target k (Quotient.mk _ x) = P.source k (Quotient.mk _ y)) :
    P.comp k (Quotient.mk _ x) (Quotient.mk _ y) h' =
      Quotient.mk _ ⟨.comp k x.val y.val, Valid.comp (P := P) k x.val y.val x.property y.property h⟩ := by
  change Quotient.mk _ (P.compTerm k x y) = _
  simp only [compTerm, dite_eq_left h]

lemma functor_ext {C : OmegaCategory.{u}} {F G : Functor P.category C}
    (h : ∀ g, F.map (P.generator g) = G.map (P.generator g)) : F = G := by
  apply Functor.ext
  funext x
  induction x using Quotient.inductionOn with | h x =>
    rcases x with ⟨x, hx⟩
    induction hx with
    | gen g => exact h g
    | source k x hx ih =>
      change F.map (P.category.source k (Quotient.mk _ ⟨x, hx⟩)) =
        G.map (P.category.source k (Quotient.mk _ ⟨x, hx⟩))
      rw [F.map_source, G.map_source, ih]
    | target k x hx ih =>
      change F.map (P.category.target k (Quotient.mk _ ⟨x, hx⟩)) =
        G.map (P.category.target k (Quotient.mk _ ⟨x, hx⟩))
      rw [F.map_target, G.map_target, ih]
    | comp k x y hx hy hm ihx ihy =>
      have hc : P.category.target k (Quotient.mk _ ⟨x, hx⟩) =
          P.category.source k (Quotient.mk _ ⟨y, hy⟩) := Quotient.sound hm
      rw [← P.mk_comp k ⟨x, hx⟩ ⟨y, hy⟩ hm hc]
      change F.map (P.category.comp k _ _ hc) = G.map (P.category.comp k _ _ hc)
      rw [F.map_comp k _ _ hc (F.map_composable hc), G.map_comp k _ _ hc (G.map_composable hc)]
      congr 1

end Thomason.OmegaCategory.Presentation

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory.Presentation

@[simp] lemma evaluate_generator (P : Presentation.{u}) (C : OmegaCategory.{u})
    (I : P.Interpretation C) (g : P.Generator) : P.evaluate C I (P.generator g) = I.map g := rfl

end Thomason.OmegaCategory.Presentation

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory


lemma truncation_isTruncated (n : ℕ) (C : OmegaCategory.{u}) :
    (truncationPresentation n C).category.IsTruncated n := by
  intro x
  apply (truncationPresentation n C).cells_ext
  intro D I
  rw [Presentation.evaluate_source]
  exact I.satisfies.1 _


@[simp] lemma truncationLift_generator {n : ℕ} {C : OmegaCategory.{u}}
    (D : NCategory.{u} n) (F : Functor C D.val) (x : C.Cell) :
    (truncationLift D F).map ((truncationUnit n C).map x) = F.map x := rfl

lemma truncation_functor_ext {n : ℕ} {C D : OmegaCategory.{u}}
    {F G : Functor (truncation n C).val D}
    (h : Functor.comp (truncationUnit n C) F = Functor.comp (truncationUnit n C) G) : F = G := by
  apply (truncationPresentation n C).functor_ext
  intro x
  exact congrArg (fun H : Functor C D => H.map x) h

open CategoryTheory


end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory


@[simp] lemma uliftUp_down (C : OmegaCategory.{u}) :
    Functor.comp (uliftUp.{u,v} C) (uliftDown C) = Functor.id C := rfl

@[simp] lemma uliftDown_up (C : OmegaCategory.{u}) :
    Functor.comp (uliftDown.{u,v} C) (uliftUp C) = Functor.id (ulift C) := rfl

open CategoryTheory


end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Opposite


noncomputable instance categorification_preservesColimits :
    Limits.PreservesColimitsOfSize.{v,w} categorification.{u} :=
  categorificationAdjunction.leftAdjoint_preservesColimits

noncomputable instance categorificationFinite_preservesColimits (n : ℕ) :
    Limits.PreservesColimitsOfSize.{v,w} (categorificationFinite.{u} n) :=
  (categorificationFiniteAdjunction n).leftAdjoint_preservesColimits

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory Limits

instance nCategoryInclusion_full (n : ℕ) : (nCategoryInclusion.{u} n).Full where
  map_surjective f := ⟨f, rfl⟩

instance nCategoryInclusion_faithful (n : ℕ) : (nCategoryInclusion.{u} n).Faithful where
  map_injective h := h

noncomputable instance nCategoryInclusion_reflective (n : ℕ) :
    Reflective (nCategoryInclusion.{u} n) where
  L := truncationFunctor n
  adj := truncationAdjunction n

end Thomason.OmegaCategory

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_ModelClasses
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.KanQuillen.boundary_small _root_.OAI.Thomason.KanQuillen.boundary_smallCardinal _root_.OAI.Thomason.KanQuillen.boundary_smallObject _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Model Classes. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory Limits

variable {J : Type u} [Category.{u} J]

@[ext]
structure LimitCell (F : J ⥤ OmegaCategory.{u}) where
  val : ∀ j, (F.obj j).Cell
  naturality : ∀ ⦃i j⦄ (f : i ⟶ j), (F.map f).map (val i) = val j
  bounded : ∃ n, ∀ j, (F.obj j).source n (val j) = val j

namespace LimitCell

variable (F : J ⥤ OmegaCategory.{u})

def source (k : ℕ) (x : LimitCell F) : LimitCell F where
  val j := (F.obj j).source k (x.val j)
  naturality {i j} f := by rw [(F.map f).map_source, x.naturality f]
  bounded := ⟨k, fun j => (F.obj j).source_source_self k _⟩

def target (k : ℕ) (x : LimitCell F) : LimitCell F where
  val j := (F.obj j).target k (x.val j)
  naturality {i j} f := by rw [(F.map f).map_target, x.naturality f]
  bounded := ⟨k, fun j => (F.obj j).source_target_self k _⟩

lemma composable {k : ℕ} {x y : LimitCell F} (h : target F k x = source F k y) (j : J) :
    (F.obj j).target k (x.val j) = (F.obj j).source k (y.val j) :=
  congrArg (fun z : LimitCell F => z.val j) h

def comp (k : ℕ) (x y : LimitCell F) (h : target F k x = source F k y) : LimitCell F where
  val j := (F.obj j).comp k (x.val j) (y.val j) (composable F h j)
  naturality {i j} f := by
    rw [(F.map f).map_comp k _ _ _ ((F.map f).map_composable (composable F h i))]
    congr 1
    · exact x.naturality f
    · exact y.naturality f
  bounded := by
    rcases x.bounded with ⟨m, hm⟩
    rcases y.bounded with ⟨n, hn⟩
    let l := max (max m n) (k+1)
    have hkl : k < l := lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_right _ _)
    refine ⟨l, fun j => ?_⟩
    rw [(F.obj j).source_comp_gt l k hkl _ _ _
      ((F.obj j).source_composable hkl (composable F h j))]
    congr 1
    · exact (F.obj j).source_fixed_upwards (le_trans (le_max_left m n) (le_max_left _ _)) (hm j)
    · exact (F.obj j).source_fixed_upwards (le_trans (le_max_right m n) (le_max_left _ _)) (hn j)

end LimitCell

def limitCategory (F : J ⥤ OmegaCategory.{u}) : OmegaCategory.{u} where
  Cell := LimitCell F
  source := LimitCell.source F
  target := LimitCell.target F
  comp := LimitCell.comp F
  source_source i j x := by
    apply LimitCell.ext; funext a
    exact (F.obj a).source_source i j (x.val a)
  target_target i j x := by
    apply LimitCell.ext; funext a
    exact (F.obj a).target_target i j (x.val a)
  source_target i j x := by
    apply LimitCell.ext; funext a
    by_cases h : i < j <;>
      simp only [LimitCell.source, LimitCell.target, (F.obj a).source_target, h, ite_true, ite_false]
  target_source i j x := by
    apply LimitCell.ext; funext a
    by_cases h : i < j <;>
      simp only [LimitCell.source, LimitCell.target, (F.obj a).target_source, h, ite_true, ite_false]
  source_comp_le i k hik x y h := by
    apply LimitCell.ext; funext a
    exact (F.obj a).source_comp_le i k hik _ _ _
  target_comp_le i k hik x y h := by
    apply LimitCell.ext; funext a
    exact (F.obj a).target_comp_le i k hik _ _ _
  source_comp_gt i k hki x y h hs := by
    apply LimitCell.ext; funext a
    exact (F.obj a).source_comp_gt i k hki _ _ _ _
  target_comp_gt i k hki x y h ht := by
    apply LimitCell.ext; funext a
    exact (F.obj a).target_comp_gt i k hki _ _ _ _
  unit_left k x h := by
    apply LimitCell.ext; funext a
    exact (F.obj a).unit_left k _ _
  unit_right k x h := by
    apply LimitCell.ext; funext a
    exact (F.obj a).unit_right k _ _
  assoc k x y z hxy hyz hxy_z hx_yz := by
    apply LimitCell.ext; funext a
    exact (F.obj a).assoc k _ _ _ _ _ _ _
  interchange k l hkl a b c d hab hcd hac hbd h₁ h₂ := by
    apply LimitCell.ext; funext j
    exact (F.obj j).interchange k l hkl _ _ _ _ _ _ _ _ _ _
  finite_dimension x := by
    rcases x.bounded with ⟨n, hn⟩
    refine ⟨n, LimitCell.ext ?_⟩
    exact funext hn

def limitProjection (F : J ⥤ OmegaCategory.{u}) (j : J) : Functor (limitCategory F) (F.obj j) where
  map x := x.val j
  map_source _ _ := rfl
  map_target _ _ := rfl
  map_comp _ _ _ _ _ := rfl

def limitLift (F : J ⥤ OmegaCategory.{u}) (s : Cone F) : Functor s.pt (limitCategory F) where
  map x := {
    val j := (s.π.app j).map x
    naturality {i j} f := congrArg (fun g : Functor s.pt _ => g.map x) (s.w f)
    bounded := by
      rcases s.pt.finite_dimension x with ⟨n, hn⟩
      refine ⟨n, fun j => ?_⟩
      exact ((s.π.app j).map_source n x).symm.trans (congrArg (s.π.app j).map hn) }
  map_source k x := by
    apply LimitCell.ext; funext j
    exact (s.π.app j).map_source k x
  map_target k x := by
    apply LimitCell.ext; funext j
    exact (s.π.app j).map_target k x
  map_comp k x y h h' := by
    apply LimitCell.ext; funext j
    exact (s.π.app j).map_comp k x y h _

def boundedLimitCone (F : J ⥤ OmegaCategory.{u}) : Cone F where
  pt := limitCategory F
  π := {
    app := limitProjection F
    naturality := by
      intro i j f
      apply Functor.ext; funext x
      exact (x.naturality f).symm }

def boundedLimitConeIsLimit (F : J ⥤ OmegaCategory.{u}) : IsLimit (boundedLimitCone F) where
  lift := limitLift F
  fac s j := by
    apply Functor.ext; funext x
    rfl
  uniq s m hm := by
    apply Functor.ext; funext x
    apply LimitCell.ext; funext j
    have h := congrArg (fun g : Functor s.pt (F.obj j) => g.map x) (hm j)
    change (m.map x).val j = ((s.π.app j).map x) at h
    exact h

instance hasLimits : HasLimitsOfSize.{u,u} OmegaCategory.{u} where
  has_limits_of_shape := fun _ _ => {
    has_limit := fun F => ⟨⟨boundedLimitCone F, boundedLimitConeIsLimit F⟩⟩ }

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory Limits

noncomputable instance nCategory_hasLimits (n : ℕ) : HasLimitsOfSize.{u,u} (NCategory.{u} n) :=
  hasLimits_of_reflective (nCategoryInclusion n)

noncomputable instance nCategoryInclusion_preservesLimits (n : ℕ) :
    PreservesLimitsOfSize.{v,w} (nCategoryInclusion.{u} n) :=
  (truncationAdjunction n).rightAdjoint_preservesLimits

end Thomason.OmegaCategory

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_AlexanderWhitney
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.KanQuillen.boundary_small _root_.OAI.Thomason.KanQuillen.boundary_smallCardinal _root_.OAI.Thomason.KanQuillen.boundary_smallObject _root_.OAI.Thomason.NormalizedChains.finiteWord _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Alexander Whitney. -/

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E]

lemma prepend_apply_zero (a : E) (c : Chains E) (w : Word E)
    (h : ∀ l : List E, a :: l ≠ w.val) : prepend a c w = 0 := by
  classical
  rw [prepend, Finsupp.linearCombination_apply, Finsupp.sum]
  simp only [Finset.sum_apply, Finsupp.coe_finsetSum]
  apply Finset.sum_eq_zero
  intro t _
  simp only [Finsupp.smul_apply, smul_eq_mul, bracket_apply, ite_eq_right (h t.val), mul_zero]

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [LinearOrder E]

lemma wordBoundary_leading {a b : E} {l : List E} (h : (a :: b :: l).Pairwise (· < ·))
    (t : Word E) (ht : b :: l ≤ t.val) :
    wordBoundary (a :: b :: l) t = if (b :: l) = t.val then 1 else 0 := by
  have hz : prepend a (wordBoundary (b :: l)) t = 0 := by
    apply prepend_apply_zero
    intro q hq
    have hab : a < b := (List.pairwise_cons.mp h).1 b (by simp)
    have hlt : a :: q < b :: l := List.Lex.rel hab
    exact (not_lt_of_ge ht) (hq ▸ hlt)
  rw [wordBoundary_cons, Finsupp.sub_apply, hz, sub_zero, bracket_apply]

lemma wordBoundary_leading' (w t : Word E) (hn : 2 ≤ w.val.length)
    (ht : tailWord w ≤ t) :
    wordBoundary w.val t = if tailWord w = t then 1 else 0 := by
  rcases w with ⟨w, hw⟩
  cases w with
  | nil => simp at hn
  | cons a w =>
    cases w with
    | nil => simp at hn
    | cons b l =>
      rw [wordBoundary_leading hw t ht]
      congr 1
      exact propext ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

lemma positive_supportedOn_of_boundary {S : Set E} (hS : IsLowerSet S)
    {p : ℕ} {c : Chains E} (hc : c ∈ grade (p+2)) (hp : Positive c)
    (hd : boundary c ∈ supportedOn S) : c ∈ supportedOn S := by
  classical
  rw [mem_supportedOn_iff]
  by_contra hn
  push Not at hn
  obtain ⟨w, hw, a, ha, hna⟩ := hn
  let T := c.support.filter (fun t => ¬∀ b ∈ t.val, b ∈ S)
  have hwT : w ∈ T := by
    exact Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hw, fun h => hna (h a ha)⟩
  have hT : (T.image tailWord).Nonempty := (show T.Nonempty from ⟨w, hwT⟩).image tailWord
  let t : Word E := (T.image tailWord).max' hT
  have htmem : t ∈ T.image tailWord := Finset.max'_mem _ _
  obtain ⟨w₀, hw₀, hwt⟩ := Finset.mem_image.mp htmem
  have hw₀c : c w₀ ≠ 0 := Finsupp.mem_support_iff.mp (Finset.mem_filter.mp hw₀).1
  have hw₀len : w₀.val.length = p+2 := (mem_grade_iff (p+2) c).mp hc w₀ hw₀c
  have htS : ¬∀ b ∈ t.val, b ∈ S := by
    rw [← hwt]
    exact tailWord_not_supported hS w₀ (by omega) (Finset.mem_filter.mp hw₀).2
  have hmax : ∀ s ∈ T, tailWord s ≤ t := by
    intro s hs
    exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
  have hcoef : ∀ s ∈ c.support, 0 ≤ wordBoundary s.val t := by
    intro s hs
    by_cases hsin : ∀ b ∈ s.val, b ∈ S
    · have hbd := wordBoundary_mem_supportedOn hsin
      have he : wordBoundary s.val t = 0 := by
        by_contra he
        exact htS ((mem_supportedOn_iff S _).mp hbd t he)
      rw [he]
    · have hlen := (mem_grade_iff (p+2) c).mp hc s (Finsupp.mem_support_iff.mp hs)
      rw [wordBoundary_leading' s t (by omega) (hmax s (Finset.mem_filter.mpr ⟨hs, hsin⟩))]
      split <;> omega
  have hpos : 0 < (boundary c) t := by
    rw [boundary, Finsupp.linearCombination_apply, Finsupp.sum]
    simp only [Finset.sum_apply, Finsupp.coe_finsetSum, Finsupp.smul_apply, smul_eq_mul]
    apply Finset.sum_pos'
    · intro s hs
      exact mul_nonneg (hp s) (hcoef s hs)
    · refine ⟨w₀, (Finset.mem_filter.mp hw₀).1, ?_⟩
      rw [wordBoundary_leading' w₀ t (by omega) (hmax w₀ hw₀), ite_eq_left hwt, mul_one]
      exact lt_of_le_of_ne (hp w₀) (Ne.symm hw₀c)
  exact htS ((mem_supportedOn_iff S _).mp hd t (ne_of_gt hpos))

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [LinearOrder E]

lemma positive_supportedOn_of_boundary_upper {S : Set E} (hS : IsUpperSet S)
    {p : ℕ} {c : Chains E} (hc : c ∈ grade (p+2)) (hp : Positive c)
    (hd : boundary c ∈ supportedOn S) : c ∈ supportedOn S := by
  apply supportedOn_of_reverseChain
  apply positive_supportedOn_of_boundary (E := Eᵒᵈ) hS
    (reverseChain_mem_grade hc) (reverseChain_positive hp)
  rw [boundary_reverseChain hc]
  exact (supportedOn (E := Eᵒᵈ) S).smul_mem _ (reverseChain_supportedOn hd)

open DirectedComplex

lemma table_supportedOn_upper {S : Set E} (hS : IsUpperSet S)
    (x : Table (complex E)) (hx : ∀ b, (x.row 0 b).val ∈ supportedOn S) :
    ∀ p b, (x.row p b).val ∈ supportedOn S := by
  intro p
  induction p with
  | zero => exact hx
  | succ p ih =>
    intro b
    apply positive_supportedOn_of_boundary_upper hS
      (x.row (p+1) b).property (x.positive _ _)
    have hb := congrArg Subtype.val (x.boundary p b)
    change boundary (x.row (p+1) b).val = (x.row p true).val - (x.row p false).val at hb
    rw [hb]
    exact (supportedOn S).sub_mem (ih true) (ih false)

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E]

open DirectedComplex

def tableObjectsEquiv : (complex E).nu.Objects ≃ E where
  toFun x := Classical.choose (table_zero_row_vertex x.val false)
  invFun a := ⟨vertexTable a, vertexTable_source a⟩
  left_inv x := by
    apply Subtype.ext
    let a := Classical.choose (table_zero_row_vertex x.val false)
    have he : vertexTable a = Table.truncate 0 false x.val := by
      ext p b
      cases p with
      | zero =>
        apply Subtype.ext
        change bracket [a] = (x.val.row 0 false).val
        exact (Classical.choose_spec (table_zero_row_vertex x.val false)).symm
      | succ p =>
        change (vertexTable a).row (p+1) b = 0
        exact vertexTable_row_pos a (by omega) b
    exact he.trans x.property
  right_inv a := by
    apply bracket_singleton_injective
    exact (Classical.choose_spec (table_zero_row_vertex (vertexTable a) false)).symm

end Thomason.NormalizedChains

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_Polyhedra
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.compactSpace _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedChainIndex _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteChainIndex _root_.OAI.Thomason.KanQuillen.boundary_small _root_.OAI.Thomason.KanQuillen.boundary_smallCardinal _root_.OAI.Thomason.KanQuillen.boundary_smallObject _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polyhedra. -/

noncomputable section
universe u v w z


namespace Thomason.GeometricRecognition

namespace PolyPoint
variable {P : Type u} [PartialOrder P]

attribute [local instance] OAI.Thomason.GeometricRecognition.PolyPoint.polyhedraDecidableEq
lemma face_coords_injective (s : Finset P) :
    Function.Injective (fun x : Face s => (fun p => x.val.weights p)) := by
  intro x y h
  apply Subtype.ext
  apply PolyPoint.ext
  exact Finsupp.ext (congrFun h)

instance faceT2 (s : Finset P) : T2Space (Face s) :=
  (Topology.IsEmbedding.induced (face_coords_injective s)).t2Space

lemma isClosed_of_face_finite {A : Set (PolyPoint P)}
    (hA : ∀ s : Finset P, ((fun x : Face s => x.val) ⁻¹' A).Finite) : IsClosed A := by
  rw [isClosed_iff_faces]
  exact fun s => (hA s.carrier).isClosed

theorem compact_finite_carrier {K : Set (PolyPoint P)} (hK : IsCompact K) :
    ∃ s : Finset P, ∀ x ∈ K, x.weights.support ⊆ s := by
  classical
  let V : Set P := {p | ∃ x ∈ K, p ∈ x.weights.support}
  let f : V → PolyPoint P := fun p => Classical.choose p.property
  have hfK (p : V) : f p ∈ K := (Classical.choose_spec p.property).1
  have hfp (p : V) : p.val ∈ (f p).weights.support :=
    (Classical.choose_spec p.property).2
  let R : Set (PolyPoint P) := Set.range f
  have hRK : R ⊆ K := by
    rintro x ⟨p, rfl⟩
    exact hfK p
  have hface (s : Finset P) : ((fun x : Face s => x.val) ⁻¹' R).Finite := by
    have hv : {p : V | p.val ∈ s}.Finite :=
      (s.finite_toSet).preimage Subtype.val_injective.injOn
    apply Set.Finite.of_finite_image (f := fun x : Face s => x.val) _
      Subtype.val_injective.injOn
    apply (hv.image f).subset
    rintro x ⟨y, ⟨p, hp⟩, rfl⟩
    refine ⟨p, ?_, hp⟩
    exact y.property ((congrArg (fun z : PolyPoint P => p.val ∈ z.weights.support) hp).mp
      (hfp p))
  have hclosed (A : Set (PolyPoint P)) (hA : A ⊆ R) : IsClosed A := by
    apply isClosed_of_face_finite
    intro s
    exact (hface s).subset (Set.preimage_mono hA)
  have hRcompact : IsCompact R := by
    simpa only [Set.inter_eq_right.mpr hRK] using hK.inter_right (hclosed R Set.Subset.rfl)
  have hRdiscrete : IsDiscrete R := by
    rw [isDiscrete_iff_discreteTopology, discreteTopology_iff_forall_isClosed]
    intro A
    have hc : IsClosed (Subtype.val '' A : Set (PolyPoint P)) :=
      hclosed _ (by rintro x ⟨a, ha, rfl⟩; exact a.property)
    have he : (Subtype.val : R → PolyPoint P) ⁻¹' (Subtype.val '' A) = A := by
      ext x
      simp
    rw [← he]
    exact hc.preimage continuous_subtype_val
  have hRfinite : R.Finite := hRcompact.finite hRdiscrete
  have hVfinite : V.Finite := by
    apply (hRfinite.biUnion (fun x _ => x.weights.support.finite_toSet)).subset
    intro p hp
    exact Set.mem_iUnion_of_mem (f ⟨p,hp⟩)
      (Set.mem_iUnion_of_mem (Set.mem_range_self _) (hfp ⟨p,hp⟩))
  refine ⟨hVfinite.toFinset, ?_⟩
  intro x hx p hp
  exact hVfinite.mem_toFinset.mpr ⟨x,hx,hp⟩

omit [PartialOrder P] in
lemma evalWeights_map {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : κ → P) (b : ι → κ) (x : Convexity.StdSimplex ℝ ι) :
    evalWeights a (Convexity.StdSimplex.map b x) = evalWeights (a ∘ b) x := by
  classical
  simp only [evalWeights, ← Finsupp.mapDomain_fintype, Convexity.StdSimplex.weights_map,
    ← Finsupp.mapDomain_comp]

lemma eval_map {ι κ : Type*} [Fintype ι] [Fintype κ] [LinearOrder ι] [LinearOrder κ]
    (a : κ →o P) (b : ι →o κ) (x : Convexity.StdSimplex ℝ ι) :
    eval a (Convexity.StdSimplex.map b x) = eval (a.comp b) x := by
  apply PolyPoint.ext
  exact evalWeights_map a b x

namespace ChainIndex

attribute [local instance] OAI.Thomason.GeometricRecognition.PolyPoint.polyhedraDecidableEq
lemma continuous_coordinates (s : ChainIndex P) : Continuous s.coordinates := by
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).continuous_iff]
  apply continuous_pi
  intro i
  exact (continuous_apply (s.vertices i)).comp continuous_induced_dom

end ChainIndex

end PolyPoint

open CategoryTheory Limits Simplicial Opposite

variable (P : Type u) [PartialOrder P]

noncomputable def polyCocone :
    Cocone ((CostructuredArrow.proj uliftYoneda.{u,0,0} (nerve P) ⋙
      uliftYoneda.{u,0,0}) ⋙ SSet.toTop.{u}) where
  pt := TopCat.of (PolyPoint P)
  ι := {
    app j := TopCat.ofHom ⟨fun z => PolyPoint.eval (SSet.yonedaEquiv j.hom).toOrderHom
      (j.left.toTopHomeoD z), (PolyPoint.continuous_eval _).comp j.left.toTopHomeoD.continuous⟩
    naturality j k a := by
      ext z
      change PolyPoint.eval (SSet.yonedaEquiv k.hom).toOrderHom
        (k.left.toTopHomeoD (SSet.toTop.map (SSet.stdSimplex.map a.left) z)) =
        PolyPoint.eval (SSet.yonedaEquiv j.hom).toOrderHom (j.left.toTopHomeoD z)
      erw [SimplexCategory.toTopHomeoD_naturality_apply]
      have hw : SSet.stdSimplex.map a.left ≫ k.hom = j.hom := CostructuredArrow.w a
      have hσ : (nerve P).map a.left.op (SSet.yonedaEquiv k.hom) =
          SSet.yonedaEquiv j.hom :=
        (SSet.yonedaEquiv_naturality a.left k.hom).trans (congrArg SSet.yonedaEquiv hw)
      rw [← hσ]
      exact PolyPoint.eval_map (SSet.yonedaEquiv k.hom).toOrderHom a.left.toOrderHom _ }

noncomputable def realizationToPoly : |nerve P| ⟶ TopCat.of (PolyPoint P) :=
  (nerveRealizationIsColimit P).desc (polyCocone P)

variable {P}

def realizeSimplex {n : ℕ} (a : Fin (n + 1) →o P)
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) : |nerve P| :=
  SSet.toTop.map ((SSet.yonedaEquiv (X := nerve P)).symm a.monotone.functor)
    ((SimplexCategory.mk n).toTopHomeoD.symm x)

lemma continuous_realizeSimplex {n : ℕ} (a : Fin (n + 1) →o P) :
    Continuous (realizeSimplex a) :=
  (SSet.toTop.map ((SSet.yonedaEquiv (X := nerve P)).symm a.monotone.functor)).hom.continuous.comp
    (SimplexCategory.mk n).toTopHomeoD.symm.continuous

lemma realizeSimplex_map {m n : ℕ} (a : Fin (n + 1) →o P)
    (b : Fin (m + 1) →o Fin (n + 1)) (x : Convexity.StdSimplex ℝ (Fin (m + 1))) :
    realizeSimplex a (Convexity.StdSimplex.map b x) = realizeSimplex (a.comp b) x := by
  let β : SimplexCategory.mk m ⟶ SimplexCategory.mk n := SimplexCategory.mkHom b
  have hβ : SSet.stdSimplex.map β ≫ (SSet.yonedaEquiv (X := nerve P)).symm a.monotone.functor =
      (SSet.yonedaEquiv (X := nerve P)).symm (a.comp b).monotone.functor := by
    apply SSet.yonedaEquiv.injective
    rw [← SSet.yonedaEquiv_naturality]
    rfl
  have ht : (SimplexCategory.mk n).toTopHomeoD.symm (Convexity.StdSimplex.map b x) =
      SSet.toTop.map (SSet.stdSimplex.map β)
        ((SimplexCategory.mk m).toTopHomeoD.symm x) := by
    apply (SimplexCategory.mk n).toTopHomeoD.injective
    rw [Homeomorph.apply_symm_apply]
    erw [SimplexCategory.toTopHomeoD_naturality_apply]
    simp only [Homeomorph.apply_symm_apply]
    rfl
  change (SSet.toTop.map ((SSet.yonedaEquiv (X := nerve P)).symm a.monotone.functor))
    ((SimplexCategory.mk n).toTopHomeoD.symm (Convexity.StdSimplex.map b x)) = _
  calc
    _ = SSet.toTop.map ((SSet.yonedaEquiv (X := nerve P)).symm a.monotone.functor)
        (SSet.toTop.map (SSet.stdSimplex.map β)
          ((SimplexCategory.mk m).toTopHomeoD.symm x)) := congrArg _ ht
    _ = _ := congrArg (fun f : SSet.toTop.obj (SSet.stdSimplex.obj (SimplexCategory.mk m)) ⟶
        SSet.toTop.obj (nerve P) => f ((SimplexCategory.mk m).toTopHomeoD.symm x))
      ((SSet.toTop.map_comp (SSet.stdSimplex.map β) _).symm.trans
        (congrArg SSet.toTop.map hβ))

namespace PolyPoint.ChainIndex

def inclusion {s t : PolyPoint.ChainIndex P} (h : s.carrier ⊆ t.carrier) :
    Fin (s.dimension + 1) →o Fin (t.dimension + 1) where
  toFun i := t.enumerate.symm ⟨s.vertices i, h (s.vertices_mem i)⟩
  monotone' := fun _ _ hij => t.enumerate.symm.monotone (s.vertices.monotone hij)

lemma vertices_inclusion {s t : PolyPoint.ChainIndex P} (h : s.carrier ⊆ t.carrier) :
    t.vertices.comp (inclusion h) = s.vertices := by
  ext i
  exact congrArg Subtype.val (t.enumerate.apply_symm_apply _)

lemma eval_injective (s : PolyPoint.ChainIndex P) : Function.Injective (PolyPoint.eval s.vertices) := by
  intro x y h
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro i
  have hw := congrArg (fun z : PolyPoint P => z.weights (s.vertices i)) h
  exact (PolyPoint.evalWeights_apply_image s.vertices s.vertices_injective x i).symm.trans
    (hw.trans (PolyPoint.evalWeights_apply_image s.vertices s.vertices_injective y i))

lemma map_coordinates {s t : PolyPoint.ChainIndex P} (h : s.carrier ⊆ t.carrier)
    (x : PolyPoint.Face s.carrier) :
    Convexity.StdSimplex.map (inclusion h) (s.coordinates x) =
      t.coordinates ⟨x.val, x.property.trans h⟩ := by
  apply t.eval_injective
  calc
    PolyPoint.eval t.vertices (Convexity.StdSimplex.map (inclusion h) (s.coordinates x)) =
        PolyPoint.eval s.vertices (s.coordinates x) := by
      rw [PolyPoint.eval_map, vertices_inclusion]
    _ = x.val := s.eval_coordinates x
    _ = _ := (t.eval_coordinates ⟨x.val, x.property.trans h⟩).symm

def faceReal (s : PolyPoint.ChainIndex P) (x : PolyPoint.Face s.carrier) : |nerve P| :=
  realizeSimplex s.vertices (s.coordinates x)

lemma continuous_faceReal (s : PolyPoint.ChainIndex P) : Continuous s.faceReal :=
  (continuous_realizeSimplex s.vertices).comp s.continuous_coordinates

lemma faceReal_inclusion {s t : PolyPoint.ChainIndex P} (h : s.carrier ⊆ t.carrier)
    (x : PolyPoint.Face s.carrier) :
    t.faceReal ⟨x.val, x.property.trans h⟩ = s.faceReal x := by
  unfold faceReal
  rw [← map_coordinates h x, realizeSimplex_map, vertices_inclusion]

end PolyPoint.ChainIndex

def polyToRealization (x : PolyPoint P) : |nerve P| :=
  x.supportIndex.faceReal ⟨x, Finset.Subset.refl _⟩

lemma polyToRealization_face (s : PolyPoint.ChainIndex P) (x : PolyPoint.Face s.carrier) :
    polyToRealization x.val = s.faceReal x := by
  exact (PolyPoint.ChainIndex.faceReal_inclusion x.property
    (⟨x.val, Finset.Subset.refl _⟩ : PolyPoint.Face x.val.supportIndex.carrier)).symm

lemma continuous_polyToRealization : Continuous (@polyToRealization P _) := by
  rw [continuous_coinduced_dom]
  apply continuous_sigma
  intro s
  have he : (fun x : PolyPoint.Face s.carrier => polyToRealization x.val) = s.faceReal :=
    funext (polyToRealization_face s)
  exact he ▸ s.continuous_faceReal

namespace PolyPoint

attribute [local instance] OAI.Thomason.GeometricRecognition.PolyPoint.imageDecidableEq
def imageIndex {n : ℕ} (a : Fin (n + 1) →o P) : ChainIndex P where
  carrier := Finset.univ.image a
  chain := by
    intro p hp q hq hpq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hq
    rcases le_total i j with h | h
    · exact Or.inl (a.monotone h)
    · exact Or.inr (a.monotone h)
  nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty

def imageOrdinal {n : ℕ} (a : Fin (n + 1) →o P) :
    Fin (n + 1) →o Fin ((imageIndex a).dimension + 1) where
  toFun i := (imageIndex a).enumerate.symm
    ⟨a i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  monotone' := fun _ _ h => (imageIndex a).enumerate.symm.monotone (a.monotone h)

lemma image_vertices {n : ℕ} (a : Fin (n + 1) →o P) :
    (imageIndex a).vertices.comp (imageOrdinal a) = a := by
  ext i
  exact congrArg Subtype.val ((imageIndex a).enumerate.apply_symm_apply _)

end PolyPoint

lemma polyToRealization_eval {n : ℕ} (a : Fin (n + 1) →o P)
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    polyToRealization (PolyPoint.eval a x) = realizeSimplex a x := by
  let s := PolyPoint.imageIndex a
  let y : PolyPoint.Face s.carrier := ⟨PolyPoint.eval a x, PolyPoint.evalWeights_support a x⟩
  have hcoord : s.coordinates y = Convexity.StdSimplex.map (PolyPoint.imageOrdinal a) x := by
    apply s.eval_injective
    calc
      PolyPoint.eval s.vertices (s.coordinates y) = PolyPoint.eval a x :=
        s.eval_coordinates y
      _ = PolyPoint.eval (s.vertices.comp (PolyPoint.imageOrdinal a)) x := by
        rw [PolyPoint.image_vertices]
      _ = _ := (PolyPoint.eval_map s.vertices (PolyPoint.imageOrdinal a) x).symm
  calc
    polyToRealization (PolyPoint.eval a x) = s.faceReal y := polyToRealization_face s y
    _ = realizeSimplex s.vertices (Convexity.StdSimplex.map (PolyPoint.imageOrdinal a) x) :=
      congrArg (realizeSimplex s.vertices) hcoord
    _ = _ := by rw [realizeSimplex_map, PolyPoint.image_vertices]

lemma realizationToPoly_realizeSimplex {n : ℕ} (a : Fin (n + 1) →o P)
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    realizationToPoly P (realizeSimplex a x) = PolyPoint.eval a x := by
  let j : CostructuredArrow uliftYoneda.{u,0,0} (nerve P) :=
    CostructuredArrow.mk ((SSet.yonedaEquiv (X := nerve P)).symm a.monotone.functor)
  have h := ConcreteCategory.congr_hom
    ((nerveRealizationIsColimit P).fac (polyCocone P) j)
    ((SimplexCategory.mk n).toTopHomeoD.symm x)
  change realizationToPoly P (realizeSimplex a x) =
    PolyPoint.eval (SSet.yonedaEquiv ((SSet.yonedaEquiv (X := nerve P)).symm
      a.monotone.functor)).toOrderHom
      ((SimplexCategory.mk n).toTopHomeoD ((SimplexCategory.mk n).toTopHomeoD.symm x)) at h
  have hσ : (SSet.yonedaEquiv ((SSet.yonedaEquiv (X := nerve P)).symm
      a.monotone.functor)).toOrderHom = a :=
    congrArg Functor.toOrderHom ((SSet.yonedaEquiv (X := nerve P)).apply_symm_apply
      a.monotone.functor)
  exact h.trans ((congrArg (fun b => PolyPoint.eval b
      ((SimplexCategory.mk n).toTopHomeoD ((SimplexCategory.mk n).toTopHomeoD.symm x))) hσ).trans
    (congrArg (PolyPoint.eval a) ((SimplexCategory.mk n).toTopHomeoD.apply_symm_apply x)))

lemma realizationToPoly_polyToRealization (x : PolyPoint P) :
    realizationToPoly P (polyToRealization x) = x := by
  exact (realizationToPoly_realizeSimplex x.supportIndex.vertices
    (x.supportIndex.coordinates ⟨x, Finset.Subset.refl _⟩)).trans
    (x.supportIndex.eval_coordinates ⟨x, Finset.Subset.refl _⟩)

noncomputable def polyToRealizationHom : TopCat.of (PolyPoint P) ⟶ |nerve P| :=
  TopCat.ofHom ⟨polyToRealization, continuous_polyToRealization⟩

lemma realizationToPoly_comp_polyToRealization :
    realizationToPoly P ≫ polyToRealizationHom = 𝟙 _ := by
  apply (nerveRealizationIsColimit P).hom_ext
  intro j
  ext z
  have hx := polyToRealization_eval (SSet.yonedaEquiv j.hom).toOrderHom (j.left.toTopHomeoD z)
  have hh := realizationToPoly_realizeSimplex (SSet.yonedaEquiv j.hom).toOrderHom
    (j.left.toTopHomeoD z)
  have he : realizeSimplex (SSet.yonedaEquiv j.hom).toOrderHom (j.left.toTopHomeoD z) =
      SSet.toTop.map j.hom z := by
    simp only [realizeSimplex]
    have hσ : (SSet.yonedaEquiv j.hom).toOrderHom.monotone.functor =
        SSet.yonedaEquiv j.hom := rfl
    rw [hσ]
    have heq := (SSet.yonedaEquiv (X := nerve P)).symm_apply_apply j.hom
    have hv := congrArg (fun f : SSet.stdSimplex.obj j.left ⟶ nerve P => SSet.toTop.map f z) heq
    change SSet.toTop.map ((SSet.yonedaEquiv (X := nerve P)).symm
      (SSet.yonedaEquiv j.hom)) (j.left.toTopHomeoD.symm (j.left.toTopHomeoD z)) = _
    exact (congrArg (SSet.toTop.map _) (j.left.toTopHomeoD.symm_apply_apply z)).trans hv
  exact (congrArg polyToRealization ((congrArg (realizationToPoly P) he).symm.trans hh)).trans
    (hx.trans he)

lemma polyToRealization_realizationToPoly (z : |nerve P|) :
    polyToRealization (realizationToPoly P z) = z :=
  ConcreteCategory.congr_hom realizationToPoly_comp_polyToRealization z

noncomputable def nerveRealizationHomeomorph : |nerve P| ≃ₜ PolyPoint P where
  toFun := realizationToPoly P
  invFun := polyToRealization
  left_inv := polyToRealization_realizationToPoly
  right_inv := realizationToPoly_polyToRealization
  continuous_toFun := (realizationToPoly P).hom.continuous
  continuous_invFun := continuous_polyToRealization

end Thomason.GeometricRecognition

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_BarycentricMesh
attribute [-instance] _root_.OAI.Thomason.KanQuillen.boundary_small _root_.OAI.Thomason.KanQuillen.boundary_smallCardinal _root_.OAI.Thomason.KanQuillen.boundary_smallObject _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Barycentric Mesh. -/

noncomputable section
universe u v w z


namespace Thomason.GeometricRecognition
namespace PolyPoint
variable {P : Type u} [PartialOrder P]

lemma embedding_weights [Finite P] :
    Topology.IsEmbedding (fun x : PolyPoint P => (fun p => x.weights p)) :=
  ((continuous_pi continuous_weights).isClosedEmbedding
    (by intro x y h; exact PolyPoint.ext (Finsupp.ext (congrFun h)))).isEmbedding

end PolyPoint
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open PartialOrder

namespace Thomason.GeometricRecognition
namespace Mesh
variable {P : Type u} [PartialOrder P]
variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]

def evaluate (v : P → V) (x : PolyPoint P) : V :=
  Finsupp.linearCombination ℝ v x.weights

lemma evaluate_eq_sum (v : P → V) (x : PolyPoint P) :
    evaluate v x = ∑ p ∈ x.weights.support, x.weights p • v p := by
  rfl

lemma norm_evaluate_sub_le (v : P → V) (x : PolyPoint P) (w : V) (d : ℝ)
    (h : ∀ p ∈ x.weights.support, ‖v p - w‖ ≤ d) : ‖evaluate v x - w‖ ≤ d := by
  have ht : ∑ p ∈ x.weights.support, x.weights p = 1 := x.total
  have he : evaluate v x - w =
      ∑ p ∈ x.weights.support, x.weights p • (v p - w) := by
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, ht, one_smul]
    rfl
  rw [he]
  calc
    ‖∑ p ∈ x.weights.support, x.weights p • (v p - w)‖ ≤
        ∑ p ∈ x.weights.support, x.weights p * d := by
      apply norm_sum_le_of_le
      intro p hp
      rw [norm_smul, Real.norm_of_nonneg (x.nonneg p)]
      exact mul_le_mul_of_nonneg_left (h p hp) (x.nonneg p)
    _ = d := by
      rw [← Finset.sum_mul, ht, one_mul]

lemma evaluate_barycenter (v : P → V) (s : NonemptyFiniteChains P) :
    evaluate v (PolyPoint.barycenter s) = average s.finset v := by
  classical
  simp only [evaluate, PolyPoint.barycenter, map_sum, Finsupp.linearCombination_single,
    ← Finset.smul_sum, average]

lemma evaluate_subdivide (v : P → V) (x : PolyPoint (NonemptyFiniteChains P)) :
    evaluate v (PolyPoint.subdivide x) =
      evaluate (fun s : NonemptyFiniteChains P => average s.finset v) x := by
  change Finsupp.linearCombination ℝ v (PolyPoint.barycentricLinear x.weights) = _
  have hi : PolyPoint.barycentricLinear x.weights =
      x.weights.sum (fun s r => r • (PolyPoint.barycenter s).weights) := rfl
  rw [hi, map_finsuppSum]
  simp only [map_smul]
  change x.weights.sum (fun s r => r • evaluate v (PolyPoint.barycenter s)) = _
  simp only [evaluate_barycenter]
  rfl

instance finiteLevel (P : PartOrd.{u}) [Finite P] (n : ℕ) : Finite (level P n) := by
  induction n with
  | zero => exact ‹Finite P›
  | succ n ih => exact @finiteChains (level P n) _ ih

def levelHomeomorph (P : PartOrd.{u}) : (n : ℕ) → PolyPoint (level P n) ≃ₜ PolyPoint P
  | 0 => Homeomorph.refl _
  | n + 1 => PolyPoint.subdivisionHomeomorph.trans (levelHomeomorph P n)

def levelVertices (P : PartOrd.{u}) (v : P → V) : (n : ℕ) → level P n → V
  | 0 => v
  | n + 1 => fun s => average s.finset (levelVertices P v n)

lemma chainBound_level (P : PartOrd.{u}) {N : ℕ} (h : ChainBound P N) (n : ℕ) :
    ChainBound (level P n) N := by
  induction n with
  | zero => exact h
  | succ n ih => exact chainBound_subdivision ih

lemma bound_level (P : PartOrd.{u}) (v : P → V) (d : ℝ) (hd : 0 ≤ d)
    (hv : Bound v d) {N : ℕ} (hN : 0 < N) (hP : ChainBound P N) (n : ℕ) :
    Bound (levelVertices P v n) ((ratio N) ^ n * d) := by
  induction n with
  | zero => simpa only [levelVertices, pow_zero, one_mul] using hv
  | succ n ih =>
    have h := bound_subdivision (levelVertices P v n) ((ratio N) ^ n * d)
      (mul_nonneg (pow_nonneg (ratio_nonneg hN) n) hd) ih (chainBound_level P hP n)
    simpa only [levelVertices, pow_succ', mul_assoc] using h

lemma evaluate_levelHomeomorph (P : PartOrd.{u}) (v : P → V) (n : ℕ)
    (x : PolyPoint (level P n)) :
    evaluate v (levelHomeomorph P n x) = evaluate (levelVertices P v n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change evaluate v (levelHomeomorph P n (PolyPoint.subdivide x)) = _
    rw [ih]
    exact evaluate_subdivide (levelVertices P v n) x

lemma exists_small_mesh (P : PartOrd.{u}) (v : P → V) (d : ℝ) (hd : 0 ≤ d)
    (hv : Bound v d) {N : ℕ} (hN : 0 < N) (hP : ChainBound P N)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ e : ℝ, 0 ≤ e ∧ e < ε ∧ Bound (levelVertices P v n) e := by
  have ht : Filter.Tendsto (fun n : ℕ => ratio N ^ n * d) Filter.atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (ratio_nonneg hN) (ratio_lt_one hN)).mul_const d
  obtain ⟨n, hn⟩ := Filter.Eventually.exists (ht.eventually (gt_mem_nhds hε))
  exact ⟨n,ratio N ^ n * d, mul_nonneg (pow_nonneg (ratio_nonneg hN) n) hd,
    hn, bound_level P v d hd hv hN hP n⟩

end Mesh
end Thomason.GeometricRecognition

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_Linearization
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.KanQuillen.boundary_small _root_.OAI.Thomason.KanQuillen.boundary_smallCardinal _root_.OAI.Thomason.KanQuillen.boundary_smallObject _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linearization. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

def op (C : OmegaCategory.{u}) : OmegaCategory.{u} where
  Cell := C.Cell
  source := C.target
  target := C.source
  source_source := C.target_target
  target_target := C.source_source
  source_target := C.target_source
  target_source := C.source_target
  comp k x y h := C.comp k y x h.symm
  source_comp_le i k hik x y h := C.target_comp_le i k hik y x h.symm
  target_comp_le i k hik x y h := C.source_comp_le i k hik y x h.symm
  source_comp_gt i k hki x y h hs :=
    C.target_comp_gt i k hki y x h.symm hs.symm
  target_comp_gt i k hki x y h ht :=
    C.source_comp_gt i k hki y x h.symm ht.symm
  unit_left k x h := C.unit_right k x h.symm
  unit_right k x h := C.unit_left k x h.symm
  assoc k x y z hxy hyz hxy_z hx_yz :=
    (C.assoc k z y x hyz.symm hxy.symm hx_yz.symm hxy_z.symm).symm
  interchange k l hkl a b c d hab hcd hac hbd hab_cd hac_bd :=
    C.interchange k l hkl d c b a hcd.symm hab.symm hbd.symm hac.symm
      hab_cd.symm hac_bd.symm
  finite_dimension x := by
    obtain ⟨k, hk⟩ := C.finite_dimension x
    exact ⟨k, C.target_eq_self_of_source_eq_self hk⟩

@[simp] lemma op_op (C : OmegaCategory.{u}) : C.op.op = C := rfl

def Functor.op {C : OmegaCategory.{u}} {D : OmegaCategory.{v}} (F : Functor C D) :
    Functor C.op D.op where
  map := F.map
  map_source := F.map_target
  map_target := F.map_source
  map_comp k x y h h' := F.map_comp k y x h.symm h'.symm

@[simp] lemma Functor.op_op {C : OmegaCategory.{u}} {D : OmegaCategory.{v}}
    (F : Functor C D) : F.op.op = F := rfl

@[simp] lemma Functor.op_id (C : OmegaCategory.{u}) : (Functor.id C).op = Functor.id C.op := rfl

@[simp] lemma Functor.op_comp {C : OmegaCategory.{u}} {D : OmegaCategory.{v}}
    {E : OmegaCategory.{w}} (F : Functor C D) (G : Functor D E) :
    (Functor.comp F G).op = Functor.comp F.op G.op := rfl

lemma op_truncated {C : OmegaCategory.{u}} {n : ℕ} (h : C.IsTruncated n) :
    C.op.IsTruncated n := fun x => C.target_eq_self_of_source_eq_self (h x)

def opFunctor : CategoryTheory.Functor OmegaCategory.{u} OmegaCategory.{u} where
  obj := op
  map := Functor.op

def opEquivalence : CategoryTheory.Equivalence OmegaCategory.{u} OmegaCategory.{u} where
  functor := opFunctor
  inverse := opFunctor
  unitIso := CategoryTheory.Iso.refl _
  counitIso := CategoryTheory.Iso.refl _

def intervalReflect : Functor interval.{u}.op interval.{u} where
  map x := ⟨⟨x.right.down.rev⟩, ⟨x.left.down.rev⟩, by
    exact Fin.rev_le_rev.mpr x.related⟩
  map_source k x := by cases k <;> rfl
  map_target k x := by cases k <;> rfl
  map_comp k x y h h' := by
    cases k with
    | zero => rfl
    | succ k =>
      have he : x = y := h
      subst y
      rfl

@[simp] lemma intervalReflect_vertex (a : Fin 2) :
    intervalReflect.map (intervalVertex a).val = (intervalVertex a.rev).val := rfl

@[simp] lemma intervalReflect_arrow : intervalReflect.map intervalArrow = intervalArrow := rfl

@[simp] lemma intervalReflect_involutive (x : interval.{u}.Cell) :
    intervalReflect.map (intervalReflect.map x) = x := by
  rcases x with ⟨⟨a⟩, ⟨b⟩, h⟩
  simp only [intervalReflect, Fin.rev_rev]
  rfl

lemma intervalReflect_injective : Function.Injective intervalReflect.{u}.map :=
  Function.LeftInverse.injective intervalReflect_involutive

def reverseLabel {C : OmegaCategory.{u}} (p : Functor C interval.{u}) :
    Functor C.op interval.{u} := Functor.comp p.op intervalReflect

@[simp] lemma reverseLabel_reverseLabel {C : OmegaCategory.{u}} (p : Functor C interval.{u}) :
    reverseLabel (reverseLabel p) = p := by
  apply Functor.ext
  funext x
  exact intervalReflect_involutive (p.map x)

open CategoryTheory

def reverseLabelFunctor : CategoryTheory.Functor (Over interval.{u}) (Over interval.{u}) where
  obj p := Over.mk (reverseLabel p.hom)
  map {p q} F := Over.homMk (Thomason.OmegaCategory.Functor.op F.left) (by
    apply Functor.ext
    funext x
    have he := congrArg (fun f : Thomason.OmegaCategory.Functor p.left interval => f.map x) (Over.w F)
    exact congrArg intervalReflect.map he)
  map_id p := by apply Over.OverMorphism.ext; rfl
  map_comp F G := by apply Over.OverMorphism.ext; rfl

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

def reverseLabelTwiceIso : reverseLabelFunctor.{u} ⋙ reverseLabelFunctor ≅ 𝟭 _ :=
  NatIso.ofComponents (fun p => Over.isoMk (Iso.refl p.left) (by
    change p.hom = reverseLabel (reverseLabel p.hom)
    exact (reverseLabel_reverseLabel p.hom).symm)) (by
      intro p q F
      apply Over.OverMorphism.ext
      rfl)

def reverseLabelEquivalence : (Over interval.{u}) ≌ (Over interval.{u}) where
  functor := reverseLabelFunctor
  inverse := reverseLabelFunctor
  unitIso := reverseLabelTwiceIso.symm
  counitIso := reverseLabelTwiceIso
  functor_unitIso_comp p := by
    apply Over.OverMorphism.ext
    rfl

instance reverseLabelFunctor_isEquivalence : reverseLabelFunctor.{u}.IsEquivalence :=
  reverseLabelEquivalence.isEquivalence_functor

instance opFunctor_isEquivalence : opFunctor.{u}.IsEquivalence :=
  opEquivalence.isEquivalence_functor

def reversedZeroFiberIso (p : Over interval.{u}) :
    ((fiberFunctor (intervalVertex 0)).obj (reverseLabelFunctor.obj p)).op ≅
      (fiberFunctor (intervalVertex 1)).obj p where
  hom := {
    map := fun x => ⟨x.val, by
      apply intervalReflect_injective
      exact x.property⟩
    map_source := fun _ _ => rfl
    map_target := fun _ _ => rfl
    map_comp := fun _ _ _ _ _ => rfl }
  inv := {
    map := fun x => ⟨x.val, by
      change intervalReflect.map (p.hom.map x.val) = (intervalVertex 0).val
      rw [x.property]
      rfl⟩
    map_source := fun _ _ => rfl
    map_target := fun _ _ => rfl
    map_comp := fun _ _ _ _ _ => rfl }
  hom_inv_id := by apply Functor.ext; rfl
  inv_hom_id := by apply Functor.ext; rfl

def reversedZeroFiberNatIso :
    (reverseLabelFunctor.{u} ⋙ fiberFunctor (intervalVertex 0)) ⋙ opFunctor ≅
      fiberFunctor (intervalVertex 1) :=
  NatIso.ofComponents reversedZeroFiberIso (by
    intro p q F
    apply Functor.ext
    rfl)

noncomputable instance oneFiber_preservesColimits :
    Limits.PreservesColimitsOfSize.{v,w} (fiberFunctor.{u} (intervalVertex 1)) :=
  Limits.preservesColimits_of_natIso reversedZeroFiberNatIso

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex

variable {E : Type u} [PartialOrder E]

lemma edgeTable_sourceObject (a b : E) (hab : a ≤ b) :
    (complex E).nu.sourceObject (edgeTable a b hab) = tableObjectsEquiv.symm a :=
  Subtype.ext (edgeTable_source a b hab)

lemma edgeTable_targetObject (a b : E) (hab : a ≤ b) :
    (complex E).nu.targetObject (edgeTable a b hab) = tableObjectsEquiv.symm b :=
  Subtype.ext (edgeTable_target a b hab)

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

def IsObjectSieve (C : OmegaCategory.{u}) (S : Set C.Objects) : Prop :=
  ∀ x : C.Cell, C.targetObject x ∈ S → C.sourceObject x ∈ S

open NormalizedChains

def Functor.liftFullOn {C : OmegaCategory.{u}} {D : OmegaCategory.{v}}
    (F : Functor C D) (S : Set D.Objects)
    (h : ∀ a : C.Objects, F.objects a ∈ S) : Functor C (D.fullOn S).category :=
  (D.fullOn S).lift F (fun x => ⟨by simpa using h (C.sourceObject x),
    by simpa using h (C.targetObject x)⟩)

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory Limits

def fullOnMap {C : OmegaCategory.{u}} {S T : Set C.Objects} (h : S ⊆ T) :
    Functor (C.fullOn S).category (C.fullOn T).category where
  map x := ⟨x.val, h x.property.1, h x.property.2⟩
  map_source _ _ := rfl
  map_target _ _ := rfl
  map_comp _ _ _ _ _ := rfl

@[simp] lemma fullOnMap_inclusion {C : OmegaCategory.{u}} {S T : Set C.Objects}
    (h : S ⊆ T) :
    Functor.comp (fullOnMap h) (C.fullOn T).inclusion = (C.fullOn S).inclusion := rfl

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

def sourceCell (C : OmegaCategory.{u}) (p : ℕ) (x : C.Cell) : C.Cells p :=
  ⟨C.source p x, C.source_source_self p x⟩

def targetCell (C : OmegaCategory.{u}) (p : ℕ) (x : C.Cell) : C.Cells p :=
  ⟨C.target p x, C.source_target_self p x⟩

@[simp] lemma sourceCell_source_lt (C : OmegaCategory.{u}) {p q : ℕ}
    (h : p < q) (x : C.Cell) : C.sourceCell p (C.source q x) = C.sourceCell p x := by
  apply Subtype.ext
  exact (C.source_source p q x).trans (congrArg (fun t => C.source t x) (Nat.min_eq_left (le_of_lt h)))

@[simp] lemma targetCell_target_lt (C : OmegaCategory.{u}) {p q : ℕ}
    (h : p < q) (x : C.Cell) : C.targetCell p (C.target q x) = C.targetCell p x := by
  apply Subtype.ext
  exact (C.target_target p q x).trans (congrArg (fun t => C.target t x) (Nat.min_eq_left (le_of_lt h)))

@[simp] lemma sourceCell_target_lt (C : OmegaCategory.{u}) {p q : ℕ}
    (h : p < q) (x : C.Cell) : C.sourceCell p (C.target q x) = C.sourceCell p x := by
  apply Subtype.ext
  simpa only [sourceCell, ite_eq_left h] using C.source_target p q x

@[simp] lemma targetCell_source_lt (C : OmegaCategory.{u}) {p q : ℕ}
    (h : p < q) (x : C.Cell) : C.targetCell p (C.source q x) = C.targetCell p x := by
  apply Subtype.ext
  simpa only [targetCell, ite_eq_left h] using C.target_source p q x

def gradedComp (C : OmegaCategory.{u}) {n k : ℕ} (hkn : k < n)
    (x y : C.Cells n) (h : C.target k x.val = C.source k y.val) : C.Cells n :=
  ⟨C.comp k x.val y.val h, by
    rw [C.source_comp_gt n k hkn x.val y.val h (C.source_composable hkn h)]
    simp only [x.property, y.property]⟩

@[simp] lemma sourceCell_comp_lt (C : OmegaCategory.{u}) {n k : ℕ} (hkn : k < n)
    (x y : C.Cell) (h : C.target k x = C.source k y) :
    C.sourceCell n (C.comp k x y h) =
      C.gradedComp hkn (C.sourceCell n x) (C.sourceCell n y) (C.source_composable hkn h) :=
  Subtype.ext (C.source_comp_gt n k hkn x y h _)

@[simp] lemma targetCell_comp_lt (C : OmegaCategory.{u}) {n k : ℕ} (hkn : k < n)
    (x y : C.Cell) (h : C.target k x = C.source k y) :
    C.targetCell n (C.comp k x y h) =
      C.gradedComp hkn (C.targetCell n x) (C.targetCell n y) (C.target_composable hkn h) :=
  Subtype.ext (C.target_comp_gt n k hkn x y h _)

abbrev LambdaRaw (C : OmegaCategory.{u}) (n : ℕ) := C.Cells n →₀ ℤ

def lambdaRelations (C : OmegaCategory.{u}) (n : ℕ) : Submodule ℤ (C.LambdaRaw n) :=
  Submodule.span ℤ ({z | ∃ (x : C.Cells n) (k : ℕ), k < n ∧ C.source k x.val = x.val ∧
      z = Finsupp.single x 1} ∪
    {z | ∃ (k : ℕ) (hk : k < n) (x y : C.Cells n)
      (h : C.target k x.val = C.source k y.val),
      z = Finsupp.single (C.gradedComp hk x y h) 1 - Finsupp.single x 1 - Finsupp.single y 1})

abbrev LambdaChain (C : OmegaCategory.{u}) (n : ℕ) := C.LambdaRaw n ⧸ C.lambdaRelations n

def lambdaGen (C : OmegaCategory.{u}) {n : ℕ} (x : C.Cells n) : C.LambdaChain n :=
  (C.lambdaRelations n).mkQ (Finsupp.single x 1)

lemma lambdaGen_degenerate (C : OmegaCategory.{u}) {n k : ℕ} (hkn : k < n)
    (x : C.Cells n) (hx : C.source k x.val = x.val) : C.lambdaGen x = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact Submodule.subset_span (Or.inl ⟨x, k, hkn, hx, rfl⟩)

lemma lambdaGen_comp (C : OmegaCategory.{u}) {n k : ℕ} (hkn : k < n)
    (x y : C.Cells n) (h : C.target k x.val = C.source k y.val) :
    C.lambdaGen (C.gradedComp hkn x y h) = C.lambdaGen x + C.lambdaGen y := by
  have hz : (C.lambdaRelations n).mkQ
      (Finsupp.single (C.gradedComp hkn x y h) 1 - Finsupp.single x 1 - Finsupp.single y 1) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Submodule.subset_span (Or.inr ⟨k, hkn, x, y, h, rfl⟩)
  change C.lambdaGen (C.gradedComp hkn x y h) - C.lambdaGen x - C.lambdaGen y = 0 at hz
  exact sub_eq_zero.mp (by simpa only [sub_add_eq_sub_sub] using hz)

lemma lambda_linear_ext (C : OmegaCategory.{u}) {n : ℕ} {M : Type v}
    [AddCommGroup M] [Module ℤ M] (f g : C.LambdaChain n →ₗ[ℤ] M)
    (h : ∀ x : C.Cells n, f (C.lambdaGen x) = g (C.lambdaGen x)) : f = g := by
  apply Submodule.linearMap_qext
  apply Finsupp.lhom_ext
  intro x z
  have hz : (Finsupp.single x z : C.LambdaRaw n) = z • Finsupp.single x 1 := by simp
  rw [hz]
  exact (map_zsmul (f.comp (C.lambdaRelations n).mkQ) z _).trans
    ((congrArg (fun t => z • t) (h x)).trans
      (map_zsmul (g.comp (C.lambdaRelations n).mkQ) z _).symm)

def lambdaRawD (C : OmegaCategory.{u}) (n : ℕ) : C.LambdaRaw (n+1) →ₗ[ℤ] C.LambdaChain n :=
  Finsupp.linearCombination ℤ (fun x =>
    C.lambdaGen (C.targetCell n x.val) - C.lambdaGen (C.sourceCell n x.val))

@[simp] lemma lambdaRawD_single (C : OmegaCategory.{u}) (n : ℕ) (x : C.Cells (n+1)) :
    C.lambdaRawD n (Finsupp.single x 1) =
      C.lambdaGen (C.targetCell n x.val) - C.lambdaGen (C.sourceCell n x.val) := by
  exact (Finsupp.linearCombination_single _ _ _).trans (one_smul ℤ _)

lemma lambdaRawD_relations (C : OmegaCategory.{u}) (n : ℕ) :
    C.lambdaRelations (n+1) ≤ LinearMap.ker (C.lambdaRawD n) := by
  apply Submodule.span_le.mpr
  intro z hz
  change C.lambdaRawD n z = 0
  rcases hz with ⟨x, k, hk, hx, rfl⟩ | ⟨k, hk, x, y, h, rfl⟩
  · rw [C.lambdaRawD_single]
    have hs : C.source n x.val = x.val := C.source_fixed_upwards (by omega) hx
    have he : C.targetCell n x.val = C.sourceCell n x.val :=
      Subtype.ext ((C.target_eq_self_of_source_eq_self hs).trans hs.symm)
    rw [he, sub_self]
  · simp only [map_sub, lambdaRawD_single]
    by_cases hkn : k < n
    · rw [show (C.gradedComp hk x y h).val = C.comp k x.val y.val h from rfl,
        C.targetCell_comp_lt hkn, C.sourceCell_comp_lt hkn]
      erw [C.lambdaGen_comp hkn, C.lambdaGen_comp hkn]
      abel
    · have he : k = n := by omega
      subst k
      have hs : C.sourceCell n (C.gradedComp hk x y h).val = C.sourceCell n x.val :=
        Subtype.ext (C.source_comp_le n n le_rfl x.val y.val h)
      have ht : C.targetCell n (C.gradedComp hk x y h).val = C.targetCell n y.val :=
        Subtype.ext (C.target_comp_le n n le_rfl x.val y.val h)
      have hh : C.targetCell n x.val = C.sourceCell n y.val := Subtype.ext h
      rw [hs, ht, hh]
      abel

def lambdaD (C : OmegaCategory.{u}) (n : ℕ) : C.LambdaChain (n+1) →ₗ[ℤ] C.LambdaChain n :=
  (C.lambdaRelations (n+1)).liftQ (C.lambdaRawD n) (C.lambdaRawD_relations n)

@[simp] lemma lambdaD_gen (C : OmegaCategory.{u}) (n : ℕ) (x : C.Cells (n+1)) :
    C.lambdaD n (C.lambdaGen x) =
      C.lambdaGen (C.targetCell n x.val) - C.lambdaGen (C.sourceCell n x.val) :=
  C.lambdaRawD_single n x

lemma lambdaD_square (C : OmegaCategory.{u}) (n : ℕ) :
    (C.lambdaD n).comp (C.lambdaD (n+1)) = 0 := by
  apply C.lambda_linear_ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  erw [lambdaD_gen, map_sub, lambdaD_gen, lambdaD_gen]
  have hss : C.sourceCell n (C.source (n+1) x.val) = C.sourceCell n x.val :=
    C.sourceCell_source_lt (by omega) x.val
  have hst : C.sourceCell n (C.target (n+1) x.val) = C.sourceCell n x.val :=
    C.sourceCell_target_lt (by omega) x.val
  have hts : C.targetCell n (C.source (n+1) x.val) = C.targetCell n x.val :=
    C.targetCell_source_lt (by omega) x.val
  have htt : C.targetCell n (C.target (n+1) x.val) = C.targetCell n x.val :=
    C.targetCell_target_lt (by omega) x.val
  change (C.lambdaGen (C.targetCell n (C.target (n+1) x.val)) -
      C.lambdaGen (C.sourceCell n (C.target (n+1) x.val))) -
    (C.lambdaGen (C.targetCell n (C.source (n+1) x.val)) -
      C.lambdaGen (C.sourceCell n (C.source (n+1) x.val))) = 0
  rw [hss, hst, hts, htt, sub_self]

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

def lambdaRawAug (C : OmegaCategory.{u}) : C.LambdaRaw 0 →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun _ => 1)

lemma lambdaRawAug_relations (C : OmegaCategory.{u}) :
    C.lambdaRelations 0 ≤ LinearMap.ker C.lambdaRawAug := by
  apply Submodule.span_le.mpr
  intro z hz
  rcases hz with ⟨x, k, hk, _, _⟩ | ⟨k, hk, x, y, h, _⟩ <;> omega

def lambdaAug (C : OmegaCategory.{u}) : C.LambdaChain 0 →ₗ[ℤ] ℤ :=
  (C.lambdaRelations 0).liftQ C.lambdaRawAug C.lambdaRawAug_relations

@[simp] lemma lambdaAug_gen (C : OmegaCategory.{u}) (x : C.Cells 0) :
    C.lambdaAug (C.lambdaGen x) = 1 := by
  change C.lambdaRawAug (Finsupp.single x 1) = 1
  exact (Finsupp.linearCombination_single _ _ _).trans (one_smul ℤ _)

lemma lambdaAug_d (C : OmegaCategory.{u}) : C.lambdaAug.comp (C.lambdaD 0) = 0 := by
  apply C.lambda_linear_ext
  intro x
  change C.lambdaAug (C.lambdaD 0 (C.lambdaGen x)) = 0
  erw [lambdaD_gen, map_sub, lambdaAug_gen, lambdaAug_gen, sub_self]

def lambdaPositive (C : OmegaCategory.{u}) (n : ℕ) : AddSubmonoid (C.LambdaChain n) :=
  AddSubmonoid.closure (Set.range (C.lambdaGen (n := n)))

lemma lambdaGen_positive (C : OmegaCategory.{u}) {n : ℕ} (x : C.Cells n) :
    C.lambdaGen x ∈ C.lambdaPositive n :=
  AddSubmonoid.subset_closure ⟨x, rfl⟩

def linearization (C : OmegaCategory.{u}) : DirectedComplex.{u} where
  Chain := C.LambdaChain
  group _ := inferInstance
  d n := (C.lambdaD n).toAddMonoidHom
  d_d n x := LinearMap.congr_fun (C.lambdaD_square n) x
  augmentation := C.lambdaAug.toAddMonoidHom
  augmentation_d x := LinearMap.congr_fun C.lambdaAug_d x
  positive := C.lambdaPositive

lemma lambdaGen_source_above (C : OmegaCategory.{u}) {p k : ℕ} (h : k < p)
    (x : C.Cell) : C.lambdaGen (C.sourceCell p (C.source k x)) = 0 := by
  apply C.lambdaGen_degenerate h
  change C.source k (C.source p (C.source k x)) = C.source p (C.source k x)
  have he := C.source_fixed_upwards (le_of_lt h) (C.source_source_self k x)
  rw [he, C.source_source_self]

lemma lambdaGen_target_above (C : OmegaCategory.{u}) {p k : ℕ} (h : k < p)
    (x : C.Cell) : C.lambdaGen (C.targetCell p (C.source k x)) = 0 := by
  apply C.lambdaGen_degenerate h
  change C.source k (C.target p (C.source k x)) = C.target p (C.source k x)
  have he := C.target_eq_self_of_source_eq_self
    (C.source_fixed_upwards (le_of_lt h) (C.source_source_self k x))
  rw [he, C.source_source_self]

def lambdaUnitTable (C : OmegaCategory.{u}) (x : C.Cell) :
    DirectedComplex.Table C.linearization where
  row p b := if b then C.lambdaGen (C.targetCell p x) else C.lambdaGen (C.sourceCell p x)
  positive p b := by
    cases b <;> exact C.lambdaGen_positive _
  boundary p b := by
    change C.lambdaD p (if b then _ else _) = _
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · erw [lambdaD_gen]
      erw [C.targetCell_source_lt (Nat.lt_succ_self p), C.sourceCell_source_lt (Nat.lt_succ_self p)]
      rfl
    · erw [lambdaD_gen]
      erw [C.targetCell_target_lt (Nat.lt_succ_self p), C.sourceCell_target_lt (Nat.lt_succ_self p)]
      rfl
  augmentation b := by
    change C.lambdaAug (if b then _ else _) = 1
    cases b <;> exact C.lambdaAug_gen _
  bounded := by
    obtain ⟨k, hk⟩ := C.finite_dimension x
    refine ⟨k, fun p hp b => ?_⟩
    rw [← hk]
    cases b <;> first
      | exact C.lambdaGen_source_above hp x
      | exact C.lambdaGen_target_above hp x

@[simp] lemma lambdaUnitTable_row (C : OmegaCategory.{u}) (x : C.Cell) (p : ℕ) (b : Bool) :
    (C.lambdaUnitTable x).row p b =
      if b then C.lambdaGen (C.targetCell p x) else C.lambdaGen (C.sourceCell p x) := rfl

end Thomason.OmegaCategory

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SimplexAtoms
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.KanQuillen.boundary_small _root_.OAI.Thomason.KanQuillen.boundary_smallCardinal _root_.OAI.Thomason.KanQuillen.boundary_smallObject _root_.OAI.Thomason.NormalizedChains.finiteWord _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simplex Atoms. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory.Functor

variable {C : OmegaCategory.{u}} {D : OmegaCategory.{v}} {E : OmegaCategory.{w}}

def onCells (F : Functor C D) (n : ℕ) (x : C.Cells n) : D.Cells n :=
  ⟨F.map x.val, by rw [← F.map_source, x.property]⟩

@[simp] lemma onCells_source (F : Functor C D) (n : ℕ) (x : C.Cell) :
    F.onCells n (C.sourceCell n x) = D.sourceCell n (F.map x) :=
  Subtype.ext (F.map_source n x)

@[simp] lemma onCells_target (F : Functor C D) (n : ℕ) (x : C.Cell) :
    F.onCells n (C.targetCell n x) = D.targetCell n (F.map x) :=
  Subtype.ext (F.map_target n x)

lemma onCells_comp (F : Functor C D) {k n : ℕ} (hkn : k < n)
    (x y : C.Cells n) (h : C.target k x.val = C.source k y.val) :
    F.onCells n (C.gradedComp hkn x y h) =
      D.gradedComp hkn (F.onCells n x) (F.onCells n y) (F.map_composable h) :=
  Subtype.ext (F.map_comp k x.val y.val h _)

def lambdaRawMap (F : Functor C D) (n : ℕ) : C.LambdaRaw n →ₗ[ℤ] D.LambdaChain n :=
  Finsupp.linearCombination ℤ (fun x => D.lambdaGen (F.onCells n x))

@[simp] lemma lambdaRawMap_single (F : Functor C D) (n : ℕ) (x : C.Cells n) :
    F.lambdaRawMap n (Finsupp.single x 1) = D.lambdaGen (F.onCells n x) :=
  (Finsupp.linearCombination_single _ _ _).trans (one_smul ℤ _)

lemma lambdaRawMap_relations (F : Functor C D) (n : ℕ) :
    C.lambdaRelations n ≤ LinearMap.ker (F.lambdaRawMap n) := by
  apply Submodule.span_le.mpr
  intro z hz
  change F.lambdaRawMap n z = 0
  rcases hz with ⟨x, k, hk, hx, rfl⟩ | ⟨k, hk, x, y, h, rfl⟩
  · rw [F.lambdaRawMap_single]
    apply D.lambdaGen_degenerate hk
    change D.source k (F.map x.val) = F.map x.val
    rw [← F.map_source, hx]
  · simp only [map_sub, F.lambdaRawMap_single]
    rw [F.onCells_comp]
    erw [D.lambdaGen_comp hk]
    abel

def lambdaMap (F : Functor C D) (n : ℕ) : C.LambdaChain n →ₗ[ℤ] D.LambdaChain n :=
  (C.lambdaRelations n).liftQ (F.lambdaRawMap n) (F.lambdaRawMap_relations n)

@[simp] lemma lambdaMap_gen (F : Functor C D) (n : ℕ) (x : C.Cells n) :
    F.lambdaMap n (C.lambdaGen x) = D.lambdaGen (F.onCells n x) :=
  F.lambdaRawMap_single n x

end Thomason.OmegaCategory.Functor

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex

namespace Table

@[simp] lemma truncate_top_row {K : DirectedComplex.{u}} (k : ℕ) (e : Bool) (x : Table K) (b : Bool) :
    (truncate k e x).row k b = x.row k e := by
  simp only [truncate_row, lt_self_iff_false, ite_false, ite_true]

lemma row_above_fixed {K : DirectedComplex.{u}} (x : Table K) {k p : ℕ}
    (h : truncate k false x = x) (hkp : k < p) (b : Bool) : x.row p b = 0 := by
  have he := congrArg (fun t : Table K => t.row p b) h
  simpa only [truncate_row, show ¬p < k by omega, show p ≠ k by omega, ite_false] using he.symm

end Table

open OmegaCategory

def lambdaCounitRaw (K : DirectedComplex.{u}) (n : ℕ) : K.nu.LambdaRaw n →ₗ[ℤ] K.Chain n :=
  Finsupp.linearCombination ℤ (fun x => x.val.row n false)

@[simp] lemma lambdaCounitRaw_single (K : DirectedComplex.{u}) (n : ℕ) (x : K.nu.Cells n) :
    K.lambdaCounitRaw n (Finsupp.single x 1) = x.val.row n false :=
  (Finsupp.linearCombination_single _ _ _).trans (one_smul ℤ _)

lemma lambdaCounitRaw_relations (K : DirectedComplex.{u}) (n : ℕ) :
    K.nu.lambdaRelations n ≤ LinearMap.ker (K.lambdaCounitRaw n) := by
  apply Submodule.span_le.mpr
  intro z hz
  change K.lambdaCounitRaw n z = 0
  rcases hz with ⟨x, k, hk, hx, rfl⟩ | ⟨k, hk, x, y, h, rfl⟩
  · rw [K.lambdaCounitRaw_single]
    exact x.val.row_above_fixed hx hk false
  · simp only [map_sub, K.lambdaCounitRaw_single]
    change (Table.comp k x.val y.val h).row n false - x.val.row n false - y.val.row n false = 0
    erw [Table.comp_row, ite_eq_right (by omega : ¬n < k), ite_eq_right (by omega : n ≠ k)]
    abel

def lambdaCounitMap (K : DirectedComplex.{u}) (n : ℕ) : K.nu.LambdaChain n →ₗ[ℤ] K.Chain n :=
  (K.nu.lambdaRelations n).liftQ (K.lambdaCounitRaw n) (K.lambdaCounitRaw_relations n)

@[simp] lemma lambdaCounitMap_gen (K : DirectedComplex.{u}) (n : ℕ) (x : K.nu.Cells n) :
    K.lambdaCounitMap n (K.nu.lambdaGen x) = x.val.row n false :=
  K.lambdaCounitRaw_single n x

end Thomason.DirectedComplex

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex

variable {E : Type u} [PartialOrder E]

lemma boundary_prepend_zero (a : E) (c : (complex E).Chain 0)
    (hc : c.val ∈ supportedOn (Set.Ici a)) :
    boundary (prepend a c.val) = c.val - (complex E).augmentation c • bracket [a] := by
  rw [boundary_prepend_supported a hc,
    grade_zero_eq_empty (boundary_mem_grade c.property), map_smul, prepend_bracket]
  rfl

def coneTable (a : E) (x : Table (complex E))
    (hx : ∀ p b, (x.row p b).val ∈ supportedOn (Set.Ici a)) : Table (complex E) where
  row p b := match p with
    | 0 => if b then x.row 0 true else ⟨bracket [a], bracket_mem_grade [a]⟩
    | p+1 => if b then x.row (p+1) true +
        ⟨prepend a (x.row p false).val, prepend_mem_grade a (x.row p false).property⟩
      else ⟨prepend a (x.row p true).val, prepend_mem_grade a (x.row p true).property⟩
  positive p b := by
    cases p with
    | zero =>
      cases b
      · change Positive (bracket [a])
        exact bracket_positive [a]
      · exact x.positive 0 true
    | succ p =>
      cases b
      · exact prepend_positive a (x.positive p true)
      · exact (complex E).positive (p+1) |>.add_mem (x.positive (p+1) true)
          (prepend_positive a (x.positive p false))
  boundary p b := by
    apply Subtype.ext
    cases p with
    | zero =>
      have h0 (e : Bool) := boundary_prepend_zero a (x.row 0 e) (hx 0 e)
      simp only [x.augmentation, one_smul] at h0
      cases b
      · exact h0 true
      · change boundary ((x.row 1 true).val + prepend a (x.row 0 false).val) =
          (x.row 0 true).val - bracket [a]
        rw [map_add, h0]
        have he := congrArg Subtype.val (x.boundary 0 true)
        change boundary (x.row 1 true).val = (x.row 0 true).val - (x.row 0 false).val at he
        rw [he]
        abel
    | succ p =>
      have he (e : Bool) := congrArg Subtype.val (x.boundary p e)
      change ∀ e, boundary (x.row (p+1) e).val = (x.row p true).val - (x.row p false).val at he
      cases b
      · change boundary (prepend a (x.row (p+1) true).val) =
          ((x.row (p+1) true).val + prepend a (x.row p false).val) -
            prepend a (x.row p true).val
        rw [boundary_prepend_supported a (hx (p+1) true), he, map_sub]
        abel
      · change boundary ((x.row (p+2) true).val + prepend a (x.row (p+1) false).val) =
          ((x.row (p+1) true).val + prepend a (x.row p false).val) -
            prepend a (x.row p true).val
        rw [map_add, boundary_prepend_supported a (hx (p+1) false), he, map_sub]
        have he' := congrArg Subtype.val (x.boundary (p+1) true)
        change boundary (x.row (p+2) true).val =
          (x.row (p+1) true).val - (x.row (p+1) false).val at he'
        rw [he']
        abel
  augmentation b := by
    cases b
    · exact (vertexTable a).augmentation false
    · exact x.augmentation true
  bounded := by
    obtain ⟨k, hk⟩ := x.bounded
    refine ⟨k+1, ?_⟩
    intro p hp b
    cases p with
    | zero => omega
    | succ p =>
      have hkp : k < p := by omega
      cases b <;> apply Subtype.ext
      · change prepend a (x.row p true).val = 0
        rw [hk p hkp true]; exact map_zero _
      · change (x.row (p+1) true).val + prepend a (x.row p false).val = 0
        rw [hk (p+1) (by omega) true, hk p hkp false]
        exact (zero_add _).trans (map_zero _)

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex

variable {E : Type u} [LinearOrder E]

lemma positive_cycle_zero {p : ℕ} {c : Chains E} (hc : c ∈ grade (p+2))
    (hp : Positive c) (hd : boundary c = 0) : c = 0 := by
  have hs : c ∈ supportedOn (∅ : Set E) :=
    positive_supportedOn_of_boundary (by intro a b hab ha; exact False.elim ha) hc hp
      (by rw [hd]; exact (supportedOn ∅).zero_mem)
  ext w
  change c w = 0
  by_contra hw
  have he := (mem_supportedOn_iff ∅ c).mp hs w hw
  have hlen := (mem_grade_iff (p+2) c).mp hc w hw
  have hn : w.val ≠ [] := by intro h; simp [h] at hlen
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hn
  exact he a ha

lemma table_endomorphism_identity (x : Table (complex E))
    (hx : x.row 0 false = x.row 0 true) : Table.truncate 0 false x = x := by
  have he : ∀ p, x.row p false = x.row p true := by
    intro p
    induction p with
    | zero => exact hx
    | succ p ih =>
      have hz (b : Bool) : x.row (p+1) b = 0 := by
        apply Subtype.ext
        apply positive_cycle_zero (x.row (p+1) b).property (x.positive (p+1) b)
        have hb := congrArg Subtype.val (x.boundary p b)
        change boundary (x.row (p+1) b).val = (x.row p true).val - (x.row p false).val at hb
        rw [ih, sub_self] at hb
        exact hb
      rw [hz false, hz true]
  ext p b
  cases p with
  | zero =>
    rw [Table.truncate_top_row]
    cases b
    · rfl
    · exact hx
  | succ p =>
    rw [Table.truncate_row, ite_eq_right (by omega), ite_eq_right (by omega)]
    symm
    apply Subtype.ext
    apply positive_cycle_zero (x.row (p+1) b).property (x.positive (p+1) b)
    have hb := congrArg Subtype.val (x.boundary p b)
    change boundary (x.row (p+1) b).val = (x.row p true).val - (x.row p false).val at hb
    rw [he p, sub_self] at hb
    exact hb

lemma table_source_le_target (x : Table (complex E)) (s t : E)
    (hs : (x.row 0 false).val = bracket [s])
    (ht : (x.row 0 true).val = bracket [t]) : s ≤ t := by
  classical
  by_contra hn
  have hts : t < s := lt_of_not_ge hn
  have hx : ∀ p b, (x.row p b).val ∈ supportedOn (Set.Ici t) := by
    apply table_supportedOn_upper (by intro a b hab ha; exact le_trans ha hab) x
    intro b
    cases b
    · rw [hs]
      exact bracket_mem_supportedOn (by simpa using le_of_lt hts)
    · rw [ht]
      exact bracket_mem_supportedOn (by simp)
  let y := coneTable t x hx
  have hy0 : y.row 0 false = y.row 0 true := by
    apply Subtype.ext
    exact ht.symm
  have hy := table_endomorphism_identity y hy0
  have hy1 := congrArg Subtype.val (Table.row_above_fixed y hy (by omega : 0 < 1) true)
  change (x.row 1 true).val + prepend t (x.row 0 false).val = 0 at hy1
  rw [hs, prepend_bracket] at hy1
  let w : Word E := ⟨[t,s], by simpa using hts⟩
  have he := congrArg (fun c : Chains E => c w) hy1
  have hb : bracket [t,s] w = 1 := by rw [bracket_of_pairwise w.property]; simp [w]
  change (x.row 1 true).val w + bracket [t,s] w = 0 at he
  rw [hb] at he
  have hp := x.positive 1 true w
  omega

lemma coneTable_one_source (x : Table (complex E)) (s t : E)
    (hs : (x.row 0 false).val = bracket [s])
    (ht : (x.row 0 true).val = bracket [t])
    (hx : ∀ p b, (x.row p b).val ∈ supportedOn (Set.Ici s)) :
    Table.truncate 1 false (coneTable s x hx) =
      edgeTable s t (table_source_le_target x s t hs ht) := by
  ext p b
  cases p with
  | zero =>
    cases b
    · rfl
    · apply Subtype.ext; exact ht
  | succ p =>
    cases p with
    | zero =>
      rw [Table.truncate_top_row]
      apply Subtype.ext
      change prepend s (x.row 0 true).val = bracket [s,t]
      rw [ht, prepend_bracket]
    | succ p => rfl

lemma coneTable_one_target (x : Table (complex E)) (s : E)
    (hs : (x.row 0 false).val = bracket [s])
    (hx : ∀ p b, (x.row p b).val ∈ supportedOn (Set.Ici s)) :
    Table.truncate 1 true (coneTable s x hx) = Table.truncate 1 true x := by
  ext p b
  cases p with
  | zero =>
    cases b
    · apply Subtype.ext; exact hs.symm
    · rfl
  | succ p =>
    cases p with
    | zero =>
      rw [Table.truncate_top_row, Table.truncate_top_row]
      apply Subtype.ext
      change (x.row 1 true).val + prepend s (x.row 0 false).val = (x.row 1 true).val
      rw [hs, prepend_bracket, bracket_of_not_pairwise (by simp), add_zero]
    | succ p => rfl

end Thomason.NormalizedChains

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SimplexRanks
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.KanQuillen.boundary_small _root_.OAI.Thomason.KanQuillen.boundary_smallCardinal _root_.OAI.Thomason.KanQuillen.boundary_smallObject _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simplex Ranks. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.Table

variable {K : DirectedComplex.{u}}

def extensionRow (n : ℕ) (x : Table K) (c : K.Chain (n+1)) : (p : ℕ) → Bool → K.Chain p :=
  Function.update (Function.update x.row n
    (fun b => x.row n false + if b then K.d n c else 0)) (n+1) (fun _ => c)

@[simp] lemma extensionRow_top (n : ℕ) (x : Table K) (c : K.Chain (n+1)) (b : Bool) :
    extensionRow n x c (n+1) b = c := by simp [extensionRow]

@[simp] lemma extensionRow_middle (n : ℕ) (x : Table K) (c : K.Chain (n+1)) (b : Bool) :
    extensionRow n x c n b = x.row n false + if b then K.d n c else 0 := by
  simp [extensionRow]

lemma extensionRow_other (n : ℕ) (x : Table K) (c : K.Chain (n+1))
    (p : ℕ) (b : Bool) (h₀ : p ≠ n) (h₁ : p ≠ n+1) :
    extensionRow n x c p b = x.row p b := by simp [extensionRow, h₀, h₁]

def extendTop (n : ℕ) (x : Table K) (hx : truncate n false x = x)
    (c : K.Chain (n+1)) (hc : c ∈ K.positive (n+1))
    (hp : x.row n false + K.d n c ∈ K.positive n) : Table K where
  row := extensionRow n x c
  positive p b := by
    by_cases h₀ : p = n
    · subst p
      rw [extensionRow_middle]
      cases b
      · simpa using x.positive n false
      · exact hp
    · by_cases h₁ : p = n+1
      · subst p; simpa using hc
      · rw [extensionRow_other n x c p b h₀ h₁]; exact x.positive p b
  boundary p b := by
    by_cases h₀ : p = n
    · subst p
      rw [extensionRow_top, extensionRow_middle, extensionRow_middle]
      simp
    · by_cases h₁ : p = n+1
      · subst p
        rw [extensionRow_top, extensionRow_top,
          extensionRow_other n x c (n+1+1) b (by omega) (by omega),
          row_above_fixed x hx (by omega : n < n+1+1) b, map_zero, sub_self]
      · by_cases h₂ : p+1 = n
        · subst n
          rw [extensionRow_middle,
            extensionRow_other (p+1) x c p true (by omega) (by omega),
            extensionRow_other (p+1) x c p false (by omega) (by omega)]
          cases b <;> simp only [Bool.false_eq_true, ite_false, add_zero, ite_true]
          · exact x.boundary p false
          · rw [map_add, K.d_d, add_zero]; exact x.boundary p false
        · rw [extensionRow_other n x c (p+1) b h₂ (by omega),
            extensionRow_other n x c p true h₀ h₁,
            extensionRow_other n x c p false h₀ h₁]
          exact x.boundary p b
  augmentation b := by
    by_cases hn : n = 0
    · subst n
      rw [extensionRow_middle]
      cases b <;> simp only [Bool.false_eq_true, ite_false, add_zero, ite_true]
      · exact x.augmentation false
      · rw [map_add, K.augmentation_d, add_zero]; exact x.augmentation false
    · rw [extensionRow_other n x c 0 b (Ne.symm hn) (by omega)]
      exact x.augmentation b
  bounded := ⟨n+1, fun p hp b => by
    rw [extensionRow_other n x c p b (by omega) (by omega)]
    exact row_above_fixed x hx (by omega) b⟩

@[simp] lemma extendTop_row (n : ℕ) (x : Table K) (hx : truncate n false x = x)
    (c : K.Chain (n+1)) (hc : c ∈ K.positive (n+1))
    (hp : x.row n false + K.d n c ∈ K.positive n) (p : ℕ) (b : Bool) :
    (extendTop n x hx c hc hp).row p b = extensionRow n x c p b := rfl

end Thomason.DirectedComplex.Table

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_OrientalCounit
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.KanQuillen.boundary_small _root_.OAI.Thomason.KanQuillen.boundary_smallCardinal _root_.OAI.Thomason.KanQuillen.boundary_smallObject _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Oriental Counit. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.Table

variable {K : DirectedComplex.{u}}

def removeContextRow (k : ℕ) (y : Table K) (c d : K.Chain (k+1)) :
    (p : ℕ) → Bool → K.Chain p :=
  Function.update (Function.update y.row k
    (fun b => if b then y.row k true - K.d k d else y.row k false + K.d k c))
    (k+1) (fun b => y.row (k+1) b - c - d)

@[simp] lemma removeContextRow_middle (k : ℕ) (y : Table K) (c d : K.Chain (k+1)) (b : Bool) :
    removeContextRow k y c d k b =
      if b then y.row k true - K.d k d else y.row k false + K.d k c := by
  simp [removeContextRow]

@[simp] lemma removeContextRow_top (k : ℕ) (y : Table K) (c d : K.Chain (k+1)) (b : Bool) :
    removeContextRow k y c d (k+1) b = y.row (k+1) b - c - d := by
  simp [removeContextRow]

lemma removeContextRow_other (k : ℕ) (y : Table K) (c d : K.Chain (k+1))
    (p : ℕ) (b : Bool) (h₀ : p ≠ k) (h₁ : p ≠ k+1) :
    removeContextRow k y c d p b = y.row p b := by simp [removeContextRow, h₀, h₁]

def removeContext (k : ℕ) (y : Table K) (c d : K.Chain (k+1))
    (ht : ∀ b, y.row (k+1) b - c - d ∈ K.positive (k+1))
    (hs : y.row k false + K.d k c ∈ K.positive k)
    (he : y.row k true - K.d k d ∈ K.positive k) : Table K where
  row := removeContextRow k y c d
  positive p b := by
    by_cases h₀ : p = k
    · subst p; rw [removeContextRow_middle]; cases b; exact hs; exact he
    · by_cases h₁ : p = k+1
      · subst p; simpa using ht b
      · rw [removeContextRow_other k y c d p b h₀ h₁]; exact y.positive p b
  boundary p b := by
    by_cases h₀ : p = k
    · subst p
      rw [removeContextRow_top, removeContextRow_middle, removeContextRow_middle]
      simp only [Bool.false_eq_true, ite_false, ite_true, map_sub, y.boundary]
      abel
    · by_cases h₁ : p = k+1
      · subst p
        rw [removeContextRow_top, removeContextRow_top,
          removeContextRow_other k y c d (k+1+1) b (by omega) (by omega), y.boundary]
        abel
      · by_cases h₂ : p+1 = k
        · subst k
          rw [removeContextRow_middle,
            removeContextRow_other (p+1) y c d p true (by omega) (by omega),
            removeContextRow_other (p+1) y c d p false (by omega) (by omega)]
          cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true, map_add, map_sub,
            K.d_d, add_zero, sub_zero, y.boundary]
        · rw [removeContextRow_other k y c d (p+1) b h₂ (by omega),
            removeContextRow_other k y c d p true h₀ h₁,
            removeContextRow_other k y c d p false h₀ h₁]
          exact y.boundary p b
  augmentation b := by
    by_cases hk : k = 0
    · subst k
      rw [removeContextRow_middle]
      cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true, map_add, map_sub,
        K.augmentation_d, add_zero, sub_zero, y.augmentation]
    · rw [removeContextRow_other k y c d 0 b (Ne.symm hk) (by omega)]
      exact y.augmentation b
  bounded := by
    obtain ⟨n, hn⟩ := y.bounded
    refine ⟨max n (k+1), fun p hp b => ?_⟩
    rw [removeContextRow_other k y c d p b (by omega) (by omega)]
    exact hn p (lt_of_le_of_lt (le_max_left _ _) hp) b

@[simp] lemma removeContext_row (k : ℕ) (y : Table K) (c d : K.Chain (k+1))
    (ht : ∀ b, y.row (k+1) b - c - d ∈ K.positive (k+1))
    (hs : y.row k false + K.d k c ∈ K.positive k)
    (he : y.row k true - K.d k d ∈ K.positive k) (p : ℕ) (b : Bool) :
    (removeContext k y c d ht hs he).row p b = removeContextRow k y c d p b := rfl

end Thomason.DirectedComplex.Table

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_FilteredColimits
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.KanQuillen.boundary_small _root_.OAI.Thomason.KanQuillen.boundary_smallCardinal _root_.OAI.Thomason.KanQuillen.boundary_smallObject _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Filtered Colimits. -/

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex

variable {E : Type u} [LinearOrder E] [Finite E]

lemma finite_positive_fillings (p : ℕ) (b : Chains E) :
    {c : Chains E | c ∈ grade (p+2) ∧ Positive c ∧ boundary c = b}.Finite := by
  classical
  let S : Set (Chains E) := {c | c ∈ grade (p+2) ∧ Positive c ∧ boundary c = b}
  let f : Chains E → Word E → ℕ := fun c w => (c w).toNat
  have hi : Set.InjOn f S := by
    intro c hc d hd h
    ext w
    have he := congrFun h w
    have hcc := Int.toNat_of_nonneg (hc.2.1 w)
    have hdd := Int.toNat_of_nonneg (hd.2.1 w)
    dsimp only [f] at he
    omega
  have ha : IsAntichain (· ≤ ·) (f '' S) := by
    rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ hne hle
    have hone : Positive (d-c) := by
      intro w
      change 0 ≤ d w - c w
      have hh := hle w
      have hcc := Int.toNat_of_nonneg (hc.2.1 w)
      have hdd := Int.toNat_of_nonneg (hd.2.1 w)
      dsimp only [f] at hh
      omega
    have hz : d-c = 0 := positive_cycle_zero ((grade (p+2)).sub_mem hd.1 hc.1)
      hone (by rw [map_sub, hd.2.2, hc.2.2, sub_self])
    exact hne (congrArg f (sub_eq_zero.mp hz).symm)
  exact (WellQuasiOrderedLE.finite_of_isAntichain ha).of_finite_image hi

lemma possibleRows_finite (p : ℕ) : (possibleRows (E := E) p).Finite := by
  induction p with
  | zero => exact Set.finite_range _
  | succ p ih =>
    exact ih.biUnion (fun s _ => ih.biUnion (fun t _ => finite_positive_fillings p (t-s)))

omit [Finite E] in
lemma table_row_possible (x : Table (complex E)) (p : ℕ) (b : Bool) :
    (x.row p b).val ∈ possibleRows p := by
  induction p generalizing b with
  | zero =>
    obtain ⟨a, ha⟩ := table_zero_row_vertex x b
    exact ⟨a, ha.symm⟩
  | succ p ih =>
    simp only [possibleRows, Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨(x.row p false).val, ih false, (x.row p true).val, ih true,
      (x.row (p+1) b).property, x.positive (p+1) b, ?_⟩
    exact congrArg Subtype.val (x.boundary p b)

instance finiteTables : Finite (Table (complex E)) := by
  classical
  let := Fintype.ofFinite E
  let (p : Fin (Fintype.card E+1)) : Finite {c : Chains E // c ∈ possibleRows p.val} :=
    (possibleRows_finite p.val).to_subtype
  let f : Table (complex E) →
      ((p : Fin (Fintype.card E+1)) → Bool → {c : Chains E // c ∈ possibleRows p.val}) :=
    fun x p b => ⟨(x.row p.val b).val, table_row_possible x p.val b⟩
  apply Finite.of_injective f
  intro x y h
  ext p b
  apply Subtype.ext
  by_cases hp : p < Fintype.card E+1
  · exact congrArg (fun c : {c : Chains E // c ∈ possibleRows p} => c.val)
      (congrFun (congrFun h ⟨p, hp⟩) b)
  · have hn : Fintype.card E < p+1 := by omega
    rw [grade_eq_zero_of_card_lt (x.row p b).property hn,
      grade_eq_zero_of_card_lt (y.row p b).property hn]

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory Limits ConcreteCategory

def cellFunctor : OmegaCategory.{u} ⥤ Type u where
  obj C := C.Cell
  map F := ↾F.map

def cellSourceNat (n : ℕ) : cellFunctor.{u} ⟶ cellFunctor where
  app C := ↾C.source n
  naturality C D F := by
    apply ConcreteCategory.hom_ext
    intro x
    exact (F.map_source n x).symm

def cellTargetNat (n : ℕ) : cellFunctor.{u} ⟶ cellFunctor where
  app C := ↾C.target n
  naturality C D F := by
    apply ConcreteCategory.hom_ext
    intro x
    exact (F.map_target n x).symm

namespace FilteredColimit

variable {J : Type u} [Category.{u} J] (F : J ⥤ OmegaCategory.{u})

abbrev CellDiagram := F ⋙ cellFunctor
abbrev Cell := colimit (CellDiagram F)
abbrev ι (j : J) : (F.obj j).Cell → Cell F := colimit.ι (CellDiagram F) j

def source (n : ℕ) : Cell F → Cell F :=
  colimMap (CategoryTheory.Functor.whiskerLeft F (cellSourceNat n))

def target (n : ℕ) : Cell F → Cell F :=
  colimMap (CategoryTheory.Functor.whiskerLeft F (cellTargetNat n))

@[simp] lemma source_ι (n : ℕ) (j : J) (x : (F.obj j).Cell) :
    source F n (ι F j x) = ι F j ((F.obj j).source n x) :=
  congr_hom (ι_colimMap (CategoryTheory.Functor.whiskerLeft F (cellSourceNat n)) j) x

@[simp] lemma target_ι (n : ℕ) (j : J) (x : (F.obj j).Cell) :
    target F n (ι F j x) = ι F j ((F.obj j).target n x) :=
  congr_hom (ι_colimMap (CategoryTheory.Functor.whiskerLeft F (cellTargetNat n)) j) x

@[simp] lemma ι_map {i j : J} (f : i ⟶ j) (x : (F.obj i).Cell) :
    ι F j ((F.map f).map x) = ι F i x :=
  congr_hom (colimit.w (CellDiagram F) f) x

lemma exists_rep (x : Cell F) : ∃ j, ∃ y : (F.obj j).Cell, ι F j y = x :=
  Types.jointly_surjective_of_isColimit (colimit.isColimit (CellDiagram F)) x

lemma source_source (i j : ℕ) (x : Cell F) :
    source F i (source F j x) = source F (min i j) x := by
  obtain ⟨k, y, rfl⟩ := exists_rep F x
  simp only [source_ι, (F.obj k).source_source]

lemma target_target (i j : ℕ) (x : Cell F) :
    target F i (target F j x) = target F (min i j) x := by
  obtain ⟨k, y, rfl⟩ := exists_rep F x
  simp only [target_ι, (F.obj k).target_target]

lemma source_target (i j : ℕ) (x : Cell F) :
    source F i (target F j x) = if i < j then source F i x else target F j x := by
  obtain ⟨k, y, rfl⟩ := exists_rep F x
  by_cases h : i < j <;> simp only [source_ι, target_ι, (F.obj k).source_target, h, ite_true, ite_false]

lemma target_source (i j : ℕ) (x : Cell F) :
    target F i (source F j x) = if i < j then target F i x else source F j x := by
  obtain ⟨k, y, rfl⟩ := exists_rep F x
  by_cases h : i < j <;> simp only [source_ι, target_ι, (F.obj k).target_source, h, ite_true, ite_false]

lemma finite_dimension (x : Cell F) : ∃ n, source F n x = x := by
  obtain ⟨j, y, rfl⟩ := exists_rep F x
  obtain ⟨n, hn⟩ := (F.obj j).finite_dimension y
  exact ⟨n, by rw [source_ι, hn]⟩

variable [IsFiltered J]

lemma lift_matches {α : Type v} {β : Type w} [Finite α] [Finite β]
    (x : α → Cell F) (s t : β → α) (d : β → ℕ)
    (h : ∀ b, target F (d b) (x (s b)) = source F (d b) (x (t b))) :
    ∃ j, ∃ y : α → (F.obj j).Cell,
      (∀ a, ι F j (y a) = x a) ∧
      (∀ b, (F.obj j).target (d b) (y (s b)) = (F.obj j).source (d b) (y (t b))) := by
  obtain ⟨i, y, hy⟩ := Thomason.FilteredTypes.finite_representatives (CellDiagram F) x
  change α → (F.obj i).Cell at y
  change ∀ a, ι F i (y a) = x a at hy
  have he b : ι F i ((F.obj i).target (d b) (y (s b))) =
      ι F i ((F.obj i).source (d b) (y (t b))) := by
    rw [← target_ι, ← source_ι, hy, hy]
    exact h b
  obtain ⟨j, f, hf⟩ := Thomason.FilteredTypes.finite_equalities (CellDiagram F)
    (fun b => (F.obj i).target (d b) (y (s b)))
    (fun b => (F.obj i).source (d b) (y (t b))) he
  refine ⟨j, fun a => (F.map f).map (y a), ?_, ?_⟩
  · intro a
    rw [ι_map, hy]
  · intro b
    rw [← (F.map f).map_target, ← (F.map f).map_source]
    exact hf b

lemma lift_pair (k : ℕ) (x y : Cell F) (h : target F k x = source F k y) :
    ∃ j, ∃ a b : (F.obj j).Cell, ι F j a = x ∧ ι F j b = y ∧
      (F.obj j).target k a = (F.obj j).source k b := by
  obtain ⟨j, z, hz, he⟩ := lift_matches F (fun b : Bool => if b then y else x)
    (fun _ : Unit => false) (fun _ : Unit => true) (fun _ => k) (fun _ => h)
  exact ⟨j, z false, z true, hz false, hz true, he ()⟩

structure PairWitness (k : ℕ) (x y : Cell F) where
  stage : J
  left : (F.obj stage).Cell
  right : (F.obj stage).Cell
  left_eq : ι F stage left = x
  right_eq : ι F stage right = y
  matching : (F.obj stage).target k left = (F.obj stage).source k right

noncomputable def pairWitness (k : ℕ) (x y : Cell F)
    (h : target F k x = source F k y) : PairWitness F k x y := by
  have : Nonempty (PairWitness F k x y) := by
    obtain ⟨j, a, b, ha, hb, hab⟩ := lift_pair F k x y h
    exact ⟨⟨j, a, b, ha, hb, hab⟩⟩
  exact Classical.choice this

noncomputable def comp (k : ℕ) (x y : Cell F)
    (h : target F k x = source F k y) : Cell F :=
  let w := pairWitness F k x y h
  ι F w.stage ((F.obj w.stage).comp k w.left w.right w.matching)

lemma comp_ι (k : ℕ) (j : J) (a b : (F.obj j).Cell)
    (h : (F.obj j).target k a = (F.obj j).source k b)
    (h' : target F k (ι F j a) = source F k (ι F j b)) :
    comp F k (ι F j a) (ι F j b) h' = ι F j ((F.obj j).comp k a b h) := by
  let w := pairWitness F k (ι F j a) (ι F j b) h'
  have he (e : Bool) : ι F w.stage (if e then w.right else w.left) =
      ι F j (if e then b else a) := by
    cases e
    · exact w.left_eq
    · exact w.right_eq
  obtain ⟨l, f, g, hfg⟩ := Thomason.FilteredTypes.compare_finite (CellDiagram F)
    (fun e : Bool => if e then w.right else w.left)
    (fun e : Bool => if e then b else a) he
  change ∀ e : Bool, (F.map f).map (if e then w.right else w.left) =
    (F.map g).map (if e then b else a) at hfg
  have hl := hfg false
  have hr := hfg true
  dsimp at hl hr
  change ι F w.stage ((F.obj w.stage).comp k w.left w.right w.matching) = _
  calc
    _ = ι F l ((F.map f).map ((F.obj w.stage).comp k w.left w.right w.matching)) :=
      (ι_map F f _).symm
    _ = ι F l ((F.map g).map ((F.obj j).comp k a b h)) := by
      rw [(F.map f).map_comp k _ _ _ ((F.map f).map_composable w.matching),
        (F.map g).map_comp k _ _ _ ((F.map g).map_composable h)]
      simp only [hl, hr]
    _ = _ := ι_map F g _

lemma source_comp_le (i k : ℕ) (hik : i ≤ k) (x y : Cell F)
    (h : target F k x = source F k y) :
    source F i (comp F k x y h) = source F i x := by
  obtain ⟨j, a, b, rfl, rfl, hab⟩ := lift_pair F k x y h
  rw [comp_ι F k j a b hab, source_ι, source_ι, (F.obj j).source_comp_le i k hik]

lemma target_comp_le (i k : ℕ) (hik : i ≤ k) (x y : Cell F)
    (h : target F k x = source F k y) :
    target F i (comp F k x y h) = target F i y := by
  obtain ⟨j, a, b, rfl, rfl, hab⟩ := lift_pair F k x y h
  rw [comp_ι F k j a b hab, target_ι, target_ι, (F.obj j).target_comp_le i k hik]

lemma source_comp_gt (i k : ℕ) (hki : k < i) (x y : Cell F)
    (h : target F k x = source F k y)
    (hs : target F k (source F i x) = source F k (source F i y)) :
    source F i (comp F k x y h) = comp F k (source F i x) (source F i y) hs := by
  obtain ⟨j, a, b, rfl, rfl, hab⟩ := lift_pair F k x y h
  simp only [source_ι] at hs ⊢
  rw [comp_ι F k j a b hab, source_ι,
    (F.obj j).source_comp_gt i k hki a b hab ((F.obj j).source_composable hki hab),
    comp_ι F k j _ _ ((F.obj j).source_composable hki hab)]

lemma target_comp_gt (i k : ℕ) (hki : k < i) (x y : Cell F)
    (h : target F k x = source F k y)
    (ht : target F k (target F i x) = source F k (target F i y)) :
    target F i (comp F k x y h) = comp F k (target F i x) (target F i y) ht := by
  obtain ⟨j, a, b, rfl, rfl, hab⟩ := lift_pair F k x y h
  simp only [target_ι] at ht ⊢
  rw [comp_ι F k j a b hab, target_ι,
    (F.obj j).target_comp_gt i k hki a b hab ((F.obj j).target_composable hki hab),
    comp_ι F k j _ _ ((F.obj j).target_composable hki hab)]

lemma unit_left (k : ℕ) (x : Cell F)
    (h : target F k (source F k x) = source F k x) :
    comp F k (source F k x) x h = x := by
  obtain ⟨j, a, rfl⟩ := exists_rep F x
  simp only [source_ι] at h ⊢
  rw [comp_ι F k j _ _ ((F.obj j).target_source_self k a), (F.obj j).unit_left]

lemma unit_right (k : ℕ) (x : Cell F)
    (h : target F k x = source F k (target F k x)) :
    comp F k x (target F k x) h = x := by
  obtain ⟨j, a, rfl⟩ := exists_rep F x
  simp only [target_ι] at h ⊢
  rw [comp_ι F k j _ _ ((F.obj j).source_target_self k a).symm, (F.obj j).unit_right]

lemma assoc (k : ℕ) (x y z : Cell F)
    (hxy : target F k x = source F k y) (hyz : target F k y = source F k z)
    (hxy_z : target F k (comp F k x y hxy) = source F k z)
    (hx_yz : target F k x = source F k (comp F k y z hyz)) :
    comp F k (comp F k x y hxy) z hxy_z = comp F k x (comp F k y z hyz) hx_yz := by
  obtain ⟨j, a, ha, he⟩ := lift_matches F ![x,y,z]
    (fun e : Bool => if e then (1 : Fin 3) else 0)
    (fun e : Bool => if e then (2 : Fin 3) else 1) (fun _ => k)
    (by intro e; cases e <;> assumption)
  have h0 : ι F j (a 0) = x := ha 0
  have h1 : ι F j (a 1) = y := ha 1
  have h2 : ι F j (a 2) = z := ha 2
  have h01 : (F.obj j).target k (a 0) = (F.obj j).source k (a 1) := he false
  have h12 : (F.obj j).target k (a 1) = (F.obj j).source k (a 2) := he true
  subst x y z
  simp only [comp_ι F k j _ _ h01, comp_ι F k j _ _ h12,
    comp_ι F k j _ _ ((F.obj j).assoc_composable_left h01 h12),
    comp_ι F k j _ _ ((F.obj j).assoc_composable_right h01 h12)]
  rw [(F.obj j).assoc]

lemma interchange (k l : ℕ) (hkl : k < l) (a b c d : Cell F)
    (hab : target F l a = source F l b) (hcd : target F l c = source F l d)
    (hac : target F k a = source F k c) (hbd : target F k b = source F k d)
    (hab_cd : target F k (comp F l a b hab) = source F k (comp F l c d hcd))
    (hac_bd : target F l (comp F k a c hac) = source F l (comp F k b d hbd)) :
    comp F k (comp F l a b hab) (comp F l c d hcd) hab_cd =
      comp F l (comp F k a c hac) (comp F k b d hbd) hac_bd := by
  obtain ⟨j, x, hx, he⟩ := lift_matches F ![a,b,c,d]
    ![(0 : Fin 4),2,0,1] ![(1 : Fin 4),3,2,3] ![l,l,k,k]
    (by intro e; fin_cases e <;> assumption)
  have h0 : ι F j (x 0) = a := hx 0
  have h1 : ι F j (x 1) = b := hx 1
  have h2 : ι F j (x 2) = c := hx 2
  have h3 : ι F j (x 3) = d := hx 3
  have h01 : (F.obj j).target l (x 0) = (F.obj j).source l (x 1) := he 0
  have h23 : (F.obj j).target l (x 2) = (F.obj j).source l (x 3) := he 1
  have h02 : (F.obj j).target k (x 0) = (F.obj j).source k (x 2) := he 2
  have h13 : (F.obj j).target k (x 1) = (F.obj j).source k (x 3) := he 3
  have hlower : (F.obj j).target k (x 1) = (F.obj j).target k (x 0) := by
    have h := congrArg ((F.obj j).target k) h01
    simpa only [(F.obj j).target_target, (F.obj j).target_source,
      min_eq_left (le_of_lt hkl), ite_eq_left hkl] using h.symm
  have hm1 : (F.obj j).target k ((F.obj j).comp l (x 0) (x 1) h01) =
      (F.obj j).source k ((F.obj j).comp l (x 2) (x 3) h23) := by
    rw [(F.obj j).target_comp_le k l (le_of_lt hkl),
      (F.obj j).source_comp_le k l (le_of_lt hkl), hlower, h02]
  have hm2 : (F.obj j).target l ((F.obj j).comp k (x 0) (x 2) h02) =
      (F.obj j).source l ((F.obj j).comp k (x 1) (x 3) h13) := by
    rw [(F.obj j).target_comp_gt l k hkl _ _ _ ((F.obj j).target_composable hkl h02),
      (F.obj j).source_comp_gt l k hkl _ _ _ ((F.obj j).source_composable hkl h13)]
    simp only [h01, h23]
  subst a b c d
  simp only [comp_ι F l j _ _ h01, comp_ι F l j _ _ h23,
    comp_ι F k j _ _ h02, comp_ι F k j _ _ h13,
    comp_ι F k j _ _ hm1, comp_ι F l j _ _ hm2]
  rw [(F.obj j).interchange k l hkl]

noncomputable def omega : OmegaCategory.{u} where
  Cell := Cell F
  source := source F
  target := target F
  source_source := source_source F
  target_target := target_target F
  source_target := source_target F
  target_source := target_source F
  comp := comp F
  source_comp_le := source_comp_le F
  target_comp_le := target_comp_le F
  source_comp_gt := source_comp_gt F
  target_comp_gt := target_comp_gt F
  unit_left := unit_left F
  unit_right := unit_right F
  assoc := assoc F
  interchange := interchange F
  finite_dimension := finite_dimension F

noncomputable def cocone : Cocone F where
  pt := omega F
  ι := {
    app := fun j => {
      map := ι F j
      map_source := fun k x => (source_ι F k j x).symm
      map_target := fun k x => (target_ι F k j x).symm
      map_comp := fun k x y h h' => (comp_ι F k j x y h h').symm }
    naturality := by
      intro i j f
      apply Functor.ext
      funext x
      exact ι_map F f x }

omit [IsFiltered J] in
lemma desc_cell_ι (s : Cocone F) (j : J) (a : (F.obj j).Cell) :
    (colimit.desc (CellDiagram F) (cellFunctor.mapCocone s)) (ι F j a) =
      (s.ι.app j).map a :=
  congr_hom (colimit.ι_desc (cellFunctor.mapCocone s) j) a

noncomputable def desc (s : Cocone F) : omega F ⟶ s.pt where
  map := colimit.desc (CellDiagram F) (cellFunctor.mapCocone s)
  map_source k x := by
    obtain ⟨j, a, rfl⟩ := exists_rep F x
    change (colimit.desc (CellDiagram F) (cellFunctor.mapCocone s))
      (source F k (ι F j a)) = _
    rw [source_ι]
    rw [desc_cell_ι, desc_cell_ι]
    exact (s.ι.app j).map_source k a
  map_target k x := by
    obtain ⟨j, a, rfl⟩ := exists_rep F x
    change (colimit.desc (CellDiagram F) (cellFunctor.mapCocone s))
      (target F k (ι F j a)) = _
    rw [target_ι]
    rw [desc_cell_ι, desc_cell_ι]
    exact (s.ι.app j).map_target k a
  map_comp k x y h h' := by
    obtain ⟨j, a, b, rfl, rfl, hab⟩ := lift_pair F k x y h
    change target F k (ι F j a) = source F k (ι F j b) at h
    change (colimit.desc (CellDiagram F) (cellFunctor.mapCocone s))
      (comp F k (ι F j a) (ι F j b) h) = _
    rw [comp_ι F k j a b hab]
    simp only [desc_cell_ι] at h' ⊢
    exact (s.ι.app j).map_comp k a b hab h'

noncomputable def isColimit : IsColimit (cocone F) where
  desc := desc F
  fac s j := by
    apply Functor.ext
    funext x
    exact desc_cell_ι F s j x
  uniq s m h := by
    apply Functor.ext
    funext x
    obtain ⟨j, a, rfl⟩ := exists_rep F x
    have hm : m.map (ι F j a) = (s.ι.app j).map a := congrArg (fun G => G.map a) (h j)
    change m.map (ι F j a) = (colimit.desc (CellDiagram F) (cellFunctor.mapCocone s)) (ι F j a)
    rw [hm]
    exact (congr_hom (colimit.ι_desc (cellFunctor.mapCocone s) j) a).symm

end FilteredColimit
end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

lemma comp_of_left_source_fixed (C : OmegaCategory.{u}) (k : ℕ) (x y : C.Cell)
    (h : C.target k x = C.source k y) (hx : C.source k x = x) :
    C.comp k x y h = y := by
  have hx' : x = C.source k y := (C.target_eq_self_of_source_eq_self hx).symm.trans h
  simpa only [← hx'] using C.unit_left k y (C.target_source_self k y)

lemma finite_truncation (C : OmegaCategory.{u}) [Finite C.Cell] :
    ∃ n, C.IsTruncated n := by
  classical
  let := Fintype.ofFinite C.Cell
  choose n hn using C.finite_dimension
  exact ⟨Finset.univ.sup n, fun x => C.source_fixed_upwards
    (Finset.le_sup (Finset.mem_univ x)) (hn x)⟩

structure GlobularMap (C : OmegaCategory.{u}) (D : OmegaCategory.{v}) where
  map : C.Cell → D.Cell
  map_source (k : ℕ) (x : C.Cell) : map (C.source k x) = D.source k (map x)
  map_target (k : ℕ) (x : C.Cell) : map (C.target k x) = D.target k (map x)

namespace FilteredColimit

open CategoryTheory Limits ConcreteCategory

variable {J : Type u} [Category.{u} J] [IsFiltered J] (F : J ⥤ OmegaCategory.{u})

lemma finite_globular_lift {C : OmegaCategory.{v}} [Finite C.Cell]
    (G : Functor C (omega F)) :
    ∃ j, ∃ H : GlobularMap C (F.obj j), ∀ x, ι F j (H.map x) = G.map x := by
  obtain ⟨n, hn⟩ := finite_truncation C
  obtain ⟨i, y, hy⟩ := Thomason.FilteredTypes.finite_representatives (CellDiagram F) G.map
  change C.Cell → (F.obj i).Cell at y
  change ∀ x, ι F i (y x) = G.map x at hy
  let z (x : C.Cell) := (F.obj i).source n (y x)
  have hz x : ι F i (z x) = G.map x := by
    change ι F i ((F.obj i).source n (y x)) = _
    rw [← source_ι, hy]
    exact (G.map_source n x).symm.trans (congrArg G.map (hn x))
  let p : (Fin (n+1) × Bool × C.Cell) → (F.obj i).Cell :=
    fun a => if a.2.1 then (F.obj i).target a.1.val (z a.2.2)
      else (F.obj i).source a.1.val (z a.2.2)
  let q : (Fin (n+1) × Bool × C.Cell) → (F.obj i).Cell :=
    fun a => z (if a.2.1 then C.target a.1.val a.2.2 else C.source a.1.val a.2.2)
  have he a : ι F i (p a) = ι F i (q a) := by
    rcases a with ⟨k, b, x⟩
    cases b
    · change ι F i ((F.obj i).source k.val (z x)) = ι F i (z (C.source k.val x))
      rw [← source_ι, hz, hz]
      exact (G.map_source k.val x).symm
    · change ι F i ((F.obj i).target k.val (z x)) = ι F i (z (C.target k.val x))
      rw [← target_ι, hz, hz]
      exact (G.map_target k.val x).symm
  obtain ⟨j, f, hf⟩ := Thomason.FilteredTypes.finite_equalities (CellDiagram F) p q he
  change ∀ a, (F.map f).map (p a) = (F.map f).map (q a) at hf
  let w (x : C.Cell) := (F.map f).map (z x)
  have hw x : (F.obj j).source n (w x) = w x := by
    dsimp [w, z]
    rw [← (F.map f).map_source, (F.obj i).source_source_self]
  refine ⟨j, ⟨w, ?_, ?_⟩, fun x => (ι_map F f (z x)).trans (hz x)⟩
  · intro k x
    by_cases hk : k ≤ n
    · have hh := hf ⟨⟨k, by omega⟩, false, x⟩
      change (F.map f).map ((F.obj i).source k (z x)) = w (C.source k x) at hh
      rw [(F.map f).map_source] at hh
      exact hh.symm
    · rw [C.source_fixed_upwards (by omega : n ≤ k) (hn x)]
      exact ((F.obj j).source_fixed_upwards (by omega) (hw x)).symm
  · intro k x
    by_cases hk : k ≤ n
    · have hh := hf ⟨⟨k, by omega⟩, true, x⟩
      change (F.map f).map ((F.obj i).target k (z x)) = w (C.target k x) at hh
      rw [(F.map f).map_target] at hh
      exact hh.symm
    · rw [C.target_eq_self_of_source_eq_self (C.source_fixed_upwards (by omega : n ≤ k) (hn x))]
      exact ((F.obj j).target_eq_self_of_source_eq_self
        ((F.obj j).source_fixed_upwards (by omega) (hw x))).symm

lemma finite_functor_lift {C : OmegaCategory.{v}} [Finite C.Cell]
    (G : Functor C (omega F)) :
    ∃ j, ∃ H : Functor C (F.obj j), ∀ x, ι F j (H.map x) = G.map x := by
  obtain ⟨n, hn⟩ := finite_truncation C
  obtain ⟨i, H, hH⟩ := finite_globular_lift F G
  let A := (k : Fin (n+1)) × {p : C.Cell × C.Cell // C.target k.val p.1 = C.source k.val p.2}
  let hm (a : A) : (F.obj i).target a.1.val (H.map a.2.val.1) =
      (F.obj i).source a.1.val (H.map a.2.val.2) := by
    rw [← H.map_target, ← H.map_source, a.2.property]
  let p (a : A) : (F.obj i).Cell :=
    (F.obj i).comp a.1.val (H.map a.2.val.1) (H.map a.2.val.2) (hm a)
  let q (a : A) : (F.obj i).Cell := H.map (C.comp a.1.val a.2.val.1 a.2.val.2 a.2.property)
  have he (a : A) : ι F i (p a) = ι F i (q a) := by
    have hh : target F a.1.val (ι F i (H.map a.2.val.1)) =
        source F a.1.val (ι F i (H.map a.2.val.2)) := by
      rw [hH, hH]
      exact G.map_composable a.2.property
    change ι F i ((F.obj i).comp a.1.val (H.map a.2.val.1) (H.map a.2.val.2) (hm a)) = _
    rw [← comp_ι F a.1.val i _ _ (hm a) hh]
    simp only [q, hH]
    exact (G.map_comp a.1.val _ _ a.2.property (G.map_composable a.2.property)).symm
  obtain ⟨j, f, hf⟩ := Thomason.FilteredTypes.finite_equalities (CellDiagram F) p q he
  change ∀ a, (F.map f).map (p a) = (F.map f).map (q a) at hf
  let w (x : C.Cell) := (F.map f).map (H.map x)
  have ws k x : w (C.source k x) = (F.obj j).source k (w x) := by
    dsimp [w]
    rw [H.map_source, (F.map f).map_source]
  have wt k x : w (C.target k x) = (F.obj j).target k (w x) := by
    dsimp [w]
    rw [H.map_target, (F.map f).map_target]
  refine ⟨j, ⟨w, ws, wt, ?_⟩, fun x => (ι_map F f (H.map x)).trans (hH x)⟩
  intro k x y h h'
  by_cases hk : k ≤ n
  · let a : A := ⟨⟨k, by omega⟩, ⟨⟨x,y⟩, h⟩⟩
    have hh := hf a
    change (F.map f).map ((F.obj i).comp k (H.map x) (H.map y) (hm a)) =
      w (C.comp k x y h) at hh
    rw [(F.map f).map_comp k _ _ _ h'] at hh
    exact hh.symm
  · have hx : C.source k x = x := C.source_fixed_upwards (by omega) (hn x)
    have hwx : (F.obj j).source k (w x) = w x := (ws k x).symm.trans (congrArg w hx)
    rw [C.comp_of_left_source_fixed k x y h hx,
      (F.obj j).comp_of_left_source_fixed k (w x) (w y) h' hwx]

lemma finite_functor_equality {C : OmegaCategory.{v}} [Finite C.Cell]
    {i : J} (G H : Functor C (F.obj i))
    (h : Functor.comp G ((cocone F).ι.app i) = Functor.comp H ((cocone F).ι.app i)) :
    ∃ (j : J) (f : i ⟶ j), Functor.comp G (F.map f) = Functor.comp H (F.map f) := by
  have he x : ι F i (G.map x) = ι F i (H.map x) :=
    congrArg (fun H : Functor C (omega F) => H.map x) h
  obtain ⟨j, f, hf⟩ := Thomason.FilteredTypes.finite_equalities (CellDiagram F) G.map H.map he
  refine ⟨j, f, ?_⟩
  apply Functor.ext
  funext x
  exact hf x

end FilteredColimit
end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory.FilteredColimit

open CategoryTheory Limits Opposite ConcreteCategory

variable {J : Type u} [Category.{u} J] [IsFiltered J] (F : J ⥤ OmegaCategory.{u})

noncomputable def streetIsColimit :
    IsColimit (streetNerveFunctor.mapCocone (cocone F)) := by
  apply evaluationJointlyReflectsColimits
  intro m
  letI : Finite (orientals.obj m.unop).Cell := NormalizedChains.finiteTables
  apply Types.FilteredColimit.isColimitOf'
  · intro G
    change Functor (orientals.obj m.unop) (omega F) at G
    obtain ⟨j, H, hH⟩ := finite_functor_lift F G
    refine ⟨j, H, ?_⟩
    apply Functor.ext
    funext x
    exact (hH x).symm
  · intro i G H h
    exact finite_functor_equality F G H h

instance streetPreservesColimit : PreservesColimit F streetNerveFunctor :=
  preservesColimit_of_preserves_colimit_cocone (isColimit F) (streetIsColimit F)

end Thomason.OmegaCategory.FilteredColimit

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Limits

instance streetPreservesFilteredShape {J : Type u} [Category.{u} J] [IsFiltered J] :
    PreservesColimitsOfShape J streetNerveFunctor.{u} where
  preservesColimit {K} := OmegaCategory.FilteredColimit.streetPreservesColimit K

end Thomason

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_Globes
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.KanQuillen.boundary_small _root_.OAI.Thomason.KanQuillen.boundary_smallCardinal _root_.OAI.Thomason.KanQuillen.boundary_smallObject _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Globes. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory Limits Opposite

def globePresentation (n : ℕ) : Presentation.{u} where
  Generator := PUnit.{u+1}
  dimension _ := n
  relations _ _ := True

noncomputable def globe (n : ℕ) : OmegaCategory.{u} := (globePresentation n).category

def globeGenerator (n : ℕ) : (globe.{u} n).Cell :=
  (globePresentation n).generator PUnit.unit

noncomputable def globeLift (n : ℕ) {C : OmegaCategory.{u}} (x : C.Cell)
    (hx : C.source n x = x) : Functor (globe.{u} n) C :=
  (globePresentation n).lift C ⟨fun _ => x, fun _ => hx, trivial⟩

@[simp] lemma globeLift_generator (n : ℕ) {C : OmegaCategory.{u}} (x : C.Cell)
    (hx : C.source n x = x) : (globeLift n x hx).map (globeGenerator n) = x := rfl

attribute [local instance] Cardinal.fact_isRegular_aleph0

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory Limits Opposite

noncomputable def isoOfBijective {C D : OmegaCategory.{u}} (F : C ⟶ D)
    (h : Function.Bijective F.map) : C ≅ D := by
  let e := Equiv.ofBijective F.map h
  let G : Functor D C :=
    { map := e.symm
      map_source k x := by
        apply e.injective
        change e (e.symm (D.source k x)) = F.map (C.source k (e.symm x))
        rw [e.apply_symm_apply, F.map_source]
        exact congrArg (D.source k) (e.apply_symm_apply x).symm
      map_target k x := by
        apply e.injective
        change e (e.symm (D.target k x)) = F.map (C.target k (e.symm x))
        rw [e.apply_symm_apply, F.map_target]
        exact congrArg (D.target k) (e.apply_symm_apply x).symm
      map_comp k x y hxy h' := by
        apply e.injective
        change e (e.symm (D.comp k x y hxy)) = F.map (C.comp k _ _ h')
        rw [e.apply_symm_apply, F.map_comp k _ _ h' (F.map_composable h')]
        have hx : F.map (e.symm x) = x := e.apply_symm_apply x
        have hy : F.map (e.symm y) = y := e.apply_symm_apply y
        congr 1
        · exact hx.symm
        · exact hy.symm }
  exact
    { hom := F
      inv := G
      hom_inv_id := Functor.ext (funext fun x => e.symm_apply_apply x)
      inv_hom_id := Functor.ext (funext fun x => e.apply_symm_apply x) }

attribute [local instance] Cardinal.fact_isRegular_aleph0

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory Limits

namespace FilteredColimit

variable {J : Type u} [Category.{u} J] [IsFiltered J]

lemma omega_truncated (n : ℕ) (F : J ⥤ NCategory.{u} n) :
    (omega (F ⋙ nCategoryInclusion n)).IsTruncated n := by
  intro x
  obtain ⟨j, y, rfl⟩ := exists_rep (F ⋙ nCategoryInclusion n) x
  change source (F ⋙ nCategoryInclusion n) n (ι (F ⋙ nCategoryInclusion n) j y) = _
  rw [source_ι]
  exact congrArg (ι (F ⋙ nCategoryInclusion n) j) ((F.obj j).property y)

noncomputable def nCocone (n : ℕ) (F : J ⥤ NCategory.{u} n) : Cocone F where
  pt := ⟨omega (F ⋙ nCategoryInclusion n), omega_truncated n F⟩
  ι := {
    app := fun j => (cocone (F ⋙ nCategoryInclusion n)).ι.app j
    naturality := fun _ _ f => (cocone (F ⋙ nCategoryInclusion n)).ι.naturality f }

noncomputable def nIsColimit (n : ℕ) (F : J ⥤ NCategory.{u} n) : IsColimit (nCocone n F) where
  desc s := desc (F ⋙ nCategoryInclusion n) ((nCategoryInclusion n).mapCocone s)
  fac s j := (isColimit (F ⋙ nCategoryInclusion n)).fac ((nCategoryInclusion n).mapCocone s) j
  uniq s m h :=
    (isColimit (F ⋙ nCategoryInclusion n)).uniq ((nCategoryInclusion n).mapCocone s) m h

instance nInclusion_preservesFilteredColimit (n : ℕ) (F : J ⥤ NCategory.{u} n) :
    PreservesColimit F (nCategoryInclusion n) :=
  preservesColimit_of_preserves_colimit_cocone (nIsColimit n F)
    (isColimit (F ⋙ nCategoryInclusion n))

end FilteredColimit

attribute [local instance] Cardinal.fact_isRegular_aleph0

instance nInclusion_finitelyAccessible (n : ℕ) :
    (nCategoryInclusion.{u} n).IsCardinalAccessible Cardinal.aleph0.{u} where
  preservesColimitOfShape J _ _ := by
    have := isFiltered_of_isCardinalFiltered J Cardinal.aleph0.{u}
    exact ⟨fun {F} => inferInstance⟩

end Thomason.OmegaCategory

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_HornRealization
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.KanQuillen.boundary_small _root_.OAI.Thomason.KanQuillen.boundary_smallCardinal _root_.OAI.Thomason.KanQuillen.boundary_smallObject _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Horn Realization. -/

noncomputable section
universe u v w z


namespace Thomason.TopologicalHorn

open scoped Topology

lemma continuous_minimum {n : ℕ} (i : Fin (n + 2)) : Continuous (minimum i) := by
  exact Continuous.finset_inf'_apply Finset.univ_nonempty
    (fun k _ => Convexity.StdSimplex.continuous_weights_apply ℝ (i.succAbove k))

noncomputable def retractSimplex {n : ℕ} (i : Fin (n + 2)) :
    C(Simplex (n + 1), Simplex (n + 1)) := by
  classical
  let r (x : Simplex (n + 1)) (j : Fin (n + 2)) :=
    if j = i then x.weights i + (n + 1 : ℝ) * minimum i x else x.weights j - minimum i x
  refine ⟨fun x => ⟨Finsupp.equivFunOnFinite.symm (r x), ?_, ?_⟩, ?_⟩
  · intro j
    dsimp [r]
    split_ifs
    · exact add_nonneg (Convexity.StdSimplex.weights_nonneg i)
        (mul_nonneg (by positivity) (minimum_nonneg i x))
    · exact sub_nonneg.mpr (minimum_le i x j ‹j ≠ i›)
  · rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    change ∑ j, r x j = 1
    rw [Fin.sum_univ_succAbove _ i]
    simp only [r, ite_eq_left rfl, Fin.succAbove_ne, ite_false, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hx := Convexity.StdSimplex.total_of_fintype x
    rw [Fin.sum_univ_succAbove _ i] at hx
    push_cast
    linarith
  · apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).continuous_iff.mpr
    apply continuous_pi
    intro j
    dsimp [r]
    split_ifs
    · exact (Convexity.StdSimplex.continuous_weights_apply ℝ i).add
        ((continuous_minimum i).const_mul _)
    · exact (Convexity.StdSimplex.continuous_weights_apply ℝ j).sub (continuous_minimum i)

lemma retractSimplex_zero {n : ℕ} (i : Fin (n + 2)) (x : Simplex (n + 1)) :
    retractSimplex i x ∈ horn i := by
  obtain ⟨j, hj, hx⟩ := minimum_attained i x
  refine ⟨j, hj, ?_⟩
  change (if j = i then _ else _) = _
  simp only [hj, ite_false, hx, sub_self]

noncomputable def retract {n : ℕ} (i : Fin (n + 2)) :
    C(Simplex (n + 1), horn i) :=
  ⟨fun x => ⟨retractSimplex i x, retractSimplex_zero i x⟩,
    (retractSimplex i).continuous.subtype_mk _⟩

lemma retract_fixed {n : ℕ} (i : Fin (n + 2)) (x : horn i) :
    (retract i x).val = x.val := by
  ext j
  change (if j = i then _ else _) = _
  rw [minimum_eq_zero i x x.property]
  split_ifs with h
  · simp [h]
  · simp

end Thomason.TopologicalHorn

end

noncomputable section
universe u v w z


namespace Thomason.TopologicalHorn

open CategoryTheory

noncomputable def drop {n : ℕ} (j : Fin (n + 2)) :
    C({x : Simplex (n+1) | x.weights j = 0}, Simplex n) := by
  refine ⟨fun x => ⟨Finsupp.equivFunOnFinite.symm (fun k => x.val.weights (j.succAbove k)),
    fun _ => Convexity.StdSimplex.weights_nonneg _, by
    have hx := Convexity.StdSimplex.total_of_fintype x.val
    rw [Fin.sum_univ_succAbove _ j, x.property, zero_add] at hx
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    exact hx⟩, ?_⟩
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous_iff.mpr
  apply continuous_pi
  intro k
  exact (Convexity.StdSimplex.continuous_weights_apply ℝ (j.succAbove k)).comp
    continuous_subtype_val

lemma map_drop {n : ℕ} (j : Fin (n + 2)) (x : Simplex (n+1)) (hx : x.weights j = 0) :
    Convexity.StdSimplex.map j.succAbove (drop j ⟨x,hx⟩) = x := by
  ext k
  by_cases h : k = j
  · subst k
    rw [map_succAbove_pivot, hx]
  · obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq h
    rw [map_succAbove_apply]
    rfl

lemma drop_map {n : ℕ} (j : Fin (n + 2)) (x : Simplex n) :
    drop j ⟨Convexity.StdSimplex.map j.succAbove x, map_succAbove_pivot j x⟩ = x := by
  ext k
  exact map_succAbove_apply j x k

end Thomason.TopologicalHorn

end

noncomputable section
universe u v w z


namespace Thomason.TopologicalHorn

open CategoryTheory Simplicial SimplicialObject

noncomputable def simplexBridge (n : ℕ) : Simplex n ≃ₜ ↥(stdSimplex ℝ (Fin (n + 1))) where
  toEquiv := (OAI.SStd.equivStdSimplex (R := ℝ) (X := Fin (n + 1))).symm
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_pi fun k => ?_
    exact Convexity.StdSimplex.continuous_weights_apply ℝ k
  continuous_invFun := by
    apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous_iff.mpr
    exact continuous_pi fun k => (continuous_apply k).comp continuous_subtype_val

noncomputable def singularValue {X : TopCat.{u}} {n : ℕ}
    (f : (SSet.stdSimplex.obj ⦋n⦌ : SSet.{u}) ⟶ TopCat.toSSet.obj X) : C(Simplex n, X) :=
  (X.toSSetObjEquiv _ (SSet.yonedaEquiv f)).comp ⟨simplexBridge n, (simplexBridge n).continuous⟩

noncomputable def singularEquiv (X : TopCat.{u}) (n : ℕ) :
    ((SSet.stdSimplex.obj ⦋n⦌ : SSet.{u}) ⟶ TopCat.toSSet.obj X) ≃ C(Simplex n, X) where
  toFun := singularValue
  invFun h := SSet.yonedaEquiv.symm
    ((X.toSSetObjEquiv _).symm (h.comp ⟨(simplexBridge n).symm, (simplexBridge n).symm.continuous⟩))
  left_inv g := by
    apply SSet.yonedaEquiv.injective
    simp only [Equiv.apply_symm_apply]
    apply (X.toSSetObjEquiv _).injective
    simp only [Equiv.apply_symm_apply]
    ext y
    simp [singularValue]
  right_inv h := by
    simp only [singularValue, Equiv.apply_symm_apply]
    ext x
    simp

lemma singularValue_delta {X : TopCat.{u}} {n : ℕ}
    (f : (SSet.stdSimplex.obj ⦋n+1⦌ : SSet.{u}) ⟶ TopCat.toSSet.obj X)
    (j : Fin (n+2)) (x : Simplex n) :
    singularValue (SSet.stdSimplex.δ j ≫ f) x =
      singularValue f (Convexity.StdSimplex.map j.succAbove x) := by
  simp only [singularValue, SSet.stdSimplex.yonedaEquiv_δ_comp,
    TopCat.toSSetObjEquiv_δ_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  congr 1
  apply Subtype.ext
  funext k
  simp [simplexBridge, OAI.SStd.equivStdSimplex, OAI.SStd.ofStdSimplex, stdSimplex.map,
    Convexity.StdSimplex.weights_map, Finsupp.mapDomain, Finsupp.sum_fintype]
  simp [FunOnFinite.linearMap_apply_apply, Finsupp.single_apply]
  rw [Finset.sum_filter]
  rfl

lemma singular_faces_agree {X : TopCat.{u}} {n : ℕ} {i : Fin (n+2)}
    (f : ∀ (j : Fin (n+2)) (_ : j ≠ i), (SSet.stdSimplex.obj ⦋n⦌ : SSet.{u}) ⟶ TopCat.toSSet.obj X)
    (hf : SSet.horn.IsCompatible f) (j k : Fin (n+2)) (hj : j ≠ i) (hk : k ≠ i)
    (x : Simplex (n+1)) (hxj : x.weights j = 0) (hxk : x.weights k = 0) :
    singularValue (f j hj) (drop j ⟨x,hxj⟩) = singularValue (f k hk) (drop k ⟨x,hxk⟩) := by
  by_cases he : j = k
  · subst k
    rfl
  suffices h : ∀ (j k : Fin (n+2)) (hj : j ≠ i) (hk : k ≠ i) (hjk : j < k)
      (hxj : x.weights j = 0) (hxk : x.weights k = 0),
      singularValue (f j hj) (drop j ⟨x,hxj⟩) =
        singularValue (f k hk) (drop k ⟨x,hxk⟩) by
    rcases lt_or_gt_of_ne he with hlt | hlt
    · exact h j k hj hk hlt hxj hxk
    · exact (h k j hk hj hlt hxk hxj).symm
  clear j k hj hk hxj hxk he
  intro j k hj hk hjk hxj hxk
  cases n with
  | zero =>
    have hs := Convexity.StdSimplex.total_of_fintype x
    rw [Fin.sum_univ_two] at hs
    fin_cases j <;> fin_cases k <;> norm_num at hjk
    change x.weights 0 = 0 at hxj
    change x.weights 1 = 0 at hxk
    linarith
  | succ n =>
    let b := k.pred (Fin.ne_zero_of_lt hjk)
    let a := j.castPred (Fin.ne_last_of_lt hjk)
    let y := drop j ⟨x,hxj⟩
    have hy : y.weights b = 0 := by
      change x.weights (j.succAbove b) = 0
      simpa only [b, Fin.succAbove_pred_of_lt j k hjk] using hxk
    let z := drop b ⟨y,hy⟩
    have hyz : Convexity.StdSimplex.map b.succAbove z = y := map_drop b y hy
    have hkz : Convexity.StdSimplex.map a.succAbove z = drop k ⟨x,hxk⟩ := by
      apply map_succAbove_injective k
      rw [map_drop, ← double_map j k hjk z, hyz]
      exact map_drop j x hxj
    have heq := congrArg (fun g => singularValue g z) (hf j k hj hk hjk)
    rw [singularValue_delta, singularValue_delta] at heq
    change singularValue (f j hj) (Convexity.StdSimplex.map b.succAbove z) =
      singularValue (f k hk) (Convexity.StdSimplex.map a.succAbove z) at heq
    rwa [hyz, hkz] at heq

noncomputable def hornValue {X : TopCat.{u}} {n : ℕ} {i : Fin (n+2)}
    (f : ∀ (j : Fin (n+2)) (_ : j ≠ i), (SSet.stdSimplex.obj ⦋n⦌ : SSet.{u}) ⟶ TopCat.toSSet.obj X)
    (hf : SSet.horn.IsCompatible f) : C(horn i, X) :=
  closedCoverPaste (fun j : {j : Fin (n+2) // j ≠ i} => {x | x.val.weights j.val = 0})
    (fun j => isClosed_eq ((Convexity.StdSimplex.continuous_weights_apply ℝ j.val).comp
      continuous_subtype_val) continuous_const)
    (fun x => by obtain ⟨j,hj,hx⟩ := x.property; exact ⟨⟨j,hj⟩,hx⟩)
    (fun j => (singularValue (f j.val j.property)).comp
      ((drop j.val).comp ⟨fun x => ⟨x.val.val,x.property⟩,
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩))
    (fun j k x hj hk => singular_faces_agree f hf j.val k.val j.property k.property x.val hj hk)

lemma hornValue_face {X : TopCat.{u}} {n : ℕ} {i : Fin (n+2)}
    (f : ∀ (j : Fin (n+2)) (_ : j ≠ i), (SSet.stdSimplex.obj ⦋n⦌ : SSet.{u}) ⟶ TopCat.toSSet.obj X)
    (hf : SSet.horn.IsCompatible f) (j : Fin (n+2)) (hj : j ≠ i) (x : Simplex n) :
    hornValue f hf ⟨Convexity.StdSimplex.map j.succAbove x, j, hj, map_succAbove_pivot j x⟩ =
      singularValue (f j hj) x := by
  rw [hornValue, closedCoverPaste_apply (j := ⟨j,hj⟩) (ha := map_succAbove_pivot j x)]
  change singularValue (f j hj)
    (drop j ⟨Convexity.StdSimplex.map j.succAbove x, map_succAbove_pivot j x⟩) = _
  rw [drop_map]

theorem singular_kan (X : TopCat.{u}) : SSet.KanComplex (TopCat.toSSet.obj X) := by
  rw [SSet.KanComplex.iff]
  intro n i f hf
  let h : C(Simplex (n+1), X) := (hornValue f hf).comp (retract i)
  let φ := SSet.yonedaEquiv.symm ((X.toSSetObjEquiv _).symm (h.comp ⟨(simplexBridge (n+1)).symm, (simplexBridge (n+1)).symm.continuous⟩))
  have hφ : singularValue φ = h := by
    simp only [singularValue, φ, Equiv.apply_symm_apply]
    ext x
    simp
  refine ⟨φ, ?_⟩
  intro j hj
  apply SSet.yonedaEquiv.injective
  apply (X.toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro y
  obtain ⟨x, rfl⟩ := (simplexBridge n).surjective y
  change singularValue (SSet.stdSimplex.δ j ≫ φ) x = singularValue (f j hj) x
  rw [singularValue_delta, hφ]
  change hornValue f hf (retract i (Convexity.StdSimplex.map j.succAbove x)) = _
  have hx : Convexity.StdSimplex.map j.succAbove x ∈ horn i := ⟨j,hj,map_succAbove_pivot j x⟩
  have he : retract i (Convexity.StdSimplex.map j.succAbove x) = ⟨_,hx⟩ :=
    Subtype.ext (retract_fixed i ⟨_,hx⟩)
  rw [he]
  exact hornValue_face f hf j hj x

end Thomason.TopologicalHorn

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SubdivisionMaps
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subdivision Maps. -/

noncomputable section
universe u v w z


namespace Thomason.TopologicalHorn

open scoped Topology unitInterval

lemma minimum_le_one {n : ℕ} (i : Fin (n+2)) (x : Simplex (n+1)) : minimum i x ≤ 1 := by
  obtain ⟨j, hj, he⟩ := minimum_attained i x
  rw [he]
  exact (Finset.single_le_sum (fun k _ => Convexity.StdSimplex.weights_nonneg k)
    (Finset.mem_univ j)).trans_eq (Convexity.StdSimplex.total_of_fintype x)

lemma prismDenominator_pos {n : ℕ} (i : Fin (n+2)) (q : I × Simplex (n+1)) :
    0 < prismDenominator i q := by
  have : (1:ℝ)/2 ≤ 1 - minimum i q.2 / 2 := by linarith [minimum_le_one i q.2]
  exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) (this.trans (le_max_left _ _))

lemma continuous_prismDenominator {n : ℕ} (i : Fin (n+2)) : Continuous (prismDenominator i) :=
  (continuous_const.sub ((continuous_minimum i).comp continuous_snd |>.div_const 2)).max
    (((continuous_subtype_val.comp continuous_fst).const_mul 2).sub continuous_const).abs

noncomputable def prismTime {n : ℕ} (i : Fin (n+2)) (q : I × Simplex (n+1)) : I :=
  ⟨1/2 + ((q.1 : ℝ)-1/2) / prismDenominator i q, by
    have hd := prismDenominator_pos i q
    have ha := abs_le.mp (le_max_right (1 - minimum i q.2 / 2) |2 * (q.1:ℝ) - 1|)
    change -prismDenominator i q ≤ _ ∧ _ ≤ prismDenominator i q at ha
    constructor
    · have : (-1/2 : ℝ) ≤ ((q.1:ℝ)-1/2) / prismDenominator i q :=
        (le_div_iff₀ hd).mpr (by linarith [ha.1])
      linarith
    · have : ((q.1:ℝ)-1/2) / prismDenominator i q ≤ (1/2 : ℝ) :=
        (div_le_iff₀ hd).mpr (by linarith [ha.2])
      linarith⟩

noncomputable def prismSpace {n : ℕ} (i : Fin (n+2)) :
    C(I × Simplex (n+1), Simplex (n+1)) := by
  classical
  let r (q : I × Simplex (n+1)) (j : Fin (n+2)) :=
    (if j = i then q.2.weights i + (2*(n+1:ℝ)-1)*(1-prismDenominator i q)
      else q.2.weights j - 2*(1-prismDenominator i q)) / prismDenominator i q
  refine ⟨fun q => ⟨Finsupp.equivFunOnFinite.symm (r q), ?_, ?_⟩, ?_⟩
  · intro j
    dsimp [r]
    apply div_nonneg _ (prismDenominator_pos i q).le
    split_ifs with he
    · exact add_nonneg (Convexity.StdSimplex.weights_nonneg _) (mul_nonneg (by have h := Nat.cast_nonneg (α := ℝ) n; linarith)
        (sub_nonneg.mpr (prismDenominator_le_one i q)))
    · have hmin := minimum_le i q.2 j he
      have hd : 1 - minimum i q.2/2 ≤ prismDenominator i q := le_max_left _ _
      linarith
  · rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    change ∑ j, r q j = 1
    rw [Fin.sum_univ_succAbove _ i]
    simp only [r, Fin.succAbove_ne, ite_false, ← Finset.sum_div,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← add_div]
    apply (div_eq_one_iff_eq (ne_of_gt (prismDenominator_pos i q))).mpr
    have hx := Convexity.StdSimplex.total_of_fintype q.2
    rw [Fin.sum_univ_succAbove _ i] at hx
    push_cast
    nlinarith
  · apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+2))).continuous_iff.mpr
    apply continuous_pi
    intro j
    dsimp [r]
    apply Continuous.div _ (continuous_prismDenominator i) (fun q => ne_of_gt (prismDenominator_pos i q))
    split_ifs
    · exact ((Convexity.StdSimplex.continuous_weights_apply ℝ i).comp continuous_snd).add
        ((continuous_const.sub (continuous_prismDenominator i)).const_mul _)
    · exact ((Convexity.StdSimplex.continuous_weights_apply ℝ j).comp continuous_snd).sub
        ((continuous_const.sub (continuous_prismDenominator i)).const_mul _)

lemma continuous_prismTime {n : ℕ} (i : Fin (n+2)) : Continuous (prismTime i) := by
  apply Continuous.subtype_mk
  exact continuous_const.add (((continuous_subtype_val.comp continuous_fst).sub continuous_const).div
    (continuous_prismDenominator i) (fun q => ne_of_gt (prismDenominator_pos i q)))

lemma prism_mem_roof {n : ℕ} (i : Fin (n+2)) (q : I × Simplex (n+1)) :
    (prismTime i q, prismSpace i q) ∈ prismRoof i := by
  have hd := prismDenominator_pos i q
  rcases le_total |2*(q.1:ℝ)-1| (1-minimum i q.2/2) with h | h
  · right; right
    have he : prismDenominator i q = 1-minimum i q.2/2 := max_eq_left h
    obtain ⟨j, hj, hjx⟩ := minimum_attained i q.2
    refine ⟨j,hj,?_⟩
    change (if j = i then q.2.weights i + (2*(n+1:ℝ)-1)*(1-prismDenominator i q)
      else q.2.weights j - 2*(1-prismDenominator i q)) / prismDenominator i q = 0
    simp only [hj, ite_false, he]
    rw [← hjx]
    ring
  · have he : prismDenominator i q = |2*(q.1:ℝ)-1| := max_eq_right h
    rcases (abs_eq hd.le).mp he.symm with hq | hq
    · right; left
      apply Subtype.ext
      change 1/2 + ((q.1:ℝ)-1/2)/prismDenominator i q = 1
      have : ((q.1:ℝ)-1/2)/prismDenominator i q = (1/2 : ℝ) :=
        (div_eq_iff (ne_of_gt hd)).mpr (by linarith)
      rw [this]; norm_num
    · left
      apply Subtype.ext
      change 1/2 + ((q.1:ℝ)-1/2)/prismDenominator i q = 0
      have : ((q.1:ℝ)-1/2)/prismDenominator i q = (-1/2 : ℝ) :=
        (div_eq_iff (ne_of_gt hd)).mpr (by linarith)
      rw [this]; norm_num

noncomputable def prismRetract {n : ℕ} (i : Fin (n+2)) : C(I × Simplex (n+1), prismRoof i) :=
  ⟨fun q => ⟨(prismTime i q, prismSpace i q), prism_mem_roof i q⟩,
    ((continuous_prismTime i).prodMk (prismSpace i).continuous).subtype_mk _⟩

lemma prismRetract_fixed {n : ℕ} (i : Fin (n+2)) (q : prismRoof i) :
    (prismRetract i q).val = q.val := by
  have he : prismDenominator i q = 1 := by
    apply le_antisymm (prismDenominator_le_one i q)
    rcases q.property with h | h | h
    · have : |2 * (q.val.1 : ℝ) - 1| = 1 := by rw [h]; norm_num
      exact this ▸ le_max_right _ _
    · have : |2 * (q.val.1 : ℝ) - 1| = 1 := by rw [h]; norm_num
      exact this ▸ le_max_right _ _
    · have : 1 - minimum i q.val.2 / 2 = 1 := by rw [minimum_eq_zero i _ h]; norm_num
      exact this ▸ le_max_left _ _
  apply Prod.ext
  · apply Subtype.ext
    change 1/2 + ((q.val.1:ℝ)-1/2)/prismDenominator i q = (q.val.1:ℝ)
    rw [he, div_one]; ring
  · ext j
    change (if j = i then _ else _) / prismDenominator i q = q.val.2.weights j
    rw [he]
    split_ifs with hj
    · rw [hj]; ring
    · ring

end Thomason.TopologicalHorn

end

noncomputable section
universe u v w z


namespace Thomason.TopologicalHorn

open scoped Topology unitInterval

lemma isClosed_horn {n : ℕ} (i : Fin (n+2)) : IsClosed (horn i) := by
  have he : horn i = {x | minimum i x = 0} := by
    ext x
    constructor
    · exact minimum_eq_zero i x
    · intro hx
      obtain ⟨j,hj,hmin⟩ := minimum_attained i x
      exact ⟨j,hj,hmin.symm.trans hx⟩
  rw [he]
  exact isClosed_eq (continuous_minimum i) continuous_const

lemma isClosed_roofPiece {n : ℕ} (i : Fin (n+2)) (b : Option Bool) :
    IsClosed (roofPiece i b) := by
  cases b with
  | none => exact (isClosed_horn i).preimage (continuous_snd.comp continuous_subtype_val)
  | some b => exact isClosed_eq (continuous_fst.comp continuous_subtype_val) continuous_const

variable {X : Type u} [TopologicalSpace X] {n : ℕ} {i : Fin (n+2)}

noncomputable def roofPieceValue (a b : C(Simplex (n+1),X)) (H : C(I × horn i,X)) :
    ∀ k, C(roofPiece i k,X)
  | none => H.comp ⟨fun q => (q.val.val.1,⟨q.val.val.2,q.property⟩),
      (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).prodMk
        ((continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _)⟩
  | some k => (if k then b else a).comp
      ⟨fun q => q.val.val.2, continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)⟩

lemma roofPieceValue_agree (a b : C(Simplex (n+1),X)) (H : C(I × horn i,X))
    (ha : ∀ x : horn i, H (0,x) = a x) (hb : ∀ x : horn i, H (1,x) = b x)
    (j k : Option Bool) (q : prismRoof i) (hj : q ∈ roofPiece i j) (hk : q ∈ roofPiece i k) :
    roofPieceValue a b H j ⟨q,hj⟩ = roofPieceValue a b H k ⟨q,hk⟩ := by
  cases j with
  | none =>
    cases k with
    | none => rfl
    | some k =>
      cases k
      · change H (q.val.1,⟨q.val.2,hj⟩) = a q.val.2
        rw [show q.val.1 = 0 from hk]
        exact ha _
      · change H (q.val.1,⟨q.val.2,hj⟩) = b q.val.2
        rw [show q.val.1 = 1 from hk]
        exact hb _
  | some j =>
    cases k with
    | none =>
      cases j
      · change a q.val.2 = H (q.val.1,⟨q.val.2,hk⟩)
        rw [show q.val.1 = 0 from hj]
        exact (ha ⟨q.val.2,hk⟩).symm
      · change b q.val.2 = H (q.val.1,⟨q.val.2,hk⟩)
        rw [show q.val.1 = 1 from hj]
        exact (hb ⟨q.val.2,hk⟩).symm
    | some k =>
      cases j <;> cases k
      · rfl
      · exact (zero_ne_one (hj.symm.trans hk)).elim
      · exact (zero_ne_one (hk.symm.trans hj)).elim
      · rfl

noncomputable def roofValue (a b : C(Simplex (n+1),X)) (H : C(I × horn i,X))
    (ha : ∀ x : horn i, H (0,x) = a x) (hb : ∀ x : horn i, H (1,x) = b x) : C(prismRoof i,X) :=
  closedCoverPaste (roofPiece i) (isClosed_roofPiece i) (roofPiece_cover i)
    (roofPieceValue a b H) (roofPieceValue_agree a b H ha hb)

noncomputable def prismExtend (a b : C(Simplex (n+1),X)) (H : C(I × horn i,X))
    (ha : ∀ x : horn i, H (0,x) = a x) (hb : ∀ x : horn i, H (1,x) = b x) : C(I × Simplex (n+1),X) :=
  (roofValue a b H ha hb).comp (prismRetract i)

lemma prismExtend_onRoof (a b : C(Simplex (n+1),X)) (H : C(I × horn i,X))
    (ha : ∀ x : horn i, H (0,x) = a x) (hb : ∀ x : horn i, H (1,x) = b x) (q : prismRoof i) :
    prismExtend a b H ha hb q = roofValue a b H ha hb q :=
  congrArg (roofValue a b H ha hb) (Subtype.ext (prismRetract_fixed i q))

lemma prismExtend_zero (a b : C(Simplex (n+1),X)) (H : C(I × horn i,X))
    (ha : ∀ x : horn i, H (0,x) = a x) (hb : ∀ x : horn i, H (1,x) = b x) (x : Simplex (n+1)) :
    prismExtend a b H ha hb (0,x) = a x := by
  rw [prismExtend_onRoof a b H ha hb ⟨(0,x),Or.inl rfl⟩]
  exact closedCoverPaste_apply (roofPiece i) (isClosed_roofPiece i) (roofPiece_cover i)
    (roofPieceValue a b H) (roofPieceValue_agree a b H ha hb) (some false) _ rfl

lemma prismExtend_one (a b : C(Simplex (n+1),X)) (H : C(I × horn i,X))
    (ha : ∀ x : horn i, H (0,x) = a x) (hb : ∀ x : horn i, H (1,x) = b x) (x : Simplex (n+1)) :
    prismExtend a b H ha hb (1,x) = b x := by
  rw [prismExtend_onRoof a b H ha hb ⟨(1,x),Or.inr (Or.inl rfl)⟩]
  exact closedCoverPaste_apply (roofPiece i) (isClosed_roofPiece i) (roofPiece_cover i)
    (roofPieceValue a b H) (roofPieceValue_agree a b H ha hb) (some true) _ rfl

lemma prismExtend_side (a b : C(Simplex (n+1),X)) (H : C(I × horn i,X))
    (ha : ∀ x : horn i, H (0,x) = a x) (hb : ∀ x : horn i, H (1,x) = b x) (t : I) (x : horn i) :
    prismExtend a b H ha hb (t,x) = H (t,x) := by
  rw [prismExtend_onRoof a b H ha hb ⟨(t,x),Or.inr (Or.inr x.property)⟩]
  exact closedCoverPaste_apply (roofPiece i) (isClosed_roofPiece i) (roofPiece_cover i)
    (roofPieceValue a b H) (roofPieceValue_agree a b H ha hb) none _ x.property

end Thomason.TopologicalHorn

end

noncomputable section
universe u v w z


namespace Thomason.TopologicalHorn

open CategoryTheory Simplicial
open scoped Topology unitInterval

lemma singularValue_post {X Y : TopCat.{u}} {n : ℕ}
    (f : (SSet.stdSimplex.obj ⦋n⦌ : SSet.{u}) ⟶ TopCat.toSSet.obj X) (p : X ⟶ Y)
    (x : Simplex n) : singularValue (f ≫ TopCat.toSSet.map p) x = p (singularValue f x) := rfl

lemma hornValue_square {X Y : TopCat.{u}} {n : ℕ} {i : Fin (n+2)}
    (g : (SSet.horn (n+1) i : SSet.{u}) ⟶ TopCat.toSSet.obj X)
    (f : (SSet.stdSimplex.obj ⦋n+1⦌ : SSet.{u}) ⟶ TopCat.toSSet.obj Y) (p : X ⟶ Y)
    (h : g ≫ TopCat.toSSet.map p = (SSet.horn (n+1) i).ι ≫ f) (x : horn i) :
    p (hornValue (fun j hj => SSet.horn.ι i j hj ≫ g) (SSet.horn.IsCompatible.of_hom g) x) =
      singularValue f x := by
  obtain ⟨j,hj,hx⟩ := x.property
  let y := drop j ⟨x.val,hx⟩
  have he : (⟨Convexity.StdSimplex.map j.succAbove y,j,hj,map_succAbove_pivot j y⟩ : horn i) = x :=
    Subtype.ext (map_drop j x hx)
  rw [← he, hornValue_face]
  have hh : (SSet.horn.ι i j hj ≫ g) ≫ TopCat.toSSet.map p = SSet.stdSimplex.δ j ≫ f := by
    rw [Category.assoc, h, SSet.horn.ι_ι_assoc]
  simpa only [singularValue_post, singularValue_delta] using congrArg (fun φ => singularValue φ y) hh

theorem singular_path_fibration (T : TopCat.{u}) :
    SSet.modelCategoryQuillen.J.rlp (TopCat.toSSet.map (pathEndpoints T)) := by
  intro A B i hi
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hi
  obtain ⟨n,⟨k⟩⟩ := hi
  constructor
  intro g f sq
  let F := fun j hj => SSet.horn.ι k j hj ≫ g
  have hF : SSet.horn.IsCompatible F := SSet.horn.IsCompatible.of_hom g
  let H : C(I × horn k,T) := (hornValue F hF).uncurry.comp ⟨Prod.swap,continuous_swap⟩
  let a : C(Simplex (n+1),T) := ContinuousMap.fst.comp (singularValue f)
  let b : C(Simplex (n+1),T) := ContinuousMap.snd.comp (singularValue f)
  have ha (x : horn k) : H (0,x) = a x :=
    congrArg Prod.fst (hornValue_square g f (pathEndpoints T) sq.w x)
  have hb (x : horn k) : H (1,x) = b x :=
    congrArg Prod.snd (hornValue_square g f (pathEndpoints T) sq.w x)
  let h : C(Simplex (n+1),C(I,T)) :=
    ((prismExtend a b H ha hb).comp ⟨Prod.swap,continuous_swap⟩).curry
  let φ := (singularEquiv (PathSpace T) _).symm h
  have hφ : singularValue φ = h := (singularEquiv (PathSpace T) _).apply_symm_apply h
  refine ⟨⟨{ l := φ, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply SSet.horn.hom_ext'
    intro j hj
    rw [SSet.horn.ι_ι_assoc]
    apply (singularEquiv (PathSpace T) _).injective
    apply ContinuousMap.ext
    intro x
    apply ContinuousMap.ext
    intro t
    change singularValue (SSet.stdSimplex.δ j ≫ φ) x t = singularValue (F j hj) x t
    rw [singularValue_delta, hφ]
    change prismExtend a b H ha hb (t,Convexity.StdSimplex.map j.succAbove x) = _
    rw [prismExtend_side a b H ha hb t
      ⟨Convexity.StdSimplex.map j.succAbove x,j,hj,map_succAbove_pivot j x⟩]
    change hornValue F hF ⟨Convexity.StdSimplex.map j.succAbove x,j,hj,map_succAbove_pivot j x⟩ t = _
    rw [hornValue_face]
  · apply (singularEquiv (EndpointSpace T) _).injective
    apply ContinuousMap.ext
    intro x
    change singularValue (φ ≫ TopCat.toSSet.map (pathEndpoints T)) x = singularValue f x
    rw [singularValue_post,hφ]
    apply Prod.ext
    · exact prismExtend_zero a b H ha hb x
    · exact prismExtend_one a b H ha hb x

end Thomason.TopologicalHorn

end

noncomputable section
universe u v w z


namespace Thomason.TopologicalHorn

open CategoryTheory Limits HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Topology unitInterval

lemma anodyne_top_extension {A B : SSet.{u}} (i : A ⟶ B) (hi : SSet.anodyneExtensions i)
    (Z : TopCat.{u}) (f : SSet.toTop.obj A ⟶ Z) :
    ∃ g : SSet.toTop.obj B ⟶ Z, SSet.toTop.map i ≫ g = f := by
  let : SSet.KanComplex (TopCat.toSSet.obj Z) := singular_kan Z
  have hp : SSet.modelCategoryQuillen.J.rlp (terminal.from (TopCat.toSSet.obj Z)) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance
  let : HasLiftingProperty i (terminal.from (TopCat.toSSet.obj Z)) := hi _ hp
  have sq : CommSq ((sSetTopAdj.homEquiv _ _) f) i
      (terminal.from (TopCat.toSSet.obj Z)) (terminal.from B) := ⟨Subsingleton.elim _ _⟩
  refine ⟨(sSetTopAdj.homEquiv _ _).symm sq.lift, ?_⟩
  apply (sSetTopAdj.homEquiv _ _).injective
  rw [sSetTopAdj.homEquiv_naturality_left, Equiv.apply_symm_apply]
  exact sq.fac_left

theorem anodyne_weak_equivalence {A B : SSet.{u}} (i : A ⟶ B) (hi : SSet.anodyneExtensions i) :
    simplicialWeakEquivalences i := by
  let j := SSet.toTop.map i
  obtain ⟨r,hr⟩ := anodyne_top_extension i hi (SSet.toTop.obj A) (𝟙 _)
  have hre (a : SSet.toTop.obj A) : r (j a) = a := ConcreteCategory.congr_hom hr a
  let f : SSet.toTop.obj A ⟶ PathSpace (SSet.toTop.obj B) :=
    TopCat.ofHom (ContinuousMap.const'.comp j.hom)
  let g : SSet.toTop.obj B ⟶ EndpointSpace (SSet.toTop.obj B) :=
    TopCat.ofHom ⟨fun b => (j (r b),b), (j.hom.continuous.comp r.hom.continuous).prodMk continuous_id⟩
  have sq : CommSq f j (pathEndpoints (SSet.toTop.obj B)) g := by
    constructor
    apply ConcreteCategory.hom_ext
    intro a
    change (j a,j a) = (j (r (j a)),j a)
    rw [hre]
  let : HasLiftingProperty j (pathEndpoints (SSet.toTop.obj B)) :=
    (sSetTopAdj.hasLiftingProperty_iff i _).mpr (hi _ (singular_path_fibration _))
  have hzero (b : SSet.toTop.obj B) : sq.lift b 0 = j (r b) :=
    congrArg Prod.fst (ConcreteCategory.congr_hom sq.fac_right b)
  have hone (b : SSet.toTop.obj B) : sq.lift b 1 = b :=
    congrArg Prod.snd (ConcreteCategory.congr_hom sq.fac_right b)
  have hfixed (a : SSet.toTop.obj A) (t : I) : sq.lift (j a) t = j a :=
    congrArg (fun γ : C(I,SSet.toTop.obj B) => γ t) (ConcreteCategory.congr_hom sq.fac_left a)
  apply WeakHomotopy.equivalence_of_strong_retract j.hom r.hom
    (congrArg TopCat.Hom.hom hr)
  refine ⟨{ toHomotopy :=
    { toFun := fun q => sq.lift q.2 q.1
      continuous_toFun := ?_
      map_zero_left := hzero
      map_one_left := hone }
            prop' := ?_ }⟩
  · exact continuous_eval.comp ((sq.lift.hom.continuous.comp continuous_snd).prodMk continuous_fst)
  · rintro t b ⟨a,rfl⟩
    change sq.lift (j a) t = j (r (j a))
    rw [hre]
    exact hfixed a t

end Thomason.TopologicalHorn

end

noncomputable section
universe u v w z


namespace Thomason.SimplicialCylinder

open CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory Limits

lemma endpoint_weak (X : SSet.{u}) :
    simplicialWeakEquivalences (SSet.ι₀ (X := X)) ∧
    simplicialWeakEquivalences (SSet.ι₁ (X := X)) :=
  ⟨TopologicalHorn.anodyne_weak_equivalence _ (endpoint_anodyne X).1,
   TopologicalHorn.anodyne_weak_equivalence _ (endpoint_anodyne X).2⟩

end Thomason.SimplicialCylinder

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SubdivisionNerves
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subdivision Nerves. -/

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder Limits

variable {E : Type u} {F : Type u} [PartialOrder E] [PartialOrder F]

noncomputable def sdNerveSimplexLeg {n : ℕ} (s : (nerve E) _⦋n⦌) :
    SimplexCategory.sd.obj ⦋n⦌ ⟶ nerve (NonemptyFiniteChains E) :=
  PartOrd.nerveFunctor.map (PartOrd.ofHom
    (NonemptyFiniteChains.orderHomMap (simplexVertices s)))

lemma sdNerveSimplexLeg_naturality {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌)
    (s : (nerve E) _⦋m⦌) :
    SimplexCategory.sd.map f ≫ sdNerveSimplexLeg s =
      sdNerveSimplexLeg ((nerve E).map f.op s) := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  apply nerve.ext_of_isThin
  funext j
  apply NonemptyFiniteChains.ext
  classical
  change Finset.image _ (Finset.image _ _) = Finset.image _ _
  rw [Finset.image_image]
  rfl

lemma sdNerveMap_fac_any {n : ℕ} (s : (nerve E) _⦋n⦌) :
    SSet.sd.map (SSet.yonedaEquiv.symm s) ≫ sdNerveMap =
      (SSet.stdSimplex.sdIso.app ⦋n⦌).hom ≫ sdNerveSimplexLeg s := by
  obtain ⟨m, φ, _, t, rfl⟩ := (nerve E).exists_nonDegenerate s
  rw [← SSet.yonedaEquiv_symm_naturality_left, SSet.sd.map_comp, Category.assoc]
  erw [sdNerveMap_fac (SSet.N.mk t.val t.property)]
  erw [← Category.assoc, SSet.stdSimplex.sdIso.hom.naturality, Category.assoc]
  change (SSet.stdSimplex.sdIso.app ⦋n⦌).hom ≫
      (SimplexCategory.sd.map φ ≫ sdNerveSimplexLeg t.val) = _
  rw [sdNerveSimplexLeg_naturality]

lemma sdNerveSimplexLeg_comp {n : ℕ} (s : (nerve E) _⦋n⦌) (f : E →o F) :
    sdNerveSimplexLeg s ≫ PartOrd.nerveFunctor.map
      (PartOrd.ofHom (NonemptyFiniteChains.orderHomMap f)) =
    sdNerveSimplexLeg ((nerveMap f.monotone.functor).app _ s) := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  apply nerve.ext_of_isThin
  funext j
  apply NonemptyFiniteChains.ext
  classical
  change Finset.image _ (Finset.image _ _) = Finset.image _ _
  rw [Finset.image_image]
  rfl

lemma sdNerveMap_naturality (f : E →o F) :
    SSet.sd.map (nerveMap f.monotone.functor) ≫ sdNerveMap =
      sdNerveMap ≫ PartOrd.nerveFunctor.map
        (PartOrd.ofHom (NonemptyFiniteChains.orderHomMap f)) := by
  apply (isColimitOfPreserves SSet.sd (nerve E).isColimitCoconeN').hom_ext
  intro s
  change SSet.sd.map (SSet.yonedaEquiv.symm s.simplex) ≫
      (SSet.sd.map (nerveMap f.monotone.functor) ≫ sdNerveMap) =
    SSet.sd.map (SSet.yonedaEquiv.symm s.simplex) ≫ (sdNerveMap ≫ _)
  erw [← Category.assoc, ← SSet.sd.map_comp, SSet.yonedaEquiv_symm_comp,
    sdNerveMap_fac_any, ← Category.assoc, sdNerveMap_fac, Category.assoc]
  exact congrArg ((SSet.stdSimplex.sdIso.app ⦋s.dim⦌).hom ≫ ·)
    (sdNerveSimplexLeg_comp s.simplex f).symm

end Thomason.Subdivision

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_GlobularComplexes
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Globular Complexes. -/

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder Limits

variable {X : Type u} [PartialOrder X]

variable {E : Type u} [PartialOrder E] (K : (nerve E).Subcomplex)

noncomputable def sdTwiceSubcomplexIso :
    (SSet.sd ⋙ SSet.sd).obj (K : SSet.{u}) ≅
      nerve (NonemptyFiniteChains (AllowedChains K)) :=
  SSet.sd.mapIso (sdSubcomplexIso K) ≪≫ sdNerveIso

noncomputable def sdTwiceNerveIso :
    (SSet.sd ⋙ SSet.sd).obj (nerve E) ≅
      nerve (NonemptyFiniteChains (NonemptyFiniteChains E)) :=
  SSet.sd.mapIso sdNerveIso ≪≫ sdNerveIso

lemma sdTwiceSubcomplexIso_naturality :
    (SSet.sd ⋙ SSet.sd).map K.ι ≫ (sdTwiceNerveIso (E := E)).hom =
      (sdTwiceSubcomplexIso K).hom ≫ PartOrd.nerveFunctor.map
        (PartOrd.ofHom (NonemptyFiniteChains.orderHomMap
          (⟨Subtype.val, fun _ _ h => h⟩ : AllowedChains K →o NonemptyFiniteChains E))) := by
  change SSet.sd.map (SSet.sd.map K.ι) ≫ (SSet.sd.map sdNerveMap ≫ sdNerveMap) =
    (SSet.sd.map (sdSubcomplexMap K) ≫ sdNerveMap) ≫ _
  rw [← Category.assoc, ← SSet.sd.map_comp, sdSubcomplexMap_naturality,
    SSet.sd.map_comp, Category.assoc]
  change SSet.sd.map (sdSubcomplexMap K) ≫
      (SSet.sd.map (nerveMap (⟨Subtype.val, fun _ _ h => h⟩ :
        AllowedChains K →o NonemptyFiniteChains E).monotone.functor) ≫ sdNerveMap) = _
  rw [sdNerveMap_naturality]
  erw [← Category.assoc]

noncomputable def sdTwiceSimplexSubcomplexIso {m : ℕ}
    (K : (SSet.stdSimplex.{u}.obj ⦋m⦌).Subcomplex) :
    (SSet.sd ⋙ SSet.sd).obj (K : SSet.{u}) ≅
      nerve (NonemptyFiniteChains (AllowedChains (orderedSimplexSubcomplex K))) :=
  (SSet.sd ⋙ SSet.sd).mapIso (orderedSimplexSubcomplexIso K) ≪≫
    sdTwiceSubcomplexIso (orderedSimplexSubcomplex K)

noncomputable def sdTwiceSimplexIso (m : ℕ) :
    (SSet.sd ⋙ SSet.sd).obj (SSet.stdSimplex.{u}.obj ⦋m⦌) ≅
      nerve (NonemptyFiniteChains (NonemptyFiniteChains (ULift.{u} (Fin (m+1))))) :=
  (SSet.sd ⋙ SSet.sd).mapIso (SSet.stdSimplex.isoNerve.{u} m) ≪≫ sdTwiceNerveIso

lemma sdTwiceSimplexSubcomplexIso_naturality {m : ℕ}
    (K : (SSet.stdSimplex.{u}.obj ⦋m⦌).Subcomplex) :
    (SSet.sd ⋙ SSet.sd).map K.ι ≫ (sdTwiceSimplexIso m).hom =
      (sdTwiceSimplexSubcomplexIso K).hom ≫ PartOrd.nerveFunctor.map
        (PartOrd.ofHom (NonemptyFiniteChains.orderHomMap
          (⟨Subtype.val, fun _ _ h => h⟩ : AllowedChains (orderedSimplexSubcomplex K) →o
            NonemptyFiniteChains (ULift.{u} (Fin (m+1)))))) := by
  change _ ≫ (_ ≫ _) = (_ ≫ _) ≫ _
  simp only [Functor.mapIso_hom]
  erw [← Category.assoc, ← Functor.map_comp]
  have h : K.ι ≫ (SSet.stdSimplex.isoNerve.{u} m).hom =
      (orderedSimplexSubcomplexIso K).hom ≫ (orderedSimplexSubcomplex K).ι := rfl
  erw [h, Functor.map_comp, Category.assoc, sdTwiceSubcomplexIso_naturality, ← Category.assoc]

end Thomason.Subdivision

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_BoundaryQuotients
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary Quotients. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

def boundarySetoid (C : OmegaCategory.{u}) (n : ℕ) : Setoid C.Cell where
  r x y := C.source n x = C.source n y ∧ C.target n x = C.target n y
  iseqv := ⟨fun _ => ⟨rfl,rfl⟩, fun h => ⟨h.1.symm,h.2.symm⟩,
    fun h h' => ⟨h.1.trans h'.1,h.2.trans h'.2⟩⟩

namespace BoundaryQuotient
variable (C : OmegaCategory.{u}) (n : ℕ)
abbrev Cell := Quotient (boundarySetoid C n)
def map (x : C.Cell) : Cell C n := Quotient.mk _ x
lemma map_eq_iff (x y : C.Cell) : map C n x = map C n y ↔
    C.source n x = C.source n y ∧ C.target n x = C.target n y := Quotient.eq
lemma surjective : Function.Surjective (map C n) := Quotient.mk_surjective

lemma source_respects (k : ℕ) {x y : C.Cell}
    (h : C.source n x = C.source n y ∧ C.target n x = C.target n y) :
    C.source n (C.source k x) = C.source n (C.source k y) ∧
      C.target n (C.source k x) = C.target n (C.source k y) := by
  by_cases hk : n < k
  · simpa [C.source_source, C.target_source, hk, min_eq_left (le_of_lt hk)] using h
  · have hs : C.source k x = C.source k y := by
      simpa [C.source_source, min_eq_left (Nat.le_of_not_gt hk)] using congrArg (C.source k) h.1
    exact ⟨congrArg (C.source n) hs, congrArg (C.target n) hs⟩

lemma target_respects (k : ℕ) {x y : C.Cell}
    (h : C.source n x = C.source n y ∧ C.target n x = C.target n y) :
    C.source n (C.target k x) = C.source n (C.target k y) ∧
      C.target n (C.target k x) = C.target n (C.target k y) := by
  by_cases hk : n < k
  · simpa [C.source_target, C.target_target, hk, min_eq_left (le_of_lt hk)] using h
  · have ht : C.target k x = C.target k y := by
      simpa [C.target_target, min_eq_left (Nat.le_of_not_gt hk)] using congrArg (C.target k) h.2
    exact ⟨congrArg (C.source n) ht, congrArg (C.target n) ht⟩

def source (k : ℕ) : Cell C n → Cell C n := Quotient.map (C.source k) (fun _ _ h => source_respects C n k h)
def target (k : ℕ) : Cell C n → Cell C n := Quotient.map (C.target k) (fun _ _ h => target_respects C n k h)
@[simp] lemma source_map (k : ℕ) (x : C.Cell) : source C n k (map C n x) = map C n (C.source k x) := rfl
@[simp] lemma target_map (k : ℕ) (x : C.Cell) : target C n k (map C n x) = map C n (C.target k x) := rfl

lemma source_high (k : ℕ) (hk : n < k) (x : Cell C n) : source C n k x = x := by
  induction x using Quotient.inductionOn with | h x =>
    apply (map_eq_iff C n _ _).mpr
    simp [C.source_source, C.target_source, hk, min_eq_left (le_of_lt hk)]
lemma target_high (k : ℕ) (hk : n < k) (x : Cell C n) : target C n k x = x := by
  induction x using Quotient.inductionOn with | h x =>
    apply (map_eq_iff C n _ _).mpr
    simp [C.source_target, C.target_target, hk, min_eq_left (le_of_lt hk)]

lemma injective_on_lower {x y : C.Cell} (hx : C.source n x = x)
    (hy : C.source n y = y) (h : map C n x = map C n y) : x = y := by
  simpa only [hx,hy] using ((map_eq_iff C n x y).mp h).1

lemma composable_low {k : ℕ} (hk : k ≤ n) {x y : C.Cell}
    (h : target C n k (map C n x) = source C n k (map C n y)) :
    C.target k x = C.source k y := by
  apply injective_on_lower C n _ _ h
  · exact C.source_fixed_upwards hk (C.source_target_self k x)
  · exact C.source_fixed_upwards hk (C.source_source_self k y)

def comp (k : ℕ) (x y : Cell C n) (h : target C n k x = source C n k y) : Cell C n :=
  if hk : k ≤ n then
    map C n (C.comp k x.out y.out (composable_low C n hk (by simpa [map] using h)))
  else x

lemma comp_map (k : ℕ) (x y : C.Cell) (h : C.target k x = C.source k y)
    (h' : target C n k (map C n x) = source C n k (map C n y)) :
    comp C n k (map C n x) (map C n y) h' = map C n (C.comp k x y h) := by
  by_cases hk : k ≤ n
  · simp only [comp, dite_eq_left hk]
    apply (map_eq_iff C n _ _).mpr
    have hx := (map_eq_iff C n _ _).mp (Quotient.out_eq (map C n x))
    have hy := (map_eq_iff C n _ _).mp (Quotient.out_eq (map C n y))
    have hr : C.target k (map C n x).out = C.source k (map C n y).out :=
      composable_low C n hk (by simpa [map] using h')
    by_cases hnk : n ≤ k
    · simpa only [C.source_comp_le n k hnk, C.target_comp_le n k hnk] using And.intro hx.1 hy.2
    · have hlt : k < n := Nat.lt_of_not_ge hnk
      constructor
      · rw [C.source_comp_gt n k hlt _ _ _ (C.source_composable hlt hr),
          C.source_comp_gt n k hlt _ _ _ (C.source_composable hlt h)]
        congr 1
        · exact hx.1
        · exact hy.1
      · rw [C.target_comp_gt n k hlt _ _ _ (C.target_composable hlt hr),
          C.target_comp_gt n k hlt _ _ _ (C.target_composable hlt h)]
        congr 1
        · exact hx.2
        · exact hy.2
  · simp only [comp, dite_eq_right hk]
    apply (map_eq_iff C n _ _).mpr
    have hn : n ≤ k := le_of_lt (Nat.lt_of_not_ge hk)
    rw [C.source_comp_le n k hn, C.target_comp_le n k hn]
    refine ⟨rfl, ?_⟩
    have he := congrArg (C.target n) h
    simpa [C.target_target, C.target_source, Nat.lt_of_not_ge hk, min_eq_left hn] using he

lemma comp_map_low (k : ℕ) (hk : k ≤ n) (x y : C.Cell)
    (h : target C n k (map C n x) = source C n k (map C n y)) :
    comp C n k (map C n x) (map C n y) h =
      map C n (C.comp k x y (composable_low C n hk h)) :=
  comp_map C n k x y _ h

lemma comp_high (k : ℕ) (hk : n < k) (x y : Cell C n)
    (h : target C n k x = source C n k y) : comp C n k x y h = x := by
  simp only [comp, dite_eq_right (Nat.not_le.mpr hk)]

lemma high_composable {k : ℕ} (hk : n < k) {x y : Cell C n}
    (h : target C n k x = source C n k y) : x = y := by
  simpa only [target_high C n k hk, source_high C n k hk] using h

lemma source_source (i j : ℕ) (x : Cell C n) :
    source C n i (source C n j x) = source C n (min i j) x := by
  obtain ⟨x,rfl⟩ := surjective C n x
  simp only [source_map,C.source_source]
lemma target_target (i j : ℕ) (x : Cell C n) :
    target C n i (target C n j x) = target C n (min i j) x := by
  obtain ⟨x,rfl⟩ := surjective C n x
  simp only [target_map,C.target_target]
lemma source_target (i j : ℕ) (x : Cell C n) :
    source C n i (target C n j x) = if i < j then source C n i x else target C n j x := by
  obtain ⟨x,rfl⟩ := surjective C n x
  by_cases h : i < j <;> simp [source_map,target_map,C.source_target,h]
lemma target_source (i j : ℕ) (x : Cell C n) :
    target C n i (source C n j x) = if i < j then target C n i x else source C n j x := by
  obtain ⟨x,rfl⟩ := surjective C n x
  by_cases h : i < j <;> simp [source_map,target_map,C.target_source,h]

lemma source_comp_le (i k : ℕ) (hik : i ≤ k) (x y : Cell C n)
    (h : target C n k x = source C n k y) :
    source C n i (comp C n k x y h) = source C n i x := by
  by_cases hk : k ≤ n
  · obtain ⟨x,rfl⟩ := surjective C n x
    obtain ⟨y,rfl⟩ := surjective C n y
    simp only [comp_map_low C n k hk,source_map,C.source_comp_le i k hik]
  · rw [comp_high C n k (Nat.lt_of_not_ge hk)]
lemma target_comp_le (i k : ℕ) (hik : i ≤ k) (x y : Cell C n)
    (h : target C n k x = source C n k y) :
    target C n i (comp C n k x y h) = target C n i y := by
  by_cases hk : k ≤ n
  · obtain ⟨x,rfl⟩ := surjective C n x
    obtain ⟨y,rfl⟩ := surjective C n y
    simp only [comp_map_low C n k hk,target_map,C.target_comp_le i k hik]
  · rw [comp_high C n k (Nat.lt_of_not_ge hk), high_composable C n (Nat.lt_of_not_ge hk) h]

lemma source_comp_gt (i k : ℕ) (hki : k < i) (x y : Cell C n)
    (h : target C n k x = source C n k y)
    (hs : target C n k (source C n i x) = source C n k (source C n i y)) :
    source C n i (comp C n k x y h) = comp C n k (source C n i x) (source C n i y) hs := by
  by_cases hk : k ≤ n
  · obtain ⟨x,rfl⟩ := surjective C n x
    obtain ⟨y,rfl⟩ := surjective C n y
    simp only [comp_map_low C n k hk,source_map]
    exact congrArg (map C n) (C.source_comp_gt i k hki x y _ _)
  · rw [comp_high C n k (Nat.lt_of_not_ge hk), comp_high C n k (Nat.lt_of_not_ge hk)]
lemma target_comp_gt (i k : ℕ) (hki : k < i) (x y : Cell C n)
    (h : target C n k x = source C n k y)
    (ht : target C n k (target C n i x) = source C n k (target C n i y)) :
    target C n i (comp C n k x y h) = comp C n k (target C n i x) (target C n i y) ht := by
  by_cases hk : k ≤ n
  · obtain ⟨x,rfl⟩ := surjective C n x
    obtain ⟨y,rfl⟩ := surjective C n y
    simp only [comp_map_low C n k hk,target_map]
    exact congrArg (map C n) (C.target_comp_gt i k hki x y _ _)
  · rw [comp_high C n k (Nat.lt_of_not_ge hk), comp_high C n k (Nat.lt_of_not_ge hk)]

lemma unit_left (k : ℕ) (x : Cell C n)
    (h : target C n k (source C n k x) = source C n k x) :
    comp C n k (source C n k x) x h = x := by
  by_cases hk : k ≤ n
  · obtain ⟨x,rfl⟩ := surjective C n x
    simp only [source_map,comp_map_low C n k hk,C.unit_left]
  · rw [comp_high C n k (Nat.lt_of_not_ge hk),source_high C n k (Nat.lt_of_not_ge hk)]
lemma unit_right (k : ℕ) (x : Cell C n)
    (h : target C n k x = source C n k (target C n k x)) :
    comp C n k x (target C n k x) h = x := by
  by_cases hk : k ≤ n
  · obtain ⟨x,rfl⟩ := surjective C n x
    simp only [target_map,comp_map_low C n k hk,C.unit_right]
  · rw [comp_high C n k (Nat.lt_of_not_ge hk)]

lemma assoc (k : ℕ) (x y z : Cell C n)
    (hxy : target C n k x = source C n k y) (hyz : target C n k y = source C n k z)
    (hxy_z : target C n k (comp C n k x y hxy) = source C n k z)
    (hx_yz : target C n k x = source C n k (comp C n k y z hyz)) :
    comp C n k (comp C n k x y hxy) z hxy_z = comp C n k x (comp C n k y z hyz) hx_yz := by
  by_cases hk : k ≤ n
  · obtain ⟨x,rfl⟩ := surjective C n x
    obtain ⟨y,rfl⟩ := surjective C n y
    obtain ⟨z,rfl⟩ := surjective C n z
    simp only [comp_map_low C n k hk]
    exact congrArg (map C n) (C.assoc k x y z _ _ _ _)
  · simp only [comp_high C n k (Nat.lt_of_not_ge hk)]

lemma interchange (k l : ℕ) (hkl : k < l) (a b c d : Cell C n)
    (hab : target C n l a = source C n l b) (hcd : target C n l c = source C n l d)
    (hac : target C n k a = source C n k c) (hbd : target C n k b = source C n k d)
    (hab_cd : target C n k (comp C n l a b hab) = source C n k (comp C n l c d hcd))
    (hac_bd : target C n l (comp C n k a c hac) = source C n l (comp C n k b d hbd)) :
    comp C n k (comp C n l a b hab) (comp C n l c d hcd) hab_cd =
      comp C n l (comp C n k a c hac) (comp C n k b d hbd) hac_bd := by
  by_cases hl : l ≤ n
  · have hk : k ≤ n := (le_of_lt hkl).trans hl
    obtain ⟨a,rfl⟩ := surjective C n a
    obtain ⟨b,rfl⟩ := surjective C n b
    obtain ⟨c,rfl⟩ := surjective C n c
    obtain ⟨d,rfl⟩ := surjective C n d
    simp only [comp_map_low C n k hk,comp_map_low C n l hl]
    exact congrArg (map C n) (C.interchange k l hkl a b c d _ _ _ _ _ _)
  · simp only [comp_high C n l (Nat.lt_of_not_ge hl)]

def category : OmegaCategory.{u} where
  Cell := Cell C n
  source := source C n
  target := target C n
  comp := comp C n
  source_source := source_source C n
  target_target := target_target C n
  source_target := source_target C n
  target_source := target_source C n
  source_comp_le := source_comp_le C n
  target_comp_le := target_comp_le C n
  source_comp_gt := source_comp_gt C n
  target_comp_gt := target_comp_gt C n
  unit_left := unit_left C n
  unit_right := unit_right C n
  assoc := assoc C n
  interchange := interchange C n
  finite_dimension x := ⟨n+1, source_high C n (n+1) (by omega) x⟩

lemma truncated : (category C n).IsTruncated (n+1) :=
  source_high C n (n+1) (by omega)

def projection : Functor C (category C n) where
  map := map C n
  map_source _ _ := rfl
  map_target _ _ := rfl
  map_comp k x y h h' := (comp_map C n k x y h h').symm

end BoundaryQuotient

lemma truncationUnit_injective_below (C : OmegaCategory.{u}) (n k : ℕ)
    (hk : k < n) {x y : C.Cell} (hx : C.source k x = x)
    (hy : C.source k y = y)
    (h : (truncationUnit n C).map x = (truncationUnit n C).map y) : x = y := by
  let D : NCategory.{u} n := ⟨BoundaryQuotient.category C k, fun z =>
    (BoundaryQuotient.category C k).source_fixed_upwards (by omega)
      (BoundaryQuotient.truncated C k z)⟩
  let F := truncationLift D (BoundaryQuotient.projection C k)
  exact BoundaryQuotient.injective_on_lower C k hx hy (congrArg F.map h)

lemma truncationUnit_surjective (C : OmegaCategory.{u}) (n : ℕ) :
    Function.Surjective (truncationUnit n C).map := by
  intro z
  induction z using Quotient.inductionOn with | h z =>
    rcases z with ⟨z,hz⟩
    induction hz with
    | gen x => exact ⟨x,rfl⟩
    | source k z hz ih =>
      obtain ⟨x,hx⟩ := ih
      refine ⟨C.source k x, ?_⟩
      rw [(truncationUnit n C).map_source, hx]
      rfl
    | target k z hz ih =>
      obtain ⟨x,hx⟩ := ih
      refine ⟨C.target k x, ?_⟩
      rw [(truncationUnit n C).map_target, hx]
      rfl
    | comp k z w hz hw hm ihz ihw =>
      obtain ⟨x,hx⟩ := ihz
      obtain ⟨y,hy⟩ := ihw
      have he : (truncationPresentation n C).category.target k (Quotient.mk _ ⟨z,hz⟩) =
          (truncationPresentation n C).category.source k (Quotient.mk _ ⟨w,hw⟩) :=
        Quotient.sound hm
      rw [← (truncationPresentation n C).mk_comp k ⟨z,hz⟩ ⟨w,hw⟩ hm he]
      change ∃ a, (truncationUnit n C).map a =
        (truncationPresentation n C).category.comp k _ _ he
      by_cases hk : k < n
      · have he' : (truncationUnit n C).map (C.target k x) =
            (truncationUnit n C).map (C.source k y) := by
          rw [(truncationUnit n C).map_target, (truncationUnit n C).map_source, hx, hy]
          exact he
        have hc := truncationUnit_injective_below C n k hk
          (C.source_target_self k x) (C.source_source_self k y) he'
        refine ⟨C.comp k x y hc, ?_⟩
        rw [(truncationUnit n C).map_comp k x y hc ((truncationUnit n C).map_composable hc)]
        congr 1
      · refine ⟨y, ?_⟩
        rw [(truncationPresentation n C).category.comp_of_left_source_fixed k _ _ he
          ((truncationPresentation n C).category.source_fixed_upwards
            (Nat.le_of_not_gt hk) (truncation_isTruncated n C _))]
        exact hy

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

lemma truncationUnit_onCells_surjective (C : OmegaCategory.{u}) (n p : ℕ) :
    Function.Surjective ((truncationUnit n C).onCells p) := by
  intro z
  obtain ⟨x,hx⟩ := truncationUnit_surjective C n z.val
  refine ⟨C.sourceCell p x, ?_⟩
  apply Subtype.ext
  change (truncationUnit n C).map (C.source p x) = z.val
  rw [(truncationUnit n C).map_source, hx, z.property]

def truncationCellLift (C : OmegaCategory.{u}) (n p : ℕ)
    (z : (truncation n C).val.Cells p) : C.Cells p :=
  (truncationUnit_onCells_surjective C n p z).choose

@[simp] lemma truncationCellLift_unit (C : OmegaCategory.{u}) (n p : ℕ)
    (z : (truncation n C).val.Cells p) :
    (truncationUnit n C).onCells p (truncationCellLift C n p z) = z :=
  (truncationUnit_onCells_surjective C n p z).choose_spec

@[simp] lemma truncationCellLift_map (C : OmegaCategory.{u}) (n p : ℕ)
    (z : (truncation n C).val.Cells p) :
    (truncationUnit n C).map (truncationCellLift C n p z).val = z.val :=
  congrArg Subtype.val (truncationCellLift_unit C n p z)

lemma truncationUnit_onCells_injective (C : OmegaCategory.{u}) (n p : ℕ) (hp : p < n) :
    Function.Injective ((truncationUnit n C).onCells p) := by
  intro x y h
  exact Subtype.ext (truncationUnit_injective_below C n p hp x.property y.property
    (congrArg Subtype.val h))

@[simp] lemma truncationCellLift_of_unit (C : OmegaCategory.{u}) (n p : ℕ) (hp : p < n)
    (x : C.Cells p) : truncationCellLift C n p ((truncationUnit n C).onCells p x) = x :=
  truncationUnit_onCells_injective C n p hp (truncationCellLift_unit C n p _)

lemma truncationCellLift_source_fixed (C : OmegaCategory.{u}) (n p : ℕ) (hp : p < n)
    (x : (truncation n C).val.Cells p) (k : ℕ) (hk : k ≤ p)
    (hx : (truncation n C).val.source k x.val = x.val) :
    C.source k (truncationCellLift C n p x).val = (truncationCellLift C n p x).val := by
  apply truncationUnit_injective_below C n p hp
    (C.source_fixed_upwards hk (C.source_source_self k _)) (truncationCellLift C n p x).property
  rw [(truncationUnit n C).map_source, truncationCellLift_map]
  exact hx

lemma truncationCellLift_composable (C : OmegaCategory.{u}) (n p : ℕ) (hp : p < n)
    (x y : (truncation n C).val.Cells p) (k : ℕ) (hk : k < p)
    (h : (truncation n C).val.target k x.val = (truncation n C).val.source k y.val) :
    C.target k (truncationCellLift C n p x).val = C.source k (truncationCellLift C n p y).val := by
  apply truncationUnit_injective_below C n k (lt_trans hk hp)
    (C.source_target_self k _) (C.source_source_self k _)
  rw [(truncationUnit n C).map_source, (truncationUnit n C).map_target,
    truncationCellLift_map, truncationCellLift_map]
  exact h

lemma truncationCellLift_comp (C : OmegaCategory.{u}) (n p : ℕ) (hp : p < n)
    (x y : (truncation n C).val.Cells p) (k : ℕ) (hk : k < p)
    (h : (truncation n C).val.target k x.val = (truncation n C).val.source k y.val) :
    truncationCellLift C n p ((truncation n C).val.gradedComp hk x y h) =
      C.gradedComp hk (truncationCellLift C n p x) (truncationCellLift C n p y)
        (truncationCellLift_composable C n p hp x y k hk h) := by
  apply truncationUnit_onCells_injective C n p hp
  rw [truncationCellLift_unit, (truncationUnit n C).onCells_comp]
  simp only [truncationCellLift_unit]
  rfl

def truncationLambdaRawRetraction (C : OmegaCategory.{u}) (n p : ℕ) :
    (truncation n C).val.LambdaRaw p →ₗ[ℤ] C.LambdaChain p :=
  Finsupp.linearCombination ℤ (fun x => C.lambdaGen (truncationCellLift C n p x))

@[simp] lemma truncationLambdaRawRetraction_single (C : OmegaCategory.{u}) (n p : ℕ)
    (x : (truncation n C).val.Cells p) :
    truncationLambdaRawRetraction C n p (Finsupp.single x 1) =
      C.lambdaGen (truncationCellLift C n p x) := by
  exact (Finsupp.linearCombination_single _ _ _).trans (one_smul ℤ _)

lemma truncationLambdaRawRetraction_relations (C : OmegaCategory.{u}) (n p : ℕ) (hp : p < n) :
    (truncation n C).val.lambdaRelations p ≤ LinearMap.ker (truncationLambdaRawRetraction C n p) := by
  apply Submodule.span_le.mpr
  intro z hz
  change truncationLambdaRawRetraction C n p z = 0
  rcases hz with ⟨x,k,hk,hx,rfl⟩ | ⟨k,hk,x,y,h,rfl⟩
  · rw [truncationLambdaRawRetraction_single]
    exact C.lambdaGen_degenerate hk _ (truncationCellLift_source_fixed C n p hp x k hk.le hx)
  · simp only [map_sub,truncationLambdaRawRetraction_single]
    rw [truncationCellLift_comp C n p hp x y k hk h, C.lambdaGen_comp hk]
    abel

def truncationLambdaRetraction (C : OmegaCategory.{u}) (n p : ℕ) (hp : p < n) :
    (truncation n C).val.LambdaChain p →ₗ[ℤ] C.LambdaChain p :=
  ((truncation n C).val.lambdaRelations p).liftQ (truncationLambdaRawRetraction C n p)
    (truncationLambdaRawRetraction_relations C n p hp)

@[simp] lemma truncationLambdaRetraction_gen (C : OmegaCategory.{u}) (n p : ℕ) (hp : p < n)
    (x : (truncation n C).val.Cells p) :
    truncationLambdaRetraction C n p hp ((truncation n C).val.lambdaGen x) =
      C.lambdaGen (truncationCellLift C n p x) :=
  truncationLambdaRawRetraction_single C n p x

end Thomason.OmegaCategory

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SkeletalCategories
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Skeletal Categories. -/

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory DirectedComplex

lemma simplicialWeakEquivalences_homotopy {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) : simplicialWeakEquivalences f ↔ simplicialWeakEquivalences g := by
  have hf : simplicialWeakEquivalences f ↔ simplicialWeakEquivalences H.h := by
    constructor
    · intro hf
      apply simplicialWeakEquivalences.of_precomp SSet.ι₀ H.h
        (SimplicialCylinder.endpoint_weak X).1
      rwa [H.h₀]
    · intro hh
      rw [← H.h₀]
      exact simplicialWeakEquivalences.comp_mem _ _ (SimplicialCylinder.endpoint_weak X).1 hh
  have hg : simplicialWeakEquivalences g ↔ simplicialWeakEquivalences H.h := by
    constructor
    · intro hg
      apply simplicialWeakEquivalences.of_precomp SSet.ι₁ H.h
        (SimplicialCylinder.endpoint_weak X).2
      rwa [H.h₁]
    · intro hh
      rw [← H.h₁]
      exact simplicialWeakEquivalences.comp_mem _ _ (SimplicialCylinder.endpoint_weak X).2 hh
  exact hf.trans hg.symm

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

def ofCategory (C : Type u) [Category.{v} C] : OmegaCategory.{max u v} where
  Cell := Arrow C
  source := CategoryCell.source
  target := CategoryCell.target
  source_source i j x := by cases i <;> cases j <;> simp [CategoryCell.source]
  target_target i j x := by cases i <;> cases j <;> simp [CategoryCell.target]
  source_target i j x := by cases i <;> cases j <;> simp [CategoryCell.source, CategoryCell.target]
  target_source i j x := by cases i <;> cases j <;> simp [CategoryCell.source, CategoryCell.target]
  comp := CategoryCell.comp
  source_comp_le i k hik x y h := by
    cases k with
    | zero =>
      have hi : i = 0 := by omega
      subst i
      rfl
    | succ k => rfl
  target_comp_le i k hik x y h := by
    cases k with
    | zero =>
      have hi : i = 0 := by omega
      subst i
      rfl
    | succ k => exact congrArg (CategoryCell.target i) h
  source_comp_gt i k hki x y h hs := by cases i <;> first | omega | rfl
  target_comp_gt i k hki x y h hs := by cases i <;> first | omega | rfl
  unit_left k x h := by
    cases k with
    | zero =>
      refine Arrow.ext (by rfl) (by rfl) ?_
      dsimp [CategoryCell.comp, CategoryCell.source]
      simp
      exact (Category.id_comp _).symm
    | succ k => rfl
  unit_right k x h := by
    cases k with
    | zero =>
      refine Arrow.ext (by rfl) (by rfl) ?_
      dsimp [CategoryCell.comp, CategoryCell.target]
      simp
      exact (Category.id_comp _).symm
    | succ k => rfl
  assoc k x y z hxy hyz hxy_z hx_yz := by
    cases k with
    | zero =>
      refine Arrow.ext (by rfl) (by rfl) ?_
      dsimp [CategoryCell.comp]
      change (x.hom ≫ eqToHom (congrArg Arrow.left hxy) ≫ y.hom) ≫
        eqToHom (congrArg Arrow.left hyz) ≫ z.hom =
        (𝟙 x.left) ≫ (x.hom ≫ eqToHom (congrArg Arrow.left hxy) ≫
          (y.hom ≫ eqToHom (congrArg Arrow.left hyz) ≫ z.hom)) ≫ 𝟙 z.right
      simp only [Category.id_comp, Category.comp_id, Category.assoc]
      exact congrArg (fun f => x.hom ≫ f) (Category.assoc _ _ _)
    | succ k => rfl
  interchange k l hkl a b c d hab hcd hac hbd hab_cd hac_bd := by
    cases l with
    | zero => omega
    | succ l => rfl
  finite_dimension x := ⟨1, rfl⟩

lemma ofCategory_truncated (C : Type u) [Category.{v} C] :
    (ofCategory C).IsTruncated 1 := fun _ => rfl

def ofCategoryMap {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
    (F : C ⥤ D) : Functor (ofCategory C) (ofCategory D) where
  map x := Arrow.mk (F.map x.hom)
  map_source k x := by
    cases k with
    | zero =>
      refine Arrow.ext (by rfl) (by rfl) ?_
      dsimp [ofCategory, CategoryCell.source]
      simp
      rfl
    | succ k => rfl
  map_target k x := by
    cases k with
    | zero =>
      refine Arrow.ext (by rfl) (by rfl) ?_
      dsimp [ofCategory, CategoryCell.target]
      simp
      rfl
    | succ k => rfl
  map_comp k x y h h' := by
    cases k with
    | zero =>
      refine Arrow.ext (by rfl) (by rfl) ?_
      dsimp [ofCategory, CategoryCell.comp]
      change F.map (x.hom ≫ eqToHom (congrArg Arrow.left h) ≫ y.hom) =
        (𝟙 (F.obj x.left)) ≫
          (F.map x.hom ≫ eqToHom (congrArg Arrow.left h') ≫ F.map y.hom) ≫
            𝟙 (F.obj y.right)
      simp only [Category.id_comp, Category.comp_id, F.map_comp]
      congr 2
      exact (F.map_comp _ _).trans
        (congrArg (fun q => q ≫ F.map y.hom) (eqToHom_map F _))
    | succ k => rfl

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

lemma comp_congr_cells (C : OmegaCategory.{u}) (k : ℕ) {x y x' y' : C.Cell}
    (h : C.target k x = C.source k y) (h' : C.target k x' = C.source k y')
    (hx : x = x') (hy : y = y') : C.comp k x y h = C.comp k x' y' h' := by
  subst x'; subst y'; rfl

def OneSkeleton (C : OmegaCategory.{u}) := C.Objects

def OneHom (C : OmegaCategory.{u}) (a b : OneSkeleton C) :=
  {x : C.Cell // C.source 1 x = x ∧ C.source 0 x = a.val ∧ C.target 0 x = b.val}

namespace OneHom

variable {C : OmegaCategory.{u}}

 def id (a : OneSkeleton C) : OneHom C a a :=
  ⟨a.val, C.source_fixed_upwards (by omega) a.property, a.property,
    C.target_eq_self_of_source_eq_self a.property⟩

 def comp {a b c : OneSkeleton C} (f : OneHom C a b) (g : OneHom C b c) :
    OneHom C a c :=
  ⟨C.comp 0 f.val g.val (f.property.2.2.trans g.property.2.1.symm), by
      rw [C.source_comp_gt 1 0 (by omega) _ _ _
        (C.source_composable (by omega) (f.property.2.2.trans g.property.2.1.symm))]
      simp only [f.property.1, g.property.1],
    (C.source_comp_le 0 0 le_rfl _ _ _).trans f.property.2.1,
    (C.target_comp_le 0 0 le_rfl _ _ _).trans g.property.2.2⟩

end OneHom

instance oneSkeletonCategory (C : OmegaCategory.{u}) : Category (OneSkeleton C) where
  Hom := OneHom C
  id := OneHom.id
  comp := OneHom.comp
  id_comp {a b} f := by
    apply Subtype.ext
    change C.comp 0 a.val f.val _ = f.val
    have ha : a.val = C.source 0 f.val := f.property.2.1.symm
    exact (C.comp_congr_cells 0 _ (C.target_source_self 0 _) ha rfl).trans
      (C.unit_left 0 f.val _)
  comp_id {a b} f := by
    apply Subtype.ext
    change C.comp 0 f.val b.val _ = f.val
    have hb : b.val = C.target 0 f.val := f.property.2.2.symm
    exact (C.comp_congr_cells 0 _ (C.source_target_self 0 _).symm rfl hb).trans
      (C.unit_right 0 f.val _)
  assoc f g h := by
    apply Subtype.ext
    exact C.assoc 0 f.val g.val h.val _ _ _ _

@[simp] lemma one_id_val {C : OmegaCategory.{u}} (a : C.OneSkeleton) :
    (𝟙 a : a ⟶ a).val = a.val := rfl

@[simp] lemma one_comp_val {C : OmegaCategory.{u}} {a b c : C.OneSkeleton}
    (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).val = C.comp 0 f.val g.val (f.property.2.2.trans g.property.2.1.symm) := rfl

@[simp] lemma one_eqToHom_val {C : OmegaCategory.{u}} {a b : C.OneSkeleton} (h : a = b) :
    (eqToHom h).val = a.val := by subst b; rfl

lemma one_eqToHom_comp_val {C : OmegaCategory.{u}} {a b c : C.OneSkeleton}
    (h : a = b) (f : b ⟶ c) : (eqToHom h ≫ f).val = f.val := by
  subst b
  simp only [eqToHom_refl, Category.id_comp]

lemma one_comp_eqToHom_val {C : OmegaCategory.{u}} {a b c : C.OneSkeleton}
    (f : a ⟶ b) (h : b = c) : (f ≫ eqToHom h).val = f.val := by
  subst c
  simp only [eqToHom_refl, Category.comp_id]

def Functor.oneMap {C : OmegaCategory.{u}} {D : OmegaCategory.{v}}
    (F : Functor C D) : C.OneSkeleton ⥤ D.OneSkeleton where
  obj a := F.objects a
  map {a b} f := ⟨F.map f.val, by rw [← F.map_source, f.property.1],
    by rw [← F.map_source, f.property.2.1]; rfl,
    by rw [← F.map_target, f.property.2.2]; rfl⟩
  map_id a := rfl
  map_comp f g := by apply Subtype.ext; exact F.map_comp 0 _ _ _ _

def oneSkeletonEvaluation (C : OmegaCategory.{u}) : Functor (ofCategory C.OneSkeleton) C where
  map x := x.hom.val
  map_source k x := by
    cases k with
    | zero => exact x.hom.property.2.1.symm
    | succ k => exact (C.source_fixed_upwards (by omega) x.hom.property.1).symm
  map_target k x := by
    cases k with
    | zero => exact x.hom.property.2.2.symm
    | succ k => exact (C.target_eq_self_of_source_eq_self
        (C.source_fixed_upwards (by omega) x.hom.property.1)).symm
  map_comp k x y h h' := by
    cases k with
    | zero =>
      have hobj : x.right = y.left := congrArg Arrow.left h
      have he : (x.hom ≫ eqToHom hobj).val = x.hom.val := by
        rw [one_comp_val]
        exact (C.comp_congr_cells 0 _ (C.source_target_self 0 _).symm rfl
          ((one_eqToHom_val hobj).trans x.hom.property.2.2.symm)).trans
            (C.unit_right 0 _ _)
      change (x.hom ≫ eqToHom hobj ≫ y.hom).val = _
      rw [← Category.assoc, one_comp_val]
      exact C.comp_congr_cells 0 _ h' he rfl
    | succ k =>
      change x.hom.val = C.comp (k+1) x.hom.val y.hom.val h'
      have hy : C.source (k+1) y.hom.val = y.hom.val :=
        C.source_fixed_upwards (by omega) y.hom.property.1
      have he : y.hom.val = C.target (k+1) x.hom.val := hy.symm.trans h'.symm
      exact ((C.comp_congr_cells (k+1) h' (C.source_target_self (k+1) _).symm rfl he).trans
        (C.unit_right (k+1) _ _)).symm

lemma oneSkeletonEvaluation_injective (C : OmegaCategory.{u}) :
    Function.Injective C.oneSkeletonEvaluation.map := by
  intro x y h
  change Arrow C.OneSkeleton at x y
  change x.hom.val = y.hom.val at h
  have hl : x.left = y.left := Subtype.ext
    (x.hom.property.2.1.symm.trans ((congrArg (C.source 0) h).trans y.hom.property.2.1))
  have hr : x.right = y.right := Subtype.ext
    (x.hom.property.2.2.symm.trans ((congrArg (C.target 0) h).trans y.hom.property.2.2))
  rcases x with ⟨a, b, f⟩
  rcases y with ⟨a', b', g⟩
  change a = a' at hl
  change b = b' at hr
  subst a'; subst b'
  have he : f = g := Subtype.ext h
  cases he
  rfl

lemma oneSkeletonEvaluation_surjective {C : OmegaCategory.{u}} (hC : C.IsTruncated 1) :
    Function.Surjective C.oneSkeletonEvaluation.map := by
  intro x
  let f : OneHom C (C.sourceObject x) (C.targetObject x) := ⟨x, hC x, rfl, rfl⟩
  exact ⟨@Arrow.mk _ (oneSkeletonCategory C) (C.sourceObject x) (C.targetObject x) f, rfl⟩

noncomputable def oneSkeletonIso {C : OmegaCategory.{u}} (hC : C.IsTruncated 1) :
    ofCategory C.OneSkeleton ≅ C :=
  isoOfBijective C.oneSkeletonEvaluation
    ⟨C.oneSkeletonEvaluation_injective, oneSkeletonEvaluation_surjective hC⟩

end Thomason.OmegaCategory

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SubdivisionFaces
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subdivision Faces. -/

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open CategoryTheory DirectedComplex OmegaCategory

variable {E : Type u} [LinearOrder E]

def tableStart (x : Table (complex E)) : E :=
  tableObjectsEquiv ((complex E).nu.sourceObject x)

def tableFinish (x : Table (complex E)) : E :=
  tableObjectsEquiv ((complex E).nu.targetObject x)

lemma tableStart_row (x : Table (complex E)) :
    (x.row 0 false).val = bracket [tableStart x] := by
  have he := congrArg (fun a : (complex E).nu.Objects => (a.val.row 0 false).val)
    (tableObjectsEquiv.symm_apply_apply ((complex E).nu.sourceObject x))
  exact he.symm

lemma tableFinish_row (x : Table (complex E)) :
    (x.row 0 true).val = bracket [tableFinish x] := by
  have he := congrArg (fun a : (complex E).nu.Objects => (a.val.row 0 false).val)
    (tableObjectsEquiv.symm_apply_apply ((complex E).nu.targetObject x))
  exact he.symm

lemma tableStart_le_finish (x : Table (complex E)) : tableStart x ≤ tableFinish x :=
  table_source_le_target x _ _ (tableStart_row x) (tableFinish_row x)

lemma map_table_eq_edge {D : OmegaCategory.{v}} (hD : D.IsTruncated 1)
    (F : OmegaCategory.Functor (complex E).nu D) (x : Table (complex E)) :
    F.map x = F.map (edgeTable (tableStart x) (tableFinish x) (tableStart_le_finish x)) := by
  have hx : ∀ p b, (x.row p b).val ∈ supportedOn (Set.Ici (tableStart x)) := by
    apply table_supportedOn_upper (by intro a b hab ha; exact le_trans ha hab) x
    intro b
    cases b
    · rw [tableStart_row]; exact bracket_mem_supportedOn (by simp)
    · rw [tableFinish_row]
      exact bracket_mem_supportedOn (by simpa using tableStart_le_finish x)
  let y := coneTable (tableStart x) x hx
  have hs : (complex E).nu.source 1 y =
      edgeTable (tableStart x) (tableFinish x) (tableStart_le_finish x) :=
    coneTable_one_source x _ _ (tableStart_row x) (tableFinish_row x) hx
  have ht : (complex E).nu.target 1 y = (complex E).nu.target 1 x :=
    coneTable_one_target x _ (tableStart_row x) hx
  calc
    F.map x = D.target 1 (F.map x) := (D.target_eq_self_of_source_eq_self (hD _)).symm
    _ = F.map ((complex E).nu.target 1 x) := (F.map_target 1 x).symm
    _ = F.map ((complex E).nu.target 1 y) := congrArg F.map ht.symm
    _ = D.target 1 (F.map y) := F.map_target 1 y
    _ = F.map y := D.target_eq_self_of_source_eq_self (hD _)
    _ = D.source 1 (F.map y) := (hD _).symm
    _ = F.map ((complex E).nu.source 1 y) := (F.map_source 1 y).symm
    _ = _ := congrArg F.map hs

def tableEndpoints : OmegaCategory.Functor (complex E).nu (ofCategory E) where
  map x := Arrow.mk (homOfLE (tableStart_le_finish x))
  map_source k x := by
    apply ordered_arrow_ext
    · cases k <;> simp [ofCategory, CategoryCell.source, tableStart]
    · cases k <;> simp [ofCategory, CategoryCell.source, tableStart, tableFinish]
  map_target k x := by
    apply ordered_arrow_ext
    · cases k <;> simp [ofCategory, CategoryCell.target, tableStart, tableFinish]
    · cases k <;> simp [ofCategory, CategoryCell.target, tableFinish]
  map_comp k x y h h' := by
    apply ordered_arrow_ext
    · cases k <;> simp [ofCategory, CategoryCell.comp, tableStart]
    · cases k with
      | zero => simp [ofCategory, CategoryCell.comp, tableFinish]
      | succ k =>
        have he := congrArg (fun z => tableObjectsEquiv ((complex E).nu.targetObject z)) h
        simpa [ofCategory, CategoryCell.comp, tableFinish] using he.symm

@[simp] lemma tableStart_edge (a b : E) (hab : a ≤ b) :
    tableStart (edgeTable a b hab) = a := by
  simp [tableStart, edgeTable_sourceObject]

@[simp] lemma tableFinish_edge (a b : E) (hab : a ≤ b) :
    tableFinish (edgeTable a b hab) = b := by
  simp [tableFinish, edgeTable_targetObject]

lemma edgeTable_diagonal (a : E) : edgeTable a a le_rfl = vertexTable a := by
  ext p b
  cases p with
  | zero => cases b <;> rfl
  | succ p =>
    cases p with
    | zero =>
      apply Subtype.ext
      change bracket [a,a] = 0
      exact bracket_of_not_pairwise (by simp)
    | succ p => rfl

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open CategoryTheory DirectedComplex OmegaCategory

variable {E : Type u} [LinearOrder E] {D : OmegaCategory.{v}}

def orientalOneFunctor (hD : D.IsTruncated 1)
    (F : OmegaCategory.Functor (complex E).nu D) : E ⥤ D.OneSkeleton where
  obj a := F.objects (tableObjectsEquiv.symm a)
  map {a b} f := ⟨F.map (edgeTable a b (leOfHom f)), hD _, by
      exact (F.map_source 0 _).symm.trans
        (congrArg F.map (edgeTable_source a b (leOfHom f))), by
      exact (F.map_target 0 _).symm.trans
        (congrArg F.map (edgeTable_target a b (leOfHom f)))⟩
  map_id a := by
    apply Subtype.ext
    exact congrArg F.map (edgeTable_diagonal a)
  map_comp {a b c} f g := by
    apply Subtype.ext
    let x := edgeTable a b (leOfHom f)
    let y := edgeTable b c (leOfHom g)
    have hxy : (complex E).nu.target 0 x = (complex E).nu.source 0 y :=
      (edgeTable_target a b _).trans (edgeTable_source b c _).symm
    let z := (complex E).nu.comp 0 x y hxy
    have hs : tableStart z = a := by
      exact (congrArg tableObjectsEquiv ((complex E).nu.sourceObject_comp 0 x y hxy)).trans
        (tableStart_edge a b _)
    have ht : tableFinish z = c := by
      exact (congrArg tableObjectsEquiv ((complex E).nu.targetObject_comp 0 x y hxy)).trans
        (tableFinish_edge b c _)
    have he := map_table_eq_edge hD F z
    have he' : F.map z = F.map (edgeTable a c (leOfHom (f ≫ g))) := by
      simpa only [hs, ht] using he
    exact he'.symm.trans (F.map_comp 0 x y hxy _)

def ordinalDiagramFunctor (G : E ⥤ D.OneSkeleton) :
    OmegaCategory.Functor (complex E).nu D :=
  OmegaCategory.Functor.comp tableEndpoints
    (OmegaCategory.Functor.comp (ofCategoryMap G) D.oneSkeletonEvaluation)

lemma ordinalDiagramFunctor_orientalOneFunctor (hD : D.IsTruncated 1)
    (F : OmegaCategory.Functor (complex E).nu D) :
    ordinalDiagramFunctor (orientalOneFunctor hD F) = F := by
  apply OmegaCategory.Functor.ext
  funext x
  exact (map_table_eq_edge hD F x).symm

@[simp] lemma tableStart_vertex (a : E) : tableStart (vertexTable a) = a := by
  have he := tableStart_edge a a le_rfl
  rwa [edgeTable_diagonal] at he

@[simp] lemma tableFinish_vertex (a : E) : tableFinish (vertexTable a) = a := by
  have he := tableFinish_edge a a le_rfl
  rwa [edgeTable_diagonal] at he

lemma tableEndpoints_vertex (a : E) : tableEndpoints.map (vertexTable a) = Arrow.mk (𝟙 a) := by
  apply ordered_arrow_ext
  · exact tableStart_vertex a
  · exact tableFinish_vertex a

lemma tableEndpoints_edge (a b : E) (hab : a ≤ b) :
    tableEndpoints.map (edgeTable a b hab) = Arrow.mk (homOfLE hab) := by
  apply ordered_arrow_ext
  · exact tableStart_edge a b hab
  · exact tableFinish_edge a b hab

lemma orientalOneFunctor_ordinalDiagramFunctor_obj (hD : D.IsTruncated 1)
    (G : E ⥤ D.OneSkeleton) (a : E) :
    (orientalOneFunctor hD (ordinalDiagramFunctor G)).obj a = G.obj a := by
  apply Subtype.ext
  change D.oneSkeletonEvaluation.map
    ((ofCategoryMap G).map (tableEndpoints.map (vertexTable a))) = _
  rw [tableEndpoints_vertex]
  change (G.map (𝟙 a)).val = _
  rw [G.map_id]
  rfl

lemma orientalOneFunctor_ordinalDiagramFunctor (hD : D.IsTruncated 1)
    (G : E ⥤ D.OneSkeleton) : orientalOneFunctor hD (ordinalDiagramFunctor G) = G := by
  refine CategoryTheory.Functor.ext
    (orientalOneFunctor_ordinalDiagramFunctor_obj hD G) ?_
  intro a b f
  apply Subtype.ext
  change D.oneSkeletonEvaluation.map
    ((ofCategoryMap G).map (tableEndpoints.map (edgeTable a b (leOfHom f)))) = _
  rw [tableEndpoints_edge]
  change (G.map (homOfLE (leOfHom f))).val = _
  have he : homOfLE (leOfHom f) = f := Subsingleton.elim _ _
  rw [he]
  simp only [one_eqToHom_comp_val, one_comp_eqToHom_val]

def orientalOneEquiv (hD : D.IsTruncated 1) :
    OmegaCategory.Functor (complex E).nu D ≃ (E ⥤ D.OneSkeleton) where
  toFun := orientalOneFunctor hD
  invFun := ordinalDiagramFunctor
  left_inv := ordinalDiagramFunctor_orientalOneFunctor hD
  right_inv := orientalOneFunctor_ordinalDiagramFunctor hD

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open CategoryTheory DirectedComplex OmegaCategory

variable {E : Type u} [LinearOrder E] {B : Type v} [LinearOrder B]
  {D : OmegaCategory.{w}}

lemma complexMap_vertex (f : E →o B) (a : E) :
    (complexMap f).nu.map (vertexTable a) = vertexTable (f a) := by
  change (complexMap f).table (vertexTable a) = _
  ext p b
  apply Subtype.ext
  cases p with
  | zero =>
    change map f (bracket [a]) = bracket [f a]
    simpa using map_bracket f (by simp : [a].Pairwise (· ≤ ·))
  | succ p => exact map_zero (map f)

lemma complexMap_edge (f : E →o B) (a b : E) (hab : a ≤ b) :
    (complexMap f).nu.map (edgeTable a b hab) = edgeTable (f a) (f b) (f.monotone hab) := by
  change (complexMap f).table (edgeTable a b hab) = _
  ext p e
  apply Subtype.ext
  cases p with
  | zero =>
    cases e <;>
      change map f (bracket [_]) = bracket [f _] <;>
      simpa using map_bracket f (by simp : [_].Pairwise (· ≤ ·))
  | succ p =>
    cases p with
    | zero =>
      change map f (bracket [a,b]) = bracket [f a, f b]
      simpa using map_bracket f (by simpa using hab : [a,b].Pairwise (· ≤ ·))
    | succ p => exact map_zero (map f)

lemma orientalOneFunctor_naturality_obj (hD : D.IsTruncated 1) (f : E →o B)
    (F : OmegaCategory.Functor (complex B).nu D) (a : E) :
    (orientalOneFunctor hD (OmegaCategory.Functor.comp (complexMap f).nu F)).obj a =
      (f.monotone.functor ⋙ orientalOneFunctor hD F).obj a := by
  apply Subtype.ext
  exact congrArg F.map (complexMap_vertex f a)

lemma orientalOneFunctor_naturality (hD : D.IsTruncated 1) (f : E →o B)
    (F : OmegaCategory.Functor (complex B).nu D) :
    orientalOneFunctor hD (OmegaCategory.Functor.comp (complexMap f).nu F) =
      f.monotone.functor ⋙ orientalOneFunctor hD F := by
  refine CategoryTheory.Functor.ext (orientalOneFunctor_naturality_obj hD f F) ?_
  intro a b g
  apply Subtype.ext
  simp only [one_eqToHom_comp_val, one_comp_eqToHom_val]
  exact congrArg F.map (complexMap_edge f a b (leOfHom g))

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Opposite NormalizedChains

def oneNerveIso {D : OmegaCategory.{u}} (hD : D.IsTruncated 1) :
    streetNerve D ≅ nerve D.OneSkeleton :=
  NatIso.ofComponents
    (fun m => Equiv.toIso (orientalOneEquiv (E := Fin (m.unop.len+1)) hD)) (by
      intro m n f
      apply ConcreteCategory.hom_ext
      intro F
      exact orientalOneFunctor_naturality hD f.unop.toOrderHom F)

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

variable {C : OmegaCategory.{u}} {D : OmegaCategory.{v}}

def oneCell (hC : C.IsTruncated 1) (x : C.Cell) :
    @Quiver.Hom C.OneSkeleton (inferInstance : Quiver C.OneSkeleton)
      (C.sourceObject x) (C.targetObject x) := ⟨x, hC x, rfl, rfl⟩

lemma oneSkeletonIso_inv_map (hC : C.IsTruncated 1) (x : C.Cell) :
    (oneSkeletonIso hC).inv.map x = Arrow.mk (oneCell hC x) := by
  apply C.oneSkeletonEvaluation_injective
  exact congrArg (fun F : OmegaCategory.Functor C C => F.map x)
    (oneSkeletonIso hC).inv_hom_id

def liftOneFunctor (hC : C.IsTruncated 1) (G : C.OneSkeleton ⥤ D.OneSkeleton) :
    OmegaCategory.Functor C D :=
  OmegaCategory.Functor.comp (oneSkeletonIso hC).inv
    (OmegaCategory.Functor.comp (ofCategoryMap G) D.oneSkeletonEvaluation)

lemma liftOneFunctor_map (hC : C.IsTruncated 1) (G : C.OneSkeleton ⥤ D.OneSkeleton)
    (x : C.Cell) : (liftOneFunctor hC G).map x = (G.map (oneCell hC x)).val := by
  change ((ofCategoryMap G).map ((oneSkeletonIso hC).inv.map x)).hom.val = _
  rw [oneSkeletonIso_inv_map]
  rfl

lemma liftOneFunctor_oneMap (hC : C.IsTruncated 1) (F : OmegaCategory.Functor C D) :
    liftOneFunctor hC F.oneMap = F := by
  ext x
  exact liftOneFunctor_map hC F.oneMap x

lemma mappedCast_val (G : C.OneSkeleton ⥤ D.OneSkeleton) {a a' b b' : C.OneSkeleton}
    (hs : a' = a) (ht : b = b') (f : a ⟶ b) :
    (G.map (eqToHom hs ≫ f ≫ eqToHom ht)).val = (G.map f).val := by
  rw [G.map_comp, G.map_comp, eqToHom_map, eqToHom_map]
  simp only [one_eqToHom_comp_val, one_comp_eqToHom_val]

lemma oneMap_liftOneFunctor_obj (hC : C.IsTruncated 1)
    (G : C.OneSkeleton ⥤ D.OneSkeleton) (a : C.OneSkeleton) :
    (liftOneFunctor hC G).oneMap.obj a = G.obj a := by
  apply Subtype.ext
  change (liftOneFunctor hC G).map a.val = (G.obj a).val
  refine (liftOneFunctor_map hC G a.val).trans ?_
  have hs : (C.sourceObject a.val : C.OneSkeleton) = a := Subtype.ext a.property
  have ht : (C.targetObject a.val : C.OneSkeleton) = a :=
    Subtype.ext (C.target_eq_self_of_source_eq_self a.property)
  have h : oneCell hC a.val =
      (@eqToHom C.OneSkeleton (inferInstance) _ _ hs) ≫ 𝟙 a ≫
        (@eqToHom C.OneSkeleton (inferInstance) _ _ ht.symm) := by
    apply Subtype.ext
    exact ((one_eqToHom_comp_val hs _).trans
      (one_comp_eqToHom_val (𝟙 a) ht.symm)).symm
  exact (congrArg (fun q => (G.map q).val) h).trans
    ((mappedCast_val G hs ht.symm (𝟙 a)).trans
      (congrArg (fun q : G.obj a ⟶ G.obj a => q.val) (G.map_id a)))

lemma oneMap_liftOneFunctor (hC : C.IsTruncated 1)
    (G : C.OneSkeleton ⥤ D.OneSkeleton) : (liftOneFunctor hC G).oneMap = G := by
  refine CategoryTheory.Functor.ext (oneMap_liftOneFunctor_obj hC G) ?_
  intro a b f
  apply Subtype.ext
  change (liftOneFunctor hC G).map f.val = _
  refine (liftOneFunctor_map hC G f.val).trans ?_
  have hs : (C.sourceObject f.val : C.OneSkeleton) = a := Subtype.ext f.property.2.1
  have ht : (C.targetObject f.val : C.OneSkeleton) = b := Subtype.ext f.property.2.2
  have h : oneCell hC f.val =
      (@eqToHom C.OneSkeleton (inferInstance) _ _ hs) ≫ f ≫
        (@eqToHom C.OneSkeleton (inferInstance) _ _ ht.symm) := by
    apply Subtype.ext
    exact ((one_eqToHom_comp_val hs _).trans (one_comp_eqToHom_val f ht.symm)).symm
  exact ((congrArg (fun q => (G.map q).val) h).trans (mappedCast_val G hs ht.symm f)).trans
    ((one_eqToHom_comp_val _ _).trans (one_comp_eqToHom_val _ _)).symm

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

def oneSkeletonCatFunctor : NCategory.{u} 1 ⥤ Cat.{u,u} where
  obj C := Cat.of C.val.OneSkeleton
  map F := F.oneMap.toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

def oneSkeletonFullyFaithful : oneSkeletonCatFunctor.{u}.FullyFaithful where
  preimage {C D} F := liftOneFunctor C.property F.toFunctor
  map_preimage {C D} F := by
    apply Cat.Hom.ext
    exact oneMap_liftOneFunctor C.property F.toFunctor
  preimage_map {C D} F := liftOneFunctor_oneMap C.property F

instance instFullNCategoryOfNatNatCatOneSkeletonCatFunctor : oneSkeletonCatFunctor.{u}.Full := oneSkeletonFullyFaithful.full
instance instFaithfulNCategoryOfNatNatCatOneSkeletonCatFunctor : oneSkeletonCatFunctor.{u}.Faithful := oneSkeletonFullyFaithful.faithful

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory OmegaCategory Opposite

lemma oneNerveIso_natural {C D : OmegaCategory.{u}} (hC : C.IsTruncated 1)
    (hD : D.IsTruncated 1) (F : OmegaCategory.Functor C D) :
    streetNerveMap F ≫ (oneNerveIso hD).hom =
      (oneNerveIso hC).hom ≫ nerveMap F.oneMap := by
  ext m x
  rfl

def oneNerveFunctorIso : streetNerveFinite.{u} 1 ≅
    oneSkeletonCatFunctor ⋙ nerveFunctor :=
  NatIso.ofComponents (fun C => oneNerveIso C.property) (by
    intro C D F
    exact oneNerveIso_natural C.property D.property F)

instance streetNerveFiniteOne_full : (streetNerveFinite.{u} 1).Full :=
  CategoryTheory.Functor.Full.of_iso oneNerveFunctorIso.symm

instance streetNerveFiniteOne_faithful : (streetNerveFinite.{u} 1).Faithful :=
  CategoryTheory.Functor.Faithful.of_iso oneNerveFunctorIso.symm

end Thomason

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_ExtensionAnodyne
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extension Anodyne. -/

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder Limits

variable {E : Type u} [PartialOrder E]

lemma lastVertex_nerve :
    sdNerveMap ≫ nerveMap (chainLast (X := E)).monotone.functor =
      lastVertex.app (nerve E) := by
  apply (isColimitOfPreserves SSet.sd (nerve E).isColimitCoconeN').hom_ext
  intro s
  change SSet.sd.map (SSet.yonedaEquiv.symm s.simplex) ≫ (_ ≫ _) =
    SSet.sd.map (SSet.yonedaEquiv.symm s.simplex) ≫ _
  rw [← Category.assoc, sdNerveMap_fac, Category.assoc, lastVertex.naturality]
  rw [lastVertex_stdSimplex, Category.assoc]
  congr 1
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  apply nerve.ext_of_isThin
  funext j
  exact chainGreatest_map (x.obj j) (simplexVertices s.simplex)

end Thomason.Subdivision

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SubdivisionWeak
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subdivision Weak. -/

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

variable {E : Type u} [PartialOrder E]

noncomputable def conicalFlagExtension (A : Set E) (p : A) (c : A →o A)
    (hc : ∀ a : A, a ≤ c a) (hp : ∀ a : A, p ≤ c a)
    (f : MeetingChains A →o A) : NonemptyFiniteChains E →o A := by
  classical
  let old (s : NonemptyFiniteChains E) := ∀ a ∈ s.finset, a ∈ A
  let meet (s : NonemptyFiniteChains E) := ∃ a ∈ s.finset, a ∈ A
  let cert (s : NonemptyFiniteChains E) (hs : old s) : MeetingChains A :=
    ⟨s, chainLast s, chainGreatest_mem s, hs _ (chainGreatest_mem s)⟩
  let r (s : NonemptyFiniteChains E) : A :=
    if hs : old s then f (cert s hs)
    else if hs : meet s then c (f ⟨s, hs⟩) else p
  refine ⟨r, fun s t hst => ?_⟩
  by_cases ht : old t
  · have hs : old s := fun a ha => ht a (hst ha)
    dsimp [r]
    rw [dite_eq_left hs, dite_eq_left ht]
    exact f.monotone hst
  · by_cases hs : old s
    · have htm : meet t := by
        obtain ⟨a, ha⟩ := s.nonempty
        exact ⟨a, hst ha, hs a ha⟩
      dsimp [r]
      rw [dite_eq_left hs, dite_eq_right ht, dite_eq_left htm]
      exact (f.monotone hst).trans (hc _)
    · by_cases hsm : meet s
      · have htm : meet t := by
          obtain ⟨a, ha, haA⟩ := hsm
          exact ⟨a, hst ha, haA⟩
        dsimp [r]
        rw [dite_eq_right hs, dite_eq_right ht, dite_eq_left hsm, dite_eq_left htm]
        exact c.monotone (f.monotone hst)
      · dsimp [r]
        rw [dite_eq_right hs, dite_eq_right ht, dite_eq_right hsm]
        split_ifs with htm
        · exact hp _
        · exact le_rfl

lemma conicalFlagExtension_old (A : Set E) (p : A) (c : A →o A)
    (hc : ∀ a : A, a ≤ c a) (hp : ∀ a : A, p ≤ c a)
    (f : MeetingChains A →o A) (s : NonemptyFiniteChains E)
    (hs : ∀ a ∈ s.finset, a ∈ A) (hm : ∃ a ∈ s.finset, a ∈ A) :
    conicalFlagExtension A p c hc hp f s = f ⟨s, hm⟩ := by
  classical
  simp only [conicalFlagExtension, OrderHom.coe_mk, dite_eq_left hs]

lemma hornFaces_downward {n : ℕ} (k : Fin (n+1))
    {s t : NonemptyFiniteChains (ULift.{u} (Fin (n+1)))} (h : s ≤ t)
    (ht : t ∈ HornFaces n k) : s ∈ HornFaces n k := by
  obtain ⟨a, hak, ha⟩ := ht
  exact ⟨a, hak, fun hs => ha (h hs)⟩

noncomputable def hornFlagOldVertices {n : ℕ} (k : Fin (n+1)) :
    MeetingChains (HornFaces.{u} n k) →o HornFaces.{u} n k where
  toFun s := ⟨(chainIntersection _ s).val.map chainLast, by
    apply hornFaces_downward k (t := chainLast (chainIntersection _ s).val)
    · intro a ha
      obtain ⟨b, hb, rfl⟩ := ((chainIntersection _ s).val.mem_map_iff chainLast a).mp ha
      exact (le_chainGreatest (chainIntersection _ s).val hb) (chainGreatest_mem b)
    · exact (chainIntersection _ s).property _ (chainGreatest_mem _)⟩
  monotone' _ _ h := (NonemptyFiniteChains.orderHomMap chainLast).monotone
    ((chainIntersection _).monotone h)

lemma hornFlagOldVertices_old {n : ℕ} (k : Fin (n+1))
    (s : NonemptyFiniteChains (NonemptyFiniteChains (ULift.{u} (Fin (n+1)))))
    (hs : ∀ a ∈ s.finset, a ∈ HornFaces n k) (hm : ∃ a ∈ s.finset, a ∈ HornFaces n k) :
    (hornFlagOldVertices k ⟨s, hm⟩).val = s.map chainLast := by
  classical
  change (chainIntersection _ ⟨s, hm⟩).val.map chainLast = s.map chainLast
  congr 1
  apply NonemptyFiniteChains.ext
  exact Finset.filter_eq_self.mpr hs

noncomputable def hornFlagExtension {n : ℕ} (hn : 1 ≤ n) (k : Fin (n+1)) :
    NonemptyFiniteChains (NonemptyFiniteChains (ULift.{u} (Fin (n+1)))) →o HornFaces.{u} n k :=
  conicalFlagExtension _ (hornFacePoint hn k) (hornFaceCone k)
    (le_hornFaceCone k) (hornFacePoint_le_cone hn k) (hornFlagOldVertices k)

lemma hornFlagExtension_old {n : ℕ} (hn : 1 ≤ n) (k : Fin (n+1))
    (s : NonemptyFiniteChains (NonemptyFiniteChains (ULift.{u} (Fin (n+1)))))
    (hs : ∀ a ∈ s.finset, a ∈ HornFaces n k) :
    (hornFlagExtension hn k s).val = s.map chainLast := by
  let hm : ∃ a ∈ s.finset, a ∈ HornFaces n k :=
    ⟨chainLast s, chainGreatest_mem _, hs _ (chainGreatest_mem _)⟩
  rw [hornFlagExtension, conicalFlagExtension_old _ _ _ _ _ _ _ hs hm]
  exact hornFlagOldVertices_old k s hs hm

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

variable {E : Type u} [PartialOrder E]

lemma sd_lastVertex_nerve :
    SSet.sd.map (lastVertex.app (nerve E)) ≫ sdNerveMap =
      sdTwiceNerveIso.hom ≫ nerveMap
        (NonemptyFiniteChains.orderHomMap (chainLast (X := E))).monotone.functor := by
  rw [← lastVertex_nerve, SSet.sd.map_comp, Category.assoc, sdNerveMap_naturality]
  rfl

noncomputable def orderedSdExtension (K : (nerve E).Subcomplex)
    (r : NonemptyFiniteChains (NonemptyFiniteChains E) →o AllowedChains K) :
    (SSet.sd ⋙ SSet.sd).obj (nerve E) ⟶ SSet.sd.obj (K : SSet) :=
  sdTwiceNerveIso.hom ≫ nerveMap r.monotone.functor ≫ (sdSubcomplexIso K).inv

lemma orderedSdExtension_restriction (K : (nerve E).Subcomplex)
    (r : NonemptyFiniteChains (NonemptyFiniteChains E) →o AllowedChains K)
    (hr : ∀ s : NonemptyFiniteChains (AllowedChains K),
      (r (s.map (OrderHom.Subtype.val _))).val =
        (s.map (OrderHom.Subtype.val _)).map chainLast) :
    (SSet.sd ⋙ SSet.sd).map K.ι ≫ orderedSdExtension K r =
      SSet.sd.map (lastVertex.app (K : SSet)) := by
  let j := nerveMap (NonemptyFiniteChains.orderHomMap (allowedChainInclusion K)).monotone.functor
  let v := nerveMap (NonemptyFiniteChains.orderHomMap (chainLast (X := E))).monotone.functor
  have he : j ≫ nerveMap r.monotone.functor ≫ allowedChainsForget K = j ≫ v := by
    apply NatTrans.ext
    funext k
    apply ConcreteCategory.hom_ext
    intro x
    apply nerve.ext_of_isThin
    funext i
    exact hr (x.obj i)
  apply (cancel_mono ((sdSubcomplexIso K).hom ≫ allowedChainsForget K)).mp
  change (_ ≫ (_ ≫ _ ≫ _)) ≫ (_ ≫ _) = _ ≫ (_ ≫ _)
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change (SSet.sd ⋙ SSet.sd).map K.ι ≫ sdTwiceNerveIso.hom ≫
      nerveMap r.monotone.functor ≫ allowedChainsForget K = _
  calc
    _ = (sdTwiceSubcomplexIso K).hom ≫ j ≫ nerveMap r.monotone.functor ≫
        allowedChainsForget K := by
      rw [← Category.assoc, sdTwiceSubcomplexIso_naturality]
      rfl
    _ = (sdTwiceSubcomplexIso K).hom ≫ j ≫ v := by rw [he]
    _ = (SSet.sd ⋙ SSet.sd).map K.ι ≫ sdTwiceNerveIso.hom ≫ v := by
      rw [← Category.assoc _ sdTwiceNerveIso.hom v, sdTwiceSubcomplexIso_naturality]
      rfl
    _ = SSet.sd.map (SSet.sd.map K.ι) ≫
        SSet.sd.map (lastVertex.app (nerve E)) ≫ sdNerveMap := by
      rw [sd_lastVertex_nerve]
      rfl
    _ = SSet.sd.map (lastVertex.app (K : SSet)) ≫ SSet.sd.map K.ι ≫ sdNerveMap := by
      rw [← Category.assoc, ← SSet.sd.map_comp, lastVertex.naturality,
        SSet.sd.map_comp, Category.assoc]
      rfl
    _ = _ := by rw [sdSubcomplexMap_naturality]; rfl

noncomputable def hornFlagExtensionAllowed {n : ℕ} (hn : 1 ≤ n) (k : Fin (n+1)) :
    NonemptyFiniteChains (NonemptyFiniteChains (ULift.{u} (Fin (n+1)))) →o
      AllowedChains (orderedSimplexSubcomplex (SSet.horn.{u} n k)) :=
  (hornFacesIso k).symm.toOrderEmbedding.toOrderHom.comp (hornFlagExtension hn k)

lemma hornFlagExtensionAllowed_old {n : ℕ} (hn : 1 ≤ n) (k : Fin (n+1))
    (s : NonemptyFiniteChains (AllowedChains (orderedSimplexSubcomplex (SSet.horn.{u} n k)))) :
    (hornFlagExtensionAllowed hn k (s.map (OrderHom.Subtype.val _))).val =
      (s.map (OrderHom.Subtype.val _)).map chainLast := by
  apply hornFlagExtension_old
  intro a ha
  obtain ⟨b, _, rfl⟩ := (s.mem_map_iff _ a).mp ha
  exact (hornFaces_allowed_iff k b.val).mp b.property

noncomputable def sdHornExtension {n : ℕ} (hn : 1 ≤ n) (k : Fin (n+1)) :
    (SSet.sd ⋙ SSet.sd).obj (SSet.stdSimplex.{u}.obj ⦋n⦌) ⟶ SSet.sd.obj (SSet.horn n k : SSet) :=
  (SSet.sd ⋙ SSet.sd).map (SSet.stdSimplex.isoNerve n).hom ≫
    orderedSdExtension _ (hornFlagExtensionAllowed hn k) ≫
      SSet.sd.map (orderedSimplexSubcomplexIso (SSet.horn n k)).inv

lemma sdHornExtension_restriction {n : ℕ} (hn : 1 ≤ n) (k : Fin (n+1)) :
    (SSet.sd ⋙ SSet.sd).map (SSet.horn.{u} n k).ι ≫ sdHornExtension hn k =
      SSet.sd.map (lastVertex.app (SSet.horn n k : SSet)) := by
  rw [sdHornExtension, ← Category.assoc, ← Functor.map_comp]
  have h : (SSet.horn.{u} n k).ι ≫ (SSet.stdSimplex.isoNerve n).hom =
      (orderedSimplexSubcomplexIso (SSet.horn n k)).hom ≫
        (orderedSimplexSubcomplex (SSet.horn n k)).ι := rfl
  rw [h, Functor.map_comp, Category.assoc, ← Category.assoc _ (orderedSdExtension _ _) _,
    orderedSdExtension_restriction _ _ (hornFlagExtensionAllowed_old hn k)]
  change SSet.sd.map (SSet.sd.map (orderedSimplexSubcomplexIso (SSet.horn n k)).hom) ≫
    SSet.sd.map (lastVertex.app _) ≫ SSet.sd.map (orderedSimplexSubcomplexIso (SSet.horn n k)).inv = _
  rw [← Category.assoc, ← SSet.sd.map_comp, lastVertex.naturality,
    SSet.sd.map_comp, Category.assoc, ← SSet.sd.map_comp, Functor.id_map]
  erw [Iso.hom_inv_id, SSet.sd.map_id, Category.comp_id]

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial

lemma exComparison_double_mate {A X : SSet.{u}} (a : A ⟶ SSet.ex.obj X) :
    (SSet.sdExAdjunction.comp SSet.sdExAdjunction).homEquiv A X
      (SSet.sd.map (lastVertex.app A) ≫ (SSet.sdExAdjunction.homEquiv A X).symm a) =
      a ≫ exComparison.app (SSet.ex.obj X) := by
  change SSet.sdExAdjunction.homEquiv A (SSet.ex.obj X)
    (SSet.sdExAdjunction.homEquiv (SSet.sd.obj A) X _) = _
  rw [SSet.sdExAdjunction.homEquiv_naturality_left]
  erw [Equiv.apply_symm_apply, SSet.sdExAdjunction.homEquiv_naturality_right]
  exact (exComparison.naturality a).symm

noncomputable def exHornExtension {n : ℕ} (hn : 1 ≤ n) (k : Fin (n+1))
    {X : SSet.{u}} (a : (SSet.horn n k : SSet.{u}) ⟶ SSet.ex.obj X) :
    SSet.stdSimplex.obj ⦋n⦌ ⟶ SSet.ex.obj (SSet.ex.obj X) :=
  (SSet.sdExAdjunction.comp SSet.sdExAdjunction).homEquiv _ _
    (sdHornExtension hn k ≫ (SSet.sdExAdjunction.homEquiv _ _).symm a)

lemma exHornExtension_restriction {n : ℕ} (hn : 1 ≤ n) (k : Fin (n+1))
    {X : SSet.{u}} (a : (SSet.horn n k : SSet.{u}) ⟶ SSet.ex.obj X) :
    (SSet.horn n k).ι ≫ exHornExtension hn k a = a ≫ exComparison.app (SSet.ex.obj X) := by
  rw [exHornExtension, ← Adjunction.homEquiv_naturality_left,
    ← Category.assoc, sdHornExtension_restriction, exComparison_double_mate]

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Limits Simplicial

lemma exInfinityComparison_anodyne (X : SSet.{u}) :
    SSet.anodyneExtensions (exInfinityComparison X) := by
  apply SSet.anodyneExtensions.transfiniteCompositionsOfShape_le ℕ
  refine ⟨{
    F := exSequence X
    isoBot := Iso.refl _
    incl := (colimit.cocone (exSequence X)).ι
    isColimit := colimit.isColimit _
    fac := Category.id_comp _
    map_mem := ?_ }⟩
  intro n _
  change SSet.anodyneExtensions ((exSequence X).map (homOfLE (Nat.le_succ n)))
  change SSet.anodyneExtensions ((Functor.ofSequence (X := exStage X)
    (fun n => exComparison.app (exStage X n))).map (homOfLE (n.le_add_right 1)))
  rw [Functor.ofSequence_map_homOfLE_succ]
  exact exComparison_anodyne (exStage X n)

lemma exInfinityComparison_weak (X : SSet.{u}) :
    simplicialWeakEquivalences (exInfinityComparison X) :=
  TopologicalHorn.anodyne_weak_equivalence _ (exInfinityComparison_anodyne X)

lemma exInfinity_horn_filling (X : SSet.{u}) {n : ℕ} (k : Fin (n+2))
    (a : (SSet.horn (n+1) k : SSet.{u}) ⟶ exInfinity X) :
    ∃ b : SSet.stdSimplex.obj ⦋n+1⦌ ⟶ exInfinity X, (SSet.horn (n+1) k).ι ≫ b = a := by
  let : PreservesFilteredColimitsOfSize.{0,0}
      (coyoneda.obj (Opposite.op (SSet.horn (n+1) k : SSet.{u}))) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  obtain ⟨m, p, hp⟩ := Limits.exists_hom_of_preservesColimit_coyoneda
    (colimit.isColimit (exSequence X)) a
  let q : (SSet.horn (n+1) k : SSet.{u}) ⟶ SSet.ex.obj (exStage X m) :=
    p ≫ exComparison.app (exStage X m)
  refine ⟨exHornExtension (by omega) k q ≫ exInfinityInclusion X (m+2), ?_⟩
  erw [← Category.assoc, exHornExtension_restriction, Category.assoc]
  change q ≫ (exComparison.app (exStage X (m+1)) ≫ exInfinityInclusion X ((m+1)+1)) = a
  rw [exInfinityInclusion_step]
  dsimp [q]
  erw [Category.assoc, exInfinityInclusion_step]
  exact hp

lemma exInfinity_kan (X : SSet.{u}) : SSet.KanComplex (exInfinity X) := by
  rw [SSet.KanComplex.iff]
  intro n i f hf
  obtain ⟨φ,hφ⟩ := exInfinity_horn_filling X i hf.desc
  refine ⟨φ, fun j hj => ?_⟩
  have h := congrArg (fun t => SSet.horn.ι i j hj ≫ t) hφ
  simpa only [← Category.assoc, SSet.horn.ι_ι, SSet.horn.IsCompatible.ι_desc] using h

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Limits

instance street_preservesFilteredColimits : PreservesFilteredColimits streetNerveFunctor.{u} where
  preserves_filtered_colimits _ _ _ := inferInstance

instance finiteInclusion_preservesFilteredColimits (n : ℕ) :
    PreservesFilteredColimits (OmegaCategory.nCategoryInclusion.{u} n) :=
  Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize.mp inferInstance

instance streetFinite_preservesFilteredColimits (n : ℕ) :
    PreservesFilteredColimits (streetNerveFinite.{u} n) := by
  change PreservesFilteredColimits (OmegaCategory.nCategoryInclusion n ⋙ streetNerveFunctor)
  infer_instance

attribute [local instance] Cardinal.fact_isRegular_aleph0

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open CategoryTheory DirectedComplex

variable (E : Type u) [PartialOrder E]

noncomputable def complexULiftIso : OmegaCategory.ulift.{u,v} (complex E).nu ≅
    (complex (ULift.{v} E)).nu where
  hom := OmegaCategory.Functor.comp (OmegaCategory.uliftDown _)
    (complexMap (orderULiftUp E)).nu
  inv := OmegaCategory.Functor.comp (complexMap (orderULiftDown E)).nu
    (OmegaCategory.uliftUp _)
  hom_inv_id := by
    apply OmegaCategory.Functor.ext
    funext x
    have he : DirectedComplex.Hom.comp (complexMap (orderULiftUp.{u,v} E))
        (complexMap (orderULiftDown E)) = DirectedComplex.Hom.id (complex E) := by
      rw [← complexMap_comp, orderULiftUp_down, complexMap_id]
    have h := congrArg (fun f => f.nu.map x.down) he
    change ULift.up ((complexMap (orderULiftDown E)).nu.map
      ((complexMap (orderULiftUp E)).nu.map x.down)) = x
    change (complexMap (orderULiftDown E)).nu.map
      ((complexMap (orderULiftUp E)).nu.map x.down) = x.down at h
    exact congrArg ULift.up h
  inv_hom_id := by
    apply OmegaCategory.Functor.ext
    funext x
    have he : DirectedComplex.Hom.comp (complexMap (orderULiftDown.{u,v} E))
        (complexMap (orderULiftUp E)) = DirectedComplex.Hom.id (complex (ULift.{v} E)) := by
      rw [← complexMap_comp, orderULiftDown_up, complexMap_id]
    exact congrArg (fun f => f.nu.map x) he

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Limits NormalizedChains

noncomputable def categorificationSimplexIso (n : SimplexCategory) :
    categorification.{u}.obj (SSet.stdSimplex.obj n) ≅ raisedOrientals.obj n :=
  ((asIso ((uliftYoneda.{u} : SimplexCategory ⥤ SSet.{u}).leftKanExtensionUnit
    raisedOrientals.{u})).symm).app n

end Thomason

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_Generators
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Generators. -/

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E] {D : Type v} [PartialOrder D]

lemma positive_supportedOn_of_boundary_upper_partial {S : Set E} (hS : IsUpperSet S)
    {p : ℕ} {c : Chains E} (hc : c ∈ grade (p+2)) (hp : Positive c)
    (hd : boundary c ∈ supportedOn S) : c ∈ supportedOn S := by
  classical
  let f := upperCutLinearExtension S hS
  let T : Set (Fin 2 ×ₗ LinearExtension E) := {z | 1 ≤ (ofLex z).1}
  have hT : IsUpperSet T := by
    intro a b hab ha
    exact le_trans ha (Prod.Lex.monotone_fst_ofLex hab)
  have hpre : f ⁻¹' T = S := by
    ext x
    change (1 ≤ (if x ∈ S then 1 else 0 : Fin 2)) ↔ x ∈ S
    by_cases hx : x ∈ S <;> simp [hx]
  have hm : map f c ∈ supportedOn T := by
    apply positive_supportedOn_of_boundary_upper hT (map_mem_grade f hc) (map_positive f hp)
    rw [← map_boundary]
    apply map_supportedOn f _ hd
    intro a ha
    change 1 ≤ (if a ∈ S then 1 else 0 : Fin 2)
    simp [ha]
  rw [← hpre]
  exact supportedOn_of_injective_map f (upperCutLinearExtension_injective S hS) hm

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex

variable {E : Type u} [PartialOrder E]

lemma positive_supportedOn_of_boundary_partial {S : Set E} (hS : IsLowerSet S)
    {p : ℕ} {c : Chains E} (hc : c ∈ grade (p+2)) (hp : Positive c)
    (hd : boundary c ∈ supportedOn S) : c ∈ supportedOn S := by
  apply supportedOn_of_reverseChain
  apply positive_supportedOn_of_boundary_upper_partial (E := Eᵒᵈ) hS
    (reverseChain_mem_grade hc) (reverseChain_positive hp)
  rw [boundary_reverseChain hc]
  exact (supportedOn (E := Eᵒᵈ) S).smul_mem _ (reverseChain_supportedOn hd)

lemma table_supportedOn_upper_partial {S : Set E} (hS : IsUpperSet S)
    (x : Table (complex E)) (hx : ∀ b, (x.row 0 b).val ∈ supportedOn S) :
    ∀ p b, (x.row p b).val ∈ supportedOn S := by
  intro p
  induction p with
  | zero => exact hx
  | succ p ih =>
    intro b
    apply positive_supportedOn_of_boundary_upper_partial hS
      (x.row (p+1) b).property (x.positive _ _)
    have hb := congrArg Subtype.val (x.boundary p b)
    change boundary (x.row (p+1) b).val = (x.row p true).val - (x.row p false).val at hb
    rw [hb]
    exact (supportedOn S).sub_mem (ih true) (ih false)

lemma table_supportedOn_lower_partial {S : Set E} (hS : IsLowerSet S)
    (x : Table (complex E)) (hx : ∀ b, (x.row 0 b).val ∈ supportedOn S) :
    ∀ p b, (x.row p b).val ∈ supportedOn S := by
  intro p
  induction p with
  | zero => exact hx
  | succ p ih =>
    intro b
    apply positive_supportedOn_of_boundary_partial hS
      (x.row (p+1) b).property (x.positive _ _)
    have hb := congrArg Subtype.val (x.boundary p b)
    change boundary (x.row (p+1) b).val = (x.row p true).val - (x.row p false).val at hb
    rw [hb]
    exact (supportedOn S).sub_mem (ih true) (ih false)

lemma table_segment_unique_lift_partial {S : Set E} (hS : IsUpperSet S ∨ IsLowerSet S)
    (x : Table (complex E)) (hx : ∀ b, (x.row 0 b).val ∈ supportedOn S) :
    ∃! y : Table (complex S),
      (complexMap (OrderEmbedding.subtype S).toOrderHom).table y = x := by
  have h : ∀ p b, (x.row p b).val ∈ supportedOn S := hS.elim
    (fun hu => table_supportedOn_upper_partial hu x hx)
    (fun hl => table_supportedOn_lower_partial hl x hx)
  refine ⟨restrictTable S x h, table_map_restrictTable S x h, ?_⟩
  intro y hy
  apply table_map_orderEmbedding_injective (OrderEmbedding.subtype S)
  exact hy.trans (table_map_restrictTable S x h).symm

lemma table_source_le_target_partial (x : Table (complex E)) (s t : E)
    (hs : (x.row 0 false).val = bracket [s])
    (ht : (x.row 0 true).val = bracket [t]) : s ≤ t := by
  classical
  let f : E →o Fin 2 :=
    { toFun := fun a => if s ≤ a then 1 else 0
      monotone' := by
        intro a b hab
        by_cases ha : s ≤ a
        · simp [ha, le_trans ha hab]
        · simp only [ha, ite_false]
          split <;> decide }
  have hh := table_source_le_target ((complexMap f).table x) (f s) (f t)
    (by change map f (x.row 0 false).val = bracket [f s]; rw [hs, map_bracket f (by simp)]; rfl)
    (by change map f (x.row 0 true).val = bracket [f t]; rw [ht, map_bracket f (by simp)]; rfl)
  by_contra hn
  change (if s ≤ s then 1 else 0 : Fin 2) ≤ (if s ≤ t then 1 else 0) at hh
  simp [hn] at hh

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains.PosetTables

open CategoryTheory DirectedComplex OmegaCategory

variable {E : Type u} [PartialOrder E]

def tableStart (x : Table (complex E)) : E :=
  tableObjectsEquiv ((complex E).nu.sourceObject x)

def tableFinish (x : Table (complex E)) : E :=
  tableObjectsEquiv ((complex E).nu.targetObject x)

lemma tableStart_row (x : Table (complex E)) :
    (x.row 0 false).val = bracket [tableStart x] := by
  have he := congrArg (fun a : (complex E).nu.Objects => (a.val.row 0 false).val)
    (tableObjectsEquiv.symm_apply_apply ((complex E).nu.sourceObject x))
  exact he.symm

lemma tableFinish_row (x : Table (complex E)) :
    (x.row 0 true).val = bracket [tableFinish x] := by
  have he := congrArg (fun a : (complex E).nu.Objects => (a.val.row 0 false).val)
    (tableObjectsEquiv.symm_apply_apply ((complex E).nu.targetObject x))
  exact he.symm

lemma tableStart_le_finish (x : Table (complex E)) : tableStart x ≤ tableFinish x :=
  table_source_le_target_partial x _ _ (tableStart_row x) (tableFinish_row x)

@[simp] lemma tableStart_edge (a b : E) (hab : a ≤ b) :
    tableStart (edgeTable a b hab) = a := by
  simp [tableStart, edgeTable_sourceObject]

@[simp] lemma tableFinish_edge (a b : E) (hab : a ≤ b) :
    tableFinish (edgeTable a b hab) = b := by
  simp [tableFinish, edgeTable_targetObject]

end Thomason.NormalizedChains.PosetTables

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains.PosetTables

open CategoryTheory DirectedComplex OmegaCategory

variable {E : Type u} [PartialOrder E] {B : Type v} [PartialOrder B]
  {D : OmegaCategory.{w}}

lemma complexMap_vertex (f : E →o B) (a : E) :
    (complexMap f).nu.map (vertexTable a) = vertexTable (f a) := by
  change (complexMap f).table (vertexTable a) = _
  ext p b
  apply Subtype.ext
  cases p with
  | zero =>
    change map f (bracket [a]) = bracket [f a]
    simpa using map_bracket f (by simp : [a].Pairwise (· ≤ ·))
  | succ p => exact map_zero (map f)

end Thomason.NormalizedChains.PosetTables

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Simplicial Opposite OmegaCategory NormalizedChains KanQuillen

lemma tableObjects_map {E : Type u} [PartialOrder E] {B : Type v} [PartialOrder B]
    (f : E →o B) (a : (complex E).nu.Objects) :
    tableObjectsEquiv ((complexMap f).nu.objects a) = f (tableObjectsEquiv a) := by
  obtain ⟨i, rfl⟩ := tableObjectsEquiv.symm.surjective a
  have he : (complexMap f).nu.objects (tableObjectsEquiv.symm i) =
      tableObjectsEquiv.symm (f i) := by
    apply Subtype.ext
    exact PosetTables.complexMap_vertex f i
  rw [he]
  simp

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

def finiteInterval (n : ℕ) (hn : 1 ≤ n) : NCategory.{u} n :=
  ⟨interval, fun x => interval.source_fixed_upwards hn (show interval.source 1 x = x from rfl)⟩

def fiberFiniteFunctor (n : ℕ) (hn : 1 ≤ n) (i : Fin 2) :
    CategoryTheory.Functor (Over (finiteInterval.{u} n hn)) (NCategory.{u} n) where
  obj p := ⟨(p.hom.fiber (intervalVertex i)).category, fun x =>
    Subtype.ext (p.left.property x.val)⟩
  map F := Functor.fiberMap _ _ F.left (Over.w F) (intervalVertex i)

def terminalConeFiniteObj (n : ℕ) (hn : 1 ≤ n) (C : NCategory.{u} n) :
    Over (finiteInterval.{u} n hn) :=
  Over.mk (X := finiteInterval n hn)
    (Y := ⟨C.val.terminalCone, terminalCone_truncated C.val hn C.property⟩) (coneLabel C.val)

def terminalConeFiniteFunctor (n : ℕ) (hn : 1 ≤ n) :
    CategoryTheory.Functor (NCategory.{u} n) (Over (finiteInterval.{u} n hn)) where
  obj := terminalConeFiniteObj n hn
  map {C D} F := Over.homMk
    (U := terminalConeFiniteObj n hn C) (V := terminalConeFiniteObj n hn D)
    (coneMap F) (by
      apply Functor.ext
      funext x
      cases x <;> rfl)
  map_id C := by
    apply Over.OverMorphism.ext
    apply Functor.ext
    funext x
    cases x <;> rfl
  map_comp F G := by
    apply Over.OverMorphism.ext
    apply Functor.ext
    funext x
    cases x <;> rfl

def zeroFiberFiniteConeAdjunction (n : ℕ) (hn : 1 ≤ n) :
    fiberFiniteFunctor.{u} n hn 0 ⊣ terminalConeFiniteFunctor n hn :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun p B => {
      toFun F := Over.homMk (coneExtend p.hom F) (coneExtend_label p.hom F)
      invFun H := coneRestrict p.hom H.left (Over.w H)
      left_inv := coneRestrict_extend p.hom
      right_inv H := by
        apply Over.OverMorphism.ext
        exact coneExtend_restrict p.hom H.left (Over.w H) }
    homEquiv_naturality_left_symm := by intros; rfl
    homEquiv_naturality_right := by
      intro p B D F G
      apply Over.OverMorphism.ext
      apply Functor.ext
      funext x
      change coneExtendMap p.hom (Functor.comp F G) x =
        (coneMap G).map (coneExtendMap p.hom F x)
      rcases interval_cases (p.hom.map x) with hx | hx | hx
      · rw [coneExtendMap_zero p.hom (Functor.comp F G) x hx]
        exact (congrArg (coneMap G).map (coneExtendMap_zero p.hom F x hx)).symm
      · rw [coneExtendMap_arrow p.hom (Functor.comp F G) x hx]
        exact (congrArg (coneMap G).map (coneExtendMap_arrow p.hom F x hx)).symm
      · rw [coneExtendMap_one p.hom (Functor.comp F G) x hx]
        exact (congrArg (coneMap G).map (coneExtendMap_one p.hom F x hx)).symm }

instance zeroFiberFinite_preservesColimits (n : ℕ) (hn : 1 ≤ n) :
    Limits.PreservesColimitsOfSize.{v,w} (fiberFiniteFunctor.{u} n hn 0) :=
  (zeroFiberFiniteConeAdjunction n hn).leftAdjoint_preservesColimits

end Thomason.OmegaCategory

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_LabelledFibers
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Labelled Fibers. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

def opFiniteFunctor (n : ℕ) : CategoryTheory.Functor (NCategory.{u} n) (NCategory.{u} n) where
  obj C := ⟨C.val.op, op_truncated C.property⟩
  map F := Thomason.OmegaCategory.Functor.op F

def opFiniteEquivalence (n : ℕ) : NCategory.{u} n ≌ NCategory.{u} n where
  functor := opFiniteFunctor n
  inverse := opFiniteFunctor n
  unitIso := Iso.refl _
  counitIso := Iso.refl _

instance opFiniteFunctor_isEquivalence (n : ℕ) : (opFiniteFunctor.{u} n).IsEquivalence :=
  (opFiniteEquivalence n).isEquivalence_functor

def reverseLabelFiniteObj (n : ℕ) (hn : 1 ≤ n) (p : Over (finiteInterval.{u} n hn)) :
    Over (finiteInterval.{u} n hn) :=
  Over.mk (X := finiteInterval n hn) (Y := (opFiniteFunctor n).obj p.left)
    (reverseLabel p.hom)

def reverseLabelFiniteFunctor (n : ℕ) (hn : 1 ≤ n) :
    CategoryTheory.Functor (Over (finiteInterval.{u} n hn)) (Over (finiteInterval.{u} n hn)) where
  obj := reverseLabelFiniteObj n hn
  map {p q} F := Over.homMk
    (U := reverseLabelFiniteObj n hn p) (V := reverseLabelFiniteObj n hn q) (Thomason.OmegaCategory.Functor.op F.left) (by
      apply Functor.ext
      funext x
      have he := congrArg (fun f : Functor p.left.val interval => f.map x) (Over.w F)
      exact congrArg intervalReflect.map he)
  map_id p := by apply Over.OverMorphism.ext; rfl
  map_comp F G := by apply Over.OverMorphism.ext; rfl

def reverseLabelFiniteTwiceIso (n : ℕ) (hn : 1 ≤ n) :
    reverseLabelFiniteFunctor.{u} n hn ⋙ reverseLabelFiniteFunctor n hn ≅ 𝟭 _ :=
  NatIso.ofComponents (fun p => Over.isoMk (Iso.refl p.left) (by
    change p.hom = reverseLabel (reverseLabel p.hom)
    exact (reverseLabel_reverseLabel p.hom).symm)) (by
      intro p q F
      apply Over.OverMorphism.ext
      rfl)

def reverseLabelFiniteEquivalence (n : ℕ) (hn : 1 ≤ n) :
    Over (finiteInterval.{u} n hn) ≌ Over (finiteInterval.{u} n hn) where
  functor := reverseLabelFiniteFunctor n hn
  inverse := reverseLabelFiniteFunctor n hn
  unitIso := (reverseLabelFiniteTwiceIso n hn).symm
  counitIso := reverseLabelFiniteTwiceIso n hn
  functor_unitIso_comp p := by
    apply Over.OverMorphism.ext
    rfl

instance reverseLabelFiniteFunctor_isEquivalence (n : ℕ) (hn : 1 ≤ n) :
    (reverseLabelFiniteFunctor.{u} n hn).IsEquivalence :=
  (reverseLabelFiniteEquivalence n hn).isEquivalence_functor

def reversedZeroFiberFiniteIso (n : ℕ) (hn : 1 ≤ n) (p : Over (finiteInterval.{u} n hn)) :
    (opFiniteFunctor n).obj ((fiberFiniteFunctor n hn 0).obj
      ((reverseLabelFiniteFunctor n hn).obj p)) ≅ (fiberFiniteFunctor n hn 1).obj p where
  hom := {
    map := fun x => ⟨x.val, by
      apply intervalReflect_injective
      exact x.property⟩
    map_source := fun _ _ => rfl
    map_target := fun _ _ => rfl
    map_comp := fun _ _ _ _ _ => rfl }
  inv := {
    map := fun x => ⟨x.val, by
      change intervalReflect.map (p.hom.map x.val) = (intervalVertex 0).val
      rw [x.property]
      rfl⟩
    map_source := fun _ _ => rfl
    map_target := fun _ _ => rfl
    map_comp := fun _ _ _ _ _ => rfl }
  hom_inv_id := by apply Functor.ext; rfl
  inv_hom_id := by apply Functor.ext; rfl

def reversedZeroFiberFiniteNatIso (n : ℕ) (hn : 1 ≤ n) :
    (reverseLabelFiniteFunctor.{u} n hn ⋙ fiberFiniteFunctor n hn 0) ⋙ opFiniteFunctor n ≅
      fiberFiniteFunctor n hn 1 :=
  NatIso.ofComponents (reversedZeroFiberFiniteIso n hn) (by
    intro p q F
    apply Functor.ext
    rfl)

noncomputable instance oneFiberFinite_preservesColimits (n : ℕ) (hn : 1 ≤ n) :
    Limits.PreservesColimitsOfSize.{v,w} (fiberFiniteFunctor.{u} n hn 1) :=
  Limits.preservesColimits_of_natIso (reversedZeroFiberFiniteNatIso n hn)

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory Limits

lemma labelled_pushout_finite_fibers (n : ℕ) (hn : 1 ≤ n)
    {A B C D : Over (finiteInterval.{u} n hn)}
    (f : A ⟶ B) (g : A ⟶ C) (h : B ⟶ D) (i : C ⟶ D)
    (H : IsPushout f.left g.left h.left i.left) (e : Fin 2) :
    IsPushout ((fiberFiniteFunctor n hn e).map f)
      ((fiberFiniteFunctor n hn e).map g)
      ((fiberFiniteFunctor n hn e).map h)
      ((fiberFiniteFunctor n hn e).map i) := by
  have hp : IsPushout f g h i := H.of_map_of_faithful (Over.forget (finiteInterval n hn))
  fin_cases e
  · exact hp.map (fiberFiniteFunctor n hn 0)
  · exact hp.map (fiberFiniteFunctor n hn 1)

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains.PosetTables

open CategoryTheory OmegaCategory DirectedComplex

variable {P : Type u} [PartialOrder P]

def fullOnVertices (S : Set P) : OmegaCategory.{u} :=
  ((complex P).nu.fullOn {a | tableObjectsEquiv (E := P) a ∈ S}).category

lemma segmentTableMap_objects_mem (S : Set P) (a : (complex S).nu.Objects) :
    tableObjectsEquiv (E := P) ((complexMap (OrderEmbedding.subtype S).toOrderHom).nu.objects a) ∈ S := by
  rw [Thomason.tableObjects_map]
  exact (tableObjectsEquiv (E := S) a).property

def segmentTableMap (S : Set P) : OmegaCategory.Functor (complex S).nu (fullOnVertices S) :=
  OmegaCategory.Functor.liftFullOn (C := (complex S).nu) (D := (complex P).nu)
    (complexMap (OrderEmbedding.subtype S).toOrderHom).nu
    {a : (complex P).nu.Objects | tableObjectsEquiv (E := P) a ∈ S} (by
      intro a
      exact segmentTableMap_objects_mem (P := P) S a)

lemma segmentTableMap_val (S : Set P) (x : Table (complex (↑S : Type u))) :
    ((segmentTableMap S).map x).val =
      (complexMap (OrderEmbedding.subtype S).toOrderHom).table x := rfl

lemma segmentTableMap_injective (S : Set P) : Function.Injective (segmentTableMap S).map := by
  intro x y h
  have he : (complexMap (OrderEmbedding.subtype S).toOrderHom).table x =
      (complexMap (OrderEmbedding.subtype S).toOrderHom).table y :=
    (segmentTableMap_val S x).symm.trans
      ((congrArg (fun z : (fullOnVertices S).Cell => z.val) h).trans (segmentTableMap_val S y))
  exact table_map_orderEmbedding_injective (E := (↑S : Type u)) (D := P)
    (OrderEmbedding.subtype S) he

lemma segmentTableMap_surjective (S : Set P) (hS : IsUpperSet S ∨ IsLowerSet S) :
    Function.Surjective (segmentTableMap S).map := by
  intro x
  change {x : Table (complex P) // x ∈
    ((complex P).nu.fullOn {a | tableObjectsEquiv (E := P) a ∈ S}).carrier} at x
  have hx : ∀ b, (x.val.row 0 b).val ∈ supportedOn S := by
    intro b
    cases b
    · rw [tableStart_row]
      apply bracket_mem_supportedOn
      intro a ha
      simp only [List.mem_singleton] at ha
      subst a
      exact x.property.1
    · rw [tableFinish_row]
      apply bracket_mem_supportedOn
      intro a ha
      simp only [List.mem_singleton] at ha
      subst a
      exact x.property.2
  obtain ⟨y, hy, _⟩ := table_segment_unique_lift_partial hS x.val hx
  exact ⟨y, Subtype.ext hy⟩

noncomputable def segmentTableIso (S : Set P) (hS : IsUpperSet S ∨ IsLowerSet S) :
    (complex S).nu ≅ fullOnVertices S :=
  isoOfBijective (segmentTableMap S)
    ⟨segmentTableMap_injective S, segmentTableMap_surjective S hS⟩

@[simp] lemma segmentTableIso_hom (S : Set P) (hS : IsUpperSet S ∨ IsLowerSet S) :
    (segmentTableIso S hS).hom = segmentTableMap S := rfl

end Thomason.NormalizedChains.PosetTables

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

variable {C : OmegaCategory.{u}}

def intervalFiberObjects (p : Functor C interval.{u}) (e : Fin 2) : Set C.Objects :=
  {a | p.objects a = intervalVertex e}

lemma interval_fiber_full_iff (p : Functor C interval.{u}) (e : Fin 2) (x : C.Cell) :
    p.map x = (intervalVertex e).val ↔
      C.sourceObject x ∈ intervalFiberObjects p e ∧ C.targetObject x ∈ intervalFiberObjects p e := by
  constructor
  · intro hx
    constructor
    · apply Subtype.ext
      change p.map (C.source 0 x) = _
      rw [p.map_source, hx]
      rfl
    · apply Subtype.ext
      change p.map (C.target 0 x) = _
      rw [p.map_target, hx]
      rfl
  · rintro ⟨hs, ht⟩
    apply ThinCell.ext
    · have he := congrArg ThinCell.left
        ((p.map_source 0 x).symm.trans (congrArg Subtype.val hs))
      exact he
    · have he := congrArg ThinCell.right
        ((p.map_target 0 x).symm.trans (congrArg Subtype.val ht))
      exact he

def intervalFiberFullIso (p : Functor C interval.{u}) (e : Fin 2) :
    (p.fiber (intervalVertex e)).category ≅ (C.fullOn (intervalFiberObjects p e)).category where
  hom := {
    map := fun x => ⟨x.val, (interval_fiber_full_iff p e x.val).mp x.property⟩
    map_source := fun _ _ => rfl
    map_target := fun _ _ => rfl
    map_comp := fun _ _ _ _ _ => rfl }
  inv := {
    map := fun x => ⟨x.val, (interval_fiber_full_iff p e x.val).mpr x.property⟩
    map_source := fun _ _ => rfl
    map_target := fun _ _ => rfl
    map_comp := fun _ _ _ _ _ => rfl }
  hom_inv_id := by apply Functor.ext; rfl
  inv_hom_id := by apply Functor.ext; rfl

lemma zero_fiber_isObjectSieve (p : Functor C interval.{u}) :
    C.IsObjectSieve (intervalFiberObjects p 0) := by
  intro x hx
  apply Subtype.ext
  change p.map (C.source 0 x) = _
  rw [p.map_source]
  have he : p.map (C.target 0 x) = (intervalVertex 0).val := congrArg Subtype.val hx
  rw [p.map_target] at he
  have hr : (p.map x).right.down = 0 := congrArg (fun a => a.right.down) he
  have hl : (p.map x).left.down = 0 := le_antisymm
    (by simpa only [hr] using (p.map x).related) (Fin.zero_le _)
  apply ThinCell.ext <;> apply ULift.ext <;> exact hl

def minLabel (p q : Functor C interval.{u}) : Functor C interval.{u} where
  map x := ⟨⟨min (p.map x).left.down (q.map x).left.down⟩,
    ⟨min (p.map x).right.down (q.map x).right.down⟩,
    min_le_min (p.map x).related (q.map x).related⟩
  map_source k x := by
    rw [p.map_source, q.map_source]
    cases k <;> rfl
  map_target k x := by
    rw [p.map_target, q.map_target]
    cases k <;> rfl
  map_comp k x y h h' := by
    rw [p.map_comp k x y h (p.map_composable h), q.map_comp k x y h (q.map_composable h)]
    cases k <;> rfl

lemma intervalCell_eq_vertex_iff (x : interval.{u}.Cell) (e : Fin 2) :
    x = (intervalVertex e).val ↔ x.left.down = e ∧ x.right.down = e := by
  constructor
  · intro h
    subst x
    exact ⟨rfl, rfl⟩
  · rintro ⟨hl, hr⟩
    apply ThinCell.ext
    · exact ULift.ext _ _ hl
    · exact ULift.ext _ _ hr

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

noncomputable def truncationOverFunctor (n : ℕ) (hn : 1 ≤ n) :
    Over interval.{u} ⥤ Over (finiteInterval.{u} n hn) :=
  Over.post (truncationFunctor n) ⋙
    Over.map ((truncationAdjunction n).counit.app (finiteInterval n hn))

noncomputable def truncationOverAdjunction (n : ℕ) (hn : 1 ≤ n) :
    truncationOverFunctor.{u} n hn ⊣ Over.post (nCategoryInclusion n) :=
  Over.postAdjunctionRight (Y := finiteInterval n hn) (truncationAdjunction n)

def terminalConeFiniteInclusionIso (n : ℕ) (hn : 1 ≤ n) :
    terminalConeFiniteFunctor.{u} n hn ⋙ Over.post (nCategoryInclusion n) ≅
      nCategoryInclusion n ⋙ terminalConeFunctor :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

noncomputable def truncationZeroFiberIso (n : ℕ) (hn : 1 ≤ n) :
    truncationOverFunctor.{u} n hn ⋙ fiberFiniteFunctor n hn 0 ≅
      fiberFunctor (intervalVertex 0) ⋙ truncationFunctor n :=
  Adjunction.leftAdjointUniq
    (((truncationOverAdjunction n hn).comp (zeroFiberFiniteConeAdjunction n hn)).ofNatIsoRight
      (terminalConeFiniteInclusionIso n hn))
    (zeroFiberConeAdjunction.comp (truncationAdjunction n))

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains.PosetTables

open CategoryTheory OmegaCategory DirectedComplex

variable {P : Type u} [PartialOrder P]

noncomputable def tableLabel (f : P →o Fin 2) : OmegaCategory.Functor (complex P).nu interval.{u} where
  map x := ⟨⟨f (tableStart x)⟩, ⟨f (tableFinish x)⟩, f.monotone (tableStart_le_finish x)⟩
  map_source k x := by
    apply ThinCell.ext
    · cases k <;> simp [interval, thin, ThinCell.source, ThinCell.vertex, tableStart]
    · cases k <;> simp [interval, thin, ThinCell.source, ThinCell.vertex, tableStart, tableFinish]
  map_target k x := by
    apply ThinCell.ext
    · cases k <;> simp [interval, thin, ThinCell.target, ThinCell.vertex, tableStart, tableFinish]
    · cases k <;> simp [interval, thin, ThinCell.target, ThinCell.vertex, tableFinish]
  map_comp k x y h h' := by
    apply ThinCell.ext
    · cases k <;> simp [interval, thin, ThinCell.comp, tableStart]
    · cases k with
      | zero => simp [interval, thin, ThinCell.comp, tableFinish]
      | succ k =>
        have he := congrArg (fun z => f (tableObjectsEquiv ((complex P).nu.targetObject z))) h
        simpa [interval, thin, ThinCell.comp, tableFinish] using congrArg (fun z : Fin 2 => (ULift.up z : ULift.{u} (Fin 2))) he.symm

def tableLabelFiberIso (f : P →o Fin 2) (e : Fin 2) :
    ((tableLabel f).fiber (intervalVertex e)).category ≅ fullOnVertices {a | f a = e} where
  hom := {
    map := fun x => ⟨x.val, (intervalCell_eq_vertex_iff ((tableLabel f).map x.val) e).mp x.property⟩
    map_source := fun _ _ => rfl
    map_target := fun _ _ => rfl
    map_comp := fun _ _ _ _ _ => rfl }
  inv := {
    map := fun x => ⟨x.val, (intervalCell_eq_vertex_iff ((tableLabel f).map x.val) e).mpr x.property⟩
    map_source := fun _ _ => rfl
    map_target := fun _ _ => rfl
    map_comp := fun _ _ _ _ _ => rfl }
  hom_inv_id := by apply OmegaCategory.Functor.ext; rfl
  inv_hom_id := by apply OmegaCategory.Functor.ext; rfl

noncomputable def tableFiberSegmentIso (f : P →o Fin 2) (e : Fin 2) :
    (complex {a // f a = e}).nu ≅ ((tableLabel f).fiber (intervalVertex e)).category :=
  (segmentTableIso {a | f a = e} (tableLabel_level_segment f e)).trans
    (tableLabelFiberIso f e).symm

end Thomason.NormalizedChains.PosetTables

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

def initialConeFunctor : OmegaCategory.{u} ⥤ Over interval.{u} :=
  opFunctor ⋙ terminalConeFunctor ⋙ reverseLabelFunctor

noncomputable def oneFiberConeAdjunction : fiberFunctor (intervalVertex 1) ⊣ initialConeFunctor.{u} :=
  (((reverseLabelEquivalence.toAdjunction).comp zeroFiberConeAdjunction).comp
    opEquivalence.toAdjunction).ofNatIsoLeft reversedZeroFiberNatIso

def initialConeFiniteFunctor (n : ℕ) (hn : 1 ≤ n) :
    NCategory.{u} n ⥤ Over (finiteInterval.{u} n hn) :=
  opFiniteFunctor n ⋙ terminalConeFiniteFunctor n hn ⋙ reverseLabelFiniteFunctor n hn

noncomputable def oneFiberFiniteConeAdjunction (n : ℕ) (hn : 1 ≤ n) :
    fiberFiniteFunctor.{u} n hn 1 ⊣ initialConeFiniteFunctor n hn :=
  ((((reverseLabelFiniteEquivalence n hn).toAdjunction).comp
    (zeroFiberFiniteConeAdjunction n hn)).comp
    (opFiniteEquivalence n).toAdjunction).ofNatIsoLeft (reversedZeroFiberFiniteNatIso n hn)

def initialConeFiniteInclusionIso (n : ℕ) (hn : 1 ≤ n) :
    initialConeFiniteFunctor.{u} n hn ⋙ Over.post (nCategoryInclusion n) ≅
      nCategoryInclusion n ⋙ initialConeFunctor :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

noncomputable def truncationOneFiberIso (n : ℕ) (hn : 1 ≤ n) :
    truncationOverFunctor.{u} n hn ⋙ fiberFiniteFunctor n hn 1 ≅
      fiberFunctor (intervalVertex 1) ⋙ truncationFunctor n :=
  Adjunction.leftAdjointUniq
    (((truncationOverAdjunction n hn).comp (oneFiberFiniteConeAdjunction n hn)).ofNatIsoRight
      (initialConeFiniteInclusionIso n hn))
    (oneFiberConeAdjunction.comp (truncationAdjunction n))

noncomputable def truncationFiberIso (n : ℕ) (hn : 1 ≤ n) (e : Fin 2) :
    truncationOverFunctor.{u} n hn ⋙ fiberFiniteFunctor n hn e ≅
      fiberFunctor (intervalVertex e) ⋙ truncationFunctor n := by
  by_cases he : e = 0
  · subst e
    exact truncationZeroFiberIso n hn
  · have he1 : e = 1 := by omega
    subst e
    exact truncationOneFiberIso n hn

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains.PosetTables

open CategoryTheory OmegaCategory DirectedComplex

variable {P : Type u} [PartialOrder P] {Q : Type u} [PartialOrder Q]

@[simp] lemma tableStart_map (g : P →o Q) (x : Table (complex P)) :
    tableStart ((complexMap g).table x) = g (tableStart x) := by
  change tableObjectsEquiv ((complex Q).nu.sourceObject ((complexMap g).nu.map x)) = _
  have he : (complexMap g).nu.objects ((complex P).nu.sourceObject x) =
      (complex Q).nu.sourceObject ((complexMap g).nu.map x) := by
    apply Subtype.ext
    exact (complexMap g).nu.map_source 0 x
  rw [← he]
  exact Thomason.tableObjects_map g _

@[simp] lemma tableFinish_map (g : P →o Q) (x : Table (complex P)) :
    tableFinish ((complexMap g).table x) = g (tableFinish x) := by
  change tableObjectsEquiv ((complex Q).nu.targetObject ((complexMap g).nu.map x)) = _
  have he : (complexMap g).nu.objects ((complex P).nu.targetObject x) =
      (complex Q).nu.targetObject ((complexMap g).nu.map x) := by
    apply Subtype.ext
    exact (complexMap g).nu.map_target 0 x
  rw [← he]
  exact Thomason.tableObjects_map g _

lemma tableLabel_natural (g : P →o Q) (f : Q →o Fin 2) :
    OmegaCategory.Functor.comp (complexMap g).nu (tableLabel f) = tableLabel (f.comp g) := by
  apply OmegaCategory.Functor.ext
  funext x
  apply ThinCell.ext
  · apply ULift.ext
    exact congrArg f (tableStart_map g x)
  · apply ULift.ext
    exact congrArg f (tableFinish_map g x)

noncomputable def lowerSegmentLabel (S : Set P) (hS : IsLowerSet S) : P →o Fin 2 := by
  classical
  exact {
    toFun := fun a => if a ∈ S then 0 else 1
    monotone' := by
      intro a b hab
      by_cases ha : a ∈ S
      · simp only [ite_eq_left ha]
        exact Fin.zero_le _
      · have hb : b ∉ S := fun hb => ha (hS hab hb)
        simp only [ite_eq_right ha, ite_eq_right hb, le_refl] }

@[simp] lemma lowerSegmentLabel_zero (S : Set P) (hS : IsLowerSet S) (a : P) :
    lowerSegmentLabel S hS a = 0 ↔ a ∈ S := by
  classical
  change (if a ∈ S then (0 : Fin 2) else 1) = 0 ↔ a ∈ S
  by_cases ha : a ∈ S <;> simp [ha]

end Thomason.NormalizedChains.PosetTables

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

noncomputable def truncationFiberComparison (n : ℕ) (hn : 1 ≤ n) (e : Fin 2)
    (p : Over interval.{u}) :
    (truncationFunctor n).obj ((fiberFunctor (intervalVertex e)).obj p) ⟶
      (fiberFiniteFunctor n hn e).obj ((truncationOverFunctor n hn).obj p) :=
  ((truncationAdjunction n).homEquiv _ _).symm
    ((fiberFunctor (intervalVertex e)).map ((truncationOverAdjunction n hn).unit.app p))

lemma truncationFiberComparison_unit (n : ℕ) (hn : 1 ≤ n) (e : Fin 2)
    (p : Over interval.{u}) :
    OmegaCategory.Functor.comp (truncationUnit n ((fiberFunctor (intervalVertex e)).obj p))
      (truncationFiberComparison n hn e p) =
        (fiberFunctor (intervalVertex e)).map ((truncationOverAdjunction n hn).unit.app p) :=
  ((truncationAdjunction n).homEquiv _ _).apply_symm_apply _

lemma truncationZeroFiberIso_inv_app (n : ℕ) (hn : 1 ≤ n) (p : Over interval.{u}) :
    (truncationZeroFiberIso n hn).inv.app p = truncationFiberComparison n hn 0 p := by
  apply ((truncationAdjunction n).homEquiv _ _).injective
  change OmegaCategory.Functor.comp (truncationUnit n _) ((truncationZeroFiberIso n hn).inv.app p) =
    OmegaCategory.Functor.comp (truncationUnit n _) (truncationFiberComparison n hn 0 p)
  rw [truncationFiberComparison_unit]
  let a := (((truncationOverAdjunction n hn).comp (zeroFiberFiniteConeAdjunction n hn)).ofNatIsoRight
    (terminalConeFiniteInclusionIso n hn))
  let b := zeroFiberConeAdjunction.comp (truncationAdjunction n)
  have hh := Adjunction.homEquiv_leftAdjointUniq_hom_app b a p
  change b.homEquiv p _ ((truncationZeroFiberIso n hn).inv.app p) = a.unit.app p at hh
  rw [Adjunction.comp_homEquiv] at hh
  simp only [zeroFiberConeAdjunction, truncationAdjunction,
    Adjunction.mkOfHomEquiv_homEquiv, Equiv.trans_apply] at hh
  apply Functor.ext
  funext x
  have hcell := congrArg (fun H => H.left.map x.val) hh
  change (coneExtend p.hom
    (Functor.comp (truncationUnit n ((fiberFunctor (intervalVertex 0)).obj p))
      ((truncationZeroFiberIso n hn).inv.app p))).map x.val = _ at hcell
  rw [show (coneExtend p.hom
      (Functor.comp (truncationUnit n ((fiberFunctor (intervalVertex 0)).obj p))
      ((truncationZeroFiberIso n hn).inv.app p))).map x.val =
      ConeCell.old (((truncationZeroFiberIso n hn).inv.app p).map
        ((truncationUnit n ((fiberFunctor (intervalVertex 0)).obj p)).map x)) from
    coneExtendMap_zero p.hom _ x.val x.property] at hcell
  let q := (truncationOverFunctor n hn).obj p
  have hx : q.hom.map ((truncationUnit n p.left).map x.val) = (intervalVertex 0).val := by
    have h := congrArg (fun F => F.map x.val) (Over.w ((truncationOverAdjunction n hn).unit.app p))
    exact h.trans x.property
  change ConeCell.old _ = coneExtendMap q.hom (Functor.id _) ((truncationUnit n p.left).map x.val) at hcell
  rw [coneExtendMap_zero q.hom (Functor.id _) _ hx] at hcell
  exact ConeCell.old.inj hcell

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

def fiberFiniteInclusion (n : ℕ) (hn : 1 ≤ n) (e : Fin 2)
    (p : Over (finiteInterval.{u} n hn)) :
    (fiberFiniteFunctor n hn e).obj p ⟶ p.left :=
  (p.hom.fiber (intervalVertex e)).inclusion

lemma truncationFiberComparison_inclusion (n : ℕ) (hn : 1 ≤ n) (e : Fin 2)
    (p : Over interval.{u}) :
    truncationFiberComparison n hn e p ≫
      fiberFiniteInclusion n hn e ((truncationOverFunctor n hn).obj p) =
      (truncationFunctor n).map (p.hom.fiber (intervalVertex e)).inclusion := by
  apply truncation_functor_ext
  apply Functor.ext
  funext x
  have h := congrArg (fun F => F.map x) (truncationFiberComparison_unit n hn e p)
  exact congrArg Subtype.val h

end Thomason.OmegaCategory

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_FiberComparisons
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fiber Comparisons. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

lemma oneFiberConeHomEquiv_old (p : Over interval.{u}) (B : OmegaCategory.{u})
    (F : (fiberFunctor (intervalVertex 1)).obj p ⟶ B)
    (x : ((fiberFunctor (intervalVertex 1)).obj p).Cell) :
    (oneFiberConeAdjunction.homEquiv p B F).left.map x.val = @ConeCell.old B.op (F.map x) := by
  have hx : (reverseLabel p.hom).map x.val = (intervalVertex 0).val := by
    change intervalReflect.map (p.hom.map x.val) = _
    rw [x.property]
    rfl
  let a := (reverseLabelEquivalence.toAdjunction.comp zeroFiberConeAdjunction).comp
    opEquivalence.toAdjunction
  have he := Adjunction.homEquiv_ofNatIsoLeft_apply a reversedZeroFiberNatIso F
  refine (congrArg (fun H : p ⟶ initialConeFunctor.obj B => H.left.map x.val) he).trans ?_
  dsimp only [a]
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  simp only [Equiv.trans_apply, zeroFiberConeAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  change coneExtendMap (reverseLabel p.hom)
    (Functor.comp (reversedZeroFiberIso p).hom F).op x.val = _
  exact coneExtendMap_zero _ _ _ hx

lemma oneFiberFiniteConeHomEquiv_old (n : ℕ) (hn : 1 ≤ n)
    (p : Over (finiteInterval.{u} n hn)) (B : NCategory.{u} n)
    (F : (fiberFiniteFunctor n hn 1).obj p ⟶ B)
    (x : ((fiberFiniteFunctor n hn 1).obj p).val.Cell) :
    ((oneFiberFiniteConeAdjunction n hn).homEquiv p B F).left.map x.val =
      @ConeCell.old B.val.op (F.map x) := by
  have hx : (reverseLabel p.hom).map x.val = (intervalVertex 0).val := by
    change intervalReflect.map (p.hom.map x.val) = _
    rw [x.property]
    rfl
  let a := (((reverseLabelFiniteEquivalence n hn).toAdjunction).comp
    (zeroFiberFiniteConeAdjunction n hn)).comp (opFiniteEquivalence n).toAdjunction
  have he := Adjunction.homEquiv_ofNatIsoLeft_apply a (reversedZeroFiberFiniteNatIso n hn) F
  refine (congrArg (fun H : p ⟶ (initialConeFiniteFunctor n hn).obj B => H.left.map x.val) he).trans ?_
  dsimp only [a]
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  simp only [Equiv.trans_apply, zeroFiberFiniteConeAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  change coneExtendMap (reverseLabel p.hom)
    (Functor.comp (reversedZeroFiberFiniteIso n hn p).hom F).op x.val = _
  exact coneExtendMap_zero _ _ _ hx

lemma truncationOneFiberIso_inv_app (n : ℕ) (hn : 1 ≤ n) (p : Over interval.{u}) :
    (truncationOneFiberIso n hn).inv.app p = truncationFiberComparison n hn 1 p := by
  apply ((truncationAdjunction n).homEquiv _ _).injective
  change OmegaCategory.Functor.comp (truncationUnit n _) ((truncationOneFiberIso n hn).inv.app p) =
    OmegaCategory.Functor.comp (truncationUnit n _) (truncationFiberComparison n hn 1 p)
  rw [truncationFiberComparison_unit]
  let a := (((truncationOverAdjunction n hn).comp (oneFiberFiniteConeAdjunction n hn)).ofNatIsoRight
    (initialConeFiniteInclusionIso n hn))
  let b := oneFiberConeAdjunction.comp (truncationAdjunction n)
  have hh := Adjunction.homEquiv_leftAdjointUniq_hom_app b a p
  change b.homEquiv p _ ((truncationOneFiberIso n hn).inv.app p) = a.unit.app p at hh
  rw [Adjunction.comp_homEquiv] at hh
  simp only [Equiv.trans_apply] at hh
  apply Functor.ext
  funext x
  have hcell := congrArg (fun H => H.left.map x.val) hh
  rw [oneFiberConeHomEquiv_old p _ _ x] at hcell
  let q := (truncationOverFunctor n hn).obj p
  have hx : q.hom.map ((truncationUnit n p.left).map x.val) = (intervalVertex 1).val := by
    have h := congrArg (fun F => F.map x.val) (Over.w ((truncationOverAdjunction n hn).unit.app p))
    exact h.trans x.property
  change ConeCell.old _ = ((oneFiberFiniteConeAdjunction n hn).unit.app q).left.map
    ((truncationUnit n p.left).map x.val) at hcell
  rw [← (oneFiberFiniteConeAdjunction n hn).homEquiv_id q] at hcell
  rw [oneFiberFiniteConeHomEquiv_old n hn q _ _ ⟨_, hx⟩] at hcell
  have h := ConeCell.old.inj hcell
  exact h

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

lemma truncationFiberIso_inv_app (n : ℕ) (hn : 1 ≤ n) (e : Fin 2) (p : Over interval.{u}) :
    (truncationFiberIso n hn e).inv.app p = truncationFiberComparison n hn e p := by
  by_cases he : e = 0
  · subst e
    simpa only [truncationFiberIso, dite_eq_left] using truncationZeroFiberIso_inv_app n hn p
  · have he1 : e = 1 := by omega
    subst e
    simpa only [truncationFiberIso, dite_eq_right he] using truncationOneFiberIso_inv_app n hn p

lemma truncationFiberIso_inv_inclusion (n : ℕ) (hn : 1 ≤ n) (e : Fin 2)
    (p : Over interval.{u}) :
    (truncationFiberIso n hn e).inv.app p ≫
      fiberFiniteInclusion n hn e ((truncationOverFunctor n hn).obj p) =
      (truncationFunctor n).map (p.hom.fiber (intervalVertex e)).inclusion := by
  rw [truncationFiberIso_inv_app]
  exact truncationFiberComparison_inclusion n hn e p

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory CategoryTheory.Limits OmegaCategory

noncomputable def categorificationSimplexDiagram (X : SSet.{u}) :
    CostructuredArrow uliftYoneda.{u,0,0} X ⥤ OmegaCategory.{u} :=
  CostructuredArrow.proj uliftYoneda.{u,0,0} X ⋙ raisedOrientals

noncomputable def categorificationSimplexCocone (X : SSet.{u}) :
    Cocone (categorificationSimplexDiagram X) :=
  (CategoryTheory.Functor.LeftExtension.mk categorification
    ((uliftYoneda.{u} : SimplexCategory ⥤ SSet.{u}).leftKanExtensionUnit
      raisedOrientals.{u})).coconeAt X

noncomputable def categorificationSimplexIsColimit (X : SSet.{u}) :
    IsColimit (categorificationSimplexCocone X) := by
  unfold categorificationSimplexCocone categorification
  exact CategoryTheory.Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _ _ X

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Opposite NormalizedChains NormalizedChains.PosetTables OmegaCategory

variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

noncomputable def posetTableNerveMap (P : Type u) [PartialOrder P] :
    nerve P ⟶ streetNerve (complex P).nu where
  app _ := ↾fun s => (complexMap (posetSimplexOrder s)).nu
  naturality m n f := by
    apply ConcreteCategory.hom_ext
    intro s
    change (complexMap ((posetSimplexOrder s).comp f.unop.toOrderHom)).nu =
      (DirectedComplex.Hom.comp (complexMap f.unop.toOrderHom)
        (complexMap (posetSimplexOrder s))).nu
    exact congrArg DirectedComplex.Hom.nu (complexMap_comp _ _)

lemma posetTableNerveMap_natural (f : P →o Q) :
    nerveMap f.monotone.functor ≫ posetTableNerveMap Q =
      posetTableNerveMap P ≫ streetNerveMap (complexMap f).nu := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro s
  change (complexMap (f.comp (posetSimplexOrder s))).nu =
    (DirectedComplex.Hom.comp (complexMap (posetSimplexOrder s)) (complexMap f)).nu
  exact congrArg DirectedComplex.Hom.nu (complexMap_comp _ _)

noncomputable def posetCategorificationTableMap (P : Type u) [PartialOrder P] :
    categorification.obj (nerve P) ⟶ (complex P).nu :=
  (categorificationAdjunction.homEquiv _ _).symm (posetTableNerveMap P)

lemma posetCategorificationTableMap_natural (f : P →o Q) :
    categorification.map (nerveMap f.monotone.functor) ≫ posetCategorificationTableMap Q =
      posetCategorificationTableMap P ≫ (complexMap f).nu := by
  calc
    _ = (categorificationAdjunction.homEquiv _ _).symm
        (nerveMap f.monotone.functor ≫ posetTableNerveMap Q) :=
      (categorificationAdjunction.homEquiv_naturality_left_symm
        (nerveMap f.monotone.functor) (posetTableNerveMap Q)).symm
    _ = (categorificationAdjunction.homEquiv _ _).symm
        (posetTableNerveMap P ≫ streetNerveFunctor.map (complexMap f).nu) :=
      congrArg (categorificationAdjunction.homEquiv _ _).symm
        (posetTableNerveMap_natural f)
    _ = _ := categorificationAdjunction.homEquiv_naturality_right_symm
      (posetTableNerveMap P) (complexMap f).nu

noncomputable def posetCategorificationLabel (f : P →o Fin 2) :
    categorification.obj (nerve P) ⟶ interval.{u} :=
  posetCategorificationTableMap P ≫ tableLabel f

lemma posetCategorificationLabel_natural (g : P →o Q) (f : Q →o Fin 2) :
    categorification.map (nerveMap g.monotone.functor) ≫ posetCategorificationLabel f =
      posetCategorificationLabel (f.comp g) := by
  unfold posetCategorificationLabel
  rw [← Category.assoc, posetCategorificationTableMap_natural, Category.assoc]
  exact congrArg (fun F => posetCategorificationTableMap P ≫ F) (tableLabel_natural g f)

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Opposite OmegaCategory NormalizedChains NormalizedChains.PosetTables

lemma categorification_homEquiv_app {X : SSet.{u}} {C : OmegaCategory.{u}}
    (F : categorification.obj X ⟶ C) {m : SimplexCategoryᵒᵖ} (s : X.obj m) :
    (categorificationAdjunction.homEquiv X C F).app m s =
      OmegaCategory.Functor.comp (uliftUp _) 
        ((categorificationSimplexCocone X).ι.app
          (CostructuredArrow.mk (uliftYonedaEquiv.symm s)) ≫ F) := by
  let L := (uliftYoneda.{u} : SimplexCategory ⥤ SSet.{u}).leftKanExtension raisedOrientals
  let α := (uliftYoneda.{u} : SimplexCategory ⥤ SSet.{u}).leftKanExtensionUnit raisedOrientals
  calc
    _ = streetYonedaEquiv C m
        (((Presheaf.uliftYonedaAdjunction.{0} L α).homEquiv X C F).app m s) := by
      exact congrArg (fun t => t.app m s)
        (Adjunction.homEquiv_ofNatIsoRight_apply
          (Presheaf.uliftYonedaAdjunction.{0} L α) streetYonedaIso F)
    _ = _ := congrArg (streetYonedaEquiv C m)
      (Presheaf.uliftYonedaAdjunction_homEquiv_app L α F s)

lemma posetCategorificationTableMap_leg {P : Type u} [PartialOrder P]
    {m : SimplexCategoryᵒᵖ} (s : (nerve P).obj m) :
    (categorificationSimplexCocone (nerve P)).ι.app
        (CostructuredArrow.mk (uliftYonedaEquiv.symm s)) ≫
      posetCategorificationTableMap P =
      OmegaCategory.Functor.comp (uliftDown _) (complexMap (posetSimplexOrder s)).nu := by
  have h := congrArg (fun t => t.app m s)
    ((categorificationAdjunction.homEquiv _ _).apply_symm_apply (posetTableNerveMap P))
  have hg := categorification_homEquiv_app (posetCategorificationTableMap P) s
  have he : OmegaCategory.Functor.comp (uliftUp _)
      ((categorificationSimplexCocone (nerve P)).ι.app
        (CostructuredArrow.mk (uliftYonedaEquiv.symm s)) ≫ posetCategorificationTableMap P) =
      (complexMap (posetSimplexOrder s)).nu := hg.symm.trans h
  exact congrArg (fun F => OmegaCategory.Functor.comp (uliftDown _) F) he

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Simplicial Opposite OmegaCategory NormalizedChains NormalizedChains.PosetTables

instance categorificationSimplexLeg_isIso {X : SSet.{u}} {m : SimplexCategoryᵒᵖ}
    (s : X.obj m) [IsIso (uliftYonedaEquiv.symm s)] :
    IsIso ((categorificationSimplexCocone X).ι.app
      (CostructuredArrow.mk (uliftYonedaEquiv.symm s))) := by
  change IsIso (((uliftYoneda.{u} : SimplexCategory ⥤ SSet.{u}).leftKanExtensionUnit
    raisedOrientals).app m.unop ≫ categorification.map (uliftYonedaEquiv.symm s))
  have h₁ : IsIso (((uliftYoneda.{u} : SimplexCategory ⥤ SSet.{u}).leftKanExtensionUnit
    raisedOrientals).app m.unop) := (categorificationSimplexIso.{u} m.unop).isIso_inv
  have h₂ : IsIso (categorification.map (uliftYonedaEquiv.symm s)) := inferInstance
  exact IsIso.comp_isIso' h₁ h₂

noncomputable instance posetCategorificationTableMap_ordinal_isIso (n : ℕ) :
    IsIso (posetCategorificationTableMap (ULift.{u} (Fin (n+1)))) := by
  let s : (nerve (ULift.{u} (Fin (n+1)))).obj (op ⦋n⦌) :=
    uliftYonedaEquiv (SSet.stdSimplex.isoNerve.{u} n).hom
  have hs : posetSimplexOrder s = orderULiftUp.{0,u} (Fin (n+1)) := by
    ext i
    rfl
  have hi : IsIso (uliftYonedaEquiv.symm s) := by
    have hh : uliftYonedaEquiv.symm s = (SSet.stdSimplex.isoNerve.{u} n).hom :=
      uliftYonedaEquiv.symm_apply_apply _
    exact hh ▸ (SSet.stdSimplex.isoNerve.{u} n).isIso_hom
  let leg := (categorificationSimplexCocone (nerve (ULift.{u} (Fin (n+1))))).ι.app
    (CostructuredArrow.mk (uliftYonedaEquiv.symm s))
  have he : leg ≫ posetCategorificationTableMap (ULift.{u} (Fin (n+1))) =
      (complexULiftIso.{0,u} (Fin (n+1))).hom := by
    have h := posetCategorificationTableMap_leg s
    rw [hs] at h
    exact h
  have hleg : IsIso leg := categorificationSimplexLeg_isIso s
  exact @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ hleg
    (complexULiftIso.{0,u} (Fin (n+1))).isIso_hom he

noncomputable def posetComplexFunctor : PartOrd.{u} ⥤ DirectedComplex.{u} where
  obj P := complex P
  map f := complexMap f.hom
  map_id _ := complexMap_id
  map_comp f g := complexMap_comp f.hom g.hom

lemma posetCategorificationTableMap_isIso_of_orderIso
    {P Q : Type u} [PartialOrder P] [PartialOrder Q] (e : P ≃o Q)
    [IsIso (posetCategorificationTableMap P)] :
    IsIso (posetCategorificationTableMap Q) := by
  have hN : IsIso (nerveMap e.toOrderEmbedding.toOrderHom.monotone.functor) :=
    (PartOrd.nerveFunctor.mapIso (PartOrd.Iso.mk (α := PartOrd.of P) (β := PartOrd.of Q) e)).isIso_hom
  have hT : IsIso (show (complex P).nu ⟶ (complex Q).nu from
      (complexMap e.toOrderEmbedding.toOrderHom).nu) :=
    ((posetComplexFunctor ⋙ DirectedComplex.nuFunctor).mapIso
      (PartOrd.Iso.mk (α := PartOrd.of P) (β := PartOrd.of Q) e)).isIso_hom
  have h := posetCategorificationTableMap_natural e.toOrderEmbedding.toOrderHom
  exact IsIso.of_isIso_fac_left h

theorem posetCategorificationTableMap_finiteLinear_isIso
    (P : Type u) [LinearOrder P] [Finite P] [Nonempty P] :
    IsIso (posetCategorificationTableMap P) := by
  classical
  let := Fintype.ofFinite P
  let n := Fintype.card P - 1
  have hn : Fintype.card P = n+1 := by
    have := Fintype.card_pos (α := P)
    dsimp only [n]
    omega
  let e : ULift.{u} (Fin (n+1)) ≃o P :=
    ULift.orderIso.trans (Fintype.orderIsoFinOfCardEq P hn)
  exact posetCategorificationTableMap_isIso_of_orderIso e

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Limits OmegaCategory NormalizedChains NormalizedChains.PosetTables

noncomputable def emptyOmegaIsInitial (C : OmegaCategory.{u}) [IsEmpty C.Cell] : IsInitial C :=
  IsInitial.ofUniqueHom
    (fun D => { map := isEmptyElim
                map_source := fun _ x => isEmptyElim x
                map_target := fun _ x => isEmptyElim x
                map_comp := fun _ x => isEmptyElim x })
    (fun _ F => by
      apply OmegaCategory.Functor.ext
      funext x
      exact isEmptyElim x)

theorem posetCategorificationTableMap_empty_isIso (P : Type u) [PartialOrder P] [IsEmpty P] :
    IsIso (posetCategorificationTableMap P) := by
  have : IsEmpty (complex P).nu.Cell := ⟨fun x => isEmptyElim (tableStart x)⟩
  exact isIso_of_isInitial
    ((emptyPosetNerveIsInitial P).isInitialObj categorification (nerve P))
    (emptyOmegaIsInitial (complex P).nu) _

theorem posetCategorificationTableMap_finiteLinear_isIso_all
    (P : Type u) [LinearOrder P] [Finite P] :
    IsIso (posetCategorificationTableMap P) := by
  cases isEmpty_or_nonempty P with
  | inl h => exact posetCategorificationTableMap_empty_isIso P
  | inr h => exact posetCategorificationTableMap_finiteLinear_isIso P

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory OmegaCategory NormalizedChains NormalizedChains.PosetTables

variable {P : Type u} [PartialOrder P]

lemma posetCategorification_level_mem (f : P →o Fin 2) (e : Fin 2)
    (x : (categorification.obj (nerve {a // f a = e})).Cell) :
    (posetCategorificationLabel f).map
      ((categorification.map (nerveMap (posetLevelInclusion f e).monotone.functor)).map x) =
      (intervalVertex e).val := by
  have h := congrArg (fun F => F.map x)
    (posetCategorificationLabel_natural (posetLevelInclusion f e) f)
  apply h.trans
  apply ThinCell.ext
  · apply ULift.ext
    exact (tableStart ((posetCategorificationTableMap {a // f a = e}).map x)).property
  · apply ULift.ext
    exact (tableFinish ((posetCategorificationTableMap {a // f a = e}).map x)).property

noncomputable def posetCategorificationFiberMap (f : P →o Fin 2) (e : Fin 2) :
    categorification.obj (nerve {a // f a = e}) ⟶
      ((posetCategorificationLabel f).fiber (intervalVertex e)).category :=
  ((posetCategorificationLabel f).fiber (intervalVertex e)).lift
    (categorification.map (nerveMap (posetLevelInclusion f e).monotone.functor))
      (posetCategorification_level_mem f e)

lemma posetCategorificationFiberMap_inclusion (f : P →o Fin 2) (e : Fin 2) :
    posetCategorificationFiberMap f e ≫
      ((posetCategorificationLabel f).fiber (intervalVertex e)).inclusion =
      categorification.map (nerveMap (posetLevelInclusion f e).monotone.functor) := rfl

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory OmegaCategory NormalizedChains NormalizedChains.PosetTables

variable {P : Type u} [PartialOrder P]

noncomputable def posetCategorificationTableOver (f : P →o Fin 2) :
    Over.mk (posetCategorificationLabel f) ⟶ Over.mk (tableLabel f) :=
  Over.homMk (posetCategorificationTableMap P) rfl

noncomputable def posetCategorificationTableFiberMap (f : P →o Fin 2) (e : Fin 2) :
    ((posetCategorificationLabel f).fiber (intervalVertex e)).category ⟶
      ((tableLabel f).fiber (intervalVertex e)).category :=
  (fiberFunctor (intervalVertex e)).map (posetCategorificationTableOver f)

lemma posetCategorificationFiberMap_table_fac (f : P →o Fin 2) (e : Fin 2) :
    posetCategorificationFiberMap f e ≫ posetCategorificationTableFiberMap f e =
      posetCategorificationTableMap {a // f a = e} ≫ (tableFiberSegmentIso f e).hom := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  exact congrArg (fun F => F.map x)
    (posetCategorificationTableMap_natural (posetLevelInclusion f e))

theorem posetCategorificationFiberMap_finiteLinear_isIso (P : Type u)
    [LinearOrder P] [Finite P] (f : P →o Fin 2) (e : Fin 2) :
    IsIso (posetCategorificationFiberMap f e) := by
  have hP := posetCategorificationTableMap_finiteLinear_isIso_all P
  have hS := posetCategorificationTableMap_finiteLinear_isIso_all {a // f a = e}
  have hForget : IsIso ((Over.forget interval).map (posetCategorificationTableOver f)) := hP
  have hO : IsIso (posetCategorificationTableOver f) :=
    isIso_of_reflects_iso _ (Over.forget _)
  have hF : IsIso (posetCategorificationTableFiberMap f e) :=
    CategoryTheory.Functor.map_isIso _ _
  have hT : IsIso (posetCategorificationTableMap {a // f a = e} ≫
      (tableFiberSegmentIso f e).hom) := IsIso.comp_isIso' hS (tableFiberSegmentIso f e).isIso_hom
  exact IsIso.of_isIso_fac_right (posetCategorificationFiberMap_table_fac f e)

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory OmegaCategory NormalizedChains NormalizedChains.PosetTables

variable {P : Type u} [PartialOrder P]

noncomputable def posetCategorificationFiniteFiberMap (n : ℕ) (hn : 1 ≤ n)
    (f : P →o Fin 2) (e : Fin 2) :
    (categorificationFinite n).obj (nerve {a // f a = e}) ⟶
      (fiberFiniteFunctor n hn e).obj
        ((truncationOverFunctor n hn).obj (Over.mk (posetCategorificationLabel f))) :=
  (truncationFunctor n).map (posetCategorificationFiberMap f e) ≫
    (truncationFiberIso n hn e).inv.app (Over.mk (posetCategorificationLabel f))

lemma posetCategorificationFiniteFiberMap_inclusion (n : ℕ) (hn : 1 ≤ n)
    (f : P →o Fin 2) (e : Fin 2) :
    posetCategorificationFiniteFiberMap n hn f e ≫
      fiberFiniteInclusion n hn e
        ((truncationOverFunctor n hn).obj (Over.mk (posetCategorificationLabel f))) =
      (categorificationFinite n).map
        (nerveMap (posetLevelInclusion f e).monotone.functor) := by
  have h := congrArg (fun F => (truncationFunctor n).map
    (posetCategorificationFiberMap f e) ≫ F)
      (truncationFiberIso_inv_inclusion n hn e (Over.mk (posetCategorificationLabel f)))
  exact h.trans (((truncationFunctor n).map_comp _ _).symm.trans
    (congrArg (truncationFunctor n).map (posetCategorificationFiberMap_inclusion f e)))

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory OmegaCategory NormalizedChains NormalizedChains.PosetTables

variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

noncomputable def posetCategorificationOverMap (g : P →o Q) (f : Q →o Fin 2) :
    Over.mk (posetCategorificationLabel (f.comp g)) ⟶
      Over.mk (posetCategorificationLabel f) :=
  Over.homMk (categorification.map (nerveMap g.monotone.functor))
    (posetCategorificationLabel_natural g f)

lemma posetCategorificationFiberMap_natural (g : P →o Q) (f : Q →o Fin 2) (e : Fin 2) :
    categorification.map (nerveMap (posetLevelMap g f e).monotone.functor) ≫
      posetCategorificationFiberMap f e =
    posetCategorificationFiberMap (f.comp g) e ≫
      (fiberFunctor (intervalVertex e)).map (posetCategorificationOverMap g f) := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change ((categorification.map (nerveMap (posetLevelMap g f e).monotone.functor) ≫
    categorification.map (nerveMap (posetLevelInclusion f e).monotone.functor)).map x) =
    ((categorification.map (nerveMap (posetLevelInclusion (f.comp g) e).monotone.functor) ≫
      categorification.map (nerveMap g.monotone.functor)).map x)
  apply congrArg (fun (F : categorification.obj (nerve {a // (f.comp g) a = e}) ⟶
    categorification.obj (nerve Q)) => F.map x)
  rw [← categorification.map_comp, ← categorification.map_comp]
  apply congrArg categorification.map
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  rfl

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory OmegaCategory NormalizedChains NormalizedChains.PosetTables

noncomputable def posetCategorificationFiberIsoFinite
    (P : Type u) [LinearOrder P] [Finite P] (f : P →o Fin 2) (e : Fin 2) :
    categorification.obj (nerve {a // f a = e}) ≅
      ((posetCategorificationLabel f).fiber (intervalVertex e)).category := by
  have h : IsIso (posetCategorificationFiberMap f e) :=
    posetCategorificationFiberMap_finiteLinear_isIso P f e
  exact asIso (posetCategorificationFiberMap f e)

lemma posetCategorificationFiberMap_inverse_natural
    {P Q : Type u} [LinearOrder P] [LinearOrder Q] [Finite P] [Finite Q]
    (g : P →o Q) (f : Q →o Fin 2) (e : Fin 2) :
    (fiberFunctor (intervalVertex e)).map (posetCategorificationOverMap g f) ≫
      (posetCategorificationFiberIsoFinite Q f e).inv =
    (posetCategorificationFiberIsoFinite P (f.comp g) e).inv ≫
      categorification.map (nerveMap (posetLevelMap g f e).monotone.functor) := by
  apply (Iso.eq_inv_comp (posetCategorificationFiberIsoFinite P (f.comp g) e)).mpr
  exact (Category.assoc (posetCategorificationFiberIsoFinite P (f.comp g) e).hom
    ((fiberFunctor (intervalVertex e)).map (posetCategorificationOverMap g f))
    (posetCategorificationFiberIsoFinite Q f e).inv).symm.trans
      ((Iso.comp_inv_eq (posetCategorificationFiberIsoFinite Q f e)).mpr
        (posetCategorificationFiberMap_natural g f e).symm)

end Thomason

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SimplexColimits
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simplex Colimits. -/

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory CategoryTheory.Limits Opposite OmegaCategory NormalizedChains NormalizedChains.PosetTables

noncomputable def simplexCategorificationIso (m : SimplexCategory) :
    raisedOrientals.{u}.obj m ≅ categorification.obj (nerve (ULift.{u} (Fin (m.len+1)))) :=
  (categorificationSimplexIso m).symm ≪≫
    categorification.mapIso (SSet.stdSimplex.isoNerve m.len)

lemma simplexCategorificationIso_natural {m n : SimplexCategory} (a : m ⟶ n) :
    raisedOrientals.{u}.map a ≫ (simplexCategorificationIso n).hom =
      (simplexCategorificationIso m).hom ≫
        categorification.map (nerveMap (liftedSimplexOrder a).monotone.functor) := by
  change raisedOrientals.map a ≫
      (((uliftYoneda.{u} : SimplexCategory ⥤ SSet.{u}).leftKanExtensionUnit
        raisedOrientals).app n ≫ categorification.map (SSet.stdSimplex.isoNerve n.len).hom) =
    (((uliftYoneda.{u} : SimplexCategory ⥤ SSet.{u}).leftKanExtensionUnit
        raisedOrientals).app m ≫ categorification.map (SSet.stdSimplex.isoNerve m.len).hom) ≫ _
  erw [← Category.assoc, ((uliftYoneda.{u} : SimplexCategory ⥤ SSet.{u}).leftKanExtensionUnit
    raisedOrientals).naturality a]
  change ((_ : raisedOrientals.obj m ⟶ categorification.obj (uliftYoneda.obj m)) ≫
    categorification.map (uliftYoneda.map a)) ≫
      categorification.map (SSet.stdSimplex.isoNerve n.len).hom = _
  erw [Category.assoc, ← categorification.map_comp, isoNerve_natural, categorification.map_comp,
    Category.assoc]
  rfl

noncomputable def posetSimplexDiagram (P : Type u) [PartialOrder P] :
    SimplexIndex P ⥤ OmegaCategory.{u} where
  obj s := categorification.obj (nerve (SimplexVertices s))
  map a := categorification.map (nerveMap (simplexVertexMap a).monotone.functor)
  map_id s := by
    have h : nerveMap (simplexVertexMap (𝟙 s)).monotone.functor = 𝟙 (nerve (SimplexVertices s)) := by
      apply NatTrans.ext
      funext m
      apply ConcreteCategory.hom_ext
      intro t
      apply nerve.ext_of_isThin
      rfl
    rw [h, categorification.map_id]
  map_comp a b := by
    rw [← categorification.map_comp]
    congr 1

noncomputable def posetSimplexDiagramIso (P : Type u) [PartialOrder P] :
    categorificationSimplexDiagram (nerve P) ≅ posetSimplexDiagram P :=
  NatIso.ofComponents (fun s => simplexCategorificationIso s.left)
    (fun a => simplexCategorificationIso_natural a.left)

noncomputable def posetSimplexCocone (P : Type u) [PartialOrder P] :
    Cocone (posetSimplexDiagram P) where
  pt := categorification.obj (nerve P)
  ι.app s := categorification.map (nerveMap (simplexVertexOrder s).monotone.functor)
  ι.naturality s t a := by
    change categorification.map (nerveMap (simplexVertexMap a).monotone.functor) ≫
      categorification.map (nerveMap (simplexVertexOrder t).monotone.functor) =
      categorification.map (nerveMap (simplexVertexOrder s).monotone.functor) ≫ 𝟙 _
    rw [Category.comp_id, ← categorification.map_comp]
    congr 1
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro k
    apply nerve.ext_of_isThin
    funext i
    exact congrArg (fun h : SimplexVertices s →o P => h (ULift.up (k.obj i).down))
      (simplexVertexOrder_natural a)

lemma posetSimplexCocone_leg {P : Type u} [PartialOrder P] (s : SimplexIndex P) :
    (simplexCategorificationIso s.left).hom ≫ (posetSimplexCocone P).ι.app s =
      (categorificationSimplexCocone (nerve P)).ι.app s := by
  change (_ ≫ categorification.map (SSet.stdSimplex.isoNerve s.left.len).hom) ≫
    categorification.map (nerveMap (simplexVertexOrder s).monotone.functor) = _
  rw [Category.assoc, ← categorification.map_comp, simplexVertexOrder_nerve]
  rfl

noncomputable def posetSimplexIsColimit (P : Type u) [PartialOrder P] :
    IsColimit (posetSimplexCocone P) := by
  apply (IsColimit.precomposeHomEquiv (posetSimplexDiagramIso P) _).toFun
  exact IsColimit.ofIsoColimit (categorificationSimplexIsColimit (nerve P))
    (Cocone.ext (Iso.refl _) (fun s => by
      change (categorificationSimplexCocone (nerve P)).ι.app s ≫ 𝟙 _ =
        (simplexCategorificationIso s.left).hom ≫ (posetSimplexCocone P).ι.app s
      rw [Category.comp_id]
      exact (posetSimplexCocone_leg s).symm))

noncomputable def posetSimplexOverDiagram {P : Type u} [PartialOrder P]
    (f : P →o Fin 2) : SimplexIndex P ⥤ Over interval.{u} where
  obj s := Over.mk (posetCategorificationLabel (f.comp (simplexVertexOrder s)))
  map {s t} a := Over.homMk ((posetSimplexDiagram P).map a) (by
    change categorification.map (nerveMap (simplexVertexMap a).monotone.functor) ≫
      posetCategorificationLabel (f.comp (simplexVertexOrder t)) =
        posetCategorificationLabel (f.comp (simplexVertexOrder s))
    rw [posetCategorificationLabel_natural]
    apply congrArg posetCategorificationLabel
    exact congrArg f.comp (simplexVertexOrder_natural a))
  map_id s := by
    apply Over.OverMorphism.ext
    exact (posetSimplexDiagram P).map_id s
  map_comp a b := by
    apply Over.OverMorphism.ext
    exact (posetSimplexDiagram P).map_comp a b

noncomputable def posetSimplexOverCocone {P : Type u} [PartialOrder P]
    (f : P →o Fin 2) : Cocone (posetSimplexOverDiagram f) where
  pt := Over.mk (posetCategorificationLabel f)
  ι.app s := posetCategorificationOverMap (simplexVertexOrder s) f
  ι.naturality s t a := by
    apply Over.OverMorphism.ext
    exact (posetSimplexCocone P).ι.naturality a

noncomputable def posetSimplexOverIsColimit {P : Type u} [PartialOrder P]
    (f : P →o Fin 2) : IsColimit (posetSimplexOverCocone f) :=
  isColimitOfReflects (Over.forget interval) (posetSimplexIsColimit P)

noncomputable def posetSimplexFiberIsColimit {P : Type u} [PartialOrder P]
    (f : P →o Fin 2) (e : Fin 2) :
    IsColimit ((fiberFunctor (intervalVertex e)).mapCocone (posetSimplexOverCocone f)) := by
  have : PreservesColimitsOfSize.{0,u} (fiberFunctor.{u} (intervalVertex e)) := by
    by_cases he : e = 0
    · subst e; infer_instance
    · have he1 : e = 1 := by omega
      subst e; infer_instance
  exact isColimitOfPreserves (fiberFunctor (intervalVertex e)) (posetSimplexOverIsColimit f)

lemma finiteFiberAssembly_natural
    {L M P : Type u} [LinearOrder L] [Finite L] [LinearOrder M] [Finite M]
    [PartialOrder P] (f : P →o Fin 2) (e : Fin 2)
    (σ : L →o P) (τ : M →o P) (g : L →o M) (h : τ.comp g = σ)
    (a : Over.mk (posetCategorificationLabel (f.comp σ)) ⟶
      Over.mk (posetCategorificationLabel (f.comp τ)))
    (ha : a.left = categorification.map (nerveMap g.monotone.functor)) :
    (fiberFunctor (intervalVertex e)).map a ≫
      ((posetCategorificationFiberIsoFinite M (f.comp τ) e).inv ≫
        categorification.map (nerveMap (posetLevelMap τ f e).monotone.functor)) =
    (posetCategorificationFiberIsoFinite L (f.comp σ) e).inv ≫
      categorification.map (nerveMap (posetLevelMap σ f e).monotone.functor) := by
  subst σ
  have he : a = posetCategorificationOverMap g (f.comp τ) := by
    apply Over.OverMorphism.ext
    exact ha
  rw [he]
  let sourceInverse := (posetCategorificationFiberIsoFinite L ((f.comp τ).comp g) e).inv
  let targetInverse := (posetCategorificationFiberIsoFinite M (f.comp τ) e).inv
  let fiberMap : ((posetCategorificationLabel ((f.comp τ).comp g)).fiber
      (intervalVertex e)).category ⟶
      ((posetCategorificationLabel (f.comp τ)).fiber (intervalVertex e)).category :=
    (fiberFunctor (intervalVertex e)).map (posetCategorificationOverMap g (f.comp τ))
  let firstMap := categorification.map
    (nerveMap (posetLevelMap g (f.comp τ) e).monotone.functor)
  let secondMap := categorification.map
    (nerveMap (posetLevelMap τ f e).monotone.functor)
  have naturality : fiberMap ≫ targetInverse = sourceInverse ≫ firstMap :=
    posetCategorificationFiberMap_inverse_natural g (f.comp τ) e
  change fiberMap ≫ (targetInverse ≫ secondMap) = sourceInverse ≫
    categorification.map (nerveMap (posetLevelMap (τ.comp g) f e).monotone.functor)
  calc
    _ = (fiberMap ≫ targetInverse) ≫ secondMap :=
      (Category.assoc _ _ _).symm
    _ = (sourceInverse ≫ firstMap) ≫ secondMap :=
      congrArg (fun morphism => morphism ≫ secondMap) naturality
    _ = sourceInverse ≫ (firstMap ≫ secondMap) := Category.assoc _ _ _
    _ = sourceInverse ≫
        categorification.map (nerveMap (posetLevelMap g (f.comp τ) e).monotone.functor ≫
          nerveMap (posetLevelMap τ f e).monotone.functor) :=
      congrArg (fun morphism => sourceInverse ≫ morphism)
        (categorification.map_comp _ _).symm
    _ = _ := rfl

noncomputable def posetFiberInverseCocone {P : Type u} [PartialOrder P]
    (f : P →o Fin 2) (e : Fin 2) :
    Cocone (posetSimplexOverDiagram f ⋙ fiberFunctor (intervalVertex e)) where
  pt := categorification.obj (nerve {a // f a = e})
  ι.app s := (posetCategorificationFiberIsoFinite (SimplexVertices s)
      (f.comp (simplexVertexOrder s)) e).inv ≫
    categorification.map (nerveMap (posetLevelMap (simplexVertexOrder s) f e).monotone.functor)
  ι.naturality s t a := by
    change (fiberFunctor (intervalVertex e)).map ((posetSimplexOverDiagram f).map a) ≫ _ =
      _ ≫ 𝟙 _
    rw [Category.comp_id]
    exact finiteFiberAssembly_natural f e _ _ _ (simplexVertexOrder_natural a) _ rfl

noncomputable def posetCategorificationFiberInverse {P : Type u} [PartialOrder P]
    (f : P →o Fin 2) (e : Fin 2) :
    ((posetCategorificationLabel f).fiber (intervalVertex e)).category ⟶
      categorification.obj (nerve {a // f a = e}) :=
  (posetSimplexFiberIsColimit f e).desc (posetFiberInverseCocone f e)

lemma posetCategorificationFiberInverse_fac {P : Type u} [PartialOrder P]
    (f : P →o Fin 2) (e : Fin 2) (s : SimplexIndex P) :
    (fiberFunctor (intervalVertex e)).map
        (posetCategorificationOverMap (simplexVertexOrder s) f) ≫
      posetCategorificationFiberInverse f e =
    (posetCategorificationFiberIsoFinite (SimplexVertices s)
      (f.comp (simplexVertexOrder s)) e).inv ≫
      categorification.map (nerveMap (posetLevelMap (simplexVertexOrder s) f e).monotone.functor) :=
  (posetSimplexFiberIsColimit f e).fac (posetFiberInverseCocone f e) s

lemma posetCategorificationFiberInverse_map {P : Type u} [PartialOrder P]
    (f : P →o Fin 2) (e : Fin 2) :
    posetCategorificationFiberInverse f e ≫ posetCategorificationFiberMap f e = 𝟙 _ := by
  apply (posetSimplexFiberIsColimit f e).hom_ext
  intro s
  change (fiberFunctor (intervalVertex e)).map
    (posetCategorificationOverMap (simplexVertexOrder s) f) ≫
      (posetCategorificationFiberInverse f e ≫ posetCategorificationFiberMap f e) = _
  erw [← Category.assoc, posetCategorificationFiberInverse_fac, Category.assoc,
    posetCategorificationFiberMap_natural]
  change (posetCategorificationFiberIsoFinite (SimplexVertices s)
    (f.comp (simplexVertexOrder s)) e).inv ≫
      ((posetCategorificationFiberIsoFinite (SimplexVertices s)
        (f.comp (simplexVertexOrder s)) e).hom ≫ _) = _
  erw [Iso.inv_hom_id_assoc]
  exact (Category.comp_id _).symm

lemma posetCategorificationFiberMap_inverse {P : Type u} [PartialOrder P]
    (f : P →o Fin 2) (e : Fin 2) :
    posetCategorificationFiberMap f e ≫ posetCategorificationFiberInverse f e = 𝟙 _ := by
  apply (posetSimplexIsColimit {a // f a = e}).hom_ext
  intro t
  let s : SimplexIndex P := simplexIndexMap (posetLevelInclusion f e) t
  let k : SimplexVertices t →o {i : SimplexVertices s // (f.comp (simplexVertexOrder s)) i = e} :=
    ⟨fun i => ⟨i, (simplexVertexOrder t i).property⟩, fun _ _ h => h⟩
  have hτ : categorification.map (nerveMap (simplexVertexOrder t).monotone.functor) =
      categorification.map (nerveMap k.monotone.functor) ≫
        categorification.map (nerveMap (posetLevelMap (simplexVertexOrder s) f e).monotone.functor) := by
    rw [← categorification.map_comp]
    congr 1
  change categorification.map (nerveMap (simplexVertexOrder t).monotone.functor) ≫
    (posetCategorificationFiberMap f e ≫ posetCategorificationFiberInverse f e) =
      categorification.map (nerveMap (simplexVertexOrder t).monotone.functor) ≫ 𝟙 _
  calc
    _ = (categorification.map (nerveMap k.monotone.functor) ≫
        categorification.map (nerveMap (posetLevelMap (simplexVertexOrder s) f e).monotone.functor)) ≫
      (posetCategorificationFiberMap f e ≫ posetCategorificationFiberInverse f e) := by rw [hτ]
    _ = categorification.map (nerveMap k.monotone.functor) ≫
      (posetCategorificationFiberMap (f.comp (simplexVertexOrder s)) e ≫
        ((fiberFunctor (intervalVertex e)).map
          (posetCategorificationOverMap (simplexVertexOrder s) f) ≫
            posetCategorificationFiberInverse f e)) := by
      erw [Category.assoc, ← Category.assoc _ (posetCategorificationFiberMap f e),
        posetCategorificationFiberMap_natural, Category.assoc]
    _ = categorification.map (nerveMap k.monotone.functor) ≫
      (posetCategorificationFiberMap (f.comp (simplexVertexOrder s)) e ≫
        ((posetCategorificationFiberIsoFinite (SimplexVertices s)
          (f.comp (simplexVertexOrder s)) e).inv ≫
            categorification.map (nerveMap (posetLevelMap (simplexVertexOrder s) f e).monotone.functor))) := by
      erw [posetCategorificationFiberInverse_fac]
    _ = categorification.map (nerveMap k.monotone.functor) ≫
        categorification.map (nerveMap (posetLevelMap (simplexVertexOrder s) f e).monotone.functor) := by
      change _ ≫ ((posetCategorificationFiberIsoFinite (SimplexVertices s)
        (f.comp (simplexVertexOrder s)) e).hom ≫ _) = _
      rw [Iso.hom_inv_id_assoc]
    _ = _ := by rw [← hτ, Category.comp_id]

noncomputable def posetCategorificationFiberIso {P : Type u} [PartialOrder P]
    (f : P →o Fin 2) (e : Fin 2) :
    categorification.obj (nerve {a // f a = e}) ≅
      ((posetCategorificationLabel f).fiber (intervalVertex e)).category where
  hom := posetCategorificationFiberMap f e
  inv := posetCategorificationFiberInverse f e
  hom_inv_id := posetCategorificationFiberMap_inverse f e
  inv_hom_id := posetCategorificationFiberInverse_map f e

theorem posetCategorificationFiberMap_isIso {P : Type u} [PartialOrder P]
    (f : P →o Fin 2) (e : Fin 2) : IsIso (posetCategorificationFiberMap f e) :=
  (posetCategorificationFiberIso f e).isIso_hom

theorem posetCategorificationFiniteFiberMap_isIso (n : ℕ) (hn : 1 ≤ n)
    {P : Type u} [PartialOrder P] (f : P →o Fin 2) (e : Fin 2) :
    IsIso (posetCategorificationFiniteFiberMap n hn f e) := by
  have := posetCategorificationFiberMap_isIso f e
  unfold posetCategorificationFiniteFiberMap
  exact IsIso.comp_isIso'
    (CategoryTheory.Functor.map_isIso _ _)
    ((truncationFiberIso n hn e).app (Over.mk (posetCategorificationLabel f))).isIso_inv

end Thomason

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_PosetComparison
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Poset Comparison. -/

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex
variable {E : Type u} [PartialOrder E] {D : Type v} [PartialOrder D]

def homWord (f : Hom (complex E) (complex D)) : List E → Chains D
  | [] => bracket []
  | a :: l => (f.map l.length ⟨bracket (a::l), bracket_mem_grade (a::l)⟩).val

def homTotal (f : Hom (complex E) (complex D)) : Chains E →ₗ[ℤ] Chains D :=
  Finsupp.linearCombination ℤ (fun l => homWord f l.val)

lemma homTotal_bracket (f : Hom (complex E) (complex D)) (l : List E) :
    homTotal f (bracket l) = homWord f l := by
  classical
  by_cases h : l.Pairwise (· < ·)
  · rw [bracket_of_pairwise h]
    change Finsupp.linearCombination ℤ _ (Finsupp.single _ 1) = _
    rw [Finsupp.linearCombination_single, one_smul]
  · rw [bracket_of_not_pairwise h, map_zero]
    cases l with
    | nil => exact (h (by simp)).elim
    | cons a l =>
      change 0 = (f.map l.length (⟨bracket (a::l), bracket_mem_grade (a::l)⟩ : (complex E).Chain l.length)).val
      have he : (⟨bracket (a::l), bracket_mem_grade (a::l)⟩ : (complex E).Chain l.length) = 0 :=
        Subtype.ext (bracket_of_not_pairwise h)
      erw [he, map_zero]; rfl

lemma homTotal_grade (f : Hom (complex E) (complex D)) {k : ℕ} {c : Chains E}
    (hc : c ∈ grade k) : homTotal f c ∈ grade k := by
  apply linearCombination_mem_grade _ k k _ hc
  rintro ⟨l,hl⟩ hlen
  subst k
  cases l with
  | nil => exact bracket_mem_grade ([] : List D)
  | cons a l => exact (f.map l.length ⟨bracket (a::l), bracket_mem_grade (a::l)⟩).property

lemma homTotal_positive (f : Hom (complex E) (complex D)) {c : Chains E}
    (hc : Positive c) : Positive (homTotal f c) := by
  apply linearCombination_positive _ ?_ hc
  rintro ⟨l,hl⟩
  cases l with
  | nil => exact bracket_positive []
  | cons a l => exact f.map_positive l.length _ (bracket_positive _)

end Thomason.NormalizedChains

end

end OAI
end

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


namespace Thomason.OmegaCategory
open CategoryTheory Limits
variable (C : Type u) [Category.{u} C]
def categorySkeletonObject (x : C) : (ofCategory C).OneSkeleton :=
  ⟨Arrow.mk (𝟙 x), rfl⟩
lemma categorySkeletonObject_left (x : (ofCategory C).OneSkeleton) :
    categorySkeletonObject C x.val.left = x := by
  apply Subtype.ext
  exact x.property

def categoryToSkeleton : C ⥤ (ofCategory C).OneSkeleton where
  obj := categorySkeletonObject C
  map f := ⟨Arrow.mk f, rfl, rfl, rfl⟩
  map_id _ := rfl
  map_comp {source middle target} f g := by
    apply Subtype.ext
    change Arrow.mk (f ≫ g) = Arrow.mk (f ≫ 𝟙 middle ≫ g)
    simp

lemma categorySkeleton_hom_left {x y : (ofCategory C).OneSkeleton} (f : x ⟶ y) :
    f.val.left = x.val.left := by
  have h : Arrow.mk (𝟙 f.val.left) = x.val := f.property.2.1
  have hh := congrArg (fun z : Arrow C => z.left) h
  exact hh
lemma categorySkeleton_hom_right {x y : (ofCategory C).OneSkeleton} (f : x ⟶ y) :
    f.val.right = y.val.left := by
  have h : Arrow.mk (𝟙 f.val.right) = y.val := f.property.2.2
  have hh := congrArg (fun z : Arrow C => z.left) h
  exact hh

def skeletonToCategory : (ofCategory C).OneSkeleton ⥤ C where
  obj x := x.val.left
  map f := eqToHom (categorySkeleton_hom_left C f).symm ≫ f.val.hom ≫
    eqToHom (categorySkeleton_hom_right C f)
  map_id x := by
    obtain ⟨a, rfl⟩ : ∃ a, categorySkeletonObject C a = x :=
      ⟨x.val.left, categorySkeletonObject_left C x⟩
    change 𝟙 a ≫ 𝟙 a ≫ 𝟙 a = 𝟙 a
    simp
  map_comp {x y z} f g := by
    simp only [one_comp_val]
    change eqToHom _ ≫ (f.val.hom ≫ eqToHom _ ≫ g.val.hom) ≫ eqToHom _ =
      (eqToHom _ ≫ f.val.hom ≫ eqToHom _) ≫
        (eqToHom _ ≫ g.val.hom ≫ eqToHom _)
    simp

lemma categoryToSkeleton_comp : categoryToSkeleton C ⋙ skeletonToCategory C = 𝟭 C := by
  refine CategoryTheory.Functor.ext (F := categoryToSkeleton C ⋙ skeletonToCategory C)
    (G := 𝟭 C) (fun _ => rfl) ?_
  intro x y f
  simp [categoryToSkeleton, skeletonToCategory]

lemma skeletonToCategory_comp : skeletonToCategory C ⋙ categoryToSkeleton C =
    𝟭 (ofCategory C).OneSkeleton := by
  refine CategoryTheory.Functor.ext (categorySkeletonObject_left C) ?_
  intro x y f
  apply Subtype.ext
  erw [one_eqToHom_comp_val, one_comp_eqToHom_val]
  change Arrow.mk (eqToHom _ ≫ f.val.hom ≫ eqToHom _) = f.val
  rcases f with ⟨⟨a,b,g⟩, hf⟩
  have ha : a = x.val.left := congrArg Arrow.left hf.2.1
  have hb : b = y.val.left := congrArg Arrow.left hf.2.2
  subst a; subst b
  change Arrow.mk (𝟙 _ ≫ g ≫ 𝟙 _) = Arrow.mk g
  simp

def categorySkeletonIso : Cat.of C ≅ Cat.of (ofCategory C).OneSkeleton where
  hom := (categoryToSkeleton C).toCatHom
  inv := (skeletonToCategory C).toCatHom
  hom_inv_id := by apply Cat.Hom.ext; exact categoryToSkeleton_comp C
  inv_hom_id := by apply Cat.Hom.ext; exact skeletonToCategory_comp C

instance instEssSurjNCategoryOfNatNatCatOneSkeletonCatFunctor : oneSkeletonCatFunctor.{u}.EssSurj where
  mem_essImage C := ⟨⟨ofCategory C, ofCategory_truncated C⟩, ⟨(categorySkeletonIso C).symm⟩⟩
instance instIsEquivalenceNCategoryOfNatNatCatOneSkeletonCatFunctor : oneSkeletonCatFunctor.{u}.IsEquivalence where

end Thomason.OmegaCategory

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SieveAttachments
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sieve Attachments. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.OneCat
open OmegaCategory

def nerveOfCategoryIso (C : Cat.{u,u}) : nerve C ≅ streetNerve (ofCategory C) :=
  nerveFunctor.mapIso (categorySkeletonIso C) ≪≫ (oneNerveIso (ofCategory_truncated C)).symm

instance oneUnitCatIso (C : Cat.{u,u}) :
    IsIso ((categorificationFiniteAdjunction 1).unit.app (nerveFunctor.obj C)) :=
  (categorificationFiniteAdjunction 1).isIso_unit_app_of_iso
    (X := ⟨ofCategory C,ofCategory_truncated C⟩) (nerveOfCategoryIso C)

def categorificationCatIso (C : Cat.{u,u}) : C ≅
    oneSkeletonCatFunctor.obj ((categorificationFinite 1).obj (nerveFunctor.obj C)) :=
  nerveFunctor.preimageIso (asIso ((categorificationFiniteAdjunction 1).unit.app (nerveFunctor.obj C)) ≪≫
    oneNerveIso ((categorificationFinite 1).obj (nerveFunctor.obj C)).property)

lemma categorificationCatIso_nerve (C : Cat.{u,u}) :
    nerveFunctor.map (categorificationCatIso C).hom =
      (categorificationFiniteAdjunction 1).unit.app (nerveFunctor.obj C) ≫
        (oneNerveIso ((categorificationFinite 1).obj (nerveFunctor.obj C)).property).hom := by
  exact nerveFunctor.map_preimage _

lemma categorificationCatIso_natural {C D : Cat.{u,u}} (f : C ⟶ D) :
    f ≫ (categorificationCatIso D).hom = (categorificationCatIso C).hom ≫
      oneSkeletonCatFunctor.map ((categorificationFinite 1).map (nerveFunctor.map f)) := by
  apply nerveFunctor.map_injective
  simp only [CategoryTheory.Functor.map_comp, categorificationCatIso_nerve]
  have hu := (categorificationFiniteAdjunction 1).unit.naturality (nerveFunctor.map f)
  change nerveFunctor.map f ≫ _ = _ at hu
  erw [← Category.assoc, hu]
  have h := oneNerveIso_natural
    ((categorificationFinite 1).obj (nerveFunctor.obj C)).property
    ((categorificationFinite 1).obj (nerveFunctor.obj D)).property
    ((categorificationFinite 1).map (nerveFunctor.map f))
  simp only [CategoryTheory.Functor.comp_map]
  exact congrArg ((categorificationFiniteAdjunction 1).unit.app (nerveFunctor.obj C) ≫ ·) h
end Thomason.OneCat

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason
open CategoryTheory Limits OmegaCategory
noncomputable def posetCategorificationFiniteLabel (n : ℕ) (hn : 1 ≤ n)
    {P : Type u} [PartialOrder P] (l : P →o Fin 2) :
    (categorificationFinite n).obj (nerve P) ⟶ finiteInterval n hn :=
  ((truncationOverFunctor n hn).obj (Over.mk (posetCategorificationLabel l))).hom

end Thomason

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.OmegaCategory
open CategoryTheory Limits

def constantLabel (C : OmegaCategory.{u}) (e : Fin 2) : C ⟶ interval where
  map _ := (intervalVertex e).val
  map_source k _ := by cases k <;> rfl
  map_target k _ := by cases k <;> rfl
  map_comp k _ _ _ _ := by cases k <;> rfl

@[simp] lemma comp_constantLabel {C D : OmegaCategory.{u}} (f : C ⟶ D) (e : Fin 2) :
    f ≫ constantLabel D e = constantLabel C e := rfl

def constantFiberIso (C : OmegaCategory.{u}) (e : Fin 2) :
    C ≅ ((constantLabel C e).fiber (intervalVertex e)).category where
  hom := ((constantLabel C e).fiber (intervalVertex e)).lift (𝟙 C) (fun _ => rfl)
  inv := ((constantLabel C e).fiber (intervalVertex e)).inclusion
  hom_inv_id := rfl
  inv_hom_id := rfl

lemma fiberInclusion_label {C : OmegaCategory.{u}} (q : C ⟶ interval) (e : Fin 2) :
    (q.fiber (intervalVertex e)).inclusion ≫ q =
      constantLabel (q.fiber (intervalVertex e)).category e := by
  apply Functor.ext
  funext x
  exact x.property

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.OmegaCategory
open CategoryTheory Limits

def constantFiniteFiberIso (n : ℕ) (hn : 1 ≤ n) (C : NCategory.{u} n) (e : Fin 2) :
    C ≅ (fiberFiniteFunctor n hn e).obj
      (Over.mk (X := finiteInterval n hn) (Y := C) (constantLabel C.val e)) where
  hom := (constantFiberIso C.val e).hom
  inv := (constantFiberIso C.val e).inv
  hom_inv_id := (constantFiberIso C.val e).hom_inv_id
  inv_hom_id := (constantFiberIso C.val e).inv_hom_id

theorem endpoint_finite_attachment (n : ℕ) (hn : 1 ≤ n)
    {C X Y : NCategory.{u} n} (q : C ⟶ finiteInterval n hn) (e : Fin 2)
    (a : (fiberFiniteFunctor n hn e).obj (Over.mk q) ⟶ X)
    (h : X ⟶ Y) (i : C ⟶ Y)
    (H : IsPushout a (fiberFiniteInclusion n hn e (Over.mk q)) h i) :
    ∃ (η : Y ⟶ finiteInterval n hn)
      (E : X ≅ (fiberFiniteFunctor n hn e).obj (Over.mk η)),
      E.hom ≫ fiberFiniteInclusion n hn e (Over.mk η) = h := by
  let F := fiberFiniteFunctor n hn e
  let A := F.obj (Over.mk q)
  let ξ : X ⟶ finiteInterval n hn := constantLabel X.val e
  let ξA : A ⟶ finiteInterval n hn := constantLabel A.val e
  let η : Y ⟶ finiteInterval n hn := H.desc ξ q
    ((comp_constantLabel a e).trans (fiberInclusion_label q e).symm)
  have hh : h ≫ η = ξ := H.inl_desc _ _ _
  have hi : i ≫ η = q := H.inr_desc _ _ _
  let af : Over.mk ξA ⟶ Over.mk ξ := Over.homMk a (comp_constantLabel a e)
  let gf : Over.mk ξA ⟶ Over.mk q :=
    Over.homMk (fiberFiniteInclusion n hn e (Over.mk q)) (fiberInclusion_label q e)
  let hf : Over.mk ξ ⟶ Over.mk η := Over.homMk h hh
  let iF : Over.mk q ⟶ Over.mk η := Over.homMk i hi
  have hp := labelled_pushout_finite_fibers n hn af gf hf iF H e
  let J := isoOfBijective ((nCategoryInclusion n).map (F.map gf)) (by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact hxy
    · intro x
      exact ⟨⟨x,rfl⟩,rfl⟩)
  let Jf : F.obj (Over.mk ξA) ≅ F.obj (Over.mk q) := {
    hom := J.hom, inv := J.inv, hom_inv_id := J.hom_inv_id, inv_hom_id := J.inv_hom_id }
  let : IsIso (F.map gf) := Jf.isIso_hom
  let : IsIso (F.map hf) := hp.isIso_inl_of_isIso
  let E : X ≅ F.obj (Over.mk η) := constantFiniteFiberIso n hn X e ≪≫ asIso (F.map hf)
  exact ⟨η,E,rfl⟩

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason
open CategoryTheory Limits OmegaCategory

def posetPieceFiniteFiberIso (n : ℕ) (hn : 1 ≤ n)
    {P : Type u} [PartialOrder P] (S : Set P)
    (l : P →o Fin 2) (e : Fin 2) (hS : S = {p | l p = e}) :
    (categorificationFinite n).obj (nerve S) ≅
      (fiberFiniteFunctor n hn e).obj (Over.mk (posetCategorificationFiniteLabel n hn l)) := by
  subst S
  haveI := posetCategorificationFiniteFiberMap_isIso n hn l e
  let fiberIso := asIso (posetCategorificationFiniteFiberMap n hn l e)
  exact fiberIso

lemma posetPieceFiniteFiberIso_inclusion (n : ℕ) (hn : 1 ≤ n)
    {P : Type u} [PartialOrder P] (S : Set P)
    (l : P →o Fin 2) (e : Fin 2) (hS : S = {p | l p = e}) :
    (posetPieceFiniteFiberIso n hn S l e hS).hom ≫
        fiberFiniteInclusion n hn e (Over.mk (posetCategorificationFiniteLabel n hn l)) =
      (categorificationFinite n).map (nerveMap (OrderEmbedding.subtype S).toOrderHom.monotone.functor) := by
  subst S
  exact posetCategorificationFiniteFiberMap_inclusion n hn l e

theorem poset_finite_sieve_attachment (n : ℕ) (hn : 1 ≤ n)
    {P : Type u} [PartialOrder P] (A : Set P) (hA : IsLowerSet A)
    {X Y : NCategory.{u} n}
    (a : (categorificationFinite n).obj (nerve A) ⟶ X) (h : X ⟶ Y)
    (i : (categorificationFinite n).obj (nerve P) ⟶ Y)
    (H : IsPushout a
      ((categorificationFinite n).map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)) h i) :
    ∃ S : Set Y.val.Objects, Y.val.IsObjectSieve S ∧
      ∃ e : X.val ≅ (Y.val.fullOn S).category,
        e.hom ≫ (Y.val.fullOn S).inclusion = h := by
  let l := NormalizedChains.PosetTables.lowerSegmentLabel A hA
  have hA' : A = {p | l p = 0} := by
    ext p
    exact (NormalizedChains.PosetTables.lowerSegmentLabel_zero A hA p).symm
  let E := posetPieceFiniteFiberIso n hn A l 0 hA'
  have hp : IsPushout (E.inv ≫ a)
      (fiberFiniteInclusion n hn 0 (Over.mk (posetCategorificationFiniteLabel n hn l))) h i :=
    H.of_iso E (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc])
      (by simp only [Iso.refl_hom, Category.comp_id]; exact (posetPieceFiniteFiberIso_inclusion n hn A l 0 hA').symm)
      (by simp) (by simp)
  obtain ⟨η,F,hF⟩ := endpoint_finite_attachment n hn
    (posetCategorificationFiniteLabel n hn l) 0 (E.inv ≫ a) h i hp
  refine ⟨intervalFiberObjects η 0, zero_fiber_isObjectSieve η,
    (nCategoryInclusion n).mapIso F ≪≫ intervalFiberFullIso η 0, ?_⟩
  exact hF

end Thomason

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.OmegaCategory
open CategoryTheory Limits
lemma Subcategory.inclusion_mono {C : OmegaCategory.{u}} (S : Subcategory C) :
    @Mono OmegaCategory.{u} inferInstance S.category C S.inclusion := by
  constructor
  intro Z f g he
  apply Functor.ext
  funext x
  apply Subtype.ext
  exact congrArg (fun F => F.map x) he
end Thomason.OmegaCategory

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_FiniteAttachments
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Attachments. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.Attachments
open CategoryTheory Limits OmegaCategory

def fullFinite (n : ℕ) (C : NCategory.{u} n) (T : Set C.val.Objects) : NCategory.{u} n :=
  ⟨(C.val.fullOn T).category, fun x => Subtype.ext (C.property x.val)⟩

def fullFiniteInclusion (n : ℕ) (C : NCategory.{u} n) (T : Set C.val.Objects) :
    fullFinite n C T ⟶ C := (C.val.fullOn T).inclusion

def IsPosetFiniteAttachmentPiece (n : ℕ) {P : Type u} [PartialOrder P]
    (A S : Set P) (hAS : A ⊆ S) {X Y : NCategory.{u} n}
    (a : (categorificationFinite n).obj (nerve A) ⟶ X) (h : X ⟶ Y)
    (i : (categorificationFinite n).obj (nerve P) ⟶ Y) (T : Set Y.val.Objects) : Prop :=
  ∃ (j : X ⟶ fullFinite n Y T)
    (k : (categorificationFinite n).obj (nerve S) ⟶ fullFinite n Y T),
    j ≫ fullFiniteInclusion n Y T = h ∧
    k ≫ fullFiniteInclusion n Y T = (categorificationFinite n).map
      (nerveMap (OrderEmbedding.subtype S).toOrderHom.monotone.functor) ≫ i ∧
    IsPushout a ((categorificationFinite n).map (nerveMap (subposetMap A S hAS).monotone.functor)) j k

def IsPosetFiniteNewPiece (n : ℕ) {P : Type u} [PartialOrder P]
    (S : Set P) {Y : NCategory.{u} n}
    (i : (categorificationFinite n).obj (nerve P) ⟶ Y) (T : Set Y.val.Objects) : Prop :=
  ∃ e : (categorificationFinite n).obj (nerve S) ≅ fullFinite n Y T,
    e.hom ≫ fullFiniteInclusion n Y T = (categorificationFinite n).map
      (nerveMap (OrderEmbedding.subtype S).toOrderHom.monotone.functor) ≫ i

end Thomason.Attachments

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.Attachments
open CategoryTheory Limits OmegaCategory NormalizedChains.PosetTables

def constantFiniteLabel (n : ℕ) (hn : 1 ≤ n) (C : NCategory.{u} n) (e : Fin 2) :
    C ⟶ finiteInterval n hn := constantLabel C.val e

lemma comp_constantFiniteLabel (n : ℕ) (hn : 1 ≤ n) {C D : NCategory.{u} n}
    (f : C ⟶ D) (e : Fin 2) :
    f ≫ constantFiniteLabel n hn D e = constantFiniteLabel n hn C e := by
  exact comp_constantLabel f e

variable (n : ℕ) (hn : 1 ≤ n) {P : Type u} [PartialOrder P] (A : Set P)
    (l : P →o Fin 2) (b : Fin 2) (hlA : ∀ p : A, l p.val = b)
    {X Y : NCategory.{u} n} (a : (categorificationFinite n).obj (nerve A) ⟶ X)
    (h : X ⟶ Y) (i : (categorificationFinite n).obj (nerve P) ⟶ Y)
    (H : IsPushout a
      ((categorificationFinite n).map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)) h i)

lemma fiberFiniteInclusion_mono (e : Fin 2) (Q : Over (finiteInterval.{u} n hn)) :
    Mono (fiberFiniteInclusion n hn e Q) := by
  constructor
  intro Z f g he
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  exact congrArg (fun F => F.map x) he

end Thomason.Attachments

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.Attachments
open CategoryTheory Limits OmegaCategory NormalizedChains.PosetTables

def minFiniteLabel (n : ℕ) (hn : 1 ≤ n) {C : NCategory.{u} n}
    (p q : C ⟶ finiteInterval n hn) : C ⟶ finiteInterval n hn := minLabel p q

lemma comp_minFiniteLabel (n : ℕ) (hn : 1 ≤ n) {C D : NCategory.{u} n}
    (f : C ⟶ D) (p q : D ⟶ finiteInterval n hn) :
    f ≫ minFiniteLabel n hn p q = minFiniteLabel n hn (f ≫ p) (f ≫ q) := rfl

end Thomason.Attachments

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SubdividedUnit
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subdivided Unit. -/

noncomputable section
universe u v w z


namespace Thomason.LastVertexProof
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory

lemma homotopic_weak_iff {A B : SSet.{u}} {f g : A ⟶ B} (H : Homotopic f g) :
    simplicialWeakEquivalences f ↔ simplicialWeakEquivalences g := by
  induction H with
  | rel f g H => exact simplicialWeakEquivalences_homotopy H.some
  | refl f => rfl
  | symm f g _ ih => exact ih.symm
  | trans f g h _ _ ih ih' => exact ih.trans ih'

end Thomason.LastVertexProof

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_CoherentGluing
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coherent Gluing. -/

noncomputable section
universe u v w z


namespace Thomason.KanLocal
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed Simplicial
open LastVertexProof KanHomotopy

def preHomotopy {A B : SSet.{u}} {f g : A ⟶ B} (H : SSet.Homotopy f g) (K : SSet.{u}) :
    SSet.Homotopy ((pre f).app K) ((pre g).app K) :=
  CoherentGluing.toHomotopy (curry (preHomotopyMap H ≫ (ihom.ev B).app K))
    (by apply uncurry_injective
        rw [uncurry_natural_left, uncurry_curry, uncurry_pre,
          ← Category.assoc, preHomotopyMap_zero])
    (by apply uncurry_injective
        rw [uncurry_natural_left, uncurry_curry, uncurry_pre,
          ← Category.assoc, preHomotopyMap_one])

lemma homotopic_pre_map {A B : SSet.{u}} {f g : A ⟶ B} (H : Homotopic f g) (K : SSet.{u}) :
    Homotopic ((pre f).app K) ((pre g).app K) := by
  induction H with
  | rel f g H => exact homotopic_of_homotopy (preHomotopy H.some K)
  | refl f => exact homotopic_refl _
  | symm f g _ ih => exact homotopic_symm ih
  | trans f g h _ _ ih ih' => exact homotopic_trans ih ih'

lemma local_homotopic {A B : SSet.{u}} {f g : A ⟶ B} (H : Homotopic f g)
    (hf : Local f) : Local g := fun K hK => heq_homotopic (homotopic_pre_map H K) (hf K hK)

lemma homotopic_uncurry' {A K : SSet.{u}} {f g : 𝟙_ SSet ⟶ (ihom A).obj K}
    (H : Homotopic f g) : Homotopic (uncurry' f) (uncurry' g) :=
  homotopic_pre (ρ_ A).inv (homotopic_uncurry H)

lemma homotopic_curry' {A K : SSet.{u}} {f g : A ⟶ K}
    (H : Homotopic f g) : Homotopic (curry' f) (curry' g) :=
  homotopic_curry (homotopic_pre (ρ_ A).hom H)

lemma precomp_surjective {A B K : SSet.{u}} (f : A ⟶ B) (hf : Local f)
    [SSet.KanComplex K] (a : A ⟶ K) : ∃ b : B ⟶ K, Homotopic (f ≫ b) a := by
  obtain ⟨g,hg,hh⟩ := hf K inferInstance
  refine ⟨uncurry' (curry' a ≫ g), ?_⟩
  have H := homotopic_uncurry' (homotopic_pre (curry' a) hh)
  simpa only [Category.comp_id, ← Category.assoc, uncurry'_pre, uncurry'_curry'] using H

lemma precomp_injective {A B K : SSet.{u}} (f : A ⟶ B) (hf : Local f)
    [SSet.KanComplex K] (a b : B ⟶ K) (H : Homotopic (f ≫ a) (f ≫ b)) : Homotopic a b := by
  obtain ⟨g,hg,hh⟩ := hf K inferInstance
  have H' := homotopic_post (homotopic_curry' H) g
  rw [curry'_pre, curry'_pre] at H'
  have h₀ := homotopic_pre (curry' a) hg
  have h₁ := homotopic_pre (curry' b) hg
  simp only [Category.comp_id, Category.assoc] at H' h₀ h₁
  have Q := homotopic_uncurry' (homotopic_trans (homotopic_symm h₀) (homotopic_trans H' h₁))
  simpa only [uncurry'_curry'] using Q

lemma local_weak {A B : SSet.{u}} (f : A ⟶ B) (hf : Local f) :
    simplicialWeakEquivalences f := by
  let R := Subdivision.exInfinityFunctor
  let eA : A ⟶ R.obj A := Subdivision.exInfinityComparison A
  let eB : B ⟶ R.obj B := Subdivision.exInfinityComparison B
  let : SSet.KanComplex (R.obj A) := Subdivision.exInfinity_kan A
  let : SSet.KanComplex (R.obj B) := Subdivision.exInfinity_kan B
  obtain ⟨t,Ht⟩ := precomp_surjective f hf eA
  have Ht' := homotopic_post Ht (R.map f)
  have he : eA ≫ R.map f = f ≫ eB := Subdivision.exInfinityInclusion_naturality f 0
  rw [he, Category.assoc] at Ht'
  have H := precomp_injective f hf (t ≫ R.map f) eB Ht'
  have hft : simplicialWeakEquivalences (f ≫ t) :=
    (homotopic_weak_iff Ht).mpr (Subdivision.exInfinityComparison_weak A)
  have htr : simplicialWeakEquivalences (t ≫ R.map f) :=
    (homotopic_weak_iff H).mpr (Subdivision.exInfinityComparison_weak B)
  exact simplicialWeakEquivalences.of_postcomp f t
    (simplicialWeakEquivalences_middle f t (R.map f) hft htr) hft

end Thomason.KanLocal

end

noncomputable section
universe u v w z


namespace Thomason.AttachmentComparison
open CategoryTheory Limits OmegaCategory Attachments

abbrev posetObj (n : ℕ) (P : Type u) [PartialOrder P] :=
  (categorificationFinite n).obj (nerve P)

abbrev sb (n : ℕ) {P : Type u} [PartialOrder P] (A B : Set P) (h : A ⊆ B) :=
  (categorificationFinite n).map (nerveMap (subposetMap A B h).toFunctor)

abbrev inc (n : ℕ) {P : Type u} [PartialOrder P] (A : Set P) :=
  (categorificationFinite n).map
    (nerveMap (OrderHom.Subtype.val (fun element : P => element ∈ A)).toFunctor)

@[reassoc] lemma sb_inc (n : ℕ) {P : Type u} [PartialOrder P]
    (A B : Set P) (h : A ⊆ B) : sb n A B h ≫ inc n B = inc n A := by
  rw [← (categorificationFinite n).map_comp]
  rfl

end Thomason.AttachmentComparison

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_KanTowers
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kan Towers. -/

noncomputable section
universe u v w z


namespace Thomason.KanTower
open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonoidalClosed Simplicial
open LastVertexProof KanHomotopy KanLocal KanPath
open SSet.modelCategoryQuillen

section
variable (F G : ℕᵒᵖ ⥤ SSet.{u}) (f : F ⟶ G)

variable (hF : ∀ n, SSet.KanComplex (F.obj (op n)))
  (hG : ∀ n, SSet.KanComplex (G.obj (op n)))
  (ha : ∀ n, simplicialFibrations (F.map (edge n)))
  (hb : ∀ n, simplicialFibrations (G.map (edge n)))
  (hf : ∀ n, IsHomotopyEquivalence (f.app (op n)))

include hF hG ha hb hf in
lemma path_limit_rlp : (MorphismProperty.monomorphisms SSet).rlp (right (limMap F G f)) := by
  intro D E i hi
  let : Mono i := hi
  constructor
  intro x y sq
  let X (n : ℕ) := {l : E ⟶ MappingPath (f.app (op n)) //
    i ≫ l = x ≫ stage F G f n ∧ l ≫ right (f.app (op n)) = y ≫ limit.π G (op n)}
  have seed : Nonempty (X 0) := by
    let := hF 0
    let := hG 0
    have : HasLiftingProperty i (right (f.app (op 0))) := right_rlp _ (hf 0) i hi
    let s : CommSq (x ≫ stage F G f 0) i (right (f.app (op 0)))
        (y ≫ limit.π G (op 0)) := ⟨by rw [Category.assoc, stage_right, ← Category.assoc, sq.w, Category.assoc]⟩
    exact ⟨⟨s.lift,s.fac_left,s.fac_right⟩⟩
  have step (n : ℕ) (l : X n) :
      Nonempty {l' : X (n+1) // l'.1 ≫ transition F G f n = l.1} := by
    let := hF n
    let := hF (n+1)
    let := hG n
    let := hG (n+1)
    let t : E ⟶ Matching (f.app (op n)) (G.map (edge n)) :=
      pullback.lift l.1 (y ≫ limit.π G (op (n+1))) (by rw [l.2.2, Category.assoc, limit.w])
    have : HasLiftingProperty i
        (relative (F.map (edge n)) (G.map (edge n)) (f.naturality (edge n))) :=
      relative_rlp _ _ _ (ha n) (hb n) (hf (n+1)) (hf n) i hi
    let s : CommSq (x ≫ stage F G f (n+1)) i
        (relative (F.map (edge n)) (G.map (edge n)) (f.naturality (edge n))) t := ⟨by
      apply pullback.hom_ext
      · simp only [Category.assoc, relative, pullback.lift_fst, t]
        change x ≫ (stage F G f (n+1) ≫ transition F G f n) = i ≫ l.1
        rw [stage_transition, l.2.1]
      · simp only [Category.assoc, relative, pullback.lift_snd, t]
        rw [stage_right, ← Category.assoc, sq.w, Category.assoc]⟩
    have h₁ : s.lift ≫ transition F G f n = l.1 := by
      simpa only [Category.assoc, relative, pullback.lift_fst, t, transition] using
        congrArg (fun r => r ≫ pullback.fst (right (f.app (op n))) (G.map (edge n))) s.fac_right
    have h₂ : s.lift ≫ right (f.app (op (n+1))) = y ≫ limit.π G (op (n+1)) := by
      simpa only [Category.assoc, relative, pullback.lift_snd, t] using
        congrArg (fun r => r ≫ pullback.snd (right (f.app (op n))) (G.map (edge n))) s.fac_right
    exact ⟨⟨⟨s.lift,s.fac_left,h₂⟩,h₁⟩⟩
  let lifts : ∀ n, X n := fun n => Nat.rec seed.some (fun n l => (step n l).some.1) n
  have hw (n : ℕ) : (lifts (n+1)).1 ≫ transition F G f n = (lifts n).1 :=
    (step n (lifts n)).some.2
  have hwA (n : ℕ) : ((lifts (n+1)).1 ≫ pullback.fst _ _) ≫ F.map (edge n) =
      (lifts n).1 ≫ pullback.fst _ _ := by
    simpa only [Category.assoc, transition_fst] using
      congrArg (fun r => r ≫ pullback.fst (f.app (op n)) (eval₀ (G.obj (op n)))) (hw n)
  have hwP (n : ℕ) : ((lifts (n+1)).1 ≫ pullback.snd _ _) ≫ (ihom Δ[1]).map (G.map (edge n)) =
      (lifts n).1 ≫ pullback.snd _ _ := by
    simpa only [Category.assoc, transition_snd] using
      congrArg (fun r => r ≫ pullback.snd (f.app (op n)) (eval₀ (G.obj (op n)))) (hw n)
  let A : E ⟶ limit F := limit.lift F (cone F (fun n => (lifts n).1 ≫ pullback.fst _ _) hwA)
  have hA (n : ℕ) : A ≫ limit.π F (op n) = (lifts n).1 ≫ pullback.fst _ _ :=
    limit.lift_π _ _
  let H : E ⊗ Δ[1] ⟶ limit G := limit.lift G (cone G (fun n => uncurryR ((lifts n).1 ≫ pullback.snd _ _))
    (fun n => by rw [← uncurryR_post, hwP]))
  have hH (n : ℕ) : H ≫ limit.π G (op n) = uncurryR ((lifts n).1 ≫ pullback.snd _ _) :=
    limit.lift_π _ _
  have h₀ : SSet.ι₀ ≫ H = A ≫ limMap F G f := by
    apply limit.hom_ext
    rintro ⟨n⟩
    simp only [Category.assoc, hH, ← comp_eval₀, limMap, lim_map, limMap_π]
    rw [← Category.assoc A, hA]
    simp only [Category.assoc, pullback.condition]
  have h₁ : SSet.ι₁ ≫ H = y := by
    apply limit.hom_ext
    rintro ⟨n⟩
    rw [Category.assoc, hH, ← comp_eval₁]
    exact (lifts n).2.2
  have hAx : i ≫ A = x ≫ pullback.fst (limMap F G f) (eval₀ (limit G)) := by
    apply limit.hom_ext
    rintro ⟨n⟩
    rw [Category.assoc, hA]
    simpa only [Category.assoc, stage_fst] using
      congrArg (fun r => r ≫ pullback.fst (f.app (op n)) (eval₀ (G.obj (op n)))) (lifts n).2.1
  have hHx : i ▷ Δ[1] ≫ H = uncurryR (x ≫ pullback.snd (limMap F G f) (eval₀ (limit G))) := by
    apply limit.hom_ext
    rintro ⟨n⟩
    rw [Category.assoc, hH, ← uncurryR_pre, ← Category.assoc, (lifts n).2.1,
      Category.assoc, stage_snd, ← Category.assoc, uncurryR_post]
  let l : E ⟶ MappingPath (limMap F G f) := pullback.lift A (curryR H)
    (by rw [comp_eval₀, uncurryR_curryR, h₀])
  refine ⟨⟨l, ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · simpa only [l, Category.assoc, pullback.lift_fst] using hAx
    · simp only [l, Category.assoc, pullback.lift_snd]
      apply uncurryR_injective
      rw [uncurryR_pre, uncurryR_curryR, hHx]
  · change l ≫ pullback.snd _ _ ≫ eval₁ (limit G) = y
    rw [← Category.assoc, pullback.lift_snd, comp_eval₁, uncurryR_curryR, h₁]

include hF hG ha hb hf in

lemma homotopyEquivalence_limit : IsHomotopyEquivalence (limMap F G f) := by
  rw [← fac (limMap F G f)]
  exact KanLocal.heq_comp (left_heq _) (heq_of_rlp _ (path_limit_rlp F G f hF hG ha hb hf))

end
end Thomason.KanTower

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_PosetalColimits
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Posetal Colimits. -/

noncomputable section
universe u v w z


namespace Thomason.KanLocal
open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonoidalClosed Simplicial
open LastVertexProof KanHomotopy KanPath
open SSet.modelCategoryQuillen

lemma local_colimit_nat (F G : ℕ ⥤ SSet.{u}) (f : F ⟶ G)
    (hF : ∀ n, Mono (F.map (homOfLE (Nat.le_succ n))))
    (hG : ∀ n, Mono (G.map (homOfLE (Nat.le_succ n))))
    (hf : ∀ n, Local (f.app n)) : Local (colim.map f) := by
  intro K hK
  let H := internalHom.flip.obj K
  let DF := F.op ⋙ H
  let DG := G.op ⋙ H
  let d : DG ⟶ DF := Functor.whiskerRight (NatTrans.op f) H
  have hcF : IsLimit (H.mapCone (colimit.cocone F).op) :=
    isLimitOfPreserves H (colimit.isColimit F).op
  have hcG : IsLimit (H.mapCone (colimit.cocone G).op) :=
    isLimitOfPreserves H (colimit.isColimit G).op
  let eF : (ihom (colimit F)).obj K ≅ limit DF :=
    hcF.conePointUniqueUpToIso (limit.isLimit DF)
  let eG : (ihom (colimit G)).obj K ≅ limit DG :=
    hcG.conePointUniqueUpToIso (limit.isLimit DG)
  have eFπ (n : ℕ) : eF.hom ≫ limit.π DF (op n) = (pre (colimit.ι F n)).app K :=
    hcF.conePointUniqueUpToIso_hom_comp (limit.isLimit DF) (op n)
  have eGπ (n : ℕ) : eG.hom ≫ limit.π DG (op n) = (pre (colimit.ι G n)).app K :=
    hcG.conePointUniqueUpToIso_hom_comp (limit.isLimit DG) (op n)
  have hd : IsHomotopyEquivalence (lim.map d) :=
    KanTower.homotopyEquivalence_limit DG DF d
      (fun n => by change SSet.KanComplex ((ihom (G.obj n)).obj K); infer_instance)
      (fun n => by change SSet.KanComplex ((ihom (F.obj n)).obj K); infer_instance)
      (fun n => by
        change J.rlp ((pre (G.map (homOfLE (Nat.le_succ n)))).app K)
        let := hG n
        rw [← fibrations_eq, ← HomotopicalAlgebra.fibration_iff]
        infer_instance)
      (fun n => by
        change J.rlp ((pre (F.map (homOfLE (Nat.le_succ n)))).app K)
        let := hF n
        rw [← fibrations_eq, ← HomotopicalAlgebra.fibration_iff]
        infer_instance)
      (fun n => hf n K hK)
  have hw : (pre (colim.map f)).app K ≫ eF.hom = eG.hom ≫ lim.map d := by
    apply limit.hom_ext
    rintro ⟨n⟩
    simp only [Category.assoc, eFπ, lim_map, limMap_π]
    rw [← Category.assoc, eGπ]
    change (pre (colim.map f)).app K ≫ (pre (colimit.ι F n)).app K =
      (pre (colimit.ι G n)).app K ≫ (pre (f.app n)).app K
    rw [← NatTrans.comp_app, ← pre_map, ← NatTrans.comp_app, ← pre_map,
      colimit.ι_map]
  apply heq_of_postcomp _ eF.hom (heq_of_isIso _)
  rw [hw]
  exact heq_comp (heq_of_isIso _) hd

end Thomason.KanLocal

end

noncomputable section
universe u v w z


namespace Thomason.SubdividedUnit
open CategoryTheory Limits
open AttachmentComparison Attachments KanLocal

abbrev C := categorificationFinite.{u} 1
abbrev N := streetNerveFinite.{u} 1

lemma nerve_attachment_mono {B : Type u} [PartialOrder B]
    (A : Set B) (hA : IsLowerSet A)
    {X Y : OmegaCategory.NCategory.{u} 1} (a : posetObj 1 A ⟶ X)
    (j : X ⟶ Y) (v : posetObj 1 B ⟶ Y) (sc : IsPushout a (inc 1 A) j v) :
    Mono (N.map j) := by
  obtain ⟨S,hS,e,he⟩ := poset_finite_sieve_attachment 1 (by decide) A hA a j v sc
  have hinc := OmegaCategory.Subcategory.inclusion_mono (Y.val.fullOn S)
  have hj : Mono ((OmegaCategory.nCategoryInclusion 1).map j) := by
    change @Mono OmegaCategory inferInstance X.val Y.val j
    rw [← he]
    infer_instance
  have : Mono j := (OmegaCategory.nCategoryInclusion 1).mono_of_mono_map hj
  let : PreservesLimits N := (categorificationFiniteAdjunction 1).rightAdjoint_preservesLimits
  infer_instance

end Thomason.SubdividedUnit

end

noncomputable section
universe u v w z


namespace Thomason.PosetCoproduct
open CategoryTheory Limits Opposite

variable (I P : Type u) [PartialOrder P]

variable {P}

open Attachments AttachmentComparison
def oldUp (A : Set P) (z : upward (old I A)) : upward A :=
  ⟨z.val.value, by
    obtain ⟨a,ha,haz⟩ := z.property
    exact ⟨a.value,ha,haz.2⟩⟩

def oldRetraction (A : Set P) (r : upward A →o A) : upward (old I A) →o old I A where
  toFun z := ⟨⟨z.val.label, (r (oldUp I A z)).val⟩, (r (oldUp I A z)).property⟩
  monotone' _ _ h := ⟨h.1, r.monotone h.2⟩

lemma oldRetraction_retract (A : Set P) (r : upward A →o A)
    (hr : ∀ a : A, r ⟨a.val,a.val,a.property,le_rfl⟩ = a) (a : old I A) :
    oldRetraction I A r ⟨a.val,a.val,a.property,le_rfl⟩ = a := by
  apply Subtype.ext
  apply Piece.ext
  · rfl
  · exact congrArg Subtype.val (hr ⟨a.val.value,a.property⟩)

lemma oldRetraction_adjunction (A : Set P) (r : upward A →o A)
    (hadj : ∀ (a : A) (z : upward A), a.val ≤ z.val ↔ a ≤ r z)
    (a : old I A) (z : upward (old I A)) :
    a.val ≤ z.val ↔ a ≤ oldRetraction I A r z := by
  change (_ ∧ _) ↔ (_ ∧ _)
  exact and_congr_right (fun _ => hadj ⟨a.val.value,a.property⟩ (oldUp I A z))

end Thomason.PosetCoproduct

end

noncomputable section
universe u v w z


namespace Thomason.HornAttachments
open CategoryTheory Limits Simplicial PartialOrder
open AttachmentComparison Subdivision

def upwardToMeeting {P : Type u} [PartialOrder P] (A : Set P) :
    upward (oldSet A) →o MeetingChains A where
  toFun s := ⟨s.val, (meetingChains_upward A s.val).mpr (by
    obtain ⟨t,ht,hts⟩ := s.property
    exact ⟨⟨t,ht⟩,hts⟩)⟩
  monotone' _ _ h := h

def flagRetraction {P : Type u} [PartialOrder P] (A : Set P) :
    upward (oldSet A) →o oldSet A :=
  (chainIntersection A).comp (upwardToMeeting A)

lemma flagRetraction_retract {P : Type u} [PartialOrder P] (A : Set P) (a : oldSet A) :
    flagRetraction A ⟨a.val,a.val,a.property,le_rfl⟩ = a :=
  chainIntersection_retraction A a

lemma flagRetraction_adjunction {P : Type u} [PartialOrder P] (A : Set P)
    (a : oldSet A) (s : upward (oldSet A)) :
    a.val ≤ s.val ↔ a ≤ flagRetraction A s :=
  chainIntersection_adjunction A a (upwardToMeeting A s)

def simplexFaces {m : ℕ} (K : (SSet.stdSimplex.{u}.obj ⦋m⦌).Subcomplex) :
    Set (NonemptyFiniteChains (ULift.{u} (Fin (m+1)))) :=
  {c | ∃ s : (orderedSimplexSubcomplex K : SSet).N,
    simplexChain (subcomplexN (orderedSimplexSubcomplex K) s).simplex = c}

def oldFlagsIso {m : ℕ} (K : (SSet.stdSimplex.{u}.obj ⦋m⦌).Subcomplex) :
    (SSet.sd ⋙ SSet.sd).obj (K : SSet.{u}) ≅ nerve (oldSet (simplexFaces K)) :=
  sdTwiceSimplexSubcomplexIso K ≪≫ PartOrd.nerveFunctor.mapIso
    (PartOrd.Iso.mk (α := PartOrd.of (NonemptyFiniteChains (AllowedChains (orderedSimplexSubcomplex K))))
      (β := PartOrd.of (oldSet (simplexFaces K))) (chainsSubtypeOrderIso (simplexFaces K)))

lemma oldFlagsIso_naturality {m : ℕ} (K : (SSet.stdSimplex.{u}.obj ⦋m⦌).Subcomplex) :
    (SSet.sd ⋙ SSet.sd).map K.ι ≫ (sdTwiceSimplexIso m).hom =
      (oldFlagsIso K).hom ≫ nerveMap (OrderEmbedding.subtype (oldSet (simplexFaces K))).toOrderHom.toFunctor := by
  rw [sdTwiceSimplexSubcomplexIso_naturality]
  rfl

end Thomason.HornAttachments

end

noncomputable section
universe u v w z


namespace Thomason.SubdividedUnit
open CategoryTheory Limits Simplicial PartialOrder
open Subdivision AttachmentComparison HornAttachments

def mappedCoprodIso (I : Type u) {X Y : SSet.{u}} (e : D.obj X ≅ Y) :
    D.obj (∐ fun _ : I => X) ≅ ∐ fun _ : I => Y :=
  PreservesCoproduct.iso D (fun _ : I => X) ≪≫ Sigma.mapIso (fun _ => e)

@[reassoc] lemma mappedCoprodIso_ι (I : Type u) {X Y : SSet.{u}} (e : D.obj X ≅ Y)
    (i : I) : D.map (Sigma.ι (fun _ : I => X) i) ≫ (mappedCoprodIso I e).hom =
      e.hom ≫ Sigma.ι (fun _ : I => Y) i := by
  have h : D.map (Sigma.ι (fun _ : I => X) i) ≫
      (PreservesCoproduct.iso D (fun _ : I => X)).hom =
      Sigma.ι (fun _ : I => D.obj X) i :=
    (isColimitOfHasCoproductOfPreservesColimit D (fun _ : I => X)).comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit _) (Discrete.mk i)
  simp only [mappedCoprodIso, Iso.trans_hom, ← Category.assoc, h, Sigma.ι_mapIso_hom]

abbrev BoundaryFlags (d : ℕ) : Set (Flags.{u} d) :=
  oldSet (simplexFaces (SSet.boundary.{u} d))

def simplexCoprodIso (I : Type u) (d : ℕ) :
    D.obj (∐ fun _ : I => Δ[d]) ≅ nerve (PosetCoproduct.Piece I (Flags d)) :=
  mappedCoprodIso I (sdTwiceSimplexIso d) ≪≫ PosetCoproduct.iso I (Flags d)

def boundaryCoprodIso (I : Type u) (d : ℕ) :
    D.obj (∐ fun _ : I => (∂Δ[d] : SSet)) ≅
      nerve (PosetCoproduct.old I (BoundaryFlags d)) :=
  mappedCoprodIso I (oldFlagsIso (SSet.boundary d)) ≪≫
    PosetCoproduct.oldNerveIso I (BoundaryFlags d)

@[reassoc] lemma simplexCoprodIso_ι (I : Type u) (d : ℕ) (i : I) :
    D.map (Sigma.ι (fun _ : I => Δ[d]) i) ≫ (simplexCoprodIso I d).hom =
      (sdTwiceSimplexIso d).hom ≫ nerveMap (PosetCoproduct.incl I (Flags d) i).toFunctor := by
  simp only [simplexCoprodIso, Iso.trans_hom]
  erw [mappedCoprodIso_ι_assoc]
  rw [PosetCoproduct.iso_hom_ι]

@[reassoc] lemma boundaryCoprodIso_ι (I : Type u) (d : ℕ) (i : I) :
    D.map (Sigma.ι (fun _ : I => (∂Δ[d] : SSet)) i) ≫ (boundaryCoprodIso I d).hom =
      (oldFlagsIso (SSet.boundary d)).hom ≫
        nerveMap ((PosetCoproduct.oldIso I (BoundaryFlags d)).toOrderEmbedding.toOrderHom.comp
          (PosetCoproduct.incl I (BoundaryFlags d) i)).toFunctor := by
  simp only [boundaryCoprodIso, Iso.trans_hom]
  erw [mappedCoprodIso_ι_assoc, PosetCoproduct.oldNerveIso_ι]

lemma mappedCoprodIso_naturality (I : Type u) {A B A' B' : SSet.{u}}
    (f : A ⟶ B) (g : A' ⟶ B') (eA : D.obj A ≅ A') (eB : D.obj B ≅ B')
    (h : D.map f ≫ eB.hom = eA.hom ≫ g) :
    D.map (Limits.Sigma.map (fun _ : I => f)) ≫ (mappedCoprodIso I eB).hom =
      (mappedCoprodIso I eA).hom ≫ Limits.Sigma.map (fun _ : I => g) := by
  apply (isColimitOfHasCoproductOfPreservesColimit D (fun _ : I => A)).hom_ext
  rintro ⟨i⟩
  change D.map (Sigma.ι (fun _ : I => A) i) ≫ _ =
    D.map (Sigma.ι (fun _ : I => A) i) ≫ _
  rw [← Category.assoc, ← D.map_comp, Sigma.ι_map, D.map_comp, Category.assoc,
    mappedCoprodIso_ι]
  simp only [← Category.assoc]
  rw [mappedCoprodIso_ι, h]
  simp only [Category.assoc, Sigma.ι_map]

lemma boundaryCoprodIso_naturality (I : Type u) (d : ℕ) :
    D.map (Limits.Sigma.map (fun _ : I => ∂Δ[d].ι)) ≫ (simplexCoprodIso I d).hom =
      (boundaryCoprodIso I d).hom ≫ nerveMap
        (OrderEmbedding.subtype (PosetCoproduct.old I (BoundaryFlags d))).toOrderHom.toFunctor := by
  have h := mappedCoprodIso_naturality I ∂Δ[d].ι
    (nerveMap (OrderEmbedding.subtype (BoundaryFlags d)).toOrderHom.toFunctor)
    (oldFlagsIso (SSet.boundary d)) (sdTwiceSimplexIso d)
    (oldFlagsIso_naturality (SSet.boundary d))
  have h' := PosetCoproduct.old_naturality I (BoundaryFlags d)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ (PosetCoproduct.iso I (Flags d)).hom) h).trans
    ((Category.assoc _ _ _).trans
    ((congrArg (fun q => (mappedCoprodIso I (oldFlagsIso (SSet.boundary d))).hom ≫ q) h').trans
    (Category.assoc _ _ _).symm)))

end Thomason.SubdividedUnit

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_PosetalReduction
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Posetal Reduction. -/

noncomputable section
universe u v w z
open CategoryTheory Limits

namespace Thomason.GeometricRecognition.PosetAttachment
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]
attribute [local instance] OAI.propDecidable
variable (A : Set P) (f : A →o Q)

def right (hA : IsLowerSet A) : P →o Obj A f where
  toFun b := if h : b ∈ A then Obj.inl (f ⟨b,h⟩) else Obj.inr ⟨b,h⟩
  monotone' := by
    intro b c hbc
    by_cases hb : b ∈ A <;> by_cases hc : c ∈ A
    · simp only [dite_eq_left hb,dite_eq_left hc]
      exact f.monotone (show (⟨b,hb⟩ : A) ≤ ⟨c,hc⟩ from hbc)
    · simp only [dite_eq_left hb,dite_eq_right hc]
      exact ⟨⟨b,hb⟩,hbc,le_rfl⟩
    · exact (hb (hA hbc hc)).elim
    · simp only [dite_eq_right hb,dite_eq_right hc]
      exact hbc

variable (r : {b : P // ∃ a ∈ A, a ≤ b} →o A)
variable (hadj : ∀ (a : A) (b : {b : P // ∃ a ∈ A, a ≤ b}),
  a.val ≤ b.val ↔ a ≤ r b)
variable {T : Type v} [Category T] (L : Q ⥤ T) (R : P ⥤ T)
variable (h : f.toFunctor ⋙ L = (OrderEmbedding.subtype A).toOrderHom.toFunctor ⋙ R)

lemma right_obj_desc (hA : IsLowerSet A) (b : P) :
    (desc A f r hadj L R h).obj (right A f hA b) = R.obj b := by
  change obj A f L R (if hb : b ∈ A then Obj.inl (f ⟨b,hb⟩) else Obj.inr ⟨b,hb⟩) = R.obj b
  split
  · exact agree A f L R h _
  · rfl

lemma right_mem (hA : IsLowerSet A) (b : P) (hb : b ∈ A) :
    right A f hA b = Obj.inl (f ⟨b,hb⟩) := dite_eq_left hb

lemma right_not_mem (hA : IsLowerSet A) (b : P) (hb : b ∉ A) :
    right A f hA b = Obj.inr ⟨b,hb⟩ := dite_eq_right hb

lemma right_desc (hA : IsLowerSet A) :
    (right A f hA).toFunctor ⋙ desc A f r hadj L R h = R := by
  apply CategoryTheory.Functor.hext (right_obj_desc A f r hadj L R h hA)
  intro b c g
  have hbc : b ≤ c := leOfHom g
  have hg : g = homOfLE hbc := Subsingleton.elim _ _
  subst g
  change HEq (arrow A f r hadj L R h ((right A f hA).monotone hbc))
    (R.map (homOfLE hbc))
  by_cases hb : b ∈ A <;> by_cases hc : c ∈ A
  · let p : (Obj.inl (f ⟨b,hb⟩) : Obj A f) ≤ Obj.inl (f ⟨c,hc⟩) :=
      f.monotone (show (⟨b,hb⟩ : A) ≤ ⟨c,hc⟩ from hbc)
    apply (arrow_heq A f r hadj L R h _ p
      (right_mem A f hA b hb) (right_mem A f hA c hc)).trans
    exact CategoryTheory.Functor.hcongr_hom h
      (homOfLE (show (⟨b,hb⟩ : A) ≤ ⟨c,hc⟩ from hbc))
  · let p : (Obj.inl (f ⟨b,hb⟩) : Obj A f) ≤ Obj.inr ⟨c,hc⟩ :=
      ⟨⟨b,hb⟩,hbc,le_rfl⟩
    apply (arrow_heq A f r hadj L R h _ p
      (right_mem A f hA b hb) (right_not_mem A f hA c hc)).trans
    change HEq (bridge A f r hadj L R h (f ⟨b,hb⟩) ⟨c,hc⟩ p) _
    rw [bridge_eq A f r hadj L R h (f ⟨b,hb⟩) ⟨c,hc⟩ _ ⟨b,hb⟩ hbc le_rfl]
    simp
  · exact (hb (hA hbc hc)).elim
  · let p : (Obj.inr ⟨b,hb⟩ : Obj A f) ≤ Obj.inr ⟨c,hc⟩ := hbc
    exact arrow_heq A f r hadj L R h _ p
      (right_not_mem A f hA b hb) (right_not_mem A f hA c hc)

lemma square (hA : IsLowerSet A) : f.toFunctor ⋙ (left A f).toFunctor =
    (OrderEmbedding.subtype A).toOrderHom.toFunctor ⋙ (right A f hA).toFunctor := by
  refine CategoryTheory.Functor.ext (fun a => (right_mem A f hA a.val a.property).symm) ?_
  intro a b g
  exact Subsingleton.elim _ _

lemma joint_ext (hA : IsLowerSet A) {F G : Obj A f ⥤ T}
    (hl : (left A f).toFunctor ⋙ F = (left A f).toFunctor ⋙ G)
    (hr : (right A f hA).toFunctor ⋙ F = (right A f hA).toFunctor ⋙ G) : F = G := by
  have ho (x : Obj A f) : F.obj x = G.obj x := by
    cases x with
    | inl x => exact CategoryTheory.Functor.congr_obj hl x
    | inr b =>
      have hh := CategoryTheory.Functor.congr_obj hr b.val
      change F.obj (right A f hA b.val) = G.obj (right A f hA b.val) at hh
      simpa only [right_not_mem A f hA b.val b.property] using hh
  apply CategoryTheory.Functor.hext ho
  intro x y g
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      have hg : g = (left A f).toFunctor.map (homOfLE (show x ≤ y from leOfHom g)) :=
        Subsingleton.elim _ _
      rw [hg]
      exact CategoryTheory.Functor.hcongr_hom hl _
    | inr b =>
      obtain ⟨a,ha,hxa⟩ := leOfHom g
      let k : (Obj.inl x : Obj A f) ⟶ Obj.inl (f a) := homOfLE hxa
      let t : (Obj.inl (f a) : Obj A f) ⟶ Obj.inr b :=
        eqToHom (right_mem A f hA a.val a.property).symm ≫
          (right A f hA).toFunctor.map (homOfLE ha) ≫
          eqToHom (right_not_mem A f hA b.val b.property)
      have hg : g = k ≫ t := Subsingleton.elim _ _
      rw [hg]
      apply CategoryTheory.Functor.map_comp_heq (ho _) (ho _) (ho _)
      · exact CategoryTheory.Functor.hcongr_hom hl (homOfLE hxa)
      · dsimp only [t]
        erw [F.map_comp (eqToHom (right_mem A f hA a.val a.property).symm)
            ((right A f hA).toFunctor.map (homOfLE ha) ≫ eqToHom (right_not_mem A f hA b.val b.property)),
          G.map_comp (eqToHom (right_mem A f hA a.val a.property).symm)
            ((right A f hA).toFunctor.map (homOfLE ha) ≫ eqToHom (right_not_mem A f hA b.val b.property)),
          F.map_comp ((right A f hA).toFunctor.map (homOfLE ha))
            (eqToHom (right_not_mem A f hA b.val b.property)),
          G.map_comp ((right A f hA).toFunctor.map (homOfLE ha))
            (eqToHom (right_not_mem A f hA b.val b.property)),
          eqToHom_map F (right_mem A f hA a.val a.property).symm,
          eqToHom_map G (right_mem A f hA a.val a.property).symm,
          eqToHom_map F (right_not_mem A f hA b.val b.property),
          eqToHom_map G (right_not_mem A f hA b.val b.property),
          eqToHom_comp_heq_iff, heq_eqToHom_comp_iff,
          comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
        exact CategoryTheory.Functor.hcongr_hom hr (homOfLE ha)
  | inr b =>
    cases y with
    | inl y => exact (leOfHom g).elim
    | inr c =>
      have hbc : b.val ≤ c.val := leOfHom g
      let t : (Obj.inr b : Obj A f) ⟶ Obj.inr c :=
        eqToHom (right_not_mem A f hA b.val b.property).symm ≫
          (right A f hA).toFunctor.map (homOfLE hbc) ≫
          eqToHom (right_not_mem A f hA c.val c.property)
      have hg : g = t := Subsingleton.elim _ _
      rw [hg]
      dsimp only [t]
      erw [F.map_comp (eqToHom (right_not_mem A f hA b.val b.property).symm)
          ((right A f hA).toFunctor.map (homOfLE hbc) ≫ eqToHom (right_not_mem A f hA c.val c.property)),
        G.map_comp (eqToHom (right_not_mem A f hA b.val b.property).symm)
          ((right A f hA).toFunctor.map (homOfLE hbc) ≫ eqToHom (right_not_mem A f hA c.val c.property)),
        F.map_comp ((right A f hA).toFunctor.map (homOfLE hbc))
          (eqToHom (right_not_mem A f hA c.val c.property)),
        G.map_comp ((right A f hA).toFunctor.map (homOfLE hbc))
          (eqToHom (right_not_mem A f hA c.val c.property)),
        eqToHom_map F (right_not_mem A f hA b.val b.property).symm,
        eqToHom_map G (right_not_mem A f hA b.val b.property).symm,
        eqToHom_map F (right_not_mem A f hA c.val c.property),
        eqToHom_map G (right_not_mem A f hA c.val c.property),
        eqToHom_comp_heq_iff, heq_eqToHom_comp_iff,
        comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
      exact CategoryTheory.Functor.hcongr_hom hr (homOfLE hbc)

include r hadj in

theorem isPushout (hA : IsLowerSet A) :
    IsPushout f.toFunctor.toCatHom
      (OrderEmbedding.subtype A).toOrderHom.toFunctor.toCatHom
      (left A f).toFunctor.toCatHom (right A f hA).toFunctor.toCatHom := by
  have hs : f.toFunctor.toCatHom ≫ (left A f).toFunctor.toCatHom =
      (OrderEmbedding.subtype A).toOrderHom.toFunctor.toCatHom ≫
        (right A f hA).toFunctor.toCatHom := Cat.Hom.ext (square A f hA)
  apply IsPushout.of_isColimit (c := PushoutCocone.mk
    (left A f).toFunctor.toCatHom (right A f hA).toFunctor.toCatHom hs)
  refine PushoutCocone.IsColimit.mk hs
    (fun s => (desc A f r hadj s.inl.toFunctor s.inr.toFunctor
      (congrArg Cat.Hom.toFunctor s.condition)).toCatHom) ?_ ?_ ?_
  · intro s
    exact Cat.Hom.ext (left_desc A f r hadj s.inl.toFunctor s.inr.toFunctor _)
  · intro s
    exact Cat.Hom.ext (right_desc A f r hadj s.inl.toFunctor s.inr.toFunctor _ hA)
  · intro s m hl hr
    apply Cat.Hom.ext
    apply joint_ext A f hA
    · exact (congrArg Cat.Hom.toFunctor hl).trans (left_desc A f r hadj
        s.inl.toFunctor s.inr.toFunctor _).symm
    · exact (congrArg Cat.Hom.toFunctor hr).trans (right_desc A f r hadj
        s.inl.toFunctor s.inr.toFunctor _ hA).symm
end Thomason.GeometricRecognition.PosetAttachment

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial PartialOrder Opposite

namespace Thomason.GeometricRecognition.Posetal
open OmegaCategory AttachmentComparison HornAttachments SubdividedUnit

lemma pushout_posetal {P : Type u} [PartialOrder P] (A : Set P) (hA : IsLowerSet A)
    (r : upward A →o A) (hadj : ∀ (a : A) (b : upward A), a.val ≤ b.val ↔ a ≤ r b)
    {X Y : Cat.{u,u}} (a : Cat.of A ⟶ X) (j : X ⟶ Y) (v : Cat.of P ⟶ Y)
    (sc : IsPushout a (OrderEmbedding.subtype A).toOrderHom.toFunctor.toCatHom j v)
    (hX : IsPosetal X) : IsPosetal Y := by
  obtain ⟨Q,⟨e⟩⟩ := hX
  let f : A →o Q := {
    toFun := fun x : A => (a ≫ e.hom).toFunctor.obj x
    monotone' := fun x y h => @leOfHom Q inferInstance _ _
      ((a ≫ e.hom).toFunctor.map (@homOfLE A inferInstance x y h)) }
  have hf : a ≫ e.hom = f.toFunctor.toCatHom := by
    apply Cat.Hom.ext
    exact CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => @Subsingleton.elim _ (Preorder.subsingleton_hom (α := Q) _ _) _ _)
  have sq : IsPushout f.toFunctor.toCatHom
      (OrderEmbedding.subtype A).toOrderHom.toFunctor.toCatHom (e.inv ≫ j) v := by
    apply sc.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
    · simpa only [Iso.refl_hom,Category.id_comp] using hf
    · simp
    · simp
    · simp
  let ht := PosetAttachment.isPushout A f r hadj hA
  exact ⟨PartOrd.of (PosetAttachment.Obj A f),
    ⟨sq.isColimit.coconePointUniqueUpToIso ht.isColimit⟩⟩

abbrev CC : SSet.{u} ⥤ Cat.{u,u} := C ⋙ oneSkeletonCatFunctor

lemma initial_posetal {X : SSet.{u}} (hX : IsInitial X) : IsPosetal (CC.obj X) := by
  let P := ULift.{u} Empty
  let : PartialOrder P := inferInstance
  have hP : IsInitial (nerve P) := SSet.isInitialOfNotNonempty (by
    rintro ⟨s⟩
    exact (s.obj 0).down.elim)
  exact ⟨PartOrd.of P, ⟨CC.mapIso (hX.uniqueUpToIso hP) ≪≫
    (OneCat.categorificationCatIso (Cat.of P)).symm⟩⟩

lemma boundary_posetal_successor (I : Type u) (d : ℕ) {X Y : SSet.{u}}
    (a : (∐ fun _ : I => (∂Δ[d] : SSet)) ⟶ X) (j : X ⟶ Y)
    (v : (∐ fun _ : I => Δ[d]) ⟶ Y)
    (sc : IsPushout a (Limits.Sigma.map (fun _ : I => ∂Δ[d].ι)) j v)
    (hX : IsPosetal (CC.obj (D.obj X))) : IsPosetal (CC.obj (D.obj Y)) := by
  let A := PosetCoproduct.old I (BoundaryFlags d)
  let rA := PosetCoproduct.oldRetraction I (BoundaryFlags d)
    (flagRetraction (simplexFaces (SSet.boundary d)))
  have hA : IsLowerSet A := PosetCoproduct.old_lower I _ (oldSet_lower _)
  have hadj : ∀ (a : A) (z : upward A), a.val ≤ z.val ↔ a ≤ rA z :=
    PosetCoproduct.oldRetraction_adjunction I _ _ (flagRetraction_adjunction _)
  let a' := (boundaryCoprodIso I d).inv ≫ D.map a
  let v' := (simplexCoprodIso I d).inv ≫ D.map v
  let i : nerve A ⟶ nerve (PosetCoproduct.Piece I (Flags d)) :=
    nerveMap (OrderEmbedding.subtype A).toOrderHom.toFunctor
  have sq : IsPushout a' i (D.map j) v' := by
    apply (sc.map D).of_iso (boundaryCoprodIso I d) (Iso.refl _)
      (simplexCoprodIso I d) (Iso.refl _)
    · simp [a']
    · exact boundaryCoprodIso_naturality I d
    · simp
    · simp [v']
  let eA : Cat.of A ≅ CC.obj (nerve A) := OneCat.categorificationCatIso (Cat.of A)
  let eP : Cat.of (PosetCoproduct.Piece I (Flags d)) ≅
      CC.obj (nerve (PosetCoproduct.Piece I (Flags d))) :=
    OneCat.categorificationCatIso (Cat.of (PosetCoproduct.Piece I (Flags d)))
  have sqC : IsPushout (eA.hom ≫ CC.map a')
      (OrderEmbedding.subtype A).toOrderHom.toFunctor.toCatHom
      (CC.map (D.map j)) (eP.hom ≫ CC.map v') := by
    apply (sq.map CC).of_iso eA.symm (Iso.refl _) eP.symm (Iso.refl _)
    · simp
    · have hn := OneCat.categorificationCatIso_natural
        ((OrderEmbedding.subtype A).toOrderHom.toFunctor.toCatHom :
          Cat.of A ⟶ Cat.of (PosetCoproduct.Piece I (Flags d)))
      change _ ≫ eP.hom = eA.hom ≫ CC.map i at hn
      have hh := congrArg (fun f => eA.inv ≫ f ≫ eP.inv) hn
      simp only [Category.assoc,Iso.hom_inv_id,Iso.inv_hom_id_assoc,Category.comp_id] at hh
      exact hh.symm
    · simp
    · simp
  exact pushout_posetal A hA rA hadj _ _ _ sqC hX

lemma skeleton_posetal (K : SSet.{u}) (d : ℕ) :
    IsPosetal (CC.obj (D.obj ((SSet.relativeCellComplex K).F.obj d))) := by
  induction d with
  | zero =>
    apply initial_posetal
    apply IsInitial.isInitialObj
    have h₀ : IsInitial (⊥ : K.Subcomplex).toSSet :=
      SSet.isInitialOfNotNonempty (by rintro ⟨s⟩; exact s.property)
    exact h₀.ofIso (SSet.relativeCellComplex K).isoBot.symm
  | succ d ih =>
    exact boundary_posetal_successor
      (SSet.relativeCellComplexOfMono.Cell (SSet.Subcomplex.ι (⊥ : K.Subcomplex)) d) d
      (SSet.relativeCellComplexOfMono.t _ d) (SSet.relativeCellComplexOfMono.r _ d)
      (SSet.relativeCellComplexOfMono.b _ d) (SSet.relativeCellComplexOfMono.isPushout _ d) ih

theorem categorification_sdTwice_posetal (K : SSet.{u}) : IsPosetal (CC.obj (D.obj K)) := by
  let c := SSet.relativeCellComplex K
  let F := c.F ⋙ D ⋙ C ⋙ N
  let : PreservesFilteredColimitsOfSize.{0,0} N :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits N
  have hc : IsColimit ((D ⋙ C ⋙ N).mapCocone { pt := K, ι := c.incl }) :=
    isColimitOfPreserves (D ⋙ C ⋙ N) c.isColimit
  have hstage (d : ℕ) := property_of_isPosetal (skeleton_posetal K d)
  let nerveIso (simplicialSet : SSet.{u}) :
      N.obj (C.obj simplicialSet) ≅ nerve (CC.obj simplicialSet) :=
    oneNerveIso (C.obj simplicialSet).property
  have ht : ∀ d, EdgeThin (F.obj d) := fun d =>
    edgeThin_of_mono (nerveIso (D.obj (c.F.obj d))).hom
      (nerve_edgeThin _ (hstage d))
  have ha : ∀ d, EdgeAntisym (F.obj d) := fun d =>
    edgeAntisym_of_mono (nerveIso (D.obj (c.F.obj d))).hom
      (nerve_edgeAntisym _ (hstage d))
  apply isPosetal_of_property
  apply property_of_nerve_edges
  · exact edgeThin_of_mono (nerveIso (D.obj K)).inv
      (edgeThin_colimit hc ht)
  · exact edgeAntisym_of_mono (nerveIso (D.obj K)).inv
      (edgeAntisym_colimit hc ha)
end Thomason.GeometricRecognition.Posetal

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory MonoidalClosed

namespace Thomason.KanLocal
open LastVertexProof

lemma local_of_precomp {A B C : SSet.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (hf : Local f) (hfg : Local (f ≫ g)) : Local g := by
  intro K hK
  have h := hfg K hK
  rw [pre_map,NatTrans.comp_app] at h
  exact heq_of_postcomp _ _ (hf K hK) h

end Thomason.KanLocal

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SimplicialApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simplicial Approximation. -/

noncomputable section
universe u v w z
open PartialOrder

namespace Thomason.GeometricRecognition.PolyPoint
variable {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]

local instance polyMapsDecEqP_r85291b_1 : DecidableEq P := Classical.decEq P
attribute [local instance] OAI.Thomason.GeometricRecognition.PolyPoint.polyMapsDecEqQ
lemma segment_support (x y : PolyPoint P) (h) (t : unitInterval) :
    (segment x y h t).weights.support ⊆ x.weights.support ∪ y.weights.support := by
  intro p hp
  rcases Finset.mem_union.mp (Finsupp.support_add hp) with hp | hp
  · exact Finset.mem_union_left _ (Finsupp.support_smul hp)
  · exact Finset.mem_union_right _ (Finsupp.support_smul hp)

def imageChain (f : P → Q) (hf : PreservesChains f) (s : NonemptyFiniteChains P) :
    NonemptyFiniteChains Q where
  finset := s.finset.image f
  nonempty := s.nonempty.image f
  comparable a b := (hf s).total a.property b.property

def orientedMap (f : P → Q) (hf : PreservesChains f) : NonemptyFiniteChains P →o Q where
  toFun s := greatest (imageChain f hf s)
  monotone' _ _ h := greatest_mono (Finset.image_subset_image h)

lemma orientedMap_mem (f : P → Q) (hf : PreservesChains f) (s : NonemptyFiniteChains P) :
    ∃ p ∈ s.finset, orientedMap f hf s = f p := by
  obtain ⟨p,hp,he⟩ := Finset.mem_image.mp (greatest_mem (imageChain f hf s))
  exact ⟨p,hp,he.symm⟩

lemma oriented_support (f : P → Q) (hf : PreservesChains f)
    (x : PolyPoint (NonemptyFiniteChains P)) :
    (map (orientedMap f hf) (preservesChains_monotone _) x).weights.support ⊆
      (subdivide x).weights.support.image f := by
  intro q hq
  obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp (map_support _ _ x hq)
  obtain ⟨p,hp,he⟩ := orientedMap_mem f hf s
  apply Finset.mem_image.mpr
  refine ⟨p,?_,he.symm⟩
  change p ∈ (barycentricLinear x.weights).support
  rw [barycentricLinear_support_eq x.weights x.nonneg]
  exact Finset.mem_biUnion.mpr ⟨s,hs,hp⟩

def carrierHomotopy {A : Type*} [TopologicalSpace A] [CompactSpace A]
    (f g : C(A, PolyPoint P))
    (h : ∀ a, IsChain (· ≤ ·) (((f a).weights.support ∪ (g a).weights.support : Finset P) : Set P)) :
    f.Homotopy g where
  toFun z := segment (f z.2) (g z.2) (h z.2) z.1
  continuous_toFun := by
    obtain ⟨s,hs⟩ := compact_finite_carrier (isCompact_range f.continuous)
    obtain ⟨t,ht⟩ := compact_finite_carrier (isCompact_range g.continuous)
    apply continuous_of_finite_carrier _ (s ∪ t)
    · intro z p hp
      rcases Finset.mem_union.mp (segment_support _ _ _ _ hp) with hp | hp
      · exact Finset.mem_union_left _ (hs _ ⟨z.2,rfl⟩ hp)
      · exact Finset.mem_union_right _ (ht _ ⟨z.2,rfl⟩ hp)
    · intro p
      have ht : Continuous (fun z : unitInterval × A => (z.1 : ℝ)) :=
        continuous_subtype_val.comp continuous_fst
      exact ((continuous_const.sub ht).mul ((continuous_weights p).comp
        (f.continuous.comp continuous_snd))).add
        (ht.mul ((continuous_weights p).comp (g.continuous.comp continuous_snd)))
  map_zero_left a := segment_zero _ _ _
  map_one_left a := segment_one _ _ _

lemma carrierHomotopy_fixed {A : Type*} [TopologicalSpace A] [CompactSpace A]
    (f g : C(A, PolyPoint P)) (h) (a : A) (ha : f a = g a) (t : unitInterval) :
    carrierHomotopy f g h (t,a) = f a := by
  change segment (f a) (g a) (h a) t = f a
  apply PolyPoint.ext
  change (1 - t.val) • (f a).weights + t.val • (g a).weights = (f a).weights
  rw [← ha, ← add_smul]
  simp

lemma eq_vertex_of_support_subset (x : PolyPoint P) (p : P)
    (h : x.weights.support ⊆ {p}) : x = vertex p := by
  have ht : x.weights p = 1 := by
    calc
      x.weights p = x.weights.sum (fun _ r => r) := by
        symm
        convert Finsupp.sum_of_support_subset x.weights h (fun _ r => r) (by simp) using 1
        all_goals try with_reducible_and_instances rfl
        simp
      _ = 1 := x.total
  apply PolyPoint.ext
  ext q
  by_cases hpq : p = q
  · subst q
    simpa only [vertex_weights, ite_true] using ht
  · have hq : q ∉ x.weights.support := fun hq => hpq (Finset.mem_singleton.mp (h hq)).symm
    simpa only [vertex_weights, ite_eq_right hpq] using Finsupp.notMem_support_iff.mp hq

end Thomason.GeometricRecognition.PolyPoint

end

noncomputable section
universe u v w z
open PartialOrder

namespace Thomason.GeometricRecognition
namespace Approximation
open PolyPoint Mesh
variable {P : Type u} [PartialOrder P]

attribute [local instance] OAI.Thomason.GeometricRecognition.Approximation.approximationDecEqP
lemma evaluate_coordinates [Fintype P] (x : PolyPoint P) :
    evaluate coordinateVertex x = fun p => x.weights p := by
  classical
  funext p
  rw [evaluate_eq_sum, Finset.sum_apply]
  simp [coordinateVertex, smul_eq_mul, mul_ite]
  exact fun h => h.symm

lemma evaluate_vertex {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (v : P → V) (p : P) : evaluate v (vertex p) = v p := by
  simp [evaluate,vertex]

lemma coordinate_level (P : PartOrd.{u}) [Fintype P] (n : ℕ)
    (x : PolyPoint (level P n)) :
    (fun p => (levelHomeomorph P n x).weights p) = evaluate (levelVertices P coordinateVertex n) x := by
  rw [← evaluate_coordinates, evaluate_levelHomeomorph]

lemma coordinate_level_vertex (P : PartOrd.{u}) [Fintype P] (n : ℕ) (p : level P n) :
    (fun q => (levelHomeomorph P n (vertex p)).weights q) = levelVertices P coordinateVertex n p := by
  rw [coordinate_level, evaluate_vertex]

theorem exists_star_labels (P : PartOrd.{u}) [Fintype P]
    {Q : Type v} [PartialOrder Q] (f : C(PolyPoint P, PolyPoint Q)) :
    ∃ n : ℕ, ∃ labels : level P n → Q,
      ∀ x : PolyPoint (level P n), ∀ p ∈ x.weights.support,
        labels p ∈ (f (levelHomeomorph P n x)).weights.support := by
  let : MetricSpace (PolyPoint P) :=
    embedding_weights.comapMetricSpace (fun x : PolyPoint P => (fun p => x.weights p))
  let U (q : Q) : Set (PolyPoint P) := {x | 0 < (f x).weights q}
  have hU (q : Q) : IsOpen (U q) := isOpen_lt continuous_const
    ((continuous_weights q).comp f.continuous)
  have hcover : (Set.univ : Set (PolyPoint P)) ⊆ ⋃ q, U q := by
    intro x hx
    obtain ⟨q,hq⟩ := (supportIndex (f x)).nonempty
    refine Set.mem_iUnion.mpr ⟨q,?_⟩
    exact lt_of_le_of_ne ((f x).nonneg q) (Ne.symm (Finsupp.mem_support_iff.mp hq))
  obtain ⟨δ,hδ,hLeb⟩ := lebesgue_number_lemma_of_metric isCompact_univ hU hcover
  have hdim : ChainBound P (Fintype.card P + 1) := by
    intro s
    exact (Finset.card_le_univ s.finset).trans (Nat.le_succ _)
  obtain ⟨n,e,he0,heδ,he⟩ := exists_small_mesh P coordinateVertex 2 (by norm_num)
    bound_coordinates (Nat.succ_pos _) hdim hδ
  have hv (p : level P n) : ∃ q, Metric.ball (levelHomeomorph P n (vertex p)) δ ⊆ U q :=
    hLeb _ (Set.mem_univ _)
  choose labels hlabels using hv
  refine ⟨n,labels,fun x p hp => ?_⟩
  have hball : levelHomeomorph P n x ∈ Metric.ball (levelHomeomorph P n (vertex p)) δ := by
    change dist (fun q => (levelHomeomorph P n x).weights q)
      (fun q => (levelHomeomorph P n (vertex p)).weights q) < δ
    rw [dist_eq_norm, coordinate_level, coordinate_level_vertex]
    exact (norm_evaluate_sub_le _ x _ e (fun q hq => he q p (x.chain.total hq hp))).trans_lt heδ
  exact Finsupp.mem_support_iff.mpr (ne_of_gt (hlabels p hball))

lemma labels_preserve_chains (P : PartOrd.{u}) {Q : Type v} [PartialOrder Q]
    (f : PolyPoint P → PolyPoint Q) (n : ℕ) (labels : level P n → Q)
    (hlabels : ∀ x : PolyPoint (level P n), ∀ p ∈ x.weights.support,
      labels p ∈ (f (levelHomeomorph P n x)).weights.support) : PreservesChains labels := by
  classical
  intro s q hq r hr hqr
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨p',hp',rfl⟩ := Finset.mem_image.mp hr
  apply (f (levelHomeomorph P n (barycenter s))).chain.total
  · exact hlabels _ p (by simpa only [barycenter_support] using hp)
  · exact hlabels _ p' (by simpa only [barycenter_support] using hp')

theorem exists_oriented_approximation (P : PartOrd.{u}) [Fintype P]
    {Q : Type v} [PartialOrder Q] (f : C(PolyPoint P, PolyPoint Q)) :
    ∃ n : ℕ, ∃ a : level P n →o Q,
      ∀ x : PolyPoint (level P n),
        (PolyPoint.map a (preservesChains_monotone a) x).weights.support ⊆
          (f (levelHomeomorph P n x)).weights.support := by
  obtain ⟨n,labels,hlabels⟩ := exists_star_labels P f
  let ha := labels_preserve_chains P f n labels hlabels
  refine ⟨n+1, orientedMap labels ha, fun x q hq => ?_⟩
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp (oriented_support labels ha x hq)
  exact hlabels (subdivide x) p hp

theorem relative_approximation (P : PartOrd.{u}) [Fintype P]
    {Q : Type v} [PartialOrder Q] (f : C(PolyPoint P, PolyPoint Q)) :
    ∃ n : ℕ, ∃ a : level P n →o Q,
      ∃ H : (affineMap a).Homotopy (f.comp ⟨levelHomeomorph P n, (levelHomeomorph P n).continuous⟩),
        (∀ x, (affineMap a x).weights.support ⊆ (f (levelHomeomorph P n x)).weights.support) ∧
        (∀ x q, f (levelHomeomorph P n x) = vertex q →
          ∀ t : unitInterval, H (t,x) = vertex q) := by
  obtain ⟨n,a,ha⟩ := exists_oriented_approximation P f
  let g := f.comp ⟨levelHomeomorph P n, (levelHomeomorph P n).continuous⟩
  have hc (x : PolyPoint (level P n)) :
      IsChain (· ≤ ·) (((affineMap a x).weights.support ∪ (g x).weights.support : Finset Q) : Set Q) := by
    change IsChain (· ≤ ·) (((PolyPoint.map a (preservesChains_monotone a) x).weights.support ∪
      (f (levelHomeomorph P n x)).weights.support : Finset Q) : Set Q)
    rw [Finset.union_eq_right.mpr (ha x)]
    exact (g x).chain
  let H := carrierHomotopy (affineMap a) g hc
  refine ⟨n,a,H,ha,fun x q hx t => ?_⟩
  have he : affineMap a x = vertex q := eq_vertex_of_support_subset _ q (by
    have hh := ha x
    rw [hx, vertex_support] at hh
    exact hh)
  exact (carrierHomotopy_fixed (affineMap a) g hc x (he.trans hx.symm) t).trans he
end Approximation
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open PartialOrder

namespace Thomason.GeometricRecognition
namespace Contiguity
open PolyPoint Mesh Approximation
variable {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]

attribute [local instance] OAI.Thomason.GeometricRecognition.Contiguity.instDecidableEq_solutions
lemma last_support (P : PartOrd.{u}) (n : ℕ) (x : PolyPoint (level P n))
    (p : level P n) (hp : p ∈ x.weights.support) :
    last P n p ∈ (levelHomeomorph P n x).weights.support := by
  induction n with
  | zero => exact hp
  | succ n ih =>
    apply ih (subdivide x) (greatest p)
    change greatest p ∈ (barycentricLinear x.weights).support
    rw [barycentricLinear_support_eq x.weights x.nonneg]
    exact Finset.mem_biUnion.mpr ⟨p,hp,greatest_mem p⟩

end Contiguity
end Thomason.GeometricRecognition

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_RelativeContiguity
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.boxBoundaryInclusion_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative Contiguity. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial PartialOrder

namespace Thomason.GeometricRecognition
open LastVertexProof KanLocal Subdivision Mesh Contiguity PolyPoint

lemma chainLast_local (P : PartOrd.{u}) :
    Local (nerveMap (chainLast (X := P)).toFunctor) := by
  have he : (sdNerveIso (E := P)).hom ≫ nerveMap (chainLast (X := P)).toFunctor =
      lastVertex.app (nerve P) := lastVertex_nerve
  exact local_of_precomp _ _ (local_iso _) (he.symm ▸ lastVertex_local _)

lemma last_local (P : PartOrd.{u}) (n : ℕ) : Local (nerveMap (last P n).toFunctor) := by
  induction n with
  | zero =>
      change Local (nerveMap (OrderHom.id : P →o P).toFunctor)
      rw [nerveOrderMap_id]
      exact local_iso _
  | succ n ih =>
      have he : last P (n+1) = (last P n).comp (chainLast (X := level P n)) := by
        ext s
        apply le_antisymm
        · apply (last P n).monotone
          exact (chain_has_greatest s).choose_spec.2 _ (greatest_mem s)
        · apply (last P n).monotone
          exact le_greatest s _ (chainGreatest_mem s)
      rw [he,nerveOrderMap_comp]
      exact local_comp (chainLast_local _) ih

end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open PartialOrder

namespace Thomason.GeometricRecognition.PolyPoint
variable {P : Type u} [PartialOrder P]

lemma exists_of_support (B : Set P) (x : PolyPoint P) :
    (∃ y : PolyPoint B, map (inclusion B) (preservesChains_monotone (inclusion B)) y = x) ↔
      ∀ p ∈ x.weights.support, p ∈ B := by
  constructor
  · rintro ⟨y,rfl⟩
    exact map_subtype_support B y
  · intro hx
    exact ⟨restrict B x hx,map_subtype_restrict B x hx⟩
end Thomason.GeometricRecognition.PolyPoint

end

noncomputable section
universe u v w z
open CategoryTheory PartialOrder

namespace Thomason.GeometricRecognition
open PolyPoint Mesh Contiguity Subdivision

lemma greatest_map {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) (s : NonemptyFiniteChains P) : greatest (s.map f) = f (greatest s) := by
  apply le_antisymm
  · obtain ⟨p,hp,he⟩ := (NonemptyFiniteChains.mem_map_iff s f _).mp (greatest_mem (s.map f))
    rw [← he]
    exact f.monotone (le_greatest s p hp)
  · exact le_greatest (s.map f) _
      ((NonemptyFiniteChains.mem_map_iff s f _).mpr ⟨greatest s,greatest_mem s,rfl⟩)

def levelMap {P Q : PartOrd.{u}} (f : P →o Q) :
    (n : ℕ) → level P n →o level Q n
  | 0 => f
  | n+1 => NonemptyFiniteChains.orderHomMap (levelMap f n)

lemma levelMap_injective {P Q : PartOrd.{u}} (f : P →o Q) (hf : Function.Injective f)
    (n : ℕ) : Function.Injective (levelMap f n) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact chains_map_injective (levelMap f n) ih

lemma last_natural {P Q : PartOrd.{u}} (f : P →o Q) (n : ℕ) :
    (last Q n).comp (levelMap f n) = f.comp (last P n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext s
    change last Q n (greatest (s.map (levelMap f n))) = f (last P n (greatest s))
    rw [greatest_map]
    exact DFunLike.congr_fun ih (greatest s)

lemma map_barycenter {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) (hf : Function.Injective f) (s : NonemptyFiniteChains P) :
    map f (preservesChains_monotone f) (barycenter s) = barycenter (s.map f) := by
  classical
  apply PolyPoint.ext
  simp only [PolyPoint.map,barycenter,NonemptyFiniteChains.map,Finsupp.mapDomain_finsetSum,
    Finsupp.mapDomain_single,Finset.card_image_of_injective _ hf]
  rw [Finset.sum_image]
  exact fun a _ b _ hab => hf hab

lemma barycentricLinear_natural {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) (hf : Function.Injective f) (w : NonemptyFiniteChains P →₀ ℝ) :
    barycentricLinear (w.mapDomain (NonemptyFiniteChains.orderHomMap f)) =
      (barycentricLinear w).mapDomain f := by
  classical
  induction w using Finsupp.induction with
  | zero => simp
  | @single_add a r w har hr ih =>
    rw [Finsupp.mapDomain_add,map_add,ih,map_add,Finsupp.mapDomain_add]
    congr 1
    rw [Finsupp.mapDomain_single]
    simp only [barycentricLinear,Finsupp.linearCombination_single,Finsupp.mapDomain_smul]
    exact congrArg (fun z : Q →₀ ℝ => r • z) (congrArg PolyPoint.weights (map_barycenter f hf a)).symm

lemma subdivide_natural {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) (hf : Function.Injective f) (x : PolyPoint (NonemptyFiniteChains P)) :
    subdivide (map (NonemptyFiniteChains.orderHomMap f)
      (preservesChains_monotone (NonemptyFiniteChains.orderHomMap f)) x) =
      map f (preservesChains_monotone f) (subdivide x) :=
  PolyPoint.ext (barycentricLinear_natural f hf x.weights)

lemma levelHomeomorph_natural {P Q : PartOrd.{u}} (f : P →o Q)
    (hf : Function.Injective f) (n : ℕ) (x : PolyPoint (level P n)) :
    levelHomeomorph Q n (map (levelMap f n) (preservesChains_monotone (levelMap f n)) x) =
      map f (preservesChains_monotone f) (levelHomeomorph P n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change levelHomeomorph Q n (subdivide (map (NonemptyFiniteChains.orderHomMap (levelMap f n))
      (preservesChains_monotone _) x)) = _
    rw [subdivide_natural (levelMap f n) (levelMap_injective f hf n)]
    exact ih (subdivide x)
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open PartialOrder
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open PolyPoint Mesh Contiguity Approximation

lemma last_affine_support (P : PartOrd.{u}) (n : ℕ) (x : PolyPoint (level P n)) :
    (affineMap (last P n) x).weights.support ⊆ (levelHomeomorph P n x).weights.support := by
  classical
  intro p hp
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp (map_support (last P n) (preservesChains_monotone (last P n)) x hp)
  exact last_support P n x q hq

def lastBarycentricHomotopy (P : PartOrd.{u}) [Finite P] (n : ℕ) :
    (affineMap (last P n)).Homotopy
      ⟨levelHomeomorph P n,(levelHomeomorph P n).continuous⟩ := by
  classical
  letI : Fintype P := Fintype.ofFinite P
  exact carrierHomotopy _ _ (fun x => (levelHomeomorph P n x).chain.mono (by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact last_affine_support P n x hp
    · exact hp))

lemma lastBarycentricHomotopy_support (P : PartOrd.{u}) [Finite P] (n : ℕ)
    (t : unitInterval) (x : PolyPoint (level P n)) :
    (lastBarycentricHomotopy P n (t,x)).weights.support ⊆
      (levelHomeomorph P n x).weights.support := by
  classical
  intro p hp
  change p ∈ ((1 - t.val) • (affineMap (last P n) x).weights +
    t.val • (levelHomeomorph P n x).weights).support at hp
  rcases Finset.mem_union.mp (Finsupp.support_add hp) with hp | hp
  · exact last_affine_support P n x (Finsupp.support_smul hp)
  · exact Finsupp.support_smul hp

lemma lastBarycentricHomotopy_pair (P : PartOrd.{u}) [Finite P] (B : Set P) (n : ℕ)
    (t : unitInterval) (x : PolyPoint (level (PartOrd.of B) n)) :
    ∃ y : PolyPoint B, map (inclusion B) (preservesChains_monotone (inclusion B)) y =
      lastBarycentricHomotopy P n (t,
        map (levelMap (P := PartOrd.of B) (Q := P) (inclusion B) n)
          (preservesChains_monotone _) x) := by
  apply (exists_of_support B _).mpr
  intro p hp
  have hx := lastBarycentricHomotopy_support P n t _ hp
  rw [levelHomeomorph_natural _ Subtype.val_injective] at hx
  exact map_subtype_support B _ p hx
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory MonoidalClosed

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal KanPath Subdivision

lemma kan_square_relative_surjective {A₁ A₀ B₁ B₀ D : SSet.{u}}
    [SSet.KanComplex A₁] [SSet.KanComplex A₀] [SSet.KanComplex B₁] [SSet.KanComplex B₀]
    {f₁ : A₁ ⟶ B₁} {f₀ : A₀ ⟶ B₀} (a : A₁ ⟶ A₀) (b : B₁ ⟶ B₀)
    (w : a ≫ f₀ = f₁ ≫ b) (ha : simplicialFibrations a) (hb : simplicialFibrations b)
    (hf₁ : IsHomotopyEquivalence f₁) (hf₀ : IsHomotopyEquivalence f₀)
    (x₀ : D ⟶ A₀) (z : D ⟶ B₁) (hz : x₀ ≫ f₀ = z ≫ b) :
    ∃ x : D ⟶ A₁, ∃ H : SSet.Homotopy (x ≫ f₁) z,
      x ≫ a = x₀ ∧ H.h ≫ b = fst D Δ[1] ≫ x₀ ≫ f₀ := by
  let y : D ⟶ Matching f₀ b := pullback.lift (x₀ ≫ left f₀) z (by simpa using hz)
  let : HasLiftingProperty (initial.to D) (relative a b w) :=
    relative_rlp a b w ha hb hf₁ hf₀ _ (by infer_instance)
  let sq : CommSq (initial.to (MappingPath f₁)) (initial.to D) (relative a b w) y :=
    ⟨by simp⟩
  let l : D ⟶ MappingPath f₁ := sq.lift
  have hl : l ≫ map a b w = x₀ ≫ left f₀ := by
    have hh := congrArg (fun t => t ≫ pullback.fst (right f₀) b) sq.fac_right
    simp only [relative,y,Category.assoc,pullback.lift_fst] at hh
    exact hh
  have hr : l ≫ right f₁ = z := by
    have hh := congrArg (fun t => t ≫ pullback.snd (right f₀) b) sq.fac_right
    simp only [relative,y,Category.assoc,pullback.lift_snd] at hh
    exact hh
  let x : D ⟶ A₁ := l ≫ pullback.fst f₁ (eval₀ B₁)
  let t : D ⟶ Paths B₁ := l ≫ pullback.snd f₁ (eval₀ B₁)
  have ht₀ : t ≫ eval₀ B₁ = x ≫ f₁ := by
    dsimp only [t,x]
    simp only [Category.assoc,← pullback.condition]
  have ht₁ : t ≫ eval₁ B₁ = z := hr
  refine ⟨x,CoherentGluing.toHomotopy (uncurryR t)
    ((comp_eval₀ t).symm.trans ht₀) ((comp_eval₁ t).symm.trans ht₁), ?_, ?_⟩
  · have hh := congrArg (fun q => q ≫ pullback.fst f₀ (eval₀ B₀)) hl
    simpa only [Category.assoc,map_fst,left,pullback.lift_fst,Category.comp_id,x] using hh
  · change uncurryR t ≫ b = _
    rw [← uncurryR_post]
    have ht : t ≫ (ihom Δ[1]).map b = x₀ ≫ f₀ ≫ const B₀ := by
      have hh := congrArg (fun q => q ≫ pullback.snd f₀ (eval₀ B₀)) hl
      simpa only [Category.assoc,map_snd,left,pullback.lift_snd,t] using hh
    rw [ht]
    simp only [uncurryR_pre,const,uncurryR_curryR,whiskerRight_fst_assoc,
      whiskerRight_fst]

end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory MonoidalClosed

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal KanPath Subdivision Contiguity

lemma pair_local_surjective {A B A' B' D K : SSet.{u}} [SSet.KanComplex K]
    (i : B ⟶ A) [Mono i] (j : B' ⟶ A') [Mono j]
    (f : A' ⟶ A) (g : B' ⟶ B) (w : j ≫ f = g ≫ i)
    (hf : Local f) (hg : Local g) (c : B ⊗ D ⟶ K) (a : A' ⊗ D ⟶ K)
    (ha : j ▷ D ≫ a = g ▷ D ≫ c) :
    ∃ b : A ⊗ D ⟶ K, ∃ H : SSet.Homotopy (f ▷ D ≫ b) a,
      i ▷ D ≫ b = c ∧ j ▷ D ▷ Δ[1] ≫ H.h = fst (B' ⊗ D) Δ[1] ≫ g ▷ D ≫ c := by
  have hs : (pre i).app K ≫ (pre g).app K = (pre f).app K ≫ (pre j).app K := by
    rw [← NatTrans.comp_app,← pre_map,← NatTrans.comp_app,← pre_map,w]
  have hc : curry c ≫ (pre g).app K = curry a ≫ (pre j).app K := by
    apply uncurry_injective
    simpa only [uncurry_pre_app,uncurry_curry] using ha.symm
  obtain ⟨x,H,hx,hH⟩ := kan_square_relative_surjective ((pre i).app K) ((pre j).app K)
    hs (pre_fibration i K) (pre_fibration j K) (hf K inferInstance) (hg K inferInstance)
    (curry c) (curry a) hc
  have hx' : i ▷ D ≫ uncurry x = c := by
    have hh := congrArg (fun z : D ⟶ (ihom B).obj K => uncurry z) hx
    simpa only [uncurry_pre_app,uncurry_curry] using hh
  have ht := uncurry_homotopy_restriction j H (curry c ≫ (pre g).app K) hH
  have hmap : uncurry (curry c ≫ (pre g).app K) = g ▷ D ≫ c := by
    rw [uncurry_pre_app,uncurry_curry]
  rw [hmap] at ht
  let G : SSet.Homotopy (f ▷ D ≫ uncurry x) a := CoherentGluing.toHomotopy
    (uncurryHomotopy H).h
    (by simpa only [uncurry_pre_app,uncurry_curry] using (uncurryHomotopy H).h₀)
    (by simpa only [uncurry_pre_app,uncurry_curry] using (uncurryHomotopy H).h₁)
  exact ⟨uncurry x,G,hx',ht⟩

end Thomason.GeometricRecognition

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_RelativeRepresentation
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.boxBoundaryInclusion_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative Representation. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory MonoidalClosed

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal KanPath Subdivision Contiguity

lemma pair_local_surjective_plain {A B A' B' K : SSet.{u}} [SSet.KanComplex K]
    (i : B ⟶ A) [Mono i] (j : B' ⟶ A') [Mono j]
    (f : A' ⟶ A) (g : B' ⟶ B) (w : j ≫ f = g ≫ i)
    (hf : Local f) (hg : Local g) (c : B ⟶ K) (a : A' ⟶ K)
    (ha : j ≫ a = g ≫ c) :
    ∃ b : A ⟶ K, ∃ H : SSet.Homotopy (f ≫ b) a,
      i ≫ b = c ∧ (j ▷ Δ[1]) ≫ H.h = fst B' Δ[1] ≫ g ≫ c := by
  obtain ⟨b,H,hb,hH⟩ := pair_local_surjective i j f g w hf hg ((ρ_ B).hom ≫ c)
    ((ρ_ A').hom ≫ a) (by rw [rightUnitor_naturality_assoc,ha,rightUnitor_naturality_assoc])
  let b' : A ⟶ K := (ρ_ A).inv ≫ b
  let H' : SSet.Homotopy (f ≫ b') a := CoherentGluing.toHomotopy
    ((ρ_ A').inv ▷ Δ[1] ≫ H.h)
    (by simpa only [homotopy_pre,CoherentGluing.toHomotopy,b',Category.assoc,rightUnitor_inv_naturality_assoc] using
      (homotopy_pre (ρ_ A').inv H).h₀)
    (by simpa only [homotopy_pre,CoherentGluing.toHomotopy,b',Category.assoc,Iso.inv_hom_id_assoc] using
      (homotopy_pre (ρ_ A').inv H).h₁)
  refine ⟨b',H',?_,?_⟩
  · dsimp only [b']
    rw [rightUnitor_inv_naturality_assoc,hb,Iso.inv_hom_id_assoc]
  · change j ▷ Δ[1] ≫ (ρ_ A').inv ▷ Δ[1] ≫ H.h = _
    rw [← comp_whiskerRight_assoc,rightUnitor_inv_naturality,
      comp_whiskerRight_assoc,hH,whiskerRight_fst_assoc]
    simp only [rightUnitor_naturality_assoc,Iso.inv_hom_id_assoc]

lemma pair_local_injective_plain {A B A' B' K : SSet.{u}} [SSet.KanComplex K]
    (i : B ⟶ A) [Mono i] (j : B' ⟶ A') [Mono j]
    (f : A' ⟶ A) (g : B' ⟶ B) (w : j ≫ f = g ≫ i)
    (hf : Local f) (hg : Local g) (c : B ⟶ K) (a b : A ⟶ K)
    (ha : i ≫ a = c) (hb : i ≫ b = c)
    (H : SSet.Homotopy (f ≫ a) (f ≫ b))
    (hH : j ▷ Δ[1] ≫ H.h = fst B' Δ[1] ≫ g ≫ c) :
    ∃ G : SSet.Homotopy a b, i ▷ Δ[1] ≫ G.h = fst B Δ[1] ≫ c := by
  let H' : SSet.Homotopy (f ▷ (𝟙_ SSet) ≫ (ρ_ A).hom ≫ a)
      (f ▷ (𝟙_ SSet) ≫ (ρ_ A).hom ≫ b) := CoherentGluing.toHomotopy
    ((ρ_ A').hom ▷ Δ[1] ≫ H.h)
    (by simpa only [homotopy_pre,CoherentGluing.toHomotopy,rightUnitor_naturality_assoc,Category.assoc] using
      (homotopy_pre (ρ_ A').hom H).h₀)
    (by simpa only [homotopy_pre,CoherentGluing.toHomotopy,rightUnitor_naturality_assoc,Category.assoc] using
      (homotopy_pre (ρ_ A').hom H).h₁)
  obtain ⟨G,hG⟩ := pair_local_injective i j f g w hf hg ((ρ_ B).hom ≫ c)
    ((ρ_ A).hom ≫ a) ((ρ_ A).hom ≫ b)
    (by rw [rightUnitor_naturality_assoc,ha])
    (by rw [rightUnitor_naturality_assoc,hb]) H' (by
      change j ▷ (𝟙_ SSet) ▷ Δ[1] ≫ (ρ_ A').hom ▷ Δ[1] ≫ H.h = _
      rw [← comp_whiskerRight_assoc,rightUnitor_naturality,
        comp_whiskerRight_assoc,hH,whiskerRight_fst_assoc]
      simp only [rightUnitor_naturality_assoc])
  let G' : SSet.Homotopy a b := CoherentGluing.toHomotopy
    ((ρ_ A).inv ▷ Δ[1] ≫ G.h)
    (by simpa only [homotopy_pre,CoherentGluing.toHomotopy,Category.assoc,Iso.inv_hom_id_assoc] using (homotopy_pre (ρ_ A).inv G).h₀)
    (by simpa only [homotopy_pre,CoherentGluing.toHomotopy,Category.assoc,Iso.inv_hom_id_assoc] using (homotopy_pre (ρ_ A).inv G).h₁)
  refine ⟨G',?_⟩
  change i ▷ Δ[1] ≫ (ρ_ A).inv ▷ Δ[1] ≫ G.h = _
  rw [← comp_whiskerRight_assoc,rightUnitor_inv_naturality,
    comp_whiskerRight_assoc,hG,whiskerRight_fst_assoc]
  simp only [Iso.inv_hom_id_assoc]
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory PartialOrder Simplicial MonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open PolyPoint Mesh Approximation Contiguity LastVertexProof KanLocal

lemma vertex_injective {Q : Type u} [PartialOrder Q] :
    Function.Injective (@vertex Q _) := by
  classical
  intro a b h
  have hh := congrArg (fun x : PolyPoint Q => x.weights.support) h
  simpa only [vertex_support,Finset.singleton_inj] using hh

lemma pair_geometric_approximation (P : PartOrd.{u}) [Finite P] (B : Set P)
    {Q : Type u} [PartialOrder Q] (q : Q) (f : C(PolyPoint P,PolyPoint Q))
    (hf : ∀ x : PolyPoint B,
      f (map (inclusion B) (preservesChains_monotone (inclusion B)) x) = vertex q) :
    ∃ n : ℕ, ∃ a : level P n →o Q,
      ∃ H : (affineMap a).Homotopy
        (f.comp ⟨levelHomeomorph P n,(levelHomeomorph P n).continuous⟩),
        (a.comp (levelMap (P := PartOrd.of B) (Q := P) (inclusion B) n) =
          OrderHom.const _ q) ∧
        ∀ t x, H (t,map (levelMap (P := PartOrd.of B) (Q := P) (inclusion B) n)
          (preservesChains_monotone _) x) = vertex q := by
  let : Fintype P := Fintype.ofFinite P
  obtain ⟨n,a,H,hc,hfixed⟩ := relative_approximation P f
  have hh (x : PolyPoint (level (PartOrd.of B) n)) (t : unitInterval) :
      H (t,map (levelMap (P := PartOrd.of B) (Q := P) (inclusion B) n)
        (preservesChains_monotone _) x) = vertex q := by
    apply hfixed
    rw [levelHomeomorph_natural _ Subtype.val_injective]
    exact hf _
  refine ⟨n,a,H,?_,fun t x => hh x t⟩
  ext x
  apply vertex_injective
  change vertex (a ((levelMap (P := PartOrd.of B) (Q := P) (inclusion B) n) x)) = vertex q
  have h := (H.apply_zero _).symm.trans (hh (vertex x) 0)
  simpa only [affineMap,ContinuousMap.coe_mk,map_vertex] using h

lemma descend_pair_approximation (P : PartOrd.{u}) (B : Set P) (n : ℕ)
    (K : SSet.{u}) [SSet.KanComplex K] (c : nerve B ⟶ K)
    (a : nerve (level P n) ⟶ K)
    (ha : nerveMap (levelMap (P := PartOrd.of B) (Q := P) (inclusion B) n).toFunctor ≫ a =
      nerveMap (last (PartOrd.of B) n).toFunctor ≫ c) :
    ∃ b : nerve P ⟶ K, ∃ H : SSet.Homotopy (nerveMap (last P n).toFunctor ≫ b) a,
      nerveMap (inclusion B).toFunctor ≫ b = c ∧
      (nerveMap (levelMap (P := PartOrd.of B) (Q := P) (inclusion B) n).toFunctor ▷ Δ[1]) ≫ H.h =
        CategoryTheory.CartesianMonoidalCategory.fst _ Δ[1] ≫
          nerveMap (last (PartOrd.of B) n).toFunctor ≫ c := by
  let := nerveOrderMap_mono (inclusion B) Subtype.val_injective
  let := nerveOrderMap_mono (levelMap (P := PartOrd.of B) (Q := P) (inclusion B) n)
    (levelMap_injective _ Subtype.val_injective n)
  apply pair_local_surjective_plain _ _ _ _ _ (last_local P n) (last_local (PartOrd.of B) n) c a ha
  rw [← nerveOrderMap_comp,← nerveOrderMap_comp,last_natural]
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh

lemma constantOrder_comp {P Q R : Type u} [PartialOrder P] [PartialOrder Q]
    [PartialOrder R] (f : P →o Q) (r : R) :
    (constantOrder Q r).comp f = constantOrder P r := rfl

lemma nerve_constant_pre {P Q R : Type u} [PartialOrder P] [PartialOrder Q]
    [PartialOrder R] (f : P →o Q) (r : R) :
    nerveMap f.toFunctor ≫ nerveMap (constantOrder Q r).toFunctor =
      nerveMap (constantOrder P r).toFunctor := by
  rw [← nerveOrderMap_comp,constantOrder_comp]

attribute [instance] PairRefinement.finiteR PairRefinement.finiteS

end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh

@[reassoc]
lemma nerve_constant_pre' {P Q R : Type u} [PartialOrder P] [PartialOrder Q]
    [PartialOrder R] (f : P →o Q) (r : R) :
    nerveMap f.toFunctor ≫ nerveMap (constantOrder Q r).toFunctor =
      nerveMap (constantOrder P r).toFunctor := nerve_constant_pre f r

end Thomason.GeometricRecognition

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_CubicalGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cubical Geometry. -/

noncomputable section
universe u v w z
open CategoryTheory Nerve Simplicial

namespace Thomason.GeometricRecognition
open PolyPoint
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

lemma map_eval {ι : Type*} [Fintype ι] [LinearOrder ι]
    (f : P →o Q) (a : ι →o P) (x : Convexity.StdSimplex ℝ ι) :
    PolyPoint.map f (preservesChains_monotone f) (eval a x) = eval (f.comp a) x := by
  apply PolyPoint.ext
  simp only [PolyPoint.map, PolyPoint.eval, evalWeights, Finsupp.mapDomain_finsetSum,
    Finsupp.mapDomain_single, OrderHom.comp_coe, Function.comp_apply]

lemma nerveMap_realizeSimplex {n : ℕ} (f : P →o Q) (a : Fin (n+1) →o P)
    (x : Convexity.StdSimplex ℝ (Fin (n+1))) :
    SSet.toTop.map (nerveMap f.monotone.functor) (realizeSimplex a x) =
      realizeSimplex (f.comp a) x := by
  have he : (SSet.yonedaEquiv (X := nerve P)).symm a.monotone.functor ≫
      nerveMap f.monotone.functor =
      (SSet.yonedaEquiv (X := nerve Q)).symm (f.comp a).monotone.functor := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp]
    rfl
  simp only [realizeSimplex]
  rw [← TopCat.comp_app, ← Functor.map_comp, he]

lemma nerveRealizationHomeomorph_natural (f : P →o Q) (z : |nerve P|) :
    nerveRealizationHomeomorph (SSet.toTop.map (nerveMap f.monotone.functor) z) =
      PolyPoint.map f (preservesChains_monotone f) (nerveRealizationHomeomorph z) := by
  obtain ⟨x,rfl⟩ := (nerveRealizationHomeomorph (P := P)).symm.surjective z
  change realizationToPoly Q (SSet.toTop.map (nerveMap f.monotone.functor)
      (polyToRealization x)) = PolyPoint.map f (preservesChains_monotone f)
        (realizationToPoly P (polyToRealization x))
  rw [realizationToPoly_polyToRealization]
  let s := supportIndex x
  let y : Face s.carrier := ⟨x,Finset.Subset.refl _⟩
  have hx : eval s.vertices (s.coordinates y) = x := s.eval_coordinates y
  rw [← hx, polyToRealization_eval, nerveMap_realizeSimplex,
    realizationToPoly_realizeSimplex, map_eval]
end Thomason.GeometricRecognition

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_CubicalRecognition
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.boxBoundaryInclusion_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cubical Recognition. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

lemma polyToRealization_natural {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (i : P →o Q) (x : PolyPoint P) :
    SSet.toTop.map (nerveMap i.toFunctor) (polyToRealization x) =
      polyToRealization (map i (preservesChains_monotone i) x) := by
  apply (nerveRealizationHomeomorph (P := Q)).injective
  rw [nerveRealizationHomeomorph_natural]
  change map i _ (realizationToPoly P (polyToRealization x)) =
    realizationToPoly Q (polyToRealization (map i _ x))
  rw [realizationToPoly_polyToRealization,realizationToPoly_polyToRealization]

def polyRealize {P : Type u} [PartialOrder P] {K : SSet.{u}} (a : nerve P ⟶ K) :
    C(PolyPoint P,SSet.toTop.obj K) := (realizeMap a).comp polyToRealizationHom.hom

lemma polyRealize_pre {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (i : P →o Q) {K : SSet.{u}} (a : nerve Q ⟶ K) :
    polyRealize (nerveMap i.toFunctor ≫ a) = (polyRealize a).comp (affineMap i) := by
  ext x
  change (SSet.toTop.map (nerveMap i.toFunctor ≫ a)) (polyToRealization x) = _
  rw [Functor.map_comp]
  change SSet.toTop.map a (SSet.toTop.map (nerveMap i.toFunctor) (polyToRealization x)) = _
  rw [polyToRealization_natural]
  rfl

end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

lemma polyRealize_const {P : Type u} [PartialOrder P] {K : SSet.{u}}
    (x : K _⦋0⦌) (a : PolyPoint P) :
    polyRealize (SSet.const x) a = KanQuillen.realVertex x := realize_const_apply x _

end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

lemma cubical_relative_surject {A : Type u} {X : Type v} {Y : Type w}
    [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (e : A ≃ₜ (Fin (n+1) → unitInterval)) (S : Set A)
    (hS : ∀ a, a ∈ S ↔ e a ∈ Cube.boundary (Fin (n+1)))
    (r : C(X,Y)) (hr : WeakHomotopy.Equivalence r) (x : X)
    (f : C(A,Y)) (hf : ∀ a ∈ S, f a = r x) :
    ∃ g : C(A,X), (∀ a ∈ S, g a = x) ∧ Nonempty ((r.comp g).HomotopyRel f S) := by
  let f' : GenLoop (Fin (n+1)) Y (r x) := ⟨f.comp ⟨e.symm,e.symm.continuous⟩,by
    intro a ha
    exact hf _ ((hS _).mpr (by simpa using ha))⟩
  obtain ⟨g,hg⟩ := (hr.2 n x).2 ⟦f'⟧
  obtain ⟨g,rfl⟩ := Quotient.mk_surjective g
  obtain ⟨G⟩ : GenLoop.Homotopic (WeakHomotopy.loopMap (Fin (n+1)) r x g) f' := Quotient.exact hg
  let g' := g.val.comp ⟨e,e.continuous⟩
  refine ⟨g',fun a ha => g.property _ ((hS a).mp ha),?_⟩
  have hh := top_homotopy_rel_pre G ⟨e,e.continuous⟩ S (fun a ha => (hS a).mp ha)
  refine ⟨hh.cast ?_ ?_⟩ <;> ext a <;> simp [g',f',WeakHomotopy.loopMap]

lemma poly_realize_boundary {P B : PartOrd.{u}} (i : B →o P) {K : SSet.{u}}
    (x : K _⦋0⦌) (a : nerve P ⟶ K) (ha : nerveMap i.toFunctor ≫ a = SSet.const x) :
    ∀ y ∈ Set.range (map i (preservesChains_monotone i)), polyRealize a y =
      KanQuillen.realVertex x := by
  rintro y ⟨z,rfl⟩
  have hh := congrArg (fun F : C(PolyPoint B,SSet.toTop.obj K) => F z) (polyRealize_pre i a)
  rw [ha] at hh
  exact hh.symm.trans (polyRealize_const x z)

lemma last_barycentric_realization_rel (P : PartOrd.{u}) [Finite P] (B : Set P)
    (n : ℕ) {K : SSet.{u}} (x : K _⦋0⦌) (a : nerve P ⟶ K)
    (ha : nerveMap (inclusion B).toFunctor ≫ a = SSet.const x) :
    Nonempty ((polyRealize (nerveMap (last P n).toFunctor ≫ a)).HomotopyRel
      ((polyRealize a).comp ⟨levelHomeomorph P n,(levelHomeomorph P n).continuous⟩)
      (Set.range (map (levelMap (P := PartOrd.of B) (Q := P) (inclusion B) n)
        (preservesChains_monotone _)))) := by
  rw [polyRealize_pre]
  refine ⟨{ toHomotopy := (ContinuousMap.Homotopy.refl (polyRealize a)).comp (lastBarycentricHomotopy P n)
            prop' := ?_ }⟩
  rintro t y ⟨z,rfl⟩
  obtain ⟨v,hv⟩ := lastBarycentricHomotopy_pair P B n t z
  have hb := poly_realize_boundary (P := P) (B := PartOrd.of B) (inclusion B) x a ha
  change polyRealize a (lastBarycentricHomotopy P n (t,_)) =
    polyRealize a (map (last P n) (preservesChains_monotone _) _)
  rw [← hv,hb _ ⟨v,rfl⟩]
  symm
  apply hb
  refine ⟨map (last (PartOrd.of B) n) (preservesChains_monotone _) z,?_⟩
  have h₁ : map (inclusion B) (preservesChains_monotone _) (map (last (PartOrd.of B) n) (preservesChains_monotone _) z) =
      map ((inclusion B).comp (last (PartOrd.of B) n)) (preservesChains_monotone _) z :=
    PolyPoint.ext Finsupp.mapDomain_comp.symm
  have h₂ : map (last P n) (preservesChains_monotone _) (map (levelMap (inclusion B) n) (preservesChains_monotone _) z) =
      map ((last P n).comp (levelMap (inclusion B) n)) (preservesChains_monotone _) z :=
    PolyPoint.ext Finsupp.mapDomain_comp.symm
  rw [h₁,h₂,last_natural]
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

lemma full_pair_home_boundary (P : PartOrd.{u}) [Finite P] (B : Set P) (n : ℕ)
    (y : PolyPoint P) (hy : y ∈ Set.range (map (inclusion B) (preservesChains_monotone _))) :
    (levelHomeomorph P n).symm y ∈ Set.range
      (map (levelMap (P := PartOrd.of B) (Q := P) (inclusion B) n) (preservesChains_monotone _)) := by
  obtain ⟨z,rfl⟩ := hy
  refine ⟨(levelHomeomorph (PartOrd.of B) n).symm z,?_⟩
  apply (levelHomeomorph P n).injective
  rw [(levelHomeomorph P n).apply_symm_apply,levelHomeomorph_natural _ Subtype.val_injective,
    (levelHomeomorph (PartOrd.of B) n).apply_symm_apply]

end Thomason.GeometricRecognition

end

end OAI
end


