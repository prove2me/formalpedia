-- Prove2me | Definitions.Def_OAIQ043T003
-- name    : OAIQ043T003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T09:42:34.477019+00:00
-- url     : https://prove2.me/theorems/6798dd03-bf04-4210-95e1-42b8581a61f7
-- title:
--   Definitions bundle OAIQ043T003 of the split of OpenAI, Thomason Model Structures in Every Strict Higher Dimension (result family 317)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Thomason.main` and `OAI.Thomason.nerveDetection_allDimensions`, carved from OpenAI's openai/math development (OpenAI, *Thomason Model Structures in Every Strict Higher Dimension (result family 317)*, OpenAI Math Release, September 25, 2026, result family 317, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 155 declarations of OpenAI's Lean: 40 definitions, 1 inductive type or structure, 20 instances and 94 theorems. The definitions and types are `OAI.Thomason.AbstractTransfer.Boundaries.oldCoprodIso`, `OAI.Thomason.AbstractTransfer.Boundaries.posetCoprodIso`, `OAI.Thomason.BoundaryProperness.sumData`, `OAI.Thomason.FilteredWeak.pathDiagram`, `OAI.Thomason.FilteredWeak.pathLeft`, `OAI.Thomason.FilteredWeak.pathProjection`, `OAI.Thomason.FilteredWeak.pathRight`, `OAI.Thomason.GeometricRecognition.Contiguity.BasedRelated`, `OAI.Thomason.GeometricRecognition.Contiguity.ChainMap`, `OAI.Thomason.GeometricRecognition.Contiguity.Contiguous`, `OAI.Thomason.GeometricRecognition.Contiguity.Fixed`, `OAI.Thomason.GeometricRecognition.Contiguity.FixedContiguous`, `OAI.Thomason.GeometricRecognition.Contiguity.FixedMap`, `OAI.Thomason.GeometricRecognition.Contiguity.RelativeRelated`, `OAI.Thomason.GeometricRecognition.Contiguity.fixedMapSetoid`, `OAI.Thomason.GeometricRecognition.Contiguity.toChainMap`, `OAI.Thomason.GeometricRecognition.Contiguity.unionChain`, `OAI.Thomason.GeometricRecognition.Contiguity.upperMap`, `OAI.Thomason.GeometricRecognition.CubeClasses`, `OAI.Thomason.GeometricRecognition.CubeMap`, `OAI.Thomason.GeometricRecognition.CubicalPair.refine`, `OAI.Thomason.GeometricRecognition.PairRefinement.identity`, `OAI.Thomason.GeometricRecognition.SimplexGeometry.simplexChartHomeomorph`, `OAI.Thomason.GeometricRecognition.SimplexGeometry.simplexCubeHomeomorph`, `OAI.Thomason.GeometricRecognition.actualCubicalPair`, `OAI.Thomason.GeometricRecognition.boundaryFaceOrderIso`, `OAI.Thomason.GeometricRecognition.cubeBoundary`, `OAI.Thomason.GeometricRecognition.cubeBoundaryInclusion`, `OAI.Thomason.GeometricRecognition.cubeMapSetoid`, `OAI.Thomason.GeometricRecognition.orderedBoundary`, `OAI.Thomason.GeometricRecognition.sdBoundaryFacesIso`, `OAI.Thomason.GeometricRecognition.simplexBoundaryProjection`, `OAI.Thomason.GeometricRecognition.simplexPairProjection`, `OAI.Thomason.GeometricRecognition.simplexPolyCoordinates`, `OAI.Thomason.GeometricRecognition.simplexPolyHomeomorph`, `OAI.Thomason.NormalizedChains.PosetTables.upperSegmentLabel`, `OAI.Thomason.NormalizedChains.awHom`, `OAI.Thomason.OneCat.orderMapCylinder`, `OAI.Thomason.OneCat.posetMapCylinder`, `OAI.Thomason.Subdivision.LastVertexStatement` and 1 more.
--
--   **Sources.** They come from these modules of lean/OAI/CategoryTheory/Thomason, in whole or in part: `Thomason_AlexanderWhitney`, `Thomason_CoherentGluing`, `Thomason_Couniversality`, `Thomason_CubicalGeometry`, `Thomason_CubicalRecognition`, `Thomason_DimensionOne`, `Thomason_FiberRecognition`, `Thomason_Globes`, `Thomason_HomotopyExtension`, `Thomason_LabelledFibers`, `Thomason_ModelClasses`, `Thomason_ModelTransfer`, `Thomason_PosetalReduction`, `Thomason_ProperTransfer`, `Thomason_RelativeContiguity`, `Thomason_RelativeRepresentation`, `Thomason_SieveAttachments`, `Thomason_SimplexBoxes`, `Thomason_SimplicialApproximation`, `Thomason_SkeletalCategories`, `Thomason_StrictCategories`, `Thomason_SubdividedUnit`, `Thomason_SubdivisionWeak`.
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
-- module Solutions.OAIQ043_TH.Thomason_StrictCategories
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.KanQuillen.boundary_small _root_.OAI.Thomason.KanQuillen.boundary_smallCardinal _root_.OAI.Thomason.KanQuillen.boundary_smallObject _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict Categories. -/

noncomputable section
universe u v w z


namespace Thomason


attribute [instance] DirectedComplex.group

namespace DirectedComplex


namespace Table

variable {K : DirectedComplex.{u}}


lemma truncate_truncate (i j : ℕ) (e f : Bool) (x : Table K) :
    truncate i e (truncate j f x) =
      if i < j then truncate i e x else truncate j f x := by
  ext p b
  by_cases hij : i < j
  · simp only [hij, ite_eq_left, truncate_row]
    by_cases hpi : p < i
    · have hpj : p < j := lt_trans hpi hij
      simp [hpi, hpj]
    · by_cases hpe : p = i
      · subst p
        simp [hij]
      · simp [hpi, hpe]
  · simp only [hij, ite_false, truncate_row]
    by_cases hpj : p < j
    · have hpi : p < i := by omega
      simp [hpj, hpi]
    · by_cases hpje : p = j
      · subst p
        by_cases hji : j < i
        · simp [hji]
        · have hi : i = j := by omega
          subst i
          simp
      · by_cases hpi : p < i
        · simp [hpi, hpj, hpje]
        · by_cases hpie : p = i
          · subst p
            simp [hij]
          · simp [hpi, hpie, hpj, hpje]

lemma truncate_truncate_same (i j : ℕ) (e : Bool) (x : Table K) :
    truncate i e (truncate j e x) = truncate (min i j) e x := by
  rw [truncate_truncate]
  split_ifs with h
  · rw [min_eq_left (le_of_lt h)]
  · rw [min_eq_right (le_of_not_gt h)]

lemma lower_rows_eq {k : ℕ} {x y : Table K}
    (h : truncate k true x = truncate k false y) {p : ℕ} (hp : p < k) (b : Bool) :
    x.row p b = y.row p b := by
  have hr := congrArg (fun z : Table K => z.row p b) h
  simpa only [truncate_row, hp, ite_eq_left] using hr

lemma target_comp_le (i k : ℕ) (hik : i ≤ k) (x y : Table K)
    (h : truncate k true x = truncate k false y) :
    truncate i true (comp k x y h) = truncate i true y := by
  ext p b
  by_cases hpi : p < i
  · have hpk : p < k := lt_of_lt_of_le hpi hik
    simp only [truncate_row, ite_eq_left hpi, comp_row, ite_eq_left hpk]
    exact lower_rows_eq h hpk b
  · by_cases hpe : p = i
    · subst p
      by_cases hik' : i < k
      · simpa [hik'] using lower_rows_eq h hik' true
      · have he : i = k := by omega
        subst i
        simp
    · simp [hpi, hpe]

end Table
end DirectedComplex
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
-- module Solutions.OAIQ043_TH.Thomason_ModelClasses
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.KanQuillen.boundary_small _root_.OAI.Thomason.KanQuillen.boundary_smallCardinal _root_.OAI.Thomason.KanQuillen.boundary_smallObject _root_.OAI.Thomason.NormalizedChains.finiteWord _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Model Classes. -/

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E] (θ : E →o Fin 2)

lemma awZeroWord_of_all {l : List E} (h : ∀ a ∈ l, θ a = 0) :
    awZeroWord θ l = bracket l := ite_eq_left h

lemma awZeroWord_of_not_all {l : List E} (h : ¬∀ a ∈ l, θ a = 0) :
    awZeroWord θ l = 0 := ite_eq_right h

lemma awZeroWord_append_of_ne (l : List E) {a : E} (ha : θ a ≠ 0) :
    awZeroWord θ (l ++ [a]) = 0 := by
  apply awZeroWord_of_not_all
  intro h
  exact ha (h a (by simp))

lemma awEdgeWord_of_all {l : List E} (h : ∀ a ∈ l, θ a = 0) :
    awEdgeWord θ l = 0 := by
  cases l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a => rw [awEdgeWord_append, ite_eq_left (h a (by simp))]

lemma boundary_awZeroWord {l : List E} {a : E}
    (h : (l ++ [a]).Pairwise (· ≤ ·)) :
    boundary (awZeroWord θ (l ++ [a])) =
      faces (awZeroWord θ) (l ++ [a]) -
        ((-1 : ℤ)^l.length) • awEdgeWord θ (l ++ [a]) := by
  by_cases ha : θ a = 0
  · have hall := all_zero_of_last_zero θ h ha
    rw [awZeroWord_of_all θ hall, awEdgeWord_of_all θ hall, smul_zero, sub_zero,
      boundary_bracket h, ← faces_bracket]
    apply faces_congr
    intro m hm
    exact (awZeroWord_of_all θ (fun b hb => hall b (hm.subset hb))).symm
  · rw [awZeroWord_append_of_ne θ l ha, map_zero, awEdgeWord_append,
      ite_eq_right ha, faces_append_singleton]
    have hz : faces (fun m => awZeroWord θ (m ++ [a])) l = 0 := by
      have he : (fun m : List E => awZeroWord θ (m ++ [a])) = fun _ => 0 := by
        funext m
        exact awZeroWord_append_of_ne θ m ha
      rw [he, faces_zero]
    rw [hz, zero_add, sub_self]

lemma boundary_awEdgeWord {l : List E} (h : l.Pairwise (· ≤ ·)) :
    boundary (awEdgeWord θ l) = faces (awEdgeWord θ) l := by
  cases l using List.reverseRecOn with
  | nil => simp
  | append_singleton l a =>
    by_cases ha : θ a = 0
    · have hall := all_zero_of_last_zero θ h ha
      rw [awEdgeWord_of_all θ hall, map_zero]
      have he : faces (awEdgeWord θ) (l ++ [a]) = faces (fun _ => 0) (l ++ [a]) := by
        apply faces_congr
        intro m hm
        exact awEdgeWord_of_all θ (fun b hb => hall b (hm.subset hb))
      rw [he, faces_zero]
    · rw [awEdgeWord_append, ite_eq_right ha, faces_append_singleton]
      have he : faces (fun m => awEdgeWord θ (m ++ [a])) l =
          faces (awZeroWord θ) l := by
        apply faces_congr
        intro m _
        rw [awEdgeWord_append, ite_eq_right ha]
      rw [he]
      cases l using List.reverseRecOn with
      | nil =>
        rw [awZeroWord_of_all θ (by simp), boundary_bracket (by simp)]
        simp only [wordBoundary_nil, faces_nil, List.length_nil, pow_zero,
          one_smul, awEdgeWord_nil, add_zero]
      | append_singleton k b =>
        rw [boundary_awZeroWord θ (List.pairwise_append.mp h).1,
          List.length_append, List.length_singleton, pow_succ, mul_neg, mul_one,
          neg_smul, sub_eq_add_neg]

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E] (θ : E →o Fin 2)

lemma awEdgeWord_eq_zero_of_not_pairwise {l : List E}
    (h : l.Pairwise (· ≤ ·)) (hn : ¬l.Pairwise (· < ·)) : awEdgeWord θ l = 0 := by
  cases l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a =>
    rw [awEdgeWord_append]
    split
    · rfl
    next ha =>
      by_cases hall : ∀ b ∈ l, θ b = 0
      · rw [awZeroWord_of_all θ hall]
        apply bracket_of_not_pairwise
        intro hl
        apply hn
        apply List.pairwise_append.mpr
        refine ⟨hl, by simp, ?_⟩
        intro b hb c hc
        simp only [List.mem_singleton] at hc
        subst c
        apply lt_of_le_of_ne ((List.pairwise_append.mp h).2.2 b hb a (by simp))
        intro hba
        exact ha (by simpa [hba] using hall b hb)
      · exact awZeroWord_of_not_all θ hall

lemma awEdge_bracket {l : List E} (h : l.Pairwise (· ≤ ·)) :
    awEdge θ (bracket l) = awEdgeWord θ l := by
  classical
  by_cases hs : l.Pairwise (· < ·)
  · rw [bracket_of_pairwise hs]
    change Finsupp.linearCombination ℤ (fun w : Word E => awEdgeWord θ w.val)
      (Finsupp.single ⟨l, hs⟩ 1) = _
    rw [Finsupp.linearCombination_single]
    simp
  · simp [bracket_of_not_pairwise hs, awEdgeWord_eq_zero_of_not_pairwise θ h hs]

lemma awEdge_wordBoundary {l : List E} (h : l.Pairwise (· ≤ ·)) :
    awEdge θ (wordBoundary l) = faces (awEdgeWord θ) l := by
  rw [← faces_bracket]
  change (awEdge θ).toAddMonoidHom (faces bracket l) = _
  rw [faces_hom]
  apply faces_congr
  intro m hm
  exact awEdge_bracket θ (h.sublist hm)

lemma awEdge_boundary (c : Chains E) :
    boundary (awEdge θ c) = awEdge θ (boundary c) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l z c _ _ ih =>
    simp only [map_add, ih]
    congr 1
    have hz : Finsupp.single l z = z • bracket l.val := by
      rw [bracket_of_pairwise l.property]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hz]
    simp only [map_smul]
    congr 1
    have hl := l.property.imp fun h => le_of_lt h
    rw [awEdge_bracket θ hl, boundary_bracket hl, awEdge_wordBoundary θ hl,
      boundary_awEdgeWord θ hl]

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E] (θ : E →o Fin 2)

lemma boundary_awZero (c : Chains E) :
    boundary (awZero θ c) = awZero θ (boundary c) - awEdge θ (degreeSign c) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l z c _ _ ih =>
    simp only [map_add, ih]
    have hz : Finsupp.single l z = z • bracket l.val := by
      rw [bracket_of_pairwise l.property]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hz]
    simp only [map_smul]
    have hw : boundary (awZero θ (bracket l.val)) =
        awZero θ (boundary (bracket l.val)) - awEdge θ (degreeSign (bracket l.val)) := by
      have hl := l.property.imp fun h => le_of_lt h
      rw [awZero_bracket, boundary_bracket hl, awZero_wordBoundary,
        degreeSign_bracket, map_smul, awEdge_bracket θ hl]
      rcases l with ⟨l, hls⟩
      cases l using List.reverseRecOn with
      | nil =>
        rw [awZeroWord_of_all θ (by simp), boundary_bracket (by simp)]
        simp only [wordBoundary_nil, faces_nil, awEdgeWord_nil, smul_zero, sub_zero]
      | append_singleton l a =>
        simpa only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
          using boundary_awZeroWord θ hl
    rw [hw, smul_sub]
    abel

lemma boundary_awZero_of_grade {p : ℕ} {c : Chains E} (hc : c ∈ grade (p+1)) :
    boundary (awZero θ c) = awZero θ (boundary c) - ((-1 : ℤ)^p) • awEdge θ c := by
  rw [boundary_awZero, degreeSign_of_grade hc, map_smul]

def awHom : DirectedComplex.Hom (complex E) (complex E).cylinder where
  map := awMap θ
  map_d p c := by
    symm
    cases p with
    | zero =>
      apply Prod.ext <;> apply Subtype.ext
      · change (boundary (awZero θ c.val) - awEdge θ c.val) = awZero θ (boundary c.val)
        rw [boundary_awZero_of_grade θ c.property]
        norm_num
      · change boundary (c.val - awZero θ c.val) + awEdge θ c.val =
          boundary c.val - awZero θ (boundary c.val)
        rw [map_sub, boundary_awZero_of_grade θ c.property]
        norm_num
        abel
    | succ p =>
      apply Prod.ext
      · apply Subtype.ext
        change boundary (awZero θ c.val) - ((-1 : ℤ)^(p+1)) • awEdge θ c.val =
          awZero θ (boundary c.val)
        rw [boundary_awZero_of_grade θ c.property, pow_succ]
        simp only [mul_neg, mul_one, neg_smul]
        abel
      · apply Prod.ext
        · apply Subtype.ext
          change boundary (c.val - awZero θ c.val) + ((-1 : ℤ)^(p+1)) • awEdge θ c.val =
            boundary c.val - awZero θ (boundary c.val)
          rw [map_sub, boundary_awZero_of_grade θ c.property, pow_succ]
          simp only [mul_neg, mul_one, neg_smul]
          abel
        · exact Subtype.ext (awEdge_boundary θ c.val)
  map_augmentation c := by
    change emptyCoefficient (boundary (awZero θ c.val)) +
      emptyCoefficient (boundary (c.val - awZero θ c.val)) =
      emptyCoefficient (boundary c.val)
    simp only [map_sub]
    abel
  map_positive p c hc := by
    cases p with
    | zero => exact ⟨awZero_positive θ hc, awOne_positive θ hc⟩
    | succ p => exact ⟨awZero_positive θ hc, awOne_positive θ hc, awEdge_positive θ hc⟩

end Thomason.NormalizedChains

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

variable {E : Type u} [PartialOrder E] {D : Type v} [PartialOrder D]

lemma awEdge_map (θ : E →o Fin 2) (f : D →o E) (c : Chains D) :
    awEdge θ (map f c) = map f (awEdge (θ.comp f) c) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l z c _ _ ih =>
    simp only [map_add, ih]
    congr 1
    have hz : Finsupp.single l z = z • bracket l.val := by
      rw [bracket_of_pairwise l.property]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hz]
    simp only [map_smul]
    congr 1
    have hl := l.property.imp fun h => le_of_lt h
    rw [map_bracket f hl,
      awEdge_bracket θ (List.pairwise_map.mpr (hl.imp fun h => f.monotone h)),
      awEdge_bracket (θ.comp f) hl, awEdgeWord_map θ f hl]

lemma awHom_naturality (θ : E →o Fin 2) (f : D →o E) :
    DirectedComplex.Hom.comp (complexMap f) (awHom θ) =
      DirectedComplex.Hom.comp (awHom (θ.comp f)) (complexMap f).cylinder := by
  ext p c
  cases p with
  | zero =>
    apply Prod.ext <;> apply Subtype.ext
    · exact awZero_map θ f c.val
    · change map f c.val - awZero θ (map f c.val) =
        map f (c.val - awZero (θ.comp f) c.val)
      rw [map_sub, awZero_map]
  | succ p =>
    apply Prod.ext
    · exact Subtype.ext (awZero_map θ f c.val)
    · apply Prod.ext
      · apply Subtype.ext
        change map f c.val - awZero θ (map f c.val) =
          map f (c.val - awZero (θ.comp f) c.val)
        rw [map_sub, awZero_map]
      · exact Subtype.ext (awEdge_map θ f c.val)

lemma awZero_const_zero (c : Chains E) :
    awZero (OrderHom.const E (0 : Fin 2)) c = c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l z c _ _ ih =>
    rw [map_add, ih]
    congr 1
    change Finsupp.linearCombination ℤ _ (Finsupp.single l z) = _
    rw [Finsupp.linearCombination_single, awZeroWord_of_all _ (by simp)]
    rw [bracket_of_pairwise l.property]
    simp

lemma awEdge_const_zero (c : Chains E) :
    awEdge (OrderHom.const E (0 : Fin 2)) c = 0 := by
  classical
  rw [awEdge, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro w _
  rw [awEdgeWord_of_all _ (by simp), smul_zero]

lemma awZero_const_one_of_grade {p : ℕ} {c : Chains E} (hc : c ∈ grade (p+1)) :
    awZero (OrderHom.const E (1 : Fin 2)) c = 0 := by
  classical
  rw [awZero, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro w hw
  have hl := (mem_grade_iff (p+1) c).mp hc w (Finsupp.mem_support_iff.mp hw)
  have hn : w.val ≠ [] := by intro he; simp [he] at hl
  rw [awZeroWord_of_not_all, smul_zero]
  intro h
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil w.val hn
  simpa using h a ha

lemma awEdge_const_one_of_grade {p : ℕ} {c : Chains E} (hc : c ∈ grade (p+2)) :
    awEdge (OrderHom.const E (1 : Fin 2)) c = 0 := by
  classical
  rw [awEdge, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro w hw
  have hl := (mem_grade_iff (p+2) c).mp hc w (Finsupp.mem_support_iff.mp hw)
  suffices awEdgeWord (OrderHom.const E (1 : Fin 2)) w.val = 0 by rw [this, smul_zero]
  rcases w with ⟨w, hws⟩
  cases w using List.reverseRecOn with
  | nil => simp at hl
  | append_singleton l a =>
    rw [awEdgeWord_append]
    change (if (1 : Fin 2) = 0 then 0 else awZeroWord (OrderHom.const E 1) l) = 0
    rw [ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
    apply awZeroWord_of_not_all
    intro h
    have hn : l ≠ [] := by intro he; simp [he] at hl
    obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil l hn
    simpa using h b hb

lemma awHom_endpoint (b : Bool) :
    awHom (OrderHom.const E (if b then (1 : Fin 2) else 0)) =
      (complex E).cylinderEndpoint b := by
  ext p c
  cases p with
  | zero =>
    cases b <;> apply Prod.ext <;> apply Subtype.ext
    · exact awZero_const_zero c.val
    · change c.val - awZero (OrderHom.const E (0 : Fin 2)) c.val = 0
      rw [awZero_const_zero, sub_self]
    · exact awZero_const_one_of_grade c.property
    · change c.val - awZero (OrderHom.const E (1 : Fin 2)) c.val = c.val
      rw [awZero_const_one_of_grade c.property, sub_zero]
  | succ p =>
    cases b
    · apply Prod.ext
      · exact Subtype.ext (awZero_const_zero c.val)
      · apply Prod.ext <;> apply Subtype.ext
        · change c.val - awZero (OrderHom.const E (0 : Fin 2)) c.val = 0
          rw [awZero_const_zero, sub_self]
        · exact awEdge_const_zero c.val
    · apply Prod.ext
      · exact Subtype.ext (awZero_const_one_of_grade c.property)
      · apply Prod.ext <;> apply Subtype.ext
        · change c.val - awZero (OrderHom.const E (1 : Fin 2)) c.val = c.val
          rw [awZero_const_one_of_grade c.property, sub_zero]
        · exact awEdge_const_one_of_grade c.property

end Thomason.NormalizedChains

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


namespace Thomason

open CategoryTheory Limits

instance boundaryImages_smallObject {C : Type v} [Category.{u} C]
    [IsLocallyPresentable.{u} C] [HasColimitsOfSize.{u,u} C] (L : SSet.{u} ⥤ C) :
    MorphismProperty.HasSmallObjectArgument.{u} (boundaryImages L) :=
  SmallObject.smallObjectArgument (boundaryImages L)

instance hornImages_smallObject {C : Type v} [Category.{u} C]
    [IsLocallyPresentable.{u} C] [HasColimitsOfSize.{u,u} C] (L : SSet.{u} ⥤ C) :
    MorphismProperty.HasSmallObjectArgument.{u} (hornImages L) :=
  SmallObject.smallObjectArgument (hornImages L)

lemma boundaryImages_weakFactorization {C : Type v} [Category.{u} C]
    [IsLocallyPresentable.{u} C] [HasColimitsOfSize.{u,u} C] (L : SSet.{u} ⥤ C) :
    MorphismProperty.IsWeakFactorizationSystem (boundaryImages L).rlp.llp
      (boundaryImages L).rlp := SmallObject.weakFactorizationSystem _

end Thomason

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


namespace Thomason.KanQuillen

open CategoryTheory Simplicial Opposite

variable {X Y : SSet.{u}}

lemma lift_edge_endpoint (p : X ⟶ Y) (hp : simplicialFibrations p)
    (j : Fin 2) (e : Y _⦋1⦌) (x : X _⦋0⦌) (hx : p.app _ x = Y.δ j e) :
    ∃ e' : X _⦋1⦌, X.δ j e' = x ∧ p.app _ e' = e := by
  have : HasLiftingProperty (SSet.stdSimplex.δ (n := 0) j) p :=
    SimplicialCylinder.delta_one_anodyne j p hp
  let sq : CommSq (SSet.yonedaEquiv.symm x) (SSet.stdSimplex.δ j) p
      (SSet.yonedaEquiv.symm e) := ⟨by
    rw [SSet.yonedaEquiv_symm_comp, SSet.stdSimplex.δ_comp_yonedaEquiv_symm, hx]⟩
  refine ⟨SSet.yonedaEquiv sq.lift, ?_, ?_⟩
  · have h := congrArg SSet.yonedaEquiv sq.fac_left
    simpa only [SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using h
  · have h := congrArg SSet.yonedaEquiv sq.fac_right
    simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using h

lemma fibration_range_edge (p : X ⟶ Y) (hp : simplicialFibrations p)
    {a b : Y _⦋0⦌} (e : Y.Edge a b) :
    (∃ x, p.app _ x = a) ↔ (∃ x, p.app _ x = b) := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨e', _, he'⟩ := lift_edge_endpoint p hp 1 e.edge x (hx.trans e.src_eq.symm)
    refine ⟨X.δ 0 e', ?_⟩
    have hn := ConcreteCategory.congr_hom (p.naturality (SimplexCategory.δ (0 : Fin 2)).op) e'
    change p.app _ (X.δ 0 e') = Y.δ 0 (p.app _ e') at hn
    exact hn.trans ((congrArg (Y.δ 0) he').trans e.tgt_eq)
  · rintro ⟨x, hx⟩
    obtain ⟨e', _, he'⟩ := lift_edge_endpoint p hp 0 e.edge x (hx.trans e.tgt_eq.symm)
    refine ⟨X.δ 1 e', ?_⟩
    have hn := ConcreteCategory.congr_hom (p.naturality (SimplexCategory.δ (1 : Fin 2)).op) e'
    change p.app _ (X.δ 1 e') = Y.δ 1 (p.app _ e') at hn
    exact hn.trans ((congrArg (Y.δ 1) he').trans e.src_eq)

lemma fibration_range_components (p : X ⟶ Y) (hp : simplicialFibrations p)
    {a b : Y _⦋0⦌} (h : SSet.π₀.mk a = SSet.π₀.mk b) :
    (∃ x, p.app _ x = a) ↔ (∃ x, p.app _ x = b) := by
  let r : SSet.π₀ Y → Prop := SSet.π₀.lift (fun y => ∃ x, p.app _ x = y)
    (fun _ _ e => propext (fibration_range_edge p hp e))
  exact Iff.of_eq (congrArg r h)

theorem weak_fibration_surjective_vertices (p : X ⟶ Y)
    (hp : simplicialFibrations p) (hw : simplicialWeakEquivalences p) :
    Function.Surjective (p.app (op ⦋0⦌)) := by
  intro y
  obtain ⟨a, ha⟩ := (map_components_bijective_of_weak p hw).2 (SSet.π₀.mk y)
  induction a using SSet.π₀.rec with | mk x =>
    exact (fibration_range_components p hp ha).1 ⟨x, rfl⟩

end Thomason.KanQuillen

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

open CategoryTheory Limits

noncomputable def exInfinityUnit : 𝟭 SSet.{u} ⟶ exInfinityFunctor where
  app := exInfinityComparison
  naturality {_ _} f := (exInfinityInclusion_naturality f 0).symm

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Limits

instance exStage_preservesLimits (n : ℕ) :
    PreservesLimits (exSequenceFunctor.{u} ⋙ (evaluation ℕ SSet).obj n) := by
  induction n with
  | zero =>
      change PreservesLimits (𝟭 SSet.{u})
      infer_instance
  | succ n ih =>
      let : PreservesLimits (exSequenceFunctor.{u} ⋙ (evaluation ℕ SSet).obj n) := ih
      change PreservesLimits ((exSequenceFunctor.{u} ⋙ (evaluation ℕ SSet).obj n) ⋙ SSet.ex)
      infer_instance

instance exSequence_preservesLimits : PreservesLimits exSequenceFunctor.{u} :=
  preservesLimits_of_evaluation _ (fun _ => inferInstance)

instance exInfinity_preservesFiniteLimits : PreservesFiniteLimits exInfinityFunctor.{u} := by
  unfold exInfinityFunctor
  infer_instance

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Limits Opposite

instance finiteOrderNerve (E : Type u) [PartialOrder E] [Finite E] : (nerve E).Finite where
  finite := Finite.of_equiv (PartialOrder.NonemptyFiniteChains E) nerveNondegenerateChains.toEquiv.symm

instance ex_preservesFilteredColimits : PreservesFilteredColimits SSet.ex.{u} where
  preserves_filtered_colimits J _ _ := by
    apply preservesColimitsOfShape_of_evaluation
    intro n
    have : SSet.Finite (SimplexCategory.sd.{u}.obj n.unop) := by
      change SSet.Finite (nerve (PartialOrder.NonemptyFiniteChains (ULift (Fin (n.unop.len+1)))))
      infer_instance
    exact preservesColimitsOfShape_of_natIso (exEvaluationIso n).symm

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Limits

instance exStage_preservesFilteredColimits (n : ℕ) :
    PreservesFilteredColimits (exSequenceFunctor.{u} ⋙ (evaluation ℕ SSet).obj n) := by
  induction n with
  | zero =>
      change PreservesFilteredColimits (𝟭 SSet.{u})
      infer_instance
  | succ n ih =>
      let : PreservesFilteredColimits (exSequenceFunctor.{u} ⋙ (evaluation ℕ SSet).obj n) := ih
      change PreservesFilteredColimits ((exSequenceFunctor.{u} ⋙ (evaluation ℕ SSet).obj n) ⋙ SSet.ex)
      infer_instance

instance exSequence_preservesFilteredColimits : PreservesFilteredColimits exSequenceFunctor.{u} where
  preserves_filtered_colimits _J _ _ :=
    preservesColimitsOfShape_of_evaluation _ _ (fun _ => inferInstance)

instance exInfinity_preservesFilteredColimits : PreservesFilteredColimits exInfinityFunctor.{u} := by
  unfold exInfinityFunctor
  infer_instance

instance exInfinity_preservesMonomorphisms : exInfinityFunctor.{u}.PreservesMonomorphisms := by
  infer_instance

end Thomason.Subdivision

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


namespace Thomason.NormalizedChains.PosetTables

open CategoryTheory OmegaCategory DirectedComplex

variable {P : Type u} [PartialOrder P] {Q : Type u} [PartialOrder Q]

noncomputable def upperSegmentLabel (S : Set P) (hS : IsUpperSet S) : P →o Fin 2 := by
  classical
  exact {
    toFun := fun a => if a ∈ S then 1 else 0
    monotone' := by
      intro a b hab
      by_cases ha : a ∈ S
      · have hb : b ∈ S := hS hab ha
        simp only [ite_eq_left ha, ite_eq_left hb, le_refl]
      · simp only [ite_eq_right ha]
        exact Fin.zero_le _ }

@[simp] lemma upperSegmentLabel_one (S : Set P) (hS : IsUpperSet S) (a : P) :
    upperSegmentLabel S hS a = 1 ↔ a ∈ S := by
  classical
  change (if a ∈ S then (1 : Fin 2) else 0) = 1 ↔ a ∈ S
  by_cases ha : a ∈ S <;> simp [ha]

end Thomason.NormalizedChains.PosetTables

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

lemma cylinderMap_zero {C D : Cat.{u,u}} (H : Cat.of (Interval.{u} × C) ⟶ D) :
    SSet.ι₀ ≫ cylinderMap H = nerveFunctor.map (endpoint C 0 ≫ H) := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro x
  rfl
lemma cylinderMap_one {C D : Cat.{u,u}} (H : Cat.of (Interval.{u} × C) ⟶ D) :
    SSet.ι₁ ≫ cylinderMap H = nerveFunctor.map (endpoint C 1 ≫ H) := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end Thomason.OneCat

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_HomotopyExtension
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Homotopy Extension. -/

noncomputable section
universe u v w z


namespace Thomason.CoherentGluing
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory

lemma zeroFactor_one (X : SSet.{u}) :
    (SimplicialCylinder.zeroFactorIso X).hom ≫ X ◁ SSet.stdSimplex.δ (n := 0) 0 = SSet.ι₁ := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.ext
    intro z
    rfl

end Thomason.CoherentGluing

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


namespace Thomason.HornSubdivision
open CategoryTheory Simplicial PartialOrder Subdivision

lemma sdTwice_horn_anodyne {n : ℕ} (hn : 1 ≤ n) (k : Fin (n+1)) :
    SSet.anodyneExtensions ((SSet.sd ⋙ SSet.sd).map (SSet.horn.{u} n k).ι) :=
  sd_preserves_anodyne _ (sd_horn_anodyne hn k)
end Thomason.HornSubdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision
open CategoryTheory

def LastVertexStatement : Prop :=
  ∀ X : SSet.{u}, simplicialWeakEquivalences (lastVertex.app X)
end Thomason.Subdivision

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

lemma local_anodyne {A B : SSet.{u}} (f : A ⟶ B) (hf : SSet.anodyneExtensions f) :
    Local f := fun K _ => heq_of_rlp _ (pre_rlp_of_anodyne f hf K)

end Thomason.KanLocal

end

noncomputable section
universe u v w z


namespace Thomason.KanLocal
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed Simplicial
open LastVertexProof KanHomotopy HornSubdivision
open SSet.modelCategoryQuillen

lemma homotopy_of_anodyne_eq_relative {A B K : SSet.{u}} (i : A ⟶ B)
    (hi : SSet.anodyneExtensions i) [SSet.KanComplex K]
    (f g : B ⟶ K) (h : i ≫ f = i ≫ g) :
    ∃ H : SSet.Homotopy f g, i ▷ Δ[1] ≫ H.h = fst _ _ ≫ i ≫ f := by
  let s := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i intervalEnds
  let H : A ⊗ Δ[1] ⟶ K := fst _ _ ≫ i ≫ f
  have hc : i ▷ SimplicialCylinder.Ends Δ[0] ≫ endsTensorMap f g = A ◁ intervalEnds ≫ H := by
    ext k x
    rcases x with ⟨x,y⟩
    cases y with
    | inl y => rfl
    | inr y => exact (congrArg (fun t : A ⟶ K => t.app k x) h).symm
  let a : s.pt ⟶ K := s.isPushout.desc (endsTensorMap f g) H hc
  have : HasLiftingProperty s.ι (terminal.from K) :=
    SSet.anodyneExtensions_pushoutObjObjι' s hi (terminal.from K)
      (by rw [← HomotopicalAlgebra.fibration_iff]; infer_instance)
  let lsq : CommSq a s.ι (terminal.from K) (terminal.from (B ⊗ Δ[1])) := ⟨by simp⟩
  have he : B ◁ intervalEnds ≫ lsq.lift = endsTensorMap f g := by
    have hij : s.inl ≫ s.ι = B ◁ intervalEnds := s.inl_ι
    rw [← hij, Category.assoc, lsq.fac_left]
    exact s.isPushout.inl_desc _ _ _
  let Q : SSet.Homotopy f g := CoherentGluing.toHomotopy lsq.lift
    (by ext k x
        exact congrArg (fun t => t.app k (x, Sum.inl (SSet.stdSimplex.objMk (OrderHom.const _ 0)))) he)
    (by ext k x
        exact congrArg (fun t => t.app k (x, Sum.inr (SSet.stdSimplex.objMk (OrderHom.const _ 0)))) he)
  refine ⟨Q, ?_⟩
  change i ▷ Δ[1] ≫ lsq.lift = H
  have hij : s.inr ≫ s.ι = i ▷ Δ[1] := s.inr_ι
  rw [← hij, Category.assoc, lsq.fac_left]
  exact s.isPushout.inr_desc _ _ _

lemma anodyne_deformation {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y]
    (i : X ⟶ Y) (hi : SSet.anodyneExtensions i) :
    ∃ (r : Y ⟶ X) (H : SSet.Homotopy (𝟙 Y) (r ≫ i)),
      i ≫ r = 𝟙 X ∧ i ▷ Δ[1] ≫ H.h = fst _ _ ≫ i := by
  obtain ⟨r,hr⟩ := extend_anodyne i hi (𝟙 X)
  obtain ⟨H,hH⟩ := homotopy_of_anodyne_eq_relative i hi (𝟙 Y) (r ≫ i)
    (by simp [← Category.assoc, hr])
  exact ⟨r,H,hr,by simpa using hH⟩

lemma heq_anodyne {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y]
    (i : X ⟶ Y) (hi : SSet.anodyneExtensions i) : IsHomotopyEquivalence i := by
  obtain ⟨r,H,hr,_⟩ := anodyne_deformation i hi
  refine ⟨r, ?_, homotopic_symm (homotopic_of_homotopy H)⟩
  rw [hr]
  exact homotopic_refl _

lemma pullback_anodyne_heq {P X E Y : SSet.{u}}
    [SSet.KanComplex X] [SSet.KanComplex Y]
    {a : P ⟶ X} {j : P ⟶ E} {i : X ⟶ Y} {p : E ⟶ Y}
    (sq : IsPullback a j i p) (hi : SSet.anodyneExtensions i)
    (hp : simplicialFibrations p) : IsHomotopyEquivalence j := by
  let : Mono i := KanQuillen.anodyne_monomorphism _ hi
  let : Mono j := MorphismProperty.of_isPullback sq
    (show (MorphismProperty.monomorphisms SSet) i from inferInstance)
  obtain ⟨r,H,hr,hH⟩ := anodyne_deformation i hi
  obtain ⟨Q,hQ,hQ₀,hQp⟩ := cylinder_lift j p hp 1 (𝟙 E)
    (fst P Δ[1] ≫ j) (p ▷ Δ[1] ≫ H.h)
    (by simp [endpoint_zero])
    (by rw [endpoint_zero, SSet.ι₀_comp_assoc, H.h₀, Category.comp_id, Category.id_comp])
    (by
      calc
        (fst P Δ[1] ≫ j) ≫ p = fst P Δ[1] ≫ a ≫ i := by rw [Category.assoc, ← sq.w]
        _ = a ▷ Δ[1] ≫ i ▷ Δ[1] ≫ H.h := by rw [hH, whiskerRight_fst_assoc]
        _ = j ▷ Δ[1] ≫ p ▷ Δ[1] ≫ H.h := by
          rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, sq.w,
            MonoidalCategory.comp_whiskerRight, Category.assoc])
  let s : E ⟶ P := sq.lift (p ≫ r) (SSet.ι₁ ≫ Q)
    (by simp only [Category.assoc]; rw [hQp, SSet.ι₁_comp_assoc, H.h₁])
  have hs : j ≫ s = 𝟙 P := by
    apply sq.hom_ext
    · simp only [Category.assoc, s, IsPullback.lift_fst, Category.id_comp]
      rw [← Category.assoc, ← sq.w, Category.assoc, hr, Category.comp_id]
    · simp only [Category.assoc, s, IsPullback.lift_snd, Category.id_comp]
      rw [← SSet.ι₁_comp_assoc, hQ]
      simp
  refine ⟨s, ?_, ?_⟩
  · rw [hs]
    exact homotopic_refl _
  · have H' : SSet.Homotopy (𝟙 E) (s ≫ j) :=
      CoherentGluing.toHomotopy Q (by simpa [endpoint_zero] using hQ₀)
        (by simp [s])
    exact homotopic_symm (homotopic_of_homotopy H')

lemma pullback_heq {P X E Y : SSet.{u}}
    [SSet.KanComplex X] [SSet.KanComplex Y]
    {a : P ⟶ X} {j : P ⟶ E} {f : X ⟶ Y} {p : E ⟶ Y}
    (sq : IsPullback a j f p) (hf : IsHomotopyEquivalence f)
    (hp : simplicialFibrations p) : IsHomotopyEquivalence j := by
  let d := MorphismProperty.factorizationData SSet.modelCategoryQuillen.J.rlp.llp
    SSet.modelCategoryQuillen.J.rlp f
  let : HomotopicalAlgebra.Fibration d.p := by
    rw [HomotopicalAlgebra.fibration_iff, SSet.modelCategoryQuillen.fibrations_eq]
    exact d.hp
  let : SSet.KanComplex d.Z := HomotopicalAlgebra.isFibrant_of_fibration d.p
  have hd : IsHomotopyEquivalence d.p := heq_of_precomp d.i d.p
    (heq_anodyne d.i d.hi) (d.fac.symm ▸ hf)
  have hd' := rlp_of_homotopy_equivalence d.p d.hp hd
  let b := pullback.fst d.p p
  let c := pullback.snd d.p p
  have sq₀ : IsPullback b c d.p p := IsPullback.of_hasPullback d.p p
  let k : P ⟶ pullback d.p p := sq₀.lift (a ≫ d.i) j
    (by rw [Category.assoc, d.fac, sq.w])
  have hk₀ : k ≫ b = a ≫ d.i := sq₀.lift_fst _ _ _
  have hk₁ : k ≫ c = j := sq₀.lift_snd _ _ _
  have sq₁ : IsPullback a k d.i b := by
    have sq' : IsPullback a (k ≫ c) (d.i ≫ d.p) p := by rw [hk₁, d.fac]; exact sq
    exact sq'.of_bot hk₀.symm sq₀
  have hb : simplicialFibrations b := by
    change SSet.modelCategoryQuillen.J.rlp b
    exact MorphismProperty.of_isPullback sq₀.flip hp
  have hk : IsHomotopyEquivalence k := pullback_anodyne_heq sq₁ d.hi hb
  have hc : IsHomotopyEquivalence c := heq_of_rlp c (MorphismProperty.of_isPullback sq₀ hd')
  exact hk₁ ▸ heq_comp hk hc

lemma local_pushout {A B C D : SSet.{u}} {f : A ⟶ B} {i : A ⟶ C}
    {j : B ⟶ D} {k : C ⟶ D} (sq : IsPushout f i j k) [Mono i]
    (hf : Local f) : Local k := by
  intro K hK
  have sq' := sq.op.map (internalHom.flip.obj K)
  have hi : simplicialFibrations ((pre i).app K) := by
    change SSet.modelCategoryQuillen.J.rlp _
    rw [← SSet.modelCategoryQuillen.fibrations_eq, ← HomotopicalAlgebra.fibration_iff]
    infer_instance
  have sq'' : IsPullback ((pre j).app K) ((pre k).app K)
      ((pre f).app K) ((pre i).app K) := sq'.flip
  exact pullback_heq sq'' (hf K hK) hi

lemma local_pushout_map {K A B C P Q : SSet.{u}} (k : K ⟶ A) (c : K ⟶ C) [Mono c]
    (f : A ⟶ B) (hf : Local f)
    {lA : A ⟶ P} {lC : C ⟶ P} (sp : IsPushout k c lA lC)
    {lB : B ⟶ Q} {lC' : C ⟶ Q} (sq : IsPushout (k ≫ f) c lB lC')
    (F : P ⟶ Q) (hFA : lA ≫ F = f ≫ lB) (hFC : lC ≫ F = lC') : Local F := by
  have sq' : IsPushout (k ≫ f) c lB (lC ≫ F) := by rw [hFC]; exact sq
  have : Mono lA := MorphismProperty.of_isPushout sp
    (show (MorphismProperty.monomorphisms SSet) c from inferInstance)
  exact local_pushout (sq'.of_left hFA.symm sp) hf

end Thomason.KanLocal

end

noncomputable section
universe u v w z


namespace Thomason.OneCat
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory

@[reassoc] lemma cylinderMap_pre {C D E : Cat.{u,u}} (f : C ⟶ D)
    (H : cylinder.obj D ⟶ E) :
    nerveFunctor.map f ▷ Δ[1] ≫ cylinderMap H = cylinderMap (cylinder.map f ≫ H) := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro x
  rfl

@[reassoc] lemma cylinderMap_post {C D E : Cat.{u,u}} (H : cylinder.obj C ⟶ D)
    (f : D ⟶ E) :
    cylinderMap H ≫ nerveFunctor.map f = cylinderMap (H ≫ f) := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro x
  rfl

lemma cylinderMap_projection (C : Cat.{u,u}) :
    cylinderMap (projection C) = fst (nerveFunctor.obj C) Δ[1] := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro x
  rfl

lemma pushout_deformation_coherent {A E X Y : Cat.{u,u}} {a : A ⟶ X} {i : A ⟶ E}
    {j : X ⟶ Y} {v : E ⟶ Y} (sq : IsPushout a i j v)
    (r : E ⟶ A) (ri : i ≫ r = 𝟙 A)
    (H : cylinder.obj E ⟶ E)
    (h₀ : endpoint E 0 ≫ H = r ≫ i)
    (h₁ : endpoint E 1 ≫ H = 𝟙 E)
    (hA : cylinder.map i ≫ H = projection A ≫ i) :
    ∃ (p : Y ⟶ X) (H' : cylinder.obj Y ⟶ Y),
      j ≫ p = 𝟙 X ∧ v ≫ p = r ≫ a ∧
      endpoint Y 0 ≫ H' = p ≫ j ∧ endpoint Y 1 ≫ H' = 𝟙 Y ∧
      cylinder.map j ≫ H' = projection X ≫ j ∧ cylinder.map v ≫ H' = H ≫ v := by
  let p : Y ⟶ X := sq.desc (𝟙 X) (r ≫ a) (by simp [← Category.assoc,ri])
  have pj : j ≫ p = 𝟙 X := sq.inl_desc _ _ _
  have pv : v ≫ p = r ≫ a := sq.inr_desc _ _ _
  have sw := sq.map cylinder
  have hw : cylinder.map a ≫ (projection X ≫ j) = cylinder.map i ≫ (H ≫ v) := by
    rw [projection_natural_assoc, ← Category.assoc (cylinder.map i),hA]
    simpa only [Category.assoc] using congrArg (projection A ≫ ·) sq.w
  let Q : cylinder.obj Y ⟶ Y := sw.desc (projection X ≫ j) (H ≫ v) hw
  have Qj : cylinder.map j ≫ Q = projection X ≫ j := sw.inl_desc _ _ _
  have Qv : cylinder.map v ≫ Q = H ≫ v := sw.inr_desc _ _ _
  refine ⟨p,Q,pj,pv,?_,?_,Qj,Qv⟩
  · apply sq.hom_ext
    · erw [← Category.assoc, ← endpoint_natural, Category.assoc, Qj, ← Category.assoc, endpoint_projection,
        Category.id_comp, ← Category.assoc, pj, Category.id_comp]
    · erw [← Category.assoc, ← endpoint_natural, Category.assoc, Qv, ← Category.assoc, h₀,
        ← Category.assoc v p j, pv]
      simpa only [Category.assoc] using congrArg (r ≫ ·) sq.w.symm
  · apply sq.hom_ext
    · erw [Category.comp_id, ← Category.assoc, ← endpoint_natural, Category.assoc, Qj,
        ← Category.assoc, endpoint_projection, Category.id_comp]
    · erw [Category.comp_id, ← Category.assoc, ← endpoint_natural, Category.assoc, Qv,
        ← Category.assoc, h₁, Category.id_comp]

lemma nerve_pushout_coherent {A E X Y : Cat.{u,u}} {a : A ⟶ X} {i : A ⟶ E}
    {j : X ⟶ Y} {v : E ⟶ Y} (sc : IsPushout a i j v)
    (r : E ⟶ A) (ri : i ≫ r = 𝟙 A)
    (HE : cylinder.obj E ⟶ E)
    (h₀ : endpoint E 0 ≫ HE = r ≫ i)
    (h₁ : endpoint E 1 ≫ HE = 𝟙 E)
    (hA : cylinder.map i ≫ HE = projection A ≫ i)
    {P : SSet.{u}} {lX : nerveFunctor.obj X ⟶ P} {lE : nerveFunctor.obj E ⟶ P}
    (ss : IsPushout (nerveFunctor.map a) (nerveFunctor.map i) lX lE)
    (F : P ⟶ nerveFunctor.obj Y) (hFX : lX ≫ F = nerveFunctor.map j)
    (hFE : lE ≫ F = nerveFunctor.map v) :
    ∃ (G : nerveFunctor.obj Y ⟶ P)
      (HP : SSet.Homotopy (F ≫ G) (𝟙 P))
      (HQ : SSet.Homotopy (G ≫ F) (𝟙 (nerveFunctor.obj Y))),
      HP.h ≫ F = F ▷ Δ[1] ≫ HQ.h := by
  obtain ⟨p,HY,hpj,hpv,hY₀,hY₁,hYX,hYE⟩ :=
    pushout_deformation_coherent sc r ri HE h₀ h₁ hA
  let G : nerveFunctor.obj Y ⟶ P := nerveFunctor.map p ≫ lX
  have hG₀ : nerveFunctor.map (p ≫ j) = G ≫ F := by
    simp only [G, CategoryTheory.Functor.map_comp, Category.assoc, hFX]
  let HQ : SSet.Homotopy (G ≫ F) (𝟙 (nerveFunctor.obj Y)) :=
    CoherentGluing.toHomotopy (cylinderMap HY)
      (by erw [cylinderMap_zero,hY₀,hG₀])
      (by erw [cylinderMap_one,hY₁,CategoryTheory.Functor.map_id])
  have hI : (nerveFunctor.map a ▷ Δ[1]) ≫ (fst (nerveFunctor.obj X) Δ[1] ≫ lX) =
      (nerveFunctor.map i ▷ Δ[1]) ≫ (cylinderMap HE ≫ lE) := by
    erw [← Category.assoc _ (cylinderMap HE), cylinderMap_pre, hA, ← cylinderMap_post,
      cylinderMap_projection]
    erw [Category.assoc, ← ss.w]
    rfl
  let sI := ss.map (tensorRight (Δ[1] : SSet.{u}))
  let H : P ⊗ Δ[1] ⟶ P := sI.desc (fst (nerveFunctor.obj X) Δ[1] ≫ lX)
    (cylinderMap HE ≫ lE) hI
  have hHX : lX ▷ Δ[1] ≫ H = fst (nerveFunctor.obj X) Δ[1] ≫ lX := sI.inl_desc _ _ _
  have hHE : lE ▷ Δ[1] ≫ H = cylinderMap HE ≫ lE := sI.inr_desc _ _ _
  have hH₀ : SSet.ι₀ ≫ H = F ≫ G := by
    apply ss.hom_ext
    · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, hHX,
        ← Category.assoc, SSet.ι₀_fst, Category.id_comp,
        ← Category.assoc lX F, hFX]
      dsimp only [G]
      rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, hpj, CategoryTheory.Functor.map_id, Category.id_comp]
    · erw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, hHE,
        ← Category.assoc, cylinderMap_zero,h₀,CategoryTheory.Functor.map_comp,
        Category.assoc, ← ss.w, ← Category.assoc lE F, hFE]
      dsimp only [G]
      rw [← Category.assoc (nerveFunctor.map v), ← CategoryTheory.Functor.map_comp, hpv]
      rw [CategoryTheory.Functor.map_comp, Category.assoc]
  have hH₁ : SSet.ι₁ ≫ H = 𝟙 P := by
    apply ss.hom_ext
    · rw [Category.comp_id, ← Category.assoc, ← SSet.ι₁_comp, Category.assoc, hHX,
        ← Category.assoc, SSet.ι₁_fst, Category.id_comp]
    · erw [Category.comp_id, ← Category.assoc, ← SSet.ι₁_comp, Category.assoc, hHE,
        ← Category.assoc, cylinderMap_one, h₁, CategoryTheory.Functor.map_id, Category.id_comp]
  refine ⟨G, CoherentGluing.toHomotopy H hH₀ hH₁, HQ, ?_⟩
  change H ≫ F = F ▷ Δ[1] ≫ cylinderMap HY
  apply sI.hom_ext
  · change lX ▷ Δ[1] ≫ (H ≫ F) = lX ▷ Δ[1] ≫ (F ▷ Δ[1] ≫ cylinderMap HY)
    erw [← Category.assoc _ H, hHX, Category.assoc, hFX,
      ← Category.assoc (lX ▷ Δ[1]), ← comp_whiskerRight, hFX,
      cylinderMap_pre, hYX, ← cylinderMap_post,cylinderMap_projection]
    rfl
  · change lE ▷ Δ[1] ≫ (H ≫ F) = lE ▷ Δ[1] ≫ (F ▷ Δ[1] ≫ cylinderMap HY)
    erw [← Category.assoc _ H, hHE, Category.assoc, hFE,
      ← Category.assoc (lE ▷ Δ[1]), ← comp_whiskerRight, hFE,
      cylinderMap_pre,hYE,← cylinderMap_post]
    rfl
end Thomason.OneCat

end

noncomputable section
universe u v w z


namespace Thomason.CoherentGluing
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory

lemma coherent_of_postIso {A B C : SSet.{u}} (f : A ⟶ B) (e : B ≅ C)
    (h : Coherent (f ≫ e.hom)) : Coherent f := by
  obtain ⟨g,HA,HB,hcoh⟩ := h
  let g' := e.hom ≫ g
  let HA' : SSet.Homotopy (f ≫ g') (𝟙 A) :=
    toHomotopy HA.h (by simpa only [g',Category.assoc] using HA.h₀) HA.h₁
  let HB' : SSet.Homotopy (g' ≫ f) (𝟙 B) :=
    toHomotopy (e.hom ▷ Δ[1] ≫ HB.h ≫ e.inv)
      (by rw [SSet.ι₀_comp_assoc, HB.h₀_assoc]; simp [g',Category.assoc])
      (by rw [SSet.ι₁_comp_assoc, HB.h₁_assoc]; simp)
  refine ⟨g',HA',HB',?_⟩
  change HA.h ≫ f = f ▷ Δ[1] ≫ e.hom ▷ Δ[1] ≫ HB.h ≫ e.inv
  apply (cancel_mono e.hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id, comp_whiskerRight] using hcoh
end Thomason.CoherentGluing

end

noncomputable section
universe u v w z


namespace Thomason.OneCat
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory

variable {A E : Type u} [PartialOrder A] [PartialOrder E]
    (i : A →o E) (r : E →o A) (ri : ∀ a, r (i a) = a)
    (counit : ∀ e, i (r e) ≤ e)

def orderMapCylinder : Interval.{u} × E →o E where
  toFun x := if x.1.down = 0 then i (r x.2) else x.2
  monotone' := by
    rintro ⟨⟨b⟩,e⟩ ⟨⟨c⟩,f⟩ ⟨hbc,hef⟩
    fin_cases b <;> fin_cases c
    · exact i.monotone (r.monotone hef)
    · exact (counit e).trans hef
    · exact False.elim (by simp at hbc)
    · exact hef

def posetMapCylinder : cylinder.obj (Cat.of E) ⟶ Cat.of E :=
  ({ obj := orderMapCylinder i r counit
     map := fun f => homOfLE ((orderMapCylinder i r counit).monotone
       ⟨leOfHom f.1,leOfHom f.2⟩) } : Interval.{u} × E ⥤ E).toCatHom

lemma posetMapCylinder_zero : endpoint (Cat.of E) 0 ≫ posetMapCylinder i r counit =
    r.toFunctor.toCatHom ≫ i.toFunctor.toCatHom := by
  apply Cat.Hom.ext
  exact CategoryTheory.Functor.ext (fun _ => rfl)
lemma posetMapCylinder_one : endpoint (Cat.of E) 1 ≫ posetMapCylinder i r counit = 𝟙 (Cat.of E) := by
  apply Cat.Hom.ext
  exact CategoryTheory.Functor.ext (fun _ => rfl)
include ri in
lemma posetMapCylinder_stationary :
    cylinder.map i.toFunctor.toCatHom ≫ posetMapCylinder i r counit =
      projection (Cat.of A) ≫ i.toFunctor.toCatHom := by
  apply Cat.Hom.ext
  exact CategoryTheory.Functor.ext (fun ⟨⟨b⟩,a⟩ => by
    change (if b = 0 then i (r (i a)) else i a) = i a
    rw [ri a]
    simp)

end Thomason.OneCat

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
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory MonoidalClosed

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal KanPath Subdivision

lemma relative_representative {E K A B : SSet.{u}}
    [SSet.KanComplex E] [SSet.KanComplex K]
    (e : E ⟶ K) (he : IsHomotopyEquivalence e) (i : B ⟶ A) [Mono i]
    (b : B ⟶ E) (a : A ⟶ K) (ha : i ≫ a = b ≫ e) :
    ∃ g : A ⟶ E, ∃ H : SSet.Homotopy (g ≫ e) a,
      i ≫ g = b ∧ (i ▷ Δ[1]) ≫ H.h = fst B Δ[1] ≫ b ≫ e := by
  let : HasLiftingProperty i (right e) := right_rlp e he i inferInstance
  let sq : CommSq (b ≫ left e) i (right e) a := ⟨by simpa using ha.symm⟩
  let g : A ⟶ E := sq.lift ≫ pullback.fst e (eval₀ K)
  let t : A ⟶ Paths K := sq.lift ≫ pullback.snd e (eval₀ K)
  have ht₀ : t ≫ eval₀ K = g ≫ e := by
    dsimp [t,g]
    simp only [Category.assoc,← pullback.condition]
  have ht₁ : t ≫ eval₁ K = a := sq.fac_right
  refine ⟨g,CoherentGluing.toHomotopy (uncurryR t)
    ((comp_eval₀ t).symm.trans ht₀) ((comp_eval₁ t).symm.trans ht₁), ?_, ?_⟩
  · dsimp [g]
    rw [← Category.assoc,sq.fac_left]
    simp [left, pullback.lift_fst]
  · change i ▷ Δ[1] ≫ uncurryR t = _
    rw [← uncurryR_pre]
    have ht : i ≫ t = b ≫ e ≫ const K := by
      dsimp [t]
      rw [← Category.assoc,sq.fac_left]
      simp [left, pullback.lift_snd]
    rw [ht]
    simp only [uncurryR_pre,const,uncurryR_curryR,whiskerRight_fst_assoc,whiskerRight_fst]

lemma finite_relative_stage {A B X : SSet.{u}} [SSet.Finite A] [SSet.Finite B]
    (i : B ⟶ A) (b : B ⟶ X) (g : A ⟶ exInfinity X)
    (hg : i ≫ g = b ≫ exInfinityComparison X) :
    ∃ n, ∃ t : A ⟶ exStage X n,
      t ≫ exInfinityInclusion X n = g ∧
      i ≫ t = b ≫ (exSequence X).map (homOfLE (Nat.zero_le n)) := by
  let : PreservesFilteredColimitsOfSize.{0,0} (coyoneda.obj (Opposite.op A)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  let : PreservesFilteredColimitsOfSize.{0,0} (coyoneda.obj (Opposite.op B)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  obtain ⟨n,t,ht⟩ := Limits.exists_hom_of_preservesColimit_coyoneda
    (colimit.isColimit (exSequence X)) g
  obtain ⟨k,u,v,hk⟩ := Limits.exists_eq_of_preservesColimit_coyoneda
    (colimit.isColimit (exSequence X)) (j := 0) (i ≫ t) b (by
      rw [Category.assoc,ht]
      exact hg)
  change ∃ stage, ∃ stageLift : A ⟶ (exSequence X).obj stage,
    stageLift ≫ colimit.ι (exSequence X) stage = g ∧
      i ≫ stageLift = b ≫ (exSequence X).map (homOfLE (Nat.zero_le stage))
  refine ⟨k,t ≫ (exSequence X).map u,?_,?_⟩
  · rw [Category.assoc]
    rw [colimit.w]
    exact ht
  · have hv : v = homOfLE (Nat.zero_le k) := Subsingleton.elim _ _
    rw [Category.assoc,hv] at hk
    exact hk
end Thomason.GeometricRecognition

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

namespace Thomason.GeometricRecognition
namespace Contiguity
open PolyPoint Mesh Approximation
variable {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]

structure ChainMap (P : Type u) (Q : Type v) [PartialOrder P] [PartialOrder Q] where
  toFun : P → Q
  chains : PreservesChains toFun
instance instCoeFunChainMapForall : CoeFun (ChainMap P Q) (fun _ => P → Q) := ⟨ChainMap.toFun⟩

attribute [local instance] OAI.Thomason.GeometricRecognition.Contiguity.instDecidableEq_solutions
def Contiguous (f g : ChainMap P Q) : Prop :=
  ∀ s : NonemptyFiniteChains P,
    IsChain (· ≤ ·) (((s.finset.image f.toFun ∪ s.finset.image g.toFun : Finset Q)) : Set Q)

lemma contiguous_of_carrier (f g : ChainMap P Q) (h : PolyPoint P → PolyPoint Q)
    (hf : ∀ x, ∀ p ∈ x.weights.support, f p ∈ (h x).weights.support)
    (hg : ∀ x, ∀ p ∈ x.weights.support, g p ∈ (h x).weights.support) :
    Contiguous f g := by
  classical
  intro s
  apply IsChain.mono (t := ((h (barycenter s)).weights.support : Set Q)) _
    (h (barycenter s)).chain
  intro q hq
  rcases Finset.mem_union.mp hq with hq | hq
  · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    exact hf _ p (by simpa only [barycenter_support] using hp)
  · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    exact hg _ p (by simpa only [barycenter_support] using hp)

lemma map_support_image (f : P → Q) (hf : PreservesChains f) (x : PolyPoint P)
    (p : P) (hp : p ∈ x.weights.support) : f p ∈ (PolyPoint.map f hf x).weights.support := by
  classical
  apply Finsupp.mem_support_iff.mpr
  apply ne_of_gt
  rw [map_apply]
  have ht : 0 < x.weights p := lt_of_le_of_ne (x.nonneg p)
    (Ne.symm (Finsupp.mem_support_iff.mp hp))
  apply lt_of_lt_of_le ht
  change x.weights p ≤ ∑ q ∈ x.weights.support, if f q = f p then x.weights q else 0
  calc
    _ = if f p = f p then x.weights p else 0 := by simp
    _ ≤ _ := Finset.single_le_sum (f := fun q : P => if f q = f p then x.weights q else 0) (fun q hq => by
      split_ifs
      · exact x.nonneg q
      · exact le_rfl) hp

def toChainMap (f : P →o Q) : ChainMap P Q := ⟨f,preservesChains_monotone f⟩

end Contiguity
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open PartialOrder CategoryTheory

namespace Thomason.GeometricRecognition.Contiguity
open PolyPoint Mesh Approximation
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

attribute [local instance] OAI.Thomason.GeometricRecognition.Contiguity.instDecidableEq_solutions_1
def unionChain (f g : ChainMap P Q) (h : Contiguous f g) (s : NonemptyFiniteChains P) :
    NonemptyFiniteChains Q where
  finset := s.finset.image f.toFun ∪ s.finset.image g.toFun
  nonempty := (s.nonempty.image f.toFun).mono Finset.subset_union_left
  comparable a b := (h s).total a.property b.property

def upperMap (f g : ChainMap P Q) (h : Contiguous f g) : NonemptyFiniteChains P →o Q where
  toFun s := greatest (unionChain f g h s)
  monotone' _ _ hst := greatest_mono (Finset.union_subset_union
    (Finset.image_subset_image hst) (Finset.image_subset_image hst))

end Thomason.GeometricRecognition.Contiguity

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_RelativeContiguity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative Contiguity. -/

noncomputable section
universe u v w z
open PartialOrder

namespace Thomason.GeometricRecognition.Contiguity
open PolyPoint Mesh Approximation
variable {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]

local instance relativeContiguityFixedDecidableEq_r9c6958_1 : DecidableEq Q := Classical.decEq Q
def Fixed (B : Set P) (q : Q) (f : ChainMap P Q) : Prop := ∀ p ∈ B, f p = q

def FixedMap (B : Set P) (q : Q) := {f : ChainMap P Q // Fixed B q f}
def FixedContiguous {B : Set P} {q : Q} (f g : FixedMap B q) : Prop :=
  Contiguous f.val g.val

def fixedMapSetoid (B : Set P) (q : Q) : Setoid (FixedMap B q) where
  r := Relation.EqvGen FixedContiguous
  iseqv := ⟨fun _ => Relation.EqvGen.refl _,fun h => Relation.EqvGen.symm _ _ h,
    fun h h' => Relation.EqvGen.trans _ _ _ h h'⟩

def RelativeRelated (B : Set P) (q : Q) (f g : ChainMap P Q) : Prop :=
  ∃ hf : Fixed B q f, ∃ hg : Fixed B q g,
    Relation.EqvGen FixedContiguous (⟨f,hf⟩ : FixedMap B q) ⟨g,hg⟩

lemma fixed_of_carrier (B : Set P) (q : Q) (f : ChainMap P Q) (h : PolyPoint P → PolyPoint Q)
    (hf : ∀ x, ∀ p ∈ x.weights.support, f p ∈ (h x).weights.support)
    (hh : ∀ p ∈ B, h (vertex p) = vertex q) : Fixed B q f := by
  intro p hp
  have hm := hf (vertex p) p (by simp only [vertex_support,Finset.mem_singleton])
  rw [hh p hp,vertex_support,Finset.mem_singleton] at hm
  exact hm

end Thomason.GeometricRecognition.Contiguity

end

noncomputable section
universe u v w z
open PartialOrder CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition.Contiguity
open PolyPoint Mesh Approximation
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

local instance relativeContiguityFaceDecidableEq_r9c6958_1 : DecidableEq Q := Classical.decEq Q
lemma upper_fixed (B : Set P) (q : Q) (f g : ChainMap P Q) (h : Contiguous f g)
    (hf : Fixed B q f) (hg : Fixed B q g) (s : relativeFaceSet B) : upperMap f g h s.val = q := by
  have hm := greatest_mem (unionChain f g h s.val)
  rcases Finset.mem_union.mp hm with hm | hm
  · obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hm
    exact he.symm.trans (hf p (s.property p hp))
  · obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hm
    exact he.symm.trans (hg p (s.property p hp))

def BasedRelated {A X Y : SSet.{u}} (i : A ⟶ X) (c : A ⟶ Y) (f g : X ⟶ Y) : Prop :=
  Relation.EqvGen (BasedHomotopy i c) f g

lemma orderHomotopy_fixed {A : Type u} [PartialOrder A] (i : A →o P)
    (f g : P →o Q) (h : ∀ p, f p ≤ g p) (q : Q)
    (hf : ∀ a, f (i a) = q) (hg : ∀ a, g (i a) = q) :
    (nerveMap i.toFunctor ▷ Δ[1]) ≫ (HornSubdivision.orderHomotopy f g h).h =
      fst _ _ ≫ nerveMap (constantOrder A q).toFunctor := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro x
  exact CategoryTheory.Functor.ext (fun j => by
    change (if (SSet.stdSimplex.objEquiv x.2).toOrderHom j = 0
      then f (i (x.1.obj j)) else g (i (x.1.obj j))) = q
    split_ifs <;> [exact hf _; exact hg _])

end Thomason.GeometricRecognition.Contiguity

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_RelativeRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative Representation. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision

lemma unmate_homotopy_relative {A B K : SSet.{u}} [SSet.KanComplex K]
    (i : B ⟶ A) [Mono i] {f g : A ⟶ SSet.ex.obj K}
    (H : SSet.Homotopy f g) (hH : i ▷ Δ[1] ≫ H.h = fst B Δ[1] ≫ i ≫ g) :
    ∃ G : SSet.Homotopy ((SSet.sdExAdjunction.homEquiv A K).symm f)
      ((SSet.sdExAdjunction.homEquiv A K).symm g),
      SSet.sd.map i ▷ Δ[1] ≫ G.h = fst (SSet.sd.obj B) Δ[1] ≫
        SSet.sd.map i ≫ (SSet.sdExAdjunction.homEquiv A K).symm g := by
  let s := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i
    (SSet.stdSimplex.δ (n := 0) (0 : Fin 2))
  have hinl : s.inl ≫ s.ι = A ◁ SSet.stdSimplex.δ (n := 0) 0 := s.inl_ι
  have hinr : s.inr ≫ s.ι = i ▷ Δ[1] := s.inr_ι
  have heq : s.ι ≫ H.h = s.ι ≫ fst A Δ[1] ≫ g := by
    apply s.isPushout.hom_ext
    · rw [← Category.assoc,hinl,← Category.assoc,hinl]
      apply (cancel_epi (SimplicialCylinder.zeroFactorIso A).hom).mp
      rw [← Category.assoc,CoherentGluing.zeroFactor_one,H.h₁,
        ← Category.assoc,CoherentGluing.zeroFactor_one,SSet.ι₁_fst_assoc]
    · rw [← Category.assoc,hinr,← Category.assoc,hinr,hH,whiskerRight_fst_assoc]
  let h := (SSet.sdExAdjunction.homEquiv (A ⊗ Δ[1]) K).symm H.h
  let g' := (SSet.sdExAdjunction.homEquiv A K).symm g
  let p := SSet.sd.map (fst A Δ[1])
  have heq' : SSet.sd.map s.ι ≫ h = SSet.sd.map s.ι ≫ p ≫ g' := by
    dsimp only [h,p,g']
    rw [← SSet.sdExAdjunction.homEquiv_naturality_left_symm]
    exact (SSet.sdExAdjunction.homEquiv_naturality_left_symm
      (show s.pt ⟶ A ⊗ Δ[1] from s.ι) H.h).symm.trans
        ((congrArg (SSet.sdExAdjunction.homEquiv s.pt K).symm heq).trans
          (SSet.sdExAdjunction.homEquiv_naturality_left_symm
            (show s.pt ⟶ A ⊗ Δ[1] from s.ι) (fst A Δ[1] ≫ g)))
  obtain ⟨R,hR⟩ := homotopy_of_anodyne_eq_relative (SSet.sd.map s.ι)
    (HornSubdivision.sd_preserves_anodyne _
      (SSet.anodyneExtensions_pushoutObjObjι s (SimplicialCylinder.delta_one_anodyne 0)))
    h (p ≫ g') heq'
  have h₀ : SSet.sd.map (SSet.ι₀ (X := A)) ≫ h =
      (SSet.sdExAdjunction.homEquiv A K).symm f := by
    dsimp only [h]
    rw [← SSet.sdExAdjunction.homEquiv_naturality_left_symm,H.h₀]
  have hp : SSet.sd.map (SSet.ι₀ (X := A)) ≫ p = 𝟙 _ := by
    dsimp only [p]
    rw [← Functor.map_comp,SSet.ι₀_fst,CategoryTheory.Functor.map_id]
  let G := homotopy_pre (SSet.sd.map (SSet.ι₀ (X := A))) R
  let G' : SSet.Homotopy ((SSet.sdExAdjunction.homEquiv A K).symm f) g' :=
    CoherentGluing.toHomotopy G.h (by simpa only [h₀] using G.h₀)
      (by simpa only [← Category.assoc,hp,Category.id_comp] using G.h₁)
  refine ⟨G',?_⟩
  change SSet.sd.map i ▷ Δ[1] ≫ SSet.sd.map SSet.ι₀ ▷ Δ[1] ≫ R.h = _
  rw [← comp_whiskerRight_assoc,← Functor.map_comp,← SSet.ι₀_comp,← hinr,
    ← Category.assoc,Functor.map_comp,comp_whiskerRight_assoc,hR,whiskerRight_fst_assoc]
  rw [← Category.assoc (SSet.sd.map _) (SSet.sd.map _),← Functor.map_comp,
    Category.assoc,hinr,SSet.ι₀_comp,Functor.map_comp,Category.assoc,h₀]
  have hfg : i ≫ f = i ≫ g := by
    have hh := congrArg (fun t => SSet.ι₀ ≫ t) hH
    simpa only [SSet.ι₀_comp_assoc,H.h₀,SSet.ι₀_fst_assoc] using hh
  rw [← SSet.sdExAdjunction.homEquiv_naturality_left_symm,
    ← SSet.sdExAdjunction.homEquiv_naturality_left_symm,hfg]
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision

lemma stage_unmate_boundary {A B X : SSet.{u}} (i : B ⟶ A) (n : ℕ)
    (t : A ⟶ exStage X (n+1)) (k : B ⟶ exStage X n)
    (ht : i ≫ t = k ≫ exComparison.app (exStage X n)) :
    SSet.sd.map i ≫ (SSet.sdExAdjunction.homEquiv A (exStage X n)).symm t =
      lastVertex.app B ≫ k := by
  rw [← SSet.sdExAdjunction.homEquiv_naturality_left_symm,ht,← mate_lastVertex,
    Equiv.symm_apply_apply]

end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh

lemma based_homotopy_pre {A B A' B' K : SSet.{u}}
    (i : B ⟶ A) (j : B' ⟶ A') (f : A' ⟶ A) (g : B' ⟶ B)
    (w : j ≫ f = g ≫ i) (z : B ⟶ K) {a b : A ⟶ K}
    (H : BasedHomotopy i z a b) : BasedHomotopy j (g ≫ z) (f ≫ a) (f ≫ b) := by
  obtain ⟨H,hH⟩ := H
  refine ⟨homotopy_pre f H,?_⟩
  change j ▷ Δ[1] ≫ f ▷ Δ[1] ≫ H.h = _
  rw [← comp_whiskerRight_assoc,w,comp_whiskerRight_assoc,hH,whiskerRight_fst_assoc]

attribute [instance] PairRefinement.finiteR PairRefinement.finiteS

def PairRefinement.identity (P B : PartOrd.{u}) [Finite P] [Finite B]
    (i : B →o P) (hi : Function.Injective i) : PairRefinement P B i where
  R := P
  S := B
  finiteR := inferInstance
  finiteS := inferInstance
  j := i
  injective := hi
  l := OrderHom.id
  k := OrderHom.id
  square := rfl
  local_l := by rw [nerveOrderMap_id]; exact local_iso _
  local_k := by rw [nerveOrderMap_id]; exact local_iso _
  home := Homeomorph.refl _
  homeB := Homeomorph.refl _
  natural := fun _ => rfl

lemma exSequence_zero_succ (X : SSet.{u}) (n : ℕ) :
    (exSequence X).map (homOfLE (Nat.zero_le (n+1))) =
      (exSequence X).map (homOfLE (Nat.zero_le n)) ≫ exComparison.app (exStage X n) := by
  have h := (exSequence X).map_comp (homOfLE (Nat.zero_le n)) (homOfLE (Nat.le_succ n))
  erw [Functor.ofSequence_map_homOfLE_succ] at h
  exact h
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity HornSubdivision

lemma edge_homotopy_const {K : SSet.{u}} {x y : K _⦋0⦌} (e : K.Edge x y) :
    Nonempty (SSet.Homotopy (SSet.const (X := Δ[0]) x) (SSet.const y)) := by
  refine ⟨CoherentGluing.toHomotopy (snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm e.edge) ?_ ?_⟩
  · rw [SSet.ι₀_snd_assoc,← SSet.stdSimplex.δ_one_eq_const,
      SSet.stdSimplex.δ_comp_yonedaEquiv_symm,e.src_eq,SSet.yonedaEquiv_symm_zero]
  · rw [SSet.ι₁_snd_assoc,← SSet.stdSimplex.δ_zero_eq_const,
      SSet.stdSimplex.δ_comp_yonedaEquiv_symm,e.tgt_eq,SSet.yonedaEquiv_symm_zero]

lemma component_homotopic_const {K : SSet.{u}} {x y : K _⦋0⦌}
    (h : SSet.π₀.mk x = SSet.π₀.mk y) :
    Homotopic (SSet.const (X := Δ[0]) x) (SSet.const y) := by
  have h' := (SSet.π₀.mk_eq_mk_iff x y).mp h
  clear h
  induction h' with
  | rel _ _ h =>
    obtain ⟨e⟩ := h
    obtain ⟨H⟩ := edge_homotopy_const e
    exact Relation.EqvGen.rel _ _ ⟨H⟩
  | refl => exact homotopic_refl _
  | symm _ _ _ ih => exact homotopic_symm ih
  | trans _ _ _ _ _ ih ih' => exact homotopic_trans ih ih'

lemma homotopy_extension {A B K : SSet.{u}} [SSet.KanComplex K]
    (i : A ⟶ B) [Mono i] (f : B ⟶ K) {a : A ⟶ K}
    (H : SSet.Homotopy (i ≫ f) a) :
    ∃ g : B ⟶ K, ∃ G : SSet.Homotopy f g, i ≫ g = a ∧ i ▷ Δ[1] ≫ G.h = H.h := by
  have hp : simplicialFibrations (terminal.from K) := by
    change SSet.modelCategoryQuillen.J.rlp (terminal.from K)
    rw [← SSet.modelCategoryQuillen.fibrations_eq,← HomotopicalAlgebra.fibration_iff]
    infer_instance
  obtain ⟨Q,hQ,h₀,_⟩ := cylinder_lift i (terminal.from K) hp 1 f H.h (terminal.from _)
    (by rw [endpoint_zero,H.h₀]) (by subsingleton) (by subsingleton)
  refine ⟨SSet.ι₁ ≫ Q,CoherentGluing.toHomotopy Q ?_ rfl,?_,hQ⟩
  · simpa only [endpoint_zero] using h₀
  · rw [← SSet.ι₁_comp_assoc,hQ,H.h₁]

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
open CategoryTheory Limits Simplicial PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

lemma based_homotopy_boundary {A B K : SSet.{u}} (i : B ⟶ A) (z : B ⟶ K)
    {a b : A ⟶ K} (H : BasedHomotopy i z a b) : i ≫ a = z ∧ i ≫ b = z := by
  obtain ⟨H,hH⟩ := H
  constructor
  · have hh := congrArg (fun q => SSet.ι₀ ≫ q) hH
    simpa only [SSet.ι₀_comp_assoc,H.h₀,SSet.ι₀_fst_assoc] using hh
  · have hh := congrArg (fun q => SSet.ι₁ ≫ q) hH
    simpa only [SSet.ι₁_comp_assoc,H.h₁,SSet.ι₁_fst_assoc] using hh

lemma based_related_boundary {A B K : SSet.{u}} (i : B ⟶ A) (z : B ⟶ K)
    {a b : A ⟶ K} (H : BasedRelated i z a b) : i ≫ a = i ≫ b := by
  induction H with
  | rel a b H => exact (based_homotopy_boundary i z H).1.trans (based_homotopy_boundary i z H).2.symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

lemma based_related_homotopy {A B K : SSet.{u}} [SSet.KanComplex K]
    (i : B ⟶ A) [Mono i] (z : B ⟶ K) {a b : A ⟶ K}
    (H : BasedRelated i z a b) : i ≫ a = z → BasedHomotopy i z a b := by
  induction H with
  | rel a b H => exact fun _ => H
  | refl a => exact fun ha => based_homotopy_refl i z a ha
  | symm a b H ih =>
    intro hb
    exact based_homotopy_symm i z (ih ((based_related_boundary i z H).trans hb))
  | trans a b c Hab Hbc ih ih' =>
    intro ha
    exact based_homotopy_trans i z (ih ha) (ih' ((based_related_boundary i z Hab).symm.trans ha))

lemma based_related_pre {A B A' B' K : SSet.{u}}
    (i : B ⟶ A) (j : B' ⟶ A') (f : A' ⟶ A) (g : B' ⟶ B)
    (w : j ≫ f = g ≫ i) (z : B ⟶ K) {a b : A ⟶ K}
    (H : BasedRelated i z a b) : BasedRelated j (g ≫ z) (f ≫ a) (f ≫ b) := by
  induction H with
  | rel a b H => exact Relation.EqvGen.rel _ _ (based_homotopy_pre i j f g w z H)
  | refl a => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'

lemma based_related_post {A B K L : SSet.{u}} (i : B ⟶ A) (z : B ⟶ K)
    {a b : A ⟶ K} (H : BasedRelated i z a b) (f : K ⟶ L) :
    BasedRelated i (z ≫ f) (a ≫ f) (b ≫ f) := by
  induction H with
  | rel a b H => exact Relation.EqvGen.rel _ _ (based_homotopy_post i z H f)
  | refl a => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'

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

lemma cubical_relative_cancel {A : Type u} {X : Type v} {Y : Type w}
    [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (e : A ≃ₜ (Fin (n+1) → unitInterval)) (S : Set A)
    (hS : ∀ a, a ∈ S ↔ e a ∈ Cube.boundary (Fin (n+1)))
    (r : C(X,Y)) (hr : WeakHomotopy.Equivalence r) (x : X)
    (f g : C(A,X)) (hf : ∀ a ∈ S, f a = x) (hg : ∀ a ∈ S, g a = x)
    (H : (r.comp f).HomotopyRel (r.comp g) S) :
    Nonempty (f.HomotopyRel g S) := by
  let f' : GenLoop (Fin (n+1)) X x := ⟨f.comp ⟨e.symm,e.symm.continuous⟩,by
    intro a ha
    exact hf _ ((hS _).mpr (by simpa using ha))⟩
  let g' : GenLoop (Fin (n+1)) X x := ⟨g.comp ⟨e.symm,e.symm.continuous⟩,by
    intro a ha
    exact hg _ ((hS _).mpr (by simpa using ha))⟩
  have hfg : WeakHomotopy.groupMap (Fin (n+1)) r x ⟦f'⟧ =
      WeakHomotopy.groupMap (Fin (n+1)) r x ⟦g'⟧ := by
    apply Quotient.sound
    exact ⟨top_homotopy_rel_pre H ⟨e.symm,e.symm.continuous⟩ (Cube.boundary (Fin (n+1)))
      (fun a ha => (hS _).mpr (by simpa using ha))⟩
  obtain ⟨G⟩ : GenLoop.Homotopic f' g' := Quotient.exact ((hr.2 n x).1 hfg)
  have hh := top_homotopy_rel_pre G ⟨e,e.continuous⟩ S (fun a ha => (hS a).mp ha)
  refine ⟨hh.cast ?_ ?_⟩ <;> ext a <;> simp [f',g']

def CubicalPair.refine {P B : PartOrd.{u}} {i : B →o P} {n : ℕ}
    (c : CubicalPair P B i n) (d : PairRefinement P B i) : CubicalPair d.R d.S d.j n where
  home := d.home.trans c.home
  boundary := by
    intro a
    change _ ↔ c.home (d.home a) ∈ _
    rw [← c.boundary]
    constructor
    · rintro ⟨b,rfl⟩
      exact ⟨d.homeB b,(d.natural b).symm⟩
    · rintro ⟨b,hb⟩
      obtain ⟨b',rfl⟩ := d.homeB.surjective b
      refine ⟨b',d.home.injective ?_⟩
      exact (d.natural b').trans hb
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

abbrev cubeBoundary (n : ℕ) : Set (cubePoset.{u} n) :=
  Cubical.boundaryFaces (ULift.{u} (Fin (n+1)))

abbrev cubeBoundaryInclusion (n : ℕ) : PartOrd.of (cubeBoundary.{u} n) →o cubePoset.{u} n :=
  inclusion (cubeBoundary n)

def actualCubicalPair (n : ℕ) :
    CubicalPair (cubePoset.{u} n) (PartOrd.of (cubeBoundary n)) (cubeBoundaryInclusion n) n where
  home := Cubical.pairCubeHomeomorph.trans
    (Homeomorph.piCongrLeft (Y := fun _ : Fin (n+1) => unitInterval) Equiv.ulift)
  boundary := by
    intro a
    have he : (Cubical.pairCubeHomeomorph (I := ULift.{u} (Fin (n+1)))) a ∈
        Cube.boundary (ULift.{u} (Fin (n+1))) ↔
      (Homeomorph.piCongrLeft (Y := fun _ : Fin (n+1) => unitInterval) Equiv.ulift)
        (Cubical.pairCubeHomeomorph a) ∈ Cube.boundary (Fin (n+1)) := by
      constructor
      · rintro ⟨j,hj⟩
        exact ⟨j.down,hj⟩
      · rintro ⟨j,hj⟩
        exact ⟨ULift.up j,hj⟩
    change _ ↔ (Homeomorph.piCongrLeft (Y := fun _ : Fin (n+1) => unitInterval) Equiv.ulift)
      (Cubical.pairCubeHomeomorph a) ∈ Cube.boundary (Fin (n+1))
    rw [← he]
    constructor
    · rintro ⟨b,rfl⟩
      exact (Cubical.boundaryHomeomorph b).property
    · intro ha
      obtain ⟨b,hb⟩ := Cubical.boundaryHomeomorph.surjective ⟨_,ha⟩
      exact ⟨b,Cubical.pairCubeHomeomorph.injective (congrArg Subtype.val hb)⟩

abbrev CubeMap (n : ℕ) {K : SSet.{u}} (x : K _⦋0⦌) :=
  {a : nerve (cubePoset.{u} n) ⟶ K //
    nerveMap (cubeBoundaryInclusion n).toFunctor ≫ a = SSet.const x}

instance cubeBoundary_mono (n : ℕ) : Mono (nerveMap (cubeBoundaryInclusion.{u} n).toFunctor) :=
  nerveOrderMap_mono _ Subtype.val_injective

def cubeMapSetoid (n : ℕ) {K : SSet.{u}} [SSet.KanComplex K] (x : K _⦋0⦌) :
    Setoid (CubeMap n x) where
  r a b := BasedHomotopy (nerveMap (cubeBoundaryInclusion n).toFunctor) (SSet.const x) a.val b.val
  iseqv := {
    refl := fun a => based_homotopy_refl _ _ a.val a.property
    symm := fun h => based_homotopy_symm _ _ h
    trans := fun h h' => based_homotopy_trans _ _ h h' }

abbrev CubeClasses (n : ℕ) {K : SSet.{u}} [SSet.KanComplex K] (x : K _⦋0⦌) :=
  Quotient (cubeMapSetoid n x)
end Thomason.GeometricRecognition

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SimplexBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simplex Boxes. -/

noncomputable section
universe u v w z
open Set Metric Bornology Filter
open scoped Topology BigOperators

namespace Thomason.GeometricRecognition.SimplexGeometry

def simplexChartHomeomorph (n : ℕ) : Convexity.StdSimplex ℝ (Fin (n+1)) ≃ₜ chartBody n where
  toFun x := ⟨fun i => x.weights i.succ,⟨fun i => x.weights_nonneg i.succ,by
    have h := x.total_of_fintype
    rw [Fin.sum_univ_succ] at h
    linarith [x.weights_nonneg 0]⟩⟩
  invFun x := {
    weights := Finsupp.equivFunOnFinite.symm (Fin.cons (1-∑i,x.val i) x.val)
    nonneg := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact sub_nonneg.mpr x.property.2
      · exact x.property.1 j
    total := by
      rw [Finsupp.sum_fintype _ _ (by simp)]
      change ∑ i, Fin.cons (1-∑j,x.val j) x.val i = 1
      simp [Fin.sum_univ_succ] }
  left_inv x := by
    apply Convexity.StdSimplex.ext
    apply Finsupp.ext
    intro i
    change Fin.cons (α := fun _ => ℝ) (1-∑index : Fin n,x.weights index.succ)
      (fun index : Fin n => x.weights index.succ) i = x.weights i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      have h := x.total_of_fintype
      rw [Fin.sum_univ_succ] at h
      linarith
    · simp only [Fin.cons_succ]
  right_inv x := by ext i; rfl
  continuous_toFun := (continuous_pi fun index : Fin n =>
    Convexity.StdSimplex.continuous_weights_apply ℝ index.succ).subtype_mk _
  continuous_invFun := by
    rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).continuous_iff]
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Continuous (fun x : chartBody n => 1-∑j,x.val j)
      fun_prop
    · exact (continuous_apply j).comp continuous_subtype_val

def simplexCubeHomeomorph (n : ℕ) : Convexity.StdSimplex ℝ (Fin (n+1)) ≃ₜ (Fin n → unitInterval) :=
  (simplexChartHomeomorph n).trans (((chartCubeAmbient n).image (chartBody n)).trans
    ((Homeomorph.setCongr (chartCubeAmbient_spec n).1).trans (cubeBodyHomeomorph n)))

lemma simplexCubeHomeomorph_boundary (n : ℕ) [Nonempty (Fin n)]
    (x : Convexity.StdSimplex ℝ (Fin (n+1))) :
    (∃ i, x.weights i = 0) ↔ simplexCubeHomeomorph n x ∈ Cube.boundary (Fin n) := by
  have hc : (∃ i, x.weights i = 0) ↔
      (simplexChartHomeomorph n x).val ∈ frontier (chartBody n) := by
    rw [mem_frontier_chartBody]
    constructor
    · rintro ⟨i,hi⟩
      refine Fin.cases ?_ (fun j hj => ?_) i hi
      · intro hzero
        right
        have h := x.total_of_fintype
        rw [Fin.sum_univ_succ,hzero,zero_add] at h
        exact h
      · exact Or.inl ⟨j,hj⟩
    · rintro (⟨i,hi⟩|hs)
      · exact ⟨i.succ,hi⟩
      · refine ⟨0,?_⟩
        have h := x.total_of_fintype
        rw [Fin.sum_univ_succ] at h
        change ∑ i : Fin n, x.weights i.succ = 1 at hs
        linarith
  rw [hc]
  let y : cubeBody n := ⟨chartCubeAmbient n (simplexChartHomeomorph n x).val,by
    rw [← (chartCubeAmbient_spec n).1]
    exact ⟨_,(simplexChartHomeomorph n x).property,rfl⟩⟩
  have he : (simplexChartHomeomorph n x).val ∈ frontier (chartBody n) ↔
      y.val ∈ frontier (cubeBody n) := by
    rw [← (chartCubeAmbient_spec n).2]
    exact ((chartCubeAmbient n).injective.mem_set_image).symm
  rw [he,mem_frontier_cubeBody]
  change (∃i,y.val i=0 ∨ y.val i=1) ↔ _
  constructor
  · rintro ⟨i,hi|hi⟩
    · exact ⟨i,Or.inl (Subtype.ext hi)⟩
    · exact ⟨i,Or.inr (Subtype.ext hi)⟩
  · rintro ⟨i,hi|hi⟩
    · exact ⟨i,Or.inl (congrArg Subtype.val hi)⟩
    · exact ⟨i,Or.inr (congrArg Subtype.val hi)⟩
end Thomason.GeometricRecognition.SimplexGeometry

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

def simplexPolyCoordinates (m : ℕ) (x : PolyPoint (simplexVertices.{u} m)) :
    Convexity.StdSimplex ℝ (Fin (m+1)) where
  weights := Finsupp.equivFunOnFinite.symm (fun i => x.weights (ULift.up i))
  nonneg i := x.nonneg (ULift.up i)
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change ∑ i : Fin (m+1), x.weights (ULift.up i) = 1
    calc
      ∑ i, x.weights (ULift.up i) = ∑ i : ULift.{u} (Fin (m+1)), x.weights i :=
        Equiv.sum_comp Equiv.ulift.symm x.weights
      _ = 1 := (Finsupp.sum_fintype x.weights (fun _ r => r) (fun _ => rfl)).symm.trans x.total

lemma continuous_simplexPolyCoordinates (m : ℕ) : Continuous (simplexPolyCoordinates.{u} m) := by
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).continuous_iff]
  exact continuous_pi fun i => continuous_weights (ULift.up i)

def simplexPolyHomeomorph (m : ℕ) : PolyPoint (simplexVertices.{u} m) ≃ₜ Convexity.StdSimplex ℝ (Fin (m+1)) where
  toFun := simplexPolyCoordinates m
  invFun := eval (simplexVertexOrder m)
  left_inv x := by
    apply PolyPoint.ext
    ext i
    exact evalWeights_apply_image (simplexVertexOrder m) ULift.up_injective _ i.down
  right_inv x := by
    apply Convexity.StdSimplex.ext
    apply Finsupp.ext
    intro i
    exact evalWeights_apply_image (simplexVertexOrder m) ULift.up_injective _ i
  continuous_toFun := continuous_simplexPolyCoordinates m
  continuous_invFun := continuous_eval (simplexVertexOrder m)

end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

abbrev orderedBoundary (m : ℕ) := orderedSimplexSubcomplex (SSet.boundary.{u} m)

lemma mem_orderedBoundary (m k : ℕ) (s : (nerve (simplexVertices.{u} m)) _⦋k⦌) :
    s ∈ (orderedBoundary m).obj _ ↔ (simplexChain s).finset ≠ Finset.univ := by
  classical
  have hmem : s ∈ (orderedBoundary m).obj _ ↔
      (SSet.stdSimplex.isoNerve m).inv.app _ s ∈ (SSet.boundary m).obj _ := by
    change (∃ x : (SSet.boundary m : SSet.{u}) _⦋k⦌,
      (SSet.stdSimplex.isoNerve m).hom.app _ x.val = s) ↔ _
    constructor
    · rintro ⟨x,rfl⟩
      simp <;> exact x.2
    · intro hs
      exact ⟨⟨_,hs⟩,by simp⟩
  rw [hmem,SSet.mem_boundary_iff_notMem_range]
  constructor
  · rintro ⟨i,hi⟩ he
    have hh : ULift.up i ∈ (simplexChain s).finset := he ▸ Finset.mem_univ _
    obtain ⟨j,hj⟩ := (mem_simplexChain s _).mp hh
    apply hi
    exact ⟨j,congrArg ULift.down hj⟩
  · intro h
    have hex : ∃ i, i ∉ (simplexChain s).finset := by
      by_contra! hh
      exact h (Finset.eq_univ_of_forall hh)
    obtain ⟨i,hi⟩ := hex
    refine ⟨i.down,?_⟩
    rintro ⟨j,hj⟩
    apply hi
    apply (mem_simplexChain s _).mpr
    exact ⟨j,ULift.ext _ _ hj⟩

lemma allowed_orderedBoundary (m : ℕ) (c : simplexPoset.{u} m) :
    (∃ s : (orderedBoundary m : SSet).N,
      simplexChain (subcomplexN (orderedBoundary m) s).simplex = c) ↔ c ∈ simplexBoundary m := by
  constructor
  · rintro ⟨s,rfl⟩
    exact (mem_orderedBoundary m s.dim s.simplex.val).mp s.simplex.property
  · intro hc
    let t := chainSimplex c
    have ht : t.simplex ∈ (orderedBoundary m).obj _ := by
      rw [mem_orderedBoundary,simplexChain_chainSimplex]
      exact hc
    let s : (orderedBoundary m : SSet).N :=
      SSet.N.mk ⟨t.simplex,ht⟩ (((orderedBoundary m).mem_nonDegenerate_iff _).mpr t.nonDegenerate)
    exact ⟨s,simplexChain_chainSimplex c⟩

def boundaryFaceOrderIso (m : ℕ) : AllowedChains (orderedBoundary.{u} m) ≃o simplexBoundary m where
  toFun c := ⟨c.val,(allowed_orderedBoundary m c.val).mp c.property⟩
  invFun c := ⟨c.val,(allowed_orderedBoundary m c.val).mpr c.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation HornSubdivision

def sdBoundaryFacesIso (m : ℕ) : SSet.sd.obj (SSet.boundary.{u} m : SSet) ≅
    nerve (simplexBoundary.{u} m) :=
  sdSimplexSubcomplexIso (SSet.boundary m) ≪≫ PartOrd.nerveFunctor.mapIso
    (PartOrd.Iso.mk (α := PartOrd.of (AllowedChains (orderedBoundary m)))
      (β := PartOrd.of (simplexBoundary m)) (boundaryFaceOrderIso m))

lemma sd_boundary_square (m : ℕ) :
    SSet.sd.map (SSet.boundary.{u} m).ι ≫ (sdSimplexIso m).hom =
      (sdBoundaryFacesIso m).hom ≫ nerveMap (inclusion (simplexBoundary m)).toFunctor := by
  rw [sdSimplexSubcomplexIso_naturality]
  rfl

def simplexPairProjection (m : ℕ) : nerve (simplexPoset.{u} m) ⟶ Δ[m] :=
  (sdSimplexIso m).inv ≫ lastVertex.app Δ[m]
def simplexBoundaryProjection (m : ℕ) : nerve (simplexBoundary.{u} m) ⟶ (SSet.boundary m : SSet) :=
  (sdBoundaryFacesIso m).inv ≫ lastVertex.app (SSet.boundary m : SSet)

lemma simplex_pair_square (m : ℕ) :
    nerveMap (inclusion (simplexBoundary.{u} m)).toFunctor ≫ simplexPairProjection m =
      simplexBoundaryProjection m ≫ (SSet.boundary m).ι := by
  apply (cancel_epi (sdBoundaryFacesIso m).hom).mp
  simp only [simplexPairProjection,simplexBoundaryProjection,← Category.assoc]
  rw [← sd_boundary_square]
  simp only [Category.assoc,Iso.hom_inv_id_assoc]
  exact lastVertex.naturality (SSet.boundary m).ι

lemma simplexPairProjection_local (m : ℕ) : Local (simplexPairProjection.{u} m) :=
  local_comp (local_iso _) (lastVertex_local _)
lemma simplexBoundaryProjection_local (m : ℕ) : Local (simplexBoundaryProjection.{u} m) :=
  local_comp (local_iso _) (lastVertex_local _)

instance simplexBoundaryInclusion_mono (m : ℕ) :
    Mono (nerveMap (inclusion (simplexBoundary.{u} m)).toFunctor) :=
  nerveOrderMap_mono _ Subtype.val_injective
end Thomason.GeometricRecognition

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_FiberRecognition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fiber Recognition. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal HornSubdivision KanPath Contiguity

lemma nullhomotopy_boundary_of_face {K : SSet.{u}}
    (n : ℕ) (x : K _⦋0⦌) (b : (∂Δ[n+1] : SSet.{u}) ⟶ K)
    (hb : hornInBoundary n ≫ b = SSet.const x)
    (H : BasedHomotopy (SSet.boundary n).ι (SSet.const x)
      (SSet.boundary.ι (0 : Fin (n+2)) ≫ b) (SSet.const x)) :
    Nonempty (SSet.Homotopy b (SSet.const x)) := by
  obtain ⟨H,hH⟩ := H
  let sq := boundary_horn_isPushout.{u} n
  have w : (SSet.boundary n).ι ≫ curryR H.h =
      boundaryInHorn n ≫ curryR (SSet.const x) := by
    apply uncurryR_injective
    simp only [uncurryR_pre,uncurryR_curryR,hH,SSet.comp_const]
  let g := sq.desc (curryR H.h) (curryR (SSet.const x)) w
  have h₀ : g ≫ eval₀ K = b := by
    apply sq.hom_ext
    · rw [← Category.assoc,sq.inl_desc,comp_eval₀,uncurryR_curryR,H.h₀]
    · rw [← Category.assoc,sq.inr_desc,comp_eval₀,uncurryR_curryR,SSet.comp_const,hb]
  have h₁ : g ≫ eval₁ K = SSet.const x := by
    apply sq.hom_ext
    · rw [← Category.assoc,sq.inl_desc,comp_eval₁,uncurryR_curryR,H.h₁,SSet.comp_const]
    · rw [← Category.assoc,sq.inr_desc,comp_eval₁,uncurryR_curryR,SSet.comp_const,SSet.comp_const]
  exact ⟨CoherentGluing.toHomotopy (uncurryR g)
    (by rw [← comp_eval₀,h₀]) (by rw [← comp_eval₁,h₁])⟩
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal HornSubdivision KanPath Contiguity

lemma based_homotopy_zero {K : SSet.{u}} {a b : Δ[0] ⟶ K}
    (x : K _⦋0⦌) (H : SSet.Homotopy a b) :
    BasedHomotopy (SSet.boundary 0).ι (SSet.const x) a b := by
  refine ⟨H,?_⟩
  ext n ⟨⟨t,ht⟩,s⟩
  simp at ht

end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open SSet.modelCategoryQuillen
open LastVertexProof KanHomotopy KanLocal KanPath HornSubdivision Contiguity

lemma strictFiber_homotopy {A K L : SSet.{u}} (p : K ⟶ L) (y : L _⦋0⦌)
    {a b : A ⟶ (strictFiber p y : SSet)}
    (H : SSet.Homotopy (a ≫ (strictFiber p y).ι) (b ≫ (strictFiber p y).ι))
    (hH : H.h ≫ p = SSet.const y) : Nonempty (SSet.Homotopy a b) := by
  refine ⟨CoherentGluing.toHomotopy (strictFiberLift p y H.h hH) ?_ ?_⟩
  · apply (cancel_mono (strictFiber p y).ι).mp
    rw [Category.assoc,strictFiberLift_ι,H.h₀]
  · apply (cancel_mono (strictFiber p y).ι).mp
    rw [Category.assoc,strictFiberLift_ι,H.h₁]
end Thomason.GeometricRecognition

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_DimensionOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dimension One. -/

noncomputable section
universe u v w z


namespace Thomason.BoundaryProperness
open CategoryTheory Limits Simplicial PartialOrder
open AttachmentComparison Attachments HornAttachments SubdividedUnit KanLocal
attribute [-instance] CategoryTheory.Sigma.sigma

attribute [instance] PosetAttachment.order

variable {I : Type u} (d : I → PosetAttachment.{u})

def sumData : PosetAttachment.{u} where
  B := Σ i, (d i).B
  order := inferInstance
  A := DependentPosets.old (fun i => (d i).A)
  lower := DependentPosets.old_lower _ (fun i => (d i).lower)
  retraction := DependentPosets.oldRetraction _ (fun i => (d i).retraction)
  retract := DependentPosets.oldRetraction_retract _ _ (fun i => (d i).retract)
  adjunction := DependentPosets.oldRetraction_adjunction _ _ (fun i => (d i).adjunction)

end Thomason.BoundaryProperness

end

noncomputable section
universe u v w z


namespace Thomason.BoundaryProperness
open CategoryTheory Limits Simplicial
open AttachmentComparison Attachments HornAttachments SubdividedUnit KanLocal
attribute [-instance] CategoryTheory.Sigma.sigma

end Thomason.BoundaryProperness

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_Couniversality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Couniversality. -/

noncomputable section
universe u v w z


namespace Thomason.FilteredWeak
open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open KanPath LastVertexProof KanHomotopy HornSubdivision SSet.modelCategoryQuillen

lemma eval₀_rlp (B : SSet.{u}) [SSet.KanComplex B] :
    (MorphismProperty.monomorphisms SSet).rlp (eval₀ B) := by
  intro D E i hi
  let : Mono i := hi
  constructor
  intro x y sq
  have hp : simplicialFibrations (terminal.from B) := by
    change J.rlp _
    rw [← fibrations_eq, ← HomotopicalAlgebra.fibration_iff]
    infer_instance
  obtain ⟨Q,hQ,h₀,_⟩ := cylinder_lift i (terminal.from B) hp 1 y
    (uncurryR x) (terminal.from _)
    (by rw [endpoint_zero, ← comp_eval₀]; exact sq.w)
    (by subsingleton) (by subsingleton)
  refine ⟨⟨{l := curryR Q, fac_left := ?_, fac_right := ?_}⟩⟩
  · apply uncurryR_injective
    rw [uncurryR_pre, uncurryR_curryR, hQ]
  · rw [comp_eval₀, uncurryR_curryR]
    simpa only [endpoint_zero] using h₀

lemma path_projection_rlp {A B : SSet.{u}} [SSet.KanComplex B] (f : A ⟶ B) :
    I.rlp (pullback.fst f (eval₀ B)) := by
  rw [← SSet.rlp_monomorphisms]
  exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback f (eval₀ B)).flip (eval₀_rlp B)

@[simp] lemma path_map_id {A B : SSet.{u}} (f : A ⟶ B)
    (h : (𝟙 A) ≫ f = f ≫ (𝟙 B)) :
    KanPath.map (𝟙 A) (𝟙 B) h = 𝟙 (MappingPath f) := by
  apply pullback.hom_ext <;> simp

lemma const_natural {A B : SSet.{u}} (f : A ⟶ B) :
    const A ≫ (ihom Δ[1]).map f = f ≫ const B := by
  apply uncurryR_injective
  rw [uncurryR_post, uncurryR_pre]
  simp only [const, uncurryR_curryR, whiskerRight_fst]

@[reassoc] lemma path_map_left {A₁ A₀ B₁ B₀ : SSet.{u}}
    {f₁ : A₁ ⟶ B₁} {f₀ : A₀ ⟶ B₀}
    (a : A₁ ⟶ A₀) (b : B₁ ⟶ B₀) (h : a ≫ f₀ = f₁ ≫ b) :
    left f₁ ≫ KanPath.map a b h = a ≫ left f₀ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, map_fst, left, pullback.lift_fst_assoc,
      pullback.lift_fst, Category.id_comp, Category.comp_id]
  · simp only [Category.assoc, map_snd, left, pullback.lift_snd_assoc, pullback.lift_snd]
    rw [const_natural, ← Category.assoc, ← h, Category.assoc]

def pathDiagram {J : Type u} [Category.{u} J]
    {X Y : J ⥤ SSet.{u}} (p : X ⟶ Y) : J ⥤ SSet.{u} where
  obj j := MappingPath (p.app j)
  map f := KanPath.map (X.map f) (Y.map f) (p.naturality f)
  map_id j := by
    apply pullback.hom_ext <;> simp
  map_comp f g := by
    apply pullback.hom_ext
    · simp
    · simp [CategoryTheory.Functor.map_comp]

def pathProjection {J : Type u} [Category.{u} J]
    {X Y : J ⥤ SSet.{u}} (p : X ⟶ Y) : pathDiagram p ⟶ X where
  app j := pullback.fst (p.app j) (eval₀ (Y.obj j))
  naturality _ _ f := map_fst _ _ (p.naturality f)

def pathLeft {J : Type u} [Category.{u} J]
    {X Y : J ⥤ SSet.{u}} (p : X ⟶ Y) : X ⟶ pathDiagram p where
  app j := left (p.app j)
  naturality _ _ f := (path_map_left _ _ (p.naturality f)).symm

def pathRight {J : Type u} [Category.{u} J]
    {X Y : J ⥤ SSet.{u}} (p : X ⟶ Y) : pathDiagram p ⟶ Y where
  app j := right (p.app j)
  naturality _ _ f := map_right _ _ (p.naturality f)

@[simp] lemma path_left_projection {J : Type u} [Category.{u} J]
    {X Y : J ⥤ SSet.{u}} (p : X ⟶ Y) :
    pathLeft p ≫ pathProjection p = 𝟙 X := by
  apply NatTrans.ext
  funext j
  exact pullback.lift_fst _ _ _

@[simp] lemma path_fac {J : Type u} [Category.{u} J]
    {X Y : J ⥤ SSet.{u}} (p : X ⟶ Y) : pathLeft p ≫ pathRight p = p := by
  apply NatTrans.ext
  funext j
  exact fac _

end Thomason.FilteredWeak

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_ModelTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Model Transfer. -/

noncomputable section
universe u v w z


namespace Thomason.AbstractTransfer
open CategoryTheory Limits MorphismProperty Simplicial
open Attachments
open AttachmentComparison (upward nerve_mono_orderMap)

variable {C : Type v} [Category.{u} C]

variable {G : SSet.{u} ⥤ C} {N : C ⥤ SSet.{u}} {adj : G ⊣ N}
variable (h : PosetComparison G N adj)
include h

omit h in
lemma unit_local_of_iso {X Y : SSet.{u}} (e : X ≅ Y)
    (hX : KanLocal.Local (adj.unit.app X)) : KanLocal.Local (adj.unit.app Y) := by
  have he : adj.unit.app Y = e.inv ≫ adj.unit.app X ≫ N.map (G.map e.hom) := by
    have hn : e.hom ≫ adj.unit.app Y = adj.unit.app X ≫ N.map (G.map e.hom) :=
      adj.unit.naturality e.hom
    rw [← hn]
    simp
  rw [he]
  exact KanLocal.local_comp (KanLocal.local_iso e.inv)
    (KanLocal.local_comp hX (KanLocal.local_iso _))

open PartialOrder HornAttachments KanLocal
open SubdividedUnit (D Flags )

end Thomason.AbstractTransfer

end

noncomputable section
universe u v w z


namespace Thomason.AbstractTransfer.Horns
open CategoryTheory Limits Simplicial PartialOrder KanLocal
open AttachmentComparison (upward)
open HornAttachments
open AbstractTransfer
open TransferAcyclicity (PosetAttachment sumData)
attribute [-instance] CategoryTheory.Sigma.sigma

variable {C : Type v} [Category.{u} C] [HasColimitsOfSize.{u,u} C]
variable {G : SSet.{u} ⥤ C} {N : C ⥤ SSet.{u}} {adj : G ⊣ N}
variable [PreservesColimitsOfSize.{u,u} G]

instance instRespectsIsoAdmissible : (Admissible G).RespectsIso :=
  MorphismProperty.RespectsIso.of_respects_arrow_iso _ (by
    rintro _ _ e ⟨d,⟨a⟩⟩
    exact ⟨d,⟨a ≪≫ e⟩⟩)

section Coproducts
variable {I : Type u} (d : I → PosetAttachment.{u})

lemma coprod_inc : Limits.Sigma.map (fun i => inc G (d i).A) ≫
    (posetCoprodIso (G := G) (fun i => (d i).B)).hom =
    (oldCoprodIso (G := G) d).hom ≫ inc G (sumData d).A := by
  apply Sigma.hom_ext
  intro i
  erw [Sigma.ι_map_assoc, posetCoprodIso_ι]
  erw [← Category.assoc]
  erw [oldCoprodIso_ι]
  change G.map _ ≫ G.map _ =
    G.map _ ≫ G.map _
  erw [← Functor.map_comp, ← Functor.map_comp]
  rfl

end Coproducts

instance admissible_coproducts (I : Type u) : (Admissible G).IsStableUnderCoproductsOfShape I := by
  apply MorphismProperty.IsStableUnderCoproductsOfShape.mk
  intro X Y _ _ f hf
  choose d e using hf
  let a (i : I) : arrow G (d i) ≅ Arrow.mk (f i) := Classical.choice (e i)
  let eA := Limits.Sigma.mapIso (fun i => Arrow.leftFunc.mapIso (a i))
  let eB := Limits.Sigma.mapIso (fun i => Arrow.rightFunc.mapIso (a i))
  have h : (Limits.Sigma.map (fun i => inc G (d i).A)) ≫ eB.hom =
      eA.hom ≫ Limits.Sigma.map f := by
    change Limits.Sigma.map (fun i => inc G (d i).A) ≫
        Limits.Sigma.map (fun i => (a i).hom.right) =
      Limits.Sigma.map (fun i => (a i).hom.left) ≫ Limits.Sigma.map f
    rw [Sigma.map_comp_map, Sigma.map_comp_map]
    congr 1
    funext i
    exact (a i).hom.w.symm
  have e' : Arrow.mk (Limits.Sigma.map (fun i => inc G (d i).A)) ≅
      Arrow.mk (Limits.Sigma.map f) := Arrow.isoMk eA eB h.symm
  have e₀ : Arrow.mk (Limits.Sigma.map (fun i => inc G (d i).A)) ≅
      arrow G (sumData d) := Arrow.isoMk (oldCoprodIso (G := G) d)
        (posetCoprodIso (G := G) (fun i => (d i).B)) (coprod_inc d).symm
  exact ⟨sumData d, ⟨e₀.symm ≪≫ e'⟩⟩

instance instIsStableUnderCoproductsAdmissible : MorphismProperty.IsStableUnderCoproducts.{u} (Admissible G) where

end Thomason.AbstractTransfer.Horns

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_ProperTransfer
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

variable {C : Type v} [Category.{u} C] [HasColimitsOfSize.{u,u} C]
variable {G : SSet.{u} ⥤ C} {N : C ⥤ SSet.{u}} {adj : G ⊣ N}
variable [PreservesColimitsOfSize.{u,u} G]

instance instRespectsIsoAdmissible : (Admissible G).RespectsIso :=
  MorphismProperty.RespectsIso.of_respects_arrow_iso _ (by
    rintro _ _ e ⟨d,⟨a⟩⟩
    exact ⟨d,⟨a ≪≫ e⟩⟩)

section Coproducts
variable {I : Type u} (d : I → PosetAttachment.{u})

def posetCoprodIso (P : I → Type u) [∀ i, PartialOrder (P i)] :
    (∐ fun i => posetObj G (P i)) ≅ posetObj G (Σ i, P i) :=
  (PreservesCoproduct.iso G (fun i => nerve (P i))).symm ≪≫
    G.mapIso (DependentPosets.iso P)

def oldCoprodIso : (∐ fun i => posetObj G (d i).A) ≅ posetObj G (sumData d).A :=
  (PreservesCoproduct.iso G (fun i => nerve (d i).A)).symm ≪≫
    G.mapIso (DependentPosets.oldNerveIso (fun i => (d i).A))

@[reassoc] lemma posetCoprodIso_ι (P : I → Type u) [∀ i, PartialOrder (P i)] (i : I) :
    Sigma.ι (fun i => posetObj G (P i)) i ≫ (posetCoprodIso (G := G) P).hom =
      G.map (nerveMap (DependentPosets.incl P i).toFunctor) := by
  simp only [posetCoprodIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← Category.assoc, PreservesCoproduct.inv_hom, ι_comp_sigmaComparison, ← Functor.map_comp,
    DependentPosets.iso_hom_ι]

@[reassoc] lemma oldCoprodIso_ι (i : I) :
    Sigma.ι (fun i => posetObj G (d i).A) i ≫ (oldCoprodIso (G := G) d).hom =
      G.map (nerveMap
        ((DependentPosets.oldIso (fun i => (d i).A)).toOrderEmbedding.toOrderHom.comp
          (DependentPosets.incl (fun i => (d i).A) i)).toFunctor) := by
  simp only [oldCoprodIso, Iso.trans_hom, Iso.symm_hom]
  erw [Functor.mapIso_hom, ← Category.assoc, PreservesCoproduct.inv_hom,
    ι_comp_sigmaComparison, ← Functor.map_comp,
    DependentPosets.oldNerveIso_ι]
  rfl

lemma coprod_inc : Limits.Sigma.map (fun i => inc G (d i).A) ≫
    (posetCoprodIso (G := G) (fun i => (d i).B)).hom =
    (oldCoprodIso (G := G) d).hom ≫ inc G (sumData d).A := by
  apply Sigma.hom_ext
  intro i
  erw [Sigma.ι_map_assoc, posetCoprodIso_ι]
  erw [← Category.assoc]
  erw [oldCoprodIso_ι]
  change G.map _ ≫ G.map _ =
    G.map _ ≫ G.map _
  erw [← Functor.map_comp, ← Functor.map_comp]
  rfl

end Coproducts

instance admissible_coproducts (I : Type u) : (Admissible G).IsStableUnderCoproductsOfShape I := by
  apply MorphismProperty.IsStableUnderCoproductsOfShape.mk
  intro X Y _ _ f hf
  choose d e using hf
  let a (i : I) : arrow G (d i) ≅ Arrow.mk (f i) := Classical.choice (e i)
  let eA := Limits.Sigma.mapIso (fun i => Arrow.leftFunc.mapIso (a i))
  let eB := Limits.Sigma.mapIso (fun i => Arrow.rightFunc.mapIso (a i))
  have h : (Limits.Sigma.map (fun i => inc G (d i).A)) ≫ eB.hom =
      eA.hom ≫ Limits.Sigma.map f := by
    change Limits.Sigma.map (fun i => inc G (d i).A) ≫
        Limits.Sigma.map (fun i => (a i).hom.right) =
      Limits.Sigma.map (fun i => (a i).hom.left) ≫ Limits.Sigma.map f
    rw [Sigma.map_comp_map, Sigma.map_comp_map]
    congr 1
    funext i
    exact (a i).hom.w.symm
  have e' : Arrow.mk (Limits.Sigma.map (fun i => inc G (d i).A)) ≅
      Arrow.mk (Limits.Sigma.map f) := Arrow.isoMk eA eB h.symm
  have e₀ : Arrow.mk (Limits.Sigma.map (fun i => inc G (d i).A)) ≅
      arrow G (sumData d) := Arrow.isoMk (oldCoprodIso (G := G) d)
        (posetCoprodIso (G := G) (fun i => (d i).B)) (coprod_inc d).symm
  exact ⟨sumData d, ⟨e₀.symm ≪≫ e'⟩⟩

instance instIsStableUnderCoproductsAdmissible : MorphismProperty.IsStableUnderCoproducts.{u} (Admissible G) where

end Thomason.AbstractTransfer.Boundaries

end

noncomputable section
universe u v w z


namespace Thomason.AbstractTransfer.Boundaries
open CategoryTheory Limits MorphismProperty
open KanLocal SubdividedUnit

variable {C : Type v} [Category.{u} C] [HasColimitsOfSize.{u,u} C]
variable {G : SSet.{u} ⥤ C} {N : C ⥤ SSet.{u}} {adj : G ⊣ N}
variable [PreservesColimitsOfSize.{u,u} G] [PreservesFilteredColimitsOfSize.{u,u} N]
variable (h : PosetComparison G N adj)
include h

omit h [HasColimitsOfSize.{u,u} C] [PreservesFilteredColimitsOfSize.{u,u} N] in
lemma weak_iso {X Y : C} (f : X ⟶ Y) [IsIso f] :
    W N f := by
  change simplicialWeakEquivalences ((R N).map f)
  exact simplicialWeakEquivalences.of_isIso _

attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

end Thomason.AbstractTransfer.Boundaries

end

end OAI
end


