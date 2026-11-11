-- Prove2me | Definitions.Def_OAIQ236Ap005
-- name    : OAIQ236Ap005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T19:52:52.715208+00:00
-- url     : https://prove2.me/theorems/c61cf49b-2441-44a5-8177-7648b855f574
-- title:
--   Definitions bundle OAIQ236Ap005 of the split of OpenAI, Parabolic intersections in Artin groups
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HarmonicArtin.ParabolicIntersections.unconditional_arbitrary_intersections`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_nonclique_dynamics`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure` and `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_intersections`, carved from OpenAI's openai/math development (OpenAI, *Parabolic intersections in Artin groups*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 222 declarations of OpenAI's Lean: 76 definitions and 146 theorems. The definitions and types are `OAI.HarmonicArtin.FusionOrbitLayerIndex`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.LeftHomIndex`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.LeftPacketIndex`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.LeftPaths`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.RightHomIndex`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.RightPacketIndex`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.RightPaths`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.arrowImage`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.basePath`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.classLabelFunctor`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.colorPacketPerm`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.complex`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.coneComparison`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.coneIndexEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.evaluationMatrix`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.evaluationSource`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.evaluationTarget`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.homComparison`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.homSwitch`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.homSwitchMap`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.homUnswitch`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.homUnswitchMap`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.homotopyEquivalence`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.indexEmbed`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.inverseEvaluationMatrix`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.leftHomComplex`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.leftHomMatrix`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.leftHomPlacement`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.leftPacketEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.leftPathIndex`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.leftPathsEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.leftSectors`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.liftPath`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearSwitch`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.map`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.matrix`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.packetSwitchMatrix`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.pathImage`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.pathSwitchEquiv` and 36 more.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `ArtinGroups_Complexes_ActedIndex`, `ArtinGroups_Complexes_BasedComplexComplex`, `ArtinGroups_Complexes_FiniteHomotopySetoid`, `ArtinGroups_Complexes_GeneratorArray`, `ArtinGroups_Complexes_GeneratorArray2`, `ArtinGroups_Complexes_InverseTwistDifferential`, `ArtinGroups_Complexes_InverseTwistIdentity`, `ArtinGroups_Complexes_LevelArrayComplexMinimal`, `ArtinGroups_Complexes_MinimalModel`, `ArtinGroups_Complexes_MinimalModelEquivalence`, `ArtinGroups_Complexes_NormalizedInverseTwistHomotopy`, `ArtinGroups_Complexes_Refl`, `ArtinGroups_Complexes_ReindexConeIsomorphism`, `ArtinGroups_Complexes_Sum`, `ArtinGroups_Complexes_TotalVector`, `ArtinGroups_Coxeter_BraidCoreFirstTarget`, `ArtinGroups_Functors_BasePath`, `ArtinGroups_Functors_ColorPacketPerm`, `ArtinGroups_Functors_ComplexPureLayer`, `ArtinGroups_Functors_ConeIndexEquiv`, `ArtinGroups_Functors_CoordinateExpansion`, `ArtinGroups_Functors_Evaluation`, `ArtinGroups_Functors_HomSwitchMap`, `ArtinGroups_Functors_Index`, `ArtinGroups_Functors_LeftHomIndex`, `ArtinGroups_Functors_LeftHomPlacement`, `ArtinGroups_Functors_LeftPacketIndex`, `ArtinGroups_Functors_PacketSwitchMatrix`, `ArtinGroups_Functors_PathImage`, `ArtinGroups_Functors_PathSwitchEquiv`, `ArtinGroups_Functors_Placement`, `ArtinGroups_Functors_SectorInverse`, `ArtinGroups_Functors_SeedEquiv`, `ArtinGroups_Geometry_CartanForm`, `ArtinGroups_Geometry_Form`, `ArtinGroups_Geometry_InvariantForm`, `ArtinGroups_Geometry_RootPair`, `ArtinGroups_Geometry_RootRowOrthogonalWord`, `ArtinGroups_Geometry_SphericalCartanPos`, `ArtinGroups_Geometry_SphericalCartanPos2`, `ArtinGroups_Geometry_StrictChamber`, `ArtinGroups_Harmonic_FusionOrbitModel`, `ArtinGroups_Harmonic_FusionPacketOrbit`, `ArtinGroups_Harmonic_FusionPacketPerm`, `ArtinGroups_Harmonic_FusionZeroLabel`, `ArtinGroups_Harmonic_Level`, `ArtinGroups_Quivers_ClosedNeighborhood`, `ArtinGroups_Quivers_Reduction`, `ArtinGroups_Quivers_ScalarCornerMatrixDegree`, `ArtinGroups_Quivers_StringArrow`, `ArtinGroups_Quivers_VertexHom`, `ArtinGroups_Quivers_VertexIdMulPath`.
--
--   **Imports.** It imports the bundles `OAIQ236Ap002`, `OAIQ236Ap003` and `OAIQ236Ap004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ236Ap008`, `OAIQ236Ap009` and `OAIQ236Ap010`.
-- source:
--   OpenAI, Parabolic intersections in Artin groups, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Parabolic-intersections-in-Artin-groups-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ236Ap002
import Definitions.Def_OAIQ236Ap003
import Definitions.Def_OAIQ236Ap004

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_VertexHom
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.instAlgebra
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.dual_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.source_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.target_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_false _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_true
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver
namespace Zigzag

variable {V A K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

variable {I J L N : Type*} [Fintype I] [Fintype J] [Fintype L]

omit [Fintype I] [Fintype J] in
lemma positiveMatrix_add {M N : Matrix I J (Q.Zigzag K)}
    (hM : PositiveMatrix Q M) (hN : PositiveMatrix Q N) :
    PositiveMatrix Q (M + N) := by
  intro i j
  simp [hM i j, hN i j]

omit [Fintype I] [Fintype L] in
lemma positiveMatrix_mul_left (M : Matrix I J (Q.Zigzag K))
    {N : Matrix J L (Q.Zigzag K)} (hN : PositiveMatrix Q N) :
    PositiveMatrix Q (M * N) := by
  intro i l
  funext v
  change (vertexHom Q (K := K) v) ((M * N) i l) = 0
  simp only [Matrix.mul_apply, map_sum, map_mul]
  apply Finset.sum_eq_zero
  intro j _
  change (M i j).vertex v * (N j l).vertex v = 0
  simp [hN j l]

omit [Fintype I] [Fintype L] in
lemma positiveMatrix_mul_right {M : Matrix I J (Q.Zigzag K)}
    (hM : PositiveMatrix Q M) (N : Matrix J L (Q.Zigzag K)) :
    PositiveMatrix Q (M * N) := by
  intro i l
  funext v
  change (vertexHom Q (K := K) v) ((M * N) i l) = 0
  simp only [Matrix.mul_apply, map_sum, map_mul]
  apply Finset.sum_eq_zero
  intro j _
  change (M i j).vertex v * (N j l).vertex v = 0
  simp [hM i j]

end Zigzag
end HarmonicArtin.ReversibleQuiver

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_Level
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

namespace ReversibleQuiver.Zigzag

variable {V A K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

lemma positive_homogeneous_nonzero_degree {a : ℤ} {x : Q.Zigzag K}
    (ha : Homogeneous Q a x) (hv : x.vertex = 0) (hx : x ≠ 0) : a = 1 ∨ a = 2 := by
  rcases homogeneous_nonzero_degree Q ha hx with h | h | h
  · subst a
    exact (hx (Zigzag.ext hv (ha.2.1 (by decide)) (ha.2.2 (by decide)))).elim
  · exact Or.inl h
  · exact Or.inr h

namespace BasedComplex

variable {I : Type*} [Fintype I]

theorem differential_level (E : BasedComplex Q (K := K) I)
    (hE : E.IsMinimal Q) {i j : I} (hij : E.differential i j ≠ 0) :
    (E.placement j).level = (E.placement i).level ∨
    (E.placement j).level = (E.placement i).level - 1 := by
  have hc : (E.placement j).cochain = (E.placement i).cochain + 1 := by
    by_contra h
    exact hij ((E.degree i j).1 h)
  have hu := positive_homogeneous_nonzero_degree Q (E.degree i j).2 (hE i j) hij
  simp only [zero_add] at hu
  dsimp only [GeneratorPlacement.level]
  omega

lemma differential_intermediate_level (E : BasedComplex Q (K := K) I)
    (hE : E.IsMinimal Q) {i j k : I} (hi : E.differential i k ≠ 0)
    (hj : E.differential k j ≠ 0) :
    (E.placement j).level ≤ (E.placement k).level ∧
    (E.placement k).level ≤ (E.placement i).level := by
  have h₁ := E.differential_level Q hE hi
  have h₂ := E.differential_level Q hE hj
  omega

lemma pureLayer_intermediate (E : BasedComplex Q (K := K) I) (hE : E.IsMinimal Q)
    (d : ℤ) : ∀ i ∈ {i | (E.placement i).level = d},
      ∀ j ∈ {j | (E.placement j).level = d},
      ∀ k ∉ {k | (E.placement k).level = d},
      E.differential i k * E.differential k j = 0 := by
  intro i hi j hj k hk
  by_cases h₁ : E.differential i k = 0
  · rw [h₁]
    exact MulZeroClass.zero_mul _
  by_cases h₂ : E.differential k j = 0
  · rw [h₂]
    exact MulZeroClass.mul_zero _
  have hb := E.differential_intermediate_level Q hE h₁ h₂
  exact (hk (le_antisymm (hi ▸ hb.2) (hj ▸ hb.1))).elim

noncomputable def pureLayer (E : BasedComplex Q (K := K) I)
    (hE : E.IsMinimal Q) (d : ℤ) :
    BasedComplex Q (K := K) (↑{i | (E.placement i).level = d} : Type _) :=
  E.restrict Q _ (E.pureLayer_intermediate Q hE d)

end BasedComplex
end ReversibleQuiver.Zigzag
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_Reduction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J L : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

omit [Fintype A] [DecidableEq V] in
lemma reductionAt_positive (p : I → GeneratorPlacement V) (q : J → GeneratorPlacement V)
    (M : Matrix I J (Q.Zigzag K)) (a : GeneratorPlacement V) (hM : PositiveMatrix Q M) :
    reductionAt Q p q M a = 0 := by
  funext i j
  change (M i.1 j.1).vertex a.color = 0
  rw [hM i.1 j.1]
  rfl

namespace BasedComplex

variable [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem multiplicity_eq_of_minimal_homotopyEquivalence
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (h : HomotopyEquivalence Q E F) (a : GeneratorPlacement V) :
    E.multiplicity Q a = F.multiplicity Q a := by
  classical
  let f := reductionAt Q E.placement F.placement h.forward.matrix a
  let g := reductionAt Q F.placement E.placement h.backward.matrix a
  have hfg : f * g = 1 := by
    dsimp only [f, g]
    rw [← reductionAt_mul Q _ _ _ _ _ a h.forward.entries h.forward.degree,
      h.sourceEquation, reductionAt_add, reductionAt_identity,
      reductionAt_positive Q _ _ _ a]
    · exact add_zero _
    · exact positiveMatrix_add Q
        (positiveMatrix_mul_right Q hE h.sourceHomotopy)
        (positiveMatrix_mul_left Q h.sourceHomotopy hE)
  have hgf : g * f = 1 := by
    dsimp only [f, g]
    rw [← reductionAt_mul Q _ _ _ _ _ a h.backward.entries h.backward.degree,
      h.targetEquation, reductionAt_add, reductionAt_identity,
      reductionAt_positive Q _ _ _ a]
    · exact add_zero _
    · exact positiveMatrix_add Q
        (positiveMatrix_mul_right Q hF h.targetHomotopy)
        (positiveMatrix_mul_left Q h.targetHomotopy hF)
  have hd := (Matrix.toLinearEquivRight'OfInv hfg hgf).finrank_eq
  simpa only [multiplicity, Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one, Nat.card_eq_fintype_card] using hd.symm

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ActedIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

def unitTest (E : BasedComplex Q (K := K) I) (α : V) (i : ActedIndex Q E α) :
    TestIndex Q E.placement α :=
  ⟨i.val, ⟨.inl α, rfl, i.property.symm⟩⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_InverseTwistDifferential
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

lemma normalizedInverseTwist_differential (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :
    (normalizedInverseTwist Q hn E α).differential = inverseTwistDifferential Q E α := by
  change ((E.negativeTwist Q α).positiveTwist Q α).differential.submatrix
    (inverseTwistIndexEquiv Q hn E α) (inverseTwistIndexEquiv Q hn E α) = _
  rw [positiveTwist_differential]
  apply Matrix.ext
  intro i j
  rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v
  all_goals simp only [Matrix.submatrix_apply, inverseTwistIndexEquiv, Equiv.coe_fn_mk,
    Matrix.of_apply,
    inverseTwistDifferential, Matrix.fromBlocks, testTransform, scalarCornerMatrix, testMatrix]
  all_goals simp only [negativeTwist_differential, Matrix.fromBlocks, Matrix.neg_apply,
    Matrix.zero_apply, Matrix.of_apply, testTransform, scalarCornerMatrix, testMatrix, Sum.elim_inl, Sum.elim_inr, MulZeroClass.mul_zero,
    coordinates_zero, zero_smul, neg_zero, selfCornerEquiv_false, selfCornerEquiv_true]
  all_goals try simp only [evaluationMatrix, Sum.inl.injEq, Sum.inr.injEq,
    Sum.inl_ne_inr, Sum.inr_ne_inl, ↓reduceIte, selfCornerEquiv_false,
    selfCornerEquiv_true, pathBasis_vertex, pathBasis_token, projectiveIdentity,
    Matrix.diagonal_apply, testPlacement, testToken]
  all_goals try simp only [_root_.mul_neg, mul_smul, map_neg, Pi.neg_apply,
    coordinates_smul, neg_smul, neg_neg]
  all_goals try simp only [vertexId_mul_self]
  · simp only [coevaluationMatrix, unitContraction, pathCoordinates_vertex]
    split_ifs <;> simp_all
  · apply congrArg Neg.neg
    change (pathBasis Q (K := K) u.2.val * coevaluationMatrix Q E.placement α u.1 v).token α •
      vertexId Q α = if u = v then vertexId Q α else 0
    by_cases hi : u.1 = v.1
    · rcases u with ⟨i, u⟩
      rcases v with ⟨j, v⟩
      dsimp only at hi
      subst j
      simp only [coevaluationMatrix, ite_true, if_true, cornerPath_basis_dual_token]
      by_cases hp : u = v
      · subst v
        simp
      · simp [hp]
    · have huv : u ≠ v := fun h => hi (congrArg Sigma.fst h)
      simp only [coevaluationMatrix, ite_eq_right hi, MulZeroClass.mul_zero,
        token_zero, Pi.zero_apply, zero_smul, ite_eq_right huv]
  all_goals
    have ht : tokenBasis Q (K := K) α * vertexId Q α = tokenBasis Q α := by
      simpa only [Path.target, pathBasis_token] using
        (pathBasis_right Q (K := K) (.inr (.inr α)))
    try simp only [ht, pathCoordinates_vertex, pathCoordinates_token]
    try simp only [vertexId, tokenBasis, vertex, token, Pi.single_apply, ite_true, if_true,
      Pi.zero_apply]
    first
    | rfl
    | exact congrArg (fun k : K => k • vertexId Q (K := K) α)
        (_root_.mul_one (pathCoordinates Q (pathBasis Q (K := K) u.2.val *
          E.differential u.1 v.1) v.2.val))
    | exact (congrArg (fun k : K => k • vertexId Q (K := K) α)
        (MulZeroClass.mul_zero (pathCoordinates Q (pathBasis Q (K := K) u.2.val *
          E.differential u.1 v.1) v.2.val))).trans (zero_smul K _)
    | refine @ite_cond_congr _ _ _ ?_ ?_ _ _ rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_InverseTwistIdentity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

lemma inverseTwist_sourceEquation (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :
    inverseTwistProjection Q E α * inverseTwistInjection Q E α =
      projectiveIdentity Q (inverseTwistPlacement Q E α) +
      (inverseTwistDifferential Q E α * inverseTwistHomotopy Q E α +
       inverseTwistHomotopy Q E α * inverseTwistDifferential Q E α) := by
  rw [inverseTwistIdentity_eq]
  let t := testTransform Q E.placement E.placement α E.differential
  let r := unitContraction Q E.placement α (K := K)
  let θ := testToken Q E.placement α (K := K)
  let ι := projectiveIdentity Q (K := K) (testPlacement Q E.placement α)
  let e := evaluationMatrix Q E.placement α (K := K)
  let η := projectiveIdentity Q (K := K) E.placement
  let c := coevaluationMatrix Q E.placement α (K := K)
  have hf : inverseTwistProjection Q E α = FiveBlock.projection e η := by
    funext i j
    rcases i with u | u | u | i | u <;> rfl
  have hg : inverseTwistInjection Q E α = FiveBlock.injection c η := by
    funext i j
    rcases j with v | v | v | j | v <;> rfl
  have hh : inverseTwistHomotopy Q E α = FiveBlock.homotopy ι := by
    funext i j
    rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v <;> rfl
  have hd : inverseTwistDifferential Q E α =
      FiveBlock.differential t r θ ι e E.differential c := by
    funext i j
    rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v <;> rfl
  have hId : inverseTwistIdentity Q E α = FiveBlock.identity ι η := by
    funext i j
    rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v <;> rfl
  rw [hf, hg, hh, hd, hId]
  apply FiveBlock.contraction
  · exact projectiveIdentity_mul Q (projectiveEntries_identity Q)
  · exact projectiveIdentity_mul Q (projectiveEntries_identity Q)
  · exact projectiveIdentity_mul Q (E.testComplex Q α).entries
  · exact mul_projectiveIdentity Q (E.testComplex Q α).entries
  · exact projectiveIdentity_mul Q (unitContraction_entries Q E α)
  · exact mul_projectiveIdentity Q (testToken_entries Q E α)
  · exact projectiveIdentity_mul Q (evaluation_entries Q E.placement α)
  · exact mul_projectiveIdentity Q (evaluation_entries Q E.placement α)
  · exact mul_projectiveIdentity Q (coevaluation_entries Q E.placement α)
  · exact projectiveIdentity_mul Q (coevaluation_entries Q E.placement α)
  · exact evaluation_coevaluation Q hn E.placement α

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_NormalizedInverseTwistHomotopy
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

noncomputable def normalizedInverseTwistHomotopyEquivalence
    (hn : ∀ a, Q.source a ≠ Q.target a) (E : BasedComplex Q (K := K) I) (α : V) :
    HomotopyEquivalence Q (normalizedInverseTwist Q hn E α) E where
  forward := {
    matrix := inverseTwistProjection Q E α
    entries := by
      rw [normalizedInverseTwist_placement]
      exact inverseTwistProjection_entries Q E α
    degree := by
      rw [normalizedInverseTwist_placement]
      exact inverseTwistProjection_degree Q E α
    commute := by
      rw [normalizedInverseTwist_differential]
      exact inverseTwistProjection_commute Q E α }
  backward := {
    matrix := inverseTwistInjection Q E α
    entries := by
      rw [normalizedInverseTwist_placement]
      exact inverseTwistInjection_entries Q E α
    degree := by
      rw [normalizedInverseTwist_placement]
      exact inverseTwistInjection_degree Q E α
    commute := by
      rw [normalizedInverseTwist_differential]
      exact inverseTwistInjection_commute Q E α }
  sourceHomotopy := inverseTwistHomotopy Q E α
  targetHomotopy := 0
  sourceEntries := by
    rw [normalizedInverseTwist_placement]
    exact inverseTwistHomotopy_entries Q E α
  targetEntries := projectiveEntries_zero Q
  sourceDegree := by
    rw [normalizedInverseTwist_placement]
    exact inverseTwistHomotopy_degree Q E α
  targetDegree := mapDegree_zero Q (-1) 0
  sourceEquation := by
    dsimp only
    rw [normalizedInverseTwist_placement, normalizedInverseTwist_differential]
    exact inverseTwist_sourceEquation Q hn E α
  targetEquation := by
    dsimp only
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
    exact inverseTwist_targetEquation Q E α

noncomputable def positive_negative_homotopyEquivalence
    (hn : ∀ a, Q.source a ≠ Q.target a) (E : BasedComplex Q (K := K) I) (α : V) :
    HomotopyEquivalence Q ((E.negativeTwist Q α).positiveTwist Q α) E := by
  classical
  exact
  (((E.negativeTwist Q α).positiveTwist Q α).reindexHomotopyEquivalence Q
    (inverseTwistIndexEquiv Q hn E α)).trans Q
      (normalizedInverseTwistHomotopyEquivalence Q hn E α)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Coxeter_BraidCoreFirstTarget
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

omit [Fintype V] in
lemma arrowBasis_reverse (a : A) :
    arrowBasis Q (K := K) a * arrowBasis Q (Q.reverse a) = tokenBasis Q (Q.source a) := by
  apply ext
  · rw [vertex_mul]
    funext i
    simp [arrowBasis, tokenBasis, vertex]
  · rw [arrow_mul]
    funext b
    simp [arrowBasis, tokenBasis, vertex, arrow, leftScale, rightScale]
  · rw [token_mul]
    funext i
    simp only [arrowBasis, tokenBasis, vertex, token, arrow, backtrack, Pi.single_apply,
      Pi.zero_apply, MulZeroClass.mul_zero,
      Pi.add_apply, zero_add]
    rw [Finset.sum_eq_single a]
    · simp [eq_comm]
    · intro b _ hb
      simp [hb]
    · simp

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_FiniteHomotopySetoid
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

universe u

variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

noncomputable def classTwistPerm (hn : ∀ a, Q.source a ≠ Q.target a) (α : V) :
    Equiv.Perm (FiniteHomotopyClass Q (K := K)) where
  toFun := classPositiveTwist Q α
  invFun := classNegativeTwist Q α
  left_inv := by
    intro x
    induction x using Quotient.inductionOn with | _ E =>
      apply Quotient.sound
      exact ⟨negative_positive_homotopyEquivalence Q hn E.complex α⟩
  right_inv := by
    intro x
    induction x using Quotient.inductionOn with | _ E =>
      apply Quotient.sound
      exact ⟨positive_negative_homotopyEquivalence Q hn E.complex α⟩

namespace FiniteModel

omit [Fintype V] [DecidableEq A] in
lemma minimalRepresentative_minimal (E : FiniteModel.{u} Q (K := K)) :
    (E.minimalRepresentative Q).complex.IsMinimal Q := (E.exists_minimal Q).choose_spec.1

noncomputable def minimalRepresentativeEquivalence (E : FiniteModel.{u} Q (K := K)) :
    HomotopyEquivalence Q E.complex (E.minimalRepresentative Q).complex :=
  (E.exists_minimal Q).choose_spec.2.some

end FiniteModel

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_BasedComplexComplex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

theorem exists_packetPerm (hn : ∀ a, Q.source a ≠ Q.target a)
    {J : Type u} [Fintype J] (v : J → V)
    (hv : Pairwise (fun a b => OrthogonalVertices Q (v a) (v b))) :
    ∃ π : Equiv.Perm (FiniteHomotopyClass Q (K := K)),
      ∀ E : FiniteModel.{u} Q (K := K), classOfComplex Q (E.complex.packetTwist Q v) =
        π (Quotient.mk (finiteHomotopySetoid Q) E) := by
  classical
  suffices hh : ∀ (J : Type u) [Fintype J] (v:J → V),
      Pairwise (fun a b => OrthogonalVertices Q (v a) (v b)) →
      ∃ π : Equiv.Perm (FiniteHomotopyClass Q (K := K)),
        ∀ E : FiniteModel.{u} Q (K := K), classOfComplex Q (E.complex.packetTwist Q v) =
          π (Quotient.mk (finiteHomotopySetoid Q) E) from hh J v hv
  intro J inst
  apply Fintype.induction_empty_option (P := fun J _ => ∀ v:J → V,
    Pairwise (fun a b => OrthogonalVertices Q (v a) (v b)) →
    ∃ π : Equiv.Perm (FiniteHomotopyClass Q (K := K)),
      ∀ E : FiniteModel.{u} Q (K := K), classOfComplex Q (E.complex.packetTwist Q v) =
        π (Quotient.mk (finiteHomotopySetoid Q) E)) _ _ _ J
  · intro J L instL e ih
    let := Fintype.ofEquiv L e.symm
    intro v hv
    obtain ⟨π,hπ⟩ := ih (v ∘ e) (fun a b hab => hv (fun he => hab (e.injective he)))
    refine ⟨π,fun E => ?_⟩
    rw [classOfComplex_packet_reindex Q E.complex v e]
    exact hπ E
  ·
    intro v hv
    refine ⟨Equiv.refl _,fun E => ?_⟩
    convert (classOfComplex_reindex Q _ (packetEmptyEquiv Q E.complex v)).trans
      (congrArg (classOfComplex Q) (packetEmpty_eq Q E.complex v)) using 1 <;> first | (with_reducible_and_instances rfl) | ((congr 2 <;> exact Subsingleton.elim _ _))
  · intro J instJ ih v hv
    obtain ⟨π,hπ⟩ := ih (v ∘ some) (fun a b hab => hv (fun he => hab (Option.some.inj he)))
    refine ⟨classTwistPerm Q hn (v none) * π,fun E => ?_⟩
    have hv' : v = fun z : Option J => z.elim (v none) (v ∘ some) := by
      funext z; cases z <;> rfl
    conv_lhs => rw [hv']
    convert (classOfComplex_packet_cons Q E.complex (v none) (v ∘ some)
      (fun a => hv (by simp))).trans (congrArg (classPositiveTwist Q (v none)) (hπ E)) using 1 <;> first | (with_reducible_and_instances rfl) | ((congr 2 <;> exact Subsingleton.elim _ _))

noncomputable def classPacketPerm (hn : ∀ a, Q.source a ≠ Q.target a)
    {J : Type u} [Fintype J] (v : J → V)
    (hv : Pairwise (fun a b => OrthogonalVertices Q (v a) (v b))) :
    Equiv.Perm (FiniteHomotopyClass Q (K := K)) :=
  (exists_packetPerm Q (K := K) hn v hv).choose

lemma classPacketPerm_apply (hn : ∀ a, Q.source a ≠ Q.target a)
    {J : Type u} [Fintype J] [DecidableEq J] (v : J → V)
    (hv : Pairwise (fun a b => OrthogonalVertices Q (v a) (v b)))
    (E : FiniteModel.{u} Q (K := K)) :
    classPacketPerm Q hn v hv (Quotient.mk (finiteHomotopySetoid Q) E) =
      classOfComplex Q (E.complex.packetTwist Q v) :=
by
  convert ((exists_packetPerm Q (K := K) hn v hv).choose_spec E).symm using 1 <;>
    (congr 2 <;> exact Subsingleton.elim _ _)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_GeneratorArray
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V] [Fintype I] [Fintype J]

variable [DecidableEq I] [DecidableEq J]

lemma generatorArray_eq_of_minimal_homotopyEquivalence
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (hE : E.IsMinimal Q) (hF : F.IsMinimal Q) (e : HomotopyEquivalence Q E F) :
    E.generatorArray Q = F.generatorArray Q := by
  ext a
  simp only [generatorArray_apply]
  exact multiplicity_eq_of_minimal_homotopyEquivalence Q E F hE hF e a

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_GeneratorArray2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

universe u

variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

noncomputable def classGeneratorArray :
    FiniteHomotopyClass Q (K := K) → (GeneratorPlacement V →₀ ℕ) :=
  Quotient.lift (fun E => (E.minimalRepresentative Q).complex.generatorArray Q)
    (by
      intro E F h
      obtain ⟨e⟩ := h
      exact generatorArray_eq_of_minimal_homotopyEquivalence Q _ _
        (E.minimalRepresentative_minimal Q) (F.minimalRepresentative_minimal Q)
        (((E.minimalRepresentativeEquivalence Q).symm Q).trans Q
          (e.trans Q (F.minimalRepresentativeEquivalence Q))))

noncomputable def classLevelArray (x : FiniteHomotopyClass Q (K := K)) : V × ℤ →₀ ℕ :=
  (classGeneratorArray Q x).mapDomain (fun a => (a.color, a.level))

omit [Fintype V] [DecidableEq A] in
lemma classGeneratorArray_of_minimal (E : FiniteModel.{u} Q (K := K))
    (hE : E.complex.IsMinimal Q) :
    classGeneratorArray Q (Quotient.mk (finiteHomotopySetoid Q) E) =
      E.complex.generatorArray Q := by
  exact (generatorArray_eq_of_minimal_homotopyEquivalence Q _ _ hE
    (E.minimalRepresentative_minimal Q) (E.minimalRepresentativeEquivalence Q)).symm

omit [Fintype V] [DecidableEq A] in
lemma classLevelArray_of_minimal (E : FiniteModel.{u} Q (K := K))
    (hE : E.complex.IsMinimal Q) :
    classLevelArray Q (Quotient.mk (finiteHomotopySetoid Q) E) =
      E.complex.levelArray Q := by
  unfold classLevelArray levelArray
  rw [classGeneratorArray_of_minimal Q E hE]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_MinimalModel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in
lemma minimalClassModel_minimal (x : FiniteHomotopyClass Q (K := K)) :
    (minimalClassModel Q x).complex.IsMinimal Q :=
  FiniteModel.minimalRepresentative_minimal Q _

omit [Fintype V] [DecidableEq A] in
lemma minimalClassModel_class (x : FiniteHomotopyClass Q (K := K)) :
    Quotient.mk (finiteHomotopySetoid Q) (minimalClassModel Q x) = x := by
  calc
    _ = Quotient.mk (finiteHomotopySetoid Q) (Quotient.out x) :=
      Quotient.sound ⟨((Quotient.out x).minimalRepresentativeEquivalence Q).symm Q⟩
    _ = x := Quotient.out_eq x

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_Sum
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I : Type u} [Fintype I] [DecidableEq I]

noncomputable def classSum (x : I → FiniteHomotopyClass Q (K := K)) :
    FiniteHomotopyClass Q (K := K) := by
  classical
  exact classOfComplex Q (finiteSum Q (fun i => (x i).out.complex))

omit [Fintype V] [DecidableEq A] in
lemma classSum_mk (E : I → FiniteModel.{u} Q (K := K)) :
    classSum Q (fun i => Quotient.mk (finiteHomotopySetoid Q) (E i)) =
      classOfComplex Q (finiteSum Q (fun i => (E i).complex)) := by
  classical
  apply classOfComplex_eq
  apply HomotopyEquivalence.finiteSum
  intro i
  exact Classical.choice (Quotient.exact (Quotient.out_eq
    (Quotient.mk (finiteHomotopySetoid Q) (E i))))

omit [Fintype V] [DecidableEq A] in
lemma classSum_complex {T : I → Type u} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
    (E : (i:I) → BasedComplex Q (K := K) (T i)) :
    classSum Q (fun i => classOfComplex Q (E i)) = classOfComplex Q (finiteSum Q E) :=
  classSum_mk Q (fun i => FiniteModel.ofComplex Q (E i))

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_Refl
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I J L N : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]
  [Fintype I] [Fintype J] [Fintype L] [Fintype N]
  [DecidableEq I] [DecidableEq J] [DecidableEq L] [DecidableEq N]

noncomputable def ChainIsomorphism.refl (E : BasedComplex Q (K := K) I) :
    ChainIsomorphism Q E E where
  forward := Map.identity Q E
  backward := Map.identity Q E
  sourceEquation := projectiveIdentity_mul Q (projectiveEntries_identity Q)
  targetEquation := projectiveIdentity_mul Q (projectiveEntries_identity Q)

noncomputable def reindexChainIsomorphism (E : BasedComplex Q (K := K) I) (e : J ≃ I) :
    ChainIsomorphism Q E (E.reindex Q e) where
  forward := E.reindexForward Q e
  backward := E.reindexBackward Q e
  sourceEquation := by
    have h := (E.reindexHomotopyEquivalence Q e).sourceEquation
    simpa only [reindexHomotopyEquivalence,Matrix.mul_zero,Matrix.zero_mul,add_zero] using h
  targetEquation := by
    have h := (E.reindexHomotopyEquivalence Q e).targetEquation
    simpa only [reindexHomotopyEquivalence,Matrix.mul_zero,Matrix.zero_mul,add_zero] using h

noncomputable def Map.reindex {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (f : Map Q E F) (e : L ≃ I) (d : N ≃ J) :
    Map Q (E.reindex Q e) (F.reindex Q d) where
  matrix := f.matrix.submatrix e d
  entries := ⟨fun i j => f.entries.1 (e i) (d j), fun i j => f.entries.2 (e i) (d j)⟩
  degree := fun i j => f.degree (e i) (d j)
  commute := by
    change E.differential.submatrix e e * f.matrix.submatrix e d =
      f.matrix.submatrix e d * F.differential.submatrix d d
    rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv,f.commute]

lemma Map.coneIdentity {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (f : Map Q E F) :
    Matrix.fromBlocks (projectiveIdentity Q (K := K) E.placement) 0 0
      (projectiveIdentity Q F.placement) = projectiveIdentity Q (f.cone Q).placement := by
  unfold projectiveIdentity
  rw [Matrix.fromBlocks_diagonal]
  congr 1
  funext i
  rcases i with i|i <;> rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_LevelArrayComplexMinimal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]
  {I : Type u} [Fintype I] [DecidableEq I]

lemma classLevelArray_complex_minimal (E : BasedComplex Q (K := K) I) (hE : E.IsMinimal Q) :
    classLevelArray Q (classOfComplex Q E) = E.levelArray Q :=
  classLevelArray_of_minimal Q (FiniteModel.ofComplex Q E) hE

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_MinimalModelEquivalence
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I : Type u} [Fintype I] [DecidableEq I]

noncomputable def classLayer (d : ℤ) (x : FiniteHomotopyClass Q (K := K)) :
    FiniteHomotopyClass Q (K := K) :=
  classOfComplex Q ((minimalClassModel Q x).complex.pureLayer Q (minimalClassModel_minimal Q x) d)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ReindexConeIsomorphism
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I J L N : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]
  [Fintype I] [Fintype J] [Fintype L] [Fintype N]
  [DecidableEq I] [DecidableEq J] [DecidableEq L] [DecidableEq N]
  {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}

omit [DecidableEq I] [DecidableEq J] [DecidableEq L] [DecidableEq N] in
lemma Map.reindexCone_eq (f : Map Q E F) (e : L ≃ I) (d : N ≃ J) :
    (f.cone Q).reindex Q (Equiv.sumCongr e d) = (f.reindex Q e d).cone Q := by
  apply ext_placement_differential
  · funext i
    rcases i with i|i <;> rfl
  · apply Matrix.ext
    intro i j
    rcases i with i|i <;> rcases j with j|j <;> rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_TotalVector
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
open _root_.Matrix
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

noncomputable def classTotalVector (x : FiniteHomotopyClass Q (K:=K)) : V → ℝ :=
  generatorVector Q (minimalClassModel Q x).complex

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_VertexIdMulPath
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V B K : Type*} (Q : ReversibleQuiver V B)
  [Field K] [Fintype V] [Fintype B] [DecidableEq V] [DecidableEq B]

lemma vertexId_mul_pathBasis (v : V) (p : Path V B) :
    vertexId Q v * pathBasis Q (K := K) p =
      if Path.source Q p = v then pathBasis Q p else 0 := by
  apply (pathCoordinates Q).injective
  funext q
  rw [coordinates_vertexId_left]
  by_cases h : Path.source Q p=v
  · rw [ite_eq_left h]
    by_cases hpq : p=q
    · subst q; rw [ite_eq_left h]
    · simp [pathBasis_coordinates,hpq]
  · rw [ite_eq_right h, map_zero]
    by_cases hpq : p=q
    · subst q; simp [h]
    · simp [pathBasis_coordinates,hpq]

lemma pathBasis_mul_vertexId (v : V) (p : Path V B) :
    pathBasis Q (K := K) p * vertexId Q v =
      if Path.target Q p = v then pathBasis Q p else 0 := by
  apply (pathCoordinates Q).injective
  funext q
  rw [coordinates_vertexId_right]
  by_cases h : Path.target Q p=v
  · rw [ite_eq_left h]
    by_cases hpq : p=q
    · subst q; rw [ite_eq_left h]
    · simp [pathBasis_coordinates,hpq]
  · rw [ite_eq_right h, map_zero]
    by_cases hpq : p=q
    · subst q; simp [h]
    · simp [pathBasis_coordinates,hpq]

omit [Fintype V] in
lemma arrowBasis_mul_arrowBasis (a b : B) :
    arrowBasis Q (K := K) a * arrowBasis Q b =
      if Q.reverse a = b then tokenBasis Q (Q.source a) else 0 := by
  by_cases hr : Q.reverse a=b
  · subst b
    rw [ite_eq_left rfl]
    exact BasedComplex.arrowBasis_reverse Q a
  · rw [ite_eq_right hr]
    apply Zigzag.ext
    · rw [vertex_mul, vertex_zero]
      funext v
      simp [arrowBasis,vertex]
    · rw [arrow_mul, arrow_zero]
      funext e
      simp [arrowBasis,vertex,arrow,leftScale,rightScale]
    · rw [token_mul, token_zero]
      funext v
      simp only [arrowBasis,vertex,arrow,token,
        Pi.add_apply,Pi.mul_apply,Pi.zero_apply]
      simp only [backtrack,Pi.single_apply]
      rw [Finset.sum_eq_single a]
      · simp [hr]
      · intro e he hea
        simp [hea]
      · simp

omit [DecidableEq B] in
lemma map_mul_of_pathBasis {R : Type*} [Ring R] [Algebra K R]
    (f : Q.Zigzag K →ₗ[K] R)
    (hf : ∀ p q, f (pathBasis Q p * pathBasis Q q)=f (pathBasis Q p)*f (pathBasis Q q))
    (x y : Q.Zigzag K) : f (x*y)=f x*f y := by
  conv_lhs => rw [← sum_pathBasis Q x, ← sum_pathBasis Q y]
  conv_rhs => rw [← sum_pathBasis Q x, ← sum_pathBasis Q y]
  simp only [Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,
    map_sum,map_smul,hf,Algebra.mul_smul_comm]

end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_StringArrow
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver

variable {V B J K : Type*} (Q : ReversibleQuiver V B)

variable (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
    (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)

def stringQuiver : ReversibleQuiver (V × J) (StringArrow step N) where
  source p := (Q.source p.base,p.left)
  target p := (Q.target p.base,p.right)
  reverse :=
    { toFun p := ⟨(Q.reverse p.base,p.right,p.left),by
        have hp := p.property
        change (if step p.base then N p.left p.right else p.left=p.right) at hp
        change (if step (Q.reverse p.base) then N p.right p.left else p.right=p.left)
        rw [hstep]
        cases hs : step p.base <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at *
        · exact hp.symm
        · exact hN hp⟩
      invFun p := ⟨(Q.reverse p.base,p.right,p.left),by
        have hp := p.property
        change (if step p.base then N p.left p.right else p.left=p.right) at hp
        change (if step (Q.reverse p.base) then N p.right p.left else p.right=p.left)
        rw [hstep]
        cases hs : step p.base <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at *
        · exact hp.symm
        · exact hN hp⟩
      left_inv p := by apply StringArrow.ext <;> simp [StringArrow.base,StringArrow.left,StringArrow.right]
      right_inv p := by apply StringArrow.ext <;> simp [StringArrow.base,StringArrow.left,StringArrow.right] }
  reverse_reverse p := by
    apply StringArrow.ext
    · exact Q.reverse_reverse p.base
    · rfl
    · rfl
  source_reverse p := Prod.ext (Q.source_reverse p.base) rfl
  target_reverse p := Prod.ext (Q.target_reverse p.base) rfl

namespace StringFunctor

variable [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]

local notation "U" => Q.stringQuiver step hstep N hN
local notation "I" => StringIndex (V := V) N

noncomputable def unitImage (a : V × J) : Matrix I I (Zigzag U K) :=
  fun i j => if i=j ∧ i.old=a then Zigzag.vertexId U i.new else 0

noncomputable def tokenImage (μ : J → K) (a : V × J) : Matrix I I (Zigzag U K) :=
  fun i j => if i=j ∧ i.old=a then (μ i.label / μ a.2) • Zigzag.tokenBasis U i.new else 0

noncomputable def arrowImage (orient : B → Bool) (μ : J → K) (A : K)
    (p : StringArrow step N) : Matrix I I (Zigzag U K) :=
  fun i j => if i.old=(U).source p ∧ j.old=(U).target p then
    if h : (if step p.base then N i.label j.label else i.label=j.label) then
      coefficient step N orient μ A p i.label j.label •
        Zigzag.arrowBasis U (⟨(p.base,i.label,j.label),h⟩ : StringArrow step N)
    else 0
  else 0

omit [DecidableEq B] in
lemma unitImage_mul (a : V × J) (M : Matrix I I (Zigzag U K))
    (hM : ∀ i j, Zigzag.vertexId U i.new * M i j = M i j) (i j : I) :
    (unitImage (K := K) Q step hstep N hN a * M) i j = if i.old=a then M i j else 0 := by
  rw [Matrix.mul_apply,Finset.sum_eq_single i]
  · simp only [unitImage,true_and]
    by_cases hi : i.old=a <;> simp [hi,hM]
  · intro k hk hki
    simp [unitImage,Ne.symm hki]
  · simp

omit [DecidableEq B] in
lemma mul_unitImage (a : V × J) (M : Matrix I I (Zigzag U K))
    (hM : ∀ i j, M i j * Zigzag.vertexId U j.new = M i j) (i j : I) :
    (M * unitImage (K := K) Q step hstep N hN a) i j = if j.old=a then M i j else 0 := by
  rw [Matrix.mul_apply,Finset.sum_eq_single j]
  · simp only [unitImage,true_and]
    by_cases hi : j.old=a <;> simp [hi,hM]
  · intro k hk hkj
    simp [unitImage,hkj]
  · simp

lemma arrowImage_left (orient : B → Bool) (μ : J → K) (A : K)
    (p : StringArrow step N) (i j : I) :
    Zigzag.vertexId U i.new * arrowImage Q step hstep N hN orient μ A p i j =
      arrowImage Q step hstep N hN orient μ A p i j := by
  unfold arrowImage
  by_cases h : i.old=(U).source p ∧ j.old=(U).target p
  swap
  · rw [ite_eq_right h,mul_zero]
  rw [ite_eq_left h]
  by_cases h' : (if step p.base then N i.label j.label else i.label=j.label)
  swap
  · rw [dite_eq_right h',mul_zero]
  rw [dite_eq_left h']
  rw [Algebra.mul_smul_comm]
  congr 1
  let r : StringArrow step N := ⟨(p.base,i.label,j.label),h'⟩
  have hr : (U).source r=i.new := by
    apply Prod.ext
    · exact (congrArg Prod.fst h.1).symm
    · rfl
  change Zigzag.vertexId U i.new * Zigzag.arrowBasis U r = _
  rw [← hr, ← Zigzag.pathBasis_arrow]
  exact Zigzag.pathBasis_left U (.inr (.inl r))

lemma arrowImage_right (orient : B → Bool) (μ : J → K) (A : K)
    (p : StringArrow step N) (i j : I) :
    arrowImage Q step hstep N hN orient μ A p i j * Zigzag.vertexId U j.new =
      arrowImage Q step hstep N hN orient μ A p i j := by
  unfold arrowImage
  by_cases h : i.old=(U).source p ∧ j.old=(U).target p
  swap
  · rw [ite_eq_right h,zero_mul]
  rw [ite_eq_left h]
  by_cases h' : (if step p.base then N i.label j.label else i.label=j.label)
  swap
  · rw [dite_eq_right h',zero_mul]
  rw [dite_eq_left h']
  rw [smul_mul_assoc]
  congr 1
  let r : StringArrow step N := ⟨(p.base,i.label,j.label),h'⟩
  have hr : (U).target r=j.new := by
    apply Prod.ext
    · exact (congrArg Prod.fst h.2).symm
    · rfl
  change Zigzag.arrowBasis U r * Zigzag.vertexId U j.new = _
  rw [← hr, ← Zigzag.pathBasis_arrow]
  exact Zigzag.pathBasis_right U (.inr (.inl r))

omit [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] in
@[simp] lemma reverse_base (p : StringArrow step N) :
    StringArrow.base ((U).reverse p) = Q.reverse p.base := rfl
omit [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] in
@[simp] lemma reverse_left (p : StringArrow step N) :
    StringArrow.left ((U).reverse p) = p.right := rfl
omit [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] in
@[simp] lemma reverse_right (p : StringArrow step N) :
    StringArrow.right ((U).reverse p) = p.left := rfl

omit [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] in
lemma reverse_eq_iff (p q : StringArrow step N) :
    (U).reverse p=q ↔ Q.reverse p.base=q.base ∧ p.right=q.left ∧ p.left=q.right := by
  constructor
  · intro h
    exact ⟨congrArg StringArrow.base h,congrArg StringArrow.left h,congrArg StringArrow.right h⟩
  · rintro ⟨h₁,h₂,h₃⟩
    exact StringArrow.ext h₁ h₂ h₃

omit [Fintype V] in
lemma arrowImage_eq_zero_left (orient : B → Bool) (μ : J → K) (A : K)
    (p : StringArrow step N) (i j : I) (h : i.old ≠ (U).source p) :
    arrowImage Q step hstep N hN orient μ A p i j = 0 := by
  exact ite_eq_right (fun h' => h h'.1)

omit [Fintype V] in
lemma arrowImage_eq_zero_right (orient : B → Bool) (μ : J → K) (A : K)
    (p : StringArrow step N) (i j : I) (h : j.old ≠ (U).target p) :
    arrowImage Q step hstep N hN orient μ A p i j = 0 := by
  exact ite_eq_right (fun h' => h h'.2)

omit [Fintype V] in
lemma arrowImage_entry_mul_of_not_reverse (orient : B → Bool) (μ : J → K) (A : K)
    (p q : StringArrow step N) (i j k : I)
    (h : Q.reverse p.base ≠ q.base ∨ i.label ≠ k.label) :
    arrowImage Q step hstep N hN orient μ A p i j *
      arrowImage Q step hstep N hN orient μ A q j k = 0 := by
  unfold arrowImage
  by_cases hp : i.old=(U).source p ∧ j.old=(U).target p
  swap
  · rw [ite_eq_right hp,zero_mul]
  rw [ite_eq_left hp]
  by_cases hq : j.old=(U).source q ∧ k.old=(U).target q
  swap
  · rw [ite_eq_right hq,mul_zero]
  rw [ite_eq_left hq]
  by_cases hp' : (if step p.base then N i.label j.label else i.label=j.label)
  swap
  · rw [dite_eq_right hp',zero_mul]
  rw [dite_eq_left hp']
  by_cases hq' : (if step q.base then N j.label k.label else j.label=k.label)
  swap
  · rw [dite_eq_right hq',mul_zero]
  rw [dite_eq_left hq',smul_mul_assoc,Algebra.mul_smul_comm,Zigzag.arrowBasis_mul_arrowBasis]
  have hr : (U).reverse (⟨(p.base,i.label,j.label),hp'⟩ : StringArrow step N) ≠
      ⟨(q.base,j.label,k.label),hq'⟩ := by
    intro hh
    rcases (reverse_eq_iff Q step hstep N hN _ _).1 hh with ⟨hb,_,hl⟩
    rcases h with h | h
    · exact h hb
    · exact h hl
  rw [ite_eq_right hr,smul_zero,smul_zero]

lemma arrowImage_mul_of_not_reverse_base (orient : B → Bool) (μ : J → K) (A : K)
    (p q : StringArrow step N) (h : Q.reverse p.base ≠ q.base) :
    arrowImage Q step hstep N hN orient μ A p *
      arrowImage Q step hstep N hN orient μ A q = 0 := by
  apply Matrix.ext
  intro i k
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero (fun j _ => arrowImage_entry_mul_of_not_reverse
    Q step hstep N hN orient μ A p q i j k (Or.inl h))

end StringFunctor
end HarmonicArtin.ReversibleQuiver

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_PathImage
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver
variable {V B J K : Type*} (Q : ReversibleQuiver V B)
variable (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
    (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
namespace StringFunctor
variable [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
local notation "U" => Q.stringQuiver step hstep N hN
local notation "I" => StringIndex (V := V) N

lemma arrowImage_mul_of_not_composable (orient : B → Bool) (μ : J → K) (A : K)
    (p q : StringArrow step N) (h : (U).target p ≠ (U).source q) :
    arrowImage Q step hstep N hN orient μ A p *
      arrowImage Q step hstep N hN orient μ A q = 0 := by
  apply Matrix.ext
  intro i k
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hp : j.old = (U).target p
  · rw [arrowImage_eq_zero_left Q step hstep N hN _ _ _ _ _ k (fun hh => h (hp.symm.trans hh)),mul_zero]
  · rw [arrowImage_eq_zero_right Q step hstep N hN _ _ _ _ i _ hp,zero_mul]

include hstep hN in
omit [Fintype V] [Fintype B] [DecidableEq V] [DecidableEq B] in
lemma coefficient_square (orient : B → Bool)
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (μ : J → K) (hμ : ∀ a, μ a ≠ 0) (δ A : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (p q : StringArrow step N) (hb : Q.reverse p.base=q.base) (hm : p.right=q.left)
    (c : J) (hc : N p.left c) (hc' : N q.right c) :
    (∑ d : {d : J // N p.right d},
      if (if step p.base then N c d else c=d) then
        coefficient step N orient μ A p c d * coefficient step N orient μ A q d c
      else 0) = if p.left=q.right then μ c / μ p.left else 0 := by
  have hsQ : step q.base=step p.base := by rw [← hb,hstep]
  cases hs : step p.base
  · have hqs : step q.base=false := hsQ.trans hs
    have hpp : p.left=p.right := by simpa only [hs,Bool.false_eq_true,ite_false, if_false,ite_true, if_true] using (show (if step p.base then N p.left p.right else p.left=p.right) from p.property)
    have hqq : q.left=q.right := by simpa only [hqs,Bool.false_eq_true,ite_false, if_false,ite_true, if_true] using (show (if step q.base then N q.left q.right else q.left=q.right) from q.property)
    have haa : p.left=q.right := hpp.trans (hm.trans hqq)
    have haq : q.left=p.left := hm.symm.trans hpp.symm
    have hNc : N p.right c := hpp ▸ hc
    rw [ite_eq_left haa,Finset.sum_eq_single (⟨c,hNc⟩ : {d : J // N p.right d})]
    · simp only [hs,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,coefficient,hqs,haq]
      have hO : orient q.base = !(orient p.base) := by rw [← hb,ho]
      rw [hO]
      cases orient p.base <;> simp
    · intro d hd hdc
      have hn : c ≠ (d : J) := by
        intro h
        apply hdc
        exact Subtype.ext h.symm
      simp [hn]
    · simp
  · have hqs : step q.base=true := hsQ.trans hs
    have hpp : N p.left p.right := by simpa only [hs,Bool.false_eq_true,ite_false, if_false,ite_true, if_true] using (show (if step p.base then N p.left p.right else p.left=p.right) from p.property)
    have hqq : N q.left q.right := by simpa only [hqs,Bool.false_eq_true,ite_false, if_false,ite_true, if_true] using (show (if step q.base then N q.left q.right else q.left=q.right) from q.property)
    simp only [hs,ite_true, if_true,coefficient,hqs]
    have heq (f : J → K) :
        (∑ d : {d : J // N p.right d}, if N c d then f d else 0) =
          ∑ d ∈ GraphConnection.neighbors N p.right ∩ GraphConnection.neighbors N c, f d := by
      rw [← Finset.sum_subtype (GraphConnection.neighbors N p.right)
        (GraphConnection.mem_neighbors N p.right) (fun d => if N c d then f d else 0),
        ← Finset.sum_filter]
      congr 1
      ext d
      simp
    rw [heq (fun d => GraphConnection.crossing μ A p.left p.right c d * GraphConnection.crossing μ A q.left q.right d c)]
    simpa only [← hm] using GraphConnection.crossing_square N μ hμ δ A hA hroot hPF
      p.left q.right p.right c (hN hpp) (hm.symm ▸ hqq) (hN hc) (hN hc')

omit [Fintype V] in
lemma arrowImage_entry_product (orient : B → Bool) (μ : J → K) (A : K)
    (p q : StringArrow step N) (i j k : I)
    (hb : Q.reverse p.base=q.base) (hm : (U).target p=(U).source q)
    (hi : i.old=(U).source p) (hk : k.old=(U).target q) (hl : i.label=k.label) :
    arrowImage Q step hstep N hN orient μ A p i j *
      arrowImage Q step hstep N hN orient μ A q j k =
    if j.old=(U).target p then
      if (if step p.base then N i.label j.label else i.label=j.label) then
        (coefficient step N orient μ A p i.label j.label *
          coefficient step N orient μ A q j.label k.label) • Zigzag.tokenBasis U i.new
      else 0
    else 0 := by
  by_cases hj : j.old=(U).target p
  swap
  · rw [ite_eq_right hj,arrowImage_eq_zero_right Q step hstep N hN _ _ _ p i j hj,zero_mul]
  rw [ite_eq_left hj]
  unfold arrowImage
  have hpold : i.old=(U).source p ∧ j.old=(U).target p := ⟨hi,hj⟩
  have hqold : j.old=(U).source q ∧ k.old=(U).target q := ⟨hj.trans hm,hk⟩
  simp only [hi,hj,hk,hm,and_self,ite_true, if_true]
  by_cases hp' : (if step p.base then N i.label j.label else i.label=j.label)
  swap
  · simp only [dite_eq_right hp',ite_eq_right hp',zero_mul]
  simp only [dite_eq_left hp',ite_eq_left hp']
  have hq' : (if step q.base then N j.label k.label else j.label=k.label) := by
    rw [← hb,hstep,← hl]
    cases hs : step p.base <;> simp only [hs,Bool.false_eq_true,ite_false, if_false,ite_true, if_true] at hp' ⊢
    · exact hp'.symm
    · exact hN hp'
  rw [dite_eq_left hq',smul_mul_assoc,Algebra.mul_smul_comm,Zigzag.arrowBasis_mul_arrowBasis]
  have hr : (U).reverse (⟨(p.base,i.label,j.label),hp'⟩ : StringArrow step N) =
      ⟨(q.base,j.label,k.label),hq'⟩ :=
    (reverse_eq_iff Q step hstep N hN _ _).2 ⟨hb,rfl,hl⟩
  rw [ite_eq_left hr,smul_smul]
  congr 2
  apply Prod.ext
  · exact (congrArg Prod.fst hi).symm
  · rfl

lemma arrowImage_mul_arrowImage (orient : B → Bool)
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (μ : J → K) (hμ : ∀ a, μ a ≠ 0) (δ A : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (p q : StringArrow step N) :
    arrowImage Q step hstep N hN orient μ A p *
      arrowImage Q step hstep N hN orient μ A q =
      if (U).reverse p=q then tokenImage Q step hstep N hN μ ((U).source p) else 0 := by
  by_cases hb : Q.reverse p.base=q.base
  swap
  · rw [arrowImage_mul_of_not_reverse_base Q step hstep N hN _ _ _ _ _ hb]
    have hr : (U).reverse p ≠ q := fun hh => hb (congrArg StringArrow.base hh)
    rw [ite_eq_right hr]
  by_cases hm : (U).target p=(U).source q
  swap
  · rw [arrowImage_mul_of_not_composable Q step hstep N hN _ _ _ _ _ hm]
    rw [ite_eq_right (fun hh => hm (hh ▸ (U).source_reverse p).symm)]
  apply Matrix.ext
  intro i k
  by_cases hi : i.old=(U).source p
  swap
  · have hz : (arrowImage Q step hstep N hN orient μ A p *
        arrowImage Q step hstep N hN orient μ A q) i k = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro j hj
      rw [arrowImage_eq_zero_left Q step hstep N hN _ _ _ _ _ _ hi,zero_mul]
    rw [hz]
    split_ifs with hr
    · simp [tokenImage,hi]
    · rfl
  by_cases hk : k.old=(U).target q
  swap
  · have hz : (arrowImage Q step hstep N hN orient μ A p *
        arrowImage Q step hstep N hN orient μ A q) i k = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro j hj
      rw [arrowImage_eq_zero_right Q step hstep N hN _ _ _ _ _ _ hk,mul_zero]
    rw [hz]
    split_ifs with hr
    · have hik : i ≠ k := by
        intro H
        subst k
        apply hk
        rw [← hr,(U).target_reverse]
        exact hi
      simp [tokenImage,hik]
    · rfl
  by_cases hl : i.label=k.label
  swap
  · have hz : (arrowImage Q step hstep N hN orient μ A p *
        arrowImage Q step hstep N hN orient μ A q) i k = 0 := by
      rw [Matrix.mul_apply]
      exact Finset.sum_eq_zero (fun j _ => arrowImage_entry_mul_of_not_reverse
        Q step hstep N hN orient μ A p q i j k (Or.inr hl))
    rw [hz]
    split_ifs with hr
    · have hik : i ≠ k := fun H => hl (congrArg StringIndex.label H)
      simp [tokenImage,hik]
    · rfl
  have hc : N p.left i.label := by
    change N ((U).source p).2 i.label
    rw [← hi]
    exact i.property
  have hc' : N q.right i.label := by
    rw [hl]
    change N ((U).target q).2 k.label
    rw [← hk]
    exact k.property
  have hs : (arrowImage Q step hstep N hN orient μ A p *
        arrowImage Q step hstep N hN orient μ A q) i k =
      (if p.left=q.right then μ i.label / μ p.left else 0) • Zigzag.tokenBasis U i.new := by
    rw [Matrix.mul_apply]
    simp_rw [arrowImage_entry_product Q step hstep N hN orient μ A p q i _ k hb hm hi hk hl]
    rw [sum_over N ((U).target p)]
    change (∑ d : {d : J // N p.right d},
      if (if step p.base then N i.label d else i.label=d) then
        (coefficient step N orient μ A p i.label d * coefficient step N orient μ A q d k.label) •
          Zigzag.tokenBasis U i.new else 0) = _
    rw [← hl]
    have hscalar := coefficient_square Q step hstep N hN orient ho μ hμ δ A hA hroot hPF
      p q hb (congrArg Prod.snd hm) i.label hc hc'
    rw [← hscalar,Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro d hd
    split_ifs <;> simp
  rw [hs]
  by_cases ha : p.left=q.right
  · have hr : (U).reverse p=q := (reverse_eq_iff Q step hstep N hN p q).2
      ⟨hb,congrArg Prod.snd hm,ha⟩
    have hik : i=k := by
      apply StringIndex.ext
      · rw [hi,hk,← hr,(U).target_reverse]
      · exact hl
    subst k
    rw [ite_eq_left hr,ite_eq_left ha]
    change (μ i.label / μ p.left) • Zigzag.tokenBasis U i.new =
      tokenImage Q step hstep N hN μ ((U).source p) i i
    unfold tokenImage
    rw [ite_eq_left ⟨rfl,hi⟩]
    rfl
  · have hr : (U).reverse p ≠ q := fun H => ha (congrArg StringArrow.right H)
    simp [ha,hr]

noncomputable def pathImage (orient : B → Bool) (μ : J → K) (A : K) :
    Path (V × J) (StringArrow step N) → Matrix I I (Zigzag U K)
  | .inl a => unitImage Q step hstep N hN a
  | .inr (.inl p) => arrowImage Q step hstep N hN orient μ A p
  | .inr (.inr a) => tokenImage Q step hstep N hN μ a

noncomputable def linearMap (orient : B → Bool) (μ : J → K) (A : K) :
    Zigzag U K →ₗ[K] Matrix I I (Zigzag U K) :=
  (Zigzag.pathBasis U).constr K (pathImage Q step hstep N hN orient μ A)

@[simp] lemma linearMap_pathBasis (orient : B → Bool) (μ : J → K) (A : K)
    (p : Path (V × J) (StringArrow step N)) :
    linearMap Q step hstep N hN orient μ A (Zigzag.pathBasis U p) =
      pathImage Q step hstep N hN orient μ A p :=
  Module.Basis.constr_basis _ _ _ _

lemma pathImage_left (orient : B → Bool) (μ : J → K) (A : K)
    (p : Path (V × J) (StringArrow step N)) (i j : I) :
    Zigzag.vertexId U i.new * pathImage Q step hstep N hN orient μ A p i j =
      pathImage Q step hstep N hN orient μ A p i j := by
  rcases p with a|p|a
  · simp only [pathImage,unitImage]
    split_ifs <;> simp [Zigzag.vertexId_mul_self]
  · exact arrowImage_left Q step hstep N hN orient μ A p i j
  · simp only [pathImage,tokenImage]
    split_ifs
    · rw [Algebra.mul_smul_comm, ← Zigzag.pathBasis_token]
      exact congrArg ((μ i.label/μ a.2) • ·) (Zigzag.pathBasis_left U (.inr (.inr i.new)))
    · simp

lemma pathImage_right (orient : B → Bool) (μ : J → K) (A : K)
    (p : Path (V × J) (StringArrow step N)) (i j : I) :
    pathImage Q step hstep N hN orient μ A p i j * Zigzag.vertexId U j.new =
      pathImage Q step hstep N hN orient μ A p i j := by
  rcases p with a|p|a
  · simp only [pathImage,unitImage]
    split_ifs with h
    · rw [h.1]; exact Zigzag.vertexId_mul_self (K := K) U j.new
    · simp
  · exact arrowImage_right Q step hstep N hN orient μ A p i j
  · simp only [pathImage,tokenImage]
    split_ifs with h
    · rw [h.1,smul_mul_assoc, ← Zigzag.pathBasis_token]
      exact congrArg ((μ j.label/μ a.2) • ·) (Zigzag.pathBasis_right U (.inr (.inr j.new)))
    · simp

omit [Fintype V] in
lemma pathImage_support (orient : B → Bool) (μ : J → K) (A : K)
    (p : Path (V × J) (StringArrow step N)) (i j : I)
    (h : i.old ≠ Path.source U p ∨ j.old ≠ Path.target U p) :
    pathImage Q step hstep N hN orient μ A p i j = 0 := by
  rcases p with a|p|a
  · change (if i=j ∧ i.old=a then Zigzag.vertexId U i.new else 0) = 0
    rw [ite_eq_right]
    rintro ⟨rfl,ha⟩
    exact h.elim (fun H => H ha) (fun H => H ha)
  · change (if i.old=(U).source p ∧ j.old=(U).target p then _ else 0) = 0
    rw [ite_eq_right]
    rintro ⟨ha,hb⟩
    exact h.elim (fun H => H ha) (fun H => H hb)
  · change (if i=j ∧ i.old=a then (μ i.label/μ a.2) • Zigzag.tokenBasis U i.new else 0) = 0
    rw [ite_eq_right]
    rintro ⟨rfl,ha⟩
    exact h.elim (fun H => H ha) (fun H => H ha)

lemma unitImage_pathImage (orient : B → Bool) (μ : J → K) (A : K)
    (a : V × J) (p : Path (V × J) (StringArrow step N)) :
    unitImage Q step hstep N hN a * pathImage Q step hstep N hN orient μ A p =
    if Path.source U p = a then pathImage Q step hstep N hN orient μ A p else 0 := by
  apply Matrix.ext
  intro i j
  rw [unitImage_mul Q step hstep N hN a _ (pathImage_left Q step hstep N hN orient μ A p)]
  by_cases hp : Path.source U p=a
  · rw [ite_eq_left hp]
    by_cases hi : i.old=a
    · rw [ite_eq_left hi]
    · rw [ite_eq_right hi,pathImage_support Q step hstep N hN orient μ A p i j
        (Or.inl (by simpa [hp] using hi))]
  · rw [ite_eq_right hp]
    by_cases hi : i.old=a
    · rw [ite_eq_left hi,pathImage_support Q step hstep N hN orient μ A p i j
        (Or.inl (by simpa [hi,eq_comm] using hp))]; rfl
    · rw [ite_eq_right hi]; rfl

lemma pathImage_unitImage (orient : B → Bool) (μ : J → K) (A : K)
    (a : V × J) (p : Path (V × J) (StringArrow step N)) :
    pathImage Q step hstep N hN orient μ A p * unitImage Q step hstep N hN a =
    if Path.target U p = a then pathImage Q step hstep N hN orient μ A p else 0 := by
  apply Matrix.ext
  intro i j
  rw [mul_unitImage Q step hstep N hN a _ (pathImage_right Q step hstep N hN orient μ A p)]
  by_cases hp : Path.target U p=a
  · rw [ite_eq_left hp]
    by_cases hi : j.old=a
    · rw [ite_eq_left hi]
    · rw [ite_eq_right hi,pathImage_support Q step hstep N hN orient μ A p i j
        (Or.inr (by simpa [hp] using hi))]
  · rw [ite_eq_right hp]
    by_cases hi : j.old=a
    · rw [ite_eq_left hi,pathImage_support Q step hstep N hN orient μ A p i j
        (Or.inr (by simpa [hi,eq_comm] using hp))]; rfl
    · rw [ite_eq_right hi]; rfl

omit [Fintype V] in
lemma pathImage_positive (orient : B → Bool) (μ : J → K) (A : K)
    (p : Path (V × J) (StringArrow step N)) (hp : Path.length p ≠ 0) (i j : I) :
    (pathImage Q step hstep N hN orient μ A p i j).vertex = 0 := by
  rcases p with a|p|a
  · exact (hp rfl).elim
  · simp only [pathImage,arrowImage]
    split_ifs <;> simp only [Zigzag.vertex_smul,Zigzag.vertex_zero]
    all_goals change (_ : K) • (0 : V × J → K) = 0
    all_goals exact smul_zero _
  · simp only [pathImage,tokenImage]
    split_ifs <;> simp only [Zigzag.vertex_smul,Zigzag.vertex_zero]
    all_goals change (_ : K) • (0 : V × J → K) = 0
    all_goals exact smul_zero _

lemma tokenImage_pathImage (orient : B → Bool) (μ : J → K) (A : K)
    (a : V × J) (p : Path (V × J) (StringArrow step N)) (hp : Path.length p ≠ 0) :
    tokenImage Q step hstep N hN μ a * pathImage Q step hstep N hN orient μ A p = 0 := by
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k hk
  unfold tokenImage
  split_ifs
  · rw [smul_mul_assoc,Zigzag.tokenBasis_mul_positive U _ _
      (pathImage_positive Q step hstep N hN orient μ A p hp k j),smul_zero]
  · exact zero_mul _

lemma pathImage_tokenImage (orient : B → Bool) (μ : J → K) (A : K)
    (a : V × J) (p : Path (V × J) (StringArrow step N)) (hp : Path.length p ≠ 0) :
    pathImage Q step hstep N hN orient μ A p * tokenImage Q step hstep N hN μ a = 0 := by
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k hk
  unfold tokenImage
  split_ifs
  · rw [Algebra.mul_smul_comm,Zigzag.positive_mul_tokenBasis U _ _
      (pathImage_positive Q step hstep N hN orient μ A p hp i k),smul_zero]
  · exact mul_zero _

lemma linearMap_mul (orient : B → Bool)
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (μ : J → K) (hμ : ∀ a, μ a ≠ 0) (δ A : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (x y : Zigzag U K) :
    linearMap Q step hstep N hN orient μ A (x*y) =
      linearMap Q step hstep N hN orient μ A x * linearMap Q step hstep N hN orient μ A y := by
  apply Zigzag.map_mul_of_pathBasis
  intro p q
  rw [linearMap_pathBasis,linearMap_pathBasis]
  rcases p with a|p|a
  · rw [Zigzag.pathBasis_vertex,Zigzag.vertexId_mul_pathBasis]
    simp only [apply_ite,map_zero,linearMap_pathBasis,pathImage]
    exact (unitImage_pathImage Q step hstep N hN orient μ A a q).symm
  · rcases q with b|q|b
    · rw [Zigzag.pathBasis_vertex,Zigzag.pathBasis_mul_vertexId]
      simp only [apply_ite,map_zero,linearMap_pathBasis]
      exact (pathImage_unitImage Q step hstep N hN orient μ A b (.inr (.inl p))).symm
    · rw [Zigzag.pathBasis_arrow,Zigzag.pathBasis_arrow,Zigzag.arrowBasis_mul_arrowBasis]
      simp only [apply_ite,map_zero, ← Zigzag.pathBasis_token,linearMap_pathBasis,pathImage]
      exact (arrowImage_mul_arrowImage Q step hstep N hN orient ho μ hμ δ A hA hroot hPF p q).symm
    · rw [Zigzag.pathBasis_arrow,Zigzag.pathBasis_token,
        Zigzag.positive_mul_tokenBasis U b _ rfl,map_zero]
      exact (pathImage_tokenImage Q step hstep N hN orient μ A b (.inr (.inl p)) (by norm_num [Path.length])).symm
  · rcases q with b|q|b
    · rw [Zigzag.pathBasis_vertex,Zigzag.pathBasis_mul_vertexId]
      simp only [apply_ite,map_zero,linearMap_pathBasis]
      exact (pathImage_unitImage Q step hstep N hN orient μ A b (.inr (.inr a))).symm
    · rw [Zigzag.pathBasis_token,Zigzag.pathBasis_arrow,
        Zigzag.tokenBasis_mul_positive U a _ rfl,map_zero]
      exact (tokenImage_pathImage Q step hstep N hN orient μ A a (.inr (.inl q)) (by norm_num [Path.length])).symm
    · rw [Zigzag.pathBasis_token,Zigzag.pathBasis_token,
        Zigzag.tokenBasis_mul_positive U a _ rfl,map_zero]
      exact (tokenImage_pathImage Q step hstep N hN orient μ A a (.inr (.inr b)) (by norm_num [Path.length])).symm

end StringFunctor
end HarmonicArtin.ReversibleQuiver

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_BasePath
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor

variable {V B J K : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  (orient : B → Bool) (μ : J → K) (A : K)

local notation "U" => Q.stringQuiver step hstep N hN

def basePath : Path (V × J) (StringArrow step N) → Path V B
  | .inl v => .inl v.1
  | .inr (.inl e) => .inr (.inl e.base)
  | .inr (.inr v) => .inr (.inr v.1)

lemma basePath_source (p : Path (V × J) (StringArrow step N)) :
    Path.source Q (basePath step N p) = (Path.source U p).1 := by
  rcases p with v|e|v <;> rfl
lemma basePath_target (p : Path (V × J) (StringArrow step N)) :
    Path.target Q (basePath step N p) = (Path.target U p).1 := by
  rcases p with v|e|v <;> rfl
lemma basePath_length (p : Path (V × J) (StringArrow step N)) :
    Path.length (basePath step N p) = Path.length p := by
  rcases p with v|e|v <;> rfl

def liftPath (p : Path V B) (a b : J)
    (h : if pathMarked step p then N a b else a=b) : Path (V × J) (StringArrow step N) :=
  match p with
  | .inl v => .inl (v,a)
  | .inr (.inl e) => .inr (.inl ⟨(e,a,b),h⟩)
  | .inr (.inr v) => .inr (.inr (v,a))

lemma liftPath_source (p : Path V B) (a b : J)
    (h : if pathMarked step p then N a b else a=b) :
    Path.source U (liftPath step N p a b h) = (Path.source Q p,a) := by
  rcases p with v|e|v <;> rfl

lemma liftPath_target (p : Path V B) (a b : J)
    (h : if pathMarked step p then N a b else a=b) :
    Path.target U (liftPath step N p a b h) = (Path.target Q p,b) := by
  rcases p with v|e|v
  · exact Prod.ext rfl h
  · rfl
  · exact Prod.ext rfl h

lemma basePath_liftPath (p : Path V B) (a b : J)
    (h : if pathMarked step p then N a b else a=b) :
    basePath step N (liftPath step N p a b h) = p := by
  rcases p with v|e|v <;> rfl

lemma path_allowed (p : Path (V × J) (StringArrow step N)) :
    if pathMarked step (basePath step N p) then N (Path.source U p).2 (Path.target U p).2
      else (Path.source U p).2=(Path.target U p).2 := by
  rcases p with v|e|v
  · rfl
  · exact e.property
  · rfl

lemma liftPath_basePath (p : Path (V × J) (StringArrow step N)) :
    liftPath step N (basePath step N p) (Path.source U p).2 (Path.target U p).2
      (path_allowed Q step hstep N hN p) = p := by
  rcases p with v|e|v
  · rfl
  · congr 2
  · rfl

abbrev LeftPaths (u t : V) (b c : J) :=
  (a : {a : J // N a c}) × Zigzag.CornerPath U (u,a) (t,b)

abbrev RightPaths (u t : V) (b c : J) :=
  (d : {d : J // N b d}) × Zigzag.CornerPath U (u,c) (t,d)

def leftPathsEquiv (u t : V) (b c : J) :
    LeftPaths Q step hstep N hN u t b c ≃
      ((p : Zigzag.CornerPath Q u t) × PathLeft step N p.val b c) where
  toFun x :=
    ⟨⟨basePath step N x.2.val,by
      constructor
      · rw [basePath_source Q step hstep N hN,x.2.property.1]
      · rw [basePath_target Q step hstep N hN,x.2.property.2]⟩,
      ⟨x.1,⟨by
        have hp := path_allowed Q step hstep N hN x.2.val
        simpa only [x.2.property.1,x.2.property.2] using hp,x.1.property⟩⟩⟩
  invFun x :=
    ⟨⟨x.2,x.2.property.2⟩,
      ⟨liftPath step N x.1.val x.2 b x.2.property.1,by
        constructor
        · rw [liftPath_source,x.1.property.1]
        · rw [liftPath_target,x.1.property.2]⟩⟩
  left_inv x := by
    dsimp only
    refine Sigma.ext (Subtype.ext rfl) ?_
    apply heq_of_eq
    apply Subtype.ext
    have hp := liftPath_basePath Q step hstep N hN x.2.val
    simpa only [x.2.property.1,x.2.property.2] using hp
  right_inv x := by
    apply Sigma.ext (Subtype.ext (basePath_liftPath step N _ _ _ _))
    cases x with
    | mk p a =>
      cases p with
      | mk p hp =>
        rcases p with v|e|v <;> rfl

def rightPathsEquiv (u t : V) (b c : J) :
    RightPaths Q step hstep N hN u t b c ≃
      ((p : Zigzag.CornerPath Q u t) × PathRight step N p.val b c) where
  toFun x :=
    ⟨⟨basePath step N x.2.val,by
      constructor
      · rw [basePath_source Q step hstep N hN,x.2.property.1]
      · rw [basePath_target Q step hstep N hN,x.2.property.2]⟩,
      ⟨x.1,⟨x.1.property,by
        have hp := path_allowed Q step hstep N hN x.2.val
        simpa only [x.2.property.1,x.2.property.2] using hp⟩⟩⟩
  invFun x :=
    ⟨⟨x.2,x.2.property.1⟩,
      ⟨liftPath step N x.1.val c x.2 x.2.property.2,by
        constructor
        · rw [liftPath_source,x.1.property.1]
        · rw [liftPath_target,x.1.property.2]⟩⟩
  left_inv x := by
    dsimp only
    refine Sigma.ext (Subtype.ext rfl) ?_
    apply heq_of_eq
    apply Subtype.ext
    have hp := liftPath_basePath Q step hstep N hN x.2.val
    simpa only [x.2.property.1,x.2.property.2] using hp
  right_inv x := by
    apply Sigma.ext (Subtype.ext (basePath_liftPath step N _ _ _ _))
    cases x with
    | mk p a =>
      cases p with
      | mk p hp =>
        rcases p with v|e|v <;> rfl

def leftPathIndex (p : Path V B) (b c : J) (a : PathLeft step N p b c) :
    StringIndex (V := V) N := ⟨((Path.source Q p,a),c),a.property.2⟩

def rightPathIndex (p : Path V B) (b c : J) (d : PathRight step N p b c) :
    StringIndex (V := V) N := ⟨((Path.target Q p,b),d),d.property.1⟩

variable [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]

lemma linearMap_liftPath (p : Path V B) (b c : J)
    (a : PathLeft step N p b c) (d : PathRight step N p b c) :
    linearMap Q step hstep N hN orient μ A
      (Zigzag.pathBasis U (liftPath step N p a b a.property.1))
      (leftPathIndex Q step N p b c a) (rightPathIndex Q step N p b c d) =
    pathSwitch step N orient μ A p b c a d •
      Zigzag.pathBasis U (liftPath step N p c d d.property.2) := by
  rw [linearMap_pathBasis]
  rcases p with v|e|v
  · have ha : a.val=b := a.property.1
    have hd : c=d.val := d.property.2
    have hi : leftPathIndex Q step N (.inl v) b c a = rightPathIndex Q step N (.inl v) b c d := by
      apply StringIndex.ext
      · exact Prod.ext rfl ha
      · exact hd
    simp only [liftPath,pathImage,unitImage,pathSwitch,Zigzag.pathBasis_vertex]
    rw [ite_eq_left ⟨hi,rfl⟩]
    change Zigzag.vertexId U (v,c) = (1 : K) • Zigzag.vertexId U (v,c)
    rw [one_smul]
  · simp only [liftPath,pathImage,arrowImage]
    rw [ite_eq_left ⟨rfl,rfl⟩]
    change (if h : (if step e then N c d else c=d) then
      coefficient step N orient μ A ⟨(e,a.val,b),a.property.1⟩ c d •
        Zigzag.arrowBasis (K := K) U ⟨(e,c,d.val),h⟩ else 0) = _
    rw [dite_eq_left (show (if step e then N c d else c=d) from d.property.2)]
    rw [Zigzag.pathBasis_arrow]
    change coefficient step N orient μ A ⟨(e,a.val,b),a.property.1⟩ c d •
      Zigzag.arrowBasis (K := K) U ⟨(e,c,d.val),d.property.2⟩ =
      pathSwitch step N orient μ A (.inr (.inl e)) b c a d •
        Zigzag.arrowBasis (K := K) U ⟨(e,c,d.val),d.property.2⟩
    congr 1
    rw [pathSwitch,GraphConnection.sectorSwitch_apply]
    cases he : step e
    · have ha : a.val=b := by simpa [pathMarked,he] using a.property.1
      have hd : c=d.val := by simpa [pathMarked,he] using d.property.2
      simp only [coefficient,pathMarked,pathScalar,he,Bool.false_eq_true,↓reduceIte,
        StringArrow.base,StringArrow.left,ha,← hd]
    · simp only [coefficient,pathMarked,he,↓reduceIte,
        StringArrow.base,StringArrow.left,StringArrow.right]
  · have ha : a.val=b := a.property.1
    have hd : c=d.val := d.property.2
    have hi : leftPathIndex Q step N (.inr (.inr v)) b c a = rightPathIndex Q step N (.inr (.inr v)) b c d := by
      apply StringIndex.ext
      · exact Prod.ext rfl ha
      · exact hd
    simp only [liftPath,pathImage,tokenImage,pathSwitch,Zigzag.pathBasis_token]
    rw [ite_eq_left ⟨hi,rfl⟩]
    change (μ c / μ a) • Zigzag.tokenBasis U (v,c) =
      (μ c / μ b) • Zigzag.tokenBasis U (v,c)
    rw [ha]

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_Index
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor

variable {V B J K : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)

local notation "U" => Q.stringQuiver step hstep N hN
local notation "I" => StringIndex (V := V) N
local notation "F" => linearMap Q step hstep N hN orient μ A
local notation "P" => pathImage Q step hstep N hN orient μ A

lemma linearMap_apply (x : Zigzag U K) (i j : I) :
    F x i j = ∑ p, Zigzag.pathCoordinates U x p • P p i j := by
  conv_lhs => rw [← Zigzag.sum_pathBasis U x]
  simp only [map_sum,map_smul,linearMap_pathBasis,Matrix.sum_apply,Matrix.smul_apply]

lemma linearMap_left (x : Zigzag U K) (i j : I) :
    Zigzag.vertexId U i.new * F x i j = F x i j := by
  rw [linearMap_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Algebra.mul_smul_comm,pathImage_left]

lemma linearMap_right (x : Zigzag U K) (i j : I) :
    F x i j * Zigzag.vertexId U j.new = F x i j := by
  rw [linearMap_apply,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [smul_mul_assoc,pathImage_right]

lemma pathImage_homogeneous (p : Path (V × J) (StringArrow step N)) (i j : I) :
    Zigzag.Homogeneous U (Path.length p) (P p i j) := by
  rcases p with a|p|a
  · simp only [pathImage,unitImage,Path.length]
    split_ifs
    · exact Zigzag.homogeneous_vertexId U _
    · exact Zigzag.homogeneous_zero U _
  · simp only [pathImage,arrowImage,Path.length]
    split_ifs
    all_goals first | exact Zigzag.homogeneous_zero U _ |
      exact Zigzag.homogeneous_smul U (by
        rw [← Zigzag.pathBasis_arrow]
        exact Zigzag.pathBasis_homogeneous (K := K) U (.inr (.inl _))) _
  · simp only [pathImage,tokenImage,Path.length]
    split_ifs
    · exact Zigzag.homogeneous_smul U (by
        rw [← Zigzag.pathBasis_token]
        exact Zigzag.pathBasis_homogeneous (K := K) U (.inr (.inr i.new))) _
    · exact Zigzag.homogeneous_zero U _

lemma linearMap_homogeneous {x : Zigzag U K} {a : ℤ}
    (hx : Zigzag.Homogeneous U a x) (i j : I) :
    Zigzag.Homogeneous U a (F x i j) := by
  rw [linearMap_apply]
  apply Zigzag.homogeneous_sum
  intro p hp
  by_cases ha : Path.length p=a
  · rw [← ha]
    exact Zigzag.homogeneous_smul U
      (pathImage_homogeneous Q step hstep N hN orient μ A p i j) _
  · rw [(Zigzag.coordinates_homogeneous U a x).1 hx p ha,zero_smul]
    exact Zigzag.homogeneous_zero U _

lemma linearMap_support {x : Zigzag U K} {a b : V × J}
    (hx : Zigzag.vertexId U a * x = x) (hy : x * Zigzag.vertexId U b = x)
    (i j : I) (h : i.old ≠ a ∨ j.old ≠ b) : F x i j = 0 := by
  rw [linearMap_apply]
  apply Finset.sum_eq_zero
  intro p hp
  by_cases hc : Zigzag.pathCoordinates U x p=0
  · rw [hc,zero_smul]
  · have hs := Zigzag.coordinates_corner U hx hy hc
    rw [pathImage_support Q step hstep N hN orient μ A p i j (by simpa [hs.1,hs.2] using h),smul_zero]

def indexEmbed {T : Type*} (p : T → GeneratorPlacement (V × J))
    (i : Index N p) : I := ⟨((p i.1).color,i.2),i.2.property⟩

noncomputable def matrix {T R : Type*} (p : T → GeneratorPlacement (V × J))
    (q : R → GeneratorPlacement (V × J)) (M : Matrix T R (Zigzag U K)) :
    Matrix (Index N p) (Index N q) (Zigzag U K) :=
  fun i j => F (M i.1 j.1) (indexEmbed N p i) (indexEmbed N q j)

lemma matrix_zero {T R : Type*} (p : T → GeneratorPlacement (V × J))
    (q : R → GeneratorPlacement (V × J)) :
    matrix Q step hstep N hN orient μ A p q 0 = 0 := by
  apply Matrix.ext
  intro i j
  exact congrFun (congrFun ((F).map_zero) (indexEmbed N p i)) (indexEmbed N q j)

lemma matrix_add {T R : Type*} (p : T → GeneratorPlacement (V × J))
    (q : R → GeneratorPlacement (V × J)) (M L : Matrix T R (Zigzag U K)) :
    matrix Q step hstep N hN orient μ A p q (M+L) =
      matrix Q step hstep N hN orient μ A p q M + matrix Q step hstep N hN orient μ A p q L := by
  apply Matrix.ext
  intro i j
  exact congrFun (congrFun ((F).map_add (M i.1 j.1) (L i.1 j.1)) (indexEmbed N p i)) (indexEmbed N q j)

lemma matrix_entries {T R : Type*} (p : T → GeneratorPlacement (V × J))
    (q : R → GeneratorPlacement (V × J)) (M : Matrix T R (Zigzag U K)) :
    Zigzag.ProjectiveEntries U (placement N p) (placement N q)
      (matrix Q step hstep N hN orient μ A p q M) := by
  constructor
  · intro i j
    exact linearMap_left Q step hstep N hN orient μ A (M i.1 j.1) (indexEmbed N p i) (indexEmbed N q j)
  · intro i j
    exact linearMap_right Q step hstep N hN orient μ A (M i.1 j.1) (indexEmbed N p i) (indexEmbed N q j)

lemma matrix_degree {T R : Type*} (p : T → GeneratorPlacement (V × J))
    (q : R → GeneratorPlacement (V × J)) (M : Matrix T R (Zigzag U K)) {n v : ℤ}
    (hM : Zigzag.MapDegree U p q n v M) :
    Zigzag.MapDegree U (placement N p) (placement N q) n v
      (matrix Q step hstep N hN orient μ A p q M) := by
  intro i j
  constructor
  · intro h
    have hz := (hM i.1 j.1).1 h
    change F (M i.1 j.1) _ _ = 0
    rw [hz,map_zero]; rfl
  · exact linearMap_homogeneous Q step hstep N hN orient μ A (hM i.1 j.1).2 _ _

lemma matrix_mul {T R L : Type*} [Fintype R]
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (p : T → GeneratorPlacement (V × J)) (q : R → GeneratorPlacement (V × J))
    (r : L → GeneratorPlacement (V × J))
    (M : Matrix T R (Zigzag U K)) (D : Matrix R L (Zigzag U K))
    (hM : Zigzag.ProjectiveEntries U p q M) :
    matrix Q step hstep N hN orient μ A p r (M*D) =
      matrix Q step hstep N hN orient μ A p q M * matrix Q step hstep N hN orient μ A q r D := by
  apply Matrix.ext
  intro i k
  simp only [matrix,Matrix.mul_apply,map_sum,Matrix.sum_apply]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j hj
  rw [linearMap_mul Q step hstep N hN orient ho μ hμ δ A hA hroot hPF,Matrix.mul_apply]
  have hh : ∀ l : I,
      F (M i.1 j) (indexEmbed N p i) l * F (D j k.1) l (indexEmbed N r k) =
      if l.old=(q j).color then
        F (M i.1 j) (indexEmbed N p i) l * F (D j k.1) l (indexEmbed N r k) else 0 := by
    intro l
    by_cases hl : l.old=(q j).color
    · exact (ite_eq_left hl).symm
    · rw [ite_eq_right hl,linearMap_support Q step hstep N hN orient μ A (hM.1 _ _) (hM.2 _ _)
        _ l (Or.inr hl),zero_mul]
  rw [Finset.sum_congr rfl (fun l _ => hh l)]
  rw [sum_over N ((q j).color)]
  rfl

lemma matrix_identity {T : Type*} [DecidableEq T]
    (p : T → GeneratorPlacement (V × J)) :
    matrix Q step hstep N hN orient μ A p p (Zigzag.projectiveIdentity U p) =
      Zigzag.projectiveIdentity U (placement N p) := by
  apply Matrix.ext
  rintro ⟨i,c⟩ ⟨j,d⟩
  by_cases hij : i=j
  · subst j
    by_cases hcd : c=d
    · subst d
      simp only [matrix,Zigzag.projectiveIdentity,Matrix.diagonal_apply,ite_true, if_true,
        ← Zigzag.pathBasis_vertex,linearMap_pathBasis,pathImage,unitImage]
      rw [ite_eq_left (by simp [indexEmbed,StringIndex.old])]
      simp only [Zigzag.pathBasis_vertex]
      rfl
    · have hind : (⟨i,c⟩ : Index N p) ≠ ⟨i,d⟩ := by simpa using hcd
      have hem : indexEmbed N p ⟨i,c⟩ ≠ indexEmbed N p ⟨i,d⟩ := by
        intro he
        apply hcd
        exact Subtype.ext (congrArg StringIndex.label he)
      simp only [matrix,Zigzag.projectiveIdentity,Matrix.diagonal_apply,ite_true, if_true,ite_eq_right hind,
        ← Zigzag.pathBasis_vertex,linearMap_pathBasis,pathImage,unitImage]
      rw [ite_eq_right (fun h => hem h.1)]
  · have hind : (⟨i,c⟩ : Index N p) ≠ ⟨j,d⟩ := fun h => hij (congrArg Sigma.fst h)
    simp only [matrix,Zigzag.projectiveIdentity,Matrix.diagonal_apply,ite_eq_right hij,ite_eq_right hind,map_zero]
    rfl

noncomputable def complex {T : Type*} [Fintype T]
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (E : Zigzag.BasedComplex U (K := K) T) :
    Zigzag.BasedComplex U (K := K) (Index N E.placement) where
  placement := placement N E.placement
  differential := matrix Q step hstep N hN orient μ A _ _ E.differential
  entries := matrix_entries Q step hstep N hN orient μ A _ _ _
  degree := matrix_degree Q step hstep N hN orient μ A _ _ _ E.degree
  square_zero := by
    rw [← matrix_mul Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
      E.placement E.placement E.placement E.differential E.differential E.entries]
    rw [E.square_zero,matrix_zero]

section Functorial
variable (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    {T R L : Type*} [Fintype T] [Fintype R] [Fintype L]

local notation "C" => complex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
local notation "M" => matrix Q step hstep N hN orient μ A

noncomputable def map {E : Zigzag.BasedComplex U (K := K) T}
    {D : Zigzag.BasedComplex U (K := K) R} (f : Zigzag.BasedComplex.Map U E D) :
    Zigzag.BasedComplex.Map U (C E) (C D) where
  matrix := M E.placement D.placement f.matrix
  entries := matrix_entries Q step hstep N hN orient μ A _ _ _
  degree := matrix_degree Q step hstep N hN orient μ A _ _ _ f.degree
  commute := by
    change M _ _ E.differential * M _ _ f.matrix = M _ _ f.matrix * M _ _ D.differential
    rw [← matrix_mul Q step hstep N hN orient μ A ho hμ δ hA hroot hPF _ _ _ _ _ E.entries,
      ← matrix_mul Q step hstep N hN orient μ A ho hμ δ hA hroot hPF _ _ _ _ _ f.entries,
      f.commute]

noncomputable def homotopyEquivalence [DecidableEq T] [DecidableEq R]
    {E : Zigzag.BasedComplex U (K := K) T} {D : Zigzag.BasedComplex U (K := K) R}
    (h : Zigzag.BasedComplex.HomotopyEquivalence U E D) :
    Zigzag.BasedComplex.HomotopyEquivalence U (C E) (C D) where
  forward := map Q step hstep N hN orient μ A ho hμ δ hA hroot hPF h.forward
  backward := map Q step hstep N hN orient μ A ho hμ δ hA hroot hPF h.backward
  sourceHomotopy := M E.placement E.placement h.sourceHomotopy
  targetHomotopy := M D.placement D.placement h.targetHomotopy
  sourceEntries := matrix_entries Q step hstep N hN orient μ A _ _ _
  targetEntries := matrix_entries Q step hstep N hN orient μ A _ _ _
  sourceDegree := matrix_degree Q step hstep N hN orient μ A _ _ _ h.sourceDegree
  targetDegree := matrix_degree Q step hstep N hN orient μ A _ _ _ h.targetDegree
  sourceEquation := by
    change M _ _ h.forward.matrix * M _ _ h.backward.matrix = _
    rw [← matrix_mul Q step hstep N hN orient μ A ho hμ δ hA hroot hPF _ _ _ _ _ h.forward.entries,
      h.sourceEquation,matrix_add,matrix_add,matrix_identity,
      matrix_mul Q step hstep N hN orient μ A ho hμ δ hA hroot hPF _ _ _ _ _ E.entries,
      matrix_mul Q step hstep N hN orient μ A ho hμ δ hA hroot hPF _ _ _ _ _ h.sourceEntries]
    rfl
  targetEquation := by
    change M _ _ h.backward.matrix * M _ _ h.forward.matrix = _
    rw [← matrix_mul Q step hstep N hN orient μ A ho hμ δ hA hroot hPF _ _ _ _ _ h.backward.entries,
      h.targetEquation,matrix_add,matrix_add,matrix_identity,
      matrix_mul Q step hstep N hN orient μ A ho hμ δ hA hroot hPF _ _ _ _ _ D.entries,
      matrix_mul Q step hstep N hN orient μ A ho hμ δ hA hroot hPF _ _ _ _ _ h.targetEntries]
    rfl
end Functorial

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_ConeIndexEquiv
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
attribute [local instance] Classical.propDecidable
variable {V B J K T R : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)
local notation "U" => Q.stringQuiver step hstep N hN
local notation "L" => linearMap Q step hstep N hN orient μ A
variable [Fintype T] [Fintype R] [DecidableEq T] [DecidableEq R]
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
local notation "C" => complex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
local notation "M" => map Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

def coneIndexEquiv {E : Zigzag.BasedComplex U (K := K) T}
    {D : Zigzag.BasedComplex U (K := K) R} (f : Zigzag.BasedComplex.Map U E D) :
    Index N E.placement ⊕ Index N D.placement ≃ Index N (Zigzag.BasedComplex.Map.cone U (I := T) (J := R) (E := E) (F := D) f).placement where
  toFun
    | .inl ⟨i,c⟩ => ⟨.inl i,c⟩
    | .inr ⟨i,c⟩ => ⟨.inr i,c⟩
  invFun
    | ⟨.inl i,c⟩ => .inl ⟨i,c⟩
    | ⟨.inr i,c⟩ => .inr ⟨i,c⟩
  left_inv i := by rcases i with ⟨i,c⟩|⟨i,c⟩ <;> rfl
  right_inv i := by rcases i with ⟨i,c⟩; cases i <;> rfl

omit [DecidableEq T] [DecidableEq R] in
lemma cone_complex_eq {E : Zigzag.BasedComplex U (K := K) T}
    {D : Zigzag.BasedComplex U (K := K) R} (f : Zigzag.BasedComplex.Map U E D) :
    (C (Zigzag.BasedComplex.Map.cone U (I := T) (J := R) (E := E) (F := D) f)).reindex U (coneIndexEquiv Q step hstep N hN f) = (M f).cone U := by
  apply Zigzag.BasedComplex.ext_placement_differential
  · funext i
    rcases i with ⟨i,c⟩|⟨i,c⟩ <;> rfl
  · apply Matrix.ext
    intro i j
    rcases i with ⟨i,c⟩|⟨i,c⟩ <;> rcases j with ⟨j,d⟩|⟨j,d⟩
    · change L (-E.differential i j) (indexEmbed N E.placement ⟨i,c⟩)
          (indexEmbed N E.placement ⟨j,d⟩) =
        -(L (E.differential i j) (indexEmbed N E.placement ⟨i,c⟩)
          (indexEmbed N E.placement ⟨j,d⟩))
      simp only [map_neg,Matrix.neg_apply]
    · rfl
    · change L 0 _ _ = 0
      simp only [map_zero,Matrix.zero_apply]
    · rfl

noncomputable def coneComparison {E : Zigzag.BasedComplex U (K := K) T}
    {D : Zigzag.BasedComplex U (K := K) R} (f : Zigzag.BasedComplex.Map U E D) :
    Zigzag.BasedComplex.ChainIsomorphism U (C (Zigzag.BasedComplex.Map.cone U (I := T) (J := R) (E := E) (F := D) f)) ((M f).cone U (E := C E) (F := C D)) := by
  rw [← cone_complex_eq Q step hstep N hN orient μ A ho hμ δ hA hroot hPF f]
  exact Zigzag.BasedComplex.reindexChainIsomorphism U _ (coneIndexEquiv Q step hstep N hN f)

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_PathSwitchEquiv
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
variable {V B J K : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)

noncomputable def pathSwitchEquiv (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (p : Path V B) (b c : J) :
    (PathLeft step N p b c → K) ≃ₗ[K] (PathRight step N p b c → K) where
  toFun := fun x => Matrix.vecMul x (pathSwitch step N orient μ A p b c)
  invFun := fun y => Matrix.vecMul y (pathUnswitch step N orient μ A p b c)
  left_inv x := by
    dsimp only
    rw [Matrix.vecMul_vecMul,pathSwitch_inverse step N hN orient μ A hμ δ hA hroot hPF,
      Matrix.vecMul_one]
  right_inv x := by
    dsimp only
    rw [Matrix.vecMul_vecMul,pathUnswitch_inverse step N hN orient μ A hμ δ hA hroot hPF,
      Matrix.vecMul_one]
  map_add' x y := Matrix.add_vecMul _ x y
  map_smul' a x := Matrix.smul_vecMul a x _

noncomputable def leftSectors (u t : V) (b c : J) :
    (LeftPaths Q step hstep N hN u t b c → K) ≃ₗ[K]
      ((p : Zigzag.CornerPath Q u t) → PathLeft step N p.val b c → K) where
  toFun x p a := x ((leftPathsEquiv Q step hstep N hN u t b c).symm ⟨p,a⟩)
  invFun x a := Sigma.uncurry x (leftPathsEquiv Q step hstep N hN u t b c a)
  left_inv x := by
    funext a
    change x ((leftPathsEquiv Q step hstep N hN u t b c).symm
      (leftPathsEquiv Q step hstep N hN u t b c a)) = x a
    rw [Equiv.symm_apply_apply]
  right_inv x := by
    funext p a
    change Sigma.uncurry x ((leftPathsEquiv Q step hstep N hN u t b c)
      ((leftPathsEquiv Q step hstep N hN u t b c).symm ⟨p,a⟩)) = x p a
    rw [Equiv.apply_symm_apply]
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def rightSectors (u t : V) (b c : J) :
    (RightPaths Q step hstep N hN u t b c → K) ≃ₗ[K]
      ((p : Zigzag.CornerPath Q u t) → PathRight step N p.val b c → K) where
  toFun x p a := x ((rightPathsEquiv Q step hstep N hN u t b c).symm ⟨p,a⟩)
  invFun x a := Sigma.uncurry x (rightPathsEquiv Q step hstep N hN u t b c a)
  left_inv x := by
    funext a
    change x ((rightPathsEquiv Q step hstep N hN u t b c).symm
      (rightPathsEquiv Q step hstep N hN u t b c a)) = x a
    rw [Equiv.symm_apply_apply]
  right_inv x := by
    funext p a
    change Sigma.uncurry x ((rightPathsEquiv Q step hstep N hN u t b c)
      ((rightPathsEquiv Q step hstep N hN u t b c).symm ⟨p,a⟩)) = x p a
    rw [Equiv.apply_symm_apply]
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def linearSwitch (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (u t : V) (b c : J) :
    (LeftPaths Q step hstep N hN u t b c → K) ≃ₗ[K]
      (RightPaths Q step hstep N hN u t b c → K) :=
  (leftSectors Q step hstep N hN u t b c).trans
    ((LinearEquiv.piCongrRight (fun p : Zigzag.CornerPath Q u t =>
      pathSwitchEquiv step N hN orient μ A hμ δ hA hroot hPF p.val b c)).trans
        (rightSectors Q step hstep N hN u t b c).symm)

omit [Fintype V] [Fintype B] [DecidableEq V] [DecidableEq B] in
lemma linearSwitch_sector (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (u t : V) (b c : J) (x : LeftPaths Q step hstep N hN u t b c → K)
    (p : Zigzag.CornerPath Q u t) (d : PathRight step N p.val b c) :
    linearSwitch Q step hstep N hN orient μ A hμ δ hA hroot hPF u t b c x
      ((rightPathsEquiv Q step hstep N hN u t b c).symm ⟨p,d⟩) =
      ∑ a : PathLeft step N p.val b c,
        x ((leftPathsEquiv Q step hstep N hN u t b c).symm ⟨p,a⟩) *
          pathSwitch step N orient μ A p.val b c a d := by
  change Sigma.uncurry
    ((LinearEquiv.piCongrRight (fun p : Zigzag.CornerPath Q u t =>
      pathSwitchEquiv step N hN orient μ A hμ δ hA hroot hPF p.val b c))
        (leftSectors Q step hstep N hN u t b c x))
    ((rightPathsEquiv Q step hstep N hN u t b c)
    ((rightPathsEquiv Q step hstep N hN u t b c).symm ⟨p,d⟩)) = _
  rw [Equiv.apply_symm_apply]
  rfl

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_Evaluation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
variable {V B J K : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)

local notation "U" => Q.stringQuiver step hstep N hN
local notation "I" => StringIndex (V := V) N
local notation "F" => linearMap Q step hstep N hN orient μ A

lemma pathImage_single (p : Path (V × J) (StringArrow step N)) (i j : I) :
    ∃ (r : Path (V × J) (StringArrow step N)) (z : K),
      basePath step N r = basePath step N p ∧
        pathImage Q step hstep N hN orient μ A p i j = z • Zigzag.pathBasis U r := by
  rcases p with v|e|v
  · simp only [pathImage,unitImage]
    split_ifs with h
    · refine ⟨.inl i.new,1,?_,?_⟩
      · change Sum.inl i.old.1 = Sum.inl v.1
        exact congrArg Sum.inl (congrArg Prod.fst h.2)
      · rw [one_smul,Zigzag.pathBasis_vertex]
    · exact ⟨.inl v,0,rfl,(zero_smul _ _).symm⟩
  · simp only [pathImage,arrowImage]
    by_cases h : i.old=(U).source e ∧ j.old=(U).target e
    · rw [ite_eq_left h]
      by_cases g : (if step e.base then N i.label j.label else i.label=j.label)
      · rw [dite_eq_left g]
        exact ⟨.inr (.inl ⟨(e.base,i.label,j.label),g⟩),_,rfl,by rw [Zigzag.pathBasis_arrow]⟩
      · rw [dite_eq_right g]
        exact ⟨.inr (.inl e),0,rfl,(zero_smul _ _).symm⟩
    · rw [ite_eq_right h]
      exact ⟨.inr (.inl e),0,rfl,(zero_smul _ _).symm⟩
  · simp only [pathImage,tokenImage]
    split_ifs with h
    · refine ⟨.inr (.inr i.new),μ i.label / μ v.2,?_,?_⟩
      · change Sum.inr (Sum.inr i.old.1) = Sum.inr (Sum.inr v.1)
        exact congrArg (Sum.inr ∘ Sum.inr) (congrArg Prod.fst h.2)
      · rw [Zigzag.pathBasis_token]
    · exact ⟨.inr (.inr v),0,rfl,(zero_smul _ _).symm⟩

lemma image_coordinate_base_ne (p q : Path (V × J) (StringArrow step N))
    (i j : I) (h : basePath step N p ≠ basePath step N q) :
    Zigzag.pathCoordinates U (F (Zigzag.pathBasis U p) i j) q = 0 := by
  rw [linearMap_pathBasis]
  obtain ⟨r,z,hr,hz⟩ := pathImage_single Q step hstep N hN orient μ A p i j
  rw [hz,map_smul]
  change z * Zigzag.pathCoordinates U (Zigzag.pathBasis U r) q = 0
  rw [Zigzag.pathBasis_coordinates,ite_eq_right, mul_zero]
  intro e
  exact h (hr.symm.trans (congrArg (basePath step N) e))

def evaluationSource (u : V) (c : J) (a : {a : J // N a c}) : I :=
  ⟨((u,a),c),a.property⟩
def evaluationTarget (t : V) (b : J) (d : {d : J // N b d}) : I :=
  ⟨((t,b),d),d.property⟩

noncomputable def evaluationMatrix (u t : V) (b c : J) :
    Matrix (LeftPaths Q step hstep N hN u t b c)
      (RightPaths Q step hstep N hN u t b c) K :=
  fun x y => Zigzag.pathCoordinates U
    (F (Zigzag.pathBasis U x.2.val)
      (evaluationSource N u c x.1) (evaluationTarget N t b y.1)) y.2.val

lemma evaluationMatrix_sector (u t : V) (b c : J)
    (p q : Zigzag.CornerPath Q u t) (a : PathLeft step N p.val b c)
    (d : PathRight step N q.val b c) :
    evaluationMatrix Q step hstep N hN orient μ A u t b c
      ((leftPathsEquiv Q step hstep N hN u t b c).symm ⟨p,a⟩)
      ((rightPathsEquiv Q step hstep N hN u t b c).symm ⟨q,d⟩) =
      if h : p=q then pathSwitch step N orient μ A q.val b c (h ▸ a) d else 0 := by
  classical
  by_cases h : p=q
  · subst q
    rw [dite_eq_left rfl]
    change Zigzag.pathCoordinates U
      (F (Zigzag.pathBasis U (liftPath step N p.val a b a.property.1))
        (evaluationSource N u c ⟨a,a.property.2⟩)
        (evaluationTarget N t b ⟨d,d.property.1⟩))
      (liftPath step N p.val c d d.property.2) = _
    have hs : evaluationSource N u c ⟨a,a.property.2⟩ = leftPathIndex Q step N p.val b c a := by
      apply StringIndex.ext <;> simp only [evaluationSource,leftPathIndex,StringIndex.old,StringIndex.label,p.property.1]
    have ht : evaluationTarget N t b ⟨d,d.property.1⟩ = rightPathIndex Q step N p.val b c d := by
      apply StringIndex.ext <;> simp only [evaluationTarget,rightPathIndex,StringIndex.old,StringIndex.label,p.property.2]
    rw [hs,ht,linearMap_liftPath,map_smul]
    change pathSwitch step N orient μ A p.val b c a d *
      Zigzag.pathCoordinates U (Zigzag.pathBasis U (liftPath step N p.val c d d.property.2))
        (liftPath step N p.val c d d.property.2) = _
    rw [Zigzag.pathBasis_coordinates,ite_eq_left rfl,mul_one]
  · rw [dite_eq_right h]
    apply image_coordinate_base_ne
    change basePath step N (liftPath step N p.val a b a.property.1) ≠
      basePath step N (liftPath step N q.val c d d.property.2)
    rw [basePath_liftPath,basePath_liftPath]
    exact fun e => h (Subtype.ext e)

lemma evaluationMatrix_vecMul (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (u t : V) (b c : J) (x : LeftPaths Q step hstep N hN u t b c → K) :
    Matrix.vecMul x (evaluationMatrix Q step hstep N hN orient μ A u t b c) =
      linearSwitch Q step hstep N hN orient μ A hμ δ hA hroot hPF u t b c x := by
  classical
  funext y
  obtain ⟨⟨q,d⟩,rfl⟩ := (rightPathsEquiv Q step hstep N hN u t b c).symm.surjective y
  rw [linearSwitch_sector]
  change (∑ z, x z * evaluationMatrix Q step hstep N hN orient μ A u t b c z _) = _
  rw [← (leftPathsEquiv Q step hstep N hN u t b c).symm.sum_comp]
  rw [Fintype.sum_sigma,Finset.sum_eq_single q]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [evaluationMatrix_sector,dite_eq_left rfl]
  · intro p hp hpq
    apply Finset.sum_eq_zero
    intro a ha
    rw [evaluationMatrix_sector,dite_eq_right hpq,mul_zero]
  · simp

lemma linearMap_mul_corner
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (x y : Zigzag U K) (a b : V × J)
    (hx : Zigzag.vertexId U a * x = x) (hy : x * Zigzag.vertexId U b = x)
    (i k : I) :
    F (x*y) i k = ∑ d : {d : J // N b.2 d},
      F x i (evaluationTarget N b.1 b.2 d) * F y (evaluationTarget N b.1 b.2 d) k := by
  rw [linearMap_mul Q step hstep N hN orient ho μ hμ δ A hA hroot hPF,Matrix.mul_apply]
  have hh : ∀ l : I, F x i l * F y l k =
      if l.old=b then F x i l * F y l k else 0 := by
    intro l
    by_cases hl : l.old=b
    · exact (ite_eq_left hl).symm
    · rw [ite_eq_right hl,linearMap_support Q step hstep N hN orient μ A hx hy i l (Or.inr hl),zero_mul]
  rw [Finset.sum_congr rfl (fun l _ => hh l),sum_over N b]
  rfl

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_CoordinateExpansion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
variable {V B J K : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)

local notation "U" => Q.stringQuiver step hstep N hN
local notation "I" => StringIndex (V := V) N
local notation "F" => linearMap Q step hstep N hN orient μ A

lemma coordinate_expansion {s t : V × J} (x : Zigzag U K)
    (hl : Zigzag.vertexId U s * x = x) (hr : x * Zigzag.vertexId U t = x)
    (i j : I) (q : Path (V × J) (StringArrow step N)) :
    ∑ p : Zigzag.CornerPath U s t, Zigzag.pathCoordinates U x p.val *
      Zigzag.pathCoordinates U (F (Zigzag.pathBasis U p.val) i j) q =
        Zigzag.pathCoordinates U (F x i j) q := by
  conv_rhs => rw [← Zigzag.sum_cornerPath U x hl hr]
  simp only [map_sum,map_smul,Matrix.sum_apply,Matrix.smul_apply,
    Zigzag.coordinates_sum,Zigzag.coordinates_smul]

lemma hom_naturality
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (u t r : V) (a b c e : J) (hac : N a c)
    (x : Zigzag.CornerPath U (u,a) (t,b)) (y : Zigzag U K)
    (hy : y * Zigzag.vertexId U (r,e) = y)
    (j : I) (w : Path (V × J) (StringArrow step N)) :
    (∑ z : Zigzag.CornerPath U (u,a) (r,e),
      Zigzag.pathCoordinates U (Zigzag.pathBasis U x.val * y) z.val *
        Zigzag.pathCoordinates U (F (Zigzag.pathBasis U z.val)
          (evaluationSource N u c ⟨a,hac⟩) j) w) =
    ∑ d : {d : J // N b d}, ∑ z : Zigzag.CornerPath U (u,c) (t,d),
      Zigzag.pathCoordinates U (F (Zigzag.pathBasis U x.val)
        (evaluationSource N u c ⟨a,hac⟩) (evaluationTarget N t b d)) z.val *
      Zigzag.pathCoordinates U (Zigzag.pathBasis U z.val *
        F y (evaluationTarget N t b d) j) w := by
  rw [coordinate_expansion Q step hstep N hN orient μ A _ (by
    rw [← mul_assoc,Zigzag.cornerPath_left]) (by rw [mul_assoc,hy])]
  rw [linearMap_mul_corner Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
    _ y (u,a) (t,b) (Zigzag.cornerPath_left U x) (Zigzag.cornerPath_right U x)]
  rw [Zigzag.coordinates_sum]
  apply Finset.sum_congr rfl
  intro d hd
  exact (Zigzag.coordinates_mul_expansion U _ _
    (linearMap_left Q step hstep N hN orient μ A _ _ _)
    (linearMap_right Q step hstep N hN orient μ A _ _ _) w).symm

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_SectorInverse
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
variable {V B J K : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)

local notation "U" => Q.stringQuiver step hstep N hN

noncomputable def sectorInverse (u t : V) (b c : J)
    (d : (p : Zigzag.CornerPath Q u t) × PathRight step N p.val b c)
    (a : (p : Zigzag.CornerPath Q u t) × PathLeft step N p.val b c) : K := by
  classical
  exact if h : d.1=a.1 then pathUnswitch step N orient μ A a.1.val b c (h ▸ d.2) a.2 else 0

noncomputable def inverseEvaluationMatrix (u t : V) (b c : J) :
    Matrix (RightPaths Q step hstep N hN u t b c)
      (LeftPaths Q step hstep N hN u t b c) K :=
  fun y x => sectorInverse Q step N orient μ A u t b c
    (rightPathsEquiv Q step hstep N hN u t b c y)
    (leftPathsEquiv Q step hstep N hN u t b c x)

omit [Fintype V] [Fintype B] [Fintype J] [DecidableRel N] in
lemma inverseEvaluationMatrix_sector (u t : V) (b c : J)
    (p q : Zigzag.CornerPath Q u t) (d : PathRight step N p.val b c)
    (a : PathLeft step N q.val b c) :
    inverseEvaluationMatrix Q step hstep N hN orient μ A u t b c
      ((rightPathsEquiv Q step hstep N hN u t b c).symm ⟨p,d⟩)
      ((leftPathsEquiv Q step hstep N hN u t b c).symm ⟨q,a⟩) =
      if h : p=q then pathUnswitch step N orient μ A q.val b c (h ▸ d) a else 0 := by
  simp only [inverseEvaluationMatrix,Equiv.apply_symm_apply]
  rfl

omit [Fintype V] [Fintype B] [DecidableEq V] [DecidableEq B] in
lemma linearSwitch_symm_sector (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (u t : V) (b c : J) (x : RightPaths Q step hstep N hN u t b c → K)
    (p : Zigzag.CornerPath Q u t) (a : PathLeft step N p.val b c) :
    (linearSwitch Q step hstep N hN orient μ A hμ δ hA hroot hPF u t b c).symm x
      ((leftPathsEquiv Q step hstep N hN u t b c).symm ⟨p,a⟩) =
      ∑ d : PathRight step N p.val b c,
        x ((rightPathsEquiv Q step hstep N hN u t b c).symm ⟨p,d⟩) *
          pathUnswitch step N orient μ A p.val b c d a := by
  change Sigma.uncurry
    ((LinearEquiv.piCongrRight (fun p : Zigzag.CornerPath Q u t =>
      pathSwitchEquiv step N hN orient μ A hμ δ hA hroot hPF p.val b c)).symm
        (rightSectors Q step hstep N hN u t b c x))
    ((leftPathsEquiv Q step hstep N hN u t b c)
      ((leftPathsEquiv Q step hstep N hN u t b c).symm ⟨p,a⟩)) = _
  rw [Equiv.apply_symm_apply]
  rfl

lemma inverseEvaluationMatrix_vecMul (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (u t : V) (b c : J) (x : RightPaths Q step hstep N hN u t b c → K) :
    Matrix.vecMul x (inverseEvaluationMatrix Q step hstep N hN orient μ A u t b c) =
      (linearSwitch Q step hstep N hN orient μ A hμ δ hA hroot hPF u t b c).symm x := by
  classical
  funext y
  obtain ⟨⟨q,a⟩,rfl⟩ := (leftPathsEquiv Q step hstep N hN u t b c).symm.surjective y
  rw [linearSwitch_symm_sector]
  change (∑ z, x z * inverseEvaluationMatrix Q step hstep N hN orient μ A u t b c z _) = _
  rw [← (rightPathsEquiv Q step hstep N hN u t b c).symm.sum_comp]
  rw [Fintype.sum_sigma,Finset.sum_eq_single q]
  · apply Finset.sum_congr rfl
    intro d hd
    rw [inverseEvaluationMatrix_sector,dite_eq_left rfl]
  · intro p hp hpq
    apply Finset.sum_eq_zero
    intro d hd
    rw [inverseEvaluationMatrix_sector,dite_eq_right hpq,mul_zero]
  · simp

lemma evaluationMatrix_inverse (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (u t : V) (b c : J) :
    evaluationMatrix Q step hstep N hN orient μ A u t b c *
      inverseEvaluationMatrix Q step hstep N hN orient μ A u t b c = (by classical exact 1) := by
  classical
  apply Matrix.vecMul_injective
  funext x
  dsimp only
  rw [← Matrix.vecMul_vecMul,
    evaluationMatrix_vecMul Q step hstep N hN orient μ A hμ δ hA hroot hPF,
    inverseEvaluationMatrix_vecMul Q step hstep N hN orient μ A hμ δ hA hroot hPF,
    LinearEquiv.symm_apply_apply,Matrix.vecMul_one]

lemma inverseEvaluationMatrix_inverse (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (u t : V) (b c : J) :
    inverseEvaluationMatrix Q step hstep N hN orient μ A u t b c *
      evaluationMatrix Q step hstep N hN orient μ A u t b c = (by classical exact 1) := by
  classical
  apply Matrix.vecMul_injective
  funext x
  dsimp only
  rw [← Matrix.vecMul_vecMul,
    inverseEvaluationMatrix_vecMul Q step hstep N hN orient μ A hμ δ hA hroot hPF,
    evaluationMatrix_vecMul Q step hstep N hN orient μ A hμ δ hA hroot hPF,
    LinearEquiv.apply_symm_apply,Matrix.vecMul_one]

lemma evaluationMatrix_length {u t : V} {b c : J}
    (x : LeftPaths Q step hstep N hN u t b c)
    (y : RightPaths Q step hstep N hN u t b c)
    (h : evaluationMatrix Q step hstep N hN orient μ A u t b c x y ≠ 0) :
    Path.length x.2.val = Path.length y.2.val := by
  by_contra hn
  exact h ((Zigzag.coordinates_homogeneous U _ _).1
    (linearMap_homogeneous Q step hstep N hN orient μ A (Zigzag.pathBasis_homogeneous U x.2.val)
      (evaluationSource N u c x.1) (evaluationTarget N t b y.1)) y.2.val (Ne.symm hn))

omit [Fintype V] [Fintype B] [Fintype J] [DecidableRel N] in
lemma inverseEvaluationMatrix_length {u t : V} {b c : J}
    (y : RightPaths Q step hstep N hN u t b c)
    (x : LeftPaths Q step hstep N hN u t b c)
    (h : inverseEvaluationMatrix Q step hstep N hN orient μ A u t b c y x ≠ 0) :
    Path.length y.2.val = Path.length x.2.val := by
  classical
  unfold inverseEvaluationMatrix sectorInverse at h
  split_ifs at h with he
  · have hf := congrArg (fun p : Zigzag.CornerPath Q u t => Path.length p.val) he
    change Path.length (basePath step N y.2.val) = Path.length (basePath step N x.2.val) at hf
    simpa only [basePath_length] using hf
  · exact (h rfl).elim

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_LeftHomIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
variable {V B J K T R : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)

local notation "U" => Q.stringQuiver step hstep N hN
local notation "F" => linearMap Q step hstep N hN orient μ A

abbrev LeftHomIndex (p : T → GeneratorPlacement (V × J)) (u:V) (c:J) :=
  (i:T) × LeftPaths Q step hstep N hN u (p i).color.1 (p i).color.2 c
abbrev RightHomIndex (p : T → GeneratorPlacement (V × J)) (u:V) (c:J) :=
  (i:T) × RightPaths Q step hstep N hN u (p i).color.1 (p i).color.2 c

noncomputable def leftHomMatrix (p : T → GeneratorPlacement (V × J))
    (q : R → GeneratorPlacement (V × J)) (u:V) (c:J)
    (M : Matrix T R (Zigzag U K)) :
    Matrix (LeftHomIndex Q step hstep N hN p u c) (LeftHomIndex Q step hstep N hN q u c) K :=
  fun x y => if x.2.1=y.2.1 then
    Zigzag.pathCoordinates U (Zigzag.pathBasis U x.2.2.val * M x.1 y.1) y.2.2.val else 0

noncomputable def rightHomMatrix (p : T → GeneratorPlacement (V × J))
    (q : R → GeneratorPlacement (V × J)) (u:V) (c:J)
    (M : Matrix T R (Zigzag U K)) :
    Matrix (RightHomIndex Q step hstep N hN p u c) (RightHomIndex Q step hstep N hN q u c) K :=
  fun x y => Zigzag.pathCoordinates U
    (Zigzag.pathBasis U x.2.2.val * F (M x.1 y.1)
      (evaluationTarget N (p x.1).color.1 (p x.1).color.2 x.2.1)
      (evaluationTarget N (q y.1).color.1 (q y.1).color.2 y.2.1)) y.2.2.val

noncomputable def homSwitch [DecidableEq T] (p : T → GeneratorPlacement (V × J)) (u:V) (c:J) :
    Matrix (LeftHomIndex Q step hstep N hN p u c) (RightHomIndex Q step hstep N hN p u c) K :=
  Matrix.blockDiagonal' (fun i => evaluationMatrix Q step hstep N hN orient μ A
    u (p i).color.1 (p i).color.2 c)

noncomputable def homUnswitch [DecidableEq T] (p : T → GeneratorPlacement (V × J)) (u:V) (c:J) :
    Matrix (RightHomIndex Q step hstep N hN p u c) (LeftHomIndex Q step hstep N hN p u c) K :=
  Matrix.blockDiagonal' (fun i => inverseEvaluationMatrix Q step hstep N hN orient μ A
    u (p i).color.1 (p i).color.2 c)

lemma homSwitch_inverse [Fintype T] [DecidableEq T]
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (p : T → GeneratorPlacement (V × J)) (u:V) (c:J) :
    homSwitch Q step hstep N hN orient μ A p u c *
      homUnswitch Q step hstep N hN orient μ A p u c = (by classical exact 1) := by
  classical
  unfold homSwitch homUnswitch
  rw [← Matrix.blockDiagonal'_mul]
  simp only [evaluationMatrix_inverse Q step hstep N hN orient μ A hμ δ hA hroot hPF]
  exact Matrix.blockDiagonal'_one

lemma homUnswitch_inverse [Fintype T] [DecidableEq T]
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (p : T → GeneratorPlacement (V × J)) (u:V) (c:J) :
    homUnswitch Q step hstep N hN orient μ A p u c *
      homSwitch Q step hstep N hN orient μ A p u c = (by classical exact 1) := by
  classical
  unfold homSwitch homUnswitch
  rw [← Matrix.blockDiagonal'_mul]
  simp only [inverseEvaluationMatrix_inverse Q step hstep N hN orient μ A hμ δ hA hroot hPF]
  exact Matrix.blockDiagonal'_one

lemma homSwitch_naturality [Fintype T] [Fintype R] [DecidableEq T] [DecidableEq R]
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (p : T → GeneratorPlacement (V × J)) (q : R → GeneratorPlacement (V × J))
    (u:V) (c:J) (M : Matrix T R (Zigzag U K)) (hM : Zigzag.ProjectiveEntries U p q M) :
    leftHomMatrix Q step hstep N hN p q u c M *
      homSwitch Q step hstep N hN orient μ A q u c =
    homSwitch Q step hstep N hN orient μ A p u c *
      rightHomMatrix Q step hstep N hN orient μ A p q u c M := by
  classical
  apply Matrix.ext
  rintro ⟨i,a,x⟩ ⟨j,d,w⟩
  simp only [homSwitch]
  rw [Matrix.mul_blockDiagonal'_entry,Matrix.blockDiagonal'_mul_entry]
  rw [Fintype.sum_sigma,Finset.sum_eq_single a]
  · simp only [leftHomMatrix,ite_true, if_true]
    rw [Fintype.sum_sigma]
    exact hom_naturality Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
      u (p i).color.1 (q j).color.1 a (p i).color.2 c (q j).color.2 a.property
      x (M i j) (hM.2 i j) (evaluationTarget N (q j).color.1 (q j).color.2 d) w.val
  · intro b hb hba
    apply Finset.sum_eq_zero
    intro z hz
    rw [leftHomMatrix,ite_eq_right (Ne.symm hba),zero_mul]
  · simp

lemma homUnswitch_naturality [Fintype T] [Fintype R] [DecidableEq T] [DecidableEq R]
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (p : T → GeneratorPlacement (V × J)) (q : R → GeneratorPlacement (V × J))
    (u:V) (c:J) (M : Matrix T R (Zigzag U K)) (hM : Zigzag.ProjectiveEntries U p q M) :
    rightHomMatrix Q step hstep N hN orient μ A p q u c M *
      homUnswitch Q step hstep N hN orient μ A q u c =
    homUnswitch Q step hstep N hN orient μ A p u c *
      leftHomMatrix Q step hstep N hN p q u c M := by
  classical
  let L := leftHomMatrix Q step hstep N hN p q u c M
  let R := rightHomMatrix Q step hstep N hN orient μ A p q u c M
  let Sp := homSwitch Q step hstep N hN orient μ A p u c
  let Sq := homSwitch Q step hstep N hN orient μ A q u c
  let Dp := homUnswitch Q step hstep N hN orient μ A p u c
  let Dq := homUnswitch Q step hstep N hN orient μ A q u c
  have hn : L*Sq=Sp*R := homSwitch_naturality Q step hstep N hN orient μ A ho hμ δ hA hroot hPF p q u c M hM
  have hDS : Dp*Sp=1 := homUnswitch_inverse Q step hstep N hN orient μ A hμ δ hA hroot hPF p u c
  have hSD : Sq*Dq=1 := homSwitch_inverse Q step hstep N hN orient μ A hμ δ hA hroot hPF q u c
  change R*Dq=Dp*L
  calc
    R*Dq = (Dp*Sp)*(R*Dq) := by rw [hDS,Matrix.one_mul]
    _ = Dp*(Sp*R)*Dq := by simp only [Matrix.mul_assoc]
    _ = Dp*(L*Sq)*Dq := by rw [← hn]
    _ = Dp*L*(Sq*Dq) := by simp only [Matrix.mul_assoc]
    _ = Dp*L := by rw [hSD,Matrix.mul_one]

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_ScalarCornerMatrixDegree
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V B K T R : Type*} (Q : ReversibleQuiver V B) [Field K]
  [Fintype B] [DecidableEq V]
lemma scalarCornerMatrix_degree (α : V) (p : T → GeneratorPlacement V)
    (q : R → GeneratorPlacement V) (M : Matrix T R K) (n v : ℤ)
    (hc : ∀ i j, M i j ≠ 0 → (q j).cochain = (p i).cochain+n)
    (hi : ∀ i j, M i j ≠ 0 → (q j).internal = (p i).internal+v) :
    MapDegree Q p q n v (scalarCornerMatrix Q α M) := by
  intro i j
  constructor
  · intro h
    have hz : M i j=0 := by
      by_contra hn
      exact h (hc i j hn)
    change M i j • vertexId Q α = 0
    rw [hz,zero_smul]
  · by_cases hz : M i j=0
    · change Homogeneous Q _ (M i j • vertexId Q α)
      rw [hz,zero_smul]
      exact homogeneous_zero Q _
    · have he : v+(p i).internal-(q j).internal=0 := by rw [hi i j hz]; omega
      rw [he]
      exact homogeneous_smul Q (homogeneous_vertexId Q α) _

lemma scalarCornerMatrix_identity [DecidableEq T] (α : V)
    (p : T → GeneratorPlacement V) (hp : ∀ i, (p i).color=α) :
    scalarCornerMatrix Q α (1 : Matrix T T K) = projectiveIdentity Q p := by
  apply Matrix.ext
  intro i j
  by_cases h : i=j
  · subst j
    simp only [scalarCornerMatrix,Matrix.one_apply_eq,one_smul,projectiveIdentity,
      Matrix.diagonal_apply,ite_true, if_true,hp]
  · simp only [scalarCornerMatrix,Matrix.one_apply_ne h,zero_smul,projectiveIdentity,
      Matrix.diagonal_apply,ite_eq_right h]
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_LeftHomPlacement
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
variable {V B J K T : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)

local notation "U" => Q.stringQuiver step hstep N hN

def leftHomPlacement (p : T → GeneratorPlacement (V × J)) (u:V) (c:J) :
    LeftHomIndex Q step hstep N hN p u c → GeneratorPlacement (V × J) :=
  fun x => ⟨(u,c),(p x.1).cochain,(p x.1).internal + Path.length x.2.2.val⟩

def rightHomEquiv (p : T → GeneratorPlacement (V × J)) (u:V) (c:J) :
    RightHomIndex Q step hstep N hN p u c ≃ Zigzag.TestIndex U (placement N p) (u,c) where
  toFun x := ⟨⟨x.1,x.2.1⟩,x.2.2⟩
  invFun x := ⟨x.1.1,⟨x.1.2,x.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

def rightHomPlacement (p : T → GeneratorPlacement (V × J)) (u:V) (c:J) :
    RightHomIndex Q step hstep N hN p u c → GeneratorPlacement (V × J) :=
  Zigzag.testPlacement U (placement N p) (u,c) ∘ rightHomEquiv Q step hstep N hN p u c

lemma rightHomMatrix_eq (p : T → GeneratorPlacement (V × J)) (u:V) (c:J)
    (M : Matrix T T (Zigzag U K)) :
    rightHomMatrix Q step hstep N hN orient μ A p p u c M =
      (Zigzag.testMatrix U (placement N p) (placement N p) (u,c)
        (matrix Q step hstep N hN orient μ A p p M)).submatrix
          (rightHomEquiv Q step hstep N hN p u c) (rightHomEquiv Q step hstep N hN p u c) := rfl

lemma leftHom_degree (p : T → GeneratorPlacement (V × J)) (u:V) (c:J)
    (M : Matrix T T (Zigzag U K)) (hM : Zigzag.MapDegree U p p 1 0 M) :
    Zigzag.MapDegree U (leftHomPlacement Q step hstep N hN p u c)
      (leftHomPlacement Q step hstep N hN p u c) 1 0
      (Zigzag.scalarCornerMatrix U (u,c) (leftHomMatrix Q step hstep N hN p p u c M)) := by
  apply Zigzag.scalarCornerMatrix_degree
  · rintro ⟨i,a,x⟩ ⟨j,b,y⟩ h
    change (p j).cochain = (p i).cochain+1
    by_contra hn
    apply h
    simp only [leftHomMatrix,(hM i j).1 hn,mul_zero,Zigzag.coordinates_zero,ite_self]
  · rintro ⟨i,a,x⟩ ⟨j,b,y⟩ h
    have hz : Zigzag.pathCoordinates U (Zigzag.pathBasis U x.val * M i j) y.val ≠ 0 := by
      intro hz
      apply h
      simp only [leftHomMatrix,hz,ite_self]
    have he := Zigzag.coordinates_mul_degree U (Zigzag.pathBasis_homogeneous U x.val)
      (hM i j).2 hz
    change (p j).internal+Path.length y.val=(p i).internal+Path.length x.val+0
    omega

section Complex
variable [Fintype T] [DecidableEq T]
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)

local notation "C" => complex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

noncomputable def rightHomComplex (E : Zigzag.BasedComplex U (K := K) T) (u:V) (c:J) :
    Zigzag.BasedComplex U (K := K) (RightHomIndex Q step hstep N hN E.placement u c) :=
  ((C E).testComplex U (u,c)).reindex U (rightHomEquiv Q step hstep N hN E.placement u c)

include ho hμ hA hroot hPF in
omit [DecidableEq T] in
lemma rightHomMatrix_square (E : Zigzag.BasedComplex U (K := K) T) (u:V) (c:J) :
    rightHomMatrix Q step hstep N hN orient μ A E.placement E.placement u c E.differential *
      rightHomMatrix Q step hstep N hN orient μ A E.placement E.placement u c E.differential = 0 := by
  simp only [rightHomMatrix_eq]
  rw [Matrix.submatrix_mul_equiv]
  change (Zigzag.testMatrix U (C E).placement (C E).placement (u,c) (C E).differential *
    Zigzag.testMatrix U (C E).placement (C E).placement (u,c) (C E).differential).submatrix _ _ = 0
  rw [Zigzag.testMatrix_mul U (u,c) _ (C E).entries]
  change (Zigzag.testMatrix U _ _ (u,c) ((C E).differential * (C E).differential)).submatrix _ _ = 0
  rw [(C E).square_zero,Zigzag.testMatrix_zero]
  rfl

include ho hμ hA hroot hPF in
lemma leftHomMatrix_square (E : Zigzag.BasedComplex U (K := K) T) (u:V) (c:J) :
    leftHomMatrix Q step hstep N hN E.placement E.placement u c E.differential *
      leftHomMatrix Q step hstep N hN E.placement E.placement u c E.differential = 0 := by
  classical
  let L := leftHomMatrix Q step hstep N hN E.placement E.placement u c E.differential
  let R := rightHomMatrix Q step hstep N hN orient μ A E.placement E.placement u c E.differential
  let S := homSwitch Q step hstep N hN orient μ A E.placement u c
  let D := homUnswitch Q step hstep N hN orient μ A E.placement u c
  have hSD : S*D=1 := homSwitch_inverse Q step hstep N hN orient μ A hμ δ hA hroot hPF _ _ _
  have hLS : L*S=S*R := homSwitch_naturality Q step hstep N hN orient μ A ho hμ δ hA hroot hPF _ _ _ _ _ E.entries
  have hRR : R*R=0 := rightHomMatrix_square Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E u c
  change L*L=0
  calc
    L*L = L*L*(S*D) := by rw [hSD,Matrix.mul_one]
    _ = L*((L*S)*D) := by simp only [Matrix.mul_assoc]
    _ = L*((S*R)*D) := by rw [hLS]
    _ = (L*S)*(R*D) := by simp only [Matrix.mul_assoc]
    _ = S*(R*R)*D := by rw [hLS]; simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hRR,Matrix.mul_zero,Matrix.zero_mul]

noncomputable def leftHomComplex (E : Zigzag.BasedComplex U (K := K) T) (u:V) (c:J) :
    Zigzag.BasedComplex U (K := K) (LeftHomIndex Q step hstep N hN E.placement u c) where
  placement := leftHomPlacement Q step hstep N hN E.placement u c
  differential := Zigzag.scalarCornerMatrix U (u,c) (leftHomMatrix Q step hstep N hN E.placement E.placement u c E.differential)
  entries := Zigzag.scalarCornerMatrix_entries U (u,c) _ _ (fun _ => rfl) (fun _ => rfl) _
  degree := leftHom_degree Q step hstep N hN _ _ _ _ E.degree
  square_zero := by
    rw [Zigzag.scalarCornerMatrix_mul,leftHomMatrix_square Q step hstep N hN orient μ A ho hμ δ hA hroot hPF,
      Zigzag.scalarCornerMatrix_zero]

end Complex
end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_HomSwitchMap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
attribute [local instance] Classical.propDecidable
variable {V B J K T : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)

local notation "U" => Q.stringQuiver step hstep N hN

lemma homSwitch_degree [DecidableEq T] (p : T → GeneratorPlacement (V × J)) (u:V) (c:J) :
    Zigzag.MapDegree U (leftHomPlacement Q step hstep N hN p u c)
      (rightHomPlacement Q step hstep N hN p u c) 0 0
      (Zigzag.scalarCornerMatrix U (u,c) (homSwitch Q step hstep N hN orient μ A p u c)) := by
  apply Zigzag.scalarCornerMatrix_degree
  · rintro ⟨i,x⟩ ⟨j,y⟩ h
    by_cases hij : i=j
    · subst j
      change (p i).cochain = (p i).cochain+0
      omega
    · exact (h (Matrix.blockDiagonal'_apply_ne _ _ _ hij)).elim
  · rintro ⟨i,x⟩ ⟨j,y⟩ h
    by_cases hij : i=j
    · subst j
      have he := evaluationMatrix_length Q step hstep N hN orient μ A x y
        (by simpa only [homSwitch,Matrix.blockDiagonal'_apply_eq] using h)
      change (p i).internal + Path.length y.2.val = (p i).internal + Path.length x.2.val + 0
      omega
    · exact (h (Matrix.blockDiagonal'_apply_ne _ _ _ hij)).elim

omit [Fintype V] in
lemma homUnswitch_degree [DecidableEq T] (p : T → GeneratorPlacement (V × J)) (u:V) (c:J) :
    Zigzag.MapDegree U (rightHomPlacement Q step hstep N hN p u c)
      (leftHomPlacement Q step hstep N hN p u c) 0 0
      (Zigzag.scalarCornerMatrix U (u,c) (homUnswitch Q step hstep N hN orient μ A p u c)) := by
  apply Zigzag.scalarCornerMatrix_degree
  · rintro ⟨i,x⟩ ⟨j,y⟩ h
    by_cases hij : i=j
    · subst j
      change (p i).cochain = (p i).cochain+0
      omega
    · exact (h (Matrix.blockDiagonal'_apply_ne _ _ _ hij)).elim
  · rintro ⟨i,x⟩ ⟨j,y⟩ h
    by_cases hij : i=j
    · subst j
      have he := inverseEvaluationMatrix_length Q step hstep N hN orient μ A x y
        (by simpa only [homUnswitch,Matrix.blockDiagonal'_apply_eq] using h)
      change (p i).internal + Path.length y.2.val = (p i).internal + Path.length x.2.val + 0
      omega
    · exact (h (Matrix.blockDiagonal'_apply_ne _ _ _ hij)).elim

section Isomorphism
variable [Fintype T] [DecidableEq T]
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)

local notation "L" => leftHomComplex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
local notation "R" => rightHomComplex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

noncomputable def homSwitchMap (E : Zigzag.BasedComplex U (K := K) T) (u:V) (c:J) :
    Zigzag.BasedComplex.Map U (L E u c) (R E u c) where
  matrix := Zigzag.scalarCornerMatrix U (u,c) (homSwitch Q step hstep N hN orient μ A E.placement u c)
  entries := Zigzag.scalarCornerMatrix_entries U (u,c) _ _ (fun _ => rfl) (fun _ => rfl) _
  degree := homSwitch_degree Q step hstep N hN orient μ A _ _ _
  commute := by
    change Zigzag.scalarCornerMatrix U (u,c) (leftHomMatrix Q step hstep N hN E.placement E.placement u c E.differential) *
      Zigzag.scalarCornerMatrix U (u,c) (homSwitch Q step hstep N hN orient μ A E.placement u c) =
      Zigzag.scalarCornerMatrix U (u,c) (homSwitch Q step hstep N hN orient μ A E.placement u c) *
      Zigzag.scalarCornerMatrix U (u,c) (rightHomMatrix Q step hstep N hN orient μ A E.placement E.placement u c E.differential)
    rw [Zigzag.scalarCornerMatrix_mul,Zigzag.scalarCornerMatrix_mul]
    congr 1
    exact homSwitch_naturality Q step hstep N hN orient μ A ho hμ δ hA hroot hPF _ _ _ _ _ E.entries

noncomputable def homUnswitchMap (E : Zigzag.BasedComplex U (K := K) T) (u:V) (c:J) :
    Zigzag.BasedComplex.Map U (R E u c) (L E u c) where
  matrix := Zigzag.scalarCornerMatrix U (u,c) (homUnswitch Q step hstep N hN orient μ A E.placement u c)
  entries := Zigzag.scalarCornerMatrix_entries U (u,c) _ _ (fun _ => rfl) (fun _ => rfl) _
  degree := homUnswitch_degree Q step hstep N hN orient μ A _ _ _
  commute := by
    change Zigzag.scalarCornerMatrix U (u,c) (rightHomMatrix Q step hstep N hN orient μ A E.placement E.placement u c E.differential) *
      Zigzag.scalarCornerMatrix U (u,c) (homUnswitch Q step hstep N hN orient μ A E.placement u c) =
      Zigzag.scalarCornerMatrix U (u,c) (homUnswitch Q step hstep N hN orient μ A E.placement u c) *
      Zigzag.scalarCornerMatrix U (u,c) (leftHomMatrix Q step hstep N hN E.placement E.placement u c E.differential)
    rw [Zigzag.scalarCornerMatrix_mul,Zigzag.scalarCornerMatrix_mul]
    congr 1
    exact homUnswitch_naturality Q step hstep N hN orient μ A ho hμ δ hA hroot hPF _ _ _ _ _ E.entries

noncomputable def homComparison (E : Zigzag.BasedComplex U (K := K) T) (u:V) (c:J) :
    Zigzag.BasedComplex.ChainIsomorphism U (L E u c) (R E u c) := by
  classical
  exact {
    forward := homSwitchMap Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E u c
    backward := homUnswitchMap Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E u c
    sourceEquation := by
      change Zigzag.scalarCornerMatrix U (u,c) _ * Zigzag.scalarCornerMatrix U (u,c) _ = _
      rw [Zigzag.scalarCornerMatrix_mul,homSwitch_inverse Q step hstep N hN orient μ A hμ δ hA hroot hPF]
      exact Zigzag.scalarCornerMatrix_identity U (u,c) _ (fun _ => rfl)
    targetEquation := by
      change Zigzag.scalarCornerMatrix U (u,c) _ * Zigzag.scalarCornerMatrix U (u,c) _ = _
      rw [Zigzag.scalarCornerMatrix_mul,homUnswitch_inverse Q step hstep N hN orient μ A hμ δ hA hroot hPF]
      exact Zigzag.scalarCornerMatrix_identity U (u,c) _ (fun _ => rfl) }

end Isomorphism
end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_LeftPacketIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
attribute [local instance] Classical.propDecidable
variable {V B J K T : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)

local notation "U" => Q.stringQuiver step hstep N hN
local notation "F" => linearMap Q step hstep N hN orient μ A

abbrev LeftPacketIndex (p : T → GeneratorPlacement (V × J)) (u:V) :=
  (c:J) × LeftHomIndex Q step hstep N hN p u c
abbrev RightPacketIndex (p : T → GeneratorPlacement (V × J)) (u:V) :=
  (c:J) × RightHomIndex Q step hstep N hN p u c

def leftPacketEquiv (p : T → GeneratorPlacement (V × J)) (u:V) :
    LeftPacketIndex Q step hstep N hN p u ≃
      Index N (Zigzag.packetPlacement U p (fun a:J => (u,a))) where
  toFun x := ⟨⟨x.2.2.1.val,⟨x.2.1,x.2.2.2⟩⟩,⟨x.1,x.2.2.1.property⟩⟩
  invFun x := ⟨x.2.val,⟨x.1.2.1,⟨⟨x.1.1,x.2.property⟩,x.1.2.2⟩⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

def rightPacketEquiv (p : T → GeneratorPlacement (V × J)) (u:V) :
    RightPacketIndex Q step hstep N hN p u ≃
      Zigzag.PacketIndex U (placement N p) (fun a:J => (u,a)) where
  toFun x := ⟨x.1,rightHomEquiv Q step hstep N hN p u x.1 x.2⟩
  invFun x := ⟨x.1,(rightHomEquiv Q step hstep N hN p u x.1).symm x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma linearMap_scalarVertex (v : V × J) (z:K) (i j : StringIndex (V := V) N) :
    F (z • Zigzag.vertexId U v) i j =
      if i=j ∧ i.old=v then z • Zigzag.vertexId U i.new else 0 := by
  rw [map_smul,← Zigzag.pathBasis_vertex,linearMap_pathBasis]
  change z • (if i=j ∧ i.old=v then Zigzag.vertexId U i.new else 0) = _
  split_ifs <;> simp

lemma leftPacket_differential [Fintype T]
    (p : T → GeneratorPlacement (V × J)) (u:V) (M : Matrix T T (Zigzag U K)) :
    (matrix Q step hstep N hN orient μ A
      (Zigzag.packetPlacement U p (fun a:J => (u,a)))
      (Zigzag.packetPlacement U p (fun a:J => (u,a)))
      (Zigzag.packetDifferential U p (fun a:J => (u,a)) M)).submatrix
      (leftPacketEquiv Q step hstep N hN p u) (leftPacketEquiv Q step hstep N hN p u) =
    Matrix.blockDiagonal' (fun c => Zigzag.scalarCornerMatrix U (u,c)
      (leftHomMatrix Q step hstep N hN p p u c M)) := by
  apply Matrix.ext
  rintro ⟨c,i,⟨a,ha⟩,x⟩ ⟨d,j,⟨b,hb⟩,y⟩
  by_cases hab : a=b
  · subst b
    by_cases hcd : c=d
    · subst d
      change F (Zigzag.packetDifferential U p (fun a:J => (u,a)) M ⟨a,⟨i,x⟩⟩ ⟨a,⟨j,y⟩⟩)
        (evaluationSource N u c ⟨a,ha⟩) (evaluationSource N u c ⟨a,hb⟩) = _
      rw [Zigzag.packetDifferential,Matrix.blockDiagonal'_apply_eq,
        Matrix.blockDiagonal'_apply_eq]
      simp only [Zigzag.scalarCornerMatrix,linearMap_scalarVertex,leftHomMatrix,ite_true, if_true,
        evaluationSource,StringIndex.old,StringIndex.new,StringIndex.label,and_self]
      rfl
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hcd]
      simp only [Matrix.submatrix_apply,matrix,leftPacketEquiv,Equiv.coe_fn_mk,
        Zigzag.packetDifferential,Matrix.blockDiagonal'_apply_eq,Zigzag.scalarCornerMatrix,
        linearMap_scalarVertex]
      apply ite_eq_right
      intro h
      exact hcd (congrArg StringIndex.label h.1)
  · have hba := Ne.symm hab
    simp only [Matrix.submatrix_apply,matrix,leftPacketEquiv,Equiv.coe_fn_mk,
      Zigzag.packetDifferential,Matrix.blockDiagonal'_apply_ne _ _ _ hab,map_zero,
      Matrix.zero_apply]
    by_cases hcd : c=d
    · subst d
      rw [Matrix.blockDiagonal'_apply_eq]
      simp only [Zigzag.scalarCornerMatrix,leftHomMatrix,Subtype.mk.injEq,ite_eq_right hab,zero_smul]
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hcd]

section Complex
variable [Fintype T] [DecidableEq T]
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
local notation "C" => complex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
local notation "L" => leftHomComplex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
local notation "R" => rightHomComplex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

lemma leftPacketComplex_eq (E : Zigzag.BasedComplex U (K := K) T) (u:V) :
    (C (E.packetTest U (fun a:J => (u,a)))).reindex U
      (leftPacketEquiv Q step hstep N hN E.placement u) =
      Zigzag.BasedComplex.finiteSum U (fun c => L E u c) := by
  apply Zigzag.BasedComplex.ext_placement_differential
  · rfl
  · exact leftPacket_differential Q step hstep N hN orient μ A _ _ _

omit [DecidableEq T] in
lemma rightPacketComplex_eq (E : Zigzag.BasedComplex U (K := K) T) (u:V) :
    ((C E).packetTest U (fun a:J => (u,a))).reindex U
      (rightPacketEquiv Q step hstep N hN E.placement u) =
      Zigzag.BasedComplex.finiteSum U (fun c => R E u c) := by
  apply Zigzag.BasedComplex.ext_placement_differential
  · rfl
  · apply Matrix.ext
    rintro ⟨c,x⟩ ⟨d,y⟩
    change Matrix.blockDiagonal' (fun a => Zigzag.scalarCornerMatrix U (u,a)
        (Zigzag.testMatrix U (placement N E.placement) (placement N E.placement) (u,a)
          (matrix Q step hstep N hN orient μ A E.placement E.placement E.differential)))
        ⟨c,rightHomEquiv Q step hstep N hN E.placement u c x⟩
        ⟨d,rightHomEquiv Q step hstep N hN E.placement u d y⟩ =
      Matrix.blockDiagonal' (fun a => (R E u a).differential) ⟨c,x⟩ ⟨d,y⟩
    by_cases h : c=d
    · subst d
      rw [Matrix.blockDiagonal'_apply_eq,Matrix.blockDiagonal'_apply_eq]
      rfl
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h,Matrix.blockDiagonal'_apply_ne _ _ _ h]

end Complex
end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_PacketSwitchMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
attribute [local instance] Classical.propDecidable
variable {V B J K T : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)
local notation "U" => Q.stringQuiver step hstep N hN

noncomputable def packetSwitchMatrix [DecidableEq T]
    (p : T → GeneratorPlacement (V × J)) (u:V) :
    Matrix (LeftPacketIndex Q step hstep N hN p u)
      (RightPacketIndex Q step hstep N hN p u) (Zigzag U K) :=
  Matrix.blockDiagonal' (fun c => Zigzag.scalarCornerMatrix U (u,c)
    (homSwitch Q step hstep N hN orient μ A p u c))

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_ColorPacketPerm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
universe u
attribute [local instance] Classical.propDecidable
variable {V B J : Type u} {K : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)
local notation "U" => Q.stringQuiver step hstep N hN
open Zigzag.BasedComplex

omit [Fintype V] [Fintype B] [Fintype J] [DecidableEq V] [DecidableEq B]
  [DecidableEq J] [DecidableRel N] in
lemma string_loopless (hn : ∀ b, Q.source b ≠ Q.target b) :
    ∀ a, (U).source a ≠ (U).target a := by
  intro a ha
  exact hn a.base (congrArg Prod.fst ha)

omit [Fintype V] [Fintype B] [Fintype J] [DecidableEq V] [DecidableEq B]
  [DecidableEq J] [DecidableRel N] in
lemma color_orthogonal (hn : ∀ b, Q.source b ≠ Q.target b) (v:V) :
    Pairwise (fun a b : J => Zigzag.OrthogonalVertices U (v,a) (v,b)) := by
  intro a b hab
  refine ⟨fun he => hab (congrArg Prod.snd he),fun p hp hq => ?_⟩
  exact hn p.base ((congrArg Prod.fst hp).trans (congrArg Prod.fst hq).symm)

noncomputable def colorPacketPerm (hn : ∀ b, Q.source b ≠ Q.target b) (v:V) :
    Equiv.Perm (FiniteHomotopyClass U (K := K)) :=
  classPacketPerm U (string_loopless Q step hstep N hN hn) (fun a:J => (v,a))
    (color_orthogonal Q step hstep N hN hn v)

lemma colorPacketPerm_apply (hn : ∀ b, Q.source b ≠ Q.target b) (v:V)
    (E : FiniteModel U (K := K)) :
    colorPacketPerm Q step hstep N hN (K := K) hn v
      (Quotient.mk (finiteHomotopySetoid U) E) =
      classOfComplex U (E.complex.packetTwist U (fun a:J => (v,a))) :=
  classPacketPerm_apply U _ _ _ E

variable (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
local notation "C" => complex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

noncomputable def classLabelFunctor : FiniteHomotopyClass U (K := K) → FiniteHomotopyClass U (K := K) :=
  Quotient.map (fun E => FiniteModel.ofComplex U (C E.complex)) (by
    intro E F ⟨e⟩
    exact ⟨homotopyEquivalence Q step hstep N hN orient μ A ho hμ δ hA hroot hPF e⟩)

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_Placement
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Iso
open Zigzag Zigzag.BasedComplex

variable {V A W B K : Type*} {Q : ReversibleQuiver V A} {R : ReversibleQuiver W B}
  (e : Iso Q R) [Field K] [Fintype A] [Fintype B] [DecidableEq V] [DecidableEq W]
  {I J L : Type*}

lemma complex_minimal [Fintype I] {E : BasedComplex Q (K := K) I} (h:E.IsMinimal Q) :
    (e.complex E).IsMinimal R := by
  intro i j
  ext v
  change (E.differential i j).vertex (e.vertex.symm v)=0
  rw [h i j]; rfl

end HarmonicArtin.ReversibleQuiver.Iso

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_ComplexPureLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Iso
open Zigzag Zigzag.BasedComplex

universe u
attribute [local instance] Classical.propDecidable
variable {V A W B : Type u} {K : Type*} {Q : ReversibleQuiver V A} {R : ReversibleQuiver W B}
  (e : Iso Q R) [Field K] [Fintype V] [Fintype W] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq W] [DecidableEq A] [DecidableEq B]
  {I : Type u} [Fintype I] [DecidableEq I]

omit [Fintype V] [Fintype W] [DecidableEq A] [DecidableEq B] [DecidableEq I] in
lemma levelArray_complex (E:BasedComplex Q (K := K) I) (α:V) (d:ℤ) :
    (e.complex E).levelArray R (e.vertex α,d) = E.levelArray Q (α,d) := by
  simp only [levelArray_apply]
  have hP : {i:I | ((e.complex E).placement i).color=e.vertex α ∧ ((e.complex E).placement i).level=d} =
      {i:I | (E.placement i).color=α ∧ (E.placement i).level=d} := by
    ext i
    change (e.vertex (E.placement i).color=e.vertex α ∧ (E.placement i).level=d) ↔ _
    rw [e.vertex.injective.eq_iff]
    rfl
  exact congrArg (fun U:Set I => Nat.card U) hP

omit [Fintype V] [Fintype W] [DecidableEq A] [DecidableEq B] in
lemma classMap_levelArray (x:FiniteHomotopyClass Q (K := K)) (α:V) (d:ℤ) :
    classLevelArray R (e.classMap x) (e.vertex α,d) = classLevelArray Q x (α,d) := by
  let E := (minimalClassModel Q x).complex
  have hE := minimalClassModel_minimal Q x
  have hx : classOfComplex Q E = x := minimalClassModel_class Q x
  rw [← hx,classMap_complex,classLevelArray_complex_minimal Q E hE,
    classLevelArray_complex_minimal R (e.complex E) (e.complex_minimal hE)]
  exact e.levelArray_complex E α d

end HarmonicArtin.ReversibleQuiver.Iso

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_SeedEquiv
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
universe u
attribute [local instance] Classical.propDecidable
variable {V B J : Type u} {K : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)
local notation "U" => Q.stringQuiver step hstep N hN
open Zigzag.BasedComplex

variable (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
local notation "C" => complex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
local notation "F" => classLabelFunctor Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

def seedEquiv (v:V) (c:J) :
    (Σ _ : {a:J // N c a}, PUnit.{u+1}) ≃
      Index N (initialProjective U (K := K) (v,c) : Zigzag.BasedComplex U PUnit.{u+1}).placement where
  toFun x := ⟨PUnit.unit,x.1⟩
  invFun x := ⟨x.2,PUnit.unit⟩
  left_inv x := by rcases x with ⟨a,⟨⟩⟩; rfl
  right_inv x := by rcases x with ⟨⟨⟩,a⟩; rfl

lemma seed_eq (v:V) (c:J) :
    (C (initialProjective U (v,c) : Zigzag.BasedComplex U PUnit.{u+1})).reindex U
      (seedEquiv Q step hstep N hN (K := K) v c) =
      finiteSum U (fun a : {a:J // N c a} => (initialProjective U (v,a) : Zigzag.BasedComplex U PUnit.{u+1})) := by
  apply ext_placement_differential U
  · funext x
    rcases x with ⟨a,⟨⟩⟩
    rfl
  · change (matrix Q step hstep N hN orient μ A _ _ 0).submatrix _ _ =
      Matrix.blockDiagonal' (fun _ : {a:J // N c a} => (0 : Matrix PUnit.{u+1} PUnit.{u+1} (Zigzag U K)))
    rw [matrix_zero,Matrix.submatrix_zero]
    exact Matrix.blockDiagonal'_zero.symm

lemma classLabel_initial (v:V) (c:J) :
    F (initialClass U (v,c)) =
      classSum U (fun a : {a:J // N c a} => initialClass U (v,a)) := by
  change classOfComplex U (C (initialProjective U (v,c) : Zigzag.BasedComplex U PUnit.{u+1})) = _
  change _ = classSum U (fun a : {a:J // N c a} =>
    classOfComplex U (initialProjective U (v,a) : Zigzag.BasedComplex U PUnit.{u+1}))
  rw [classSum_complex]
  exact (classOfComplex_reindex U _ (seedEquiv Q step hstep N hN (K := K) v c)).trans
    (congrArg (classOfComplex U) (seed_eq Q step hstep N hN orient μ A ho hμ δ hA hroot hPF v c))

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_InvariantForm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
open _root_.Matrix
open scoped _root_.Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W:Type*} [Fintype S] [DecidableEq S] [Group W] [Fintype W]
  {M:CoxeterMatrix S} (cs:CoxeterSystem M W)

lemma invariantScale_balance (i j:S) :
    invariantScale cs i * cartan M i j=invariantScale cs j * cartan M i j := by
  have h:=invariantForm_symm cs (Pi.single i 1) (Pi.single j 1)
  rw [invariantForm_basis_row cs i (Pi.single j 1),invariantForm_basis_row cs j (Pi.single i 1)] at h
  simpa [Matrix.mulVec_single,← cartan_symm M i j,invariantScale] using h

include cs in

theorem cartan_posDef : (cartan M).PosDef := by
  have hs : (cartan M).IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    ext i j
    exact cartan_symm M j i
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hs
  intro x hx
  let z:S → ℝ := fun i=>x i/Real.sqrt (invariantScale cs i)
  have hz:z≠0 := by
    intro h
    apply hx
    ext i
    have hi:=congrFun h i
    exact (div_eq_zero_iff.mp hi).resolve_right (ne_of_gt (Real.sqrt_pos.2 (invariantScale_pos cs i)))
  have hpos:=invariantForm_pos cs z hz
  rw [invariantForm_matrix] at hpos
  have he : (∑ i,∑ j,invariantScale cs i*cartan M i j*z i*z j)=x ⬝ᵥ (cartan M *ᵥ x) := by
    simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij:cartan M i j=0
    · simp [hij]
    · have hd:=mul_right_cancel₀ hij (invariantScale_balance cs i j)
      have hn:=ne_of_gt (Real.sqrt_pos.2 (invariantScale_pos cs i))
      have hsq:=Real.sq_sqrt (invariantScale_pos cs i).le
      dsimp [z]
      rw [← hd]
      field_simp
      rw [hsq]
      ring
  rw [he] at hpos
  simpa only [star_trivial] using hpos

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_StrictChamber
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
open _root_.Matrix
open scoped _root_.Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W:Type*} [Fintype S] [DecidableEq S] [Group W] [Fintype W]
  {M:CoxeterMatrix S} (cs:CoxeterSystem M W)

include cs in

lemma exists_strict_chamber : ∃ p:S → ℝ,∀ i,(cartan M *ᵥ p) i=1 := by
  have hu := (cartan_posDef cs).isUnit
  have hs := (Matrix.mulVec_surjective_iff_isUnit (A:=cartan M)).mpr hu
  obtain ⟨p,hp⟩:=hs (fun _=>1)
  exact ⟨p,fun i=>congrFun hp i⟩

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_CartanForm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
open _root_.Matrix CoxeterExchange
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W:Type*} [Fintype S] [DecidableEq S] [Group W]
  {M:CoxeterMatrix S} (cs:CoxeterSystem M W)

lemma cartanForm_symm (M:CoxeterMatrix S) (x y:S→ℝ) : cartanForm M x y=cartanForm M y x := by
  simp only [cartanForm,Matrix.mulVec,dotProduct,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [cartan_symm M j i]
  ring

lemma cartanForm_single_right (M:CoxeterMatrix S) (x:S→ℝ) (i:S) :
    cartanForm M x (Pi.single i 1)=(cartan M *ᵥ x) i := by
  rw [cartanForm_symm,cartanForm_single_left]

lemma cartanForm_reflection (M:CoxeterMatrix S) (i:S) (x y:S→ℝ) :
    cartanForm M (simpleReflection M i x) (simpleReflection M i y)=cartanForm M x y := by
  simp only [simpleReflection_apply,cartanForm,Matrix.mulVec_sub,Matrix.mulVec_smul,
    dotProduct_sub,sub_dotProduct,dotProduct_smul,smul_dotProduct,smul_eq_mul]
  change cartanForm M x y - (cartan M *ᵥ x) i * cartanForm M (Pi.single i 1) y -
    (cartan M *ᵥ y) i * (cartanForm M x (Pi.single i 1) -
      (cartan M *ᵥ x) i * cartanForm M (Pi.single i 1) (Pi.single i 1)) = _
  rw [cartanForm_single_right,cartanForm_single_left,cartanForm_single_left]
  have hd : (cartan M *ᵥ Pi.single i (1:ℝ)) i = 2 := by simp [Matrix.mulVec_single]
  rw [hd]
  change cartanForm M x y - _ - _ = cartanForm M x y
  ring

lemma cartanForm_invariant (w:W) (x y:S→ℝ) :
    cartanForm M (representation cs w x) (representation cs w y)=cartanForm M x y := by
  obtain ⟨u,hu,he⟩:=cs.exists_isReduced w
  rw [he]
  clear hu he w
  induction u with
  | nil => simp
  | cons i u ih =>
    simpa only [cs.wordProd_cons,map_mul,LinearEquiv.mul_apply,representation_simple,
      cartanForm_reflection] using ih

lemma positive_root_sum_ge_one (w:W) (i:S)
    (h:∀j,0 ≤ representation cs w (Pi.single i 1) j) :
    1≤∑j,representation cs w (Pi.single i 1) j := by
  let v:=representation cs w (Pi.single i 1)
  have hq:cartanForm M v v=2 := by
    rw [cartanForm_invariant,cartanForm_single_left]
    simp [Matrix.mulVec_single]
  have hb:∀j k,cartan M j k≤(2:ℝ) := by
    intro j k
    by_cases he:j=k
    · subst k; simp
    · exact (cartan_off_nonpos M j k he).trans (by norm_num)
  have hh:cartanForm M v v≤2*(∑j,v j)^2 := by
    calc
      cartanForm M v v = ∑j,∑k,v j*cartan M j k*v k := by
        simp only [cartanForm,Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc]
      _ ≤ ∑j,∑k,v j*2*v k := by
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hb j k) (h j)) (h k)
      _ = 2*(∑j,v j)^2 := by
        simp only [Finset.sum_mul,Finset.mul_sum,pow_two]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        ring
  have hn:0≤∑j,v j:=Finset.sum_nonneg (fun j _=>h j)
  change 1≤∑j,v j
  nlinarith

lemma length_sum_bound (x:S→ℝ) (hx:cartan M *ᵥ x=1) (w:W) :
    (cs.length w:ℝ)+(∑i,representation cs w x i)≤∑i,x i := by
  have H:∀u:List S,cs.IsReduced u→
      (u.length:ℝ)+(∑i,representation cs (cs.wordProd u) x i)≤∑i,x i := by
    intro u
    induction u using List.reverseRecOn with
    | nil => simp
    | append_singleton u i ih =>
      intro hr
      have hru:cs.IsReduced u:=by simpa only [List.take_left] using hr.take u.length
      have hp:=ih hru
      have has:cs.length (cs.wordProd u*cs.simple i)=cs.length (cs.wordProd u)+1 := by
        simpa only [cs.wordProd_append,cs.wordProd_singleton,List.length_append,
          List.length_singleton,hru.eq] using hr.eq
      have hroot:=positive_root_sum_ge_one cs (cs.wordProd u) i (root_nonneg_of_ascent cs _ _ has)
      have he:simpleReflection M i x=x-Pi.single i 1 := by
        rw [simpleReflection_apply,hx]
        simp only [Pi.one_apply,one_smul]
      simp only [cs.wordProd_append,cs.wordProd_singleton,map_mul,LinearEquiv.mul_apply,
        representation_simple,he,map_sub,Pi.sub_apply,Finset.sum_sub_distrib,
        List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one]
      linarith
  obtain ⟨u,hu,he⟩:=cs.exists_isReduced w
  simpa only [←hu.eq,←he] using H u hu

include cs in

theorem finite_of_cartan_posDef (hC:(cartan M).PosDef) : Finite W := by
  let x: S→ℝ := (cartan M)⁻¹ *ᵥ 1
  have hx:cartan M *ᵥ x=1 := by
    dsimp [x]
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hC.isUnit),
      Matrix.one_mulVec]
  have hs:∀v:S→ℝ,cartanForm M v x=∑i,v i := by
    intro v
    simp only [cartanForm,hx,dotProduct,Pi.one_apply,mul_one]
  have hl:∀w:W,-(∑i,x i)≤∑i,representation cs w x i := by
    intro w
    let v:=representation cs w x
    have hn:=hC.posSemidef.dotProduct_mulVec_nonneg (v+x)
    simp only [star_trivial] at hn
    have hq:cartanForm M v v=cartanForm M x x:=cartanForm_invariant cs w x x
    have he:cartanForm M (v+x) (v+x)=cartanForm M v v+cartanForm M v x+
        cartanForm M x v+cartanForm M x x := by
      simp only [cartanForm,Matrix.mulVec_add,dotProduct_add,add_dotProduct]
      ring
    change 0 ≤ cartanForm M (v+x) (v+x) at hn
    rw [he,hq,cartanForm_symm M x v,hs,hs] at hn
    dsimp [v] at hn
    linarith
  obtain ⟨N,hN⟩:=exists_nat_ge (2*∑i,x i)
  have hb:∀w:W,cs.length w≤N := by
    intro w
    have h1:=length_sum_bound cs x hx w
    have h2:=hl w
    have h3:(cs.length w:ℝ)≤N:=by linarith
    exact_mod_cast h3
  apply Set.finite_univ_iff.mp
  apply ((List.finite_length_le S N).image cs.wordProd).subset
  intro w _
  obtain ⟨u,hu,he⟩:=cs.exists_isReduced w
  refine ⟨u,?_,he.symm⟩
  change u.length≤N
  rw [←hu.eq,←he]
  exact hb w

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_Form
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric.FiniteOrbit
open _root_.Matrix
open scoped _root_.Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S G:Type*} [Fintype S] [Group G] [Fintype G]
  (ρ:G →* (S → ℝ) ≃ₗ[ℝ] (S → ℝ))

variable [DecidableEq S]

variable {T:Type*}
  {M:CoxeterMatrix S} (ι:T → S) (g:T → G) (hg:∀ i,ρ (g i)=simpleReflection M (ι i))

include hg

lemma scale_balance (i j:T) :
    scale ρ (ι i)*cartan M (ι i) (ι j)=scale ρ (ι j)*cartan M (ι i) (ι j) := by
  have h:=form_symm ρ (Pi.single (ι i) 1) (Pi.single (ι j) 1)
  rw [form_basis_row ρ (ι i) (g i) (hg i) (Pi.single (ι j) 1),
    form_basis_row ρ (ι j) (g j) (hg j) (Pi.single (ι i) 1)] at h
  simpa [Matrix.mulVec_single,← cartan_symm M (ι i) (ι j),scale] using h

variable [Fintype T]

lemma form_matrix (x y:T → ℝ) :
    form ρ (∑ i,x i • Pi.single (ι i) 1) (∑ j,y j • Pi.single (ι j) 1)=
      ∑ i,∑ j,scale ρ (ι i)*cartan M (ι i) (ι j)*x i*y j := by
  rw [form_sum_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [form_smul_left,form_basis_row ρ (ι i) (g i) (hg i)]
  simp only [Matrix.mulVec_sum,Matrix.mulVec_smul,Finset.sum_apply,Pi.smul_apply,
    Matrix.mulVec_single,smul_eq_mul,Finset.mul_sum,scale,
    MulOpposite.op_one,one_smul,Matrix.col,Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem principal_posDef (hι:Function.Injective ι) :
    ((cartan M).submatrix ι ι).PosDef := by
  have hs : ((cartan M).submatrix ι ι).IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    ext i j
    exact cartan_symm M (ι j) (ι i)
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hs
  intro x hx
  let z:T → ℝ := fun i=>x i/Real.sqrt (scale ρ (ι i))
  have heval (v:T → ℝ) (i:T) : (∑ j,v j • Pi.single (ι j) (1:ℝ)) (ι i)=v i := by
    simp only [Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul]
    simp [hι.eq_iff]
  have hz:(∑ i,z i • Pi.single (ι i) (1:ℝ))≠0 := by
    intro h
    apply hx
    ext i
    have hi:=congrFun h (ι i)
    rw [heval] at hi
    exact (div_eq_zero_iff.mp hi).resolve_right (ne_of_gt (Real.sqrt_pos.2 (scale_pos ρ (ι i))))
  have hpos:=form_pos ρ _ hz
  rw [form_matrix ρ ι g hg] at hpos
  have he : (∑ i,∑ j,scale ρ (ι i)*cartan M (ι i) (ι j)*z i*z j)=
      x ⬝ᵥ (((cartan M).submatrix ι ι) *ᵥ x) := by
    simp only [Matrix.mulVec,dotProduct,Finset.mul_sum,Matrix.submatrix_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij:cartan M (ι i) (ι j)=0
    · simp [hij]
    · have hd:=mul_right_cancel₀ hij (scale_balance ρ ι g hg i j)
      have hn:=ne_of_gt (Real.sqrt_pos.2 (scale_pos ρ (ι i)))
      have hsq:=Real.sq_sqrt (scale_pos ρ (ι i)).le
      dsimp [z]
      rw [← hd]
      field_simp
      rw [hsq]
      ring
  rw [he] at hpos
  simpa only [star_trivial] using hpos

end HarmonicArtin.Geometric.FiniteOrbit

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_RootPair
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
open _root_.Matrix HarmonicArtin.CoxeterExchange
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W : Type*} [Fintype S] [DecidableEq S] [Group W]
  {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

lemma rootPair_symm (M : CoxeterMatrix S) (x y : S → ℝ) : rootPair M x y=rootPair M y x := by
  simp only [rootPair,Matrix.mulVec,dotProduct,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [cartan_symm M j i]
  ring

lemma rootPair_sub_left (M : CoxeterMatrix S) (x y z : S → ℝ) :
    rootPair M (x-y) z=rootPair M x z-rootPair M y z := by
  simp only [rootPair,sub_dotProduct]

lemma rootPair_sub_right (M : CoxeterMatrix S) (x y z : S → ℝ) :
    rootPair M x (y-z)=rootPair M x y-rootPair M x z := by
  simp only [rootPair,Matrix.mulVec_sub,dotProduct_sub]

lemma rootPair_smul_left (M : CoxeterMatrix S) (r : ℝ) (x y : S → ℝ) :
    rootPair M (r • x) y=r*rootPair M x y := by
  simp only [rootPair,smul_dotProduct,smul_eq_mul]

lemma rootPair_smul_right (M : CoxeterMatrix S) (r : ℝ) (x y : S → ℝ) :
    rootPair M x (r • y)=r*rootPair M x y := by
  rw [rootPair_symm,rootPair_smul_left,rootPair_symm M y x]

lemma rootPair_basis_left (M : CoxeterMatrix S) (i : S) (x : S → ℝ) :
    rootPair M (Pi.single i 1) x=rootRow M i x := by
  simp [rootPair,dotProduct,Pi.single_apply,rootRow_apply]

lemma rootPair_basis_right (M : CoxeterMatrix S) (i : S) (x : S → ℝ) :
    rootPair M x (Pi.single i 1)=rootRow M i x := by
  rw [rootPair_symm,rootPair_basis_left]

lemma reflection_rootPair (M : CoxeterMatrix S) (i : S) (x y : S → ℝ) :
    rootPair M (simpleReflection M i x) (simpleReflection M i y)=rootPair M x y := by
  simp only [simpleReflection_apply,← rootRow_apply,rootPair_sub_left,rootPair_sub_right,
    rootPair_smul_left,rootPair_smul_right,rootPair_basis_left,rootPair_basis_right,
    map_sub,map_smul,rootRow_single,cartan_diag,smul_eq_mul]
  ring

lemma representation_rootPair (w : W) (x y : S → ℝ) :
    rootPair M (representation cs w x) (representation cs w y)=rootPair M x y := by
  induction w using cs.simple_induction_left generalizing x y with
  | one => simp
  | mul_simple_left w i ih =>
    rw [map_mul,LinearEquiv.mul_apply,LinearEquiv.mul_apply,representation_simple,
      reflection_rootPair,ih]

lemma rootRow_representation (w : W) (s : S) (p : S → ℝ) :
    rootRow M s (representation cs w p)=rootPair M (representation cs w⁻¹ (Pi.single s 1)) p := by
  have h := representation_rootPair cs w (representation cs w⁻¹ (Pi.single s 1)) p
  rw [← LinearEquiv.mul_apply,← map_mul,mul_inv_cancel,map_one] at h
  change rootPair M (Pi.single s 1) (representation cs w p)=_ at h
  simpa only [rootPair_basis_left] using h

lemma rootPair_pos (M : CoxeterMatrix S) (p x : S → ℝ)
    (hp : ∀ i,0 < rootRow M i p) (hx : ∀ i,0 ≤ x i) (hne : x≠0) :
    0 < rootPair M x p := by
  obtain ⟨i,hi⟩ : ∃ i,x i≠0 := by
    by_contra! h
    exact hne (funext h)
  have hi' : 0 < x i := lt_of_le_of_ne (hx i) (Ne.symm hi)
  change 0 < ∑ j,x j*rootRow M j p
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hx j) (hp j).le)
    ⟨i,Finset.mem_univ _,mul_pos hi' (hp i)⟩

lemma rootPair_nonpos (M : CoxeterMatrix S) (p x : S → ℝ)
    (hp : ∀ i,0 < rootRow M i p) (hx : ∀ i,x i≤0) : rootPair M x p≤0 := by
  change (∑ j,x j*rootRow M j p)≤0
  exact Finset.sum_nonpos (fun j _ => mul_nonpos_of_nonpos_of_nonneg (hx j) (hp j).le)

theorem rootRow_pos_iff_left_ascent (p : S → ℝ) (hp : ∀ i,0 < rootRow M i p)
    (w : W) (s : S) :
    0 < rootRow M s (representation cs w p) ↔
      cs.length (cs.simple s*w)=cs.length w+1 := by
  rw [rootRow_representation]
  constructor
  · intro h
    rcases cs.length_mul_simple w⁻¹ s with ha | hd
    · simpa only [inverse_right_length,cs.length_inv] using ha
    · have hn := root_nonpos_of_descent cs w⁻¹ s hd
      exact (not_lt_of_ge (rootPair_nonpos M p _ hp hn) h).elim
  · intro h
    have ha : cs.length (w⁻¹*cs.simple s)=cs.length w⁻¹+1 := by
      simpa only [inverse_right_length,cs.length_inv] using h
    exact rootPair_pos M p _ hp (root_nonneg_of_ascent cs w⁻¹ s ha)
      (geometric_root_ne_zero cs w⁻¹ s)

theorem chamber_stabilizer (p : S → ℝ) (hp : ∀ i,0 < rootRow M i p)
    (w : W) (hw : representation cs w p=p) : w=1 := by
  by_contra h
  obtain ⟨s,hs⟩ := exists_right_descent cs (inv_ne_one.mpr h)
  have has : cs.length (cs.simple s*w)=cs.length w+1 :=
    (rootRow_pos_iff_left_ascent cs p hp w s).mp (by rw [hw]; exact hp s)
  rw [inverse_right_length,cs.length_inv] at hs
  omega

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_RootRowOrthogonalWord
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
open HarmonicArtin.CoxeterExchange
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W : Type*} [Fintype S] [DecidableEq S] [Group W]
  {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

theorem orthogonal_ascent_block (p : S → ℝ) (hp : ∀ i,0 < rootRow M i p)
    (u : List S) (hu : u.Nodup)
    (ho : ∀ i∈u,∀ j∈u,i≠j → cartan M i j=0)
    (w : W) (hw : ∀ i∈u,cs.length (cs.simple i*w)=cs.length w+1) :
    cs.length (cs.wordProd u*w)=u.length+cs.length w := by
  induction u with
  | nil => simp
  | cons i u ih =>
    obtain ⟨hin,hn⟩ := List.nodup_cons.mp hu
    have ho' : ∀ a∈u,∀ b∈u,a≠b → cartan M a b=0 :=
      fun a ha b hb => ho a (by simp [ha]) b (by simp [hb])
    have hw' : ∀ a∈u,cs.length (cs.simple a*w)=cs.length w+1 :=
      fun a ha => hw a (by simp [ha])
    have hi : 0 < rootRow M i (representation cs w p) :=
      (rootRow_pos_iff_left_ascent cs p hp w i).mpr (hw i (by simp))
    have hi' : 0 < rootRow M i (representation cs (cs.wordProd u*w) p) := by
      rw [map_mul,LinearEquiv.mul_apply,rootRow_orthogonal_word]
      · exact hi
      · intro j hj
        exact ho i (by simp) j (by simp [hj]) (fun he => hin (he ▸ hj))
    have ha := (rootRow_pos_iff_left_ascent cs p hp (cs.wordProd u*w) i).mp hi'
    rw [CoxeterSystem.wordProd_cons,mul_assoc,ha,ih hn ho' hw',List.length_cons]
    omega

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_SphericalCartanPos
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] [DecidableEq S]

theorem spherical_cartan_posDef (M:CoxeterMatrix S) (J:Set S) (hJ:IsSpherical M J) :
    ((cartan M).submatrix ((↑):J → S) ((↑):J → S)).PosDef := by
  let : Finite (coxeterParabolic M J) := hJ
  let : Fintype (coxeterParabolic M J) := Fintype.ofFinite _
  let ρ := (representation M.toCoxeterSystem).comp (coxeterParabolic M J).subtype
  let g:J → coxeterParabolic M J := fun i=>⟨M.simple i,
    Subgroup.subset_closure (Set.mem_image_of_mem _ i.property)⟩
  apply FiniteOrbit.principal_posDef ρ ((↑):J → S) g
  · intro i
    exact representation_simple M.toCoxeterSystem i
  · exact Subtype.val_injective

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_SphericalCartanPos2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
open HarmonicArtin.CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] [DecidableEq S]

theorem spherical_of_cartan_posDef (M:CoxeterMatrix S) (J:Set S)
    (hJ:((cartan M).submatrix ((↑):J→S) Subtype.val).PosDef) : IsSpherical M J := by
  have hC:(cartan (restrictedMatrix M J)).PosDef := by rwa [cartan_restricted]
  let : Finite (restrictedMatrix M J).Group := finite_of_cartan_posDef
    (restrictedMatrix M J).toCoxeterSystem hC
  have hr:coxeterParabolic M J≤(restrictionHom M J).range := by
    apply (Subgroup.closure_le _).mpr
    rintro y ⟨i,hi,rfl⟩
    exact ⟨(restrictedMatrix M J).toCoxeterSystem.simple ⟨i,hi⟩,restrictionHom_simple M J ⟨i,hi⟩⟩
  apply Finite.of_surjective
    (fun w=>(⟨restrictionHom M J w,restrictionHom_mem_parabolic M J w⟩:coxeterParabolic M J))
  intro y
  obtain ⟨w,hw⟩:=hr y.property
  exact ⟨w,Subtype.ext hw⟩

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionPacketPerm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V : Type} {K:Type*} [Field K]
  [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd
local notation "hn" => fusionQuiver_no_loops m d hd hdiag

noncomputable def fusionPacketPerm (s:V) : Equiv.Perm (FiniteHomotopyClass Q (K:=K)) :=
  classPacketPerm Q hn (fun L:FusionLabel m=>(s,L)) (fusionColor_orthogonal m d hd hdiag s)

noncomputable def fusionSignedPacketPerm (a:V × Bool) :
    Equiv.Perm (FiniteHomotopyClass Q (K:=K)) :=
  if a.2 then fusionPacketPerm m d hd hdiag a.1
  else (fusionPacketPerm m d hd hdiag a.1)⁻¹

noncomputable def fusionWordPacketPerm : List (V × Bool) →
    Equiv.Perm (FiniteHomotopyClass Q (K:=K))
  | [] => 1
  | a::w => fusionSignedPacketPerm m d hd hdiag a * fusionWordPacketPerm w

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionPacketOrbit
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V : Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd

noncomputable def fusionPacketOrbit (w:List (V × Bool)) (s:V) (L:FusionLabel m) :
    FiniteHomotopyClass Q (K:=ℂ) :=
  fusionWordPacketPerm m d hd hdiag w (initialClass Q (s,L))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionOrbitModel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag

noncomputable def fusionOrbitModel (w:List (V × Bool)) (s:V) (L:FusionLabel m) :
    FiniteModel Q (K:=ℂ) := minimalClassModel Q (O w s L)

abbrev FusionOrbitLayerIndex (w:List (V × Bool)) (s:V) (L:FusionLabel m) (q:ℤ) :=
  {i:(fusionOrbitModel m d hd hdiag w s L).Index //
    ((fusionOrbitModel m d hd hdiag w s L).complex.placement i).level=q}

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_ClosedNeighborhood
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver
universe u
variable {V A : Type u} (Q : ReversibleQuiver V A)

def closedNeighborhood (U : Set V) : Set V :=
  {β | β∈U ∨ ∃ α∈U, ∃ a : A,Q.source a=α ∧ Q.target a=β}

namespace Zigzag.BasedComplex
open _root_.Matrix
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {K : Type*} [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

def ClassCapOn (x : FiniteHomotopyClass Q (K:=K)) (U : Set V) (q : ℤ) : Prop :=
  ∀ i,((minimalClassModel Q x).complex.placement i).color∈U →
    ((minimalClassModel Q x).complex.placement i).level≤q

end Zigzag.BasedComplex
end HarmonicArtin.ReversibleQuiver

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionZeroLabel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E V:Type} {K:Type*} [Field K]
  [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E→ℕ) (d:V→V→FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hm:∀ e,2 ≤ m e)
local notation "Q" => fusionQuiver m d hd

noncomputable def fusionFamilyMultiplicity (x:FusionLabel m→FiniteHomotopyClass Q (K:=K))
    (q:ℤ) (v:V) : ℝ :=
  (∑ L,fusionWeight m L * classTotalVector Q (classLayer Q q (x L)) (v,fusionZeroLabel m hm)) /
    fusionWeight m (fusionZeroLabel m hm)

end HarmonicArtin

end OAI
end


