-- Prove2me | Definitions.Def_OAIQ225Ag002
-- name    : OAIQ225Ag002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:20:16.748194+00:00
-- url     : https://prove2.me/theorems/eb84b281-45a3-4a1b-84c5-e6aea7c07d57
-- title:
--   Definitions bundle OAIQ225Ag002 of the split of OpenAI, Harmonic heights and the Artin K(pi,1) conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HarmonicArtin.salvetti_cover_contractible`, carved from OpenAI's openai/math development (OpenAI, *Harmonic heights and the Artin K(pi,1) conjecture*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 292 declarations of OpenAI's Lean: 105 definitions, 3 inductive types or structures, 3 instances and 181 theorems. The definitions and types are `OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap`, `OAI.HarmonicArtin.ReversibleQuiver.Iso.path`, `OAI.HarmonicArtin.ReversibleQuiver.Path.dual`, `OAI.HarmonicArtin.ReversibleQuiver.Path.length`, `OAI.HarmonicArtin.ReversibleQuiver.Path.source`, `OAI.HarmonicArtin.ReversibleQuiver.Path.target`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.FiniteHomotopyClass`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.FiniteModel`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.FiniteModel.minimalRepresentative`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.FiniteModel.ofComplex`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.HomotopyEquivalence.negativeTwist`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.HomotopyEquivalence.positiveTwist`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.HomotopyEquivalence.refl`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.HomotopyEquivalence.symm`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.HomotopyEquivalence.trans`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.InverseTwistIndex`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.IsMinimal`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.Map.cocone`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.Map.coconeDifferential`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.Map.coconeMap`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.Map.coconePlacement`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.Map.comp`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.Map.cone`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.Map.coneDifferential`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.Map.coneMap`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.Map.conePlacement`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.Map.cotest`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.Map.identity`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.Map.negativeTwist`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.Map.positiveTwist`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.Map.test`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ScalarPivot`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ScalarPivot.Retained`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ScalarPivot.homotopy`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ScalarPivot.inclusionMap`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ScalarPivot.inverseValue`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ScalarPivot.reduced`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ScalarPivot.reducedDifferential`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ScalarPivot.reductionEquivalence`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ScalarPivot.reductionMap` and 68 more.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `ArtinGroups_Cancellation_Retained`, `ArtinGroups_Cancellation_ScalarPivot`, `ArtinGroups_Complexes_BasedComplexComplex`, `ArtinGroups_Complexes_CoconePlacement`, `ArtinGroups_Complexes_ConeMap`, `ArtinGroups_Complexes_ConePlacement`, `ArtinGroups_Complexes_FiniteHomotopySetoid`, `ArtinGroups_Complexes_Identity`, `ArtinGroups_Complexes_Initial`, `ArtinGroups_Complexes_InitialProjective`, `ArtinGroups_Complexes_InverseTwistDifferential`, `ArtinGroups_Complexes_InverseTwistIdentity`, `ArtinGroups_Complexes_InverseTwistIndex`, `ArtinGroups_Complexes_InverseTwistPlacement`, `ArtinGroups_Complexes_MinimalModel`, `ArtinGroups_Complexes_NormalizedInverseTwistHomotopy`, `ArtinGroups_Complexes_NormalizedReverseTwistHomotopy`, `ArtinGroups_Complexes_PacketConsEquiv`, `ArtinGroups_Complexes_PositiveTwistHomotopy`, `ArtinGroups_Complexes_Reindex`, `ArtinGroups_Complexes_ReverseTwistDifferential`, `ArtinGroups_Complexes_ReverseTwistIndexEquiv`, `ArtinGroups_Complexes_ReverseTwistProjection`, `ArtinGroups_Complexes_ReverseTwistProjectionCommute`, `ArtinGroups_Functors_Path`, `ArtinGroups_Functors_ReversibleQuiverMap`, `ArtinGroups_Harmonic_FusionVertex`, `ArtinGroups_Harmonic_GeneratorPlacement`, `ArtinGroups_Harmonic_Level`, `ArtinGroups_Quivers_CornerPath`, `ArtinGroups_Quivers_CornerScalar`, `ArtinGroups_Quivers_CotestPlacement`, `ArtinGroups_Quivers_Dual`, `ArtinGroups_Quivers_ExtArrow`, `ArtinGroups_Quivers_OrthogonalVertices`, `ArtinGroups_Quivers_PacketIndex`, `ArtinGroups_Quivers_Path`, `ArtinGroups_Quivers_SelfCornerEquiv`, `ArtinGroups_Quivers_SimpleEdge`, `ArtinGroups_Quivers_SmulMul`, `ArtinGroups_Quivers_TestIndex`, `ArtinGroups_Quivers_TestPlacement`, `ArtinGroups_Quivers_TestTransform`, `ArtinGroups_Quivers_VertexHom`.
--
--   **Imports.** It imports the bundles `OAIQ225Ag000` and `OAIQ225Ag001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ225Ag005`, `OAIQ225Ag006`, `OAIQ225Ag007` and `OAIQ225Ag008`.
-- source:
--   OpenAI, Harmonic heights and the Artin K(pi,1) conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Harmonic-heights-and-the-Artin-K-pi-1-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ225Ag000
import Definitions.Def_OAIQ225Ag001

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_VertexHom
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

def PositiveMatrix (M : Matrix I J (Q.Zigzag K)) : Prop :=
  ∀ i j, (M i j).vertex = 0

end Zigzag
end HarmonicArtin.ReversibleQuiver

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_GeneratorPlacement
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

namespace ReversibleQuiver.Zigzag

variable {V A K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

variable {I J L : Type*}

namespace BasedComplex

variable [Fintype I] [Fintype J] [Fintype L]

def IsMinimal (E : BasedComplex Q (K := K) I) : Prop :=
  PositiveMatrix Q E.differential

end BasedComplex
end ReversibleQuiver.Zigzag
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_CornerScalar
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

lemma corner_scalar {v : V} {x : Q.Zigzag K}
    (hx : vertexId Q v * x = x) (h0 : Homogeneous Q 0 x) :
    x = x.vertex v • vertexId Q v := by
  apply Zigzag.ext
  · ext w
    by_cases hw : w = v
    · subst w
      simp
    · have he := congrArg (fun z : Q.Zigzag K => z.vertex w) hx
      change (vertexId Q v).vertex w * x.vertex w = x.vertex w at he
      rw [vertexId_eval, ite_eq_right hw, MulZeroClass.zero_mul] at he
      simpa [vertexId_eval, hw] using he.symm
  · change x.arrow = x.vertex v • (0 : A → K)
    rw [smul_zero]
    exact h0.2.1 (by decide)
  · change x.token = x.vertex v • (0 : V → K)
    rw [smul_zero]
    exact h0.2.2 (by decide)

variable {I J : Type*}

lemma degree_vertex_support {p : I → GeneratorPlacement V}
    {q : J → GeneratorPlacement V} {M : Matrix I J (Q.Zigzag K)}
    {n v : ℤ} (hc : ProjectiveEntries Q p q M) (hd : MapDegree Q p q n v M)
    (i : I) (j : J) (w : V) (hne : (M i j).vertex w ≠ 0) :
    (p i).color = w ∧ (q j).color = w ∧
    (q j).cochain = (p i).cochain + n ∧
    (q j).internal = (p i).internal + v := by
  have hleft := congrArg (fun x : Q.Zigzag K => x.vertex w) (hc.1 i j)
  have hright := congrArg (fun x : Q.Zigzag K => x.vertex w) (hc.2 i j)
  have hpv : (p i).color = w := by
    by_contra h
    have hh : w ≠ (p i).color := Ne.symm h
    change (vertexId Q (p i).color).vertex w * (M i j).vertex w = (M i j).vertex w at hleft
    rw [vertexId_eval, ite_eq_right hh, MulZeroClass.zero_mul] at hleft
    exact hne hleft.symm
  have hqv : (q j).color = w := by
    by_contra h
    have hh : w ≠ (q j).color := Ne.symm h
    change (M i j).vertex w * (vertexId Q (q j).color).vertex w = (M i j).vertex w at hright
    rw [vertexId_eval, ite_eq_right hh, MulZeroClass.mul_zero] at hright
    exact hne hright.symm
  have hcq : (q j).cochain = (p i).cochain + n := by
    by_contra h
    have hz := (hd i j).1 h
    exact hne (by simp [hz])
  have hiq : (q j).internal = (p i).internal + v := by
    by_contra h
    have hh : v + (p i).internal - (q j).internal ≠ 0 := by omega
    have hz := (hd i j).2.1 hh
    exact hne (by rw [hz]; rfl)
  exact ⟨hpv, hqv, hcq, hiq⟩

namespace BasedComplex

variable [Fintype I]

theorem exists_pivot_of_not_minimal (E : BasedComplex Q (K := K) I)
    (hE : ¬E.IsMinimal Q) :
    ∃ i j : I, ∃ a : K, i ≠ j ∧ a ≠ 0 ∧
      (E.placement j).color = (E.placement i).color ∧
      (E.placement j).cochain = (E.placement i).cochain + 1 ∧
      (E.placement j).internal = (E.placement i).internal ∧
      E.differential i j = a • vertexId Q (E.placement i).color := by
  classical
  change ¬∀ i j, (E.differential i j).vertex = 0 at hE
  push Not at hE
  obtain ⟨i, j, hij⟩ := hE
  have hv : ∃ w, (E.differential i j).vertex w ≠ 0 := by
    by_contra h
    push Not at h
    exact hij (funext h)
  obtain ⟨w, hw⟩ := hv
  obtain ⟨hi, hj, hc, hu⟩ := degree_vertex_support Q E.entries E.degree i j w hw
  have hu' : (E.placement j).internal = (E.placement i).internal := by omega
  refine ⟨i, j, (E.differential i j).vertex w, ?_, hw, hj.trans hi.symm, hc, hu', ?_⟩
  · intro he
    subst j
    omega
  · have hdeg : Homogeneous Q 0 (E.differential i j) := by
      simpa only [zero_add, hu', sub_self] using (E.degree i j).2
    simpa only [hi] using corner_scalar Q (E.entries.1 i j) hdeg

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_Level
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

namespace ReversibleQuiver.Zigzag

variable {V A K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

lemma homogeneous_nonzero_degree {a : ℤ} {x : Q.Zigzag K}
    (ha : Homogeneous Q a x) (hx : x ≠ 0) : a = 0 ∨ a = 1 ∨ a = 2 := by
  by_contra h
  have h0 : a ≠ 0 := fun he => h (Or.inl he)
  have h1 : a ≠ 1 := fun he => h (Or.inr (Or.inl he))
  have h2 : a ≠ 2 := fun he => h (Or.inr (Or.inr he))
  apply hx
  exact Zigzag.ext (ha.1 h0) (ha.2.1 h1) (ha.2.2 h2)

end ReversibleQuiver.Zigzag
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_SmulMul
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

theorem smul_mul (a : K) (x y : Q.Zigzag K) :
    (a • x) * y = a • (x * y) := by
  apply Zigzag.ext
  · ext v
    simp only [vertex_mul, vertex_smul, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · ext e
    simp only [arrow_mul, arrow_smul, vertex_smul, leftScale, rightScale,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · ext v
    simp only [token_mul, token_smul, vertex_smul, arrow_smul, backtrack,
      Pi.mul_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, _root_.mul_add]
    congr 1
    · ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> ring

theorem mul_smul (a : K) (x y : Q.Zigzag K) :
    x * (a • y) = a • (x * y) := by
  apply Zigzag.ext
  · ext v
    simp only [vertex_mul, vertex_smul, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · ext e
    simp only [arrow_mul, arrow_smul, vertex_smul, leftScale, rightScale,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · ext v
    simp only [token_mul, token_smul, vertex_smul, arrow_smul, backtrack,
      Pi.mul_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, _root_.mul_add]
    congr 1
    · ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> ring

instance instAlgebra : Algebra K (Q.Zigzag K) :=
  Algebra.ofModule (smul_mul Q) (mul_smul Q)

lemma homogeneous_zero (a : ℤ) : Homogeneous Q a (0 : Q.Zigzag K) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

lemma homogeneous_add {a : ℤ} {x y : Q.Zigzag K}
    (hx : Homogeneous Q a x) (hy : Homogeneous Q a y) :
    Homogeneous Q a (x + y) := by
  exact ⟨fun h => by simp [hx.1 h, hy.1 h],
    fun h => by simp [hx.2.1 h, hy.2.1 h],
    fun h => by simp [hx.2.2 h, hy.2.2 h]⟩

omit [Fintype A] [DecidableEq V] in
lemma homogeneous_neg {a : ℤ} {x : Q.Zigzag K}
    (hx : Homogeneous Q a x) : Homogeneous Q a (-x) := by
  exact ⟨fun h => by change -x.vertex = 0; simp [hx.1 h],
    fun h => by change -x.arrow = 0; simp [hx.2.1 h],
    fun h => by change -x.token = 0; simp [hx.2.2 h]⟩

lemma homogeneous_sum {T : Type*} (t : Finset T) {a : ℤ}
    {f : T → Q.Zigzag K} (h : ∀ i ∈ t, Homogeneous Q a (f i)) :
    Homogeneous Q a (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using homogeneous_zero Q a
  | @insert i t hi iht =>
    rw [Finset.sum_insert hi]
    exact homogeneous_add Q (h i (Finset.mem_insert_self _ _))
      (iht fun j hj => h j (Finset.mem_insert_of_mem hj))

lemma homogeneous_mul {a b : ℤ} {x y : Q.Zigzag K}
    (hx : Homogeneous Q a x) (hy : Homogeneous Q b y) :
    Homogeneous Q (a + b) (x * y) := by
  by_cases hx0 : x = 0
  · subst x
    rw [MulZeroClass.zero_mul]
    exact homogeneous_zero Q _
  by_cases hy0 : y = 0
  · subst y
    rw [MulZeroClass.mul_zero]
    exact homogeneous_zero Q _
  rcases homogeneous_nonzero_degree Q hx hx0 with ha | ha | ha <;>
    rcases homogeneous_nonzero_degree Q hy hy0 with hb | hb | hb <;>
    subst a <;> subst b <;>
    simp_all [Homogeneous]
  all_goals
    ext e
    simp [leftScale, rightScale]

variable {I J L : Type*} {p : I → GeneratorPlacement V}
  {q : J → GeneratorPlacement V} {r : L → GeneratorPlacement V}

lemma projectiveEntries_zero :
    ProjectiveEntries Q p q (0 : Matrix I J (Q.Zigzag K)) := by
  constructor <;> intro i j <;> simp

lemma projectiveEntries_add {M N : Matrix I J (Q.Zigzag K)}
    (hM : ProjectiveEntries Q p q M) (hN : ProjectiveEntries Q p q N) :
    ProjectiveEntries Q p q (M + N) := by
  constructor
  · intro i j
    change vertexId Q _ * (M i j + N i j) = _
    rw [_root_.mul_add, hM.1, hN.1]
    rfl
  · intro i j
    change (M i j + N i j) * vertexId Q _ = _
    rw [_root_.add_mul, hM.2, hN.2]
    rfl

lemma projectiveEntries_neg {M : Matrix I J (Q.Zigzag K)}
    (hM : ProjectiveEntries Q p q M) : ProjectiveEntries Q p q (-M) := by
  constructor
  · intro i j
    change vertexId Q _ * (-M i j) = _
    rw [mul_neg, hM.1]
    rfl
  · intro i j
    change (-M i j) * vertexId Q _ = _
    rw [neg_mul, hM.2]
    rfl

lemma projectiveEntries_mul [Fintype J]
    {M : Matrix I J (Q.Zigzag K)} {N : Matrix J L (Q.Zigzag K)}
    (hM : ProjectiveEntries Q p q M) (hN : ProjectiveEntries Q q r N) :
    ProjectiveEntries Q p r (M * N) := by
  constructor
  · intro i k
    simp only [Matrix.mul_apply, Finset.mul_sum, ← _root_.mul_assoc, hM.1]
  · intro i k
    simp only [Matrix.mul_apply, Finset.sum_mul, _root_.mul_assoc, hN.2]

lemma projectiveEntries_identity [DecidableEq I] :
    ProjectiveEntries Q p p (projectiveIdentity Q (K := K) p) := by
  constructor <;> intro i j <;> by_cases h : i = j
  all_goals simp [projectiveIdentity, h, vertexId_mul_self]

lemma projectiveIdentity_mul [Fintype I] [DecidableEq I]
    {M : Matrix I J (Q.Zigzag K)} (hM : ProjectiveEntries Q p q M) :
    projectiveIdentity Q p * M = M := by
  apply Matrix.ext
  intro i j
  exact (Matrix.diagonal_mul (fun i => vertexId Q (K := K) (p i).color) M i j).trans
    (hM.1 i j)

lemma mul_projectiveIdentity [Fintype J] [DecidableEq J]
    {M : Matrix I J (Q.Zigzag K)} (hM : ProjectiveEntries Q p q M) :
    M * projectiveIdentity Q q = M := by
  apply Matrix.ext
  intro i j
  exact (Matrix.mul_diagonal (fun j => vertexId Q (K := K) (q j).color) M i j).trans
    (hM.2 i j)

lemma mapDegree_zero (n v : ℤ) :
    MapDegree Q p q n v (0 : Matrix I J (Q.Zigzag K)) :=
  fun _ _ => ⟨fun _ => rfl, homogeneous_zero Q _⟩

lemma mapDegree_add {n v : ℤ} {M N : Matrix I J (Q.Zigzag K)}
    (hM : MapDegree Q p q n v M) (hN : MapDegree Q p q n v N) :
    MapDegree Q p q n v (M + N) := by
  intro i j
  exact ⟨fun h => by simp [(hM i j).1 h, (hN i j).1 h],
    homogeneous_add Q (hM i j).2 (hN i j).2⟩

lemma mapDegree_neg {n v : ℤ} {M : Matrix I J (Q.Zigzag K)}
    (hM : MapDegree Q p q n v M) : MapDegree Q p q n v (-M) := by
  intro i j
  exact ⟨fun h => by simp [(hM i j).1 h], homogeneous_neg Q (hM i j).2⟩

lemma mapDegree_mul [Fintype J] {n v m w : ℤ}
    {M : Matrix I J (Q.Zigzag K)} {N : Matrix J L (Q.Zigzag K)}
    (hM : MapDegree Q p q n v M) (hN : MapDegree Q q r m w N) :
    MapDegree Q p r (n + m) (v + w) (M * N) := by
  intro i k
  constructor
  · intro h
    simp only [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hc : (q j).cochain = (p i).cochain + n
    · have he : (r k).cochain ≠ (q j).cochain + m := by omega
      rw [(hN j k).1 he, MulZeroClass.mul_zero]
    · rw [(hM i j).1 hc, MulZeroClass.zero_mul]
  · rw [Matrix.mul_apply]
    apply homogeneous_sum Q
    intro j _
    convert homogeneous_mul Q (hM i j).2 (hN j k).2 using 1
    all_goals try with_reducible_and_instances rfl
    ring

omit [Fintype A] in
lemma homogeneous_vertexId (v : V) : Homogeneous Q 0 (vertexId Q (K := K) v) :=
  ⟨fun h => (h rfl).elim, fun _ => rfl, fun _ => rfl⟩

lemma mapDegree_identity [DecidableEq I] :
    MapDegree Q p p 0 0 (projectiveIdentity Q (K := K) p) := by
  intro i j
  by_cases h : i = j
  · subst j
    constructor
    · intro hn
      exact (hn (by omega)).elim
    · simpa only [projectiveIdentity, Matrix.diagonal_apply_eq, zero_add, sub_self]
        using homogeneous_vertexId Q (K := K) (p i).color
  · have hz : projectiveIdentity Q (K := K) p i j = 0 :=
      Matrix.diagonal_apply_ne _ h
    rw [hz]
    exact ⟨fun _ => rfl, homogeneous_zero Q _⟩

end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Cancellation_ScalarPivot
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

lemma homogeneous_smul {a : ℤ} {x : Q.Zigzag K} (hx : Homogeneous Q a x) (r : K) :
    Homogeneous Q a (r • x) := by
  exact ⟨fun h => by simp [hx.1 h], fun h => by simp [hx.2.1 h],
    fun h => by simp [hx.2.2 h]⟩

variable {I J : Type*} [DecidableEq I] [DecidableEq J]

lemma projectiveEntries_single (p : I → GeneratorPlacement V)
    (q : J → GeneratorPlacement V) (i : I) (j : J) (x : Q.Zigzag K)
    (hl : vertexId Q (p i).color * x = x)
    (hr : x * vertexId Q (q j).color = x) :
    ProjectiveEntries Q p q (Matrix.single i j x) := by
  constructor <;> intro k l <;> by_cases hk : i = k <;> by_cases hl' : j = l
  all_goals subst_vars
  all_goals simp_all [Matrix.single]

lemma mapDegree_single (p : I → GeneratorPlacement V)
    (q : J → GeneratorPlacement V) (i : I) (j : J) (x : Q.Zigzag K)
    (n v : ℤ) (hc : (q j).cochain = (p i).cochain + n)
    (hx : Homogeneous Q (v + (p i).internal - (q j).internal) x) :
    MapDegree Q p q n v (Matrix.single i j x) := by
  intro k l
  by_cases hk : k = i
  · subst k
    by_cases hl : l = j
    · subst l
      simp only [Matrix.single_apply_same]
      exact ⟨fun h => (h hc).elim, hx⟩
    · have hz : Matrix.single i j x i l = 0 := by simp [Matrix.single, Ne.symm hl]
      rw [hz]
      exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
  · have hz : Matrix.single i j x k l = 0 := by simp [Matrix.single, Ne.symm hk]
    rw [hz]
    exact ⟨fun _ => rfl, homogeneous_zero Q _⟩

namespace BasedComplex

variable [Fintype I]

structure ScalarPivot (E : BasedComplex Q (K := K) I) where
  source : I
  target : I
  coefficient : K
  distinct : source ≠ target
  nonzero : coefficient ≠ 0
  color : (E.placement target).color = (E.placement source).color
  cochain : (E.placement target).cochain = (E.placement source).cochain + 1
  internal : (E.placement target).internal = (E.placement source).internal
  entry : E.differential source target = coefficient • vertexId Q (E.placement source).color

omit [DecidableEq I] in
lemma scalarPivot_of_not_minimal (E : BasedComplex Q (K := K) I) (hE : ¬E.IsMinimal Q) :
    Nonempty (ScalarPivot Q E) := by
  obtain ⟨i, j, a, hij, ha, hc, hn, hu, he⟩ := E.exists_pivot_of_not_minimal Q hE
  exact ⟨⟨i, j, a, hij, ha, hc, hn, hu, he⟩⟩

namespace ScalarPivot

variable {E : BasedComplex Q (K := K) I} (p : ScalarPivot Q E)

def inverseValue : Q.Zigzag K :=
  p.coefficient⁻¹ • vertexId Q (E.placement p.source).color

def homotopy : Matrix I I (Q.Zigzag K) :=
  Matrix.single p.target p.source (p.inverseValue Q)

omit [DecidableEq I] in
lemma inverseValue_left : vertexId Q (E.placement p.target).color * p.inverseValue Q =
    p.inverseValue Q := by
  dsimp only [inverseValue]
  rw [p.color, mul_smul_comm, vertexId_mul_self]

omit [DecidableEq I] in
lemma inverseValue_right : p.inverseValue Q * vertexId Q (E.placement p.source).color =
    p.inverseValue Q := by
  dsimp only [inverseValue]
  rw [smul_mul_assoc, vertexId_mul_self]

omit [DecidableEq I] in
lemma inverseValue_entry : p.inverseValue Q * E.differential p.source p.target =
    vertexId Q (E.placement p.target).color := by
  rw [inverseValue, p.entry, smul_mul_assoc, mul_smul_comm, vertexId_mul_self,
    smul_smul, inv_mul_cancel₀ p.nonzero, one_smul, p.color]

omit [DecidableEq I] in
lemma entry_inverseValue : E.differential p.source p.target * p.inverseValue Q =
    vertexId Q (E.placement p.source).color := by
  rw [inverseValue, p.entry, smul_mul_assoc, mul_smul_comm, vertexId_mul_self,
    smul_smul, mul_inv_cancel₀ p.nonzero, one_smul]

lemma homotopy_entries : ProjectiveEntries Q E.placement E.placement (p.homotopy Q) :=
  projectiveEntries_single Q _ _ _ _ _ (p.inverseValue_left Q) (p.inverseValue_right Q)

lemma homotopy_degree : MapDegree Q E.placement E.placement (-1) 0 (p.homotopy Q) := by
  apply mapDegree_single Q
  · have hc := p.cochain
    omega
  · have hh := homogeneous_smul Q
      (homogeneous_vertexId Q (K := K) (E.placement p.source).color) p.coefficient⁻¹
    simpa only [inverseValue, p.internal, zero_add, sub_self] using hh

lemma homotopy_square : p.homotopy Q * p.homotopy Q = 0 := by
  exact Matrix.single_mul_single_of_ne _ _ _ _ p.distinct _

lemma homotopy_retract : p.homotopy Q * E.differential * p.homotopy Q = p.homotopy Q := by
  rw [homotopy, Matrix.single_mul_mul_single, p.inverseValue_entry Q,
    p.inverseValue_left Q]

noncomputable def remainder : Matrix I I (Q.Zigzag K) :=
  GaussianCancellation.cornerRemainder (projectiveIdentity Q E.placement)
    E.differential (p.homotopy Q)

lemma remainder_entries : ProjectiveEntries Q E.placement E.placement (p.remainder Q) := by
  unfold remainder GaussianCancellation.cornerRemainder
  simp only [sub_eq_add_neg]
  exact projectiveEntries_add Q
    (projectiveEntries_add Q (projectiveEntries_identity Q)
      (projectiveEntries_neg Q (projectiveEntries_mul Q E.entries (p.homotopy_entries Q))))
    (projectiveEntries_neg Q (projectiveEntries_mul Q (p.homotopy_entries Q) E.entries))

lemma remainder_degree : MapDegree Q E.placement E.placement 0 0 (p.remainder Q) := by
  have h₁ := mapDegree_mul Q E.degree (p.homotopy_degree Q)
  have h₂ := mapDegree_mul Q (p.homotopy_degree Q) E.degree
  norm_num at h₁ h₂
  unfold remainder GaussianCancellation.cornerRemainder
  simp only [sub_eq_add_neg]
  exact mapDegree_add Q (mapDegree_add Q (mapDegree_identity Q) (mapDegree_neg Q h₁))
    (mapDegree_neg Q h₂)

lemma remainder_commutes : p.remainder Q * E.differential = E.differential * p.remainder Q :=
  GaussianCancellation.cornerRemainder_commutes _ _ _
    (projectiveIdentity_mul Q E.entries) (mul_projectiveIdentity Q E.entries) E.square_zero

lemma remainder_square : p.remainder Q * p.remainder Q = p.remainder Q :=
  GaussianCancellation.cornerRemainder_idempotent _ _ _
    (projectiveIdentity_mul Q (projectiveEntries_identity Q))
    (projectiveIdentity_mul Q E.entries) (mul_projectiveIdentity Q E.entries)
    (projectiveIdentity_mul Q (p.homotopy_entries Q))
    (mul_projectiveIdentity Q (p.homotopy_entries Q))
    E.square_zero (p.homotopy_square Q) (p.homotopy_retract Q)

lemma remainder_source_row (k : I) : p.remainder Q p.source k = 0 := by
  change (projectiveIdentity Q E.placement) p.source k -
      (E.differential * p.homotopy Q) p.source k -
      (p.homotopy Q * E.differential) p.source k = 0
  rw [homotopy, Matrix.single_mul_apply_of_ne _ _ _ _ _ p.distinct]
  by_cases hk : k = p.source
  · subst k
    rw [Matrix.mul_single_apply_same, p.entry_inverseValue Q]
    simp [projectiveIdentity]
  · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hk]
    simp [projectiveIdentity, Ne.symm hk]

lemma remainder_target_column (k : I) : p.remainder Q k p.target = 0 := by
  change (projectiveIdentity Q E.placement) k p.target -
      (E.differential * p.homotopy Q) k p.target -
      (p.homotopy Q * E.differential) k p.target = 0
  rw [homotopy, Matrix.mul_single_apply_of_ne _ _ _ _ _ (Ne.symm p.distinct)]
  by_cases hk : k = p.target
  · subst k
    rw [Matrix.single_mul_apply_same, p.inverseValue_entry Q]
    simp [projectiveIdentity]
  · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hk]
    simp [projectiveIdentity, hk]

lemma remainder_retained (k l : I) (hk : k ≠ p.target) (hl : l ≠ p.source) :
    p.remainder Q k l = (projectiveIdentity Q E.placement) k l := by
  change (projectiveIdentity Q E.placement) k l -
      (E.differential * p.homotopy Q) k l -
      (p.homotopy Q * E.differential) k l = _
  rw [homotopy, Matrix.mul_single_apply_of_ne _ _ _ _ _ hl,
    Matrix.single_mul_apply_of_ne _ _ _ _ _ hk, sub_zero, sub_zero]

end ScalarPivot
end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Cancellation_Retained
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ScalarPivot

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V] [Fintype I] [DecidableEq I]
  {E : BasedComplex Q (K := K) I} (p : ScalarPivot Q E)

abbrev Retained := {k : I // k ≠ p.source ∧ k ≠ p.target}

lemma retained_sum {X Y : Type*} (U : Matrix X I (Q.Zigzag K))
    (V : Matrix I Y (Q.Zigzag K)) (hU : ∀ i, U i p.target = 0)
    (hV : ∀ j, V p.source j = 0) (i : X) (j : Y) :
    (∑ k : p.Retained Q, U i k * V k j) = (U * V) i j := by
  apply Fintype.sum_of_injective (Subtype.val : p.Retained Q → I) Subtype.val_injective
  · intro k hk
    change U i k * V k j = 0
    by_cases hs : k = p.source
    · subst k
      rw [hV, MulZeroClass.mul_zero]
    · by_cases ht : k = p.target
      · subst k
        rw [hU, MulZeroClass.zero_mul]
      · exact (hk ⟨⟨k, hs, ht⟩, rfl⟩).elim
  · intro k
    rfl

noncomputable def reducedDifferential : Matrix I I (Q.Zigzag K) :=
  p.remainder Q * E.differential

lemma reducedDifferential_entries :
    ProjectiveEntries Q E.placement E.placement (p.reducedDifferential Q) :=
  projectiveEntries_mul Q (p.remainder_entries Q) E.entries

lemma reducedDifferential_degree :
    MapDegree Q E.placement E.placement 1 0 (p.reducedDifferential Q) := by
  exact mapDegree_mul Q (p.remainder_degree Q) E.degree

lemma reducedDifferential_square : p.reducedDifferential Q * p.reducedDifferential Q = 0 :=
  GaussianCancellation.cornerReduced_square _ _ _
    (projectiveIdentity_mul Q E.entries) (mul_projectiveIdentity Q E.entries) E.square_zero

lemma reducedDifferential_source_row (k : I) : p.reducedDifferential Q p.source k = 0 := by
  change (∑ j, p.remainder Q p.source j * E.differential j k) = 0
  simp only [p.remainder_source_row Q, MulZeroClass.zero_mul, Finset.sum_const_zero]

lemma reducedDifferential_target_column (k : I) : p.reducedDifferential Q k p.target = 0 := by
  unfold reducedDifferential
  rw [p.remainder_commutes Q]
  change (∑ j, E.differential k j * p.remainder Q j p.target) = 0
  simp only [p.remainder_target_column Q, MulZeroClass.mul_zero, Finset.sum_const_zero]

lemma remainder_mul_reduced : p.remainder Q * p.reducedDifferential Q = p.reducedDifferential Q := by
  unfold reducedDifferential
  rw [← _root_.mul_assoc, p.remainder_square Q]

lemma reduced_mul_remainder : p.reducedDifferential Q * p.remainder Q = p.reducedDifferential Q := by
  unfold reducedDifferential
  rw [_root_.mul_assoc, ← p.remainder_commutes Q, ← _root_.mul_assoc, p.remainder_square Q]

noncomputable def reduced : BasedComplex Q (K := K) (p.Retained Q) where
  placement := fun i => E.placement i
  differential := fun i j => p.reducedDifferential Q i j
  entries := ⟨fun i j => (p.reducedDifferential_entries Q).1 i j,
    fun i j => (p.reducedDifferential_entries Q).2 i j⟩
  degree := fun i j => p.reducedDifferential_degree Q i j
  square_zero := by
    apply Matrix.ext
    intro i j
    change (∑ k : p.Retained Q,
      p.reducedDifferential Q i k * p.reducedDifferential Q k j) = 0
    rw [p.retained_sum Q _ _ (p.reducedDifferential_target_column Q)
      (p.reducedDifferential_source_row Q), p.reducedDifferential_square Q]
    rfl

noncomputable def reductionMap : Map Q E (p.reduced Q) where
  matrix := fun i j => p.remainder Q i j
  entries := ⟨fun i j => (p.remainder_entries Q).1 i j,
    fun i j => (p.remainder_entries Q).2 i j⟩
  degree := fun i j => p.remainder_degree Q i j
  commute := by
    apply Matrix.ext
    intro i j
    change (E.differential * p.remainder Q) i j =
      ∑ k : p.Retained Q, p.remainder Q i k * p.reducedDifferential Q k j
    rw [p.retained_sum Q _ _ (p.remainder_target_column Q)
      (p.reducedDifferential_source_row Q), p.remainder_mul_reduced Q,
      ← p.remainder_commutes Q]
    rfl

noncomputable def inclusionMap : Map Q (p.reduced Q) E where
  matrix := fun i j => p.remainder Q i j
  entries := ⟨fun i j => (p.remainder_entries Q).1 i j,
    fun i j => (p.remainder_entries Q).2 i j⟩
  degree := fun i j => p.remainder_degree Q i j
  commute := by
    apply Matrix.ext
    intro i j
    change (∑ k : p.Retained Q, p.reducedDifferential Q i k * p.remainder Q k j) =
      (p.remainder Q * E.differential) i j
    rw [p.retained_sum Q _ _ (p.reducedDifferential_target_column Q)
      (p.remainder_source_row Q), p.reduced_mul_remainder Q]
    rfl

lemma reduction_inclusion :
    (p.reductionMap Q).matrix * (p.inclusionMap Q).matrix = p.remainder Q := by
  apply Matrix.ext
  intro i j
  change (∑ k : p.Retained Q, p.remainder Q i k * p.remainder Q k j) = p.remainder Q i j
  rw [p.retained_sum Q _ _ (p.remainder_target_column Q)
    (p.remainder_source_row Q), p.remainder_square Q]

lemma inclusion_reduction :
    (p.inclusionMap Q).matrix * (p.reductionMap Q).matrix =
      projectiveIdentity Q (p.reduced Q).placement := by
  apply Matrix.ext
  intro i j
  change (p.remainder Q * p.remainder Q) i j = _
  rw [p.remainder_square Q, p.remainder_retained Q i j i.property.2 j.property.1]
  change (Matrix.diagonal (fun k => vertexId Q (E.placement k).color)) i.val j.val =
    (Matrix.diagonal (fun k : p.Retained Q => vertexId Q (E.placement k).color)) i j
  by_cases h : i = j
  · subst j
    simp
  · have hv : i.val ≠ j.val := fun he => h (Subtype.ext he)
    simp [Matrix.diagonal, h, hv]

noncomputable def reductionEquivalence : HomotopyEquivalence Q E (p.reduced Q) where
  forward := p.reductionMap Q
  backward := p.inclusionMap Q
  sourceHomotopy := -p.homotopy Q
  targetHomotopy := 0
  sourceEntries := projectiveEntries_neg Q (p.homotopy_entries Q)
  targetEntries := projectiveEntries_zero Q
  sourceDegree := mapDegree_neg Q (p.homotopy_degree Q)
  targetDegree := mapDegree_zero Q (-1) 0
  sourceEquation := by
    rw [p.reduction_inclusion Q]
    exact GaussianCancellation.cornerRemainder_homotopy _ _ _
  targetEquation := by
    rw [p.inclusion_reduction Q, Matrix.mul_zero, Matrix.zero_mul, add_zero, add_zero]

lemma retained_card_lt : Fintype.card (p.Retained Q) < Fintype.card I := by
  apply Fintype.card_lt_of_injective_not_surjective (Subtype.val : p.Retained Q → I)
    Subtype.val_injective
  intro h
  obtain ⟨k, hk⟩ := h p.source
  exact k.property.1 hk

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ScalarPivot

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_Identity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

universe u
variable {V A K I J L : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]
  [Fintype I] [Fintype J] [Fintype L]
  [DecidableEq I] [DecidableEq J] [DecidableEq L]
  {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
  {G : BasedComplex Q (K := K) L}

namespace Map

noncomputable def identity (E : BasedComplex Q (K := K) I) : Map Q E E where
  matrix := projectiveIdentity Q E.placement
  entries := projectiveEntries_identity Q
  degree := mapDegree_identity Q
  commute := (mul_projectiveIdentity Q E.entries).trans (projectiveIdentity_mul Q E.entries).symm

omit [DecidableEq I] [DecidableEq J] [DecidableEq L] in
noncomputable def comp (f : Map Q E F) (g : Map Q F G) : Map Q E G where
  matrix := f.matrix * g.matrix
  entries := projectiveEntries_mul Q f.entries g.entries
  degree := mapDegree_mul Q f.degree g.degree
  commute := by
    rw [← Matrix.mul_assoc, f.commute, Matrix.mul_assoc, g.commute, Matrix.mul_assoc]

omit [DecidableEq I] [DecidableEq J] in
lemma conjugateBoundary (f : Map Q E F) (g : Map Q F E)
    (h : Matrix J J (Q.Zigzag K)) :
    f.matrix * (F.differential * h + h * F.differential) * g.matrix =
      E.differential * (f.matrix * h * g.matrix) +
        (f.matrix * h * g.matrix) * E.differential := by
  rw [Matrix.mul_add, Matrix.add_mul]
  congr 1
  · rw [← Matrix.mul_assoc f.matrix F.differential, ← f.commute]
    simp only [Matrix.mul_assoc]
  · simp only [Matrix.mul_assoc]
    rw [g.commute]

end Map

namespace HomotopyEquivalence

noncomputable def refl (E : BasedComplex Q (K := K) I) : HomotopyEquivalence Q E E where
  forward := Map.identity Q E
  backward := Map.identity Q E
  sourceHomotopy := 0
  targetHomotopy := 0
  sourceEntries := projectiveEntries_zero Q
  targetEntries := projectiveEntries_zero Q
  sourceDegree := mapDegree_zero Q (-1) 0
  targetDegree := mapDegree_zero Q (-1) 0
  sourceEquation := by
    change projectiveIdentity Q E.placement * projectiveIdentity Q E.placement = _
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
    exact projectiveIdentity_mul Q (projectiveEntries_identity Q)
  targetEquation := by
    change projectiveIdentity Q E.placement * projectiveIdentity Q E.placement = _
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
    exact projectiveIdentity_mul Q (projectiveEntries_identity Q)

noncomputable def trans (f : HomotopyEquivalence Q E F) (g : HomotopyEquivalence Q F G) :
    HomotopyEquivalence Q E G where
  forward := f.forward.comp Q g.forward
  backward := g.backward.comp Q f.backward
  sourceHomotopy := f.sourceHomotopy + f.forward.matrix * g.sourceHomotopy * f.backward.matrix
  targetHomotopy := g.targetHomotopy + g.backward.matrix * f.targetHomotopy * g.forward.matrix
  sourceEntries := projectiveEntries_add Q f.sourceEntries
    (projectiveEntries_mul Q (projectiveEntries_mul Q f.forward.entries g.sourceEntries)
      f.backward.entries)
  targetEntries := projectiveEntries_add Q g.targetEntries
    (projectiveEntries_mul Q (projectiveEntries_mul Q g.backward.entries f.targetEntries)
      g.forward.entries)
  sourceDegree := by
    have h := mapDegree_mul Q (mapDegree_mul Q f.forward.degree g.sourceDegree) f.backward.degree
    norm_num at h
    exact mapDegree_add Q f.sourceDegree h
  targetDegree := by
    have h := mapDegree_mul Q (mapDegree_mul Q g.backward.degree f.targetDegree) g.forward.degree
    norm_num at h
    exact mapDegree_add Q g.targetDegree h
  sourceEquation := by
    change (f.forward.matrix * g.forward.matrix) * (g.backward.matrix * f.backward.matrix) = _
    calc
      _ = f.forward.matrix * (g.forward.matrix * g.backward.matrix) * f.backward.matrix := by
        simp only [Matrix.mul_assoc]
      _ = f.forward.matrix * (projectiveIdentity Q F.placement +
          (F.differential * g.sourceHomotopy + g.sourceHomotopy * F.differential)) *
          f.backward.matrix := by rw [g.sourceEquation]
      _ = f.forward.matrix * f.backward.matrix + f.forward.matrix *
          (F.differential * g.sourceHomotopy + g.sourceHomotopy * F.differential) *
          f.backward.matrix := by
        rw [Matrix.mul_add, Matrix.add_mul]
        exact congrArg (fun M => M * f.backward.matrix +
          f.forward.matrix * (F.differential * g.sourceHomotopy +
            g.sourceHomotopy * F.differential) * f.backward.matrix)
          (mul_projectiveIdentity Q f.forward.entries)
      _ = _ := by
        rw [f.sourceEquation, Map.conjugateBoundary Q f.forward f.backward]
        simp only [Matrix.mul_add, Matrix.add_mul]
        abel
  targetEquation := by
    change (g.backward.matrix * f.backward.matrix) * (f.forward.matrix * g.forward.matrix) = _
    calc
      _ = g.backward.matrix * (f.backward.matrix * f.forward.matrix) * g.forward.matrix := by
        simp only [Matrix.mul_assoc]
      _ = g.backward.matrix * (projectiveIdentity Q F.placement +
          (F.differential * f.targetHomotopy + f.targetHomotopy * F.differential)) *
          g.forward.matrix := by rw [f.targetEquation]
      _ = g.backward.matrix * g.forward.matrix + g.backward.matrix *
          (F.differential * f.targetHomotopy + f.targetHomotopy * F.differential) *
          g.forward.matrix := by
        rw [Matrix.mul_add, Matrix.add_mul]
        exact congrArg (fun M => M * g.forward.matrix +
          g.backward.matrix * (F.differential * f.targetHomotopy +
            f.targetHomotopy * F.differential) * g.forward.matrix)
          (mul_projectiveIdentity Q g.backward.entries)
      _ = _ := by
        rw [g.targetEquation, Map.conjugateBoundary Q g.backward g.forward]
        simp only [Matrix.mul_add, Matrix.add_mul]
        abel

end HomotopyEquivalence

structure FiniteModel where
  Index : Type u
  fintype : Fintype Index
  decidableEq : DecidableEq Index
  complex : @BasedComplex V A K Q _ _ _ Index fintype

attribute [instance] FiniteModel.fintype FiniteModel.decidableEq

namespace FiniteModel

noncomputable def ofComplex {I : Type u} [Fintype I] [DecidableEq I]
    (E : BasedComplex Q (K := K) I) : FiniteModel.{u} Q (K := K) where
  Index := I
  fintype := inferInstance
  decidableEq := inferInstance
  complex := E

theorem exists_minimal (E : FiniteModel.{u} Q (K := K)) :
    ∃ F : FiniteModel.{u} Q (K := K), F.complex.IsMinimal Q ∧
      Nonempty (HomotopyEquivalence Q E.complex F.complex) := by
  have h : ∀ n (B : FiniteModel.{u} Q (K := K)), Fintype.card B.Index = n →
      ∃ F : FiniteModel.{u} Q (K := K), F.complex.IsMinimal Q ∧
        Nonempty (HomotopyEquivalence Q B.complex F.complex) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro B hn
      by_cases hm : B.complex.IsMinimal Q
      · exact ⟨B, hm, ⟨HomotopyEquivalence.refl Q B.complex⟩⟩
      · obtain ⟨p⟩ := scalarPivot_of_not_minimal Q B.complex hm
        let C := ofComplex Q (p.reduced Q)
        have hc : Fintype.card C.Index < n := by
          dsimp only [C, ofComplex]
          rw [← hn]
          exact p.retained_card_lt Q
        obtain ⟨F, hF, ⟨e⟩⟩ := ih (Fintype.card C.Index) hc C rfl
        exact ⟨F, hF, ⟨(p.reductionEquivalence Q).trans Q e⟩⟩
  exact h (Fintype.card E.Index) E rfl

end FiniteModel
end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ConePlacement
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V] [Fintype I] [Fintype J]
  {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}

namespace Map

def conePlacement (_f : Map Q E F) : I ⊕ J → GeneratorPlacement V
  | .inl i => ⟨(E.placement i).color, (E.placement i).cochain - 1,
      (E.placement i).internal⟩
  | .inr j => F.placement j

noncomputable def coneDifferential (f : Map Q E F) : Matrix (I ⊕ J) (I ⊕ J) (Q.Zigzag K) :=
  Matrix.fromBlocks (-E.differential) f.matrix 0 F.differential

lemma cone_entries (f : Map Q E F) :
    ProjectiveEntries Q (f.conePlacement Q) (f.conePlacement Q) (f.coneDifferential Q) := by
  constructor
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact (projectiveEntries_neg Q E.entries).1 i j
    · exact f.entries.1 i j
    · exact MulZeroClass.mul_zero _
    · exact F.entries.1 i j
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact (projectiveEntries_neg Q E.entries).2 i j
    · exact f.entries.2 i j
    · exact MulZeroClass.zero_mul _
    · exact F.entries.2 i j

lemma cone_degree (f : Map Q E F) :
    MapDegree Q (f.conePlacement Q) (f.conePlacement Q) 1 0 (f.coneDifferential Q) := by
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · constructor
    · intro hc
      have hd : (E.placement j).cochain ≠ (E.placement i).cochain + 1 := by
        intro he
        apply hc
        dsimp only [conePlacement]
        omega
      change -E.differential i j = 0
      rw [(E.degree i j).1 hd, neg_zero]
    · exact homogeneous_neg Q (E.degree i j).2
  · constructor
    · intro hc
      apply (f.degree i j).1
      intro he
      apply hc
      dsimp only [conePlacement]
      omega
    · exact (f.degree i j).2
  · exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
  · exact F.degree i j

lemma cone_square (f : Map Q E F) : f.coneDifferential Q * f.coneDifferential Q = 0 := by
  unfold coneDifferential
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.neg_mul, Matrix.mul_neg, E.square_zero, F.square_zero,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, f.commute, neg_add_cancel, neg_zero]
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j <;> rfl

noncomputable def cone (f : Map Q E F) : BasedComplex Q (K := K) (I ⊕ J) where
  placement := f.conePlacement Q
  differential := f.coneDifferential Q
  entries := f.cone_entries Q
  degree := f.cone_degree Q
  square_zero := f.cone_square Q

end Map
end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_Path
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver

namespace Path

variable {V A : Type*} (Q : ReversibleQuiver V A)

def source : Path V A → V
  | .inl v => v
  | .inr (.inl a) => Q.source a
  | .inr (.inr v) => v

def target : Path V A → V
  | .inl v => v
  | .inr (.inl a) => Q.target a
  | .inr (.inr v) => v

def length : Path V A → ℤ
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

end Path

namespace Zigzag

variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]

variable [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

attribute [local instance] OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathModule
noncomputable def pathBasis : Module.Basis (Path V A) K (Q.Zigzag K) :=
  Module.Basis.ofEquivFun (pathCoordinates Q)

lemma pathBasis_coordinates (p q : Path V A) :
    pathCoordinates Q (pathBasis Q (K := K) p) q = if p = q then 1 else 0 := by
  exact (pathBasis Q).repr_self_apply p q

omit [DecidableEq A] in
lemma sum_pathBasis (x : Q.Zigzag K) :
    ∑ p, pathCoordinates Q x p • pathBasis Q p = x := (pathBasis Q).sum_repr x

lemma pathBasis_vertex (v : V) : pathBasis Q (K := K) (.inl v) = vertexId Q v := by
  apply (pathCoordinates Q).injective
  funext p
  rw [pathBasis_coordinates]
  rcases p with w | a | w
  all_goals simp only [pathCoordinates_vertex, pathCoordinates_arrow, pathCoordinates_token]
  all_goals simp [vertexId, vertex, arrow, token, Pi.single_apply, eq_comm]

lemma pathBasis_arrow (a : A) : pathBasis Q (K := K) (.inr (.inl a)) = arrowBasis Q a := by
  apply (pathCoordinates Q).injective
  funext p
  rw [pathBasis_coordinates]
  rcases p with w | b | w
  all_goals simp only [pathCoordinates_vertex, pathCoordinates_arrow, pathCoordinates_token]
  all_goals simp [arrowBasis, vertex, arrow, token, Pi.single_apply, eq_comm]

lemma pathBasis_token (v : V) : pathBasis Q (K := K) (.inr (.inr v)) = tokenBasis Q v := by
  apply (pathCoordinates Q).injective
  funext p
  rw [pathBasis_coordinates]
  rcases p with w | a | w
  all_goals simp only [pathCoordinates_vertex, pathCoordinates_arrow, pathCoordinates_token]
  all_goals simp [tokenBasis, vertex, arrow, token, Pi.single_apply, eq_comm]

omit [Fintype V] [DecidableEq A] in
lemma coordinates_vertexId_left (v : V) (x : Q.Zigzag K) (p : Path V A) :
    pathCoordinates Q (vertexId Q v * x) p =
      if Path.source Q p = v then pathCoordinates Q x p else 0 := by
  rcases p with w | a | w
  · simp [Path.source, Pi.single_apply]
    rfl
  · simp [Path.source, leftScale, rightScale, Pi.single_apply]
    rfl
  · simp [Path.source, Pi.single_apply]
    rfl

omit [Fintype V] [DecidableEq A] in
lemma coordinates_vertexId_right (v : V) (x : Q.Zigzag K) (p : Path V A) :
    pathCoordinates Q (x * vertexId Q v) p =
      if Path.target Q p = v then pathCoordinates Q x p else 0 := by
  rcases p with w | a | w
  · simp [Path.target, Pi.single_apply]
    rfl
  · simp [Path.target, leftScale, rightScale, Pi.single_apply]
    rfl
  · simp [Path.target, Pi.single_apply]
    rfl

lemma pathBasis_left (p : Path V A) :
    vertexId Q (Path.source Q p) * pathBasis Q (K := K) p = pathBasis Q p := by
  apply (pathCoordinates Q).injective
  funext q
  rw [coordinates_vertexId_left, pathBasis_coordinates]
  by_cases h : p = q
  · subst q
    simp
  · simp [h]

lemma pathBasis_right (p : Path V A) :
    pathBasis Q (K := K) p * vertexId Q (Path.target Q p) = pathBasis Q p := by
  apply (pathCoordinates Q).injective
  funext q
  rw [coordinates_vertexId_right, pathBasis_coordinates]
  by_cases h : p = q
  · subst q
    simp
  · simp [h]

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] in
lemma coordinates_homogeneous (a : ℤ) (x : Q.Zigzag K) :
    Homogeneous Q a x ↔ ∀ p, Path.length p ≠ a → pathCoordinates Q x p = 0 := by
  constructor
  · intro h p hp
    rcases p with v | b | v
    · exact congrFun (h.1 (Ne.symm hp)) v
    · exact congrFun (h.2.1 (Ne.symm hp)) b
    · exact congrFun (h.2.2 (Ne.symm hp)) v
  · intro h
    constructor
    · intro ha
      funext v
      exact h (.inl v) (Ne.symm ha)
    constructor
    · intro ha
      funext b
      exact h (.inr (.inl b)) (Ne.symm ha)
    · intro ha
      funext v
      exact h (.inr (.inr v)) (Ne.symm ha)

lemma pathBasis_homogeneous (p : Path V A) :
    Homogeneous Q (Path.length p) (pathBasis Q (K := K) p) := by
  rw [coordinates_homogeneous]
  intro q hq
  rw [pathBasis_coordinates, ite_eq_right]
  intro hp
  exact hq (congrArg Path.length hp.symm)

omit [Fintype V] [DecidableEq A] in
lemma coordinates_corner {s t : V} {x : Q.Zigzag K}
    (hl : vertexId Q s * x = x) (hr : x * vertexId Q t = x)
    {p : Path V A} (hp : pathCoordinates Q x p ≠ 0) :
    Path.source Q p = s ∧ Path.target Q p = t := by
  constructor
  · by_contra h
    have he := congrArg (fun z => pathCoordinates Q z p) hl
    rw [coordinates_vertexId_left, ite_eq_right h] at he
    exact hp he.symm
  · by_contra h
    have he := congrArg (fun z => pathCoordinates Q z p) hr
    rw [coordinates_vertexId_right, ite_eq_right h] at he
    exact hp he.symm

omit [Fintype V] [DecidableEq A] in
lemma coordinates_mul_degree {a b : ℤ} {x y : Q.Zigzag K}
    (hx : Homogeneous Q a x) (hy : Homogeneous Q b y) {p : Path V A}
    (hp : pathCoordinates Q (x * y) p ≠ 0) : Path.length p = a + b := by
  by_contra h
  exact hp ((coordinates_homogeneous Q (a + b) (x * y)).mp (homogeneous_mul Q hx hy) p h)

end Zigzag
end HarmonicArtin.ReversibleQuiver

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_CornerPath
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver

namespace Zigzag

variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

abbrev CornerPath (s t : V) := {p : Path V A // Path.source Q p = s ∧ Path.target Q p = t}

omit [Fintype V] [DecidableEq A] in
lemma coordinates_zero (p : Path V A) : pathCoordinates Q (0 : Q.Zigzag K) p = 0 := by
  rcases p with v | a | v <;> rfl

omit [Fintype V] [DecidableEq A] in
lemma coordinates_add (x y : Q.Zigzag K) (p : Path V A) :
    pathCoordinates Q (x + y) p = pathCoordinates Q x p + pathCoordinates Q y p := by
  rcases p with v | a | v <;> rfl

omit [Fintype V] [DecidableEq A] in
lemma coordinates_smul (r : K) (x : Q.Zigzag K) (p : Path V A) :
    pathCoordinates Q (r • x) p = r * pathCoordinates Q x p := by
  rcases p with v | a | v <;> rfl

omit [Fintype V] [DecidableEq A] in
lemma coordinates_sum {B : Type*} (T : Finset B) (f : B → Q.Zigzag K) (p : Path V A) :
    pathCoordinates Q (∑ b ∈ T, f b) p = ∑ b ∈ T, pathCoordinates Q (f b) p := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [coordinates_zero]
  | @insert b T hb ih => simp [Finset.sum_insert hb, coordinates_add, ih]

omit [DecidableEq A] in
lemma sum_cornerPath {s t : V} (x : Q.Zigzag K)
    (hl : vertexId Q s * x = x) (hr : x * vertexId Q t = x) :
    ∑ p : CornerPath Q s t, pathCoordinates Q x p.val • pathBasis Q p.val = x := by
  classical
  conv_rhs => rw [← sum_pathBasis Q x]
  apply Fintype.sum_of_injective (fun p : CornerPath Q s t => p.val) Subtype.val_injective
  · intro p hp
    have hz : pathCoordinates Q x p = 0 := by
      by_contra h
      have hc := coordinates_corner Q hl hr h
      exact hp ⟨⟨p, hc⟩, rfl⟩
    rw [hz, zero_smul]
  · intro p
    rfl

lemma cornerPath_left {s t : V} (p : CornerPath Q s t) :
    vertexId Q s * pathBasis Q (K := K) p.val = pathBasis Q p.val := by
  simpa only [p.property.1] using pathBasis_left Q (K := K) p.val

lemma cornerPath_right {s t : V} (p : CornerPath Q s t) :
    pathBasis Q (K := K) p.val * vertexId Q t = pathBasis Q p.val := by
  simpa only [p.property.2] using pathBasis_right Q (K := K) p.val

omit [DecidableEq A] in
lemma sum_cornerPath_mul {s t : V} (x y : Q.Zigzag K)
    (hl : vertexId Q s * x = x) (hr : x * vertexId Q t = x) :
    ∑ p : CornerPath Q s t, pathCoordinates Q x p.val • (pathBasis Q p.val * y) = x * y := by
  conv_rhs => rw [← sum_cornerPath Q x hl hr]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _
  exact (smul_mul Q _ _ _).symm

omit [DecidableEq A] in
lemma coordinates_mul_expansion {s t : V} (x y : Q.Zigzag K)
    (hl : vertexId Q s * x = x) (hr : x * vertexId Q t = x) (r : Path V A) :
    ∑ p : CornerPath Q s t, pathCoordinates Q x p.val *
      pathCoordinates Q (pathBasis Q p.val * y) r = pathCoordinates Q (x * y) r := by
  rw [← sum_cornerPath_mul Q x y hl hr, coordinates_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact (coordinates_smul Q _ _ _).symm

end Zigzag
end HarmonicArtin.ReversibleQuiver

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_Dual
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver

namespace Path

variable {V A : Type*} (Q : ReversibleQuiver V A)

def dual : Path V A → Path V A
  | .inl v => .inr (.inr v)
  | .inr (.inl a) => .inr (.inl (Q.reverse a))
  | .inr (.inr v) => .inl v

@[simp] lemma dual_dual (p : Path V A) : dual Q (dual Q p) = p := by
  rcases p with v | a | v <;> simp [dual]

@[simp] lemma source_dual (p : Path V A) : source Q (dual Q p) = target Q p := by
  rcases p with v | a | v
  · rfl
  · exact Q.source_reverse a
  · rfl

@[simp] lemma target_dual (p : Path V A) : target Q (dual Q p) = source Q p := by
  rcases p with v | a | v
  · rfl
  · exact Q.target_reverse a
  · rfl

lemma length_dual (p : Path V A) : length (dual Q p) = 2 - length p := by
  rcases p with v | a | v <;> rfl

end Path

namespace Zigzag

variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

def cornerDual (s t : V) : CornerPath Q s t ≃ CornerPath Q t s where
  toFun p := ⟨Path.dual Q p.val, by simpa only [Path.source_dual, Path.target_dual] using p.property.symm⟩
  invFun p := ⟨Path.dual Q p.val, by simpa only [Path.source_dual, Path.target_dual] using p.property.symm⟩
  left_inv p := by apply Subtype.ext; exact Path.dual_dual Q p.val
  right_inv p := by apply Subtype.ext; exact Path.dual_dual Q p.val

lemma coordinates_trace (x : Q.Zigzag K) (p : Path V A) :
    pathCoordinates Q x p = trace Q (x * pathBasis Q (Path.dual Q p)) := by
  rcases p with v | a | v
  · simp only [Path.dual, pathBasis_token, trace_mul_tokenBasis, pathCoordinates_vertex]
  · simp only [Path.dual, pathBasis_arrow, trace_mul_arrowBasis, pathCoordinates_arrow]
  · rw [Path.dual, pathBasis_vertex]
    exact (trace_mul_vertexBasis Q x v).symm

omit [DecidableEq A] in
lemma sum_dual_cornerPath {s t : V} (x : Q.Zigzag K)
    (hl : vertexId Q t * x = x) (hr : x * vertexId Q s = x) :
    ∑ p : CornerPath Q s t, pathCoordinates Q x (Path.dual Q p.val) •
      pathBasis Q (Path.dual Q p.val) = x := by
  classical
  calc
    _ = ∑ p : CornerPath Q t s, pathCoordinates Q x p.val • pathBasis Q p.val := by
      apply Fintype.sum_equiv (cornerDual Q s t)
      intro p
      rfl
    _ = x := sum_cornerPath Q x hl hr

lemma dual_right_action {s t α : V} (x : Q.Zigzag K)
    (hl : vertexId Q s * x = x)
    (q : CornerPath Q α t) :
    ∑ p : CornerPath Q α s, pathCoordinates Q (pathBasis Q p.val * x) q.val •
      pathBasis Q (Path.dual Q p.val) = x * pathBasis Q (Path.dual Q q.val) := by
  have hl' : vertexId Q s * (x * pathBasis Q (Path.dual Q q.val)) =
      x * pathBasis Q (Path.dual Q q.val) := by
    rw [← _root_.mul_assoc, hl]
  have hr' : (x * pathBasis Q (Path.dual Q q.val)) * vertexId Q α =
      x * pathBasis Q (Path.dual Q q.val) := by
    rw [_root_.mul_assoc]
    exact congrArg (fun z => x * z) (cornerPath_right Q ((cornerDual Q α t) q))
  conv_rhs => rw [← sum_dual_cornerPath Q _ hl' hr']
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  rw [coordinates_trace, coordinates_trace, Path.dual_dual]
  rw [trace_mul_comm Q (x * pathBasis Q (Path.dual Q q.val)) (pathBasis Q p.val)]
  exact congrArg (trace Q) (_root_.mul_assoc _ _ _)

end Zigzag
end HarmonicArtin.ReversibleQuiver

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_TestIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J L : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

abbrev TestIndex (p : I → HarmonicArtin.GeneratorPlacement V) (α : V) :=
  (i : I) × CornerPath Q α (p i).color

noncomputable def testMatrix (p : I → HarmonicArtin.GeneratorPlacement V)
    (q : J → HarmonicArtin.GeneratorPlacement V) (α : V)
    (M : Matrix I J (Q.Zigzag K)) : Matrix (TestIndex Q p α) (TestIndex Q q α) K :=
  fun u v => pathCoordinates Q (pathBasis Q u.2.val * M u.1 v.1) v.2.val

omit [DecidableEq A] in
lemma testMatrix_zero (p : I → HarmonicArtin.GeneratorPlacement V)
    (q : J → HarmonicArtin.GeneratorPlacement V) (α : V) :
    testMatrix Q p q α (0 : Matrix I J (Q.Zigzag K)) = 0 := by
  apply Matrix.ext
  intro u v
  exact (congrArg (fun x => pathCoordinates Q x v.2.val)
    (MulZeroClass.mul_zero (pathBasis Q u.2.val))).trans (coordinates_zero Q v.2.val)

lemma testMatrix_mul [Fintype J]
    {p : I → HarmonicArtin.GeneratorPlacement V}
    {q : J → HarmonicArtin.GeneratorPlacement V}
    {r : L → HarmonicArtin.GeneratorPlacement V} (α : V)
    {M : Matrix I J (Q.Zigzag K)} (N : Matrix J L (Q.Zigzag K))
    (hM : ProjectiveEntries Q p q M) :
    testMatrix Q p q α M * testMatrix Q q r α N = testMatrix Q p r α (M * N) := by
  apply Matrix.ext
  intro u v
  simp only [Matrix.mul_apply, Fintype.sum_sigma, testMatrix]
  rw [Finset.mul_sum, coordinates_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hl : vertexId Q α * (pathBasis Q u.2.val * M u.1 j) =
      pathBasis Q u.2.val * M u.1 j := by
    rw [← _root_.mul_assoc, cornerPath_left Q u.2]
  have hr : (pathBasis Q u.2.val * M u.1 j) * vertexId Q (q j).color =
      pathBasis Q u.2.val * M u.1 j := by
    rw [_root_.mul_assoc, hM.2 u.1 j]
  exact (coordinates_mul_expansion Q _ (N j v.1) hl hr v.2.val).trans
    (congrArg (fun x => pathCoordinates Q x v.2.val) (_root_.mul_assoc _ _ _))

def scalarCornerMatrix (α : V) (M : Matrix I J K) : Matrix I J (Q.Zigzag K) :=
  fun i j => M i j • vertexId Q α

omit [Fintype V] [DecidableEq A] in
lemma scalarCornerMatrix_zero (α : V) :
    scalarCornerMatrix Q α (0 : Matrix I J K) = 0 := by
  apply Matrix.ext
  intro i j
  exact zero_smul _ _

omit [Fintype V] [DecidableEq A] in
lemma scalarCornerMatrix_mul [Fintype J] (α : V) (M : Matrix I J K) (N : Matrix J L K) :
    scalarCornerMatrix Q α M * scalarCornerMatrix Q α N =
      scalarCornerMatrix Q α (M * N) := by
  apply Matrix.ext
  intro i k
  simp only [Matrix.mul_apply, scalarCornerMatrix, smul_mul, mul_smul, vertexId_mul_self,
    smul_smul, Finset.sum_smul, mul_comm]

omit [Fintype V] [DecidableEq A] in
lemma scalarCornerMatrix_entries (α : V)
    (p : I → HarmonicArtin.GeneratorPlacement V) (q : J → HarmonicArtin.GeneratorPlacement V)
    (hp : ∀ i, (p i).color = α) (hq : ∀ j, (q j).color = α) (M : Matrix I J K) :
    ProjectiveEntries Q p q (scalarCornerMatrix Q α M) := by
  constructor
  · intro i j
    change vertexId Q (p i).color * (M i j • vertexId Q α) = _
    rw [hp i, mul_smul, vertexId_mul_self]
    rfl
  · intro i j
    change (M i j • vertexId Q α) * vertexId Q (q j).color = _
    rw [hq j, smul_mul, vertexId_mul_self]
    rfl

end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_TestPlacement
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.dual_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.source_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.target_dual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

def testPlacement (p : I → HarmonicArtin.GeneratorPlacement V) (α : V) :
    TestIndex Q p α → HarmonicArtin.GeneratorPlacement V :=
  fun u => ⟨α, (p u.1).cochain, (p u.1).internal + Path.length u.2.val⟩

lemma testMatrix_degree {p : I → HarmonicArtin.GeneratorPlacement V}
    {q : J → HarmonicArtin.GeneratorPlacement V} (α : V)
    {n v : ℤ} {M : Matrix I J (Q.Zigzag K)} (hM : MapDegree Q p q n v M) :
    MapDegree Q (testPlacement Q p α) (testPlacement Q q α) n v
      (scalarCornerMatrix Q α (testMatrix Q p q α M)) := by
  intro a b
  constructor
  · intro hc
    change (pathCoordinates Q (pathBasis Q a.2.val * M a.1 b.1) b.2.val) • vertexId Q α = 0
    rw [(hM a.1 b.1).1 hc, MulZeroClass.mul_zero, coordinates_zero, zero_smul]
  · change Homogeneous Q (v + ((p a.1).internal + Path.length a.2.val) -
      ((q b.1).internal + Path.length b.2.val))
      ((pathCoordinates Q (pathBasis Q a.2.val * M a.1 b.1) b.2.val) • vertexId Q α)
    by_cases hz : pathCoordinates Q (pathBasis Q a.2.val * M a.1 b.1) b.2.val = 0
    · rw [hz, zero_smul]
      exact homogeneous_zero Q _
    · have he := coordinates_mul_degree Q (pathBasis_homogeneous Q a.2.val)
        (hM a.1 b.1).2 hz
      have hd : v + ((p a.1).internal + Path.length a.2.val) -
          ((q b.1).internal + Path.length b.2.val) = 0 := by omega
      rw [hd]
      exact homogeneous_smul Q (homogeneous_vertexId Q α) _

noncomputable def evaluationMatrix (p : I → HarmonicArtin.GeneratorPlacement V) (α : V) :
    Matrix (TestIndex Q p α) I (Q.Zigzag K) := by
  classical
  exact fun u i => if u.1 = i then pathBasis Q u.2.val else 0

lemma evaluation_entries (p : I → HarmonicArtin.GeneratorPlacement V) (α : V) :
    ProjectiveEntries Q (testPlacement Q p α) p (evaluationMatrix Q p α (K := K)) := by
  classical
  constructor
  · intro u i
    dsimp only [evaluationMatrix, testPlacement]
    split_ifs
    · exact cornerPath_left Q u.2
    · exact MulZeroClass.mul_zero _
  · intro u i
    dsimp only [evaluationMatrix]
    split_ifs with h
    · subst i
      exact cornerPath_right Q u.2
    · exact MulZeroClass.zero_mul _

lemma evaluation_degree (p : I → HarmonicArtin.GeneratorPlacement V) (α : V) :
    MapDegree Q (testPlacement Q p α) p 0 0 (evaluationMatrix Q p α (K := K)) := by
  classical
  intro u i
  by_cases hi : u.1 = i
  · subst i
    have hev : evaluationMatrix Q p α (K := K) u u.1 = pathBasis Q u.2.val := ite_eq_left rfl
    rw [hev]
    constructor
    · intro h
      exact (h (by simp [testPlacement])).elim
    · convert pathBasis_homogeneous Q (K := K) u.2.val using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [testPlacement]
      omega
  · have hev : evaluationMatrix Q p α (K := K) u i = 0 := ite_eq_right hi
    rw [hev]
    exact ⟨fun _ => rfl, homogeneous_zero Q _⟩

omit [DecidableEq A] in
lemma evaluation_mul [Fintype I]
    (p : I → HarmonicArtin.GeneratorPlacement V)
    (α : V)
    (M : Matrix I J (Q.Zigzag K)) (u : TestIndex Q p α) (j : J) :
    (evaluationMatrix Q p α (K := K) * M) u j = pathBasis Q u.2.val * M u.1 j := by
  classical
  rw [Matrix.mul_apply]
  simp only [evaluationMatrix, ite_mul, MulZeroClass.zero_mul]
  simp

lemma testMatrix_evaluation [Fintype J]
    (p : I → HarmonicArtin.GeneratorPlacement V)
    (q : J → HarmonicArtin.GeneratorPlacement V) (α : V)
    {M : Matrix I J (Q.Zigzag K)} (hM : ProjectiveEntries Q p q M)
    (u : TestIndex Q p α) (j : J) :
    (scalarCornerMatrix Q α (testMatrix Q p q α M) * evaluationMatrix Q q α (K := K)) u j =
      pathBasis Q u.2.val * M u.1 j := by
  classical
  simp only [Matrix.mul_apply, Fintype.sum_sigma, evaluationMatrix, scalarCornerMatrix,
    testMatrix, mul_ite, MulZeroClass.mul_zero]
  rw [Finset.sum_eq_single j]
  · simp only [smul_mul, cornerPath_left]
    apply sum_cornerPath Q
    · rw [← _root_.mul_assoc, cornerPath_left]
    · rw [_root_.mul_assoc, hM.2 u.1 j]
  · intro b _ hbj
    apply Finset.sum_eq_zero
    intro c _
    exact ite_eq_right hbj
  · simp

namespace BasedComplex

variable [Fintype I]

noncomputable def testComplex (E : BasedComplex Q (K := K) I) (α : V) :
    BasedComplex Q (K := K) (TestIndex Q E.placement α) where
  placement := testPlacement Q E.placement α
  differential := scalarCornerMatrix Q α (testMatrix Q E.placement E.placement α E.differential)
  entries := scalarCornerMatrix_entries Q α _ _ (fun _ => rfl) (fun _ => rfl) _
  degree := testMatrix_degree Q α E.degree
  square_zero := by
    rw [scalarCornerMatrix_mul, testMatrix_mul Q α _ E.entries, E.square_zero,
      testMatrix_zero, scalarCornerMatrix_zero]

noncomputable def evaluation (E : BasedComplex Q (K := K) I) (α : V) :
    Map Q (E.testComplex Q α) E where
  matrix := evaluationMatrix Q E.placement α
  entries := evaluation_entries Q _ α
  degree := evaluation_degree Q _ α
  commute := by
    apply Matrix.ext
    intro u i
    exact (testMatrix_evaluation Q _ _ α E.entries u i).trans
      (evaluation_mul Q _ α E.differential u i).symm

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_CotestPlacement
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

def cotestPlacement (p : I → HarmonicArtin.GeneratorPlacement V) (α : V) :
    TestIndex Q p α → HarmonicArtin.GeneratorPlacement V :=
  fun u => ⟨α, (p u.1).cochain, (p u.1).internal + Path.length u.2.val - 2⟩

lemma cotestMatrix_degree {p : I → HarmonicArtin.GeneratorPlacement V}
    {q : J → HarmonicArtin.GeneratorPlacement V} (α : V)
    {n v : ℤ} {M : Matrix I J (Q.Zigzag K)} (hM : MapDegree Q p q n v M) :
    MapDegree Q (cotestPlacement Q p α) (cotestPlacement Q q α) n v
      (scalarCornerMatrix Q α (testMatrix Q p q α M)) := by
  intro a b
  have he := testMatrix_degree Q α hM a b
  constructor
  · exact he.1
  · convert he.2 using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [cotestPlacement, testPlacement]
    ring

noncomputable def coevaluationMatrix (p : I → HarmonicArtin.GeneratorPlacement V) (α : V) :
    Matrix I (TestIndex Q p α) (Q.Zigzag K) := by
  classical
  exact fun i u => if i = u.1 then pathBasis Q (Path.dual Q u.2.val) else 0

lemma coevaluation_entries (p : I → HarmonicArtin.GeneratorPlacement V) (α : V) :
    ProjectiveEntries Q p (cotestPlacement Q p α)
      (coevaluationMatrix Q p α (K := K)) := by
  classical
  constructor
  · intro i u
    dsimp only [coevaluationMatrix]
    split_ifs with h
    · subst i
      exact cornerPath_left Q ((cornerDual Q α (p u.1).color) u.2)
    · exact MulZeroClass.mul_zero _
  · intro i u
    dsimp only [coevaluationMatrix, cotestPlacement]
    split_ifs
    · exact cornerPath_right Q ((cornerDual Q α (p u.1).color) u.2)
    · exact MulZeroClass.zero_mul _

lemma coevaluation_degree (p : I → HarmonicArtin.GeneratorPlacement V) (α : V) :
    MapDegree Q p (cotestPlacement Q p α) 0 0
      (coevaluationMatrix Q p α (K := K)) := by
  classical
  intro i u
  by_cases hi : i = u.1
  · subst i
    have hev : coevaluationMatrix Q p α (K := K) u.1 u =
        pathBasis Q (Path.dual Q u.2.val) := ite_eq_left rfl
    rw [hev]
    constructor
    · intro h
      exact (h (by simp [cotestPlacement])).elim
    · convert pathBasis_homogeneous Q (K := K) (Path.dual Q u.2.val) using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [cotestPlacement]
      rw [Path.length_dual]
      omega
  · have hev : coevaluationMatrix Q p α (K := K) i u = 0 := ite_eq_right hi
    rw [hev]
    exact ⟨fun _ => rfl, homogeneous_zero Q _⟩

omit [DecidableEq A] in
lemma mul_coevaluation [Fintype J]
    (q : J → HarmonicArtin.GeneratorPlacement V) (α : V)
    (M : Matrix I J (Q.Zigzag K)) (i : I) (u : TestIndex Q q α) :
    (M * coevaluationMatrix Q q α (K := K)) i u =
      M i u.1 * pathBasis Q (Path.dual Q u.2.val) := by
  classical
  rw [Matrix.mul_apply]
  simp only [coevaluationMatrix, mul_ite, MulZeroClass.mul_zero]
  simp

lemma coevaluation_testMatrix [Fintype I]
    (p : I → HarmonicArtin.GeneratorPlacement V)
    (q : J → HarmonicArtin.GeneratorPlacement V) (α : V)
    {M : Matrix I J (Q.Zigzag K)} (hM : ProjectiveEntries Q p q M)
    (i : I) (u : TestIndex Q q α) :
    (coevaluationMatrix Q p α (K := K) * scalarCornerMatrix Q α (testMatrix Q p q α M)) i u =
      M i u.1 * pathBasis Q (Path.dual Q u.2.val) := by
  classical
  simp only [Matrix.mul_apply, Fintype.sum_sigma, coevaluationMatrix, scalarCornerMatrix,
    testMatrix, ite_mul, MulZeroClass.zero_mul]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true, if_true, mul_smul]
    have hright (p' : CornerPath Q α (p i).color) :
        pathBasis Q (K := K) (Path.dual Q p'.val) * vertexId Q α =
          pathBasis Q (Path.dual Q p'.val) :=
      cornerPath_right Q ((cornerDual Q α (p i).color) p')
    simp only [hright]
    exact dual_right_action Q (M i u.1) (hM.1 i u.1) u.2
  · intro b _ hbi
    apply Finset.sum_eq_zero
    intro c _
    exact ite_eq_right (Ne.symm hbi)
  · simp

namespace BasedComplex

variable [Fintype I]

noncomputable def cotestComplex (E : BasedComplex Q (K := K) I) (α : V) :
    BasedComplex Q (K := K) (TestIndex Q E.placement α) where
  placement := cotestPlacement Q E.placement α
  differential := scalarCornerMatrix Q α (testMatrix Q E.placement E.placement α E.differential)
  entries := scalarCornerMatrix_entries Q α _ _ (fun _ => rfl) (fun _ => rfl) _
  degree := cotestMatrix_degree Q α E.degree
  square_zero := by
    rw [scalarCornerMatrix_mul, testMatrix_mul Q α _ E.entries, E.square_zero,
      testMatrix_zero, scalarCornerMatrix_zero]

noncomputable def coevaluation (E : BasedComplex Q (K := K) I) (α : V) :
    Map Q E (E.cotestComplex Q α) where
  matrix := coevaluationMatrix Q E.placement α
  entries := coevaluation_entries Q _ α
  degree := coevaluation_degree Q _ α
  commute := by
    apply Matrix.ext
    intro i u
    exact (mul_coevaluation Q _ α E.differential i u).trans
      (coevaluation_testMatrix Q _ _ α E.entries i u).symm

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_CoconePlacement
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V] [Fintype I] [Fintype J]
  {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}

namespace Map

def coconePlacement (_f : Map Q E F) : I ⊕ J → GeneratorPlacement V
  | .inl i => E.placement i
  | .inr j => ⟨(F.placement j).color, (F.placement j).cochain + 1,
      (F.placement j).internal⟩

noncomputable def coconeDifferential (f : Map Q E F) :
    Matrix (I ⊕ J) (I ⊕ J) (Q.Zigzag K) :=
  Matrix.fromBlocks E.differential f.matrix 0 (-F.differential)

lemma cocone_entries (f : Map Q E F) :
    ProjectiveEntries Q (f.coconePlacement Q) (f.coconePlacement Q)
      (f.coconeDifferential Q) := by
  constructor
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact E.entries.1 i j
    · exact f.entries.1 i j
    · exact MulZeroClass.mul_zero _
    · exact (projectiveEntries_neg Q F.entries).1 i j
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact E.entries.2 i j
    · exact f.entries.2 i j
    · exact MulZeroClass.zero_mul _
    · exact (projectiveEntries_neg Q F.entries).2 i j

lemma cocone_degree (f : Map Q E F) :
    MapDegree Q (f.coconePlacement Q) (f.coconePlacement Q) 1 0
      (f.coconeDifferential Q) := by
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · exact E.degree i j
  · constructor
    · intro hc
      apply (f.degree i j).1
      intro he
      apply hc
      dsimp only [coconePlacement]
      omega
    · exact (f.degree i j).2
  · exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
  · constructor
    · intro hc
      have hd : (F.placement j).cochain ≠ (F.placement i).cochain + 1 := by
        intro he
        apply hc
        dsimp only [coconePlacement]
        omega
      change -F.differential i j = 0
      rw [(F.degree i j).1 hd, neg_zero]
    · exact homogeneous_neg Q (F.degree i j).2

lemma cocone_square (f : Map Q E F) :
    f.coconeDifferential Q * f.coconeDifferential Q = 0 := by
  unfold coconeDifferential
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.neg_mul, Matrix.mul_neg, E.square_zero, F.square_zero,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, f.commute, add_neg_cancel, neg_zero]
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j <;> rfl

noncomputable def cocone (f : Map Q E F) : BasedComplex Q (K := K) (I ⊕ J) where
  placement := f.coconePlacement Q
  differential := f.coconeDifferential Q
  entries := f.cocone_entries Q
  degree := f.cocone_degree Q
  square_zero := f.cocone_square Q

end Map

variable [Fintype V] [DecidableEq A]

noncomputable def positiveTwist (E : BasedComplex Q (K := K) I) (α : V) :
    BasedComplex Q (K := K) (TestIndex Q E.placement α ⊕ I) :=
  (E.evaluation Q α).cone Q

noncomputable def negativeTwist (E : BasedComplex Q (K := K) I) (α : V) :
    BasedComplex Q (K := K) (I ⊕ TestIndex Q E.placement α) :=
  (E.coevaluation Q α).cocone Q

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_Reindex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V] [Fintype I] [Fintype J]

noncomputable def reindex (E : BasedComplex Q (K := K) I) (e : J ≃ I) :
    BasedComplex Q (K := K) J where
  placement := E.placement ∘ e
  differential := E.differential.submatrix e e
  entries := ⟨fun i j => E.entries.1 (e i) (e j), fun i j => E.entries.2 (e i) (e j)⟩
  degree i j := E.degree (e i) (e j)
  square_zero := by
    rw [Matrix.submatrix_mul_equiv, E.square_zero]
    rfl

variable [DecidableEq I] [DecidableEq J]

noncomputable def reindexForward (E : BasedComplex Q (K := K) I) (e : J ≃ I) :
    Map Q E (E.reindex Q e) where
  matrix := (projectiveIdentity Q E.placement).submatrix id e
  entries := ⟨fun i j => (projectiveEntries_identity Q (K := K) (p := E.placement)).1 i (e j),
    fun i j => (projectiveEntries_identity Q (K := K) (p := E.placement)).2 i (e j)⟩
  degree i j := mapDegree_identity Q (p := E.placement) i (e j)
  commute := by
    change E.differential.submatrix id (Equiv.refl I) *
        (projectiveIdentity Q E.placement).submatrix (Equiv.refl I) e =
      (projectiveIdentity Q E.placement).submatrix id e * E.differential.submatrix e e
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    exact congrArg (fun M : Matrix I I (Q.Zigzag K) => M.submatrix id e)
      ((mul_projectiveIdentity Q E.entries).trans (projectiveIdentity_mul Q E.entries).symm)

noncomputable def reindexBackward (E : BasedComplex Q (K := K) I) (e : J ≃ I) :
    Map Q (E.reindex Q e) E where
  matrix := (projectiveIdentity Q E.placement).submatrix e id
  entries := ⟨fun i j => (projectiveEntries_identity Q (K := K) (p := E.placement)).1 (e i) j,
    fun i j => (projectiveEntries_identity Q (K := K) (p := E.placement)).2 (e i) j⟩
  degree i j := mapDegree_identity Q (p := E.placement) (e i) j
  commute := by
    change E.differential.submatrix e e * (projectiveIdentity Q E.placement).submatrix e id =
      (projectiveIdentity Q E.placement).submatrix e (Equiv.refl I) *
        E.differential.submatrix (Equiv.refl I) id
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    exact congrArg (fun M : Matrix I I (Q.Zigzag K) => M.submatrix e id)
      ((mul_projectiveIdentity Q E.entries).trans (projectiveIdentity_mul Q E.entries).symm)

lemma reindexIdentity (E : BasedComplex Q (K := K) I) (e : J ≃ I) :
    (projectiveIdentity Q (K := K) E.placement).submatrix e e =
      projectiveIdentity Q (E.reindex Q e).placement := by
  apply Matrix.ext
  intro i j
  change (if e i = e j then vertexId Q (E.placement (e i)).color else 0) =
    if i = j then vertexId Q (E.placement (e i)).color else 0
  simp only [e.injective.eq_iff]

noncomputable def reindexHomotopyEquivalence (E : BasedComplex Q (K := K) I) (e : J ≃ I) :
    HomotopyEquivalence Q E (E.reindex Q e) where
  forward := E.reindexForward Q e
  backward := E.reindexBackward Q e
  sourceHomotopy := 0
  targetHomotopy := 0
  sourceEntries := projectiveEntries_zero Q
  targetEntries := projectiveEntries_zero Q
  sourceDegree := mapDegree_zero Q (-1) 0
  targetDegree := mapDegree_zero Q (-1) 0
  sourceEquation := by
    change (projectiveIdentity Q E.placement).submatrix id e *
        (projectiveIdentity Q E.placement).submatrix e id = _
    rw [Matrix.submatrix_mul_equiv]
    simp only [Matrix.submatrix_id_id, Matrix.mul_zero, Matrix.zero_mul, add_zero]
    exact projectiveIdentity_mul Q (projectiveEntries_identity Q (K := K) (p := E.placement))
  targetEquation := by
    change (projectiveIdentity Q E.placement).submatrix e (Equiv.refl I) *
        (projectiveIdentity Q E.placement).submatrix (Equiv.refl I) e = _
    rw [Matrix.submatrix_mul_equiv]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
    exact (congrArg (fun M : Matrix I I (Q.Zigzag K) => M.submatrix e e)
      (projectiveIdentity_mul Q (projectiveEntries_identity Q (K := K) (p := E.placement)))).trans
        (reindexIdentity Q E e)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_SelfCornerEquiv
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I : Type*} (Q : ReversibleQuiver V A)

def selfCornerEquiv (hn : ∀ a, Q.source a ≠ Q.target a) (α : V) :
    Bool ≃ CornerPath Q α α where
  toFun b := if b then ⟨.inr (.inr α), rfl, rfl⟩ else ⟨.inl α, rfl, rfl⟩
  invFun p := match p.val with
    | .inl _ => false
    | .inr (.inl _) => false
    | .inr (.inr _) => true
  left_inv b := by cases b <;> rfl
  right_inv p := by
    rcases p with ⟨v | a | v, hs, ht⟩
    · apply Subtype.ext
      change Sum.inl α = Sum.inl v
      exact congrArg Sum.inl hs.symm
    · exact (hn a (hs.trans ht.symm)).elim
    · apply Subtype.ext
      change Sum.inr (Sum.inr α) = Sum.inr (Sum.inr v)
      exact congrArg (fun x => Sum.inr (Sum.inr x)) hs.symm

@[simp] lemma selfCornerEquiv_false (hn : ∀ a, Q.source a ≠ Q.target a) (α : V) :
    ((selfCornerEquiv Q hn α) false).val = .inl α := rfl
@[simp] lemma selfCornerEquiv_true (hn : ∀ a, Q.source a ≠ Q.target a) (α : V) :
    ((selfCornerEquiv Q hn α) true).val = .inr (.inr α) := rfl

variable [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma diagonal_corner_decomposition (hn : ∀ a, Q.source a ≠ Q.target a)
    (α : V) (x : Q.Zigzag K) (hl : vertexId Q α * x = x)
    (hr : x * vertexId Q α = x) :
    x = x.vertex α • vertexId Q α + x.token α • tokenBasis Q α := by
  calc
    x = ∑ p : CornerPath Q α α, pathCoordinates Q x p.val • pathBasis Q p.val :=
      (sum_cornerPath Q x hl hr).symm
    _ = ∑ b : Bool, pathCoordinates Q x ((selfCornerEquiv Q hn α) b).val •
        pathBasis Q ((selfCornerEquiv Q hn α) b).val :=
      (Equiv.sum_comp (selfCornerEquiv Q hn α) _).symm
    _ = _ := by simpa only [Fintype.sum_bool, selfCornerEquiv_false, selfCornerEquiv_true,
      pathCoordinates_vertex, pathCoordinates_token, pathBasis_vertex, pathBasis_token]
      using add_comm (x.token α • tokenBasis Q α) (x.vertex α • vertexId Q α)

lemma cornerPath_basis_dual_token {α β : V} (u v : CornerPath Q α β) :
    (pathBasis Q (K := K) u.val * pathBasis Q (Path.dual Q v.val)).token α =
      if u = v then 1 else 0 := by
  have hl : vertexId Q α * (pathBasis Q (K := K) u.val *
      pathBasis Q (Path.dual Q v.val)) =
      pathBasis Q u.val * pathBasis Q (Path.dual Q v.val) := by
    rw [← _root_.mul_assoc, cornerPath_left]
  have hc := coordinates_vertexId_left Q α
    (pathBasis Q (K := K) u.val * pathBasis Q (Path.dual Q v.val))
  have ht : trace Q (pathBasis Q (K := K) u.val * pathBasis Q (Path.dual Q v.val)) =
      (pathBasis Q (K := K) u.val * pathBasis Q (Path.dual Q v.val)).token α := by
    unfold trace
    apply Finset.sum_eq_single α
    · intro β _ hb
      have he := hc (.inr (.inr β))
      rw [hl] at he
      simpa [Path.source, hb] using he
    · simp
  rw [← ht, ← coordinates_trace, pathBasis_coordinates]
  simp only [Subtype.ext_iff]

noncomputable def unitContraction (p : I → GeneratorPlacement V) (α : V) :
    Matrix (TestIndex Q p α) (TestIndex Q p α) (Q.Zigzag K) := by
  classical
  exact fun u v => if u.1 = v.1 then
    (pathBasis Q (K := K) u.2.val * pathBasis Q (Path.dual Q v.2.val)).vertex α •
      vertexId Q α else 0

noncomputable def testToken [DecidableEq I] (p : I → GeneratorPlacement V) (α : V) :
    Matrix (TestIndex Q p α) (TestIndex Q p α) (Q.Zigzag K) :=
  Matrix.diagonal (fun _ => tokenBasis Q α)

lemma evaluation_coevaluation [Fintype I] [DecidableEq I]
    (hn : ∀ a, Q.source a ≠ Q.target a) (p : I → GeneratorPlacement V) (α : V) :
    evaluationMatrix Q p α (K := K) * coevaluationMatrix Q p α (K := K) =
      unitContraction Q p α + testToken Q p α := by
  apply Matrix.ext
  intro u v
  rw [evaluation_mul]
  dsimp only [coevaluationMatrix]
  by_cases hi : u.1 = v.1
  · rcases u with ⟨i, u⟩
    rcases v with ⟨j, v⟩
    dsimp only at hi
    subst j
    rw [ite_eq_left rfl]
    have hl : vertexId Q α * (pathBasis Q (K := K) u.val * pathBasis Q (Path.dual Q v.val)) =
        pathBasis Q u.val * pathBasis Q (Path.dual Q v.val) := by
      rw [← _root_.mul_assoc, cornerPath_left]
    have hr : (pathBasis Q (K := K) u.val * pathBasis Q (Path.dual Q v.val)) * vertexId Q α =
        pathBasis Q u.val * pathBasis Q (Path.dual Q v.val) := by
      rw [_root_.mul_assoc]
      exact congrArg (fun z => pathBasis Q (K := K) u.val * z)
        (cornerPath_right Q (K := K) ((cornerDual Q α (p i).color) v))
    rw [diagonal_corner_decomposition Q hn α _ hl hr, cornerPath_basis_dual_token]
    simp only [Matrix.add_apply, unitContraction, testToken, Matrix.diagonal_apply, ite_true, if_true]
    by_cases hp : u = v
    · subst v
      simp
    · simp [hp]
  · have huv : u ≠ v := fun h => hi (congrArg Sigma.fst h)
    simp only [ite_eq_right hi, MulZeroClass.mul_zero, unitContraction, testToken,
      Matrix.add_apply, Matrix.diagonal_apply, ite_eq_right huv, add_zero]

end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_InverseTwistIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I]

noncomputable instance testIndexDecidableEq (p : I → GeneratorPlacement V) (α : V) :
    DecidableEq (TestIndex Q p α) := Classical.decEq _

abbrev InverseTwistIndex (E : BasedComplex Q (K := K) I) (α : V) :=
  TestIndex Q E.placement α ⊕ TestIndex Q E.placement α ⊕
    TestIndex Q E.placement α ⊕ I ⊕ TestIndex Q E.placement α

noncomputable instance inverseTwistIndexDecidableEq
    (E : BasedComplex Q (K := K) I) (α : V) : DecidableEq (InverseTwistIndex Q E α) :=
  Classical.decEq _

noncomputable def inverseTwistIndexEquiv (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :
    InverseTwistIndex Q E α ≃
      (TestIndex Q (E.negativeTwist Q α).placement α ⊕ (I ⊕ TestIndex Q E.placement α)) where
  toFun
    | .inl u => .inl ⟨.inl u.1, u.2⟩
    | .inr (.inl u) => .inl ⟨.inr u, selfCornerEquiv Q hn α false⟩
    | .inr (.inr (.inl u)) => .inl ⟨.inr u, selfCornerEquiv Q hn α true⟩
    | .inr (.inr (.inr (.inl i))) => .inr (.inl i)
    | .inr (.inr (.inr (.inr u))) => .inr (.inr u)
  invFun
    | .inl ⟨.inl i, p⟩ => .inl ⟨i, p⟩
    | .inl ⟨.inr u, p⟩ => if (selfCornerEquiv Q hn α).symm p then
        .inr (.inr (.inl u)) else .inr (.inl u)
    | .inr (.inl i) => .inr (.inr (.inr (.inl i)))
    | .inr (.inr u) => .inr (.inr (.inr (.inr u)))
  left_inv u := by
    rcases u with u | u | u | i | u <;> rfl
  right_inv u := by
    rcases u with ⟨i | u, p⟩ | i | u
    · rfl
    · have he := (selfCornerEquiv Q hn α).apply_symm_apply p
      cases h : (selfCornerEquiv Q hn α).symm p
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        congr 2
        change (selfCornerEquiv Q hn α false : CornerPath Q α α) = p
        simpa only [h] using he
      · simp only [h, ↓reduceIte]
        congr 2
        change (selfCornerEquiv Q hn α true : CornerPath Q α α) = p
        simpa only [h] using he
    · rfl
    · rfl

noncomputable def normalizedInverseTwist (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :
    BasedComplex Q (K := K) (InverseTwistIndex Q E α) :=
  ((E.negativeTwist Q α).positiveTwist Q α).reindex Q (inverseTwistIndexEquiv Q hn E α)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_TestTransform
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_false _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_true
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J L : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

noncomputable def testTransform (p : I → GeneratorPlacement V)
    (q : J → GeneratorPlacement V) (α : V) (M : Matrix I J (Q.Zigzag K)) :
    Matrix (TestIndex Q p α) (TestIndex Q q α) (Q.Zigzag K) :=
  scalarCornerMatrix Q α (testMatrix Q p q α M)

lemma testTransform_mul [Fintype J] {p : I → GeneratorPlacement V}
    {q : J → GeneratorPlacement V} {r : L → GeneratorPlacement V} (α : V)
    {M : Matrix I J (Q.Zigzag K)} (N : Matrix J L (Q.Zigzag K))
    (hM : ProjectiveEntries Q p q M) :
    testTransform Q p q α M * testTransform Q q r α N =
      testTransform Q p r α (M * N) := by
  unfold testTransform
  rw [scalarCornerMatrix_mul, testMatrix_mul Q α N hM]

omit [DecidableEq A] in
lemma testTransform_add (p : I → GeneratorPlacement V)
    (q : J → GeneratorPlacement V) (α : V) (M N : Matrix I J (Q.Zigzag K)) :
    testTransform Q p q α (M + N) = testTransform Q p q α M +
      testTransform Q p q α N := by
  apply Matrix.ext
  intro i j
  simp only [testTransform, scalarCornerMatrix, testMatrix, Matrix.add_apply,
    _root_.mul_add, coordinates_add, add_smul]

lemma testTransform_identity [DecidableEq I] (p : I → GeneratorPlacement V) (α : V) :
    testTransform Q p p α (projectiveIdentity Q p (K := K)) =
      projectiveIdentity Q (testPlacement Q p α) := by
  classical
  apply Matrix.ext
  intro u v
  change pathCoordinates Q (pathBasis Q u.2.val *
    (if u.1 = v.1 then vertexId Q (p u.1).color else 0)) v.2.val • vertexId Q α =
    if u = v then vertexId Q α else 0
  by_cases hi : u.1 = v.1
  · rcases u with ⟨i, u⟩
    rcases v with ⟨j, v⟩
    dsimp only at hi
    subst j
    dsimp only
    simp only [ite_true, if_true, cornerPath_right, pathBasis_coordinates]
    by_cases hp : u = v
    · subst v
      simp
    · have hv : u.val ≠ v.val := fun h => hp (Subtype.ext h)
      simp [hp, hv]
  · simp only [ite_eq_right hi, MulZeroClass.mul_zero, coordinates_zero, zero_smul]
    have huv : u ≠ v := fun h => hi (congrArg Sigma.fst h)
    exact (ite_eq_right huv).symm

lemma evaluation_natural [Fintype I] [Fintype J]
    {p : I → GeneratorPlacement V} {q : J → GeneratorPlacement V} (α : V)
    {M : Matrix I J (Q.Zigzag K)} (hM : ProjectiveEntries Q p q M) :
    testTransform Q p q α M * evaluationMatrix Q q α (K := K) =
      evaluationMatrix Q p α (K := K) * M := by
  apply Matrix.ext
  intro u j
  exact (testMatrix_evaluation Q p q α hM u j).trans (evaluation_mul Q p α M u j).symm

lemma coevaluation_natural [Fintype I] [Fintype J]
    {p : I → GeneratorPlacement V} {q : J → GeneratorPlacement V} (α : V)
    {M : Matrix I J (Q.Zigzag K)} (hM : ProjectiveEntries Q p q M) :
    coevaluationMatrix Q p α (K := K) * testTransform Q p q α M =
      M * coevaluationMatrix Q q α (K := K) := by
  apply Matrix.ext
  intro i u
  exact (coevaluation_testMatrix Q p q α hM i u).trans (mul_coevaluation Q q α M i u).symm

namespace BasedComplex.Map

variable [Fintype I] [Fintype J]
  {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}

noncomputable def test (f : Map Q E F) (α : V) :
    Map Q (E.testComplex Q α) (F.testComplex Q α) where
  matrix := testTransform Q E.placement F.placement α f.matrix
  entries := scalarCornerMatrix_entries Q α _ _ (fun _ => rfl) (fun _ => rfl) _
  degree := testMatrix_degree Q α f.degree
  commute := by
    change testTransform Q _ _ α E.differential * _ =
      _ * testTransform Q _ _ α F.differential
    rw [testTransform_mul Q α _ E.entries, testTransform_mul Q α _ f.entries, f.commute]

noncomputable def cotest (f : Map Q E F) (α : V) :
    Map Q (E.cotestComplex Q α) (F.cotestComplex Q α) where
  matrix := testTransform Q E.placement F.placement α f.matrix
  entries := scalarCornerMatrix_entries Q α _ _ (fun _ => rfl) (fun _ => rfl) _
  degree := cotestMatrix_degree Q α f.degree
  commute := by
    change testTransform Q _ _ α E.differential * _ =
      _ * testTransform Q _ _ α F.differential
    rw [testTransform_mul Q α _ E.entries, testTransform_mul Q α _ f.entries, f.commute]

end BasedComplex.Map
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_InverseTwistDifferential
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

noncomputable def inverseTwistDifferential (E : BasedComplex Q (K := K) I) (α : V) :
    Matrix (InverseTwistIndex Q E α) (InverseTwistIndex Q E α) (Q.Zigzag K) :=
  fun i j => match i, j with
  | .inl u, .inl v => -testTransform Q E.placement E.placement α E.differential u v
  | .inl u, .inr (.inl v) => -unitContraction Q E.placement α u v
  | .inl u, .inr (.inr (.inl v)) => -projectiveIdentity Q (testPlacement Q E.placement α) u v
  | .inl u, .inr (.inr (.inr (.inl j))) => evaluationMatrix Q E.placement α u j
  | .inr (.inl u), .inr (.inl v) => testTransform Q E.placement E.placement α E.differential u v
  | .inr (.inl u), .inr (.inr (.inr (.inr v))) =>
      projectiveIdentity Q (testPlacement Q E.placement α) u v
  | .inr (.inr (.inl u)), .inr (.inr (.inl v)) =>
      testTransform Q E.placement E.placement α E.differential u v
  | .inr (.inr (.inl u)), .inr (.inr (.inr (.inr v))) => testToken Q E.placement α u v
  | .inr (.inr (.inr (.inl i))), .inr (.inr (.inr (.inl j))) => E.differential i j
  | .inr (.inr (.inr (.inl i))), .inr (.inr (.inr (.inr v))) => coevaluationMatrix Q E.placement α i v
  | .inr (.inr (.inr (.inr u))), .inr (.inr (.inr (.inr v))) =>
      -testTransform Q E.placement E.placement α E.differential u v
  | _, _ => 0

omit [DecidableEq I] in
lemma positiveTwist_differential (E : BasedComplex Q (K := K) I) (α : V) :
    (E.positiveTwist Q α).differential =
      Matrix.fromBlocks (-testTransform Q E.placement E.placement α E.differential)
        (evaluationMatrix Q E.placement α) 0 E.differential := rfl

omit [DecidableEq I] in
lemma negativeTwist_differential (E : BasedComplex Q (K := K) I) (α : V) :
    (E.negativeTwist Q α).differential =
      Matrix.fromBlocks E.differential (coevaluationMatrix Q E.placement α)
        0 (-testTransform Q E.placement E.placement α E.differential) := rfl

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_OrthogonalVertices
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A : Type*} (Q : ReversibleQuiver V A)

def OrthogonalVertices (α β : V) : Prop :=
  α ≠ β ∧ ∀ a, Q.source a = α → Q.target a ≠ β

lemma no_corner_of_orthogonal {α β : V} (h : OrthogonalVertices Q α β)
    (p : CornerPath Q α β) : False := by
  rcases p with ⟨v | a | v, hs, ht⟩
  · exact h.1 (hs.symm.trans ht)
  · exact h.2 a hs ht
  · exact h.1 (hs.symm.trans ht)

namespace BasedComplex

variable {K I J : Type*} [Field K] [Fintype V] [Fintype A]
  [DecidableEq V] [DecidableEq A] [Fintype I] [Fintype J]

omit [Fintype V] [DecidableEq A] in
@[ext] lemma ext_placement_differential
    {E F : BasedComplex Q (K := K) I} (hp : E.placement = F.placement)
    (hd : E.differential = F.differential) : E = F := by
  cases E
  cases F
  cases hp
  cases hd
  rfl

variable [DecidableEq I] [DecidableEq J]

noncomputable def HomotopyEquivalence.symm
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    (h : HomotopyEquivalence Q E F) : HomotopyEquivalence Q F E where
  forward := h.backward
  backward := h.forward
  sourceHomotopy := h.targetHomotopy
  targetHomotopy := h.sourceHomotopy
  sourceEntries := h.targetEntries
  targetEntries := h.sourceEntries
  sourceDegree := h.targetDegree
  targetDegree := h.sourceDegree
  sourceEquation := h.targetEquation
  targetEquation := h.sourceEquation

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_InverseTwistPlacement
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

def inverseTwistPlacement (E : BasedComplex Q (K := K) I) (α : V) :
    InverseTwistIndex Q E α → GeneratorPlacement V
  | .inl u => ⟨α, (E.placement u.1).cochain - 1,
      (E.placement u.1).internal + Path.length u.2.val⟩
  | .inr (.inl u) => ⟨α, (E.placement u.1).cochain,
      (E.placement u.1).internal + Path.length u.2.val - 2⟩
  | .inr (.inr (.inl u)) => testPlacement Q E.placement α u
  | .inr (.inr (.inr (.inl i))) => E.placement i
  | .inr (.inr (.inr (.inr u))) => ⟨α, (E.placement u.1).cochain + 1,
      (E.placement u.1).internal + Path.length u.2.val - 2⟩

omit [DecidableEq I] in
lemma normalizedInverseTwist_placement (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :
    (normalizedInverseTwist Q hn E α).placement = inverseTwistPlacement Q E α := by
  funext i
  rcases i with u | u | u | i | u
  · rfl
  · change (⟨α, (E.placement u.1).cochain + 1 - 1,
      (E.placement u.1).internal + Path.length u.2.val - 2 + 0⟩ : GeneratorPlacement V) = _
    simp only [add_sub_cancel_right, add_zero]
    rfl
  · change (⟨α, (E.placement u.1).cochain + 1 - 1,
      (E.placement u.1).internal + Path.length u.2.val - 2 + 2⟩ : GeneratorPlacement V) = _
    simp only [add_sub_cancel_right, sub_add_cancel]
    rfl
  · rfl
  · rfl

noncomputable def inverseTwistProjection (E : BasedComplex Q (K := K) I) (α : V) :
    Matrix (InverseTwistIndex Q E α) I (Q.Zigzag K)
  | .inr (.inr (.inl u)), j => evaluationMatrix Q E.placement α u j
  | .inr (.inr (.inr (.inl i))), j => projectiveIdentity Q E.placement i j
  | _, _ => 0

noncomputable def inverseTwistInjection (E : BasedComplex Q (K := K) I) (α : V) :
    Matrix I (InverseTwistIndex Q E α) (Q.Zigzag K)
  | i, .inr (.inl u) => -coevaluationMatrix Q E.placement α i u
  | i, .inr (.inr (.inr (.inl j))) => projectiveIdentity Q E.placement i j
  | _, _ => 0

noncomputable def inverseTwistHomotopy (E : BasedComplex Q (K := K) I) (α : V) :
    Matrix (InverseTwistIndex Q E α) (InverseTwistIndex Q E α) (Q.Zigzag K)
  | .inr (.inr (.inl u)), .inl v => projectiveIdentity Q (testPlacement Q E.placement α) u v
  | .inr (.inr (.inr (.inr u))), .inr (.inl v) =>
      -projectiveIdentity Q (testPlacement Q E.placement α) u v
  | _, _ => 0

lemma inverseTwistProjection_entries (E : BasedComplex Q (K := K) I) (α : V) :
    ProjectiveEntries Q (inverseTwistPlacement Q E α) E.placement
      (inverseTwistProjection Q E α) := by
  constructor
  · intro i j
    rcases i with u | u | u | i | u
    · exact MulZeroClass.mul_zero _
    · exact MulZeroClass.mul_zero _
    · exact (evaluation_entries Q E.placement α).1 u j
    · exact (projectiveEntries_identity Q).1 i j
    · exact MulZeroClass.mul_zero _
  · intro i j
    rcases i with u | u | u | i | u
    · exact MulZeroClass.zero_mul _
    · exact MulZeroClass.zero_mul _
    · exact (evaluation_entries Q E.placement α).2 u j
    · exact (projectiveEntries_identity Q).2 i j
    · exact MulZeroClass.zero_mul _

lemma inverseTwistProjection_degree (E : BasedComplex Q (K := K) I) (α : V) :
    MapDegree Q (inverseTwistPlacement Q E α) E.placement 0 0
      (inverseTwistProjection Q E α) := by
  intro i j
  rcases i with u | u | u | i | u
  · exact ⟨fun _ => by trivial, homogeneous_zero Q _⟩
  · exact ⟨fun _ => by trivial, homogeneous_zero Q _⟩
  · exact evaluation_degree Q E.placement α u j
  · exact mapDegree_identity Q i j
  · exact ⟨fun _ => by trivial, homogeneous_zero Q _⟩

lemma inverseTwistInjection_entries (E : BasedComplex Q (K := K) I) (α : V) :
    ProjectiveEntries Q E.placement (inverseTwistPlacement Q E α)
      (inverseTwistInjection Q E α) := by
  constructor
  · intro i j
    rcases j with u | u | u | j | u
    · exact MulZeroClass.mul_zero _
    · exact (projectiveEntries_neg Q (coevaluation_entries Q E.placement α)).1 i u
    · exact MulZeroClass.mul_zero _
    · exact (projectiveEntries_identity Q).1 i j
    · exact MulZeroClass.mul_zero _
  · intro i j
    rcases j with u | u | u | j | u
    · exact MulZeroClass.zero_mul _
    · exact (projectiveEntries_neg Q (coevaluation_entries Q E.placement α)).2 i u
    · exact MulZeroClass.zero_mul _
    · exact (projectiveEntries_identity Q).2 i j
    · exact MulZeroClass.zero_mul _

lemma inverseTwistInjection_degree (E : BasedComplex Q (K := K) I) (α : V) :
    MapDegree Q E.placement (inverseTwistPlacement Q E α) 0 0
      (inverseTwistInjection Q E α) := by
  intro i j
  rcases j with u | u | u | j | u
  · exact ⟨fun _ => by trivial, homogeneous_zero Q _⟩
  · exact mapDegree_neg Q (coevaluation_degree Q E.placement α) i u
  · exact ⟨fun _ => by trivial, homogeneous_zero Q _⟩
  · exact mapDegree_identity Q i j
  · exact ⟨fun _ => by trivial, homogeneous_zero Q _⟩

omit [Fintype V] in
omit [DecidableEq A] [DecidableEq I] in
lemma inverseTwistHomotopy_entries (E : BasedComplex Q (K := K) I) (α : V) :
    ProjectiveEntries Q (inverseTwistPlacement Q E α) (inverseTwistPlacement Q E α)
      (inverseTwistHomotopy Q E α) := by
  constructor
  · intro i j
    rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v
    all_goals first
      | exact MulZeroClass.mul_zero _
      | exact (projectiveEntries_identity Q (K := K)
          (p := testPlacement Q E.placement α)).1 u v
      | exact (projectiveEntries_neg Q (projectiveEntries_identity Q (K := K)
          (p := testPlacement Q E.placement α))).1 u v
  · intro i j
    rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v
    all_goals first
      | exact MulZeroClass.zero_mul _
      | exact (projectiveEntries_identity Q (K := K)
          (p := testPlacement Q E.placement α)).2 u v
      | exact (projectiveEntries_neg Q (projectiveEntries_identity Q (K := K)
          (p := testPlacement Q E.placement α))).2 u v

omit [Fintype V] in
omit [DecidableEq A] [DecidableEq I] in
lemma inverseTwistHomotopy_degree (E : BasedComplex Q (K := K) I) (α : V) :
    MapDegree Q (inverseTwistPlacement Q E α) (inverseTwistPlacement Q E α) (-1) 0
      (inverseTwistHomotopy Q E α) := by
  intro i j
  rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v
  all_goals try exact ⟨fun _ => by trivial, homogeneous_zero Q _⟩
  · by_cases h : u = v
    · subst v
      simp only [inverseTwistHomotopy, projectiveIdentity, Matrix.diagonal_apply, ite_true, if_true]
      constructor
      · intro hc
        apply (hc _).elim
        dsimp only [inverseTwistPlacement, testPlacement]
        omega
      · convert homogeneous_vertexId Q (K := K) α using 1 <;>
          simp [inverseTwistPlacement, testPlacement]
    · simp only [inverseTwistHomotopy, projectiveIdentity, Matrix.diagonal_apply, ite_eq_right h]
      exact ⟨fun _ => by trivial, homogeneous_zero Q _⟩
  · by_cases h : u = v
    · subst v
      simp only [inverseTwistHomotopy, projectiveIdentity, Matrix.diagonal_apply, ite_true, if_true]
      constructor
      · intro hc
        apply (hc _).elim
        dsimp only [inverseTwistPlacement, testPlacement]
        omega
      · convert homogeneous_neg Q (homogeneous_vertexId Q (K := K) α) using 1 <;>
          simp [inverseTwistPlacement, testPlacement]
    · simp only [inverseTwistHomotopy, projectiveIdentity, Matrix.diagonal_apply, ite_eq_right h,
        neg_zero]
      exact ⟨fun _ => by trivial, homogeneous_zero Q _⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_InverseTwistIdentity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

lemma inverseTwistProjection_commute (E : BasedComplex Q (K := K) I) (α : V) :
    inverseTwistDifferential Q E α * inverseTwistProjection Q E α =
      inverseTwistProjection Q E α * E.differential := by
  apply Matrix.ext
  intro i j
  rcases i with u | u | u | i | u
  all_goals simp only [Matrix.mul_apply, Fintype.sum_sum_type, inverseTwistDifferential,
    inverseTwistProjection, MulZeroClass.zero_mul, MulZeroClass.mul_zero,
    Finset.sum_const_zero, _root_.neg_mul, Finset.sum_neg_distrib, add_zero, zero_add]
  · exact (congrArg₂ (fun a b : Q.Zigzag K => -a + b)
      (congrFun (congrFun (projectiveIdentity_mul Q
        (evaluation_entries Q E.placement α)) u) j)
      (congrFun (congrFun (mul_projectiveIdentity Q
        (evaluation_entries Q E.placement α)) u) j)).trans (neg_add_cancel _)
  · exact congrFun (congrFun (evaluation_natural Q α E.entries) u) j
  · exact congrFun (congrFun ((mul_projectiveIdentity Q E.entries).trans
      (projectiveIdentity_mul Q E.entries).symm) i) j

lemma inverseTwistInjection_commute (E : BasedComplex Q (K := K) I) (α : V) :
    E.differential * inverseTwistInjection Q E α =
      inverseTwistInjection Q E α * inverseTwistDifferential Q E α := by
  apply Matrix.ext
  intro i j
  rcases j with u | u | u | j | u
  all_goals simp only [Matrix.mul_apply, Fintype.sum_sum_type, inverseTwistDifferential,
    inverseTwistInjection, MulZeroClass.zero_mul, MulZeroClass.mul_zero,
    Finset.sum_const_zero, _root_.neg_mul, _root_.mul_neg, Finset.sum_neg_distrib,
    add_zero, zero_add, neg_zero]
  · exact congrArg Neg.neg (congrFun (congrFun (coevaluation_natural Q α E.entries).symm i) u)
  · exact congrFun (congrFun ((mul_projectiveIdentity Q E.entries).trans
      (projectiveIdentity_mul Q E.entries).symm) i) j
  · exact ((congrArg₂ (fun a b : Q.Zigzag K => -a + b)
      (congrFun (congrFun (mul_projectiveIdentity Q
        (coevaluation_entries Q E.placement α)) i) u)
      (congrFun (congrFun (projectiveIdentity_mul Q
        (coevaluation_entries Q E.placement α)) i) u)).trans (neg_add_cancel _)).symm

omit [DecidableEq A] in
lemma inverseTwist_targetEquation (E : BasedComplex Q (K := K) I) (α : V) :
    inverseTwistInjection Q E α * inverseTwistProjection Q E α =
      projectiveIdentity Q (K := K) E.placement := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, inverseTwistInjection,
    inverseTwistProjection, MulZeroClass.zero_mul, MulZeroClass.mul_zero,
    Finset.sum_const_zero, add_zero, zero_add]
  exact congrFun (congrFun (projectiveIdentity_mul Q
    (projectiveEntries_identity Q (K := K) (p := E.placement))) i) j

noncomputable def inverseTwistIdentity (E : BasedComplex Q (K := K) I) (α : V) :
    Matrix (InverseTwistIndex Q E α) (InverseTwistIndex Q E α) (Q.Zigzag K)
  | .inl u, .inl v => projectiveIdentity Q (testPlacement Q E.placement α) u v
  | .inr (.inl u), .inr (.inl v) => projectiveIdentity Q (testPlacement Q E.placement α) u v
  | .inr (.inr (.inl u)), .inr (.inr (.inl v)) =>
      projectiveIdentity Q (testPlacement Q E.placement α) u v
  | .inr (.inr (.inr (.inl i))), .inr (.inr (.inr (.inl j))) =>
      projectiveIdentity Q E.placement i j
  | .inr (.inr (.inr (.inr u))), .inr (.inr (.inr (.inr v))) =>
      projectiveIdentity Q (testPlacement Q E.placement α) u v
  | _, _ => 0

omit [Fintype V] [DecidableEq A] in
lemma inverseTwistIdentity_eq (E : BasedComplex Q (K := K) I) (α : V) :
    projectiveIdentity Q (K := K) (inverseTwistPlacement Q E α) =
      inverseTwistIdentity Q E α := by
  apply Matrix.ext
  intro i j
  rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v
  all_goals simp [projectiveIdentity, Matrix.diagonal_apply,
    inverseTwistIdentity, inverseTwistPlacement, testPlacement]

omit [DecidableEq A] in
lemma unitContraction_entries (E : BasedComplex Q (K := K) I) (α : V) :
    ProjectiveEntries Q (testPlacement Q E.placement α) (testPlacement Q E.placement α)
      (unitContraction Q E.placement α (K := K)) := by
  constructor
  · intro u v
    dsimp only [unitContraction, testPlacement]
    split_ifs <;> simp only [mul_smul, vertexId_mul_self, MulZeroClass.mul_zero]
  · intro u v
    dsimp only [unitContraction, testPlacement]
    split_ifs <;> simp only [smul_mul, vertexId_mul_self, MulZeroClass.zero_mul]

lemma testToken_entries (E : BasedComplex Q (K := K) I) (α : V) :
    ProjectiveEntries Q (testPlacement Q E.placement α) (testPlacement Q E.placement α)
      (testToken Q E.placement α (K := K)) := by
  have hl : vertexId Q (K := K) α * tokenBasis Q α = tokenBasis Q α := by
    simpa only [Path.source, pathBasis_token] using
      (pathBasis_left Q (K := K) (.inr (.inr α)))
  have hr : tokenBasis Q (K := K) α * vertexId Q α = tokenBasis Q α := by
    simpa only [Path.target, pathBasis_token] using
      (pathBasis_right Q (K := K) (.inr (.inr α)))
  constructor
  · intro u v
    dsimp only [testToken, Matrix.diagonal_apply, testPlacement]
    split_ifs <;> simp only [hl, MulZeroClass.mul_zero]
  · intro u v
    dsimp only [testToken, Matrix.diagonal_apply, testPlacement]
    split_ifs <;> simp only [hr, MulZeroClass.zero_mul]

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_NormalizedInverseTwistHomotopy
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ReverseTwistIndexEquiv
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I]

noncomputable def reverseTwistIndexEquiv (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :
    InverseTwistIndex Q E α ≃
      ((TestIndex Q E.placement α ⊕ I) ⊕ TestIndex Q (E.positiveTwist Q α).placement α) where
  toFun
    | .inl u => .inl (.inl u)
    | .inr (.inl u) => .inr ⟨.inl u, selfCornerEquiv Q hn α false⟩
    | .inr (.inr (.inl u)) => .inr ⟨.inl u, selfCornerEquiv Q hn α true⟩
    | .inr (.inr (.inr (.inl i))) => .inl (.inr i)
    | .inr (.inr (.inr (.inr u))) => .inr ⟨.inr u.1, u.2⟩
  invFun
    | .inl (.inl u) => .inl u
    | .inl (.inr i) => .inr (.inr (.inr (.inl i)))
    | .inr ⟨.inl u, p⟩ => if (selfCornerEquiv Q hn α).symm p then
        .inr (.inr (.inl u)) else .inr (.inl u)
    | .inr ⟨.inr i, p⟩ => .inr (.inr (.inr (.inr ⟨i, p⟩)))
  left_inv u := by
    rcases u with u | u | u | i | u <;> rfl
  right_inv u := by
    rcases u with (u | i) | ⟨u | i, p⟩
    · rfl
    · rfl
    · have he := (selfCornerEquiv Q hn α).apply_symm_apply p
      cases h : (selfCornerEquiv Q hn α).symm p
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        congr 2
        change (selfCornerEquiv Q hn α false : CornerPath Q α α) = p
        simpa only [h] using he
      · simp only [h, ↓reduceIte]
        congr 2
        change (selfCornerEquiv Q hn α true : CornerPath Q α α) = p
        simpa only [h] using he
    · rfl

noncomputable def normalizedReverseTwist (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :
    BasedComplex Q (K := K) (InverseTwistIndex Q E α) :=
  ((E.positiveTwist Q α).negativeTwist Q α).reindex Q (reverseTwistIndexEquiv Q hn E α)

lemma normalizedReverseTwist_placement (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :
    (normalizedReverseTwist Q hn E α).placement = inverseTwistPlacement Q E α := by
  funext i
  rcases i with u | u | u | i | u
  · rfl
  · change (⟨α, (E.placement u.1).cochain - 1 + 1,
      (E.placement u.1).internal + Path.length u.2.val + 0 - 2⟩ : GeneratorPlacement V) = _
    simp only [sub_add_cancel, add_zero]
    rfl
  · change (⟨α, (E.placement u.1).cochain - 1 + 1,
      (E.placement u.1).internal + Path.length u.2.val + 2 - 2⟩ : GeneratorPlacement V) = _
    simp only [sub_add_cancel, add_sub_cancel_right]
    rfl
  · rfl
  · rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ReverseTwistDifferential
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

noncomputable def reverseTwistDifferential (E : BasedComplex Q (K := K) I) (α : V) :
    Matrix (InverseTwistIndex Q E α) (InverseTwistIndex Q E α) (Q.Zigzag K)
  | .inl u, .inl v => -testTransform Q E.placement E.placement α E.differential u v
  | .inl u, .inr (.inl v) => testToken Q E.placement α u v
  | .inl u, .inr (.inr (.inl v)) => projectiveIdentity Q (testPlacement Q E.placement α) u v
  | .inl u, .inr (.inr (.inr (.inl j))) => evaluationMatrix Q E.placement α u j
  | .inr (.inl u), .inr (.inl v) => testTransform Q E.placement E.placement α E.differential u v
  | .inr (.inl u), .inr (.inr (.inr (.inr v))) =>
      -projectiveIdentity Q (testPlacement Q E.placement α) u v
  | .inr (.inr (.inl u)), .inr (.inr (.inl v)) =>
      testTransform Q E.placement E.placement α E.differential u v
  | .inr (.inr (.inl u)), .inr (.inr (.inr (.inr v))) => -unitContraction Q E.placement α u v
  | .inr (.inr (.inr (.inl i))), .inr (.inr (.inr (.inl j))) => E.differential i j
  | .inr (.inr (.inr (.inl i))), .inr (.inr (.inr (.inr v))) => coevaluationMatrix Q E.placement α i v
  | .inr (.inr (.inr (.inr u))), .inr (.inr (.inr (.inr v))) =>
      -testTransform Q E.placement E.placement α E.differential u v
  | _, _ => 0

lemma coordinates_tokenBasis_mul (α : V) (x : Q.Zigzag K) (p : Path V A) :
    pathCoordinates Q (tokenBasis Q α * x) p =
      (x * pathBasis Q (Path.dual Q p)).vertex α := by
  rw [coordinates_trace, _root_.mul_assoc, trace_mul_comm, trace_mul_tokenBasis]

lemma normalizedReverseTwist_differential (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :
    (normalizedReverseTwist Q hn E α).differential = reverseTwistDifferential Q E α := by
  change ((E.positiveTwist Q α).negativeTwist Q α).differential.submatrix
    (reverseTwistIndexEquiv Q hn E α) (reverseTwistIndexEquiv Q hn E α) = _
  rw [negativeTwist_differential]
  apply Matrix.ext
  intro i j
  rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v
  all_goals simp only [Matrix.submatrix_apply, reverseTwistIndexEquiv, Equiv.coe_fn_mk,
    Matrix.of_apply, reverseTwistDifferential, Matrix.fromBlocks, testTransform,
    scalarCornerMatrix, testMatrix]
  all_goals simp only [positiveTwist_differential, Matrix.fromBlocks, Matrix.neg_apply,
    Matrix.zero_apply, Matrix.of_apply, testTransform, scalarCornerMatrix, testMatrix,
    Sum.elim_inl, Sum.elim_inr, MulZeroClass.mul_zero, coordinates_zero, zero_smul,
    neg_zero, selfCornerEquiv_false, selfCornerEquiv_true]
  all_goals try simp only [coevaluationMatrix, Sum.inl.injEq, Sum.inr.injEq,
    Sum.inl_ne_inr, Sum.inr_ne_inl, ↓reduceIte, selfCornerEquiv_false,
    selfCornerEquiv_true, Path.dual, pathBasis_vertex, pathBasis_token, projectiveIdentity,
    Matrix.diagonal_apply, testPlacement, testToken]
  all_goals try simp only [_root_.mul_neg, mul_smul, map_neg, Pi.neg_apply,
    coordinates_smul, neg_smul, neg_neg]
  all_goals try simp only [vertexId_mul_self]
  all_goals try (refine @ite_cond_congr _ _ _ ?_ ?_ _ _ rfl)
  all_goals try (
    have ht : tokenBasis Q (K := K) α * vertexId Q α = tokenBasis Q α := by
      simpa only [Path.target, pathBasis_token] using
        (pathBasis_right Q (K := K) (.inr (.inr α)))
    simp only [ht, pathCoordinates_vertex, pathCoordinates_token]
    simp only [vertexId, tokenBasis, vertex, token, Pi.single_apply, ite_true, if_true, Pi.zero_apply]
    first
      | exact congrArg (fun k : K => k • vertexId Q (K := K) α)
          (_root_.mul_one (pathCoordinates Q (pathBasis Q (K := K) u.2.val *
            E.differential u.1 v.1) v.2.val))
      | exact (congrArg (fun k : K => k • vertexId Q (K := K) α)
          (MulZeroClass.mul_zero (pathCoordinates Q (pathBasis Q (K := K) u.2.val *
            E.differential u.1 v.1) v.2.val))).trans (zero_smul K _))
  · apply congrArg Neg.neg
    by_cases hi : u.1 = v.1
    · rcases u with ⟨i, u⟩
      rcases v with ⟨j, v⟩
      dsimp only at hi
      subst j
      simp only [evaluationMatrix, ite_true, if_true, cornerPath_left, pathBasis_coordinates]
      by_cases hp : u = v
      · subst v
        simp
      · have hp' : u.val ≠ v.val := fun h => hp (Subtype.ext h)
        simp [hp, hp']
    · have huv : u ≠ v := fun h => hi (congrArg Sigma.fst h)
      simp only [evaluationMatrix, ite_eq_right hi, MulZeroClass.mul_zero,
        coordinates_zero, zero_smul, ite_eq_right huv]
  · apply congrArg Neg.neg
    by_cases hi : u.1 = v.1
    · simp only [evaluationMatrix, ite_eq_left hi, coordinates_tokenBasis_mul,
        unitContraction]
    · simp only [evaluationMatrix, ite_eq_right hi, MulZeroClass.mul_zero,
        coordinates_zero, zero_smul, unitContraction]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ReverseTwistProjection
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

noncomputable def reverseTwistProjection (E : BasedComplex Q (K := K) I) (α : V) :
    Matrix (InverseTwistIndex Q E α) I (Q.Zigzag K)
  | .inr (.inr (.inl u)), j => -evaluationMatrix Q E.placement α u j
  | .inr (.inr (.inr (.inl i))), j => projectiveIdentity Q E.placement i j
  | _, _ => 0

noncomputable def reverseTwistInjection (E : BasedComplex Q (K := K) I) (α : V) :
    Matrix I (InverseTwistIndex Q E α) (Q.Zigzag K)
  | i, .inr (.inl u) => coevaluationMatrix Q E.placement α i u
  | i, .inr (.inr (.inr (.inl j))) => projectiveIdentity Q E.placement i j
  | _, _ => 0

noncomputable def reverseTwistHomotopy (E : BasedComplex Q (K := K) I) (α : V) :
    Matrix (InverseTwistIndex Q E α) (InverseTwistIndex Q E α) (Q.Zigzag K) :=
  -inverseTwistHomotopy Q E α

lemma reverseTwistProjection_entries (E : BasedComplex Q (K := K) I) (α : V) :
    ProjectiveEntries Q (inverseTwistPlacement Q E α) E.placement
      (reverseTwistProjection Q E α) := by
  constructor
  · intro i j
    rcases i with u | u | u | i | u
    · exact MulZeroClass.mul_zero _
    · exact MulZeroClass.mul_zero _
    · exact (projectiveEntries_neg Q (evaluation_entries Q E.placement α)).1 u j
    · exact (projectiveEntries_identity Q).1 i j
    · exact MulZeroClass.mul_zero _
  · intro i j
    rcases i with u | u | u | i | u
    · exact MulZeroClass.zero_mul _
    · exact MulZeroClass.zero_mul _
    · exact (projectiveEntries_neg Q (evaluation_entries Q E.placement α)).2 u j
    · exact (projectiveEntries_identity Q).2 i j
    · exact MulZeroClass.zero_mul _

lemma reverseTwistProjection_degree (E : BasedComplex Q (K := K) I) (α : V) :
    MapDegree Q (inverseTwistPlacement Q E α) E.placement 0 0
      (reverseTwistProjection Q E α) := by
  intro i j
  rcases i with u | u | u | i | u
  · exact ⟨fun _ => by trivial, homogeneous_zero Q _⟩
  · exact ⟨fun _ => by trivial, homogeneous_zero Q _⟩
  · exact mapDegree_neg Q (evaluation_degree Q E.placement α) u j
  · exact mapDegree_identity Q i j
  · exact ⟨fun _ => by trivial, homogeneous_zero Q _⟩

lemma reverseTwistInjection_entries (E : BasedComplex Q (K := K) I) (α : V) :
    ProjectiveEntries Q E.placement (inverseTwistPlacement Q E α)
      (reverseTwistInjection Q E α) := by
  constructor
  · intro i j
    rcases j with u | u | u | j | u
    · exact MulZeroClass.mul_zero _
    · exact (coevaluation_entries Q E.placement α).1 i u
    · exact MulZeroClass.mul_zero _
    · exact (projectiveEntries_identity Q).1 i j
    · exact MulZeroClass.mul_zero _
  · intro i j
    rcases j with u | u | u | j | u
    · exact MulZeroClass.zero_mul _
    · exact (coevaluation_entries Q E.placement α).2 i u
    · exact MulZeroClass.zero_mul _
    · exact (projectiveEntries_identity Q).2 i j
    · exact MulZeroClass.zero_mul _

lemma reverseTwistInjection_degree (E : BasedComplex Q (K := K) I) (α : V) :
    MapDegree Q E.placement (inverseTwistPlacement Q E α) 0 0
      (reverseTwistInjection Q E α) := by
  intro i j
  rcases j with u | u | u | j | u
  · exact ⟨fun _ => by trivial, homogeneous_zero Q _⟩
  · exact coevaluation_degree Q E.placement α i u
  · exact ⟨fun _ => by trivial, homogeneous_zero Q _⟩
  · exact mapDegree_identity Q i j
  · exact ⟨fun _ => by trivial, homogeneous_zero Q _⟩

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma reverseTwistHomotopy_entries (E : BasedComplex Q (K := K) I) (α : V) :
    ProjectiveEntries Q (inverseTwistPlacement Q E α) (inverseTwistPlacement Q E α)
      (reverseTwistHomotopy Q E α) :=
  projectiveEntries_neg Q (inverseTwistHomotopy_entries Q E α)

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma reverseTwistHomotopy_degree (E : BasedComplex Q (K := K) I) (α : V) :
    MapDegree Q (inverseTwistPlacement Q E α) (inverseTwistPlacement Q E α) (-1) 0
      (reverseTwistHomotopy Q E α) :=
  mapDegree_neg Q (inverseTwistHomotopy_degree Q E α)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ReverseTwistProjectionCommute
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

lemma reverseTwistProjection_commute (E : BasedComplex Q (K := K) I) (α : V) :
    reverseTwistDifferential Q E α * reverseTwistProjection Q E α =
      reverseTwistProjection Q E α * E.differential := by
  apply Matrix.ext
  intro i j
  rcases i with u | u | u | i | u
  all_goals simp only [Matrix.mul_apply, Fintype.sum_sum_type, reverseTwistDifferential,
    reverseTwistProjection, MulZeroClass.zero_mul, MulZeroClass.mul_zero,
    Finset.sum_const_zero, _root_.neg_mul, _root_.mul_neg, Finset.sum_neg_distrib, add_zero, zero_add, neg_zero]
  · exact (congrArg₂ (fun a b : Q.Zigzag K => -a + b)
      (congrFun (congrFun (projectiveIdentity_mul Q
        (evaluation_entries Q E.placement α)) u) j)
      (congrFun (congrFun (mul_projectiveIdentity Q
        (evaluation_entries Q E.placement α)) u) j)).trans (neg_add_cancel _)
  · exact congrArg Neg.neg (congrFun (congrFun (evaluation_natural Q α E.entries) u) j)
  · exact congrFun (congrFun ((mul_projectiveIdentity Q E.entries).trans
      (projectiveIdentity_mul Q E.entries).symm) i) j

lemma reverseTwistInjection_commute (E : BasedComplex Q (K := K) I) (α : V) :
    E.differential * reverseTwistInjection Q E α =
      reverseTwistInjection Q E α * reverseTwistDifferential Q E α := by
  apply Matrix.ext
  intro i j
  rcases j with u | u | u | j | u
  all_goals simp only [Matrix.mul_apply, Fintype.sum_sum_type, reverseTwistDifferential,
    reverseTwistInjection, MulZeroClass.zero_mul, MulZeroClass.mul_zero,
    Finset.sum_const_zero, _root_.mul_neg, Finset.sum_neg_distrib,
    add_zero, zero_add, neg_zero]
  · exact congrFun (congrFun (coevaluation_natural Q α E.entries).symm i) u
  · exact congrFun (congrFun ((mul_projectiveIdentity Q E.entries).trans
      (projectiveIdentity_mul Q E.entries).symm) i) j
  · exact ((congrArg₂ (fun a b : Q.Zigzag K => -a + b)
      (congrFun (congrFun (mul_projectiveIdentity Q
        (coevaluation_entries Q E.placement α)) i) u)
      (congrFun (congrFun (projectiveIdentity_mul Q
        (coevaluation_entries Q E.placement α)) i) u)).trans (neg_add_cancel _)).symm

omit [DecidableEq A] in
lemma reverseTwist_targetEquation (E : BasedComplex Q (K := K) I) (α : V) :
    reverseTwistInjection Q E α * reverseTwistProjection Q E α =
      projectiveIdentity Q (K := K) E.placement := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, reverseTwistInjection,
    reverseTwistProjection, MulZeroClass.zero_mul, MulZeroClass.mul_zero,
    Finset.sum_const_zero, add_zero, zero_add]
  exact congrFun (congrFun (projectiveIdentity_mul Q
    (projectiveEntries_identity Q (K := K) (p := E.placement))) i) j

lemma reverseTwist_sourceEquation (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :
    reverseTwistProjection Q E α * reverseTwistInjection Q E α =
      projectiveIdentity Q (inverseTwistPlacement Q E α) +
      (reverseTwistDifferential Q E α * reverseTwistHomotopy Q E α +
       reverseTwistHomotopy Q E α * reverseTwistDifferential Q E α) := by
  rw [inverseTwistIdentity_eq]
  let t := testTransform Q E.placement E.placement α E.differential
  let r := unitContraction Q E.placement α (K := K)
  let θ := testToken Q E.placement α (K := K)
  let ι := projectiveIdentity Q (K := K) (testPlacement Q E.placement α)
  let e := evaluationMatrix Q E.placement α (K := K)
  let η := projectiveIdentity Q (K := K) E.placement
  let c := coevaluationMatrix Q E.placement α (K := K)
  have hf : reverseTwistProjection Q E α = FiveBlock.reverseProjection e η := by
    funext i j
    rcases i with u | u | u | i | u <;> rfl
  have hg : reverseTwistInjection Q E α = FiveBlock.reverseInjection c η := by
    funext i j
    rcases j with v | v | v | j | v <;> rfl
  have hh : reverseTwistHomotopy Q E α = FiveBlock.reverseHomotopy ι := by
    funext i j
    rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v <;>
      simp only [reverseTwistHomotopy, inverseTwistHomotopy, FiveBlock.reverseHomotopy,
        Matrix.neg_apply, neg_zero, neg_neg]
    all_goals rfl
  have hd : reverseTwistDifferential Q E α =
      FiveBlock.reverseDifferential t r θ ι e E.differential c := by
    funext i j
    rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v <;> rfl
  have hId : inverseTwistIdentity Q E α = FiveBlock.identity ι η := by
    funext i j
    rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v <;> rfl
  rw [hf, hg, hh, hd, hId]
  apply FiveBlock.reverseContraction
  · exact projectiveIdentity_mul Q (projectiveEntries_identity Q)
  · exact projectiveIdentity_mul Q (projectiveEntries_identity Q)
  · exact projectiveIdentity_mul Q (E.testComplex Q α).entries
  · exact mul_projectiveIdentity Q (E.testComplex Q α).entries
  · exact mul_projectiveIdentity Q (unitContraction_entries Q E α)
  · exact projectiveIdentity_mul Q (testToken_entries Q E α)
  · exact projectiveIdentity_mul Q (evaluation_entries Q E.placement α)
  · exact mul_projectiveIdentity Q (evaluation_entries Q E.placement α)
  · exact mul_projectiveIdentity Q (coevaluation_entries Q E.placement α)
  · exact projectiveIdentity_mul Q (coevaluation_entries Q E.placement α)
  · exact evaluation_coevaluation Q hn E.placement α

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_NormalizedReverseTwistHomotopy
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

noncomputable def normalizedReverseTwistHomotopyEquivalence
    (hn : ∀ a, Q.source a ≠ Q.target a) (E : BasedComplex Q (K := K) I) (α : V) :
    HomotopyEquivalence Q (normalizedReverseTwist Q hn E α) E where
  forward := {
    matrix := reverseTwistProjection Q E α
    entries := by
      rw [normalizedReverseTwist_placement]
      exact reverseTwistProjection_entries Q E α
    degree := by
      rw [normalizedReverseTwist_placement]
      exact reverseTwistProjection_degree Q E α
    commute := by
      rw [normalizedReverseTwist_differential]
      exact reverseTwistProjection_commute Q E α }
  backward := {
    matrix := reverseTwistInjection Q E α
    entries := by
      rw [normalizedReverseTwist_placement]
      exact reverseTwistInjection_entries Q E α
    degree := by
      rw [normalizedReverseTwist_placement]
      exact reverseTwistInjection_degree Q E α
    commute := by
      rw [normalizedReverseTwist_differential]
      exact reverseTwistInjection_commute Q E α }
  sourceHomotopy := reverseTwistHomotopy Q E α
  targetHomotopy := 0
  sourceEntries := by
    rw [normalizedReverseTwist_placement]
    exact reverseTwistHomotopy_entries Q E α
  targetEntries := projectiveEntries_zero Q
  sourceDegree := by
    rw [normalizedReverseTwist_placement]
    exact reverseTwistHomotopy_degree Q E α
  targetDegree := mapDegree_zero Q (-1) 0
  sourceEquation := by
    dsimp only
    rw [normalizedReverseTwist_placement, normalizedReverseTwist_differential]
    exact reverseTwist_sourceEquation Q hn E α
  targetEquation := by
    dsimp only
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
    exact reverseTwist_targetEquation Q E α

noncomputable def negative_positive_homotopyEquivalence
    (hn : ∀ a, Q.source a ≠ Q.target a) (E : BasedComplex Q (K := K) I) (α : V) :
    HomotopyEquivalence Q ((E.positiveTwist Q α).negativeTwist Q α) E := by
  classical
  exact
  (((E.positiveTwist Q α).negativeTwist Q α).reindexHomotopyEquivalence Q
    (reverseTwistIndexEquiv Q hn E α)).trans Q
      (normalizedReverseTwistHomotopyEquivalence Q hn E α)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ConeMap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.Map

variable {V A K I J L N : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]
  [Fintype I] [Fintype J] [Fintype L] [Fintype N]
  {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
  {G : BasedComplex Q (K := K) L} {H : BasedComplex Q (K := K) N}

lemma coneMap_entries (f : Map Q E F) (g : Map Q G H)
    (a : Map Q E G) (b : Map Q F H) :
    ProjectiveEntries Q (f.conePlacement Q) (g.conePlacement Q)
      (Matrix.fromBlocks a.matrix 0 0 b.matrix) := by
  constructor
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact a.entries.1 i j
    · exact MulZeroClass.mul_zero _
    · exact MulZeroClass.mul_zero _
    · exact b.entries.1 i j
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact a.entries.2 i j
    · exact MulZeroClass.zero_mul _
    · exact MulZeroClass.zero_mul _
    · exact b.entries.2 i j

lemma coneMap_degree (f : Map Q E F) (g : Map Q G H)
    (a : Map Q E G) (b : Map Q F H) :
    MapDegree Q (f.conePlacement Q) (g.conePlacement Q) 0 0
      (Matrix.fromBlocks a.matrix 0 0 b.matrix) := by
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · constructor
    · intro hc
      apply (a.degree i j).1
      intro he
      apply hc
      dsimp only [conePlacement]
      omega
    · exact (a.degree i j).2
  · exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
  · exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
  · exact b.degree i j

noncomputable def coneMap (f : Map Q E F) (g : Map Q G H)
    (a : Map Q E G) (b : Map Q F H)
    (comm : a.matrix * g.matrix = f.matrix * b.matrix) :
    Map Q (f.cone Q) (g.cone Q) where
  matrix := Matrix.fromBlocks a.matrix 0 0 b.matrix
  entries := coneMap_entries Q f g a b
  degree := coneMap_degree Q f g a b
  commute := by
    change f.coneDifferential Q * _ = _ * g.coneDifferential Q
    unfold coneDifferential
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_zero, Matrix.zero_mul,
      zero_add, add_zero, neg_zero, a.commute, b.commute, comm]

lemma coconeMap_entries (f : Map Q E F) (g : Map Q G H)
    (a : Map Q E G) (b : Map Q F H) :
    ProjectiveEntries Q (f.coconePlacement Q) (g.coconePlacement Q)
      (Matrix.fromBlocks a.matrix 0 0 b.matrix) := by
  constructor
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact a.entries.1 i j
    · exact MulZeroClass.mul_zero _
    · exact MulZeroClass.mul_zero _
    · exact b.entries.1 i j
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact a.entries.2 i j
    · exact MulZeroClass.zero_mul _
    · exact MulZeroClass.zero_mul _
    · exact b.entries.2 i j

lemma coconeMap_degree (f : Map Q E F) (g : Map Q G H)
    (a : Map Q E G) (b : Map Q F H) :
    MapDegree Q (f.coconePlacement Q) (g.coconePlacement Q) 0 0
      (Matrix.fromBlocks a.matrix 0 0 b.matrix) := by
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · exact a.degree i j
  · exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
  · exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
  · constructor
    · intro hc
      apply (b.degree i j).1
      intro he
      apply hc
      dsimp only [coconePlacement]
      omega
    · exact (b.degree i j).2

noncomputable def coconeMap (f : Map Q E F) (g : Map Q G H)
    (a : Map Q E G) (b : Map Q F H)
    (comm : a.matrix * g.matrix = f.matrix * b.matrix) :
    Map Q (f.cocone Q) (g.cocone Q) where
  matrix := Matrix.fromBlocks a.matrix 0 0 b.matrix
  entries := coconeMap_entries Q f g a b
  degree := coconeMap_degree Q f g a b
  commute := by
    change f.coconeDifferential Q * _ = _ * g.coconeDifferential Q
    unfold coconeDifferential
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_zero, Matrix.zero_mul,
      zero_add, add_zero, neg_zero, a.commute, b.commute, comm]

variable [Fintype V] [DecidableEq A]

noncomputable def positiveTwist (f : Map Q E F) (α : V) :
    Map Q (E.positiveTwist Q α) (F.positiveTwist Q α) :=
  coneMap Q (E.evaluation Q α) (F.evaluation Q α) (f.test Q α) f
    (evaluation_natural Q α f.entries)

noncomputable def negativeTwist (f : Map Q E F) (α : V) :
    Map Q (E.negativeTwist Q α) (F.negativeTwist Q α) :=
  coconeMap Q (E.coevaluation Q α) (F.coevaluation Q α) f (f.cotest Q α)
    (coevaluation_natural Q α f.entries).symm

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.Map

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PositiveTwistHomotopy
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [Fintype J]

noncomputable def positiveTwistHomotopy (E : BasedComplex Q (K := K) I) (α : V)
    (h : Matrix I I (Q.Zigzag K)) :=
  Matrix.fromBlocks (-testTransform Q E.placement E.placement α h) 0 0 h

noncomputable def negativeTwistHomotopy (E : BasedComplex Q (K := K) I) (α : V)
    (h : Matrix I I (Q.Zigzag K)) :=
  Matrix.fromBlocks h 0 0 (-testTransform Q E.placement E.placement α h)

lemma positiveTwistHomotopy_entries (E : BasedComplex Q (K := K) I) (α : V)
    {h : Matrix I I (Q.Zigzag K)} (hh : ProjectiveEntries Q E.placement E.placement h) :
    ProjectiveEntries Q (E.positiveTwist Q α).placement (E.positiveTwist Q α).placement
      (positiveTwistHomotopy Q E α h) := by
  have ht : ProjectiveEntries Q (testPlacement Q E.placement α)
      (testPlacement Q E.placement α) (testTransform Q E.placement E.placement α h) :=
    scalarCornerMatrix_entries Q α _ _ (fun _ => rfl) (fun _ => rfl) _
  constructor
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact (projectiveEntries_neg Q ht).1 i j
    · exact MulZeroClass.mul_zero _
    · exact MulZeroClass.mul_zero _
    · exact hh.1 i j
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact (projectiveEntries_neg Q ht).2 i j
    · exact MulZeroClass.zero_mul _
    · exact MulZeroClass.zero_mul _
    · exact hh.2 i j

lemma negativeTwistHomotopy_entries (E : BasedComplex Q (K := K) I) (α : V)
    {h : Matrix I I (Q.Zigzag K)} (hh : ProjectiveEntries Q E.placement E.placement h) :
    ProjectiveEntries Q (E.negativeTwist Q α).placement (E.negativeTwist Q α).placement
      (negativeTwistHomotopy Q E α h) := by
  have ht : ProjectiveEntries Q (cotestPlacement Q E.placement α)
      (cotestPlacement Q E.placement α) (testTransform Q E.placement E.placement α h) :=
    scalarCornerMatrix_entries Q α _ _ (fun _ => rfl) (fun _ => rfl) _
  constructor
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact hh.1 i j
    · exact MulZeroClass.mul_zero _
    · exact MulZeroClass.mul_zero _
    · exact (projectiveEntries_neg Q ht).1 i j
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact hh.2 i j
    · exact MulZeroClass.zero_mul _
    · exact MulZeroClass.zero_mul _
    · exact (projectiveEntries_neg Q ht).2 i j

lemma positiveTwistHomotopy_degree (E : BasedComplex Q (K := K) I) (α : V)
    {h : Matrix I I (Q.Zigzag K)} (hh : MapDegree Q E.placement E.placement (-1) 0 h) :
    MapDegree Q (E.positiveTwist Q α).placement (E.positiveTwist Q α).placement (-1) 0
      (positiveTwistHomotopy Q E α h) := by
  have ht := mapDegree_neg Q (testMatrix_degree Q α hh)
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · constructor
    · intro hc
      apply (ht i j).1
      intro he
      apply hc
      change (testPlacement Q E.placement α j).cochain - 1 =
        (testPlacement Q E.placement α i).cochain - 1 + -1
      omega
    · exact (ht i j).2
  · exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
  · exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
  · exact hh i j

lemma negativeTwistHomotopy_degree (E : BasedComplex Q (K := K) I) (α : V)
    {h : Matrix I I (Q.Zigzag K)} (hh : MapDegree Q E.placement E.placement (-1) 0 h) :
    MapDegree Q (E.negativeTwist Q α).placement (E.negativeTwist Q α).placement (-1) 0
      (negativeTwistHomotopy Q E α h) := by
  have ht := mapDegree_neg Q (cotestMatrix_degree Q α hh)
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · exact hh i j
  · exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
  · exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
  · constructor
    · intro hc
      apply (ht i j).1
      intro he
      apply hc
      change (cotestPlacement Q E.placement α j).cochain + 1 =
        (cotestPlacement Q E.placement α i).cochain + 1 + -1
      omega
    · exact (ht i j).2

lemma positiveTwistHomotopy_boundary (E : BasedComplex Q (K := K) I) (α : V)
    {h : Matrix I I (Q.Zigzag K)} (hh : ProjectiveEntries Q E.placement E.placement h) :
    (E.positiveTwist Q α).differential * positiveTwistHomotopy Q E α h +
      positiveTwistHomotopy Q E α h * (E.positiveTwist Q α).differential =
    Matrix.fromBlocks
      (testTransform Q E.placement E.placement α (E.differential * h + h * E.differential))
      0 0 (E.differential * h + h * E.differential) := by
  change Matrix.fromBlocks (-testTransform Q _ _ α E.differential)
      (evaluationMatrix Q E.placement α) 0 E.differential * _ +
    _ * Matrix.fromBlocks (-testTransform Q _ _ α E.differential)
      (evaluationMatrix Q E.placement α) 0 E.differential = _
  unfold positiveTwistHomotopy
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_zero, Matrix.zero_mul,
    zero_add, add_zero, neg_zero]
  rw [testTransform_mul Q α _ E.entries, testTransform_mul Q α _ hh,
    evaluation_natural Q α hh, add_neg_cancel, testTransform_add]

lemma negativeTwistHomotopy_boundary (E : BasedComplex Q (K := K) I) (α : V)
    {h : Matrix I I (Q.Zigzag K)} (hh : ProjectiveEntries Q E.placement E.placement h) :
    (E.negativeTwist Q α).differential * negativeTwistHomotopy Q E α h +
      negativeTwistHomotopy Q E α h * (E.negativeTwist Q α).differential =
    Matrix.fromBlocks (E.differential * h + h * E.differential) 0 0
      (testTransform Q E.placement E.placement α (E.differential * h + h * E.differential)) := by
  change Matrix.fromBlocks E.differential (coevaluationMatrix Q E.placement α) 0
      (-testTransform Q _ _ α E.differential) * _ +
    _ * Matrix.fromBlocks E.differential (coevaluationMatrix Q E.placement α) 0
      (-testTransform Q _ _ α E.differential) = _
  unfold negativeTwistHomotopy
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_zero, Matrix.zero_mul,
    zero_add, add_zero, neg_zero]
  rw [testTransform_mul Q α _ E.entries, testTransform_mul Q α _ hh,
    coevaluation_natural Q α hh, neg_add_cancel, testTransform_add]

lemma positiveTwist_identity [DecidableEq I] (E : BasedComplex Q (K := K) I) (α : V) :
    projectiveIdentity Q (K := K) (E.positiveTwist Q α).placement =
      Matrix.fromBlocks (testTransform Q E.placement E.placement α
        (projectiveIdentity Q E.placement)) 0 0 (projectiveIdentity Q E.placement) := by
  rw [testTransform_identity]
  unfold projectiveIdentity
  rw [Matrix.fromBlocks_diagonal]
  congr 1
  funext i
  rcases i with i | i <;> rfl

lemma negativeTwist_identity [DecidableEq I] (E : BasedComplex Q (K := K) I) (α : V) :
    projectiveIdentity Q (K := K) (E.negativeTwist Q α).placement =
      Matrix.fromBlocks (projectiveIdentity Q E.placement) 0 0
        (testTransform Q E.placement E.placement α (projectiveIdentity Q E.placement)) := by
  rw [testTransform_identity]
  unfold projectiveIdentity
  rw [Matrix.fromBlocks_diagonal]
  congr 1
  funext i
  rcases i with i | i <;> rfl

lemma positiveTwist_homotopy_equation [DecidableEq I]
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    (f : Map Q E F) (g : Map Q F E) (α : V)
    {h : Matrix I I (Q.Zigzag K)} (hh : ProjectiveEntries Q E.placement E.placement h)
    (he : f.matrix * g.matrix = projectiveIdentity Q E.placement +
      (E.differential * h + h * E.differential)) :
    (f.positiveTwist Q α).matrix * (g.positiveTwist Q α).matrix =
      projectiveIdentity Q (E.positiveTwist Q α).placement +
      ((E.positiveTwist Q α).differential * positiveTwistHomotopy Q E α h +
        positiveTwistHomotopy Q E α h * (E.positiveTwist Q α).differential) := by
  rw [positiveTwistHomotopy_boundary Q E α hh, positiveTwist_identity,
    Matrix.fromBlocks_add]
  change Matrix.fromBlocks (testTransform Q _ _ α f.matrix) 0 0 f.matrix *
    Matrix.fromBlocks (testTransform Q _ _ α g.matrix) 0 0 g.matrix = _
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [testTransform_mul Q α _ f.entries, he, testTransform_add]

lemma negativeTwist_homotopy_equation [DecidableEq I]
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    (f : Map Q E F) (g : Map Q F E) (α : V)
    {h : Matrix I I (Q.Zigzag K)} (hh : ProjectiveEntries Q E.placement E.placement h)
    (he : f.matrix * g.matrix = projectiveIdentity Q E.placement +
      (E.differential * h + h * E.differential)) :
    (f.negativeTwist Q α).matrix * (g.negativeTwist Q α).matrix =
      projectiveIdentity Q (E.negativeTwist Q α).placement +
      ((E.negativeTwist Q α).differential * negativeTwistHomotopy Q E α h +
        negativeTwistHomotopy Q E α h * (E.negativeTwist Q α).differential) := by
  rw [negativeTwistHomotopy_boundary Q E α hh, negativeTwist_identity,
    Matrix.fromBlocks_add]
  change Matrix.fromBlocks f.matrix 0 0 (testTransform Q _ _ α f.matrix) *
    Matrix.fromBlocks g.matrix 0 0 (testTransform Q _ _ α g.matrix) = _
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [testTransform_mul Q α _ f.entries, he, testTransform_add]

namespace HomotopyEquivalence

variable [DecidableEq I] [DecidableEq J]

noncomputable def positiveTwist {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (e : HomotopyEquivalence Q E F) (α : V) :
    HomotopyEquivalence Q (E.positiveTwist Q α) (F.positiveTwist Q α) where
  forward := e.forward.positiveTwist Q α
  backward := e.backward.positiveTwist Q α
  sourceHomotopy := positiveTwistHomotopy Q E α e.sourceHomotopy
  targetHomotopy := positiveTwistHomotopy Q F α e.targetHomotopy
  sourceEntries := positiveTwistHomotopy_entries Q E α e.sourceEntries
  targetEntries := positiveTwistHomotopy_entries Q F α e.targetEntries
  sourceDegree := positiveTwistHomotopy_degree Q E α e.sourceDegree
  targetDegree := positiveTwistHomotopy_degree Q F α e.targetDegree
  sourceEquation := positiveTwist_homotopy_equation Q e.forward e.backward α
    e.sourceEntries e.sourceEquation
  targetEquation := positiveTwist_homotopy_equation Q e.backward e.forward α
    e.targetEntries e.targetEquation

noncomputable def negativeTwist {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (e : HomotopyEquivalence Q E F) (α : V) :
    HomotopyEquivalence Q (E.negativeTwist Q α) (F.negativeTwist Q α) where
  forward := e.forward.negativeTwist Q α
  backward := e.backward.negativeTwist Q α
  sourceHomotopy := negativeTwistHomotopy Q E α e.sourceHomotopy
  targetHomotopy := negativeTwistHomotopy Q F α e.targetHomotopy
  sourceEntries := negativeTwistHomotopy_entries Q E α e.sourceEntries
  targetEntries := negativeTwistHomotopy_entries Q F α e.targetEntries
  sourceDegree := negativeTwistHomotopy_degree Q E α e.sourceDegree
  targetDegree := negativeTwistHomotopy_degree Q F α e.targetDegree
  sourceEquation := negativeTwist_homotopy_equation Q e.forward e.backward α
    e.sourceEntries e.sourceEquation
  targetEquation := negativeTwist_homotopy_equation Q e.backward e.forward α
    e.targetEntries e.targetEquation

end HomotopyEquivalence
end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_SimpleEdge
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.dual_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.source_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.target_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_false _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_true
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A : Type*} (Q : ReversibleQuiver V A)

structure SimpleEdge (α β : V) where
  arrow : A
  source : Q.source arrow = α
  target : Q.target arrow = β
  distinct : α ≠ β
  unique : ∀ a, Q.source a = α → Q.target a = β → a = arrow

namespace SimpleEdge

variable {α β : V} (e : SimpleEdge Q α β)

def reverse : SimpleEdge Q β α where
  arrow := Q.reverse e.arrow
  source := (Q.source_reverse _).trans e.target
  target := (Q.target_reverse _).trans e.source
  distinct := e.distinct.symm
  unique a hs ht := by
    have h := e.unique (Q.reverse a) ((Q.source_reverse _).trans ht)
      ((Q.target_reverse _).trans hs)
    have h' := congrArg Q.reverse h
    simpa only [Q.reverse_reverse] using h'

def corner : CornerPath Q α β := ⟨.inr (.inl e.arrow), e.source, e.target⟩

@[simp] lemma corner_val : (e.corner Q).val = .inr (.inl e.arrow) := rfl
@[simp] lemma reverse_arrow : (e.reverse Q).arrow = Q.reverse e.arrow := rfl

end SimpleEdge
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_ExtArrow
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.dual_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.source_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.target_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_false _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_true
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge

variable {V A : Type*} (Q : ReversibleQuiver V A) {α β : V}

lemma ext_arrow {e f : SimpleEdge Q α β} (h : e.arrow = f.arrow) : e = f := by
  cases e
  cases f
  cases h
  rfl

@[simp] lemma reverse_reverse (e : SimpleEdge Q α β) : (e.reverse Q).reverse Q = e := by
  apply ext_arrow Q
  exact Q.reverse_reverse e.arrow

end HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_FiniteHomotopySetoid
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

def finiteHomotopySetoid : Setoid (FiniteModel.{u} Q (K := K)) where
  r E F := Nonempty (HomotopyEquivalence Q E.complex F.complex)
  iseqv := {
    refl E := ⟨HomotopyEquivalence.refl Q E.complex⟩
    symm := fun ⟨e⟩ => ⟨e.symm Q⟩
    trans := fun ⟨e⟩ ⟨f⟩ => ⟨e.trans Q f⟩ }

abbrev FiniteHomotopyClass := Quotient (finiteHomotopySetoid Q (K := K))

noncomputable def classPositiveTwist (α : V) :
    FiniteHomotopyClass Q (K := K) → FiniteHomotopyClass Q (K := K) :=
  Quotient.map (fun E => FiniteModel.ofComplex Q (E.complex.positiveTwist Q α))
    (by
      intro E F ⟨e⟩
      change Nonempty (HomotopyEquivalence Q (E.complex.positiveTwist Q α)
        (F.complex.positiveTwist Q α))
      refine ⟨?_⟩
      convert e.positiveTwist Q α using 1)

noncomputable def classNegativeTwist (α : V) :
    FiniteHomotopyClass Q (K := K) → FiniteHomotopyClass Q (K := K) :=
  Quotient.map (fun E => FiniteModel.ofComplex Q (E.complex.negativeTwist Q α))
    (by
      intro E F ⟨e⟩
      change Nonempty (HomotopyEquivalence Q (E.complex.negativeTwist Q α)
        (F.complex.negativeTwist Q α))
      refine ⟨?_⟩
      convert e.negativeTwist Q α using 1)

namespace FiniteModel

noncomputable def minimalRepresentative (E : FiniteModel.{u} Q (K := K)) :
    FiniteModel.{u} Q (K := K) := (E.exists_minimal Q).choose

end FiniteModel

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_PacketIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.dual_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.source_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.target_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_false _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_true
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [Fintype J] [DecidableEq J]

abbrev PacketIndex (p : I → GeneratorPlacement V) (v : J → V) :=
  (a : J) × TestIndex Q p (v a)

def packetPlacement (p : I → GeneratorPlacement V) (v : J → V) :
    PacketIndex Q p v → GeneratorPlacement V :=
  fun x => testPlacement Q p (v x.1) x.2

noncomputable def packetDifferential (p : I → GeneratorPlacement V) (v : J → V)
    (M : Matrix I I (Zigzag Q K)) :
    Matrix (PacketIndex Q p v) (PacketIndex Q p v) (Zigzag Q K) :=
  Matrix.blockDiagonal' (fun a => scalarCornerMatrix Q (v a) (testMatrix Q p p (v a) M))

omit [DecidableEq A] [Fintype I] [Fintype J] in
lemma packet_entries (p : I → GeneratorPlacement V) (v : J → V)
    (M : Matrix I I (Zigzag Q K)) :
    ProjectiveEntries Q (packetPlacement Q p v) (packetPlacement Q p v)
      (packetDifferential Q p v M) := by
  constructor
  · rintro ⟨a,x⟩ ⟨b,y⟩
    by_cases h : a=b
    · subst b
      rw [packetDifferential,Matrix.blockDiagonal'_apply_eq]
      exact (scalarCornerMatrix_entries Q (v a) (testPlacement Q p (v a)) (testPlacement Q p (v a)) (fun _ => rfl) (fun _ => rfl) _).1 x y
    · rw [packetDifferential,Matrix.blockDiagonal'_apply_ne _ _ _ h,mul_zero]
  · rintro ⟨a,x⟩ ⟨b,y⟩
    by_cases h : a=b
    · subst b
      rw [packetDifferential,Matrix.blockDiagonal'_apply_eq]
      exact (scalarCornerMatrix_entries Q (v a) (testPlacement Q p (v a)) (testPlacement Q p (v a)) (fun _ => rfl) (fun _ => rfl) _).2 x y
    · rw [packetDifferential,Matrix.blockDiagonal'_apply_ne _ _ _ h,zero_mul]

omit [Fintype I] [Fintype J] in
lemma packet_degree (p : I → GeneratorPlacement V) (v : J → V)
    (M : Matrix I I (Zigzag Q K)) (hM : MapDegree Q p p 1 0 M) :
    MapDegree Q (packetPlacement Q p v) (packetPlacement Q p v) 1 0
      (packetDifferential Q p v M) := by
  rintro ⟨a,x⟩ ⟨b,y⟩
  by_cases h : a=b
  · subst b
    rw [packetDifferential,Matrix.blockDiagonal'_apply_eq]
    exact testMatrix_degree Q (v a) hM x y
  · rw [packetDifferential,Matrix.blockDiagonal'_apply_ne _ _ _ h]
    exact ⟨fun _ => rfl,homogeneous_zero Q _⟩

namespace BasedComplex

noncomputable def packetTest (E : BasedComplex Q (K := K) I) (v : J → V) :
    BasedComplex Q (K := K) (PacketIndex Q E.placement v) where
  placement := packetPlacement Q E.placement v
  differential := packetDifferential Q E.placement v E.differential
  entries := packet_entries Q E.placement v E.differential
  degree := packet_degree Q E.placement v E.differential E.degree
  square_zero := by
    simp only [packetDifferential,← Matrix.blockDiagonal'_mul]
    have h : (fun a => scalarCornerMatrix Q (v a) (testMatrix Q E.placement E.placement (v a) E.differential) *
        scalarCornerMatrix Q (v a) (testMatrix Q E.placement E.placement (v a) E.differential)) = 0 := by
      funext a
      exact (E.testComplex Q (v a)).square_zero
    rw [h,Matrix.blockDiagonal'_zero]

noncomputable def packetEvaluationMatrix (E : BasedComplex Q (K := K) I) (v : J → V) :
    Matrix (PacketIndex Q E.placement v) I (Zigzag Q K) :=
  fun x i => evaluationMatrix Q E.placement (v x.1) x.2 i

lemma packetEvaluation_commute (E : BasedComplex Q (K := K) I) (v : J → V) :
    (E.packetTest Q v).differential * E.packetEvaluationMatrix Q v =
      E.packetEvaluationMatrix Q v * E.differential := by
  apply Matrix.ext
  rintro ⟨a,x⟩ i
  change (∑ y, packetDifferential Q E.placement v E.differential ⟨a,x⟩ y *
      packetEvaluationMatrix Q E v y i) = _
  rw [Fintype.sum_sigma,Finset.sum_eq_single a]
  · simp only [packetDifferential,Matrix.blockDiagonal'_apply_eq,packetEvaluationMatrix]
    exact congrFun (congrFun (E.evaluation Q (v a)).commute x) i
  · intro b hb hba
    apply Finset.sum_eq_zero
    intro y hy
    rw [packetDifferential,Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hba),zero_mul]
  · simp

noncomputable def packetEvaluation (E : BasedComplex Q (K := K) I) (v : J → V) :
    Map Q (E.packetTest Q v) E where
  matrix := E.packetEvaluationMatrix Q v
  entries := ⟨fun x i => (evaluation_entries Q E.placement (v x.1)).1 x.2 i,
    fun x i => (evaluation_entries Q E.placement (v x.1)).2 x.2 i⟩
  degree := fun x i => evaluation_degree Q E.placement (v x.1) x.2 i
  commute := E.packetEvaluation_commute Q v

noncomputable def packetTwist (E : BasedComplex Q (K := K) I) (v : J → V) :
    BasedComplex Q (K := K) (PacketIndex Q E.placement v ⊕ I) :=
  (E.packetEvaluation Q v).cone Q

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PacketConsEquiv
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I J L : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

noncomputable def packetConsEquiv (E : BasedComplex Q (K := K) I)
    (α:V) (v:J → V) (h : ∀ a, OrthogonalVertices Q α (v a)) :
    (PacketIndex Q E.placement (fun z : Option J => z.elim α v) ⊕ I) ≃
      (TestIndex Q (E.packetTwist Q v).placement α ⊕ (PacketIndex Q E.placement v ⊕ I)) where
  toFun
    | .inl ⟨none,u⟩ => .inl ⟨.inr u.1,u.2⟩
    | .inl ⟨some a,u⟩ => .inr (.inl ⟨a,u⟩)
    | .inr i => .inr (.inr i)
  invFun
    | .inl ⟨.inl ⟨a,_⟩,p⟩ => (no_corner_of_orthogonal Q (h a) p).elim
    | .inl ⟨.inr i,p⟩ => .inl ⟨none,i,p⟩
    | .inr (.inl ⟨a,u⟩) => .inl ⟨some a,u⟩
    | .inr (.inr i) => .inr i
  left_inv z := by rcases z with ⟨_|a,u⟩|i <;> rfl
  right_inv z := by
    rcases z with ⟨⟨a,x⟩|i,p⟩|⟨a,u⟩|i
    · exact (no_corner_of_orthogonal Q (h a) p).elim
    all_goals rfl

lemma packetCons_eq (E : BasedComplex Q (K := K) I)
    (α:V) (v:J → V) (h : ∀ a, OrthogonalVertices Q α (v a)) :
    ((E.packetTwist Q v).positiveTwist Q α).reindex Q (packetConsEquiv Q E α v h) =
      E.packetTwist Q (fun z : Option J => z.elim α v) := by
  apply ext_placement_differential Q
  · funext z
    rcases z with ⟨_|a,u⟩|i <;> rfl
  · apply Matrix.ext
    intro z w
    rcases z with ⟨_|a,u⟩|i <;> rcases w with ⟨_|b,t⟩|j
    all_goals dsimp only [reindex, Matrix.submatrix_apply, packetConsEquiv, Equiv.coe_fn_mk]
    all_goals simp only [
      positiveTwist_differential,packetTwist,Map.cone,packetEvaluation,packetTest,
      Map.coneDifferential,Matrix.fromBlocks,Matrix.of_apply,Matrix.neg_apply,Matrix.zero_apply,
      testTransform,scalarCornerMatrix,testMatrix,packetDifferential,packetEvaluationMatrix,
      evaluationMatrix,Sum.inr_ne_inl,Sum.inr.injEq,Sum.elim_inl,Sum.elim_inr,Option.elim_none,
      Option.elim_some,Matrix.blockDiagonal'_apply_eq,↓reduceIte]
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ (by simp),neg_zero]
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ (by simp),neg_zero]
    · by_cases hab : a=b
      · subst b
        simp only [Matrix.blockDiagonal',Matrix.of_apply, ↓reduceDIte,Option.elim_some]
      · simp only [Matrix.blockDiagonal',Matrix.of_apply,hab,Option.some.injEq, ↓reduceDIte]

variable [Fintype L] [DecidableEq L]

def packetReindexEquiv (E : BasedComplex Q (K := K) I) (v:J → V) (e:L ≃ J) :
    (PacketIndex Q E.placement (v ∘ e) ⊕ I) ≃ (PacketIndex Q E.placement v ⊕ I) :=
  Equiv.sumCongr (Equiv.sigmaCongrLeft (β := fun a : J => TestIndex Q E.placement (v a)) e) (Equiv.refl I)

omit [DecidableEq I] in
lemma packetReindex_eq (E : BasedComplex Q (K := K) I) (v:J → V) (e:L ≃ J) :
    (E.packetTwist Q v).reindex Q (packetReindexEquiv Q E v e) = E.packetTwist Q (v ∘ e) := by
  apply ext_placement_differential Q
  · funext z
    rcases z with ⟨a,u⟩|i <;> rfl
  · apply Matrix.ext
    intro z w
    rcases z with ⟨a,u⟩|i <;> rcases w with ⟨b,t⟩|j
    · change -(Matrix.blockDiagonal' (fun a => scalarCornerMatrix Q (v a)
        (testMatrix Q E.placement E.placement (v a) E.differential)) ⟨e a,u⟩ ⟨e b,t⟩) = _
      by_cases hab : a=b
      · subst b
        simp only [packetTwist,Map.cone,Map.coneDifferential,packetEvaluation,packetTest,
          packetDifferential,Matrix.fromBlocks,Matrix.of_apply,Matrix.neg_apply,
          Matrix.blockDiagonal'_apply_eq,Function.comp_apply,Sum.elim_inl]
      · rw [Matrix.blockDiagonal'_apply_ne _ _ _ (fun he => hab (e.injective he))]
        change -(0 : Zigzag Q K) = -(Matrix.blockDiagonal' (fun a : L =>
          scalarCornerMatrix Q (v (e a)) (testMatrix Q E.placement E.placement (v (e a)) E.differential)) ⟨a,u⟩ ⟨b,t⟩)
        rw [Matrix.blockDiagonal'_apply_ne _ _ _ hab]
    all_goals rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_BasedComplexComplex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

noncomputable def classOfComplex {I : Type u} [Fintype I] [DecidableEq I]
    (E : BasedComplex Q (K := K) I) : FiniteHomotopyClass Q (K := K) :=
  Quotient.mk (finiteHomotopySetoid Q) (FiniteModel.ofComplex Q E)

omit [Fintype V] [DecidableEq A] in
lemma classOfComplex_eq {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    (e : HomotopyEquivalence Q E F) : classOfComplex Q E = classOfComplex Q F :=
  Quotient.sound ⟨e⟩

omit [Fintype V] [DecidableEq A] in
lemma classOfComplex_reindex {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (E : BasedComplex Q (K := K) I) (e : J ≃ I) :
    classOfComplex Q E = classOfComplex Q (E.reindex Q e) :=
  classOfComplex_eq Q (E.reindexHomotopyEquivalence Q e)

lemma classOfComplex_packet_reindex {I J L : Type u}
    [Fintype I] [Fintype J] [Fintype L] [DecidableEq I] [DecidableEq J] [DecidableEq L]
    (E : BasedComplex Q (K := K) I) (v:J → V) (e:L ≃ J) :
    classOfComplex Q (E.packetTwist Q v) = classOfComplex Q (E.packetTwist Q (v ∘ e)) := by
  rw [classOfComplex_reindex Q _ (packetReindexEquiv Q E v e),packetReindex_eq]

lemma classOfComplex_packet_cons {I J : Type u}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (E : BasedComplex Q (K := K) I) (α:V) (v:J → V)
    (h : ∀ a, OrthogonalVertices Q α (v a)) :
    classOfComplex Q (E.packetTwist Q (fun z : Option J => z.elim α v)) =
      classPositiveTwist Q α (classOfComplex Q (E.packetTwist Q v)) := by
  change _ = classOfComplex Q ((E.packetTwist Q v).positiveTwist Q α)
  rw [classOfComplex_reindex Q _ (packetConsEquiv Q E α v h),packetCons_eq]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_InitialProjective
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

noncomputable def initialProjective (α : V) : BasedComplex Q (K := K) PUnit where
  placement _ := ⟨α, 0, 0⟩
  differential := 0
  entries := projectiveEntries_zero Q
  degree := mapDegree_zero Q 1 0
  square_zero := Matrix.zero_mul _

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_Initial
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

noncomputable def initialClass (α : V) : FiniteHomotopyClass Q (K := K) :=
  Quotient.mk (finiteHomotopySetoid Q) (FiniteModel.ofComplex Q (initialProjective Q α))

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_MinimalModel
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

noncomputable def minimalClassModel (x : FiniteHomotopyClass Q (K := K)) :
    FiniteModel.{u} Q (K := K) := (Quotient.out x).minimalRepresentative Q

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_Path
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.dual_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.source_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.target_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_false _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_true
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Iso
open Zigzag

variable {V A W B K : Type*} {Q : ReversibleQuiver V A} {R : ReversibleQuiver W B}
  (e : Iso Q R)

def path : Path V A ≃ Path W B := e.vertex.sumCongr (e.arrow.sumCongr e.vertex)

@[simp] lemma path_source (p:Path V A) : Path.source R (e.path p) = e.vertex (Path.source Q p) := by
  rcases p with v|a|v
  · rfl
  · exact e.source a
  · rfl
@[simp] lemma path_target (p:Path V A) : Path.target R (e.path p) = e.vertex (Path.target Q p) := by
  rcases p with v|a|v
  · rfl
  · exact e.target a
  · rfl
@[simp] lemma path_length (p:Path V A) : Path.length (e.path p) = Path.length p := by
  rcases p with v|a|v <;> rfl

end HarmonicArtin.ReversibleQuiver.Iso

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_ReversibleQuiverMap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Iso
open Zigzag Zigzag.BasedComplex

universe u
variable {V A W B : Type u} {K : Type*} {Q : ReversibleQuiver V A} {R : ReversibleQuiver W B}
  (e : Iso Q R) [Field K] [Fintype V] [Fintype W] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq W] [DecidableEq A] [DecidableEq B]
  {I : Type u} [Fintype I] [DecidableEq I]

noncomputable def classMap : FiniteHomotopyClass Q (K := K) → FiniteHomotopyClass R (K := K) :=
  Quotient.map (fun E => FiniteModel.ofComplex R (e.complex E.complex)) (by
    intro E F ⟨h⟩
    exact ⟨e.homotopyEquivalence h⟩)

omit [Fintype V] [Fintype W] [DecidableEq A] [DecidableEq B] in
@[simp] lemma classMap_complex (E:BasedComplex Q (K := K) I) :
    e.classMap (classOfComplex Q E) = classOfComplex R (e.complex E) := rfl

end HarmonicArtin.ReversibleQuiver.Iso

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionVertex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

variable {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m : E → ℕ) (d : V → V → FusionEdge E)

noncomputable def fusionArrowReverse (hd : ∀ s t, d s t = d t s) :
    FusionQuiverArrow m d → FusionQuiverArrow m d := fun a =>
  ⟨(a.1.2,a.1.1), Fin.cast (by rw [hd a.1.1.1 a.1.2.1, FusionEdge.multiplicity_symm]) a.2⟩

omit [Fintype V] [DecidableEq V] in
lemma fusionArrowReverse_twice (hd : ∀ s t, d s t = d t s) (a : FusionQuiverArrow m d) :
    fusionArrowReverse m d hd (fusionArrowReverse m d hd a) = a := by
  rcases a with ⟨⟨α,β⟩,k⟩
  rfl

noncomputable def fusionQuiver (hd : ∀ s t, d s t = d t s) :
    ReversibleQuiver (FusionVertex (V := V) m) (FusionQuiverArrow m d) where
  source a := a.1.1
  target a := a.1.2
  reverse :=
    { toFun := fusionArrowReverse m d hd
      invFun := fusionArrowReverse m d hd
      left_inv := fusionArrowReverse_twice m d hd
      right_inv := fusionArrowReverse_twice m d hd }
  reverse_reverse := fusionArrowReverse_twice m d hd
  source_reverse _ := rfl
  target_reverse _ := rfl

end HarmonicArtin

end OAI
end


