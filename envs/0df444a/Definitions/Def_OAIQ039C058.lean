-- Prove2me | Definitions.Def_OAIQ039C058
-- name    : OAIQ039C058
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:15:31.182041+00:00
-- url     : https://prove2.me/theorems/10925da3-f74a-474f-ab29-af32a7dbbcba
-- title:
--   Definitions bundle OAIQ039C058 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 25 declarations of OpenAI's Lean: 18 definitions, 1 inductive type or structure and 6 theorems. The definitions and types are `OAI.Kadison.FreeBlocks.WordActions`, `OAI.Kadison.FreeBlocks.tracialWordActions`, `OAI.Kadison.FreeBlocks.wordConjugationAction`, `OAI.Kadison.FreeBlocks.wordLeftAction`, `OAI.Kadison.FreeBlocks.wordLevel`, `OAI.Kadison.FreeBlocks.wordStructure`, `OAI.Kadison.FreeBlocks.wordStructureRule`, `OAI.Kadison.PartialIsometryOrder.DyadicCuts.cut`, `OAI.Kadison.PartialIsometryOrder.DyadicCuts.half`, `OAI.Kadison.PartialIsometryOrder.DyadicCuts.link`, `OAI.Kadison.PartialIsometryOrder.DyadicCuts.next`, `OAI.Kadison.PartialIsometryOrder.DyadicCuts.side`, `OAI.Kadison.PartialIsometryOrder.DyadicPartition.dimension`, `OAI.Kadison.PartialIsometryOrder.DyadicPartition.lower`, `OAI.Kadison.PartialIsometryOrder.DyadicPartition.partition`, `OAI.Kadison.TracialGNS.rightOperator`, `OAI.Kadison.TracialGNS.stageCoefficient`, `OAI.Kadison.TracialGNS.wordConjugation`, `OAI.Kadison.TracialGNS.wordLeft`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_CountableProjectionJoin`, `Commutator_DiffuseHalving`, `Commutator_DyadicCuts`, `Commutator_DyadicDimension`, `Commutator_DyadicPartition`, `Commutator_EndpointGNS`, `Commutator_EndpointGNS2`, `Commutator_FreeActualStructure`, `Commutator_ProjectionJoin`, `Commutator_TracialCommutation`, `Commutator_TracialRightClosure`.
--
--   **Imports.** It imports the bundles `OAIQ039C046`, `OAIQ039C047`, `OAIQ039C048`, `OAIQ039C051` and `OAIQ039C052` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C066`, `OAIQ039C067`, `OAIQ039C068` and `OAIQ039C069`; the statements `OAI.Kadison.PartialIsometryOrder.DyadicPartition.dimension_base`, `OAI.Kadison.PartialIsometryOrder.DyadicPartition.dimension_complement`, `OAI.Kadison.PartialIsometryOrder.DyadicPartition.dimension_difference`, `OAI.Kadison.PartialIsometryOrder.DyadicPartition.dimension_tendsto_of_strong_increasing`, `OAI.Kadison.PartialIsometryOrder.DyadicPartition.exists_base_subEquivalent`, `OAI.Kadison.PartialIsometryOrder.DyadicPartition.exists_coherent_comparisons`, `OAI.Kadison.PartialIsometryOrder.DyadicPartition.lower_orthogonal_add_le`, `OAI.Kadison.PartialIsometryOrder.DyadicPartition.lower_orthogonal_add_upper`, `OAI.Kadison.PartialIsometryOrder.DyadicPartition.subEquivalent_of_dimension_le`, `OAI.Kadison.ProjectionDimensionTopology.vector_uniform_absolute_continuity`, `OAI.Kadison.ProjectionJoin.dimension_finiteJoin_le`, `OAI.Kadison.TraceDimension.trace_projection_dimension`, `OAI.Kadison.TracialGNS.stageCoefficient_crossing`, `OAI.Kadison.TracialGNS.stageCoefficient_cycleCutoff`, `OAI.Kadison.TracialGNS.stageCoefficient_rank_one`, `OAI.Kadison.TracialGNS.stageWord_inner_classification`, `OAI.Kadison.TracialGNS.stage_pairing_expansion`, `OAI.Kadison.TracialGNS.stage_pairing_same_side_zero` and `OAI.Kadison.TracialGNS.word_multiplicity_slices`; the proofs of `OAI.Kadison.NormalGNS.commutant_range_eq_of_commutative`, `OAI.Kadison.OrbitStateHull.hull_projectionContinuousAtOne`, `OAI.Kadison.PartialIsometryOrder.DyadicPartition.dimension_base`, `OAI.Kadison.PartialIsometryOrder.DyadicPartition.dimension_complement`, `OAI.Kadison.PartialIsometryOrder.DyadicPartition.dimension_difference`, `OAI.Kadison.PartialIsometryOrder.DyadicPartition.dimension_tendsto_of_strong_increasing`, `OAI.Kadison.PartialIsometryOrder.DyadicPartition.exists_base_subEquivalent`, `OAI.Kadison.PartialIsometryOrder.DyadicPartition.exists_coherent_comparisons`, `OAI.Kadison.PartialIsometryOrder.DyadicPartition.lower_orthogonal_add_le`, `OAI.Kadison.PartialIsometryOrder.DyadicPartition.lower_orthogonal_add_upper`, `OAI.Kadison.PartialIsometryOrder.DyadicPartition.subEquivalent_of_dimension_le`, `OAI.Kadison.ProjectionJoin.dimension_finiteJoin_le`, `OAI.Kadison.TraceDimension.faithful`, `OAI.Kadison.TraceDimension.trace_projection_dimension`, `OAI.Kadison.TracialGNS.stageCoefficient_crossing`, `OAI.Kadison.TracialGNS.stageCoefficient_cycleCutoff`, `OAI.Kadison.TracialGNS.stageCoefficient_rank_one`, `OAI.Kadison.TracialGNS.stageWord_inner_classification`, `OAI.Kadison.TracialGNS.stage_pairing_expansion`, `OAI.Kadison.TracialGNS.stage_pairing_same_side_zero` and `OAI.Kadison.TracialGNS.word_multiplicity_slices`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C046
import Definitions.Def_OAIQ039C047
import Definitions.Def_OAIQ039C048
import Definitions.Def_OAIQ039C051
import Definitions.Def_OAIQ039C052

section
-- module Solutions.OAIQ039_CM.Commutator_DiffuseHalving
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.PartialIsometryOrder.instCompleteSpaceSubtypeMemSubmoduleComplexFamilySpace _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem diffuse_halving (M : VonNeumannAlgebra H) (hM : FactorCorner.IsFactor M)
    (hd : DiffuseProjection.HasNoMinimalProjections M)
    {e : H →L[ℂ] H} (heM : e∈M) (he : IsStarProjection e) :
    ∃ v : Link M e e, v.val*v.val=0 ∧ v.initial+v.final=e := by
  classical
  obtain ⟨v,hmax⟩ := exists_maximal_squareZero M he
  refine ⟨v.val,v.property,?_⟩
  have hpq := v.val.initial_mul_final_eq_zero v.property
  have hsum : IsStarProjection (v.val.initial+v.val.final) :=
    v.val.initial_projection.add v.val.final_projection hpq
  have hsume : v.val.initial+v.val.final≤e := by
    apply (hsum.le_iff_mul_eq_right he).mpr
    rw [mul_add,(v.val.initial_projection.le_iff_mul_eq_right he).mp v.val.source_le,
      (v.val.final_projection.le_iff_mul_eq_right he).mp v.val.target_le]
  let r := e-(v.val.initial+v.val.final)
  have hr : IsStarProjection r := hsum.sub_of_mul_eq_left he
    ((hsum.le_iff_mul_eq_left he).mp hsume)
  have hrM : r∈M := M.sub_mem heM (M.add_mem
    (M.mul_mem (M.star_mem' v.val.mem) v.val.mem)
    (M.mul_mem v.val.mem (M.star_mem' v.val.mem)))
  by_contra hn
  have hrn : r≠0 := fun hz => hn (sub_eq_zero.mp hz).symm
  obtain ⟨a,haM,ha,han,har,hle⟩ := hd r hrM hr hrn
  have hrr : IsStarProjection (r-a) := ha.sub_of_mul_eq_left hr
    ((ha.le_iff_mul_eq_left hr).mp hle)
  have hrrn : r-a≠0 := fun hz => har (sub_eq_zero.mp hz).symm
  obtain ⟨w,hwM,hwn,hwt,hwi,hwf⟩ := FactorCorner.exists_linking_partialIsometry M hM
    haM (M.sub_mem hrM haM) ha hrr han hrrn
  let w₀ : Link M a (r-a) := ⟨w,hwM,hwt,hwi,hwf⟩
  have hww : w*w=0 := by
    have har0 : a*(r-a)=0 := by
      rw [mul_sub,(ha.le_iff_mul_eq_left hr).mp hle,ha.isIdempotentElem.eq,sub_self]
    calc
      _=(w*a)*((r-a)*w) := by rw [w₀.mul_source ha,w₀.target_mul hrr]
      _=0 := by rw [mul_assoc,←mul_assoc a,har0,zero_mul,mul_zero]
  have hir : star w*w ≤ r := hwi.trans hle
  have hfr : w*star w ≤ r := hwf.trans (sub_le_self r ha.nonneg)
  let wr : Link M r r := ⟨w,hwM,hwt,hir,hfr⟩
  have hie : r≤e-v.val.initial := sub_le_sub_left
    (le_add_of_nonneg_right v.val.final_projection.nonneg) e
  have hfe : r≤e-v.val.final := sub_le_sub_left
    (le_add_of_nonneg_left v.val.initial_projection.nonneg) e
  let w' : Link M (e-v.val.initial) (e-v.val.final) :=
    ⟨w,hwM,hwt,hir.trans hie,hfr.trans hfe⟩
  have hvr : v.val.val*r=0 := by
    change v.val.val*(e-(v.val.initial+v.val.final))=0
    rw [mul_sub,mul_add,v.val.mul_source he,v.val.mul_initial,
      v.val.self_mul_final_eq_zero v.property,add_zero,sub_self]
  have hrv : r*v.val.val=0 := by
    change (e-(v.val.initial+v.val.final))*v.val.val=0
    rw [sub_mul,add_mul,v.val.target_mul he,v.val.initial_mul_self_eq_zero v.property,
      v.val.final_mul,zero_add,sub_self]
  have hvw : v.val.val*w=0 := by
    calc
      _=v.val.val*(r*w) := by rw [wr.target_mul hr]
      _=0 := by rw [←mul_assoc,hvr,zero_mul]
  have hwv : w*v.val.val=0 := by
    calc
      _=(w*r)*v.val.val := by rw [wr.mul_source hr]
      _=0 := by rw [mul_assoc,hrv,mul_zero]
  let u : SquareZeroLink M e := ⟨v.val.extend he he w',by
    change (v.val.val+w)*(v.val.val+w)=0
    rw [add_mul,mul_add,mul_add,v.property,hvw,hwv,hww,zero_add,zero_add]⟩
  have hvu : v≤u := v.val.le_extend he he w'
  have heq : u=v := le_antisymm (hmax hvu) hvu
  have hval := congrArg (fun z : SquareZeroLink M e => z.val.val) heq
  change v.val.val+w=v.val.val at hval
  exact hwn (add_left_cancel (hval.trans (add_zero v.val.val).symm))

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DyadicCuts
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace DyadicCuts

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
    (hd : DiffuseProjection.HasNoMinimalProjections M)

def half (e : ProjectionIn M) : Link M e.val e.val :=
  (diffuse_halving M hfac hd e.mem e.projection).choose

lemma half_square (e : ProjectionIn M) : (half M hfac hd e).val*(half M hfac hd e).val=0 :=
  (diffuse_halving M hfac hd e.mem e.projection).choose_spec.1

lemma half_sum (e : ProjectionIn M) :
    (half M hfac hd e).initial+(half M hfac hd e).final=e.val :=
  (diffuse_halving M hfac hd e.mem e.projection).choose_spec.2

def next (e : ProjectionIn M) : ProjectionIn M :=
  ⟨(half M hfac hd e).initial,
    M.mul_mem (M.star_mem' (half M hfac hd e).mem) (half M hfac hd e).mem,
    (half M hfac hd e).initial_projection⟩

def cut : ℕ → ProjectionIn M
  | 0 => ⟨1,M.one_mem,IsStarProjection.one _⟩
  | n+1 => next M hfac hd (cut n)

def link (n : ℕ) := half M hfac hd (cut M hfac hd n)

def side (n : ℕ) : H →L[ℂ] H := (link M hfac hd n).final

end DyadicCuts

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DyadicPartition
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace BigOperators

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace DyadicPartition

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
  (hd : DiffuseProjection.HasNoMinimalProjections M)

def partition : (n : ℕ) → EqualPartition M (Index n)
  | 0 => EqualPartition.singleton M
  | n+1 =>
    let D := partition n
    let e : ProjectionIn M := ⟨D.base,D.base_mem,D.base_projection⟩
    D.double (DyadicCuts.half M hfac hd e) (DyadicCuts.half_square M hfac hd e)
      (DyadicCuts.half_sum M hfac hd e)

end DyadicPartition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DyadicDimension
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

open Filter

namespace Kadison.PartialIsometryOrder.DyadicPartition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
  (hd : DiffuseProjection.HasNoMinimalProjections M)

def lower (e : H →L[ℂ] H) (n : ℕ) : ℝ :=
  ((partition M hfac hd n).rank e : ℝ)/(2:ℝ)^n

def dimension (e : H →L[ℂ] H) : ℝ := sSup (Set.range (lower M hfac hd e))

end Kadison.PartialIsometryOrder.DyadicPartition

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionJoin
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.ProjectionJoin

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma right_le {p q : H →L[ℂ] H} (hp : IsStarProjection p) (hq : IsStarProjection q) : q≤join p q := by
  apply (hq.le_iff_mul_eq_right (join_projection hp q)).mpr
  have hs : remainder p q*((1-p)*q)=(1-p)*q := Polar.leftSupport_mul _
  have hsp : remainder p q*(1-p)=remainder p q := by
    rw [mul_sub,mul_one,remainder_mul hp q,sub_zero]
  rw [←mul_assoc,hsp] at hs
  change (p+remainder p q)*q=q
  rw [add_mul,hs,sub_mul,one_mul]
  abel

open PartialIsometryOrder PartialIsometryOrder.DyadicPartition

end Kadison.ProjectionJoin

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CountableProjectionJoin
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Kadison.ProjectionJoin

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma le_finiteJoin_succ (P : ℕ → H →L[ℂ] H) (hP : ∀ n,IsStarProjection (P n)) (n : ℕ) :
    P n≤finiteJoin P (n+1) := right_le (finiteJoin_projection P n) (hP n)

open PartialIsometryOrder PartialIsometryOrder.DyadicPartition

end Kadison.ProjectionJoin

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_EndpointGNS
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.TracialGNS

open PreHilbert

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1)

noncomputable def wordConjugation (u : unitary A) (k : ℕ) :
    wordSpace (fullSpace τ) (zeroSpace τ) k →ₗᵢ[ℂ]
      wordSpace (fullSpace τ) (zeroSpace τ) k :=
  wordMap (fullSpace τ) (zeroSpace τ) (conjugation τ hτ u)
    (centeredIsometry (vacuum τ) (conjugation τ hτ u) (conjugation_vacuum τ hτ u)) k

variable {k l : ℕ}

variable (Y : wordSpace (fullSpace τ) (zeroSpace τ) k →L[ℂ]
  wordSpace (fullSpace τ) (zeroSpace τ) l)

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

noncomputable def stageCoefficient (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) :
    MultilinearMap ℂ (fun _ : Option (Fin k ⊕ Fin l) => Matrix I I ℂ) ℂ :=
  coefficientMultilinear (fullSpace τ) (zeroSpace τ) k l Y (vacuum τ)
    (stageVector τ φ) (centeredStageVector τ φ)

end Kadison.TracialGNS
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_EndpointGNS2
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion

namespace Kadison.TracialGNS

open PreHilbert

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1)

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

noncomputable def wordLeft (a : A) (k : ℕ) :
    wordSpace (fullSpace τ) (zeroSpace τ) k →L[ℂ]
      wordSpace (fullSpace τ) (zeroSpace τ) k :=
  HilbertTensor.map (τ.gnsStarAlgHom a) (1 : power (zeroSpace τ) k →L[ℂ] power (zeroSpace τ) k)

end Kadison.TracialGNS
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeActualStructure
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct

open UniformSpace

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments FreeWordAction

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (ht : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

variable (hij : i≠j) (hcolors : ∀ c : ι, c=i ∨ c=j)

variable (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]

variable (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] D)

variable (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)

variable (he : ∀ n m (h : n ≤ m) a, φ m (e h a)=φ n a)

variable (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))

variable (hDgen : ∀ a : D, (factorTrace t f hf).gnsStarAlgHom a ∈
  Set.centralizer (Set.centralizer
    (TracialGNS.stageAlgebra (factorTrace t f hf) I φ : Set _)))

variable (G : t.functional.GNS →L[ℂ] t.functional.GNS)

variable (hGL : ∀ a : D, G.comp (t.functional.gnsStarAlgHom (f a))=
  (t.functional.gnsStarAlgHom (f a)).comp G)

structure WordActions (algebra : Type) [CStarAlgebra algebra] where
  full : PreHilbert
  centered : PreHilbert
  left : algebra → full →L[ℂ] full
  conjugation : unitary algebra → full →ₗᵢ[ℂ] full
  centeredConjugation : unitary algebra → centered →ₗᵢ[ℂ] centered

def tracialWordActions (functional : D →ₚ[ℂ] ℂ)
    (tracial : ∀ first second : D, functional (first * second) =
      functional (second * first)) : WordActions D where
  full := TracialGNS.fullSpace functional
  centered := TracialGNS.zeroSpace functional
  left := functional.gnsStarAlgHom
  conjugation := TracialGNS.conjugation functional tracial
  centeredConjugation unitary := centeredIsometry (TracialGNS.vacuum functional)
    (TracialGNS.conjugation functional tracial unitary)
    (TracialGNS.conjugation_vacuum functional tracial unitary)

abbrev wordLevel (actions : WordActions D) (multiplicity : ℕ → Type*)
    [∀ level, NormedAddCommGroup (multiplicity level)]
    [∀ level, InnerProductSpace ℂ (multiplicity level)] (level : ℕ) :=
  Completion (PreHilbert.wordSpace actions.full actions.centered level ⊗[ℂ] multiplicity level)

abbrev wordLeftAction (actions : WordActions D) (multiplicity : ℕ → Type*)
    [∀ level, NormedAddCommGroup (multiplicity level)]
    [∀ level, InnerProductSpace ℂ (multiplicity level)] (element : D) (level : ℕ) :
    wordLevel actions multiplicity level →L[ℂ] wordLevel actions multiplicity level :=
  HilbertTensor.map (HilbertTensor.map (actions.left element)
    (1 : PreHilbert.power actions.centered level →L[ℂ] PreHilbert.power actions.centered level))
    (1 : multiplicity level →L[ℂ] multiplicity level)

abbrev wordConjugationAction (actions : WordActions D) (multiplicity : ℕ → Type*)
    [∀ level, NormedAddCommGroup (multiplicity level)]
    [∀ level, InnerProductSpace ℂ (multiplicity level)] (unitary : unitary D) (level : ℕ) :
    wordLevel actions multiplicity level →L[ℂ] wordLevel actions multiplicity level :=
  HilbertTensor.map (PreHilbert.wordMap actions.full actions.centered
    (actions.conjugation unitary) (actions.centeredConjugation unitary) level).toContinuousLinearMap
    (1 : multiplicity level →L[ℂ] multiplicity level)

abbrev wordStructure (full centered : PreHilbert)
    (multiplicity : ℕ → Type*) [∀ level, NormedAddCommGroup (multiplicity level)]
    [∀ level, InnerProductSpace ℂ (multiplicity level)]
    [∀ level, CompleteSpace (multiplicity level)]
    (ambient : Type*) [NormedAddCommGroup ambient] [InnerProductSpace ℂ ambient] [CompleteSpace ambient]
    (embedding : ∀ level, Completion
      (PreHilbert.wordSpace full centered level ⊗[ℂ] multiplicity level) →ₗᵢ[ℂ] ambient)
    (operator : ambient →L[ℂ] ambient) : Prop :=
  ∃ coefficient : ∀ level, multiplicity level →L[ℂ] multiplicity level,
    (∀ level, ‖coefficient level‖ ≤ ‖operator‖) ∧
    (∀ level (scalar : full) (letter : centered) (vector : multiplicity level),
      operator (embedding level (HilbertTensor.pair
        (PreHilbert.word full centered level scalar (fun _ => letter)) vector)) =
      embedding level (HilbertTensor.pair
        (PreHilbert.word full centered level scalar (fun _ => letter)) (coefficient level vector))) ∧
    (∀ level (scalar : full) (letter : centered) (vector : multiplicity level),
      operator.adjoint (embedding level (HilbertTensor.pair
        (PreHilbert.word full centered level scalar (fun _ => letter)) vector)) =
      embedding level (HilbertTensor.pair
        (PreHilbert.word full centered level scalar (fun _ => letter))
        ((coefficient level).adjoint vector)))

def wordStructureRule (actions : WordActions D)
    (multiplicity : ℕ → Type*) [∀ level, NormedAddCommGroup (multiplicity level)]
    [∀ level, InnerProductSpace ℂ (multiplicity level)]
    [∀ level, CompleteSpace (multiplicity level)]
    (ambient : Type*) [NormedAddCommGroup ambient] [InnerProductSpace ℂ ambient] [CompleteSpace ambient]
    : Prop :=
  ∀ (embedding : ∀ level, wordLevel actions multiplicity level →ₗᵢ[ℂ] ambient),
    IsHilbertSum ℂ (wordLevel actions multiplicity) embedding →
    ∀ (left : D → ambient →L[ℂ] ambient)
    (symmetries : ∀ stage, unitary (Matrix (I stage) (I stage) ℂ) → ambient →L[ℂ] ambient)
    (operator : ambient →L[ℂ] ambient),
    (∀ element level, (left element).comp (embedding level).toContinuousLinearMap =
      (embedding level).toContinuousLinearMap.comp
        (wordLeftAction actions multiplicity element level)) →
    (∀ stage unitary level,
      (symmetries stage unitary).comp (embedding level).toContinuousLinearMap =
      (embedding level).toContinuousLinearMap.comp
        (wordConjugationAction actions multiplicity
          (TracialGNS.stageUnitary (φ stage) unitary) level)) →
    (∀ element, operator.comp (left element) = (left element).comp operator) →
    (∀ stage unitary, operator.comp (symmetries stage unitary) =
      (symmetries stage unitary).comp operator) →
    wordStructure actions.full actions.centered multiplicity ambient embedding operator

end Kadison.FreeBlocks

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialCommutation
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped ComplexOrder InnerProductSpace

open Complex ContinuousLinearMap UniformSpace Completion

namespace Kadison.TracialGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))

@[simp] lemma operatorConjugate_apply (T : τ.GNS →L[ℂ] τ.GNS) (x : τ.GNS) :
    operatorConjugate τ hτ T x=starMap τ hτ (T (starMap τ hτ x)) := rfl

end Kadison.TracialGNS

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialRightClosure
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped ComplexOrder InnerProductSpace

open Complex ContinuousLinearMap UniformSpace Completion

noncomputable section

namespace Kadison.TracialGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a*b)=τ (b*a))

def rightOperator (T : τ.GNS →L[ℂ] τ.GNS) : τ.GNS →L[ℂ] τ.GNS :=
  operatorConjugate τ hτ (star T)

end Kadison.TracialGNS

end

end
end

end OAI
end


