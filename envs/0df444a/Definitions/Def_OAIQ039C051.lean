-- Prove2me | Definitions.Def_OAIQ039C051
-- name    : OAIQ039C051
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:12:43.699254+00:00
-- url     : https://prove2.me/theorems/e7bf3dd7-858d-414b-a3a7-a31ce791b656
-- title:
--   Definitions bundle OAIQ039C051 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 24 declarations of OpenAI's Lean: 10 definitions and 14 theorems. The definitions and types are `OAI.Kadison.PartialIsometryOrder.EqualPartition.double`, `OAI.Kadison.PartialIsometryOrder.EqualPartition.rank`, `OAI.Kadison.PartialIsometryOrder.Equivalent`, `OAI.Kadison.PartialIsometryOrder.Link.adjoint`, `OAI.Kadison.PartialIsometryOrder.Link.compFull`, `OAI.Kadison.PartialIsometryOrder.Link.orthogonalSum`, `OAI.Kadison.PartialIsometryOrder.PartialDecomposition.finitePacking`, `OAI.Kadison.PartialIsometryOrder.SubEquivalent`, `OAI.Kadison.ProjectionJoin.finiteJoin`, `OAI.Kadison.TracialGNS.operatorConjugate`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_CountableProjectionJoin`, `Commutator_DyadicPartition`, `Commutator_MatrixAlgebraEquiv`, `Commutator_PartitionRank`, `Commutator_ProjectionAddition`, `Commutator_ProjectionEquivalence`, `Commutator_ProjectionJoin`, `Commutator_ReplicaPacking`, `Commutator_SquareZeroMaximal`, `Commutator_TracialCommutation`.
--
--   **Imports.** It imports the bundles `OAIQ039C032`, `OAIQ039C033`, `OAIQ039C034`, `OAIQ039C035`, `OAIQ039C039` and `OAIQ039C040` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C057` and `OAIQ039C058`; the statements `OAI.Kadison.PartialIsometryOrder.EqualPartition.card_le_of_part_subEquivalent` and `OAI.Kadison.PartialIsometryOrder.EqualPartition.rank_add_le_card`; the proofs of `OAI.Kadison.HilbertModuleSB.exists_unitary_of_embeddings`, `OAI.Kadison.PartialIsometryOrder.EqualPartition.card_le_of_part_subEquivalent`, `OAI.Kadison.PartialIsometryOrder.EqualPartition.rank_add_le_card` and `OAI.Kadison.PartialIsometryOrder.nonfinite_two_isometries`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C032
import Definitions.Def_OAIQ039C033
import Definitions.Def_OAIQ039C034
import Definitions.Def_OAIQ039C035
import Definitions.Def_OAIQ039C039
import Definitions.Def_OAIQ039C040

section
-- module Solutions.OAIQ039_CM.Commutator_SquareZeroMaximal
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.PartialIsometryOrder.instCompleteSpaceSubtypeMemSubmoduleComplexFamilySpace _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) {e : H →L[ℂ] H} (he : IsStarProjection e)

include he

lemma squareZero_chain_has_upper (c : Set (SquareZeroLink M e)) (hc : IsChain (·≤·) c)
    (hne : c.Nonempty) : BddAbove c := by
  let : Nonempty c := hne.to_subtype
  let : IsDirectedOrder c := hc.directedOn.isDirectedOrder
  let ω : Ultrafilter c := Ultrafilter.of atTop
  have hω : (ω : Filter c)≤atTop := Ultrafilter.of_le atTop
  obtain ⟨W,hnW,hlim⟩ := WeakOperatorLimit.exists_ultralimit ω (fun v : c => v.val.val.val)
    1 zero_le_one (fun v => v.val.val.norm_le_one)
  have hWM : W∈M := WeakOperatorLimit.mem_vonNeumann hlim M
    (Filter.Eventually.of_forall fun v => v.val.val.mem)
  have hWe : W*e=W := by
    have h := WeakOperatorLimit.intertwine hlim e 1 (Filter.Eventually.of_forall
      fun v => by simpa only [one_mul] using v.val.val.mul_source he)
    simpa only [one_mul] using h
  have heW : e*W=W := by
    have h := WeakOperatorLimit.intertwine hlim 1 e (Filter.Eventually.of_forall
      fun v => by simpa only [mul_one] using (v.val.val.target_mul he).symm)
    simpa only [mul_one] using h.symm
  have hWv (v : c) : W*v.val.val.val=0 := by
    have hev : ∀ᶠ w : c in (ω : Filter c), v.val≤w.val :=
      (Filter.eventually_ge_atTop v).filter_mono hω
    apply WeakOperatorLimit.right_eq hlim v.val.val.val 0
    filter_upwards [hev] with w hw
    have hfix := (Link.le_def v.val.val w.val.val).mp hw |>.2
    calc
      _=w.val.val.val*(w.val.val.val*v.val.val.initial) := by rw [hfix]
      _=0 := by rw [←mul_assoc,w.val.property,zero_mul]
  have hWW : W*W=0 := by
    ext x
    apply ext_inner_right ℂ
    intro y
    have hs : ∀ v : c, inner ℂ (v.val.val.val x) (star W y)=0 := by
      intro v
      rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
      simpa only [mul_apply_eq_comp,zero_apply,inner_zero_left] using
        congrArg (fun U : H →L[ℂ] H => inner ℂ (U x) y) (hWv v)
    have hl := hlim x (star W y)
    simp only [hs] at hl
    have h := tendsto_nhds_unique hl tendsto_const_nhds
    simpa only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right,
      mul_apply_eq_comp,zero_apply,inner_zero_left] using h
  let u : Link M e e :=
    { val := Polar.partialIsometry W
      mem := Polar.partialIsometry_mem_vonNeumann M hWM
      triple := Polar.partialIsometry_triple W
      source_le := by rw [Polar.partialIsometry_initial]; exact Polar.rightSupport_le W e he hWe
      target_le := Polar.leftSupport_le W e he heW }
  let u' : SquareZeroLink M e := ⟨u,Polar.partialIsometry_square_zero W hWW⟩
  refine ⟨u',?_⟩
  intro v hv
  have hev : ∀ᶠ w : c in (ω : Filter c), v≤w.val :=
    (Filter.eventually_ge_atTop (⟨v,hv⟩ : c)).filter_mono hω
  have hWext : W*v.val.initial=v.val.val := WeakOperatorLimit.right_eq hlim v.val.initial v.val.val
    (hev.mono fun w hw => (Link.le_def v.val w.val.val).mp hw |>.2)
  have hExt := Polar.partialIsometry_extends hnW v.val.triple hWext
  change v.val≤u
  apply (Link.le_def v.val u).mpr
  constructor
  · change v.val.initial ≤ star (Polar.partialIsometry W)*Polar.partialIsometry W
    rw [Polar.partialIsometry_initial]
    exact hExt.2
  · exact hExt.1

theorem exists_maximal_squareZero : ∃ v : SquareZeroLink M e, IsMax v := by
  let v0 : Link M e e :=
    { val := 0
      mem := M.zero_mem
      triple := by simp
      source_le := by simpa using he.nonneg
      target_le := by simpa using he.nonneg }
  let : Nonempty (SquareZeroLink M e) := ⟨⟨v0,by simp [v0]⟩⟩
  exact zorn_le_nonempty (squareZero_chain_has_upper M he)

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ReplicaPacking
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

open Filter

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace PartialDecomposition

variable {M : VonNeumannAlgebra H} {r : H →L[ℂ] H}

variable (D : PartialDecomposition M r) (R : Replicas M r) (hr : IsStarProjection r)

def finitePacking (f : D.I → ℕ) (s : Finset D.I) : H →L[ℂ] H :=
  ∑ i∈s,R.a (f i)*star (D.v i).val

end PartialDecomposition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionEquivalence
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.PartialIsometryOrder.instCompleteSpaceSubtypeMemSubmoduleComplexFamilySpace _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

def SubEquivalent (M : VonNeumannAlgebra H) (e f : H →L[ℂ] H) : Prop :=
  ∃ v : Link M e f, v.initial=e

def Equivalent (M : VonNeumannAlgebra H) (e f : H →L[ℂ] H) : Prop :=
  ∃ v : Link M e f, v.initial=e ∧ v.final=f

namespace Link

variable {M : VonNeumannAlgebra H} {e f g : H →L[ℂ] H}

def adjoint (v : Link M e f) : Link M f e :=
  ⟨star v.val,M.star_mem' v.mem,by
    simpa only [star_mul,star_star,←mul_assoc] using congrArg star v.triple,
    by simpa only [star_star] using v.target_le,
    by simpa only [star_star] using v.source_le⟩

@[simp] lemma adjoint_initial (v : Link M e f) : v.adjoint.initial=v.final := by
  simp only [initial,final,adjoint,star_star]

@[simp] lemma adjoint_final (v : Link M e f) : v.adjoint.final=v.initial := by
  simp only [initial,final,adjoint,star_star]

def compFull (w : Link M f g) (v : Link M e f)
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (hvi : v.initial=e) (hwi : w.initial=f) : Link M e g := by
  have hi : star (w.val*v.val)*(w.val*v.val)=e := by
    rw [star_mul,mul_assoc,←mul_assoc (star w.val),←Link.initial,hwi,v.target_mul hf,←Link.initial,hvi]
  have ht : (w.val*v.val)*star (w.val*v.val)*(w.val*v.val)=w.val*v.val := by
    rw [mul_assoc,hi,mul_assoc,v.mul_source he]
  have hfin : IsStarProjection ((w.val*v.val)*star (w.val*v.val)) := by
    refine ⟨?_,IsSelfAdjoint.mul_star_self _⟩
    change ((w.val*v.val)*star (w.val*v.val))*((w.val*v.val)*star (w.val*v.val))=_
    rw [←mul_assoc,ht]
  have hle : (w.val*v.val)*star (w.val*v.val)≤w.final := by
    apply (hfin.le_iff_mul_eq_right w.final_projection).mpr
    change (w.val*star w.val)*((w.val*v.val)*star (w.val*v.val))=_
    rw [←mul_assoc,←mul_assoc,w.triple]
  exact ⟨w.val*v.val,M.mul_mem w.mem v.mem,ht,hi.le,hle.trans w.target_le⟩

@[simp] lemma compFull_initial (w : Link M f g) (v : Link M e f)
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (hvi : v.initial=e) (hwi : w.initial=f) :
    (w.compFull v he hf hvi hwi).initial=e := by
  change star (w.val*v.val)*(w.val*v.val)=e
  rw [star_mul,mul_assoc,←mul_assoc (star w.val),←Link.initial,hwi,v.target_mul hf,←Link.initial,hvi]

end Link

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

namespace EqualPartition

variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι]

variable (D : EqualPartition M ι)

attribute [local instance] OAI.Kadison.PartialIsometryOrder.EqualPartition.instDecidableEq_1
def double (w : Link M D.base D.base) (hww : w.val*w.val=0)
    (hsum : w.initial+w.final=D.base) : EqualPartition M (ι × Bool) := by
  classical
  let a := w.initial
  let t : Bool → H →L[ℂ] H := fun b => if b then w.val else a
  have ha : IsStarProjection a := w.initial_projection
  have hti : ∀ b,star (t b)*t b=a := by
    intro b
    cases b <;> simp only [t,Bool.false_eq_true,↓reduceIte,ha.isSelfAdjoint.star_eq,
      ha.isIdempotentElem.eq]
    rfl
  have hts : ∀ b,t b*a=t b := by
    intro b
    cases b
    · exact ha.isIdempotentElem.eq
    · exact w.mul_initial
  have htb : ∀ b,D.base*t b=t b := by
    intro b
    cases b
    · exact (ha.le_iff_mul_eq_right D.base_projection).mp w.source_le
    · exact w.target_mul D.base_projection
  have htc : ∀ b c,b≠c → star (t b)*t c=0 := by
    intro b c hbc
    cases b <;> cases c
    · exact (hbc rfl).elim
    · simpa only [t,Bool.false_eq_true,↓reduceIte,ha.isSelfAdjoint.star_eq] using
        w.initial_mul_self_eq_zero hww
    · simpa only [t,Bool.false_eq_true,↓reduceIte,star_mul,star_zero,←show a=w.initial from rfl,ha.isSelfAdjoint.star_eq,star_star] using
        congrArg star (w.initial_mul_self_eq_zero hww)
    · exact (hbc rfl).elim
  have hsumt : (∑ b : Bool,t b*star (t b))=D.base := by
    simpa only [Fintype.sum_bool,t,Bool.false_eq_true,↓reduceIte,
      ha.isSelfAdjoint.star_eq,ha.isIdempotentElem.eq,add_comm,a,Link.final] using hsum
  refine ⟨a,M.mul_mem (M.star_mem' w.mem) w.mem,ha,
    fun i => D.v i.1*t i.2,?_,?_,?_,?_,?_⟩
  · intro i
    apply M.mul_mem (D.mem i.1)
    cases i.2
    · exact M.mul_mem (M.star_mem' w.mem) w.mem
    · exact w.mem
  · intro i
    rw [star_mul,show star (t i.2)*star (D.v i.1)*(D.v i.1*t i.2)=
      star (t i.2)*(star (D.v i.1)*D.v i.1)*t i.2 by noncomm_ring,
      D.initial,mul_assoc,htb,hti]
  · intro i
    rw [mul_assoc,hts]
  · intro i j hij
    rw [star_mul,show star (t i.2)*star (D.v i.1)*(D.v j.1*t j.2)=
      star (t i.2)*(star (D.v i.1)*D.v j.1)*t j.2 by noncomm_ring]
    by_cases he : i.1=j.1
    · rw [he,D.initial,mul_assoc,htb,htc i.2 j.2 (fun h => hij (Prod.ext he h))]
    · rw [D.cross i.1 j.1 he,mul_zero,zero_mul]
  · rw [Fintype.sum_prod_type]
    simp only [star_mul]
    calc
      _=∑ i,D.v i*(∑ b : Bool,t b*star (t b))*star (D.v i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Finset.mul_sum,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b hb
        noncomm_ring
      _=∑ i,D.v i*star (D.v i) := by simp only [hsumt,D.source]
      _=1 := D.total

end EqualPartition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionAddition
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.PartialIsometryOrder.instCompleteSpaceSubtypeMemSubmoduleComplexFamilySpace _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

namespace Link

variable {M : VonNeumannAlgebra H} {e f e' f' : H →L[ℂ] H}

def orthogonalSum (v : Link M e f) (w : Link M e' f')
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (he' : IsStarProjection e') (hf' : IsStarProjection f')
    (hes : e*e'=0) (hfs : f*f'=0) (hvi : v.initial=e) : Link M (e+e') (f+f') := by
  let b : Link M (e+e') (f+f') :=
    ⟨v.val,v.mem,v.triple,v.source_le.trans (le_add_of_nonneg_right he'.nonneg),
      v.target_le.trans (le_add_of_nonneg_right hf'.nonneg)⟩
  have hbi : b.initial=e := hvi
  let c : Link M ((e+e')-b.initial) ((f+f')-b.final) :=
    ⟨w.val,w.mem,w.triple,by simpa only [hbi,add_sub_cancel_left] using w.source_le,
      w.target_le.trans (by
        apply le_sub_iff_add_le.mpr
        change f' + v.final ≤ f + f'
        have hv : v.final ≤ f := v.target_le
        calc
          f' + v.final = v.final + f' := add_comm _ _
          _ ≤ f+f' := add_le_add hv le_rfl)⟩
  exact b.extend (he.add he' hes) (hf.add hf' hfs) c

end Link

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartitionRank
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

namespace EqualPartition

variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι]

variable (D : EqualPartition M ι)

local instance partitionRankDecidableEq_r920331_1 : DecidableEq ι := Classical.decEq ι
def rank (e : H →L[ℂ] H) : ℕ := by
  classical
  exact Nat.findGreatest (fun k => ∃ s : Finset ι,s.card=k ∧ SubEquivalent M (D.part s) e)
    (Fintype.card ι)

end EqualPartition

end Kadison.PartialIsometryOrder

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

lemma remainder_le {p : H →L[ℂ] H} (hp : IsStarProjection p) (q : H →L[ℂ] H) :
    remainder p q≤1-p := by
  apply Polar.leftSupport_le _ _ hp.one_sub
  rw [←mul_assoc,hp.one_sub.isIdempotentElem.eq]

lemma remainder_mul {p : H →L[ℂ] H} (hp : IsStarProjection p) (q : H →L[ℂ] H) :
    remainder p q*p=0 := by
  have h := ((remainder_projection p q).le_iff_mul_eq_left hp.one_sub).mp (remainder_le hp q)
  rw [mul_sub,mul_one] at h
  exact sub_eq_self.mp h

lemma mul_remainder {p : H →L[ℂ] H} (hp : IsStarProjection p) (q : H →L[ℂ] H) :
    p*remainder p q=0 := by
  simpa only [star_mul,hp.isSelfAdjoint.star_eq,(remainder_projection p q).isSelfAdjoint.star_eq,
    star_zero] using congrArg star (remainder_mul hp q)

lemma join_projection {p : H →L[ℂ] H} (hp : IsStarProjection p) (q : H →L[ℂ] H) :
    IsStarProjection (join p q) := by
  refine ⟨?_,hp.isSelfAdjoint.add (remainder_projection p q).isSelfAdjoint⟩
  change (p+remainder p q)*(p+remainder p q)=p+remainder p q
  rw [add_mul,mul_add,mul_add,hp.isIdempotentElem.eq,(remainder_projection p q).isIdempotentElem.eq,
    mul_remainder hp q,remainder_mul hp q,add_zero,zero_add]

lemma join_le {p q r : H →L[ℂ] H} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hr : IsStarProjection r) (hpr : p ≤ r) (hqr : q ≤ r) : join p q ≤ r := by
  have hrp := (hp.le_iff_mul_eq_right hr).mp hpr
  have hrq := (hq.le_iff_mul_eq_right hr).mp hqr
  have hs : remainder p q ≤ r := by
    apply Polar.leftSupport_le _ _ hr
    rw [←mul_assoc,mul_sub,mul_one,hrp,sub_mul,hrq,sub_mul,one_mul]
  apply ((join_projection hp q).le_iff_mul_eq_right hr).mpr
  change r*(p+remainder p q)=p+remainder p q
  rw [mul_add,hrp,((remainder_projection p q).le_iff_mul_eq_right hr).mp hs]

lemma join_mem (M : VonNeumannAlgebra H) {p q : H →L[ℂ] H} (hp : p∈M) (hq : q∈M) :
    join p q∈M := M.add_mem hp (remainder_mem M hp hq)

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

def finiteJoin (P : ℕ → H →L[ℂ] H) : ℕ → H →L[ℂ] H
  | 0 => 0
  | n+1 => join (finiteJoin P n) (P n)

lemma finiteJoin_projection (P : ℕ → H →L[ℂ] H) (n : ℕ) : IsStarProjection (finiteJoin P n) := by
  induction n with
  | zero => exact IsStarProjection.zero _
  | succ n ih => exact join_projection ih _

lemma finiteJoin_le (P : ℕ → H →L[ℂ] H) (hP : ∀ n,IsStarProjection (P n))
    {Q : H →L[ℂ] H} (hQ : IsStarProjection Q) (hle : ∀ n,P n≤Q) (n : ℕ) : finiteJoin P n≤Q := by
  induction n with
  | zero => exact hQ.nonneg
  | succ n ih => exact join_le (finiteJoin_projection P n) (hP n) hQ ih (hle n)

open PartialIsometryOrder PartialIsometryOrder.DyadicPartition

end Kadison.ProjectionJoin

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixAlgebraEquiv
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

attribute [local instance] OAI.Kadison.OperatorAmplification.instDecidableEq_solutions
lemma entry_matrixRepresentation (X : CStarMatrix ι ι M) (i j : ι) :
    entry ι (CyclicColumns.matrixRepresentation (A:=M) (H:=H) M.toStarSubalgebra.subtype X) i j=
      (X i j:H →L[ℂ] H) := by
  ext x
  simp only [entry_apply,CyclicColumns.matrixRepresentation,CyclicColumns.matrixAction_apply,
    StarAlgHom.coe_mk]
  simp [apply_ite]
  rfl

end Kadison.OperatorAmplification

end

end
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

noncomputable def operatorConjugate (T : τ.GNS →L[ℂ] τ.GNS) : τ.GNS →L[ℂ] τ.GNS :=
  (starMap τ hτ).comp (T.comp (starMap τ hτ))

end Kadison.TracialGNS

end
end

end OAI
end


