-- Prove2me | Definitions.Def_Yukon_0e3496485be9a551c983331b
-- name    : Yukon_0e3496485be9a551c983331b
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T05:12:33.40161+00:00
-- url     : https://prove2.me/theorems/bfa6468f-a1c7-4e7e-bee4-52013eb02e49
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.BoundaryTailCounting.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.BoundaryTailCounting.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/BoundaryTailCounting.lean
--
--   yukon-proof-operation:foundation-direct-121003a2c9e9eaec1522cb594a0e2686a7d63e9a537d83b42d2c5c8b62e54c57
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNGJjZDg0OWRlNTIzZjBkYWZhZTBiMGNkNTIxZjE5ZmY1MTBiMTg2Y2E4N2EyZjJjYzc4ZjNmMjBkNTI2ODEzOCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTEyMTAwM2EyYzllOWVhZWMxNTIyY2I1OTRhMGUyNjg2YTdkNjNlOWE1MzdkODNiNDJkMmM1YzhiNjJlNTRjNTciLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8wZTM0OTY0ODViZTlhNTUxYzk4MzMzMWIiLCJ2IjoyfQ]

import Definitions.Def_Yukon_867f9fe91b5fcd4219c71561














































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.BoundaryTailDegreeAwareChain
open scoped Classical BigOperators
open RCN174 RCN319 RCN081 RCN082 RCN167 RCN286 RCN052 RCN260 RCN318 RCN267 RCN313
  RCN135 RCN138 RCN136 RCN238 RCN293 RCN231 RCN243 LocatorDerivativeChain
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K : Type} [Field K]
local instance  _root_.ProximityPrize.SubmissionLower.BoundaryTailDegreeAwareChain.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq _
local instance  _root_.ProximityPrize.SubmissionLower.BoundaryTailDegreeAwareChain.instStrongNormalizationMonoidMvPolynomialFinOfNatNat_proximityPrize : StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
variable {Iota : Type}
local instance  _root_.ProximityPrize.SubmissionLower.BoundaryTailDegreeAwareChain.instDecidableEq_proximityPrize_1 : DecidableEq Iota := Classical.decEq _

/-- Keep the derivative stages and the one tail of each factor correlated. -/
theorem factor_charge_le
    (F : MvPolynomial (Fin 4) K) (selected : K → Polynomial K) (Gamma : Finset K)
    (stage : ℕ → ℕ) (tail unit : ℕ)
    (hstages : ∀ j ∈ Finset.Ico 1 (chainLength F),
      (chainSeeds F j selected Gamma).card ≤ stage j)
    (htail : (tailSeeds F selected Gamma).card ≤ tail)
    (hreceipt : (∑ j ∈ Finset.Ico 1 (F.degreeOf 2), stage j) + tail ≤
      F.degreeOf 2 * unit) :
    (∑ j ∈ Finset.Ico 1 (chainLength F), (chainSeeds F j selected Gamma).card) +
      (tailSeeds F selected Gamma).card ≤ F.degreeOf 2 * unit := by
  have hsub : Finset.Ico 1 (chainLength F) ⊆ Finset.Ico 1 (F.degreeOf 2) := by
    intro j hj
    exact Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hj).1,
      (Finset.mem_Ico.mp hj).2.trans_le (chainLength_le F)⟩
  exact (Nat.add_le_add
    ((Finset.sum_le_sum hstages).trans (Finset.sum_le_sum_of_subset hsub)) htail).trans hreceipt

end
end ProximityPrize.SubmissionLower.BoundaryTailDegreeAwareChain

/-! Shared factor budgets and derivative counts using actual coordinate degrees. -/
namespace ProximityPrize.SubmissionLower.BoundaryTailSharedDegreeBudget
open scoped Classical BigOperators
open RCN238 RCN081 RCN071 RCN167 RCN174 RCN319 RCN052 RCN260 RCN313 LocatorDerivativeChain
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K : Type} [Field K]
local instance  _root_.ProximityPrize.SubmissionLower.BoundaryTailSharedDegreeBudget.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq _

/-- A common factor and the quotient use the same slope budget of the selected polynomial. -/
theorem split_slope_charge {A B : Type*} [DecidableEq A] [DecidableEq B]
    (fs us : Finset A) (bs : Finset B) (hus : us ⊆ fs)
    (f : A → MvPolynomial (Fin 4) K) (g : B → MvPolynomial (Fin 4) K)
    (H Q : MvPolynomial (Fin 4) K) (hH : H ≠ 0) (hQ : Q ≠ 0)
    (hf : (∏ a ∈ fs, f a) ∣ H) (hg : (∏ b ∈ bs, g b) ∣ Q)
    (cap unitU unitRest : ℕ) (hcap : (H * Q).degreeOf 2 ≤ cap)
    (costA : A → ℕ) (costB : B → ℕ)
    (hu : ∀ a ∈ us, costA a ≤ (f a).degreeOf 2 * unitU)
    (ha : ∀ a ∈ fs \ us, costA a ≤ (f a).degreeOf 2 * unitRest)
    (hb : ∀ b ∈ bs, costB b ≤ (g b).degreeOf 2 * unitRest) :
    (∑ a ∈ fs, costA a) + (∑ b ∈ bs, costB b) ≤
      (∑ a ∈ us, (f a).degreeOf 2) * unitU +
        (cap - ∑ a ∈ us, (f a).degreeOf 2) * unitRest := by
  have hdA := sum_degreeOf_le_of_prod_dvd fs f H hH hf (2 : Fin 4)
  have hdB := sum_degreeOf_le_of_prod_dvd bs g Q hQ hg (2 : Fin 4)
  have heq := MvPolynomial.degreeOf_mul_eq (n := (2 : Fin 4)) hH hQ
  have hs := Finset.sum_sdiff hus (f := fun a => (f a).degreeOf 2)
  have hd : (∑ a ∈ fs \ us, (f a).degreeOf 2) + (∑ b ∈ bs, (g b).degreeOf 2) ≤
      cap - ∑ a ∈ us, (f a).degreeOf 2 := by omega
  have hcu := Finset.sum_le_sum hu
  have hca := Finset.sum_le_sum ha
  have hcb := Finset.sum_le_sum hb
  rw [← Finset.sum_mul] at hcu hca hcb
  have hrest := Nat.add_le_add hca hcb
  rw [← Nat.add_mul] at hrest
  have hrest' := hrest.trans (Nat.mul_le_mul_right unitRest hd)
  have hcs := Finset.sum_sdiff hus (f := costA)
  omega

/-- Coordinate degrees suffice for the mixed-degree budget; no ambient box is needed. -/
theorem regularVector_budgets_actual
    (P : UnequalParameters) (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hY : Q.degreeOf 1 ≤ P.leftY) (hR : Q.degreeOf 2 ≤ P.leftR)
    (hZ : Q.degreeOf 3 ≤ P.leftZ) :
    (∑ F : RegularIndex Q, (regularVector P F.1).y) ≤ P.mixedCost.y ∧
    (∑ F : RegularIndex Q, (regularVector P F.1).r) ≤ P.mixedCost.r ∧
    (∑ F : RegularIndex Q, (regularVector P F.1).z) ≤ P.mixedCost.z := by
  have hi (i : Fin 4) : (∑ F : RegularIndex Q, F.1.degreeOf i) ≤ Q.degreeOf i := by
    rw [← Finset.sum_subtype (positiveRFactors Q) (fun _ => Iff.rfl)]
    exact sum_degreeOf_le_of_prod_dvd (positiveRFactors Q) id Q hQ
      (positiveRFactors_product_dvd Q hQ) i
  have hy := (hi 1).trans hY
  have hr := (hi 2).trans hR
  have hz := (hi 3).trans hZ
  simp only [regularVector, Finset.sum_add_distrib]
  constructor
  · rw [← Finset.sum_mul, ← Finset.sum_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_right P.rightZ hr) (Nat.mul_le_mul_right P.rightR hz)
  constructor
  · rw [← Finset.sum_mul, ← Finset.sum_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_right P.rightZ hy) (Nat.mul_le_mul_right P.rightY hz)
  · rw [← Finset.sum_mul, ← Finset.sum_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_right P.rightR hy) (Nat.mul_le_mul_right P.rightY hr)

theorem dR_degree_le (j : ℕ) (F : MvPolynomial (Fin 4) K) (i : Fin 4) :
    (dR j F).degreeOf i ≤ F.degreeOf i := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [dR_succ]
    exact pderiv_degree_bound 2 i (dR j F) (F.degreeOf i) ih

variable {I : Type}
local instance  _root_.ProximityPrize.SubmissionLower.BoundaryTailSharedDegreeBudget.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq _

end
end ProximityPrize.SubmissionLower.BoundaryTailSharedDegreeBudget

/-!
Sharper derivative-chain accounting. The derivative polynomial supplies the
agreement equations, so its own degrees suffice in the agreement numerator.
The right-hand polynomial supplies the geometric intersection only. The Y/Z
caps below apply to the derivative itself and may therefore also use the
weighted degree lost under repeated R differentiation.

The aggregation structure is adapted from the promoted submission and the
actual-degree chain proof from jsign's PR506; the asymmetric numerator and
separate derivative caps are the changes made here.
-/
namespace ProximityPrize.SubmissionLower.BoundaryTailChainHelper
open AsymmetricHelper
open scoped Classical BigOperators
open RCN238 RCN081 RCN071 RCN167 RCN174 RCN319 RCN052 RCN260 RCN313 RCN294
  LocatorDerivativeChain BoundaryTailSharedDegreeBudget
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K I : Type} [Field K]
local instance  _root_.ProximityPrize.SubmissionLower.BoundaryTailChainHelper.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq _
local instance  _root_.ProximityPrize.SubmissionLower.BoundaryTailChainHelper.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq _

theorem sum_regular_counts_bound_left
   (P:UnequalParameters) (Q T:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (hcost:
     (∑ F:RegularIndex Q,(regularVector P F.1).y) ≤ P.mixedCost.y∧
     (∑ F:RegularIndex Q,(regularVector P F.1).r) ≤ P.mixedCost.r∧
     (∑ F:RegularIndex Q,(regularVector P F.1).z) ≤ P.mixedCost.z)
   (hcount:∀ F:RegularIndex Q,
     (regularPairSeeds Q T selected Gamma F).card*P.gap ≤
       (P.n-P.w)*dot P.leftAgreement (regularVector P F.1)+
         (P.errors+1)*P.gap*(regularVector P F.1).z):
   (∑ F:RegularIndex Q,(regularPairSeeds Q T selected Gamma F).card)*
       P.gap ≤ leftRegularNumerator P:=by
 calc
   _=∑ F:RegularIndex Q,
       (regularPairSeeds Q T selected Gamma F).card*P.gap:=by
     rw [Finset.sum_mul]
   _ ≤ ∑ F:RegularIndex Q,
       ((P.n-P.w)*dot P.leftAgreement (regularVector P F.1)+
         (P.errors+1)*P.gap*(regularVector P F.1).z):=
     Finset.sum_le_sum fun F _↦hcount F
   _=(P.n-P.w)*dot P.leftAgreement
         (RCN294.sumVector fun F:RegularIndex Q↦
           regularVector P F.1)+
       (P.errors+1)*P.gap*
         (RCN294.sumVector fun F:RegularIndex Q↦
           regularVector P F.1).z:=by
     rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum,
       ←dot_sum_right]
     simp only [RCN294.sumVector]
   _ ≤ (P.n-P.w)*dot P.leftAgreement P.mixedCost+
       (P.errors+1)*P.gap*P.mixedCost.z:=by
     apply Nat.add_le_add
     · exact Nat.mul_le_mul_left _ (Nat.add_le_add
         (Nat.add_le_add
           (Nat.mul_le_mul_left P.leftAgreement.y hcost.1)
           (Nat.mul_le_mul_left P.leftAgreement.r hcost.2.1))
         (Nat.mul_le_mul_left P.leftAgreement.z hcost.2.2))
     · exact Nat.mul_le_mul_left _ hcost.2.2
   _=leftRegularNumerator P:=rfl

theorem chainSeeds_card_le_left
    (P : UnequalParameters) (F : MvPolynomial (Fin 4) K) (hF : Irreducible F)
    (p : ℕ) [CharP K p] (hpos : 0 < F.degreeOf 2) (hsmall : F.degreeOf 2 < p)
    (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ chainLength F)
    (hgap : 0 < P.gap)
    (hY : (dR j F).degreeOf 1 ≤ P.leftY) (hR : F.degreeOf 2 - j ≤ P.leftR)
    (hZ : (dR j F).degreeOf 3 ≤ P.leftZ)
    (hY' : F.degreeOf 1 ≤ P.rightY) (hR' : F.degreeOf 2 ≤ P.rightR)
    (hZ' : F.degreeOf 3 ≤ P.rightZ)
    (hleftR : 1 ≤ P.leftR)
    (hleftYSmall : P.leftY < p) (hleftRSmall : P.leftR < p) (hleftZSmall : P.leftZ < p)
    (hmixedYSmall : P.mixedCost.y < p) (hmixedRSmall : P.mixedCost.r < p)
    (hmixedZSmall : P.mixedCost.z < p)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset I) (x u0 u1 : I → K) (hinj : Set.InjOn x nodes)
    (hnodes : nodes.card = P.n) (hw : 1 ≤ P.w) (hchar : P.w < p)
    (hwa : P.w < P.a) (han : P.a ≤ P.n)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ P.w)
    (hagreement : ∀ gamma ∈ Gamma, P.a ≤ (nodes.filter (fun i =>
      (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma P.w P.errors) :
    (chainSeeds F j selected Gamma).card ≤ leftRegularCountCap P := by
  have hne := dR_ne_zero F hF.ne_zero p hsmall j hj
  have hrel := isRelPrime_dR F hF p hpos hsmall j hj1 hj
  have hy := hY
  have hr := (dR_R_degree_le j F).trans hR
  have hz := hZ
  have hcount (G : RegularIndex (dR j F)) := regularPairSeeds_bound_left P (dR j F) F hrel G p
    ((degreeOf_le_of_dvd 1 G.1 (dR j F) (positiveRFactors_spec _ _ G.2).2.1 hne).trans hy)
    ((degreeOf_le_of_dvd 2 G.1 (dR j F) (positiveRFactors_spec _ _ G.2).2.1 hne).trans hr)
    ((degreeOf_le_of_dvd 3 G.1 (dR j F) (positiveRFactors_spec _ _ G.2).2.1 hne).trans hz)
    hY' hR' hZ' hleftR hleftYSmall hleftRSmall hleftZSmall
    hmixedYSmall hmixedRSmall hmixedZSmall selected Gamma nodes x u0 u1
    hinj hnodes hw hchar hwa han hdegree hagreement hno
  have hsum := sum_regular_counts_bound_left P (dR j F) F selected Gamma
    (regularVector_budgets_actual P (dR j F) hne hy hr hz) hcount
  have hc : (∑ G : RegularIndex (dR j F),
      (regularPairSeeds (dR j F) F selected Gamma G).card) ≤ leftRegularCountCap P :=
    (Nat.le_div_iff_mul_le hgap).mpr hsum
  exact (Finset.card_le_card (chainSeeds_subset_regularPairSeeds F j hne selected Gamma)).trans
    (Finset.card_biUnion_le.trans hc)

end
end ProximityPrize.SubmissionLower.BoundaryTailChainHelper

/-! Carrier-only chain accounting at error 80811. The polynomial endpoint
argument is adapted from jsign PR506's shared-chain proof. Using the derivative
carrier's agreement degrees replaces its old cross term by the smaller one
proved in `stageNumerator` below. This file alone is not a protocol claim. -/
namespace ProximityPrize.SubmissionLower.AsymmetricChainPolynomial80811
open scoped BigOperators
open RCN238 RCN223 RCN260 RCN313 RCN294 BoundaryTailChainHelper AsymmetricHelper
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

end ProximityPrize.SubmissionLower.AsymmetricChainPolynomial80811

/-! Shared factor-family counting for the proposed error-80811 profile.
The aggregation framework is adapted from jsign PR506. Its AsymmetricChainPolynomial80811.stage count is
replaced by the checked derivative-carrier numerator and polynomial bound.
This module does not assert a protocol claim. -/

namespace ProximityPrize.SubmissionLower.Lower80811.Counting
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN081 RCN100 RCN130 RCN140 RCN156 RCN167 RCN174 RCN234 RCN238
  RCN243 RCN260 RCN267 RCN275 RCN286 RCN294 RCN303 RCN313 RCN318 RCN319
open LocatorDerivativeChain BoundaryTailSharedDegreeBudget AsymmetricChainPolynomial80811 BoundaryTailChainHelper AsymmetricHelper
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K
local instance  _root_.ProximityPrize.SubmissionLower.Lower80811.Counting.instDecidableEqK : DecidableEq K := Classical.decEq _
local instance  _root_.ProximityPrize.SubmissionLower.Lower80811.Counting.instDecidableEqI : DecidableEq I := Classical.decEq _
local instance  _root_.ProximityPrize.SubmissionLower.Lower80811.Counting.instCharPKOfNatNat : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600
local instance  _root_.ProximityPrize.SubmissionLower.Lower80811.Counting.instStrongNormalizationMonoidP4 : StrongNormalizationMonoid P4 := UniqueFactorizationMonoid.strongNormalizationMonoid

variable {u0 u1 : I → K} {selected : K → Polynomial K} {Gamma : Finset K}

end
end ProximityPrize.SubmissionLower.Lower80811.Counting

namespace ProximityPrize.SubmissionLower.Lower80811.Budgets
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN071 RCN081 RCN095 RCN100 RCN130 RCN140 RCN156 RCN167 RCN174 RCN234 RCN238 RCN243 RCN260 RCN266 RCN319
open RCN286 RCN267 RCN180 LocatorBatchProductRoute
open LocatorFactorAggregate LocatorBatchPhase6800 LocatorPhase6800Oracle Counting BoundaryTailSharedDegreeBudget AsymmetricChainPolynomial80811
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
local instance  _root_.ProximityPrize.SubmissionLower.Lower80811.Budgets.instDecidableEqK : DecidableEq K := Classical.decEq _
local instance  _root_.ProximityPrize.SubmissionLower.Lower80811.Budgets.instDecidableEqI : DecidableEq I := Classical.decEq _

end
end ProximityPrize.SubmissionLower.Lower80811.Budgets


