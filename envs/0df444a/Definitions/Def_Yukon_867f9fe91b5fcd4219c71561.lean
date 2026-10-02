-- Prove2me | Definitions.Def_Yukon_867f9fe91b5fcd4219c71561
-- name    : Yukon_867f9fe91b5fcd4219c71561
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T04:43:38.591785+00:00
-- url     : https://prove2.me/theorems/4df6a276-054e-4155-8134-e1775888d6de
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.LowerGeometry.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.LowerGeometry.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerGeometry.lean
--
--   yukon-proof-operation:foundation-direct-ca19df5d69fd5651409254ab62c1dcdfa8bbe3de78ef4ca8caae8669eb4e0f1c
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiODUzNGEwMTcyNDE4MDgyMTdjYzliZWUzNGY4ODM1MjBhZTI4OTdlOGEzNTBmZWU1NTg3ZmFlZDFiMDc5NDhlNiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWNhMTlkZjVkNjlmZDU2NTE0MDkyNTRhYjYyYzFkY2RmYThiYmUzZGU3OGVmNGNhOGNhYWU4NjY5ZWI0ZTBmMWMiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl84NjdmOWZlOTFiNWZjZDQyMTljNzE1NjEiLCJ2IjoyfQ]

import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_07bb1fdf83fc478e7c5449e7
import Definitions.Def_Yukon_755f5ab5e1dfa660f8e11f09














































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Compact lower-bound proof; prior work is credited in the enclosed components. -/

-- Mathlib's linters run interpreted after every declaration; they only warn.
set_option linter.all false

section Compact_PackedLocatorTail
/-! Packed: amortised derivative-chain caps. -/
section PackedLocator_ChainAmort

/-!
# Amortised chain caps

The derivative chain over an irreducible factor `F` of `R`-degree `d` charges its
level `j` to the coprime pair `(d_R^j F, F)`, whose LEFT `R`-degree is at most
`d - j` (`dR_R_degree_le`); the RIGHT factor is `F` itself and does not descend.
With a monotone level cap, `capSum cap d` is superadditive, so a family of factors
whose `R`-degrees sum to at most `s` costs at most `capSum cap s`.

Each factor also carries ONE slope-free tail, and there is one further global
`R`-free tail.  Charging the chain at its `k = 1` maximum and the tails at their
`k = s` maximum double-counts: with `tail <= cap 1` the augmented allowance
`capSumT cap tail d = capSum cap d + tail` is still superadditive, so chains and
tails together cost `capSum cap s + tail`, and the global tail brings the total to
`capSum cap s + 2 * tail` in place of `capSum cap s + (s+1) * tail`.
-/

open Finset

namespace ChainAmort

end ChainAmort

namespace ChainAmort

end ChainAmort

namespace ChainAmort

end ChainAmort

namespace ChainGroupMaj
open ProximityPrize.SubmissionLower.RCN260 ProximityPrize.SubmissionLower.RCN294

end ChainGroupMaj

end PackedLocator_ChainAmort

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrierChainAmort : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorNestedProjection. -/
section PackedLocator_LocatorNestedProjection
namespace ProximityPrize.SubmissionLower.LocatorLowQuotient
open scoped BigOperators
open RCN081 RCN156 RCN180 RCN234
noncomputable section
variable {K:Type*} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.LocatorLowQuotient.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
def nestedExponents (D w T YS S:ℕ):Set (Fin 4 →₀ ℕ) :=
  {d | d 1 + d 2 + d 3 ≤ T ∧ d 1 + d 2 ≤ YS ∧ d 2 ≤ S ∧
    d 0 + w * d 1 + (w - 1) * d 2 < D}
def nestedCoefficientBox (K:Type*) [Field K] (D w T YS S:ℕ) :
    Submodule K (MvPolynomial (Fin 4) K) :=
  MvPolynomial.restrictSupport K (nestedExponents D w T YS S)

/-- The PR #437 kernel-cheap range sum. -/
def kernelSumRange (f : ℕ → ℕ) : ℕ → ℕ := KernelEval.sumRange f

theorem kernelSumRange_succ (f : ℕ → ℕ) (n : ℕ) :
    kernelSumRange f (n + 1) = kernelSumRange f n + f n := by
  exact KernelEval.sumRange_succ f n

theorem kernelSumRange_eq (f : ℕ → ℕ) (n : ℕ) :
    kernelSumRange f n = ∑ i ∈ Finset.range n, f i := by
  exact KernelEval.sumRange_eq f n

theorem finset_sum_range_sub (a m : ℕ) (h : m ≤ a) :
    ∑ r ∈ Finset.range (m + 1), (a - r) =
      (m + 1) * a - (m + 1) * m / 2 := by
  exact KernelEval.sum_range_sub a m h

def channelCount (T YS S:ℕ):ℕ :=
  kernelSumRange (fun y =>
    let M := min S (min (T - y) (YS - y))
    (M + 1) * (T + 1 - y) - (M + 1) * M / 2) (min T YS + 1)

theorem channelCount_eq (T YS S : ℕ) :
    channelCount T YS S =
      ∑ y ∈ Finset.range (min T YS + 1),
        ∑ r ∈ Finset.range (min S (min (T - y) (YS - y)) + 1),
          (T + 1 - y - r) := by
  rw [channelCount, kernelSumRange_eq]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  let M := min S (min (T - y) (YS - y))
  have hM : M ≤ T + 1 - y := by
    have hMT : M ≤ T - y := by
      exact (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
    omega
  simpa [M] using (finset_sum_range_sub (T + 1 - y) M hM).symm
abbrev HighBandIndex (delta T YS S:ℕ) :=
  (y:Fin (min T YS + 1)) ×
    (r:Fin (min S (min (T - y.val) (YS - y.val)) + 1)) ×
      (Fin (T + 1 - y.val - r.val) × Fin delta)
theorem highBandIndex_card (delta T YS S:ℕ) :
    Fintype.card (HighBandIndex delta T YS S) = delta * channelCount T YS S:=by
  rw [channelCount_eq]
  simp [HighBandIndex, Fintype.card_sigma,
    Finset.sum_range, Finset.mul_sum, Nat.mul_comm]
def highBandExponent (w Dlow:ℕ) {delta T YS S:ℕ}
    (c:HighBandIndex delta T YS S):Fin 4 →₀ ℕ :=
  Finsupp.single 0 (Dlow - w * c.1.val - (w - 1) * c.2.1.val + c.2.2.2.val) +
    Finsupp.single 1 c.1.val + Finsupp.single 2 c.2.1.val +
      Finsupp.single 3 c.2.2.1.val
def highBandMap (w Dlow delta T YS S:ℕ) :
    MvPolynomial (Fin 4) K →ₗ[K] (HighBandIndex delta T YS S → K) :=
  LinearMap.pi (fun c => MvPolynomial.lcoeff K (highBandExponent w Dlow c))
@[simp] theorem highBandMap_apply (w Dlow delta T YS S:ℕ)
    (P:MvPolynomial (Fin 4) K) (c:HighBandIndex delta T YS S) :
    highBandMap w Dlow delta T YS S P c =
      MvPolynomial.coeff (highBandExponent w Dlow c) P:=rfl
theorem nested_mem_global {D w T YS S:ℕ} {P:MvPolynomial (Fin 4) K}
    (hP:P ∈ nestedCoefficientBox K D w T YS S) :
    P ∈ RCN100.globalCoefficientBox K D w T S:=by
  intro d hd
  have h:=hP hd
  exact ⟨h.1, h.2.2.1, h.2.2.2⟩
theorem nested_mem_weights {D w T YS S:ℕ} {P:MvPolynomial (Fin 4) K}
    (hP:P ∈ nestedCoefficientBox K D w T YS S) (hne:P ≠ 0) :
    wt residualTotalWeights P ≤ T ∧ wt residualYSWeights P ≤ YS ∧
      wt residualSWeights P ≤ S ∧ wt (contactWeights w) P < D:=by
  have hD:0 < D:=by
    obtain ⟨d, hd⟩:=MvPolynomial.support_nonempty.mpr hne
    have h:=(hP hd).2.2.2
    omega
  have h:=(mem_flagGlobalCoefficientBox_iff P D w T S hD).mp
    (nested_mem_global hP)
  refine ⟨h.1, ?_, h.2.1, by omega⟩
  apply (weightedTotalDegree_le_iff residualYSWeights P YS).mpr
  intro d hd
  have hdYS:=(hP hd).2.1
  rw [weight_fin4]
  simpa [residualYSWeights] using hdYS
theorem flag_box_ys_bound (D w L s YS:ℕ) (hw:1 ≤ w)
    (hshape:D + s ≤ w * (YS + 1)) (P:MvPolynomial (Fin 4) K)
    (hP:P ∈ RCN100.globalCoefficientBox K D w L s) :
    wt residualYSWeights P ≤ YS:=by
  apply (weightedTotalDegree_le_iff residualYSWeights P YS).mpr
  intro d hd
  have hs:=(hP hd).2.1
  have hc:=(hP hd).2.2
  have hwr:w * d 2 = (w - 1) * d 2 + d 2:=by
    calc
      w * d 2 = ((w - 1) + 1) * d 2:=by rw [Nat.sub_add_cancel hw]
      _ = (w - 1) * d 2 + d 2:=by ring
  have hm:w * (d 1 + d 2) < w * (YS + 1):=by
    rw [Nat.mul_add, hwr]
    omega
  have hlt:d 1 + d 2 < YS + 1 :=
    (Nat.mul_lt_mul_left (by omega:0 < w)).mp hm
  rw [weight_fin4]
  simpa [residualYSWeights] using (Nat.le_of_lt_succ hlt)
section LinearSelection
variable {V:Type*} [AddCommGroup V] [Module K V]
end LinearSelection
end
end ProximityPrize.SubmissionLower.LocatorLowQuotient
end PackedLocator_LocatorNestedProjection

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier01 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorContact. -/
section PackedLocator_LocatorContact
namespace ProximityPrize.SubmissionLower.LocatorContact
open scoped BigOperators
open RCN081 RCN100 RCN119 RCN122 RCN156 RCN180 RCN234 RCN313 ContactOrderBridge
noncomputable section
variable {K I:Type*} [Field K] [Fintype I]
local instance _root_.ProximityPrize.SubmissionLower.LocatorContact.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq _
local instance _root_.ProximityPrize.SubmissionLower.LocatorContact.instDecidableEq_proximityPrize_1 :DecidableEq I:=Classical.decEq _
abbrev P4 (K:Type*) [Field K]:=MvPolynomial (Fin 4) K
theorem pderiv_R_weight_add_le (weights:Fin 4 → ℕ) (Q:P4 K)
    (hder:MvPolynomial.pderiv (2:Fin 4) Q ≠ 0) :
    wt weights (MvPolynomial.pderiv (2:Fin 4) Q) + weights 2 ≤ wt weights Q:=by
  classical
  obtain ⟨d, hd, heq⟩:=Finset.exists_mem_eq_sup
    (MvPolynomial.pderiv (2:Fin 4) Q).support
    (MvPolynomial.support_nonempty.mpr hder) (Finsupp.weight weights)
  have hbefore:=support_before_pderiv (2:Fin 4) Q d hd
  have hbound:=MvPolynomial.le_weightedTotalDegree weights hbefore
  change wt weights (MvPolynomial.pderiv (2:Fin 4) Q) =
    Finsupp.weight weights d at heq
  rw [heq]
  simpa only [wt, map_add, Finsupp.weight_single, one_nsmul] using hbound
end
end ProximityPrize.SubmissionLower.LocatorContact
end PackedLocator_LocatorContact

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier02 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorLowQuotient. -/
section PackedLocator_LocatorLowQuotient
namespace ProximityPrize.SubmissionLower.LocatorLowQuotient
open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 600000
variable {K I:Type*} [Field K] [Fintype I]
local instance _root_.ProximityPrize.SubmissionLower.LocatorLowQuotient.instDecidableEq_proximityPrize_1 :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.LocatorLowQuotient.instDecidableEq_proximityPrize_2 :DecidableEq I:=Classical.decEq I
theorem quotient_box_of_full_divisor
    (D w L s m c t r:ℕ) (nodes u0 u1:I → K)
    (F:MvPolynomial (Fin 4) K) (hF:F ≠ 0)
    (hdiv:∀ v:ConstraintKernel (K:=K) D w L s m nodes u0 u1,
      F ∣ kernelReconstructLinear (K:=K) D w L s m nodes u0 u1 v)
    (hc:c ≤ wt (contactWeights w) F)
    (ht:t ≤ wt residualTotalWeights F) (hr:r ≤ wt residualSWeights F) :
    ∀ v:ConstraintKernel (K:=K) D w L s m nodes u0 u1,
      quotientPolynomial (kernelReconstructLinear (K:=K) D w L s m nodes u0 u1)
        F hdiv v ∈ globalCoefficientBox K (D - c) w (L - t) (s - r):=by
  let recon:=kernelReconstructLinear (K:=K) D w L s m nodes u0 u1
  intro v
  by_cases hv:v = 0
  · subst v
    have hz:quotientPolynomial recon F hdiv 0 = 0 :=
      (quotientLinear recon F hF hdiv).map_zero
    rw [hz]
    exact (globalCoefficientBox K _ _ _ _).zero_mem
  · have hQ:recon v ≠ 0:=by
      intro hz
      apply hv
      apply kernelReconstructLinear_injective (K:=K) D w L s m nodes u0 u1
      simpa only [map_zero] using hz
    have heq:=recon_eq_mul_quotientPolynomial recon F hdiv v
    have hq:quotientPolynomial recon F hdiv v ≠ 0:=by
      intro hz
      exact hQ (by rw [heq, hz, mul_zero])
    have hReconBox:recon v ∈ globalCoefficientBox K D w L s:=by
      change reconstruct K D w L s v.1 ∈ globalCoefficientBox K D w L s
      exact reconstruct_mem_globalCoefficientBox K D w L s v.1
    exact quotient_mem_flagGlobalCoefficientBox_of_mul_eq
      (recon v) F (quotientPolynomial recon F hdiv v)
      D w L s c t r hQ hF hq hReconBox heq hc ht hr
end
end ProximityPrize.SubmissionLower.LocatorLowQuotient
end PackedLocator_LocatorLowQuotient

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier03 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorFifthPowerAvoidance. -/
section PackedLocator_LocatorFifthPowerAvoidance

namespace ProximityPrize.SubmissionLower.LocatorCoprimeQuotient
open scoped Classical BigOperators
open UniqueFactorizationMonoid RCN081 RCN156 RCN234 RCN260
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
variable {K I:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.LocatorCoprimeQuotient.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.LocatorCoprimeQuotient.instDecidableEq_proximityPrize_1 :DecidableEq I:=Classical.decEq I
local instance _root_.ProximityPrize.SubmissionLower.LocatorCoprimeQuotient.instStrongNormalizationMonoidMvPolynomialFinOfNatNat_proximityPrize :StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
public theorem regular_mem_normalizedFactors
    (H:MvPolynomial (Fin 4) K) (F:RCN266.RegularIndex H) :
    F.1 ∈ normalizedFactors H:=by
  have hactive:F.1 ∈ RCN082.activeFactors H :=
    (Finset.mem_filter.mp F.2).1
  have hnf:F.1 ∈ (normalizedFactors H).toFinset :=
    (Finset.mem_filter.mp hactive).1
  exact Multiset.mem_toFinset.mp hnf
def regularIndexSelf (H:MvPolynomial (Fin 4) K)
    (F:RCN266.RegularIndex H):RCN052.RegularIndex F.1:=by
  have hF:=RCN167.positiveRFactors_spec H F.1 F.2
  refine ⟨F.1, ?_⟩
  change F.1 ∈ (RCN082.activeFactors F.1).filter (fun G => 0 < G.degreeOf 2)
  refine Finset.mem_filter.mpr ⟨?_, hF.2.2⟩
  change F.1 ∈ (normalizedFactors F.1).toFinset.filter
    (fun G => 0 < G.degreeOf 1 + G.degreeOf 2 + G.degreeOf 3)
  refine Finset.mem_filter.mpr ⟨?_, by omega⟩
  apply Multiset.mem_toFinset.mpr
  rw [normalizedFactors_irreducible hF.1,
    normalize_normalized_factor F.1 (regular_mem_normalizedFactors H F)]
  exact Multiset.mem_singleton_self _
@[simp] theorem regularIndexSelf_val (H:MvPolynomial (Fin 4) K)
    (F:RCN266.RegularIndex H):(regularIndexSelf H F).1 = F.1:=rfl
theorem regularVector_le_mixedCost (P:UnequalParameters)
    (F:MvPolynomial (Fin 4) K)
    (hY:F.degreeOf 1 ≤ P.leftY) (hR:F.degreeOf 2 ≤ P.leftR)
    (hZ:F.degreeOf 3 ≤ P.leftZ) :
    (RCN052.regularVector P F).y ≤ P.mixedCost.y ∧
      (RCN052.regularVector P F).r ≤ P.mixedCost.r ∧
      (RCN052.regularVector P F).z ≤ P.mixedCost.z:=by
  exact ⟨Nat.add_le_add (Nat.mul_le_mul_right P.rightZ hR)
      (Nat.mul_le_mul_right P.rightR hZ),
    Nat.add_le_add (Nat.mul_le_mul_right P.rightZ hY)
      (Nat.mul_le_mul_right P.rightY hZ),
    Nat.add_le_add (Nat.mul_le_mul_right P.rightR hY)
      (Nat.mul_le_mul_right P.rightY hR)⟩
end
end ProximityPrize.SubmissionLower.LocatorCoprimeQuotient

namespace ProximityPrize.SubmissionLower.LocatorDoubleSquareAvoidance

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 400000

variable {K V I : Type*} [Field K]
local instance  _root_.ProximityPrize.SubmissionLower.LocatorDoubleSquareAvoidance.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K

theorem quotient_mem_nestedCoefficientBox_of_mul_eq
    (P F Q : MvPolynomial (Fin 4) K) (D w T YS S : ℕ)
    (hP : P ≠ 0) (hF : F ≠ 0) (hQ : Q ≠ 0)
    (hbox : P ∈ nestedCoefficientBox K D w T YS S)
    (heq : P = F * Q) :
    Q ∈ nestedCoefficientBox K
      (D - wt (contactWeights w) F) w
      (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
      (S - wt residualSWeights F) := by
  have hglobal :
      Q ∈ globalCoefficientBox K
        (D - wt (contactWeights w) F) w
        (T - wt residualTotalWeights F) (S - wt residualSWeights F) :=
    quotient_mem_flagGlobalCoefficientBox_of_mul_eq P F Q D w T S
      (wt (contactWeights w) F) (wt residualTotalWeights F)
      (wt residualSWeights F) hP hF hQ (nested_mem_global hbox) heq
      le_rfl le_rfl le_rfl
  have hPYS : wt residualYSWeights P ≤ YS :=
    (nested_mem_weights hbox hP).2.1
  have hmul := weightedTotalDegree_mul residualYSWeights F Q hF hQ
  have hsum : wt residualYSWeights F + wt residualYSWeights Q ≤ YS := by
    change MvPolynomial.weightedTotalDegree residualYSWeights F +
      MvPolynomial.weightedTotalDegree residualYSWeights Q ≤ YS
    rw [← hmul, ← heq]
    exact hPYS
  have hQYS : wt residualYSWeights Q ≤ YS - wt residualYSWeights F := by
    omega
  intro d hd
  have hb := hglobal hd
  have hy := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at hy
  simp only [wt] at hQYS
  simp only [residualYSWeights] at hy ⊢
  refine ⟨hb.1, ?_, hb.2.1, hb.2.2⟩
  change d 1 + d 2 ≤ YS -
    MvPolynomial.weightedTotalDegree residualYSWeights F
  simpa [residualYSWeights] using hy.trans hQYS

section LinearDichotomy

variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

end LinearDichotomy

section SecondDerivative

variable [Fintype I]
local instance  _root_.ProximityPrize.SubmissionLower.LocatorDoubleSquareAvoidance.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I

end SecondDerivative

end

end ProximityPrize.SubmissionLower.LocatorDoubleSquareAvoidance

namespace ProximityPrize.SubmissionLower.LocatorTripleCubeAvoidance

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient
open LocatorDoubleSquareAvoidance

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 800000

variable {K V I : Type*} [Field K]
local instance  _root_.ProximityPrize.SubmissionLower.LocatorTripleCubeAvoidance.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K

section LinearDichotomy

variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

end LinearDichotomy

section ThirdDerivative

variable [Fintype I]
local instance  _root_.ProximityPrize.SubmissionLower.LocatorTripleCubeAvoidance.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I

end ThirdDerivative

end

end ProximityPrize.SubmissionLower.LocatorTripleCubeAvoidance

namespace ProximityPrize.SubmissionLower.LocatorFourthPowerAvoidance

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient
open LocatorDoubleSquareAvoidance LocatorTripleCubeAvoidance

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

variable {K V I : Type*} [Field K]
local instance  _root_.ProximityPrize.SubmissionLower.LocatorFourthPowerAvoidance.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K

section LinearDichotomy

variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

end LinearDichotomy

section FourthDerivative

variable [Fintype I]
local instance  _root_.ProximityPrize.SubmissionLower.LocatorFourthPowerAvoidance.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I

end FourthDerivative

end

end ProximityPrize.SubmissionLower.LocatorFourthPowerAvoidance

namespace ProximityPrize.SubmissionLower.LocatorFifthPowerAvoidance

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient
open LocatorDoubleSquareAvoidance LocatorTripleCubeAvoidance
open LocatorFourthPowerAvoidance

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

variable {K V I : Type*} [Field K]
local instance  _root_.ProximityPrize.SubmissionLower.LocatorFifthPowerAvoidance.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K

section LinearDichotomy

variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

end LinearDichotomy

section FifthDerivative

variable [Fintype I]
local instance  _root_.ProximityPrize.SubmissionLower.LocatorFifthPowerAvoidance.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I

end FifthDerivative

end

end ProximityPrize.SubmissionLower.LocatorFifthPowerAvoidance
end PackedLocator_LocatorFifthPowerAvoidance

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier04 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorQuotientMonotone. -/
section PackedLocator_LocatorQuotientMonotone
namespace ProximityPrize.SubmissionLower.LocatorLowQuotient
open scoped BigOperators
theorem channelCount_mono {T T' YS YS' S S':ℕ}
    (ht:T ≤ T') (hy:YS ≤ YS') (hs:S ≤ S') :
    channelCount T YS S ≤ channelCount T' YS' S':=by
  rw [channelCount_eq, channelCount_eq]
  calc
    _ ≤ ∑ y ∈ Finset.range (min T YS + 1),
        ∑ r ∈ Finset.range (min S' (min (T' - y) (YS' - y)) + 1),
          (T' + 1 - y - r):=by
      apply Finset.sum_le_sum
      intro y _
      have hin:Finset.range (min S (min (T-y) (YS-y)) + 1) ⊆
          Finset.range (min S' (min (T'-y) (YS'-y)) + 1):=by
        apply Finset.range_mono
        have h:=min_le_min hs
          (min_le_min (Nat.sub_le_sub_right ht y) (Nat.sub_le_sub_right hy y))
        omega
      exact (Finset.sum_le_sum (fun r _ => by omega)).trans
        (Finset.sum_le_sum_of_subset_of_nonneg hin (fun _ _ _ => Nat.zero_le _))
    _ ≤ _:=by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono (Nat.add_le_add_right (min_le_min ht hy) 1)
      · intro _ _ _
        exact Nat.zero_le _
end ProximityPrize.SubmissionLower.LocatorLowQuotient
end PackedLocator_LocatorQuotientMonotone

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier05 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorArbitraryPowerAvoidance. -/
section PackedLocator_LocatorArbitraryPowerAvoidance

/-!
# Arbitrarily many successive locator quotient projections

This is the recursive form of the explicitly unrolled second-through-ninth
power-avoidance lemmas.  It deliberately concerns only the linear high-band
selection.  Contact-order vanishing and extraction of the terminal quotient
from an iterated derivative are independent consumers of the witness returned
here.
-/

namespace ProximityPrize.SubmissionLower.LocatorArbitraryPowerAvoidance

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient
  LocatorDoubleSquareAvoidance

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

variable {K V : Type*} [Field K]
local instance  _root_.ProximityPrize.SubmissionLower.LocatorArbitraryPowerAvoidance.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K

/-- The exact cumulative cost of `k` successive high-band projections.
The decrement form is chosen so that removing the first projection is
definitionally the same budget at the shifted quotient box. -/
def powerBandBudget
    (delta dT dY dS T YS S : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
      delta * channelCount T YS S +
        powerBandBudget delta dT dY dS
          (T - dT) (YS - dY) (S - dS) k

/-- Enlarging the current box and decreasing its per-stage losses can only
increase the cumulative high-band budget. -/
theorem powerBandBudget_mono
    (delta dT₁ dY₁ dS₁ T₁ Y₁ S₁ dT₂ dY₂ dS₂ T₂ Y₂ S₂ k : ℕ)
    (hT : T₁ ≤ T₂) (hY : Y₁ ≤ Y₂) (hS : S₁ ≤ S₂)
    (hdT : dT₂ ≤ dT₁) (hdY : dY₂ ≤ dY₁)
    (hdS : dS₂ ≤ dS₁) :
    powerBandBudget delta dT₁ dY₁ dS₁ T₁ Y₁ S₁ k ≤
      powerBandBudget delta dT₂ dY₂ dS₂ T₂ Y₂ S₂ k := by
  induction k generalizing T₁ Y₁ S₁ T₂ Y₂ S₂ with
  | zero =>
      simp only [powerBandBudget]
      exact Nat.zero_le _
  | succ k ih =>
      simp only [powerBandBudget]
      apply Nat.add_le_add
      · exact Nat.mul_le_mul_left delta (channelCount_mono hT hY hS)
      · apply ih
        · omega
        · omega
        · omega

/-! ## Contact-thinned band (lever S1)

The band map reads coefficients at `highBandExponent w Dlow c`, `c : HighBandIndex`.  Every
monomial of the `Dhigh` box has `w * d1 + (w-1) * d2 ≤ Dhigh - 1` and `d2 ≤ S`, hence
`d1 + d2 ≤ (Dhigh + S - 1) / w`: index rows above that cut carry no monomial of the box, so
the band map built on the cut index set keeps its kernel inside the `Dlow` box, and its
rank bound is `delta * channelCount` of the cut caps.  The contact cap drops by
`delta + wt_c F` per level, so the cut sharpens with the depth. -/

/-- Largest `d 1 + d 2` a monomial of the `Dhigh` box (slope cap `S`) can have. -/
def thinTop (w Dhigh S : ℕ) : ℕ := (Dhigh + S - 1) / w

theorem thinTop_mono {w D D' S S' : ℕ} (hD : D ≤ D') (hS : S ≤ S') :
    thinTop w D S ≤ thinTop w D' S' :=
  Nat.div_le_div_right (by omega)

theorem ys_le_thinTop (Dhigh w T YS S : ℕ) (hw : 1 ≤ w) (d : Fin 4 →₀ ℕ)
    (hd : d ∈ nestedExponents Dhigh w T YS S) :
    d 1 + d 2 ≤ thinTop w Dhigh S := by
  rcases hd with ⟨_, _, hS, hD⟩
  have hwr : w * d 2 = (w - 1) * d 2 + d 2 := by
    calc
      w * d 2 = ((w - 1) + 1) * d 2 := by rw [Nat.sub_add_cancel hw]
      _ = (w - 1) * d 2 + d 2 := by ring
  have hmul : (d 1 + d 2) * w ≤ Dhigh + S - 1 := by
    rw [Nat.mul_comm, Nat.mul_add, hwr]
    omega
  exact (Nat.le_div_iff_mul_le (by omega)).mpr hmul

/-- `mem_low_of_highBandMap_eq_zero` for the band map built on the cut index set. -/
theorem mem_low_of_highBandMap_cut_eq_zero
    (Dhigh Dlow w delta T YS S : ℕ) (hw : 1 ≤ w)
    (hwidth : Dhigh ≤ Dlow + delta) (P : MvPolynomial (Fin 4) K)
    (hP : P ∈ nestedCoefficientBox K Dhigh w T YS S)
    (hzero : highBandMap w Dlow delta T (min YS (thinTop w Dhigh S)) S P = 0) :
    P ∈ nestedCoefficientBox K Dlow w T YS S := by
  intro d hd
  rcases hP hd with ⟨hT, hYS, hS, hD⟩
  have htop := ys_le_thinTop Dhigh w T YS S hw d ⟨hT, hYS, hS, hD⟩
  refine ⟨hT, hYS, hS, ?_⟩
  by_contra hnot
  have hy : d 1 < min T (min YS (thinTop w Dhigh S)) + 1 := by omega
  have hr : d 2 < min S (min (T - d 1) (min YS (thinTop w Dhigh S) - d 1)) + 1 := by
    omega
  have hz : d 3 < T + 1 - d 1 - d 2 := by omega
  have hstart : Dlow - w * d 1 - (w - 1) * d 2 ≤ d 0 := by omega
  have hx : d 0 - (Dlow - w * d 1 - (w - 1) * d 2) < delta := by omega
  let c : HighBandIndex delta T (min YS (thinTop w Dhigh S)) S :=
    ⟨⟨d 1, hy⟩, ⟨⟨d 2, hr⟩,
      ⟨⟨d 3, hz⟩, ⟨d 0 - (Dlow - w * d 1 - (w - 1) * d 2), hx⟩⟩⟩⟩
  have he : highBandExponent w Dlow c = d := by
    ext i
    fin_cases i <;> simp [highBandExponent, c] <;> omega
  have hc := congrFun hzero c
  have hcoeff : MvPolynomial.coeff d P = 0 := by
    simpa only [highBandMap_apply, he, Pi.zero_apply] using hc
  exact (MvPolynomial.mem_support_iff.mp hd) hcoeff

/-- The cell-side lower bound on the contact weight: the monomial attaining the
`YS` weight has slope exponent at most `wt_S F`. -/
theorem contact_ge_ys (w : ℕ) (hw : 1 ≤ w) (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0) :
    w * wt residualYSWeights F - wt residualSWeights F ≤
      wt (contactWeights w) F := by
  obtain ⟨d, hd, hsup⟩ := Finset.exists_mem_eq_sup F.support
    (MvPolynomial.support_nonempty.mpr hF) (Finsupp.weight residualYSWeights)
  have hys : wt residualYSWeights F = d 1 + d 2 := by
    change MvPolynomial.weightedTotalDegree residualYSWeights F = d 1 + d 2
    rw [MvPolynomial.weightedTotalDegree, hsup, weight_fin4]
    simp [residualYSWeights]
  have hs : d 2 ≤ wt residualSWeights F := by
    have h := MvPolynomial.le_weightedTotalDegree residualSWeights hd
    rw [weight_fin4] at h
    change d 0 * 0 + d 1 * 0 + d 2 * 1 + d 3 * 0 ≤ wt residualSWeights F at h
    omega
  have hc : d 0 + w * d 1 + (w - 1) * d 2 ≤ wt (contactWeights w) F := by
    have h := MvPolynomial.le_weightedTotalDegree (contactWeights w) hd
    rw [contact_weight] at h
    exact h
  have hwr : w * d 2 = (w - 1) * d 2 + d 2 := by
    calc
      w * d 2 = ((w - 1) + 1) * d 2 := by rw [Nat.sub_add_cancel hw]
      _ = (w - 1) * d 2 + d 2 := by ring
  rw [hys, Nat.mul_add, hwr]
  omega

/-- The contact-aware budget: level `k+1` charges the cut band at contact cap `Dh` and
recurses with the cap lowered by `delta + dc` (`dc` a lower bound on `wt_c F`). -/
def powerBandBudgetThin
    (w Dh delta dc dT dY dS T YS S : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
      delta * channelCount T (min YS (thinTop w Dh S)) S +
        powerBandBudgetThin w (Dh - delta - dc) delta dc dT dY dS
          (T - dT) (YS - dY) (S - dS) k

theorem powerBandBudgetThin_le (w delta dc dT dY dS : ℕ) :
    ∀ (k Dh T YS S : ℕ),
      powerBandBudgetThin w Dh delta dc dT dY dS T YS S k ≤
        powerBandBudget delta dT dY dS T YS S k := by
  intro k
  induction k with
  | zero => intro _ _ _ _; simp [powerBandBudgetThin, powerBandBudget]
  | succ k ih =>
      intro Dh T YS S
      simp only [powerBandBudgetThin, powerBandBudget]
      exact Nat.add_le_add
        (Nat.mul_le_mul_left delta
          (channelCount_mono le_rfl (Nat.min_le_left _ _) le_rfl))
        (ih _ _ _ _)

/-- Monotone: a larger cap, a smaller contact decrement, a larger box and smaller
per-stage losses can only increase the thin budget. -/
theorem powerBandBudgetThin_mono (w delta : ℕ) :
    ∀ (k Dh₁ dc₁ dT₁ dY₁ dS₁ T₁ Y₁ S₁ Dh₂ dc₂ dT₂ dY₂ dS₂ T₂ Y₂ S₂ : ℕ),
      Dh₁ ≤ Dh₂ → dc₂ ≤ dc₁ → T₁ ≤ T₂ → Y₁ ≤ Y₂ → S₁ ≤ S₂ →
      dT₂ ≤ dT₁ → dY₂ ≤ dY₁ → dS₂ ≤ dS₁ →
      powerBandBudgetThin w Dh₁ delta dc₁ dT₁ dY₁ dS₁ T₁ Y₁ S₁ k ≤
        powerBandBudgetThin w Dh₂ delta dc₂ dT₂ dY₂ dS₂ T₂ Y₂ S₂ k := by
  intro k
  induction k with
  | zero =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      simp [powerBandBudgetThin]
  | succ k ih =>
      intro Dh₁ dc₁ dT₁ dY₁ dS₁ T₁ Y₁ S₁ Dh₂ dc₂ dT₂ dY₂ dS₂ T₂ Y₂ S₂
        hD hdc hT hY hS hdT hdY hdS
      simp only [powerBandBudgetThin]
      apply Nat.add_le_add
      · exact Nat.mul_le_mul_left delta
          (channelCount_mono hT (min_le_min hY (thinTop_mono hD hS)) hS)
      · apply ih
        · omega
        · exact hdc
        · omega
        · omega
        · omega
        · exact hdT
        · exact hdY
        · exact hdS

theorem powerBandBudgetThin_le_succ
    (w Dh delta dc dT dY dS T YS S k : ℕ) :
    powerBandBudgetThin w Dh delta dc dT dY dS T YS S k ≤
      powerBandBudgetThin w Dh delta dc dT dY dS T YS S (k + 1) := by
  induction k generalizing Dh T YS S with
  | zero =>
      simp only [powerBandBudgetThin]
      exact Nat.zero_le _
  | succ k ih =>
      simp only [powerBandBudgetThin]
      exact Nat.add_le_add_left (ih _ _ _ _) _

theorem powerBandBudgetThin_mono_fuel
    (w Dh delta dc dT dY dS T YS S : ℕ) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) :
    powerBandBudgetThin w Dh delta dc dT dY dS T YS S k₁ ≤
      powerBandBudgetThin w Dh delta dc dT dY dS T YS S k₂ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction d with
  | zero => simp
  | succ d ih =>
      calc
        powerBandBudgetThin w Dh delta dc dT dY dS T YS S k₁ ≤
            powerBandBudgetThin w Dh delta dc dT dY dS T YS S (k₁ + d) :=
          ih (Nat.le_add_right _ _)
        _ ≤ powerBandBudgetThin w Dh delta dc dT dY dS T YS S ((k₁ + d) + 1) :=
          powerBandBudgetThin_le_succ w Dh delta dc dT dY dS T YS S (k₁ + d)
        _ = powerBandBudgetThin w Dh delta dc dT dY dS T YS S (k₁ + d.succ) := by
          congr 1

end

end ProximityPrize.SubmissionLower.LocatorArbitraryPowerAvoidance
end PackedLocator_LocatorArbitraryPowerAvoidance

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier06 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorArbitraryPowerContact. -/
section PackedLocator_LocatorArbitraryPowerContact

/-!
# Arbitrary-order locator contact and power extraction

This module is the order-independent consumer for
`LocatorArbitraryPowerAvoidance`.  It replaces the explicitly unrolled
second-through-tenth derivative arguments by three reusable facts:

* an `R`-derivative lowers contact order by at most one;
* a nonzero `j`-fold `R`-derivative loses at least `j` times the `R` weight;
* at derivative order `j`, the surviving term of `dR^[j] (F^j * Q)` is
  `j! * Q * (dR F)^j` after specializing on `F = 0`.
-/

namespace ProximityPrize.SubmissionLower.LocatorArbitraryPowerContact

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

variable {K I : Type*} [Field K]
local instance  _root_.ProximityPrize.SubmissionLower.LocatorArbitraryPowerContact.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K

abbrev P4 (K : Type*) [Field K] := MvPolynomial (Fin 4) K

/-- The `j`-fold derivative in the received-coordinate variable. -/
def iteratePderivR (j : ℕ) (Q : P4 K) : P4 K :=
  (fun H : P4 K => MvPolynomial.pderiv (2 : Fin 4) H)^[j] Q

@[simp] theorem iteratePderivR_zero (Q : P4 K) :
    iteratePderivR 0 Q = Q := rfl

theorem iteratePderivR_succ (j : ℕ) (Q : P4 K) :
    iteratePderivR (j + 1) Q =
      MvPolynomial.pderiv (2 : Fin 4) (iteratePderivR j Q) := by
  simp only [iteratePderivR, Function.iterate_succ_apply']

@[simp] theorem iteratePderivR_zero_poly (j : ℕ) :
    iteratePderivR (K := K) j 0 = 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [iteratePderivR_succ, ih, map_zero]

/-- Contact order falls by at most one at every received-coordinate
derivative, uniformly in the number of iterations. -/
theorem contactAtLeast_iteratePderivR
    (x u0 u1 : K) (m j : ℕ) (Q : P4 K)
    (hQ : ContactOrderBridge.ContactAtLeast K x u0 u1 m Q) :
    ContactOrderBridge.ContactAtLeast K x u0 u1 (m - j)
      (iteratePderivR j Q) := by
  induction j with
  | zero => simpa only [iteratePderivR_zero, Nat.sub_zero] using hQ
  | succ j ih =>
      rw [iteratePderivR_succ]
      have hnext := ContactOrderBridge.contactAtLeast_pderiv_R
        K x u0 u1 (m - j) (iteratePderivR j Q) ih
      simpa only [Nat.sub_sub] using hnext

/-- If a successor iterate is nonzero, its immediate predecessor is nonzero. -/
theorem iteratePderivR_ne_zero_of_succ
    (Q : P4 K) (j : ℕ)
    (hne : iteratePderivR (j + 1) Q ≠ 0) :
    iteratePderivR j Q ≠ 0 := by
  intro hz
  apply hne
  rw [iteratePderivR_succ, hz, map_zero]

/-- A nonzero `j`-fold received-coordinate derivative pays `j` copies of
the received-coordinate weight.  This is the generic replacement for all
manually chained `pderiv_R_weight_add_le` calculations. -/
theorem iteratePderivR_weight_add_le
    (weights : Fin 4 → ℕ) (Q : P4 K) (j : ℕ)
    (hne : iteratePderivR j Q ≠ 0) :
    wt weights (iteratePderivR j Q) + j * weights 2 ≤ wt weights Q := by
  induction j with
  | zero =>
      simp only [iteratePderivR_zero, Nat.zero_mul, Nat.add_zero]
      exact le_rfl
  | succ j ih =>
      have hprev : iteratePderivR j Q ≠ 0 :=
        iteratePderivR_ne_zero_of_succ Q j (by
          simpa only [Nat.succ_eq_add_one] using hne)
      have hstepNe :
          MvPolynomial.pderiv (2 : Fin 4) (iteratePderivR j Q) ≠ 0 := by
        simpa only [Nat.succ_eq_add_one, iteratePderivR_succ] using hne
      have hstep := LocatorContact.pderiv_R_weight_add_le
        weights (iteratePderivR j Q) hstepNe
      calc
        wt weights (iteratePderivR (Nat.succ j) Q) +
              Nat.succ j * weights 2 =
            (wt weights (MvPolynomial.pderiv (2 : Fin 4)
              (iteratePderivR j Q)) + weights 2) + j * weights 2 := by
              simp only [Nat.succ_eq_add_one, iteratePderivR_succ,
                Nat.add_mul, one_mul]
              ac_rfl
        _ ≤ wt weights (iteratePderivR j Q) + j * weights 2 :=
          Nat.add_le_add_right hstep _
        _ ≤ wt weights Q := ih hprev

theorem iteratePderivR_weight_le_sub
    (weights : Fin 4 → ℕ) (Q : P4 K) (j d : ℕ)
    (hne : iteratePderivR j Q ≠ 0)
    (hQ : wt weights Q ≤ d) :
    wt weights (iteratePderivR j Q) ≤ d - j * weights 2 := by
  exact Nat.le_sub_of_add_le
    ((iteratePderivR_weight_add_le weights Q j hne).trans hQ)

section KernelVanishing

variable [Fintype I]
local instance  _root_.ProximityPrize.SubmissionLower.LocatorArbitraryPowerContact.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I

/-- The generic contact/degree vanishing theorem at derivative order `j`.
The capacity hypothesis is exactly the one used by each previously unrolled
fixed-order theorem. -/
theorem specialization_iteratePderivR_eq_zero_of_kernel_low_box
    (j D Dlow w L s m : ℕ) (nodes : I ↪ K) (u0 u1 : I → K)
    (v : ConstraintKernel (K := K) D w L s m nodes u0 u1)
    (hlow : reconstruct K D w L s v.1 ∈
      globalCoefficientBox K Dlow w L s)
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hj : 1 ≤ j) (hw : 1 ≤ w) (hP : P.natDegree ≤ w)
    (hcapacity : Dlow ≤ (m - j) * support.card + j * (w - 1))
    (hvalues : ∀ i ∈ support,
      P.eval (nodes i) = u0 i + gamma * u1 i) :
    RCN319.specialization K P gamma
      (iteratePderivR j (reconstruct K D w L s v.1)) = 0 := by
  classical
  cases j with
  | zero => omega
  | succ k =>
      let H := reconstruct K D w L s v.1
      by_contra hne
      have hfinal : iteratePderivR (Nat.succ k) H ≠ 0 := by
        intro hz
        apply hne
        rw [hz, map_zero]
      have hprev : iteratePderivR k H ≠ 0 := by
        apply iteratePderivR_ne_zero_of_succ H k
        simpa only [Nat.succ_eq_add_one] using hfinal
      have hH : H ≠ 0 := by
        intro hz
        apply hfinal
        rw [hz, iteratePderivR_zero_poly]
      have hDlow : 0 < Dlow := by
        obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hH
        have h := (hlow hd).2.2
        omega
      have hHweight : wt (contactWeights w) H ≤ Dlow - 1 :=
        ((mem_flagGlobalCoefficientBox_iff H Dlow w L s hDlow).mp hlow).2.2
      have hprevWeight :
          wt (contactWeights w) (iteratePderivR k H) ≤
            Dlow - 1 - k * (w - 1) := by
        have hbound := iteratePderivR_weight_le_sub
          (contactWeights w) H k (Dlow - 1) hprev hHweight
        change wt (contactWeights w) (iteratePderivR k H) ≤
          Dlow - 1 - k * (w - 1) at hbound
        exact hbound
      have hregular : RCN319.specialization K P gamma
          (MvPolynomial.pderiv (2 : Fin 4) (iteratePderivR k H)) ≠ 0 := by
        simpa only [Nat.succ_eq_add_one, iteratePderivR_succ] using hne
      have hdegree := ContactOrderBridge.specialized_R_derivative_degree K
        (iteratePderivR k H) P gamma w
        (Dlow - 1 - k * (w - 1)) hP hprevWeight hregular
      have hdegreeStrict :
          (RCN122.specialization K P gamma
            (iteratePderivR (Nat.succ k) H)).natDegree <
              (m - Nat.succ k) * support.card := by
        rw [Nat.succ_eq_add_one, iteratePderivR_succ]
        rw [RCN101.specialization_eq_ordinary]
        rw [RCN101.specialization_eq_ordinary] at hdegree
        have hkc : k * (w - 1) ≤ Dlow - 1 := by
          by_contra hnot
          have hlt : Dlow - 1 < k * (w - 1) := Nat.lt_of_not_ge hnot
          have hzero : Dlow - 1 - k * (w - 1) = 0 :=
            Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)
          rw [hzero] at hdegree
          have hwOne : w - 1 = 0 := by omega
          rw [hwOne, Nat.mul_zero] at hlt
          omega
        have hsplit :
            (Dlow - 1 - k * (w - 1)) + k * (w - 1) = Dlow - 1 :=
          Nat.sub_add_cancel hkc
        have hwSplit : w - 1 + 1 = w := Nat.sub_add_cancel hw
        simp only [Nat.succ_eq_add_one, Nat.add_mul, one_mul] at hcapacity
        omega
      have hcontact : ∀ i ∈ support, ∀ r : ℕ,
          slopeDifference K ^ (m - Nat.succ k - r) ∣
            (RCN122.homogenizedTranslation K (nodes i) (u0 i) (u1 i)
              (iteratePderivR (Nat.succ k) H)).coeff r := by
        intro i _hi
        apply (ContactOrderBridge.contactAtLeast_iff_block_divisibility
          K (nodes i) (u0 i) (u1 i) (m - Nat.succ k) _).mp
        exact contactAtLeast_iteratePderivR
          (nodes i) (u0 i) (u1 i) m (Nat.succ k) H
          (ContactOrderBridge.contactAtLeast_of_mem_kernel
            K D w L s m nodes u0 u1 v.1 v.2 i)
      have hz := RCN122.specialization_eq_zero_of_contact_and_degree K
        (iteratePderivR (Nat.succ k) H) P gamma nodes u0 u1 support
        (m - Nat.succ k) hcontact hvalues hdegreeStrict
      apply hne
      simpa only [H, RCN101.specialization_eq_ordinary] using hz

end KernelVanishing

/-- Local factorial divisibility criterion, kept here because `CH`'s
corresponding helper is intentionally private. -/
public theorem prime_dvd_factorial_local : ∀ {n p : ℕ},
    p.Prime → (p ∣ n.factorial ↔ p ≤ n)
  | 0, _, hp => iff_of_false hp.not_dvd_one (not_le_of_gt hp.pos)
  | n + 1, p, hp => by
      rw [Nat.factorial_succ, hp.dvd_mul, prime_dvd_factorial_local hp]
      exact ⟨fun h => h.elim (Nat.le_of_dvd (Nat.succ_pos _)) Nat.le_succ_of_le,
        fun h => (_root_.lt_or_eq_of_le h).elim
          (Or.inr ∘ Nat.le_of_lt_succ) fun h => Or.inl <| by rw [h]⟩

/-- A prime characteristic larger than `j` does not annihilate `j!`. -/
theorem factorial_ne_zero_of_lt_char
    (p j : ℕ) [CharP K p] (hp : p.Prime) (hj : j < p) :
    (j.factorial : K) ≠ 0 := by
  intro hz
  have hdvd : p ∣ j.factorial :=
    (CharP.cast_eq_zero_iff K p j.factorial).mp hz
  exact (not_le_of_gt hj) ((prime_dvd_factorial_local hp).mp hdvd)

/-- Generic extraction of the terminal quotient from a `j`th derivative.
After specializing on `F = 0`, `RCN324.iterate_pow_mul_expansion` kills its
error term and leaves `j! * Q * (dR F)^j`. -/
theorem specialization_eq_zero_of_iteratePderivR_power_product
    (j : ℕ) (P : Polynomial K) (gamma : K) (F Q : P4 K)
    (hfactorial : (j.factorial : K) ≠ 0)
    (hFzero : RCN319.specialization K P gamma F = 0)
    (hregular : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hpower : RCN319.specialization K P gamma
      (iteratePderivR j (F ^ j * Q)) = 0) :
    RCN319.specialization K P gamma Q = 0 := by
  obtain ⟨error, herror⟩ := RCN324.iterate_pow_mul_expansion
    (MvPolynomial.pderiv (2 : Fin 4)) F Q j j le_rfl
  have hexpansion :
      iteratePderivR j (F ^ j * Q) =
        (j.descFactorial j : P4 K) * F ^ (j - j) * Q *
            (MvPolynomial.pderiv (2 : Fin 4) F) ^ j +
          F ^ (j - j + 1) * error := by
    simpa only [iteratePderivR] using herror
  rw [hexpansion] at hpower
  have hmul :
      (j.factorial : Polynomial K) *
          RCN319.specialization K P gamma Q *
            (RCN319.specialization K P gamma
              (MvPolynomial.pderiv (2 : Fin 4) F)) ^ j = 0 := by
    simpa only [Nat.descFactorial_self, Nat.sub_self, pow_zero, one_mul, mul_one,
      zero_add, pow_one, map_add, map_mul, map_pow, map_natCast,
      map_one, hFzero, zero_mul, add_zero] using hpower
  have hfactorialPoly : (j.factorial : Polynomial K) ≠ 0 := by
    intro hz
    apply hfactorial
    have heval := congrArg (Polynomial.eval 0) hz
    simpa using heval
  have hcoef :
      (j.factorial : Polynomial K) *
          (RCN319.specialization K P gamma
            (MvPolynomial.pderiv (2 : Fin 4) F)) ^ j ≠ 0 :=
    mul_ne_zero hfactorialPoly (pow_ne_zero j hregular)
  have hmul' :
      ((j.factorial : Polynomial K) *
          (RCN319.specialization K P gamma
            (MvPolynomial.pderiv (2 : Fin 4) F)) ^ j) *
        RCN319.specialization K P gamma Q = 0 := by
    calc
      _ = (j.factorial : Polynomial K) *
          RCN319.specialization K P gamma Q *
            (RCN319.specialization K P gamma
              (MvPolynomial.pderiv (2 : Fin 4) F)) ^ j := by ring
      _ = 0 := hmul
  exact (mul_eq_zero.mp hmul').resolve_left hcoef

end

end ProximityPrize.SubmissionLower.LocatorArbitraryPowerContact
end PackedLocator_LocatorArbitraryPowerContact

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier07 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorTwoFactorAvoidance. -/
section PackedLocator_LocatorTwoFactorAvoidance

/-!
# A shared high-band route for two regular factors

The one-factor power route pays for a high-band projection independently for
every regular factor.  For two factors the projection can be shared.  On the
resulting low subspace there are only four cases: neither divisibility
condition is universal, exactly one is universal, or both are universal.  In
the first case one vector avoids both divisors; in a one-universal case the
other factor is finished and the universal factor continues through the
one-factor route; in the both-universal case the product is divided out and
the shared route continues.

This file contains the linear-algebraic core.  It intentionally returns
weight bounds rather than coefficient-box membership: those are precisely
the data consumed by the derivative and unequal-pair arguments, and they are
stable when the other factor is multiplied back into a recursively produced
helper.
-/

namespace ProximityPrize.SubmissionLower.LocatorTwoFactorAvoidance

open scoped BigOperators
open UniqueFactorizationMonoid
open RCN081 RCN100 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient
  LocatorDoubleSquareAvoidance LocatorArbitraryPowerAvoidance
  LocatorArbitraryPowerContact

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

variable {K V : Type} [Field K]
local instance  _root_.ProximityPrize.SubmissionLower.LocatorTwoFactorAvoidance.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.LocatorTwoFactorAvoidance.instStrongNormalizationMonoidMvPolynomialFinOfNatNat_proximityPrize : StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

abbrev P4 (K : Type*) [Field K] := MvPolynomial (Fin 4) K

public theorem regular_mem_normalizedFactors
    (H : P4 K) (F : RCN266.RegularIndex H) :
    F.1 ∈ normalizedFactors H := by
  have hactive : F.1 ∈ RCN082.activeFactors H :=
    (Finset.mem_filter.mp F.2).1
  have hnf : F.1 ∈ (normalizedFactors H).toFinset :=
    (Finset.mem_filter.mp hactive).1
  exact Multiset.mem_toFinset.mp hnf

/-- Distinct regular indices are represented by distinct normalized prime
factors, hence are relatively prime. -/
theorem regularIndex_isRelPrime_of_ne
    (H : P4 K) (F G : RCN266.RegularIndex H) (hne : F.1 ≠ G.1) :
    IsRelPrime F.1 G.1 := by
  have hFs := RCN167.positiveRFactors_spec H F.1 F.2
  have hGs := RCN167.positiveRFactors_spec H G.1 G.2
  apply hFs.1.isRelPrime_iff_not_dvd.mpr
  intro hd
  apply hne
  apply UniqueFactorizationMonoid.mem_normalizedFactors_eq_of_associated
    (regular_mem_normalizedFactors H F) (regular_mem_normalizedFactors H G)
  exact (hFs.1.dvd_irreducible_iff_associated hGs.1).mp hd

/-- Dividing an injective nested-box family by a universal divisor preserves
injectivity and subtracts the four factor weights. -/
theorem quotientLinear_nested_data
    [AddCommGroup V] [Module K V]
    (D w T YS S : ℕ) (q : V →ₗ[K] P4 K)
    (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K D w T YS S)
    (F : P4 K) (hF : F ≠ 0) (hdiv : ∀ v, F ∣ q v) :
    Function.Injective (quotientLinear q F hF hdiv) ∧
      (∀ v, q v = F * quotientLinear q F hF hdiv v) ∧
      ∀ v, quotientLinear q F hF hdiv v ∈ nestedCoefficientBox K
        (D - wt (contactWeights w) F) w
        (T - wt residualTotalWeights F)
        (YS - wt residualYSWeights F)
        (S - wt residualSWeights F) := by
  classical
  let qF := quotientLinear q F hF hdiv
  have hqF : Function.Injective qF :=
    quotientLinear_injective q hq F hF hdiv
  have hprod (v : V) : q v = F * qF v :=
    recon_eq_mul_quotientPolynomial q F hdiv v
  refine ⟨hqF, hprod, ?_⟩
  intro v
  by_cases hv : v = 0
  · subst v
    rw [map_zero]
    exact (nestedCoefficientBox K _ _ _ _ _).zero_mem
  · have hqv : q v ≠ 0 := by
      intro hz
      apply hv
      apply hq
      simpa only [map_zero] using hz
    have hqFv : qF v ≠ 0 := by
      intro hz
      apply hqv
      rw [hprod v, hz, mul_zero]
    exact quotient_mem_nestedCoefficientBox_of_mul_eq
      (q v) F (qF v) D w T YS S hqv hF hqFv (hmem v) (hprod v)

/-- Exact weighted degree of a nonzero power. -/
theorem wt_pow_eq (weights : Fin 4 → ℕ) (F : P4 K) (hF : F ≠ 0)
    (j : ℕ) : wt weights (F ^ j) = j * wt weights F := by
  unfold wt
  induction j with
  | zero => simp [pow_zero, MvPolynomial.weightedTotalDegree]
  | succ j ih =>
      rw [pow_succ', weightedTotalDegree_mul weights F (F ^ j) hF
        (pow_ne_zero j hF), ih]
      simp only [Nat.succ_eq_add_one, Nat.add_mul, one_mul]
      omega

end

end ProximityPrize.SubmissionLower.LocatorTwoFactorAvoidance
end PackedLocator_LocatorTwoFactorAvoidance

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier08 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorFactorAggregate. -/
section PackedLocator_LocatorFactorAggregate
namespace ProximityPrize.SubmissionLower.LocatorFactorAggregate
open scoped BigOperators
open RCN095
set_option maxRecDepth 2048
set_option maxHeartbeats 300000
def middle (p:FlagDegree):ℕ:=p.yz + p.all
def total (p:FlagDegree):ℕ:=p.zOnly + p.yz + p.all
def Below (p q:FlagDegree):Prop :=
  p.all ≤ q.all ∧ middle p ≤ middle q ∧ total p ≤ total q
theorem mixed_expansion (p q r:FlagDegree) :
    flagMixed p q r =
      (q.all * r.all + q.yz * r.all + q.all * r.yz) * total p +
      (q.zOnly * r.all + q.all * r.zOnly) * middle p +
      (q.yz * r.yz + q.zOnly * r.yz + q.yz * r.zOnly) * p.all:=by
  simp only [flagMixed, middle, total]
  ring
theorem mixed_mono_first {p P:FlagDegree} (h:Below p P) (q r:FlagDegree) :
    flagMixed p q r ≤ flagMixed P q r:=by
  rw [mixed_expansion p q r, mixed_expansion P q r]
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left _ h.2.2) (Nat.mul_le_mul_left _ h.2.1))
    (Nat.mul_le_mul_left _ h.1)
theorem mixed_mono_second (p:FlagDegree) {q Q:FlagDegree}
    (h:Below q Q) (r:FlagDegree):flagMixed p q r ≤ flagMixed p Q r:=by
  calc
    flagMixed p q r = flagMixed q p r:=by unfold flagMixed; ring
    _ ≤ flagMixed Q p r:=mixed_mono_first h p r
    _ = flagMixed p Q r:=by unfold flagMixed; ring
theorem mixed_mono_third (p q:FlagDegree) {r R:FlagDegree}
    (h:Below r R):flagMixed p q r ≤ flagMixed p q R:=by
  calc
    flagMixed p q r = flagMixed r q p:=by unfold flagMixed; ring
    _ ≤ flagMixed R q p:=mixed_mono_first h q p
    _ = flagMixed p q R:=by unfold flagMixed; ring
theorem mixed_mono_tails (p:FlagDegree) {q Q r R:FlagDegree}
    (hq:Below q Q) (hr:Below r R):flagMixed p q r ≤ flagMixed p Q R :=
  (mixed_mono_second p hq r).trans (mixed_mono_third p Q hr)
theorem sum_mixed_le {I:Type*} [Fintype I]
    (p:I → FlagDegree) (P q r:FlagDegree)
    (hs:(∑ i, (p i).all) ≤ P.all)
    (hy:(∑ i, middle (p i)) ≤ middle P)
    (ht:(∑ i, total (p i)) ≤ total P) :
    (∑ i, flagMixed (p i) q r) ≤ flagMixed P q r:=by
  rw [Finset.sum_congr rfl (fun i _ => mixed_expansion (p i) q r),
    mixed_expansion P q r]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left _ ht) (Nat.mul_le_mul_left _ hy))
    (Nat.mul_le_mul_left _ hs)
def padS (p:FlagDegree):ℕ:=max p.all 2
def padY (p:FlagDegree):ℕ:=max (middle p) (padS p + 1)
def padT (p:FlagDegree):ℕ:=max (total p) (padY p)
def paddedTail (p:FlagDegree) (d:ℕ):FlagDegree :=
  ⟨2 * (padT p - padY p) * d,
    1 + 2 * (padY p - padS p) * d,
    2 * (padS p - 1) * d⟩
def paddedCost (d e:ℕ) (p:FlagDegree):ℕ :=
  flagMixed p (paddedTail p d) (paddedTail p e)
theorem paddedTail_cumulative (p:FlagDegree) (d:ℕ) :
    (paddedTail p d).all = 2 * (padS p - 1) * d ∧
    middle (paddedTail p d) = 1 + 2 * (padY p - 1) * d ∧
    total (paddedTail p d) = 1 + 2 * (padT p - 1) * d:=by
  have hs:1 ≤ padS p:=by
    have h:2 ≤ padS p:=le_max_right _ _
    omega
  have hy:padS p + 1 ≤ padY p:=le_max_right _ _
  have ht:padY p ≤ padT p:=le_max_right _ _
  have hyadd:padY p - padS p + (padS p - 1) = padY p - 1:=by omega
  have htadd:padT p - padY p + (padY p - padS p) + (padS p - 1) =
      padT p - 1:=by omega
  refine ⟨rfl, ?_, ?_⟩
  · change (1 + 2 * (padY p - padS p) * d) + 2 * (padS p - 1) * d = _
    calc
      _ = 1 + 2 * (padY p - padS p + (padS p - 1)) * d:=by ring
      _ = _:=by rw [hyadd]
  · change (2 * (padT p - padY p) * d +
      (1 + 2 * (padY p - padS p) * d)) + 2 * (padS p - 1) * d = _
    calc
      _ = 1 + 2 * (padT p - padY p + (padY p - padS p) +
        (padS p - 1)) * d:=by ring
      _ = _:=by rw [htadd]
theorem padding_mono {p q:FlagDegree} (h:Below p q) :
    padS p ≤ padS q ∧ padY p ≤ padY q ∧ padT p ≤ padT q:=by
  have hs:padS p ≤ padS q:=max_le_max h.1 (Nat.le_refl 2)
  have hy:padY p ≤ padY q:=max_le_max h.2.1 (Nat.add_le_add_right hs 1)
  have ht:padT p ≤ padT q:=max_le_max h.2.2 hy
  exact ⟨hs, hy, ht⟩
theorem paddedTail_mono (d:ℕ) {p q:FlagDegree} (h:Below p q) :
    Below (paddedTail p d) (paddedTail q d):=by
  have hp:=paddedTail_cumulative p d
  have hq:=paddedTail_cumulative q d
  have hc:=padding_mono h
  have hm {a b:ℕ} (hab:a ≤ b):2 * (a - 1) * d ≤ 2 * (b - 1) * d :=
    Nat.mul_le_mul_right d (Nat.mul_le_mul_left 2 (Nat.sub_le_sub_right hab 1))
  unfold Below
  rw [hp.1, hp.2.1, hp.2.2, hq.1, hq.2.1, hq.2.2]
  exact ⟨hm hc.1, Nat.add_le_add_left (hm hc.2.1) 1,
    Nat.add_le_add_left (hm hc.2.2) 1⟩
theorem paddedCost_mono (d e:ℕ) {p q:FlagDegree} (h:Below p q) :
    paddedCost d e p ≤ paddedCost d e q:=by
  exact (mixed_mono_first h _ _).trans
    (mixed_mono_tails q (paddedTail_mono d h) (paddedTail_mono e h))
theorem all_le_middle (p:FlagDegree):p.all ≤ middle p:=by
  dsimp [middle]
  omega
theorem middle_le_total (p:FlagDegree):middle p ≤ total p:=by
  dsimp [middle, total]
  omega
end ProximityPrize.SubmissionLower.LocatorFactorAggregate
end PackedLocator_LocatorFactorAggregate

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier09 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridCost. -/
section PackedLocator_LocatorHybridCost

/-!
# Hybrid second-surface cost

The ordinary cost of a regular factor with cumulative flag `p` is the padded
two-tail Bezout count `paddedCost 131072 131073 p`.  When the padded slope is at
least `2` and the padded middle exceeds the padded slope by at least `2`, the
delayed second tail can be replaced by the hybrid coordinate surface, giving
`hybridCost p`, which is smaller by roughly a fifth on the binding cells.  All
tail flags are monotone in the padded cumulative degrees, so the cost is
monotone under `Below`, exactly like `paddedCost`.
-/

namespace ProximityPrize.SubmissionLower.LocatorHybridCost

open scoped BigOperators
open RCN095 LocatorFactorAggregate

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

def rationalFlag (p : FlagDegree) : FlagDegree :=
  ⟨131072 * (padT p - padY p) + 2 * (padT p - padY p),
    131072 * (padY p - padS p - 1) + 2 * (padY p - padS p - 1) + 2,
    131072 * (padS p - 2) + 2 * (padS p - 2) + 3⟩

def movingFiber (p : FlagDegree) : FlagDegree :=
  ⟨padT p - padY p, padY p - padS p, padS p + 1⟩

def movingCut (p : FlagDegree) : FlagDegree :=
  rationalFlag p + ⟨0, 131072, 262144⟩

/-- The hybrid branch applies when the slope is at least `2` and the middle
exceeds the slope by at least `2`. -/
def HybridApplies (p : FlagDegree) : Prop := 2 ≤ p.all ∧ p.all + 2 ≤ middle p

instance  _root_.ProximityPrize.SubmissionLower.LocatorHybridCost.instDecidableHybridApplies (p : FlagDegree) : Decidable (HybridApplies p) := by
  unfold HybridApplies; infer_instance

theorem pad_bounds (p : FlagDegree) :
    2 ≤ padS p ∧ padS p + 1 ≤ padY p ∧ padY p ≤ padT p :=
  ⟨le_max_right _ _, le_max_right _ _, le_max_right _ _⟩

theorem movingFiber_cumulative (p : FlagDegree) :
    (movingFiber p).all = padS p + 1 ∧
      middle (movingFiber p) = padY p + 1 ∧
      total (movingFiber p) = padT p + 1 := by
  have h := pad_bounds p
  dsimp only [movingFiber, middle, total]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem movingCut_cumulative (p : FlagDegree) :
    (movingCut p).all = 131074 * (padS p - 2) + 262147 ∧
      middle (movingCut p) = 131074 * (padY p - 3) + 393221 ∧
      total (movingCut p) = 131074 * (padT p - 3) + 393221 := by
  have h := pad_bounds p
  dsimp only [movingCut, rationalFlag, middle, total, add_zOnly, add_yz, add_all]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem movingFiber_mono {p q : FlagDegree} (h : Below p q) :
    Below (movingFiber p) (movingFiber q) := by
  have hp := movingFiber_cumulative p
  have hq := movingFiber_cumulative q
  have hc := padding_mono h
  unfold Below
  rw [hp.1, hp.2.1, hp.2.2, hq.1, hq.2.1, hq.2.2]
  omega

theorem movingCut_mono {p q : FlagDegree} (h : Below p q) :
    Below (movingCut p) (movingCut q) := by
  have hp := movingCut_cumulative p
  have hq := movingCut_cumulative q
  have hc := padding_mono h
  have hb := pad_bounds p
  have hb' := pad_bounds q
  unfold Below
  rw [hp.1, hp.2.1, hp.2.2, hq.1, hq.2.1, hq.2.2]
  omega

/-! `ordinaryCostOf` and `OwnBound` are defined by `LocatorHybridCostSelect` (C2). -/

end ProximityPrize.SubmissionLower.LocatorHybridCost
end PackedLocator_LocatorHybridCost

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridCostC1. -/
section PackedLocator_LocatorHybridCostC1
/-
HYBRID SECOND-SURFACE COST — C1 VARIANT (flag level).

Differences from `LocatorHybridCost`:
  * the hybrid coordinate is the bare `rationalFlag` (the half-tail offset
    `⟨0, 65536, 196608⟩` is gone);
  * the moving term's outer factor is `131076 = w + 5` instead of `131072`;
  * `HybridApplies` requires `3 ≤ p.all` (i.e. `r ≥ 3`) rather than `2 ≤ p.all`;
  * `ordinaryCostOf` takes the MINIMUM of the hybrid and padded costs on the
    hybrid branch, so a cell can never be made worse by the branch.

`sharpTail`, `rationalFlag`, `movingFiber` and `movingCut` are reused verbatim
from `LocatorHybridCost`, together with their cumulative and monotonicity lemmas.
-/

namespace ProximityPrize.SubmissionLower.LocatorHybridCostC1

open scoped BigOperators
open RCN095 LocatorFactorAggregate LocatorHybridCost

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

/-- C1: the hybrid coordinate is the rational coordinate. -/
def hybridCoordinateC1 (p : FlagDegree) : FlagDegree := rationalFlag p

/-- The hybrid branch now needs slope at least `3`. -/
def HybridAppliesC1 (p : FlagDegree) : Prop := 3 ≤ p.all ∧ p.all + 2 ≤ middle p

instance  _root_.ProximityPrize.SubmissionLower.LocatorHybridCostC1.instDecidableHybridAppliesC1 (p : FlagDegree) : Decidable (HybridAppliesC1 p) := by
  unfold HybridAppliesC1; infer_instance

theorem rationalFlag_cumulative (p : FlagDegree) :
    (rationalFlag p).all = 131074 * (padS p - 2) + 3 ∧
      middle (rationalFlag p) = 131074 * (padY p - 3) + 5 ∧
      total (rationalFlag p) = 131074 * (padT p - 3) + 5 := by
  have h := pad_bounds p
  dsimp only [rationalFlag, middle, total]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem hybridCoordinateC1_cumulative (p : FlagDegree) :
    (hybridCoordinateC1 p).all = 131074 * (padS p - 2) + 3 ∧
      middle (hybridCoordinateC1 p) = 131074 * (padY p - 3) + 5 ∧
      total (hybridCoordinateC1 p) = 131074 * (padT p - 3) + 5 :=
  rationalFlag_cumulative p

theorem hybridCoordinateC1_mono {p q : FlagDegree} (h : Below p q) :
    Below (hybridCoordinateC1 p) (hybridCoordinateC1 q) := by
  have hp := hybridCoordinateC1_cumulative p
  have hq := hybridCoordinateC1_cumulative q
  have hc := padding_mono h
  have hb := pad_bounds p
  have hb' := pad_bounds q
  unfold Below
  rw [hp.1, hp.2.1, hp.2.2, hq.1, hq.2.1, hq.2.2]
  omega

end ProximityPrize.SubmissionLower.LocatorHybridCostC1
end PackedLocator_LocatorHybridCostC1

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridCostC2. -/
section PackedLocator_LocatorHybridCostC2
/-
HYBRID SECOND-SURFACE COST — C2 VARIANT (flag level).

C2 = C1 plus the REDUCED first tail.  The first tail flag drops from

  sharpTail p   = ⟨2(padT-padY)·d, 1+(2(padY-padS)-1)·d, (2padS-1)·d⟩
to
  reducedTail p = ⟨2(padT-padY)·d, 1+2(padY-padS)·d, 2(padS-1)·d⟩ = paddedTail p d

with `d = 131072`.  The two agree on `yz + all` and on the total, and the
reduced one is smaller by `d` in the `all` column, so it is strictly `Below` the
sharp one and `flagMixed` drops.  Worth about 1.29% on the binding cells.

Everything else is inherited from C1: the coordinate is `rationalFlag`, the
moving factor is `131076 = w + 5`, the branch needs `3 ≤ p.all`, and
`ordinaryCostOf` takes the minimum against the padded two-tail cost.
-/

namespace ProximityPrize.SubmissionLower.LocatorHybridCostC2

open scoped BigOperators
open RCN095 LocatorFactorAggregate LocatorHybridCost LocatorHybridCostC1

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

/-- The reduced first tail at `d = 131072`; it is literally `paddedTail p 131072`. -/
def reducedTail (p : FlagDegree) : FlagDegree := paddedTail p 131072

theorem reducedTail_cumulative (p : FlagDegree) :
    (reducedTail p).all = 2 * (padS p - 1) * 131072 ∧
      middle (reducedTail p) = 1 + 2 * (padY p - 1) * 131072 ∧
      total (reducedTail p) = 1 + 2 * (padT p - 1) * 131072 :=
  paddedTail_cumulative p 131072

theorem reducedTail_mono {p q : FlagDegree} (h : Below p q) :
    Below (reducedTail p) (reducedTail q) := by
  have hp := reducedTail_cumulative p
  have hq := reducedTail_cumulative q
  have hc := padding_mono h
  have hb := pad_bounds p
  have hb' := pad_bounds q
  unfold Below
  rw [hp.1, hp.2.1, hp.2.2, hq.1, hq.2.1, hq.2.2]
  omega

/-- The C2 hybrid cost. -/
def hybridCostC2 (p : FlagDegree) : ℕ :=
  flagMixed p (reducedTail p) (hybridCoordinateC1 p) +
    131076 * flagMixed p (movingFiber p) (movingCut p)

/-- The hybrid branch condition, unchanged from C1. -/
def HybridAppliesC2 (p : FlagDegree) : Prop := 3 ≤ p.all ∧ p.all + 2 ≤ middle p

instance  _root_.ProximityPrize.SubmissionLower.LocatorHybridCostC2.instDecidableHybridAppliesC2 (p : FlagDegree) : Decidable (HybridAppliesC2 p) := by
  unfold HybridAppliesC2; infer_instance

theorem hybridCostC2_mono {p q : FlagDegree} (h : Below p q) :
    hybridCostC2 p ≤ hybridCostC2 q := by
  unfold hybridCostC2
  apply Nat.add_le_add
  · exact (mixed_mono_first h _ _).trans
      (mixed_mono_tails q (reducedTail_mono h) (hybridCoordinateC1_mono h))
  · apply Nat.mul_le_mul_left
    exact (mixed_mono_first h _ _).trans
      (mixed_mono_tails q (movingFiber_mono h) (movingCut_mono h))

end ProximityPrize.SubmissionLower.LocatorHybridCostC2
end PackedLocator_LocatorHybridCostC2

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridCostSelect. -/
section PackedLocator_LocatorHybridCostSelect
/-!
# The ordinary cost of the 6800 certificate (C2 selection)

`LocatorHybridCost.ordinaryCostOf` is the C2 hybrid cost on the C2 branch
(`3 ≤ slope` and `slope + 2 ≤ middle`) and the padded two-tail cost otherwise.
There is deliberately no `min` against the padded cost: on the narrow box
`hybridCostC2 ≤ paddedCost 131072 131073` holds pointwise, and the `if` shape
is what `LocatorOrdinaryZConvex` needs (affine in `z`, not merely concave).
`OwnBound` is `OwnBoundC2`, produced by `LocatorFixedOwnBoundC2`.
-/

namespace ProximityPrize.SubmissionLower.LocatorHybridCost

open RCN095 LocatorFactorAggregate LocatorHybridCostC2

def ordinaryCostOf (p : FlagDegree) : ℕ :=
  if HybridAppliesC2 p then hybridCostC2 p else paddedCost 131072 131073 p

end ProximityPrize.SubmissionLower.LocatorHybridCost
end PackedLocator_LocatorHybridCostSelect

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier10 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorBatchProductRoute. -/
section PackedLocator_LocatorBatchProductRoute
/-!
# Collision-free extraction from a batch of regular factors

Let `A` be a finite set of distinct regular factors and let `P` be their
product.  Suppose a shared power route has reached a quotient family `q` at
depth `j`, so an original row has the form `P^j * q v`.  At the first stage
where not every factor divides every value of `q`, the nonuniversal
divisibility conditions are proper submodules.  A finite-union argument
chooses one `v` avoiding all of them simultaneously.

For `F ∈ A` put `G_F = ∏ (A.erase F)` and retain the cofactor in the
helper:

`Q_F = G_F^j * q v`.

Then `P^j * q v = F^j * Q_F`.  Consequently the order-`j` derivative
extraction makes `Q_F` vanish on every `F`-regular seed, including seeds at
which another factor vanishes.  There is no internal-collision error term or
collision charge.  Pairwise coprimality also gives `IsRelPrime F Q_F`, and
the cofactor exactly restores all residual weight lost to the other factors.
-/

namespace ProximityPrize.SubmissionLower.LocatorBatchProductRoute

open scoped BigOperators
open UniqueFactorizationMonoid
open RCN081 RCN100 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient
  LocatorArbitraryPowerAvoidance LocatorArbitraryPowerContact
  LocatorTwoFactorAvoidance

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

variable {K V : Type} [Field K]
local instance  _root_.ProximityPrize.SubmissionLower.LocatorBatchProductRoute.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.LocatorBatchProductRoute.instStrongNormalizationMonoidMvPolynomialFinOfNatNat_proximityPrize : StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

abbrev P4 (K : Type) [Field K] := MvPolynomial (Fin 4) K

/-! ## Divisibility subspaces and simultaneous avoidance -/

/-- The preimage under a linear polynomial family of the principal ideal
generated by `F`. -/
def dvdSubmodule [AddCommGroup V] [Module K V]
    (q : V →ₗ[K] P4 K) (F : P4 K) : Submodule K V where
  carrier := {v | F ∣ q v}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change F ∣ q x at hx
    change F ∣ q y at hy
    change F ∣ q (x + y)
    rw [map_add]
    exact dvd_add hx hy
  smul_mem' := by
    intro a x hx
    change F ∣ q x at hx
    change F ∣ q (a • x)
    rw [map_smul, MvPolynomial.smul_eq_C_mul]
    exact dvd_mul_of_dvd_right hx _

@[simp] theorem mem_dvdSubmodule [AddCommGroup V] [Module K V]
    (q : V →ₗ[K] P4 K) (F : P4 K) (v : V) :
    v ∈ dvdSubmodule q F ↔ F ∣ q v := Iff.rfl

theorem dvdSubmodule_ne_top_of_not_universal
    [AddCommGroup V] [Module K V]
    (q : V →ₗ[K] P4 K) (F : P4 K)
    (h : ¬ ∀ v, F ∣ q v) :
    dvdSubmodule q F ≠ ⊤ := by
  intro htop
  apply h
  intro v
  have hv : v ∈ dvdSubmodule q F := by rw [htop]; trivial
  exact hv

/-- A field with more elements than the number of nonuniversal factors
contains one vector avoiding every corresponding divisibility subspace.
The vector is automatically nonzero when the factor set is nonempty. -/
theorem exists_avoiding_nonuniversal_factors
    [AddCommGroup V] [Module K V]
    {A : Type} [DecidableEq A] (s : Finset A) (hs : s.Nonempty)
    (q : V →ₗ[K] P4 K) (factor : A → P4 K)
    (hnonuniversal : ∀ a ∈ s, ¬ ∀ v, factor a ∣ q v)
    (hcard : s.card < ENat.card K) :
    ∃ v, v ≠ 0 ∧ ∀ a ∈ s, ¬ factor a ∣ q v := by
  classical
  let bad : s → Submodule K V := fun a => dvdSubmodule q (factor a.1)
  have hproper : ∀ a : s, bad a ≠ ⊤ := by
    intro a
    exact dvdSubmodule_ne_top_of_not_universal q (factor a.1)
      (hnonuniversal a.1 a.2)
  have hsmall : (Finset.univ : Finset s).card < ENat.card K := by
    simpa using hcard
  have hss := RCN133.finite_iUnion_ssubset
    (Finset.univ : Finset s) bad hproper hsmall
  obtain ⟨v, hv⟩ := Set.ssubset_univ_iff_nonempty_compl.mp hss
  have havoid : ∀ a : s, v ∉ bad a := by
    intro a hmem
    apply hv
    simp only [Set.mem_iUnion, Finset.mem_univ, true_and]
    exact ⟨a, trivial, hmem⟩
  have hv0 : v ≠ 0 := by
    intro hz
    obtain ⟨a, ha⟩ := hs
    have hnot := havoid ⟨a, ha⟩
    apply hnot
    subst v
    change factor a ∣ q 0
    simp
  refine ⟨v, hv0, ?_⟩
  intro a ha
  simpa only [bad, mem_dvdSubmodule] using havoid ⟨a, ha⟩

/-! ## Products of distinct regular factors -/

/-- The squarefree product represented by a finite set of regular indices. -/
def regularProduct (H : P4 K) (A : Finset (RCN266.RegularIndex H)) : P4 K :=
  ∏ F ∈ A, F.1

/-- The complementary product after removing one regular index. -/
def regularCofactor (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (F : RCN266.RegularIndex H) : P4 K :=
  ∏ G ∈ A.erase F, G.1

theorem regularFactor_ne_zero (H : P4 K) (F : RCN266.RegularIndex H) :
    F.1 ≠ 0 :=
  (RCN167.positiveRFactors_spec H F.1 F.2).1.ne_zero

theorem regularProduct_ne_zero (H : P4 K)
    (A : Finset (RCN266.RegularIndex H)) : regularProduct H A ≠ 0 := by
  classical
  unfold regularProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro F hF
  exact regularFactor_ne_zero H F

theorem regularCofactor_ne_zero (H : P4 K)
    (A : Finset (RCN266.RegularIndex H)) (F : RCN266.RegularIndex H) :
    regularCofactor H A F ≠ 0 := by
  classical
  unfold regularCofactor
  apply Finset.prod_ne_zero_iff.mpr
  intro G hG
  exact regularFactor_ne_zero H G

/-- Exact factor/cofactor decomposition of the batch product. -/
theorem regularFactor_mul_cofactor
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (F : RCN266.RegularIndex H) (hFA : F ∈ A) :
    F.1 * regularCofactor H A F = regularProduct H A := by
  classical
  simpa only [regularProduct, regularCofactor] using
    Finset.mul_prod_erase A (fun G => G.1) hFA

/-- A regular factor is coprime to the product of all the other regular
factors in the same finite set. -/
theorem regularFactor_isRelPrime_cofactor
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (F : RCN266.RegularIndex H) (hFA : F ∈ A) :
    IsRelPrime F.1 (regularCofactor H A F) := by
  classical
  unfold regularCofactor
  apply IsRelPrime.prod_right
  intro G hG
  have hGe := Finset.mem_erase.mp hG
  apply regularIndex_isRelPrime_of_ne H F G
  intro heq
  apply hGe.1
  exact Subtype.ext heq.symm

/-- Splitting a batch power around one selected factor. -/
theorem regularProduct_power_split
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (F : RCN266.RegularIndex H) (hFA : F ∈ A)
    (j : ℕ) (J : P4 K) :
    regularProduct H A ^ j * J =
      F.1 ^ j * (regularCofactor H A F ^ j * J) := by
  rw [← regularFactor_mul_cofactor H A F hFA, mul_pow]
  ring

/-- Avoiding `F` in the common residual witness makes the cofactor-retaining
helper coprime to `F`. -/
theorem regularFactor_isRelPrime_liftedHelper
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (F : RCN266.RegularIndex H) (hFA : F ∈ A)
    (j : ℕ) (J : P4 K) (hnot : ¬ F.1 ∣ J) :
    IsRelPrime F.1 (regularCofactor H A F ^ j * J) := by
  have hFirred := (RCN167.positiveRFactors_spec H F.1 F.2).1
  apply hFirred.isRelPrime_iff_not_dvd.mpr
  intro hd
  apply hnot
  exact ((regularFactor_isRelPrime_cofactor H A F hFA).pow_right)
    |>.dvd_of_dvd_mul_left hd

/-! ## Exact restoration of residual weights -/

/-- Multiplying the common residual witness by the complementary product
restores precisely the weight spent on all factors other than `F`. -/
theorem cofactor_power_mul_weight_le_sub
    (weights : Fin 4 → ℕ) (B j : ℕ) (F C J : P4 K)
    (hF : F ≠ 0) (hC : C ≠ 0) (hJ : J ≠ 0)
    (hfeasible : j * wt weights (F * C) ≤ B)
    (hbound : wt weights J ≤ B - j * wt weights (F * C)) :
    wt weights (C ^ j * J) ≤ B - j * wt weights F := by
  have hFC := weightedTotalDegree_mul weights F C hF hC
  have hCJ := weightedTotalDegree_mul weights (C ^ j) J
    (pow_ne_zero j hC) hJ
  have hCp := wt_pow_eq weights C hC j
  unfold wt at hfeasible hbound hFC hCJ hCp ⊢
  rw [hFC, Nat.mul_add] at hfeasible hbound
  rw [hCp] at hCJ
  rw [hCJ]
  let f := MvPolynomial.weightedTotalDegree weights F
  let c := MvPolynomial.weightedTotalDegree weights C
  let x := MvPolynomial.weightedTotalDegree weights J
  change j * f + j * c ≤ B at hfeasible
  change x ≤ B - (j * f + j * c) at hbound
  change j * c + x ≤ B - j * f
  have htotal : j * f + (j * c + x) ≤ B := by
    calc
      j * f + (j * c + x) = (j * f + j * c) + x := by omega
      _ ≤ (j * f + j * c) + (B - (j * f + j * c)) :=
        Nat.add_le_add_left hbound _
      _ = B := Nat.add_sub_of_le hfeasible
  have htotal' : (j * c + x) + j * f ≤ B := by
    simpa only [Nat.add_comm] using htotal
  exact Nat.le_sub_of_add_le htotal'

/-- The three residual bounds for every lifted helper. -/
theorem liftedHelper_residual_bounds
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (F : RCN266.RegularIndex H) (hFA : F ∈ A)
    (T YS S j : ℕ) (J : P4 K) (hJ : J ≠ 0)
    (hT : wt residualTotalWeights J ≤
      T - j * wt residualTotalWeights (regularProduct H A))
    (hY : wt residualYSWeights J ≤
      YS - j * wt residualYSWeights (regularProduct H A))
    (hS : wt residualSWeights J ≤
      S - j * wt residualSWeights (regularProduct H A))
    (hTfeasible : j * wt residualTotalWeights (regularProduct H A) ≤ T)
    (hYfeasible : j * wt residualYSWeights (regularProduct H A) ≤ YS)
    (hSfeasible : j * wt residualSWeights (regularProduct H A) ≤ S) :
    wt residualTotalWeights (regularCofactor H A F ^ j * J) ≤
        T - j * wt residualTotalWeights F.1 ∧
      wt residualYSWeights (regularCofactor H A F ^ j * J) ≤
        YS - j * wt residualYSWeights F.1 ∧
      wt residualSWeights (regularCofactor H A F ^ j * J) ≤
        S - j * wt residualSWeights F.1 := by
  have hfactor := regularFactor_mul_cofactor H A F hFA
  have hF0 := regularFactor_ne_zero H F
  have hC0 := regularCofactor_ne_zero H A F
  rw [← hfactor] at hT hY hS hTfeasible hYfeasible hSfeasible
  exact ⟨
    cofactor_power_mul_weight_le_sub residualTotalWeights T j F.1
      (regularCofactor H A F) J hF0 hC0 hJ hTfeasible hT,
    cofactor_power_mul_weight_le_sub residualYSWeights YS j F.1
      (regularCofactor H A F) J hF0 hC0 hJ hYfeasible hY,
    cofactor_power_mul_weight_le_sub residualSWeights S j F.1
      (regularCofactor H A F) J hF0 hC0 hJ hSfeasible hS⟩

/-! ## One common witness and all collision-free helpers -/

/-! ## The current post-projection split -/

/-- Factors whose divisibility subspace is the whole *current* domain. -/
noncomputable def universalFactors
    [AddCommGroup V] [Module K V]
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (q : V →ₗ[K] P4 K) : Finset (RCN266.RegularIndex H) := by
  classical
  exact A.filter fun F => ∀ v, F.1 ∣ q v

@[simp] theorem mem_universalFactors
    [AddCommGroup V] [Module K V]
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (q : V →ₗ[K] P4 K) (F : RCN266.RegularIndex H) :
    F ∈ universalFactors H A q ↔ F ∈ A ∧ ∀ v, F.1 ∣ q v := by
  classical
  simp only [universalFactors, Finset.mem_filter]

theorem universalFactors_subset
    [AddCommGroup V] [Module K V]
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (q : V →ₗ[K] P4 K) : universalFactors H A q ⊆ A := by
  intro F hF
  exact (mem_universalFactors H A q F).mp hF |>.1

/-- Individual universal divisibility combines to divisibility by the entire
squarefree regular product. -/
theorem regularProduct_dvd_of_each
    (H : P4 K) (A : Finset (RCN266.RegularIndex H)) (Q : P4 K)
    (hdiv : ∀ F ∈ A, F.1 ∣ Q) : regularProduct H A ∣ Q := by
  classical
  induction A using Finset.induction_on with
  | empty => simp only [regularProduct, Finset.notMem_empty,
      Finset.prod_empty, one_dvd]
  | @insert F A hFA ih =>
      have hFdiv : F.1 ∣ Q := hdiv F (Finset.mem_insert_self F A)
      have hAdiv : regularProduct H A ∣ Q := by
        apply ih
        intro G hGA
        exact hdiv G (Finset.mem_insert_of_mem hGA)
      have hrel : IsRelPrime F.1 (regularProduct H A) := by
        unfold regularProduct
        apply IsRelPrime.prod_right
        intro G hGA
        apply regularIndex_isRelPrime_of_ne H F G
        intro heq
        apply hFA
        have hFG : F = G := Subtype.ext heq
        rwa [hFG]
      have hprod : regularProduct H (insert F A) =
          F.1 * regularProduct H A := by
        simp only [regularProduct, Finset.prod_insert hFA]
      rw [hprod]
      exact hrel.mul_dvd hFdiv hAdiv

/-- The squarefree product of any set of regular indices divides the
ambient carrier polynomial.  This is the bridge used after a universal
source split: the source controls the product's narrow coordinates, while
the selected carrier still controls its total coordinate. -/
theorem regularProduct_dvd_carrier
    (H : P4 K) (A : Finset (RCN266.RegularIndex H)) :
    regularProduct H A ∣ H := by
  apply regularProduct_dvd_of_each
  intro F _hFA
  exact (RCN167.positiveRFactors_spec H F.1 F.2).2.1

/-- The product of the current universal subset divides every value of the
current family. -/
theorem universalProduct_dvd
    [AddCommGroup V] [Module K V]
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (q : V →ₗ[K] P4 K) :
    ∀ v, regularProduct H (universalFactors H A q) ∣ q v := by
  intro v
  apply regularProduct_dvd_of_each
  intro F hF
  exact (mem_universalFactors H A q F).mp hF |>.2 v

/-! ## Quotienting a fully universal batch -/

/-- A raw constraint-kernel reconstruction lies in the nested source box as
soon as the usual contact/slope shape inequality supplies its YS cap. -/
theorem kernelReconstruct_mem_nested
    {I:Type} [Fintype I]
    (D w L S m YS:ℕ) (nodes u0 u1:I → K)
    (hw:1 ≤ w) (hshape:D+S ≤ w*(YS+1)):
    ∀ v:ConstraintKernel (K:=K) D w L S m nodes u0 u1,
      kernelReconstructLinear (K:=K) D w L S m nodes u0 u1 v ∈
        nestedCoefficientBox K D w L YS S:=by
  intro v d hd
  have hglobal:=reconstruct_mem_globalCoefficientBox K D w L S v.1
  have hb:=hglobal hd
  have hYS:=flag_box_ys_bound D w L S YS hw hshape
    (reconstruct K D w L S v.1) hglobal
  have hy:=(MvPolynomial.le_weightedTotalDegree residualYSWeights hd).trans hYS
  rw [weight_fin4] at hy
  simp only [residualYSWeights] at hy
  refine ⟨hb.1,?_,hb.2.1,hb.2.2⟩
  simpa [residualYSWeights] using hy

/-- Source-entry adapter for a universally divisible squarefree regular
product.  This is the batch analogue of the single-factor private
`quotient_nested` construction: it builds the injective quotient family and
subtracts the product's four weights exactly once. -/
theorem kernelQuotient_regularProduct_nested
    {I:Type} [Fintype I]
    (D w L S m YS:ℕ) (nodes u0 u1:I → K)
    (hw:1 ≤ w) (hshape:D+S ≤ w*(YS+1))
    (H:P4 K) (A:Finset (RCN266.RegularIndex H))
    (hdiv:∀ v:ConstraintKernel (K:=K) D w L S m nodes u0 u1,
      regularProduct H A ∣ reconstruct K D w L S v.1):
    ∃ q:ConstraintKernel (K:=K) D w L S m nodes u0 u1 →ₗ[K] P4 K,
      Function.Injective q ∧
      (∀ v,reconstruct K D w L S v.1=regularProduct H A*q v) ∧
      ∀ v,q v ∈ nestedCoefficientBox K
        (D-wt (contactWeights w) (regularProduct H A)) w
        (L-wt residualTotalWeights (regularProduct H A))
        (YS-wt residualYSWeights (regularProduct H A))
        (S-wt residualSWeights (regularProduct H A)):=by
  let recon:=kernelReconstructLinear (K:=K) D w L S m nodes u0 u1
  have hdiv':∀ v,regularProduct H A ∣ recon v:=by
    intro v
    simpa only [recon,kernelReconstructLinear_apply] using hdiv v
  obtain ⟨hq,hprod,hbox⟩:=quotientLinear_nested_data D w L YS S recon
    (kernelReconstructLinear_injective (K:=K) D w L S m nodes u0 u1)
    (kernelReconstruct_mem_nested D w L S m YS nodes u0 u1 hw hshape)
    (regularProduct H A) (regularProduct_ne_zero H A) hdiv'
  let q:=quotientLinear recon (regularProduct H A)
    (regularProduct_ne_zero H A) hdiv'
  refine ⟨q,hq,?_,?_⟩
  · intro v
    simpa only [recon,kernelReconstructLinear_apply,q] using hprod v
  · exact hbox

/-! ## First strict exit in a shared product-power chain -/

/-- A shared band chain exits when the post-projection universal factors form
a strict subset `U` of the current batch.  The index `j` counts additional
whole-product quotients after the displayed input family `q`; thus a source
which was quotiented once before calling this interface has original power
`j+1` at the exit. -/
def HasBatchExitStage
    [AddCommGroup V] [Module K V]
    (fuel Dlow w delta T YS S : ℕ)
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (q : V →ₗ[K] P4 K) : Prop :=
  ∃ (j : Fin fuel) (U : Finset (RCN266.RegularIndex H)) (v : V) (J : P4 K),
    U ⊂ A ∧ v ≠ 0 ∧ J ≠ 0 ∧
      regularProduct H A ^ j.val * J = q v ∧
      J ∈ nestedCoefficientBox K
        (Dlow - j.val * delta -
          j.val * wt (contactWeights w) (regularProduct H A)) w
        (T - j.val * wt residualTotalWeights (regularProduct H A))
        (YS - j.val * wt residualYSWeights (regularProduct H A))
        (S - j.val * wt residualSWeights (regularProduct H A)) ∧
      ∀ F ∈ A \ U, ¬ F.1 ∣ J

/-! ## Contact-thinned batch selector (lever S1) -/

theorem exists_batchExitStage_of_bandBudgetThin_succ
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (steps Dhigh Dlow w delta T YS S : ℕ)
    (hw : 1 ≤ w) (hDlow : Dlow = Dhigh - delta)
    (q : V →ₗ[K] P4 K) (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K Dhigh w T YS S)
    (H : P4 K) (A : Finset (RCN266.RegularIndex H)) (hA : A.Nonempty)
    (hsource :
      LocatorArbitraryPowerAvoidance.powerBandBudgetThin w Dhigh delta
          (wt (contactWeights w) (regularProduct H A))
          (wt residualTotalWeights (regularProduct H A))
          (wt residualYSWeights (regularProduct H A))
          (wt residualSWeights (regularProduct H A))
          T YS S (steps + 1) < Module.finrank K V)
    (hterminal :
      T - steps * wt residualTotalWeights (regularProduct H A) <
          wt residualTotalWeights (regularProduct H A) ∨
      YS - steps * wt residualYSWeights (regularProduct H A) <
          wt residualYSWeights (regularProduct H A) ∨
      S - steps * wt residualSWeights (regularProduct H A) <
          wt residualSWeights (regularProduct H A))
    (hfield : A.card < ENat.card K) :
    HasBatchExitStage (steps + 1) Dlow w delta T YS S H A q := by
  classical
  let P := regularProduct H A
  have hP : P ≠ 0 := by
    simpa only [P] using regularProduct_ne_zero H A
  change LocatorArbitraryPowerAvoidance.powerBandBudgetThin w Dhigh delta
      (wt (contactWeights w) P)
      (wt residualTotalWeights P) (wt residualYSWeights P)
      (wt residualSWeights P) T YS S (steps + 1) <
    Module.finrank K V at hsource
  change
    T - steps * wt residualTotalWeights P < wt residualTotalWeights P ∨
    YS - steps * wt residualYSWeights P < wt residualYSWeights P ∨
    S - steps * wt residualSWeights P < wt residualSWeights P at hterminal
  induction steps generalizing V Dhigh Dlow T YS S with
  | zero =>
      let bandOne := (highBandMap (K := K) w Dlow delta T
        (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S).comp q
      let lowOne := LinearMap.ker bandOne
      have hwidth : Dhigh ≤ Dlow + delta := by omega
      have hrangeOne : Module.finrank K bandOne.range ≤
          delta * channelCount T
            (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S := by
        calc
          Module.finrank K bandOne.range ≤
              Module.finrank K (HighBandIndex delta T
                (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S → K) :=
            bandOne.range.finrank_le
          _ = delta * channelCount T
              (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S := by
            rw [Module.finrank_fintype_fun_eq_card, highBandIndex_card]
      have hlowOneRank : 0 < Module.finrank K lowOne := by
        have hsum := bandOne.finrank_range_add_finrank_ker
        change Module.finrank K bandOne.range + Module.finrank K lowOne =
          Module.finrank K V at hsum
        have hfirst : delta * channelCount T
            (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S <
              Module.finrank K V := by
          simpa only [LocatorArbitraryPowerAvoidance.powerBandBudgetThin,
            Nat.add_zero] using hsource
        omega
      let qOne : lowOne →ₗ[K] P4 K := q.comp lowOne.subtype
      have hqOne : Function.Injective qOne := by
        intro a b hab
        apply Subtype.ext
        apply hq
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using hab
      have hqOneBox : ∀ v : lowOne,
          qOne v ∈ nestedCoefficientBox K Dlow w T YS S := by
        intro v
        have hzero : highBandMap w Dlow delta T
            (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S (q v.1) = 0 := by
          have hv := v.2
          change bandOne v.1 = 0 at hv
          simpa only [bandOne, qOne, LinearMap.comp_apply,
            Submodule.coe_subtype] using hv
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using
          LocatorArbitraryPowerAvoidance.mem_low_of_highBandMap_cut_eq_zero
            Dhigh Dlow w delta T YS S hw hwidth (q v.1) (hmem v.1) hzero
      let U := universalFactors H A qOne
      have hUsub : U ⊆ A := universalFactors_subset H A qOne
      by_cases hall : U = A
      · have hdivP : ∀ v : lowOne, P ∣ qOne v := by
          intro v
          have hv := universalProduct_dvd H A qOne v
          change regularProduct H U ∣ qOne v at hv
          rw [hall] at hv
          simpa only [P] using hv
        exfalso
        obtain ⟨v, hv⟩ :=
          Module.finrank_pos_iff_exists_ne_zero.mp hlowOneRank
        have hqv : qOne v ≠ 0 := by
          intro hz
          apply hv
          apply hqOne
          simpa only [map_zero] using hz
        have hb := nested_mem_weights (hqOneBox v) hqv
        have hdivT : wt residualTotalWeights P ≤
            wt residualTotalWeights (qOne v) := by
          simpa only [wt] using
            weightedTotalDegree_le_of_dvd residualTotalWeights P
              (qOne v) (hdivP v) hqv
        have hdivY : wt residualYSWeights P ≤
            wt residualYSWeights (qOne v) := by
          simpa only [wt] using
            weightedTotalDegree_le_of_dvd residualYSWeights P
              (qOne v) (hdivP v) hqv
        have hdivS : wt residualSWeights P ≤
            wt residualSWeights (qOne v) := by
          simpa only [wt] using
            weightedTotalDegree_le_of_dvd residualSWeights P
              (qOne v) (hdivP v) hqv
        rcases hterminal with ht | hy | hs
        · apply (not_lt_of_ge (hdivT.trans hb.1))
          simpa only [Nat.zero_mul, Nat.sub_zero] using ht
        · apply (not_lt_of_ge (hdivY.trans hb.2.1))
          simpa only [Nat.zero_mul, Nat.sub_zero] using hy
        · apply (not_lt_of_ge (hdivS.trans hb.2.2.1))
          simpa only [Nat.zero_mul, Nat.sub_zero] using hs
      · have hproper : U ⊂ A :=
          (_root_.ssubset_iff_subset_ne).mpr ⟨hUsub, hall⟩
        have hN : (A \ U).Nonempty := by
          apply Finset.sdiff_nonempty.mpr
          intro hAU
          exact hall (Finset.Subset.antisymm hUsub hAU)
        have hnon : ∀ F ∈ A \ U, ¬ ∀ v, F.1 ∣ qOne v := by
          intro F hFN hdiv
          have hp := Finset.mem_sdiff.mp hFN
          apply hp.2
          exact (mem_universalFactors H A qOne F).mpr ⟨hp.1, hdiv⟩
        have hNcard : (A \ U).card < ENat.card K := by
          calc
            ((A \ U).card : ENat) ≤ (A.card : ENat) := by
              exact_mod_cast (Finset.card_le_card Finset.sdiff_subset)
            _ < ENat.card K := hfield
        obtain ⟨v, hv, havoid⟩ := exists_avoiding_nonuniversal_factors
          (A \ U) hN qOne (fun F => F.1) hnon hNcard
        have hqv : qOne v ≠ 0 := by
          intro hz
          apply hv
          apply hqOne
          simpa only [map_zero] using hz
        refine ⟨⟨0, by omega⟩, U, v.1, qOne v, hproper, ?_, hqv, ?_, ?_, ?_⟩
        · intro hz
          apply hv
          exact Subtype.ext hz
        · simp only [Fin.val_zero, pow_zero, one_mul, qOne,
            LinearMap.comp_apply, Submodule.coe_subtype]
        · simpa only [Fin.val_zero, zero_mul, Nat.sub_zero] using hqOneBox v
        · exact havoid
  | succ steps ih =>
      let bandOne := (highBandMap (K := K) w Dlow delta T
        (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S).comp q
      let lowOne := LinearMap.ker bandOne
      have hwidth : Dhigh ≤ Dlow + delta := by omega
      have hrangeOne : Module.finrank K bandOne.range ≤
          delta * channelCount T
            (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S := by
        calc
          Module.finrank K bandOne.range ≤
              Module.finrank K (HighBandIndex delta T
                (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S → K) :=
            bandOne.range.finrank_le
          _ = delta * channelCount T
              (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S := by
            rw [Module.finrank_fintype_fun_eq_card, highBandIndex_card]
      have hlowOneRank :
          LocatorArbitraryPowerAvoidance.powerBandBudgetThin w
              (Dhigh - delta - wt (contactWeights w) P) delta
              (wt (contactWeights w) P)
              (wt residualTotalWeights P) (wt residualYSWeights P)
              (wt residualSWeights P)
              (T - wt residualTotalWeights P)
              (YS - wt residualYSWeights P)
              (S - wt residualSWeights P) (steps + 1) <
            Module.finrank K lowOne := by
        have hsum := bandOne.finrank_range_add_finrank_ker
        change Module.finrank K bandOne.range + Module.finrank K lowOne =
          Module.finrank K V at hsum
        have hbudget :
            delta * channelCount T
                (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S +
                LocatorArbitraryPowerAvoidance.powerBandBudgetThin w
                  (Dhigh - delta - wt (contactWeights w) P) delta
                  (wt (contactWeights w) P)
                  (wt residualTotalWeights P) (wt residualYSWeights P)
                  (wt residualSWeights P)
                  (T - wt residualTotalWeights P)
                  (YS - wt residualYSWeights P)
                  (S - wt residualSWeights P) (steps + 1) <
              Module.finrank K V := by
          simpa only [LocatorArbitraryPowerAvoidance.powerBandBudgetThin,
            Nat.succ_eq_add_one, Nat.add_assoc] using hsource
        omega
      let qOne : lowOne →ₗ[K] P4 K := q.comp lowOne.subtype
      have hqOne : Function.Injective qOne := by
        intro a b hab
        apply Subtype.ext
        apply hq
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using hab
      have hqOneBox : ∀ v : lowOne,
          qOne v ∈ nestedCoefficientBox K Dlow w T YS S := by
        intro v
        have hzero : highBandMap w Dlow delta T
            (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S (q v.1) = 0 := by
          have hv := v.2
          change bandOne v.1 = 0 at hv
          simpa only [bandOne, qOne, LinearMap.comp_apply,
            Submodule.coe_subtype] using hv
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using
          LocatorArbitraryPowerAvoidance.mem_low_of_highBandMap_cut_eq_zero
            Dhigh Dlow w delta T YS S hw hwidth (q v.1) (hmem v.1) hzero
      let U := universalFactors H A qOne
      have hUsub : U ⊆ A := universalFactors_subset H A qOne
      by_cases hall : U = A
      · have hdivP : ∀ v : lowOne, P ∣ qOne v := by
          intro v
          have hv := universalProduct_dvd H A qOne v
          change regularProduct H U ∣ qOne v at hv
          rw [hall] at hv
          simpa only [P] using hv
        let qTwo := quotientLinear qOne P hP hdivP
        obtain ⟨hqTwo, _hprodTwo, hqTwoBox⟩ :=
          quotientLinear_nested_data Dlow w T YS S qOne hqOne hqOneBox
            P hP hdivP
        let DOneHigh := Dlow - wt (contactWeights w) P
        let DOneLow := Dlow - delta - wt (contactWeights w) P
        let TOne := T - wt residualTotalWeights P
        let YOne := YS - wt residualYSWeights P
        let SOne := S - wt residualSWeights P
        have hDlowRest : DOneLow = DOneHigh - delta := by
          simp only [DOneHigh, DOneLow]
          omega
        have hterminalRest :
            TOne - steps * wt residualTotalWeights P <
                wt residualTotalWeights P ∨
            YOne - steps * wt residualYSWeights P <
                wt residualYSWeights P ∨
            SOne - steps * wt residualSWeights P <
                wt residualSWeights P := by
          rcases hterminal with ht | hy | hs
          · left
            simpa only [TOne, Nat.sub_sub, Nat.add_mul, one_mul,
              Nat.succ_eq_add_one, Nat.add_comm] using ht
          · right; left
            simpa only [YOne, Nat.sub_sub, Nat.add_mul, one_mul,
              Nat.succ_eq_add_one, Nat.add_comm] using hy
          · right; right
            simpa only [SOne, Nat.sub_sub, Nat.add_mul, one_mul,
              Nat.succ_eq_add_one, Nat.add_comm] using hs
        obtain ⟨j, child, v, J, hchild, hv, hJ, heq, hbox, havoid⟩ :=
          ih DOneHigh DOneLow TOne YOne SOne hDlowRest qTwo hqTwo
            (by simpa only [qTwo, DOneHigh, TOne, YOne, SOne] using hqTwoBox)
            (by simpa only [DOneHigh, TOne, YOne, SOne, hDlow] using hlowOneRank)
            hterminalRest
        let jUp : Fin (Nat.succ steps + 1) := ⟨j.val + 1, by omega⟩
        refine ⟨jUp, child, v.1, J, hchild, ?_, hJ, ?_, ?_, havoid⟩
        · intro hz
          apply hv
          exact Subtype.ext hz
        · change P ^ (j.val + 1) * J = q v.1
          calc
            P ^ (j.val + 1) * J = P * (P ^ j.val * J) := by
              rw [pow_succ']
              ring
            _ = P * qTwo v := by rw [heq]
            _ = qOne v :=
              (recon_eq_mul_quotientPolynomial qOne P hdivP v).symm
            _ = q v.1 := rfl
        · have hD :
              DOneLow - j.val * delta -
                  j.val * wt (contactWeights w) P =
                Dlow - (j.val + 1) * delta -
                  (j.val + 1) * wt (contactWeights w) P := by
              simp only [DOneLow, Nat.sub_sub, Nat.add_mul, one_mul]
              congr 1
              omega
          have hT : TOne - j.val * wt residualTotalWeights P =
              T - (j.val + 1) * wt residualTotalWeights P := by
            simp only [TOne, Nat.sub_sub, Nat.add_mul, one_mul]
            congr 1
            omega
          have hY : YOne - j.val * wt residualYSWeights P =
              YS - (j.val + 1) * wt residualYSWeights P := by
            simp only [YOne, Nat.sub_sub, Nat.add_mul, one_mul]
            congr 1
            omega
          have hS : SOne - j.val * wt residualSWeights P =
              S - (j.val + 1) * wt residualSWeights P := by
            simp only [SOne, Nat.sub_sub, Nat.add_mul, one_mul]
            congr 1
            omega
          change J ∈ nestedCoefficientBox K
            (DOneLow - j.val * delta -
              j.val * wt (contactWeights w) P) w
            (TOne - j.val * wt residualTotalWeights P)
            (YOne - j.val * wt residualYSWeights P)
            (SOne - j.val * wt residualSWeights P) at hbox
          change J ∈ nestedCoefficientBox K
            (Dlow - (j.val + 1) * delta -
              (j.val + 1) * wt (contactWeights w) P) w
            (T - (j.val + 1) * wt residualTotalWeights P)
            (YS - (j.val + 1) * wt residualYSWeights P)
            (S - (j.val + 1) * wt residualSWeights P)
          rw [hD, hT, hY, hS] at hbox
          exact hbox
      · have hproper : U ⊂ A :=
          (_root_.ssubset_iff_subset_ne).mpr ⟨hUsub, hall⟩
        have hN : (A \ U).Nonempty := by
          apply Finset.sdiff_nonempty.mpr
          intro hAU
          exact hall (Finset.Subset.antisymm hUsub hAU)
        have hnon : ∀ F ∈ A \ U, ¬ ∀ v, F.1 ∣ qOne v := by
          intro F hFN hdiv
          have hp := Finset.mem_sdiff.mp hFN
          apply hp.2
          exact (mem_universalFactors H A qOne F).mpr ⟨hp.1, hdiv⟩
        have hNcard : (A \ U).card < ENat.card K := by
          calc
            ((A \ U).card : ENat) ≤ (A.card : ENat) := by
              exact_mod_cast (Finset.card_le_card Finset.sdiff_subset)
            _ < ENat.card K := hfield
        obtain ⟨v, hv, havoid⟩ := exists_avoiding_nonuniversal_factors
          (A \ U) hN qOne (fun F => F.1) hnon hNcard
        have hqv : qOne v ≠ 0 := by
          intro hz
          apply hv
          apply hqOne
          simpa only [map_zero] using hz
        refine ⟨⟨0, by omega⟩, U, v.1, qOne v, hproper, ?_, hqv, ?_, ?_, ?_⟩
        · intro hz
          apply hv
          exact Subtype.ext hz
        · simp only [Fin.val_zero, pow_zero, one_mul, qOne,
            LinearMap.comp_apply, Submodule.coe_subtype]
        · simpa only [Fin.val_zero, zero_mul, Nat.sub_zero] using hqOneBox v
        · exact havoid

/-! ## Derivative extraction has no internal-collision locus -/

/-- The retained complementary product is part of the helper passed to the
power-extraction lemma.  Hence this conclusion holds on every regular seed,
without assuming that the complementary product specializes nonzero. -/
theorem specialization_eq_zero_of_batch_power
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (F : RCN266.RegularIndex H) (hFA : F ∈ A)
    (j : ℕ) (P : Polynomial K) (gamma : K) (J : P4 K)
    (hfactorial : (j.factorial : K) ≠ 0)
    (hFzero : RCN319.specialization K P gamma F.1 = 0)
    (hregular : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) F.1) ≠ 0)
    (hpower : RCN319.specialization K P gamma
      (iteratePderivR j (regularProduct H A ^ j * J)) = 0) :
    RCN319.specialization K P gamma
      (regularCofactor H A F ^ j * J) = 0 := by
  rw [regularProduct_power_split H A F hFA j J] at hpower
  exact specialization_eq_zero_of_iteratePderivR_power_product
    j P gamma F.1 (regularCofactor H A F ^ j * J)
    hfactorial hFzero hregular hpower

/-- Kernel/contact wrapper for the collision-free batch extraction.  The
only capacity cost is the derivative order `j`; no specialization condition
on any other regular factor appears. -/
theorem batch_helper_zero_on_regularSeeds
    {I : Type} [Fintype I] [DecidableEq I]
    (j D Dlow w L S m agreements p : ℕ)
    [CharP K p] (hp : p.Prime)
    (nodes : I ↪ K) (u0 u1 : I → K)
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (F : RCN266.RegularIndex H) (hFA : F ∈ A)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (v : ConstraintKernel (K := K) D w L S m nodes u0 u1)
    (J : P4 K)
    (hj : 1 ≤ j) (hjchar : j < p) (hw : 1 ≤ w)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (nodes i) = u0 i + gamma * u1 i)).card)
    (hcapacity : Dlow ≤ (m - j) * agreements + j * (w - 1))
    (hlow : reconstruct K D w L S v.1 ∈
      globalCoefficientBox K Dlow w L S)
    (heq : regularProduct H A ^ j * J = reconstruct K D w L S v.1) :
    ∀ gamma ∈ regularSeeds H selected Gamma F,
      RCN319.specialization K (selected gamma) gamma
        (regularCofactor H A F ^ j * J) = 0 := by
  classical
  intro gamma hgamma
  have hgammaG := regularSeeds_subset H selected Gamma F hgamma
  let support := (Finset.univ : Finset I).filter (fun i ↦
    (selected gamma).eval (nodes i) = u0 i + gamma * u1 i)
  have hcard : agreements ≤ support.card := hagreement gamma hgammaG
  have hcap : Dlow ≤ (m - j) * support.card + j * (w - 1) :=
    hcapacity.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left (m - j) hcard) _)
  have hvalues : ∀ i ∈ support,
      (selected gamma).eval (nodes i) = u0 i + gamma * u1 i := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hder := specialization_iteratePderivR_eq_zero_of_kernel_low_box
    j D Dlow w L S m nodes u0 u1 v hlow
    (selected gamma) gamma support hj hw (hdegree gamma hgammaG)
    hcap hvalues
  rw [← heq] at hder
  obtain ⟨hFzero, hregular⟩ := (Finset.mem_filter.mp hgamma).2
  exact specialization_eq_zero_of_batch_power H A F hFA j
    (selected gamma) gamma J
    (factorial_ne_zero_of_lt_char p j hp hjchar)
    hFzero hregular hder

/-! ## Numerical one-split interface -/

/-! ## Abstract recursion by a phase potential

The state type below is deliberately indexed by an arbitrary well-founded
phase rank.  A state may therefore carry the current quotient space, its
post-projection linear family, the product identity, and all box receipts;
none of those data has to be compressed into a flag.  Its `factors` are
exactly the factors universal immediately after the preceding projection.

At a successor state a consumer has two choices.

* Stop, by showing that the sum of ordinary per-factor caps fits the current
  potential.
* Produce a child state on the universal subset `U`.  All factors in `A \ U`
  must receive helper bounds from the *current* post-projection family.  The
  child potential plus those helper caps must fit the parent potential.

The child may have `U = A`; the phase rank then records one fewer band of the
same source.  When `U ⊂ A`, the child may instead reset to a fresh source and
the phase rank can encode a lexicographic measure such as aggregate positive
R-weight followed by that source's remaining bands.  At rank zero `hbase` is the
terminal receipt (usually the fact that no nonempty universal subset fits the
residual box, followed by one last simultaneous-avoidance split).
-/

/-! ## Complete descent through one source phase

The rank-indexed interface above is convenient while constructing one
particular algebraic route.  Numerical prefix certificates use a different
view: keep applying the same source while it routes the current aggregate,
and stop at the first nonrouteable strict subaggregate.  The next two lemmas
are the finite-set induction engine for that view.

Crucially, a routed step must return a *strict* child.  Thus its algebraic
implementation may restart from a fresh source on that child; no claim about
mixed powers in the preceding source family is hidden in this bookkeeping.
-/

/-- Repeatedly remove a helper-charged complement while `routeable` holds.
At the terminal subaggregate the single shared `defect` bounds what remains
above the additive charge. -/
theorem sum_count_le_charge_add_defect_of_strict_routes
    {A : Type} [DecidableEq A]
    (count charge : A → ℕ)
    (routeable : Finset A → Prop)
    (ambient : Finset A) (defect : ℕ)
    (hterminal : ∀ B, B ⊆ ambient → ¬ routeable B →
      (∑ a ∈ B, count a) ≤ (∑ a ∈ B, charge a) + defect)
    (hroute : ∀ B, B ⊆ ambient → routeable B →
      ∃ U, U ⊂ B ∧
        (∑ a ∈ B \ U, count a) ≤ (∑ a ∈ B \ U, charge a)) :
    (∑ a ∈ ambient, count a) ≤
      (∑ a ∈ ambient, charge a) + defect := by
  classical
  have aux : ∀ B : Finset A, B ⊆ ambient →
      (∑ a ∈ B, count a) ≤ (∑ a ∈ B, charge a) + defect := by
    intro B
    induction B using Finset.strongInduction with
    | H B ih =>
        intro hB
        by_cases hr : routeable B
        · obtain ⟨U, hUB, hexit⟩ := hroute B hB hr
          have hUsub : U ⊆ B := hUB.subset
          have hUambient : U ⊆ ambient := hUsub.trans hB
          have hUbound := ih U hUB hUambient
          let exited := B \ U
          have hexit' : (∑ a ∈ exited, count a) ≤
              (∑ a ∈ exited, charge a) := by
            simpa only [exited] using hexit
          have hsplit : B = U ∪ exited := by
            dsimp only [exited]
            exact (Finset.union_sdiff_of_subset hUsub).symm
          have hdisjoint : Disjoint U exited := by
            apply Finset.disjoint_left.mpr
            intro a hau had
            change a ∈ B \ U at had
            exact (Finset.mem_sdiff.mp had).2 hau
          calc
            (∑ a ∈ B, count a) =
                (∑ a ∈ U, count a) + (∑ a ∈ exited, count a) := by
              rw [hsplit, Finset.sum_union hdisjoint]
            _ ≤ ((∑ a ∈ U, charge a) + defect) +
                (∑ a ∈ exited, charge a) :=
              Nat.add_le_add hUbound hexit'
            _ = (∑ a ∈ B, charge a) + defect := by
              rw [hsplit, Finset.sum_union hdisjoint]
              omega
        · exact hterminal B hB hr
  exact aux ambient (fun _ ha => ha)

/-- One numerical phase transition.  `previous` is the already certified
bound before adding this source.  A nonrouteable terminal row bounds the
previous excess over the new additive charge, while a routeable row supplies
a strict child and helper-charged complement.  The resulting bound is the
minimum of retaining the previous certificate and using the new phase. -/
theorem sum_count_le_min_previous_onePhase
    {A : Type} [DecidableEq A]
    (count charge : A → ℕ)
    (routeable : Finset A → Prop)
    (previous : Finset A → ℕ)
    (ambient : Finset A) (defect : ℕ)
    (hprevious : ∀ B, B ⊆ ambient →
      (∑ a ∈ B, count a) ≤ previous B)
    (hterminal : ∀ B, B ⊆ ambient → ¬ routeable B →
      previous B ≤ (∑ a ∈ B, charge a) + defect)
    (hroute : ∀ B, B ⊆ ambient → routeable B →
      ∃ U, U ⊂ B ∧
        (∑ a ∈ B \ U, count a) ≤ (∑ a ∈ B \ U, charge a)) :
    (∑ a ∈ ambient, count a) ≤
      min (previous ambient) ((∑ a ∈ ambient, charge a) + defect) := by
  classical
  apply le_min
  · exact hprevious ambient (fun _ ha => ha)
  · apply sum_count_le_charge_add_defect_of_strict_routes
      count charge routeable ambient defect
    · intro B hB hnroute
      exact (hprevious B hB).trans (hterminal B hB hnroute)
    · exact hroute

end

end ProximityPrize.SubmissionLower.LocatorBatchProductRoute
end PackedLocator_LocatorBatchProductRoute

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier11 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorGenericHelperFactorSwitch. -/
section PackedLocator_LocatorGenericHelperFactorSwitch

namespace ProximityPrize.SubmissionLower.LocatorGenericHelperFactorSwitch

open ProximityPrize.Benchmark
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN260 RCN266 RCN319
open LocatorCoprimeQuotient LocatorLowQuotient

open scoped Classical

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

local instance  _root_.ProximityPrize.SubmissionLower.LocatorGenericHelperFactorSwitch.instDecidableEqK : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.LocatorGenericHelperFactorSwitch.instDecidableEqI : DecidableEq I := Classical.decEq I
local instance  _root_.ProximityPrize.SubmissionLower.LocatorGenericHelperFactorSwitch.instCharPKOfNatNat : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

end

end ProximityPrize.SubmissionLower.LocatorGenericHelperFactorSwitch
end PackedLocator_LocatorGenericHelperFactorSwitch

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier12 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorGenericPowerRoute. -/
section PackedLocator_LocatorGenericPowerRoute

/-!
# A generic arbitrary-power locator route

This file packages the three generic ingredients needed by the replacement
grid.  A source first supplies either an immediate helper-pair bound or a
common factor.  In the common-factor branch, arbitrary many high-band
projections select an `F`-adic stage.  The arbitrary contact and product
lemmas then make its terminal quotient vanish on every regular seed, and the
same unequal-pair count charges that stage.

There is no hard-coded maximum power and no source-specific arithmetic here.
-/

namespace ProximityPrize.SubmissionLower.LocatorGenericPowerRoute

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN260 RCN266 RCN319
open LocatorCoprimeQuotient LocatorLowQuotient
open LocatorArbitraryPowerAvoidance LocatorArbitraryPowerContact
open LocatorGenericHelperFactorSwitch

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

local instance  _root_.ProximityPrize.SubmissionLower.LocatorGenericPowerRoute.instDecidableEqK : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.LocatorGenericPowerRoute.instDecidableEqI : DecidableEq I := Classical.decEq I
local instance  _root_.ProximityPrize.SubmissionLower.LocatorGenericPowerRoute.instCharPKOfNatNat : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

end

end ProximityPrize.SubmissionLower.LocatorGenericPowerRoute
end PackedLocator_LocatorGenericPowerRoute

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier13 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800Oracle. -/
section PackedLocator_LocatorPhase6800Oracle

/-!
# Compact numerical oracle for the 6800 regular-factor phases

This module contains only the small, reusable interface of the numerical
certificate.  The generated receipt rows live in separate modules.  A raw
state `⟨z,v,r⟩` represents cumulative degrees
`(total, middle, slope) = (z+v+r,v+r,r)`.

The four source phases are, in order, R1200, C, Split500 and Split390.  Three
prefixes forget `z`.  The C prefix retains 304-wide buckets (offset 64) only
on the critical rectangle `r ≤ 17, v ≤ 64`; outside that rectangle it too
forgets `z`.  This is a sound weakening of the exact prefix recurrence.
-/

namespace ProximityPrize.SubmissionLower.LocatorPhase6800Oracle

open scoped BigOperators
open RCN095 LocatorFactorAggregate
open LocatorLowQuotient LocatorArbitraryPowerAvoidance
open LocatorGenericPowerRoute LocatorGenericHelperFactorSwitch

set_option autoImplicit false
set_option maxRecDepth 100000

/-- Coefficients of an additive potential in cumulative coordinates. -/
structure Potential where
  totalCoeff : ℕ
  middleCoeff : ℕ
  slopeCoeff : ℕ
  deriving DecidableEq, Repr

def Potential.eval (q : Potential) (p : FlagDegree) : ℕ :=
  q.totalCoeff * total p + q.middleCoeff * middle p + q.slopeCoeff * p.all

/-- The cumulative boxes used by a power source. -/
structure SourceNumbers where
  totalCap : ℕ
  middleCap : ℕ
  slopeCap : ℕ
  gap : ℕ
  deriving DecidableEq, Repr

def sourceR1200 : SourceNumbers :=
  ⟨526750, 10983, 2450, 36963750380693986577⟩

def sourceC : SourceNumbers :=
  ⟨328400, 6641, 1480, 5090867013182078230⟩

def sourceSplit500 : SourceNumbers :=
  ⟨165000, 3320, 750, 315862958949324685⟩

def sourceSplit390 : SourceNumbers :=
  ⟨19500, 539, 120, 91073661700890⟩

def SourceNumbers.fuel (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  min (s.totalCap / total p)
    (min (s.middleCap / middle p) (s.slopeCap / p.all))

def SourceNumbers.band (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  powerBandBudget 50293 (total p) (middle p) p.all
    (s.totalCap - total p) (s.middleCap - middle p)
    (s.slopeCap - p.all) (s.fuel p)

/-- Lever S1.  The product of the routed factors has contact weight at least
`131071 * middle p - p.all` (`contact_ge_ys` with the exact aggregate weights), and the
source's kernel degree satisfies `D + slopeCap ≤ 131071 * (middleCap + 1)`; so the level-1
contact cap of the band ladder is at most `contactCap`, and it drops by `50293 + contactDec`
per level.  `bandThin` is the ladder charged on the rows that can carry a monomial. -/
def contactDec (p : FlagDegree) : ℕ := 131071 * middle p - p.all

def SourceNumbers.contactCap (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  (131071 * (s.middleCap + 1) - s.slopeCap) - contactDec p

def SourceNumbers.bandThin (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  powerBandBudgetThin 131071 (s.contactCap p) 50293 (contactDec p)
    (total p) (middle p) p.all
    (s.totalCap - total p) (s.middleCap - middle p)
    (s.slopeCap - p.all) (s.fuel p)

def SourceNumbers.Routeable (s : SourceNumbers) (p : FlagDegree) : Prop :=
  1 ≤ p.all ∧ total p ≤ s.totalCap ∧ middle p ≤ s.middleCap ∧
    p.all ≤ s.slopeCap ∧ (s.band p < s.gap ∨ s.bandThin p < s.gap)

instance  _root_.ProximityPrize.SubmissionLower.LocatorPhase6800Oracle.instDecidableRouteable (s : SourceNumbers) (p : FlagDegree) : Decidable (s.Routeable p) :=
  by unfold SourceNumbers.Routeable; infer_instance

/-- Raw-to-cumulative flag constructor. -/
def rawFlag (r v z : ℕ) : FlagDegree := ⟨z, v, r⟩

@[simp] theorem rawFlag_all (r v z : ℕ) : (rawFlag r v z).all = r := rfl
@[simp] theorem rawFlag_middle (r v z : ℕ) : middle (rawFlag r v z) = r + v := by
  simp [rawFlag, middle, Nat.add_comm]
@[simp] theorem rawFlag_total (r v z : ℕ) : total (rawFlag r v z) = r + v + z := by
  simp [rawFlag, total, Nat.add_comm, Nat.add_left_comm]

def sumFlag {ι : Type} (s : Finset ι) (p : ι → FlagDegree) : FlagDegree :=
  ⟨∑ i ∈ s, (p i).zOnly, ∑ i ∈ s, (p i).yz,
    ∑ i ∈ s, (p i).all⟩

@[simp] theorem sumFlag_all {ι : Type} (s : Finset ι)
    (p : ι → FlagDegree) :
    (sumFlag s p).all = ∑ i ∈ s, (p i).all := rfl

@[simp] theorem sumFlag_middle {ι : Type} (s : Finset ι)
    (p : ι → FlagDegree) :
    middle (sumFlag s p) = ∑ i ∈ s, middle (p i) := by
  simp only [sumFlag, middle, Finset.sum_add_distrib]

@[simp] theorem sumFlag_total {ι : Type} (s : Finset ι)
    (p : ι → FlagDegree) :
    total (sumFlag s p) = ∑ i ∈ s, total (p i) := by
  simp only [sumFlag, total, Finset.sum_add_distrib]

/-- A threshold row says at which `z` each source becomes routeable for fixed
positive slope `r` and residual middle coordinate `v`. -/
structure ThresholdReceipt where
  r : ℕ
  v : ℕ
  r1200 : ℕ
  sourceC : ℕ
  split500 : ℕ
  split1200 : ℕ
  split390 : ℕ
  deriving DecidableEq, Repr

def thresholdBoundary (s : SourceNumbers) (r v threshold : ℕ) : Prop :=
  let maxZ := 6677 - (r + v)
  if threshold = 0 then s.Routeable (rawFlag r v 0)
  else if threshold ≤ maxZ then
    ¬s.Routeable (rawFlag r v (threshold - 1)) ∧
      s.Routeable (rawFlag r v threshold)
  else threshold = maxZ + 1 ∧ ¬s.Routeable (rawFlag r v maxZ)

instance  _root_.ProximityPrize.SubmissionLower.LocatorPhase6800Oracle.instDecidableThresholdBoundary (s : SourceNumbers) (r v threshold : ℕ) :
    Decidable (thresholdBoundary s r v threshold) := by
  unfold thresholdBoundary
  infer_instance

def ThresholdReceipt.Valid (q : ThresholdReceipt) : Prop :=
  1 ≤ q.r ∧ q.r ≤ 29 ∧ q.r + q.v ≤ 135 ∧
    thresholdBoundary sourceR1200 q.r q.v q.r1200 ∧
    thresholdBoundary LocatorPhase6800Oracle.sourceC q.r q.v q.sourceC ∧
    thresholdBoundary sourceSplit500 q.r q.v q.split500 ∧
    thresholdBoundary sourceSplit390 q.r q.v q.split390

instance  _root_.ProximityPrize.SubmissionLower.LocatorPhase6800Oracle.instDecidableValid (q : ThresholdReceipt) : Decidable q.Valid := by
  unfold ThresholdReceipt.Valid
  infer_instance

/-! ## Compact exact base table

For fixed raw `(r,v)`, the ordinary partition maximum is stored explicitly at
`z=0,1,2`.  From `z=3` onward it is the maximum of affine carrier lines.  A
segment stores its value at its first integer, avoiding signed intercepts.
-/

structure BaseSegment where
  start : ℕ
  valueAtStart : ℕ
  slope : ℕ
  deriving DecidableEq, Repr

def BaseSegment.evalAt (q : BaseSegment) (z : ℕ) : ℕ :=
  q.valueAtStart + q.slope * (z - q.start)

structure BaseRow where
  r : ℕ
  v : ℕ
  z0 : ℕ
  z1 : ℕ
  z2 : ℕ
  segments : List BaseSegment
  deriving DecidableEq, Repr

def evalBaseSegments : List BaseSegment → ℕ → ℕ
  | [], _ => 0
  | q :: qs, z =>
      (qs.foldl (fun best next => if next.start ≤ z then next else best) q).evalAt z

def BaseRow.evalAt (q : BaseRow) (z : ℕ) : ℕ :=
  if z = 0 then q.z0
  else if z = 1 then q.z1
  else if z = 2 then q.z2
  else evalBaseSegments q.segments z

/-- Row order used by the generated array: increasing `r`, then increasing
`v`, over `1 ≤ r ≤ 29` and `r+v ≤ 135`. -/
def baseRowIndex (r v : ℕ) : ℕ :=
  (r - 1) * 136 - ((r - 1) * r) / 2 + v

def defaultBaseRow : BaseRow := ⟨0, 0, 0, 0, 0, []⟩

def lookupBaseRow (rows : Array BaseRow) (r v : ℕ) : BaseRow :=
  (rows[baseRowIndex r v]?).getD defaultBaseRow

def baseTableCap (rows : Array BaseRow) (p : FlagDegree) : ℕ :=
  (lookupBaseRow rows p.all p.yz).evalAt p.zOnly

def BaseRowsIndexed (rows : Array BaseRow) : Prop :=
  rows.size = 3509 ∧
    ∀ r ∈ (List.range 29).map (fun q => q + 1),
      ∀ v ∈ List.range (136 - r),
        let q := lookupBaseRow rows r v
        q.r = r ∧ q.v = v

instance  _root_.ProximityPrize.SubmissionLower.LocatorPhase6800Oracle.instDecidableBaseRowsIndexed (rows : Array BaseRow) : Decidable (BaseRowsIndexed rows) := by
  unfold BaseRowsIndexed
  infer_instance

def BaseRow.ExpectedShape (q : BaseRow) : Prop :=
  1 ≤ q.r ∧ q.r ≤ 29 ∧ q.r + q.v ≤ 135 ∧
    q.segments ≠ [] ∧ q.segments.head?.map BaseSegment.start = some 3 ∧
    q.segments.Pairwise (fun a b => a.start < b.start) ∧
    ∀ s ∈ q.segments, s.start ≤ 6677 - (q.r + q.v)

instance  _root_.ProximityPrize.SubmissionLower.LocatorPhase6800Oracle.instDecidableExpectedShape (q : BaseRow) : Decidable q.ExpectedShape := by
  unfold BaseRow.ExpectedShape
  infer_instance

/-- Componentwise raw containment used by the defect-prefix recurrence. -/
def RawBelow (q p : FlagDegree) : Prop :=
  q.all ≤ p.all ∧ q.yz ≤ p.yz ∧ q.zOnly ≤ p.zOnly

def RawStrictSlopeBelow (q p : FlagDegree) : Prop :=
  RawBelow q p ∧ q.all < p.all

/-! ## Generic finite-set transition consumed by the batch route -/

end ProximityPrize.SubmissionLower.LocatorPhase6800Oracle
end PackedLocator_LocatorPhase6800Oracle

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier14 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorOrdinaryZConvex. -/
section PackedLocator_LocatorOrdinaryZConvex

namespace ProximityPrize.SubmissionLower.LocatorOrdinaryZConvex

open RCN095 LocatorFactorAggregate LocatorHybridCost LocatorHybridCostC1 LocatorHybridCostC2

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

def rawCost (r v z : ℕ) : ℕ := ordinaryCostOf ⟨z, v, r⟩

theorem hybridApplies_raw (r v z : ℕ) (hr : 3 ≤ r) (hv : 2 ≤ v) :
    HybridAppliesC2 (⟨z, v, r⟩ : FlagDegree) := by
  change 3 ≤ r ∧ r + 2 ≤ v + r
  omega

theorem padS_raw_hybrid (r v z : ℕ) (hr : 2 ≤ r) :
    padS (⟨z, v, r⟩ : FlagDegree) = r := by
  simp only [padS]
  omega

theorem padY_raw_hybrid (r v z : ℕ) (hr : 2 ≤ r) (hv : 2 ≤ v) :
    padY (⟨z, v, r⟩ : FlagDegree) = r + v := by
  simp only [padY, middle, padS_raw_hybrid r v z hr]
  omega

theorem padT_raw_hybrid (r v z : ℕ) (hr : 2 ≤ r) (hv : 2 ≤ v) :
    padT (⟨z, v, r⟩ : FlagDegree) = r + v + z := by
  simp only [padT, total, padY_raw_hybrid r v z hr hv]
  omega

theorem reduced_raw_hybrid (r v z : ℕ) (hr : 2 ≤ r) (hv : 2 ≤ v) :
    reducedTail (⟨z, v, r⟩ : FlagDegree) =
      ⟨2 * z * 131072, 1 + 2 * v * 131072, 2 * (r - 1) * 131072⟩ := by
  unfold reducedTail paddedTail
  rw [padS_raw_hybrid r v z hr, padY_raw_hybrid r v z hr hv,
    padT_raw_hybrid r v z hr hv]
  congr <;> omega

theorem rational_raw_hybrid (r v z : ℕ) (hr : 2 ≤ r) (hv : 2 ≤ v) :
    rationalFlag (⟨z, v, r⟩ : FlagDegree) =
      ⟨131074 * z, 131074 * (v - 1) + 2, 131074 * (r - 2) + 3⟩ := by
  unfold rationalFlag
  rw [padS_raw_hybrid r v z hr, padY_raw_hybrid r v z hr hv,
    padT_raw_hybrid r v z hr hv]
  congr <;> omega

theorem moving_raw_hybrid (r v z : ℕ) (hr : 2 ≤ r) (hv : 2 ≤ v) :
    movingFiber (⟨z, v, r⟩ : FlagDegree) = ⟨z, v, r + 1⟩ := by
  unfold movingFiber
  rw [padS_raw_hybrid r v z hr, padY_raw_hybrid r v z hr hv,
    padT_raw_hybrid r v z hr hv]
  congr <;> omega

theorem hybridCostC2_raw_affine (r v z : ℕ) (hr : 3 ≤ r) (hv : 2 ≤ v) :
    2 * hybridCostC2 (⟨z + 1, v, r⟩ : FlagDegree) =
      hybridCostC2 ⟨z, v, r⟩ + hybridCostC2 ⟨z + 2, v, r⟩ := by
  have hr2 : 2 ≤ r := by omega
  unfold hybridCostC2 hybridCoordinateC1 movingCut
  rw [reduced_raw_hybrid r v z hr2 hv,
    reduced_raw_hybrid r v (z + 1) hr2 hv,
    reduced_raw_hybrid r v (z + 2) hr2 hv,
    rational_raw_hybrid r v z hr2 hv,
    rational_raw_hybrid r v (z + 1) hr2 hv,
    rational_raw_hybrid r v (z + 2) hr2 hv,
    moving_raw_hybrid r v z hr2 hv,
    moving_raw_hybrid r v (z + 1) hr2 hv,
    moving_raw_hybrid r v (z + 2) hr2 hv]
  unfold flagMixed
  simp only [add_zOnly, add_yz, add_all]
  ring

theorem rawCost_affine_of_hybrid (r v z : ℕ) (hr : 3 ≤ r) (hv : 2 ≤ v) :
    2 * rawCost r v (z + 1) = rawCost r v z + rawCost r v (z + 2) := by
  rw [rawCost, rawCost, rawCost]
  simp only [ordinaryCostOf, if_pos (hybridApplies_raw r v z hr hv),
    if_pos (hybridApplies_raw r v (z + 1) hr hv),
    if_pos (hybridApplies_raw r v (z + 2) hr hv)]
  exact hybridCostC2_raw_affine r v z hr hv

theorem paddedTail_raw_of_r_two_v_pos (r v z d : ℕ)
    (hr : 2 ≤ r) (hv : 1 ≤ v) :
    paddedTail (⟨z, v, r⟩ : FlagDegree) d =
      ⟨2 * z * d, 1 + 2 * v * d, 2 * (r - 1) * d⟩ := by
  unfold paddedTail
  have hs : padS (⟨z, v, r⟩ : FlagDegree) = r := by
    simp only [padS]
    omega
  have hy : padY (⟨z, v, r⟩ : FlagDegree) = r + v := by
    simp only [padY, middle, hs]
    omega
  have ht : padT (⟨z, v, r⟩ : FlagDegree) = r + v + z := by
    simp only [padT, total, hy]
    omega
  rw [hs, hy, ht]
  congr <;> omega

theorem paddedCost_raw_affine_of_r_two_v_pos (r v z : ℕ)
    (hr : 2 ≤ r) (hv : 1 ≤ v) :
    2 * paddedCost 131072 131073 (⟨z + 1, v, r⟩ : FlagDegree) =
      paddedCost 131072 131073 ⟨z, v, r⟩ +
        paddedCost 131072 131073 ⟨z + 2, v, r⟩ := by
  unfold paddedCost
  rw [paddedTail_raw_of_r_two_v_pos r v z 131072 hr hv,
    paddedTail_raw_of_r_two_v_pos r v z 131073 hr hv,
    paddedTail_raw_of_r_two_v_pos r v (z + 1) 131072 hr hv,
    paddedTail_raw_of_r_two_v_pos r v (z + 1) 131073 hr hv,
    paddedTail_raw_of_r_two_v_pos r v (z + 2) 131072 hr hv,
    paddedTail_raw_of_r_two_v_pos r v (z + 2) 131073 hr hv]
  unfold flagMixed
  ring

theorem rawCost_affine_of_r_two_v_one (r z : ℕ) (hr : 2 ≤ r) :
    2 * rawCost r 1 (z + 1) = rawCost r 1 z + rawCost r 1 (z + 2) := by
  have hn (x : ℕ) : ¬ HybridAppliesC2 (⟨x, 1, r⟩ : FlagDegree) := by
    intro h
    have hbad := h.2
    change r + 2 ≤ 1 + r at hbad
    omega
  simp only [rawCost, ordinaryCostOf, if_neg (hn z), if_neg (hn (z + 1)),
    if_neg (hn (z + 2))]
  exact paddedCost_raw_affine_of_r_two_v_pos r 1 z hr (by decide)

theorem rawCost_affine_of_r_two_v_two (v z : ℕ) (hv : 2 ≤ v) :
    2 * rawCost 2 v (z + 1) = rawCost 2 v z + rawCost 2 v (z + 2) := by
  have hn (x : ℕ) : ¬ HybridAppliesC2 (⟨x, v, 2⟩ : FlagDegree) := by
    intro h
    have hbad := h.1
    change 3 ≤ 2 at hbad
    omega
  simp only [rawCost, ordinaryCostOf, if_neg (hn z), if_neg (hn (z + 1)),
    if_neg (hn (z + 2))]
  exact paddedCost_raw_affine_of_r_two_v_pos 2 v z (le_refl 2) (by omega)

theorem paddedTail_raw_of_r_one_v_two (v z d : ℕ) (hv : 2 ≤ v) :
    paddedTail (⟨z, v, 1⟩ : FlagDegree) d =
      ⟨2 * z * d, 1 + 2 * (v - 1) * d, 2 * d⟩ := by
  have hs : padS (⟨z, v, 1⟩ : FlagDegree) = 2 := by rfl
  have hy : padY (⟨z, v, 1⟩ : FlagDegree) = v + 1 := by
    unfold padY
    rw [hs]
    change max (v + 1) 3 = v + 1
    omega
  have ht : padT (⟨z, v, 1⟩ : FlagDegree) = v + 1 + z := by
    unfold padT
    rw [hy]
    change max (z + v + 1) (v + 1) = v + 1 + z
    omega
  change (⟨2 * (padT (⟨z, v, 1⟩ : FlagDegree) -
      padY ⟨z, v, 1⟩) * d,
    1 + 2 * (padY (⟨z, v, 1⟩ : FlagDegree) -
      padS ⟨z, v, 1⟩) * d,
    2 * (padS (⟨z, v, 1⟩ : FlagDegree) - 1) * d⟩ : FlagDegree) = _
  rw [ht, hy, hs]
  have hz : v + 1 + z - (v + 1) = z := by omega
  have hvsub : v + 1 - 2 = v - 1 := by omega
  rw [hz, hvsub]

theorem paddedCost_raw_affine_of_r_one_v_two (v z : ℕ) (hv : 2 ≤ v) :
    2 * paddedCost 131072 131073 (⟨z + 1, v, 1⟩ : FlagDegree) =
      paddedCost 131072 131073 ⟨z, v, 1⟩ +
        paddedCost 131072 131073 ⟨z + 2, v, 1⟩ := by
  unfold paddedCost
  rw [paddedTail_raw_of_r_one_v_two v z 131072 hv,
    paddedTail_raw_of_r_one_v_two v z 131073 hv,
    paddedTail_raw_of_r_one_v_two v (z + 1) 131072 hv,
    paddedTail_raw_of_r_one_v_two v (z + 1) 131073 hv,
    paddedTail_raw_of_r_one_v_two v (z + 2) 131072 hv,
    paddedTail_raw_of_r_one_v_two v (z + 2) 131073 hv]
  unfold flagMixed
  ring

theorem rawCost_affine_of_r_one_v_two (v z : ℕ) (hv : 2 ≤ v) :
    2 * rawCost 1 v (z + 1) = rawCost 1 v z + rawCost 1 v (z + 2) := by
  have hn (x : ℕ) : ¬ HybridAppliesC2 (⟨x, v, 1⟩ : FlagDegree) := by
    intro h
    have hbad := h.1
    change 3 ≤ 1 at hbad
    omega
  simp only [rawCost, ordinaryCostOf, if_neg (hn z), if_neg (hn (z + 1)),
    if_neg (hn (z + 2))]
  exact paddedCost_raw_affine_of_r_one_v_two v z hv

theorem paddedTail_raw_of_r_two_v_zero (r z d : ℕ)
    (hr : 2 ≤ r) (hz : 1 ≤ z) :
    paddedTail (⟨z, 0, r⟩ : FlagDegree) d =
      ⟨2 * (z - 1) * d, 1 + 2 * d, 2 * (r - 1) * d⟩ := by
  have hs : padS (⟨z, 0, r⟩ : FlagDegree) = r := by
    unfold padS
    change max r 2 = r
    omega
  have hy : padY (⟨z, 0, r⟩ : FlagDegree) = r + 1 := by
    unfold padY middle
    rw [hs]
    change max (0 + r) (r + 1) = r + 1
    omega
  have ht : padT (⟨z, 0, r⟩ : FlagDegree) = r + z := by
    unfold padT total
    rw [hy]
    change max (z + 0 + r) (r + 1) = r + z
    omega
  change (⟨2 * (padT (⟨z, 0, r⟩ : FlagDegree) -
      padY ⟨z, 0, r⟩) * d,
    1 + 2 * (padY (⟨z, 0, r⟩ : FlagDegree) -
      padS ⟨z, 0, r⟩) * d,
    2 * (padS (⟨z, 0, r⟩ : FlagDegree) - 1) * d⟩ : FlagDegree) = _
  rw [ht, hy, hs]
  have hzsub : r + z - (r + 1) = z - 1 := by omega
  rw [hzsub]
  congr <;> omega

theorem paddedCost_raw_affine_of_r_two_v_zero (r z : ℕ)
    (hr : 2 ≤ r) (hz : 1 ≤ z) :
    2 * paddedCost 131072 131073 (⟨z + 1, 0, r⟩ : FlagDegree) =
      paddedCost 131072 131073 ⟨z, 0, r⟩ +
        paddedCost 131072 131073 ⟨z + 2, 0, r⟩ := by
  unfold paddedCost
  rw [paddedTail_raw_of_r_two_v_zero r z 131072 hr hz,
    paddedTail_raw_of_r_two_v_zero r z 131073 hr hz,
    paddedTail_raw_of_r_two_v_zero r (z + 1) 131072 hr (by omega),
    paddedTail_raw_of_r_two_v_zero r (z + 1) 131073 hr (by omega),
    paddedTail_raw_of_r_two_v_zero r (z + 2) 131072 hr (by omega),
    paddedTail_raw_of_r_two_v_zero r (z + 2) 131073 hr (by omega)]
  have h1 : z + 1 - 1 = z := by omega
  have h2 : z + 2 - 1 = z + 1 := by omega
  rw [h1, h2]
  have hzsplit : z = (z - 1) + 1 := by omega
  rw [hzsplit]
  simp only [Nat.add_sub_cancel]
  unfold flagMixed
  ring

theorem rawCost_affine_of_r_two_v_zero (r z : ℕ)
    (hr : 2 ≤ r) (hz : 1 ≤ z) :
    2 * rawCost r 0 (z + 1) = rawCost r 0 z + rawCost r 0 (z + 2) := by
  have hn (x : ℕ) : ¬ HybridAppliesC2 (⟨x, 0, r⟩ : FlagDegree) := by
    intro h
    have hbad := h.2
    change r + 2 ≤ 0 + r at hbad
    omega
  simp only [rawCost, ordinaryCostOf, if_neg (hn z), if_neg (hn (z + 1)),
    if_neg (hn (z + 2))]
  exact paddedCost_raw_affine_of_r_two_v_zero r z hr hz

theorem paddedTail_raw_r_one_v_one (z d : ℕ) (hz : 1 ≤ z) :
    paddedTail (⟨z, 1, 1⟩ : FlagDegree) d =
      ⟨2 * (z - 1) * d, 1 + 2 * d, 2 * d⟩ := by
  unfold paddedTail padT padY padS middle total
  norm_num
  have hm : max (z + 2) 3 = z + 2 := by omega
  rw [hm]
  congr <;> omega

theorem paddedTail_raw_r_one_v_zero (z d : ℕ) (hz : 2 ≤ z) :
    paddedTail (⟨z, 0, 1⟩ : FlagDegree) d =
      ⟨2 * (z - 2) * d, 1 + 2 * d, 2 * d⟩ := by
  unfold paddedTail padT padY padS middle total
  norm_num
  have hm : max (z + 1) 3 = z + 1 := by omega
  rw [hm]
  congr <;> omega

theorem rawBelow_of_z_le (r v z₁ z₂ : ℕ) (hz : z₁ ≤ z₂) :
    Below (⟨z₁, v, r⟩ : FlagDegree) ⟨z₂, v, r⟩ := by
  change r ≤ r ∧ v + r ≤ v + r ∧ z₁ + v + r ≤ z₂ + v + r
  omega

theorem rawCost_mono_z (r v : ℕ) : Monotone (rawCost r v) := by
  intro z₁ z₂ hz
  have hb := rawBelow_of_z_le r v z₁ z₂ hz
  by_cases ha : HybridAppliesC2 (⟨z₁, v, r⟩ : FlagDegree)
  · have ha' : HybridAppliesC2 (⟨z₂, v, r⟩ : FlagDegree) := by
      rcases ha with ⟨hr, hv⟩
      exact ⟨hr, hv⟩
    simp only [rawCost, ordinaryCostOf, if_pos ha, if_pos ha']
    exact hybridCostC2_mono hb
  · have ha' : ¬ HybridAppliesC2 (⟨z₂, v, r⟩ : FlagDegree) := by
      intro h
      apply ha
      rcases h with ⟨hr, hv⟩
      exact ⟨hr, hv⟩
    simp only [rawCost, ordinaryCostOf, if_neg ha, if_neg ha']
    exact paddedCost_mono 131072 131073 hb

def forwardDiff (f : ℕ → ℕ) (n : ℕ) : ℕ := f (n + 1) - f n

theorem rawCost_affine_r_one_v_one (z : ℕ) (hz : 1 ≤ z) :
    2 * rawCost 1 1 (z + 1) = rawCost 1 1 z + rawCost 1 1 (z + 2) := by
  have hn (x : ℕ) : ¬ HybridAppliesC2 (⟨x, 1, 1⟩ : FlagDegree) := by
    intro h
    have hbad := h.1
    change 3 ≤ 1 at hbad
    omega
  simp only [rawCost, ordinaryCostOf, if_neg (hn z), if_neg (hn (z + 1)),
    if_neg (hn (z + 2))]
  unfold paddedCost
  rw [paddedTail_raw_r_one_v_one z 131072 hz,
    paddedTail_raw_r_one_v_one z 131073 hz,
    paddedTail_raw_r_one_v_one (z + 1) 131072 (by omega),
    paddedTail_raw_r_one_v_one (z + 1) 131073 (by omega),
    paddedTail_raw_r_one_v_one (z + 2) 131072 (by omega),
    paddedTail_raw_r_one_v_one (z + 2) 131073 (by omega)]
  have h1 : z + 1 - 1 = z := by omega
  have h2 : z + 2 - 1 = z + 1 := by omega
  rw [h1, h2]
  have hzsplit : z = (z - 1) + 1 := by omega
  rw [hzsplit]
  simp only [Nat.add_sub_cancel]
  unfold flagMixed
  ring

theorem rawCost_affine_r_one_v_zero (z : ℕ) (hz : 2 ≤ z) :
    2 * rawCost 1 0 (z + 1) = rawCost 1 0 z + rawCost 1 0 (z + 2) := by
  have hn (x : ℕ) : ¬ HybridAppliesC2 (⟨x, 0, 1⟩ : FlagDegree) := by
    intro h
    have hbad := h.1
    change 3 ≤ 1 at hbad
    omega
  simp only [rawCost, ordinaryCostOf, if_neg (hn z), if_neg (hn (z + 1)),
    if_neg (hn (z + 2))]
  unfold paddedCost
  rw [paddedTail_raw_r_one_v_zero z 131072 hz,
    paddedTail_raw_r_one_v_zero z 131073 hz,
    paddedTail_raw_r_one_v_zero (z + 1) 131072 (by omega),
    paddedTail_raw_r_one_v_zero (z + 1) 131073 (by omega),
    paddedTail_raw_r_one_v_zero (z + 2) 131072 (by omega),
    paddedTail_raw_r_one_v_zero (z + 2) 131073 (by omega)]
  have h1 : z + 1 - 2 = z - 1 := by omega
  have h2 : z + 2 - 2 = z := by omega
  rw [h1, h2]
  have hzsplit : z = (z - 2) + 2 := by omega
  rw [hzsplit]
  norm_num
  unfold flagMixed
  ring

theorem rawCost_affine_step_from_two (r v z : ℕ)
    (hr : 1 ≤ r) (hz : 2 ≤ z) :
    2 * rawCost r v (z + 1) = rawCost r v z + rawCost r v (z + 2) := by
  by_cases hr1 : r = 1
  · subst r
    by_cases hv0 : v = 0
    · subst v
      exact rawCost_affine_r_one_v_zero z hz
    · by_cases hv1 : v = 1
      · subst v
        exact rawCost_affine_r_one_v_one z (by omega)
      · exact rawCost_affine_of_r_one_v_two v z (by omega)
  · have hr2 : 2 ≤ r := by omega
    by_cases hv0 : v = 0
    · subst v
      exact rawCost_affine_of_r_two_v_zero r z hr2 (by omega)
    · by_cases hv1 : v = 1
      · subst v
        exact rawCost_affine_of_r_two_v_one r z hr2
      · by_cases hr3 : r = 2
        · subst hr3
          exact rawCost_affine_of_r_two_v_two v z (by omega)
        · exact rawCost_affine_of_hybrid r v z (by omega) (by omega)

theorem forwardDiff_eq_next_of_affine
    (f : ℕ → ℕ) (hmono : Monotone f)
    (n : ℕ) (hstep : 2 * f (n + 1) = f n + f (n + 2)) :
    forwardDiff f n = forwardDiff f (n + 1) := by
  have h₀ := hmono (Nat.le_add_right n 1)
  have h₁ := hmono (Nat.le_add_right (n + 1) 1)
  unfold forwardDiff
  rw [show n + 1 + 1 = n + 2 by omega]
  omega

theorem affine_formula_from_three
    (f : ℕ → ℕ) (hmono : Monotone f)
    (hstep : ∀ n, 2 ≤ n → 2 * f (n + 1) = f n + f (n + 2))
    (z : ℕ) (hz : 3 ≤ z) :
    f z = f 3 + (f 4 - f 3) * (z - 3) := by
  have hdiffStep (n : ℕ) (hn : 2 ≤ n) :
      forwardDiff f n = forwardDiff f (n + 1) :=
    forwardDiff_eq_next_of_affine f hmono n (hstep n hn)
  have hdiff : ∀ n, 3 ≤ n → forwardDiff f n = forwardDiff f 3 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih => exact (hdiffStep n (by omega)).symm.trans ih
  induction z, hz using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
      have hmn := hmono (Nat.le_add_right n 1)
      have hd := hdiff n hn
      have hd' : f (n + 1) - f n = f 4 - f 3 := by
        simpa only [forwardDiff, show 3 + 1 = 4 by decide] using hd
      calc
        f (n + 1) = f n + (f (n + 1) - f n) :=
          (Nat.add_sub_of_le hmn).symm
        _ = f n + (f 4 - f 3) := by rw [hd']
        _ = (f 3 + (f 4 - f 3) * (n - 3)) + (f 4 - f 3) := by
          rw [ih]
        _ = f 3 + (f 4 - f 3) * (n + 1 - 3) := by
          have hnsub : n + 1 - 3 = (n - 3) + 1 := by omega
          rw [hnsub]
          ring

end ProximityPrize.SubmissionLower.LocatorOrdinaryZConvex
end PackedLocator_LocatorOrdinaryZConvex

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier15 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorOrdinaryConcentration. -/
section PackedLocator_LocatorOrdinaryConcentration

/-!
# Concentrating ordinary-factor excess total degree

Discrete convexity lets all raw `z` weight in a finite nonempty family be
moved to one carrier without decreasing the upper bound.  This reduces the
three-coordinate ordinary partition problem to a two-coordinate zero-`z`
knapsack plus one carrier line.
-/

namespace ProximityPrize.SubmissionLower.LocatorOrdinaryConcentration

open scoped BigOperators
open LocatorOrdinaryZConvex

set_option autoImplicit false

end ProximityPrize.SubmissionLower.LocatorOrdinaryConcentration
end PackedLocator_LocatorOrdinaryConcentration

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier16 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800Audit. -/
section PackedLocator_LocatorPhase6800Audit

/-!
# Soundness utilities for the compact 6800 phase receipt

These lemmas are deliberately separate from the generated receipt data.  The
first records the correlated (rather than independent-maxima) initial-A
ledger.  The remaining lemmas justify interpreting a checked threshold row as
an exact routeability cutoff in the raw total coordinate.
-/

namespace ProximityPrize.SubmissionLower.LocatorPhase6800Audit

open scoped BigOperators
open RCN095 LocatorFactorAggregate LocatorArbitraryPowerAvoidance
open LocatorPhase6800Oracle

set_option autoImplicit false
set_option maxRecDepth 100000

/-- Taking one more high-band projection only adds a nonnegative summand. -/
theorem powerBandBudget_le_succ
    (delta dT dY dS T YS S k : ℕ) :
    powerBandBudget delta dT dY dS T YS S k ≤
      powerBandBudget delta dT dY dS T YS S (k + 1) := by
  induction k generalizing T YS S with
  | zero =>
      simp only [powerBandBudget, Nat.zero_add]
      exact Nat.zero_le _
  | succ k ih =>
      simp only [powerBandBudget]
      exact Nat.add_le_add_left
        (ih (T := T - dT) (YS := YS - dY) (S := S - dS)) _

/-- The cumulative high-band cost is monotone in the number of projections. -/
theorem powerBandBudget_mono_fuel
    (delta dT dY dS T YS S : ℕ) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) :
    powerBandBudget delta dT dY dS T YS S k₁ ≤
      powerBandBudget delta dT dY dS T YS S k₂ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction d with
  | zero => simp
  | succ d ih =>
      calc
        powerBandBudget delta dT dY dS T YS S k₁ ≤
            powerBandBudget delta dT dY dS T YS S (k₁ + d) :=
          ih (Nat.le_add_right _ _)
        _ ≤ powerBandBudget delta dT dY dS T YS S ((k₁ + d) + 1) :=
          powerBandBudget_le_succ delta dT dY dS T YS S (k₁ + d)
        _ = powerBandBudget delta dT dY dS T YS S (k₁ + d.succ) := by
          congr 1

/-! ## Noncircular semantics of a prefix receipt -/

/-! ## State-local base semantics -/

/-- The zero-`z` two-coordinate table.  The zero-slope state represents the
empty family; positive-slope states are the `z = 0` entries of the base rows. -/
def baseZeroCap (rows : Array BaseRow) (r v : ℕ) : ℕ :=
  if r = 0 then 0 else baseTableCap rows (rawFlag r v 0)

/-- Slope of the carrier's affine ordinary-cost tail, valid from `z = 3`. -/
def candidateSlope (r v : ℕ) : ℕ :=
  LocatorOrdinaryZConvex.rawCost r v 4 -
    LocatorOrdinaryZConvex.rawCost r v 3

/-- Carrier line after adding the exact zero-`z` residual-table value. -/
def candidateLine (rows : Array BaseRow) (R V r v z : ℕ) : ℕ :=
  LocatorOrdinaryZConvex.rawCost r v 3 +
    baseZeroCap rows (R - r) (V - v) + candidateSlope r v * (z - 3)

/-- Finite arithmetic checked for one aggregate row and one candidate
carrier.  Every generated row has one or two useful affine segments. -/
def CandidateRowCheck (rows : Array BaseRow) (R V r v : ℕ) : Prop :=
  let q := lookupBaseRow rows R V
  let zero := baseZeroCap rows (R - r) (V - v)
  LocatorOrdinaryZConvex.rawCost r v 0 + zero ≤ q.z0 ∧
  LocatorOrdinaryZConvex.rawCost r v 1 + zero ≤ q.z1 ∧
  LocatorOrdinaryZConvex.rawCost r v 2 + zero ≤ q.z2 ∧
  match q.segments with
  | [s] =>
      s.start = 3 ∧ candidateLine rows R V r v s.start ≤ s.valueAtStart ∧
        candidateSlope r v ≤ s.slope
  | [s₁, s₂] =>
      s₁.start = 3 ∧ s₁.start < s₂.start ∧
        candidateLine rows R V r v s₁.start ≤ s₁.valueAtStart ∧
        candidateLine rows R V r v (s₂.start - 1) ≤
          s₁.evalAt (s₂.start - 1) ∧
        candidateLine rows R V r v s₂.start ≤ s₂.valueAtStart ∧
        candidateSlope r v ≤ s₂.slope
  | _ => False

instance  _root_.ProximityPrize.SubmissionLower.LocatorPhase6800Audit.instDecidableCandidateRowCheck (rows : Array BaseRow) (R V r v : ℕ) :
    Decidable (CandidateRowCheck rows R V r v) := by
  unfold CandidateRowCheck
  dsimp only
  generalize hq : lookupBaseRow rows R V = q
  cases hs : q.segments with
  | nil =>
      simp only [hs]
      infer_instance
  | cons s tail =>
      cases ht : tail with
      | nil =>
          simp only [hs, ht]
          infer_instance
      | cons s₂ rest =>
          cases hu : rest with
          | nil =>
              simp only [hs, ht, hu]
              infer_instance
          | cons s₃ rest₃ =>
              simp only [hs, ht, hu]
              infer_instance

/-- One finite `R` layer of the carrier-row checker. -/
def CandidateRCheck (rows : Array BaseRow) (R : ℕ) : Prop :=
  ∀ V ∈ List.range (136 - R),
    ∀ r ∈ List.range (R + 1), 1 ≤ r →
      ∀ v ∈ List.range (V + 1), (r < R ∨ v = V) →
        CandidateRowCheck rows R V r v

instance  _root_.ProximityPrize.SubmissionLower.LocatorPhase6800Audit.instDecidableCandidateRCheck (rows : Array BaseRow) (R : ℕ) : Decidable (CandidateRCheck rows R) := by
  unfold CandidateRCheck
  infer_instance

/-- Complete finite base-table checker.  Its executable domain has only the
2.443-million aggregate/carrier splits, not a `z` grid. -/
def BaseCandidateChecks (rows : Array BaseRow) : Prop :=
  ∀ R ∈ List.range 30, 1 ≤ R → CandidateRCheck rows R

instance  _root_.ProximityPrize.SubmissionLower.LocatorPhase6800Audit.instDecidableBaseCandidateChecks (rows : Array BaseRow) : Decidable (BaseCandidateChecks rows) := by
  unfold BaseCandidateChecks
  infer_instance

end ProximityPrize.SubmissionLower.LocatorPhase6800Audit
end PackedLocator_LocatorPhase6800Audit

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier17 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorBatchPowerRoute. -/
section PackedLocator_LocatorBatchPowerRoute

/-!
# Counting consumer for shared regular-product power routes

`LocatorBatchProductRoute` selects the first strict post-projection factor
subset.  This file turns that algebraic stage into the helper bounds used by
the numerical phase recursion.  Source-specific gaps and receipt arithmetic
remain parameters here and are instantiated in the phase bridge.
-/

namespace ProximityPrize.SubmissionLower.LocatorBatchPowerRoute

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN260 RCN266 RCN319
open LocatorLowQuotient LocatorCoprimeQuotient
  LocatorArbitraryPowerAvoidance LocatorArbitraryPowerContact
  LocatorGenericHelperFactorSwitch LocatorGenericPowerRoute
  LocatorBatchProductRoute

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

local instance  _root_.ProximityPrize.SubmissionLower.LocatorBatchPowerRoute.instDecidableEqK : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.LocatorBatchPowerRoute.instDecidableEqI : DecidableEq I := Classical.decEq I
local instance  _root_.ProximityPrize.SubmissionLower.LocatorBatchPowerRoute.instCharPKOfNatNat : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

/-! ## Contact-thinned consumer (lever S1): the band hypothesis is the thin budget. -/

end

end ProximityPrize.SubmissionLower.LocatorBatchPowerRoute
end PackedLocator_LocatorBatchPowerRoute

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier18 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorFastKernelArithmetic. -/
section PackedLocator_LocatorFastKernelArithmetic

/-!
# Kernel-cheap arithmetic for large locator sources

The contact-rank bound is definitionally a sum of nested `Finset.range` sums.
For the larger replacement sources, evaluating that definition directly would
expand hundreds of millions of summands.  This file closes each rectangular
block symbolically and leaves only one primitive recursion over the contact
rows.  It also provides a primitive-recursive evaluator for coefficient
counts after the weighted cutoff has removed the long zero tail.
-/

namespace ProximityPrize.SubmissionLower.LocatorFastKernelArithmetic

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN100 RCN119 RCN180 RCN302
open LocatorLowQuotient

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Number of entries in a rectangular block, weighted by the descending
affine function `L + 1 - offset - i - j`. -/
def rectangularCount (ni nj offset L : ℕ) : ℕ :=
  ni * nj * (L + 1 - offset) -
    (nj * (ni * (ni - 1) / 2) + ni * (nj * (nj - 1) / 2))

public theorem pairIndexSum (ni nj : ℕ) :
    (∑ i ∈ Finset.range ni, ∑ j ∈ Finset.range nj, (i + j)) =
      nj * (ni * (ni - 1) / 2) + ni * (nj * (nj - 1) / 2) := by
  calc
    (∑ i ∈ Finset.range ni, ∑ j ∈ Finset.range nj, (i + j)) =
        ∑ i ∈ Finset.range ni,
          (nj * i + nj * (nj - 1) / 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_add_distrib, Finset.sum_range_id]
      simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
    _ = nj * (ni * (ni - 1) / 2) + ni * (nj * (nj - 1) / 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_range_id]
      simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]

theorem rectangularSum_eq_rectangularCount (ni nj offset L : ℕ)
    (hbound : offset + (ni - 1) + (nj - 1) ≤ L) :
    (∑ i ∈ Finset.range ni,
      ∑ j ∈ Finset.range nj, (L + 1 - offset - i - j)) =
      rectangularCount ni nj offset L := by
  have hpoint : ∀ i ∈ Finset.range ni, ∀ j ∈ Finset.range nj,
      (L + 1 - offset - i - j) + (i + j) = L + 1 - offset := by
    intro i hi j hj
    have hil : i ≤ ni - 1 := by
      have := Finset.mem_range.mp hi
      omega
    have hjl : j ≤ nj - 1 := by
      have := Finset.mem_range.mp hj
      omega
    omega
  have hadd :
      (∑ i ∈ Finset.range ni,
        ∑ j ∈ Finset.range nj, (L + 1 - offset - i - j)) +
          (∑ i ∈ Finset.range ni,
            ∑ j ∈ Finset.range nj, (i + j)) =
        ni * nj * (L + 1 - offset) := by
    calc
      _ = ∑ i ∈ Finset.range ni,
          ((∑ j ∈ Finset.range nj, (L + 1 - offset - i - j)) +
            ∑ j ∈ Finset.range nj, (i + j)) := by
          rw [Finset.sum_add_distrib]
      _ = ∑ i ∈ Finset.range ni,
          ∑ j ∈ Finset.range nj,
            ((L + 1 - offset - i - j) + (i + j)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact Finset.sum_add_distrib.symm
      _ = ∑ i ∈ Finset.range ni,
          ∑ _j ∈ Finset.range nj, (L + 1 - offset) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          exact hpoint i hi j hj
      _ = ni * nj * (L + 1 - offset) := by
          simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
          ring
  rw [pairIndexSum] at hadd
  unfold rectangularCount
  omega

theorem blockInputCount_eq_rectangularCount (M L s : ℕ)
    (hbound : M + s ≤ L) :
    blockInputCount M L s = rectangularCount (M + 1) (s + 1) 0 L := by
  simpa only [blockInputCount, Nat.zero_add, Nat.sub_zero] using
    rectangularSum_eq_rectangularCount (M + 1) (s + 1) 0 L (by omega)

theorem blockKernelLowerBound_eq_rectangularCount (M L s h : ℕ)
    (hbound : M + s ≤ L) :
    blockKernelLowerBound M L s h =
      rectangularCount (M + 1 - h) (s + 1 - h) h L := by
  by_cases hM : h ≤ M
  · by_cases hs : h ≤ s
    · have hL : h ≤ L := by omega
      have hshape : M - h + (s - h) ≤ L - h := by omega
      have heq : blockKernelLowerBound M L s h =
          blockInputCount (M - h) (L - h) (s - h) := by
        have hMr : M + 1 - h = M - h + 1 := by omega
        have hsr : s + 1 - h = s - h + 1 := by omega
        have hLr : L + 1 - h = L - h + 1 := by omega
        unfold blockKernelLowerBound blockInputCount
        rw [hMr, hsr, hLr]
      rw [heq, blockInputCount_eq_rectangularCount _ _ _ hshape]
      have hMr : M + 1 - h = M - h + 1 := by omega
      have hsr : s + 1 - h = s - h + 1 := by omega
      have hLr : L + 1 - h = L - h + 1 := by omega
      unfold rectangularCount
      rw [hMr, hsr, hLr]
      simp only [Nat.sub_zero]
    · have hz : s + 1 - h = 0 := by omega
      simp [blockKernelLowerBound, rectangularCount, hz]
  · have hz : M + 1 - h = 0 := by omega
    simp [blockKernelLowerBound, rectangularCount, hz]

theorem contactRankBound_eq_rectangularCount (M L s h : ℕ)
    (hbound : M + s ≤ L) :
    contactRankBound M L s h =
      rectangularCount (M + 1) (s + 1) 0 L -
        rectangularCount (M + 1 - h) (s + 1 - h) h L := by
  unfold contactRankBound
  rw [blockInputCount_eq_rectangularCount M L s hbound,
    blockKernelLowerBound_eq_rectangularCount M L s h hbound]

/-- The same local rank as `RCN119.localRankBound`, but every rectangular
block is closed and the sole remaining sum uses primitive recursion. -/
def fastLocalRankBound (m L s : ℕ) : ℕ :=
  kernelSumRange (fun r =>
    let M := min r L
    let h := min (r + 1) (m - r)
    rectangularCount (M + 1) (s + 1) 0 L -
      rectangularCount (M + 1 - h) (s + 1 - h) h L) m

theorem localRankBound_eq_fastLocalRankBound (m L s : ℕ)
    (hshape : m + s ≤ L + 1) :
    localRankBound m L s = fastLocalRankBound m L s := by
  unfold localRankBound fastLocalRankBound
  rw [kernelSumRange_eq]
  apply Finset.sum_congr rfl
  intro r hr
  have hrm : r < m := Finset.mem_range.mp hr
  have hb : min r L + s ≤ L := by
    have hm : min r L ≤ r := Nat.min_le_left _ _
    omega
  exact contactRankBound_eq_rectangularCount
    (min r L) L s (min (r + 1) (m - r)) hb

/-! The primitive evaluator above is already much cheaper than the original
nested `Finset` computation, but it still performs `cutoff * (s + 1)` steps.
The inner summand is quadratic, so the following evaluator closes each row and
performs only `cutoff` primitive steps. -/

/-! ## Constant-time coefficient count in the one-residue regime

For the large power sources used by the 6800 locator, write `D = q*w+r`.
Their entire slope range satisfies `r+s <= w`.  Hence, in slope row `j`,
the nonzero weighted columns are exactly `0,...,q-j`.  Reflecting those
columns and summing the resulting quadratic gives a linear combination of
`choose (q+1-j) 1`, `choose (q+1-j) 2`, and `choose (q+1-j) 3`.
The hockey-stick identity then closes the remaining slope sum.  Numerical
evaluation below uses descending factorials, so its cost depends only on the
fixed indices `2,3,4`, rather than on `q` or `s`.
-/

public theorem two_mul_choose_two_add (n : ℕ) :
    2 * n.choose 2 + n = n * n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.choose_succ_succ]
      simp only [Nat.choose_one_right]
      calc
        2 * (n + n.choose 2) + (n + 1) =
            (2 * n.choose 2 + n) + (2 * n + 1) := by ring
        _ = n * n + (2 * n + 1) := by rw [ih]
        _ = (n + 1) * (n + 1) := by ring

public theorem kernelSumRange_square_eq_choose (n : ℕ) :
    kernelSumRange (fun i => i * i) n =
      2 * n.choose 3 + n.choose 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [kernelSumRange_succ, ih, Nat.choose_succ_succ,
        Nat.choose_succ_succ]
      simp only [Nat.choose_one_right]
      rw [← two_mul_choose_two_add n]
      ring

public theorem finset_sum_range_square_eq_choose (n : ℕ) :
    (∑ i ∈ Finset.range n, i * i) =
      2 * n.choose 3 + n.choose 2 := by
  rw [← kernelSumRange_eq, kernelSumRange_square_eq_choose]

public theorem sum_increasingProduct_eq_choose (U C w N : ℕ) :
    (∑ h ∈ Finset.range N, (U + h) * (C + w * h)) =
      N * (U * C) + (U * w + C) * N.choose 2 +
        w * (2 * N.choose 3 + N.choose 2) := by
  calc
    (∑ h ∈ Finset.range N, (U + h) * (C + w * h)) =
        ∑ h ∈ Finset.range N,
          (U * C + (U * w + C) * h + w * (h * h)) := by
      apply Finset.sum_congr rfl
      intro h hh
      ring
    _ = N * (U * C) + (U * w + C) * N.choose 2 +
          w * (2 * N.choose 3 + N.choose 2) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
      rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_range_id,
        finset_sum_range_square_eq_choose, ← Nat.choose_two_right]

public theorem three_mul_choose_three_add_two_mul_choose_two (n : ℕ) :
    3 * n.choose 3 + 2 * n.choose 2 = n * n.choose 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.choose_succ_succ, Nat.choose_succ_succ]
      simp only [Nat.choose_one_right]
      calc
        3 * (n.choose 2 + n.choose 3) +
              2 * (n + n.choose 2) =
            (3 * n.choose 3 + 2 * n.choose 2) +
              (2 * n.choose 2 + n) + (n.choose 2 + n) := by ring
        _ = n * n.choose 2 + n * n + (n.choose 2 + n) := by
          rw [ih, two_mul_choose_two_add]
        _ = (n + 1) * (n + n.choose 2) := by ring

public theorem oneResidueRow_algebra
    (U C w r j q N wm T V : ℕ)
    (hC : C = r + j) (hN : N + j = q + 1) (hw : wm + 2 = w)
    (hsq : 2 * T + N = N * N)
    (hcub : 3 * V + 2 * T = N * T) :
    N * (U * C) + (U * w + C) * T + w * (2 * V + T) =
      U * (r + q) * N +
        (U * wm + r + q + (wm + 1)) * T +
          (2 * wm + 1) * V := by
  have hCz : (C : ℤ) = (r : ℤ) + j := by exact_mod_cast hC
  have hNz : (N : ℤ) + j = (q : ℤ) + 1 := by exact_mod_cast hN
  have hwz : (wm : ℤ) + 2 = w := by exact_mod_cast hw
  have hsqz : 2 * (T : ℤ) + N = N * N := by exact_mod_cast hsq
  have hcubz : 3 * (V : ℤ) + 2 * T = N * T := by exact_mod_cast hcub
  have hqz : (q : ℤ) = N + j - 1 := by linarith
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [hCz, ← hwz, hqz]
  linear_combination (U : ℤ) * hsqz + hcubz

/-- The three binomial coefficients of one slope row after reflecting its
weighted columns. -/
public def oneResidueCoefficientRow (q r w L j : ℕ) : ℕ :=
  let U := L + 1 - q
  let N := q + 1 - j
  U * (r + q) * N.choose 1 +
    (U * (w - 2) + r + q + ((w - 2) + 1)) * N.choose 2 +
      (2 * (w - 2) + 1) * N.choose 3

public theorem coefficientColumn_eq_oneResidueCoefficientRow
    (q r w L j : ℕ) (hw : 2 ≤ w) (hj : j ≤ q)
    (hL : q ≤ L) (hres : r + j ≤ w) :
    (∑ i ∈ Finset.range (q + 1),
      (L + 1 - i - j) *
        (q * w + r - w * i - (w - 1) * j)) =
      oneResidueCoefficientRow q r w L j := by
  let N := q + 1 - j
  let U := L + 1 - q
  let C := r + j
  have hNpos : 0 < N := by simp only [N]; omega
  have hNq : N ≤ q + 1 := by simp only [N]; omega
  have hsubset : Finset.range N ⊆ Finset.range (q + 1) :=
    Finset.range_mono hNq
  have htrim :
      (∑ i ∈ Finset.range N,
        (L + 1 - i - j) *
          (q * w + r - w * i - (w - 1) * j)) =
      ∑ i ∈ Finset.range (q + 1),
        (L + 1 - i - j) *
          (q * w + r - w * i - (w - 1) * j) := by
    apply Finset.sum_subset hsubset
    intro i hi hinot
    have hiq : i ≤ q := by
      have := Finset.mem_range.mp hi
      omega
    have hiN : N ≤ i := by
      by_contra hni
      exact hinot (Finset.mem_range.mpr (by omega))
    have hij : q + 1 ≤ i + j := by simp only [N] at hiN; omega
    have hr : r ≤ w - j := by omega
    have hmul : w * (q + 1) ≤ w * (i + j) :=
      Nat.mul_le_mul_left w hij
    have hwj : w * j - j = (w - 1) * j := by
      symm
      rw [Nat.sub_mul]
      simp only [Nat.one_mul]
    have hweight : q * w + r ≤ w * i + (w - 1) * j := by
      calc
        q * w + r ≤ q * w + (w - j) := Nat.add_le_add_left hr _
        _ = w * (q + 1) - j := by
          rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm w q]
          omega
        _ ≤ w * (i + j) - j := Nat.sub_le_sub_right hmul j
        _ = w * i + (w - 1) * j := by
          have hjwj : j ≤ w * j :=
            Nat.le_mul_of_pos_left j (by omega)
          rw [Nat.mul_add, Nat.add_sub_assoc hjwj, hwj]
    have hz : q * w + r - w * i - (w - 1) * j = 0 := by
      rw [Nat.sub_sub]
      exact Nat.sub_eq_zero_of_le hweight
    simp only [hz, Nat.mul_zero]
  have hreflect :
      (∑ i ∈ Finset.range N,
        (L + 1 - i - j) *
          (q * w + r - w * i - (w - 1) * j)) =
      ∑ h ∈ Finset.range N, (U + h) * (C + w * h) := by
    rw [← Finset.sum_range_reflect (fun i =>
      (L + 1 - i - j) *
        (q * w + r - w * i - (w - 1) * j)) N]
    apply Finset.sum_congr rfl
    intro h hh
    have hhN : h < N := Finset.mem_range.mp hh
    have hidx : N - 1 - h = q - j - h := by
      simp only [N]
      omega
    have hqsplit : q = (q - j - h) + j + h := by omega
    have hwj : w * j = (w - 1) * j + j := by
      have hw' : w - 1 + 1 = w := by omega
      calc
        w * j = (w - 1 + 1) * j := by rw [hw']
        _ = (w - 1) * j + j := by ring
    have htotal :
        q * w + r = w * (q - j - h) + (w - 1) * j +
          (r + j + w * h) := by
      calc
        q * w + r = ((q - j - h) + j + h) * w + r := by rw [← hqsplit]
        _ = w * (q - j - h) + w * j + w * h + r := by ring
        _ = w * (q - j - h) + (w - 1) * j +
            (r + j + w * h) := by rw [hwj]; ring
    have hfirst : L + 1 - (N - 1 - h) - j = U + h := by
      simp only [N, U]
      omega
    have hsecond :
        q * w + r - w * (N - 1 - h) - (w - 1) * j =
          C + w * h := by
      rw [hidx]
      simp only [C]
      omega
    rw [hfirst, hsecond]
  have hsum := sum_increasingProduct_eq_choose U C w N
  have hNj : N + j = q + 1 := by simp only [N]; omega
  have hwsub : w - 2 + 2 = w := by omega
  have hsq := two_mul_choose_two_add N
  have hcub := three_mul_choose_three_add_two_mul_choose_two N
  rw [← htrim, hreflect, hsum]
  change N * (U * C) + (U * w + C) * N.choose 2 +
      w * (2 * N.choose 3 + N.choose 2) =
    U * (r + q) * N.choose 1 +
      (U * (w - 2) + r + q + ((w - 2) + 1)) * N.choose 2 +
        (2 * (w - 2) + 1) * N.choose 3
  simp only [Nat.choose_one_right]
  exact oneResidueRow_algebra
    (U := U) (C := C) (w := w) (r := r) (j := j) (q := q)
    (N := N) (wm := w - 2) (T := N.choose 2) (V := N.choose 3)
    (by rfl) hNj hwsub hsq hcub

public theorem sum_range_choose_descending_add (N s k : ℕ)
    (hs : s ≤ N) :
    (∑ j ∈ Finset.range (s + 1), (N - j).choose k) +
        (N - s).choose (k + 1) = (N + 1).choose (k + 1) := by
  induction s with
  | zero =>
      simp only [Nat.sub_zero, Finset.range_one, Finset.sum_singleton]
      exact (Nat.choose_succ_succ' N k).symm
  | succ s ih =>
      have hs' : s ≤ N := by omega
      rw [Finset.sum_range_succ]
      have hold := ih hs'
      have hpred : N - s = (N - (s + 1)) + 1 := by omega
      have hp := Nat.choose_succ_succ' (N - (s + 1)) k
      rw [← hpred] at hp
      omega

public theorem sum_range_choose_descending (N s k : ℕ)
    (hs : s ≤ N) :
    (∑ j ∈ Finset.range (s + 1), (N - j).choose k) =
      (N + 1).choose (k + 1) - (N - s).choose (k + 1) := by
  have h := sum_range_choose_descending_add N s k hs
  omega

/-- `Nat.choose` evaluated through a descending factorial.  In this file it
is used only at indices at most four, so closed source receipts do not recurse
through a thousand Pascal rows. -/
def smallChoose (n k : ℕ) : ℕ :=
  n.descFactorial k / Nat.factorial k

public theorem choose_eq_smallChoose (n k : ℕ) :
    n.choose k = smallChoose n k := by
  simpa only [smallChoose] using
    Nat.choose_eq_descFactorial_div_factorial n k

/-- Constant-time coefficient count for `D=q*w+r` when the complete slope
range remains in the first residue regime. -/
def oneResidueCoefficientCount (q r w L s : ℕ) : ℕ :=
  let U := L + 1 - q
  let c1 := U * (r + q)
  let c2 := U * (w - 2) + r + q + ((w - 2) + 1)
  let c3 := 2 * (w - 2) + 1
  c1 * (smallChoose (q + 2) 2 - smallChoose (q + 1 - s) 2) +
    c2 * (smallChoose (q + 2) 3 - smallChoose (q + 1 - s) 3) +
      c3 * (smallChoose (q + 2) 4 - smallChoose (q + 1 - s) 4)

theorem coefficientCount_eq_oneResidueCoefficientCount
    (q r w L s : ℕ) (hw : 2 ≤ w) (hsq : s ≤ q)
    (hL : q ≤ L) (hres : r + s ≤ w) :
    coefficientCount (q * w + r) w L s =
      oneResidueCoefficientCount q r w L s := by
  have hcutoff : q + 1 ≤ L + 1 := by omega
  have hweight : q * w + r ≤ w * (q + 1) := by
    have hrw : r ≤ w := by omega
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm w q]
    omega
  rw [coefficientCount_eq_sum_range_of_weighted_cutoff
    (q * w + r) w L s (q + 1) hcutoff hweight]
  rw [Finset.sum_comm]
  have hrows :
      (∑ j ∈ Finset.range (s + 1),
        ∑ i ∈ Finset.range (q + 1),
          (L + 1 - i - j) *
            (q * w + r - w * i - (w - 1) * j)) =
      ∑ j ∈ Finset.range (s + 1),
        oneResidueCoefficientRow q r w L j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjs : j ≤ s := by
      have := Finset.mem_range.mp hj
      omega
    exact coefficientColumn_eq_oneResidueCoefficientRow q r w L j hw
      (hjs.trans hsq) hL ((Nat.add_le_add_left hjs r).trans hres)
  rw [hrows]
  let U := L + 1 - q
  let c1 := U * (r + q)
  let c2 := U * (w - 2) + r + q + ((w - 2) + 1)
  let c3 := 2 * (w - 2) + 1
  have h1 := sum_range_choose_descending (q + 1) s 1 (by omega)
  have h2 := sum_range_choose_descending (q + 1) s 2 (by omega)
  have h3 := sum_range_choose_descending (q + 1) s 3 (by omega)
  unfold oneResidueCoefficientRow
  change (∑ j ∈ Finset.range (s + 1),
      (c1 * (q + 1 - j).choose 1 +
        c2 * (q + 1 - j).choose 2 +
          c3 * (q + 1 - j).choose 3)) = _
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, h1, h2, h3]
  unfold oneResidueCoefficientCount
  rw [← choose_eq_smallChoose, ← choose_eq_smallChoose,
    ← choose_eq_smallChoose, ← choose_eq_smallChoose,
    ← choose_eq_smallChoose, ← choose_eq_smallChoose]

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

/-- A numerical nullity receipt for any source profile gives the dimension
needed by the arbitrary-power route, uniformly in the two received words. -/
theorem challengeConstraintKernel_finrank_lower_bound_of_numeric
    (D L s m gap : ℕ) (u0 u1 : I → K)
    (hnumeric : gap ≤ coefficientCount D 131071 L s -
      262144 * localRankBound m L s) :
    gap ≤ Module.finrank K
      (ConstraintKernel (K := K) D 131071 L s m
        IRSProfile.domain u0 u1) := by
  have hcard : Fintype.card I = 262144 := by
    norm_num [I, IRSProfile.Index]
  have hlo := constraintKernel_finrank_lower_bound
    (K := K) D 131071 L s m IRSProfile.domain u0 u1
  have hlo' := hcard ▸ hlo
  exact hnumeric.trans hlo'

end ProximityPrize.SubmissionLower.LocatorFastKernelArithmetic
end PackedLocator_LocatorFastKernelArithmetic

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier19 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200Parameters. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1200P : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200Coefficient. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1200C : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankA. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1200RA : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankB. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1200RB : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankC. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1200RC : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankD. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1200RD : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankE. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1200RE : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankF. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1200RF : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankG. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1200RG : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankH. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1200RH : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankI. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1200RI : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankJ. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1200RJ : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankK. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1200RK : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankL. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1200RL : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankM. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1200RM : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankN. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1200RN : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankO. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1200RO : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankP. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1200RP : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankQ. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1200RQ : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankR. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1200RR : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankS. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1200RS : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankT. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1200RT : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankU. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1200RU : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankV. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1200RV : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankW. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1200RW : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankX. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1200RX : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankY. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1200RY : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200Rank. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1200RankAsm : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200Source. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1200S : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1Parameters. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1P : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1Coefficient. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1C : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1RankA. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1RA : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1RankB. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1RB : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1RankC. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1RC : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1RankD. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1RD : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1RankE. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1RE : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1RankF. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1RF : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1RankG. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1RG : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1RankH. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1RH : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1RankI. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1RI : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1RankJ. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1RJ : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1RankK. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1RK : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1RankL. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1RL : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1RankM. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1RM : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1RankN. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1RN : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1RankO. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1RO : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1Rank. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1RankAsm : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1Source. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_R1S : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorChainArithmetic. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier28 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorArithmetic. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier29 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSourceCGap. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier30 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit500Parameters. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_Split500P : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit500Coefficient. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_Split500C : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit500RankA. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_Split500RA : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit500RankB. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_Split500RB : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit500RankC. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_Split500RC : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit500RankD. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_Split500RD : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit500RankE. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_Split500RE : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit500RankF. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_Split500RF : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit500RankG. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_Split500RG : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit500RankH. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_Split500RH : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit500Rank. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_Split500RankAsm : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit500Source. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_Split500S : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit390Parameters. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_Split390P : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit390Coefficient. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_Split390C : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit390RankA. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_Split390RA : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit390RankB. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_Split390RB : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit390Rank. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_Split390RankAsm : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit390Source. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_Split390S : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit1200Parameters. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_Split1200P : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit1200Coefficient. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_Split1200C : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit1200RankA. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_Split1200RA : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit1200RankB. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_Split1200RB : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit1200RankC. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_Split1200RC : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit1200RankD. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_Split1200RD : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit1200Rank. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_Split1200RankAsm : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit1200Source. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_Split1200S : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorBatchPhase6800. -/
section PackedLocator_LocatorBatchPhase6800

/-!
# Semantic batch phases for the 6800 certificate

This module identifies a finset's cumulative flag with the three exact
weights of its squarefree regular product and connects the numerical
`SourceNumbers.Routeable` predicate to the shared batch source theorem.
-/

namespace ProximityPrize.SubmissionLower.LocatorBatchPhase6800

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN071 RCN081 RCN095 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156
  RCN180 RCN234 RCN238 RCN260 RCN266
open LocatorFactorAggregate LocatorArbitraryPowerAvoidance
  LocatorBatchProductRoute LocatorBatchPowerRoute
  LocatorGenericHelperFactorSwitch LocatorPhase6800Oracle

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance  _root_.ProximityPrize.SubmissionLower.LocatorBatchPhase6800.instDecidableEqK : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.LocatorBatchPhase6800.instDecidableEqI : DecidableEq I := Classical.decEq I

/-- Additive flag of a finite batch of regular factors. -/
def regularAggregateFlag (H : P4) (A : Finset (RegularIndex H)) : FlagDegree :=
  sumFlag A (regularCumulativeFlag H)

public theorem regularProduct_weight_eq_sum
    (weights : Fin 4 → ℕ) (H : P4) (A : Finset (RegularIndex H)) :
    wt weights (regularProduct H A) = ∑ F ∈ A, wt weights F.1 := by
  have h := weightedTotalDegree_prod_eq weights A
    (fun F : RegularIndex H => F.1)
    (fun F _hF => regularFactor_ne_zero H F)
  simpa only [regularProduct, wt] using h

theorem regularAggregateFlag_all (H : P4) (A : Finset (RegularIndex H)) :
    (regularAggregateFlag H A).all =
      wt residualSWeights (regularProduct H A) := by
  rw [regularAggregateFlag, sumFlag_all]
  calc
    (∑ F ∈ A, (regularCumulativeFlag H F).all) =
        ∑ F ∈ A, wt residualSWeights F.1 := by
      apply Finset.sum_congr rfl
      intro F _hF
      exact (originalCumulativeFlag_cumulative F.1).1
    _ = wt residualSWeights (regularProduct H A) :=
      (regularProduct_weight_eq_sum residualSWeights H A).symm

theorem regularAggregateFlag_middle (H : P4)
    (A : Finset (RegularIndex H)) :
    middle (regularAggregateFlag H A) =
      wt residualYSWeights (regularProduct H A) := by
  rw [regularAggregateFlag, sumFlag_middle]
  calc
    (∑ F ∈ A, middle (regularCumulativeFlag H F)) =
        ∑ F ∈ A, wt residualYSWeights F.1 := by
      apply Finset.sum_congr rfl
      intro F _hF
      exact (originalCumulativeFlag_cumulative F.1).2.1
    _ = wt residualYSWeights (regularProduct H A) :=
      (regularProduct_weight_eq_sum residualYSWeights H A).symm

theorem regularAggregateFlag_total (H : P4)
    (A : Finset (RegularIndex H)) :
    total (regularAggregateFlag H A) =
      wt residualTotalWeights (regularProduct H A) := by
  rw [regularAggregateFlag, sumFlag_total]
  calc
    (∑ F ∈ A, total (regularCumulativeFlag H F)) =
        ∑ F ∈ A, wt residualTotalWeights F.1 := by
      apply Finset.sum_congr rfl
      intro F _hF
      exact (originalCumulativeFlag_cumulative F.1).2.2
    _ = wt residualTotalWeights (regularProduct H A) :=
      (regularProduct_weight_eq_sum residualTotalWeights H A).symm

theorem regularAggregateFlag_mono (H : P4)
    {A B : Finset (RegularIndex H)} (hAB : A ⊆ B) :
    (regularAggregateFlag H A).all ≤ (regularAggregateFlag H B).all ∧
      middle (regularAggregateFlag H A) ≤
        middle (regularAggregateFlag H B) ∧
      total (regularAggregateFlag H A) ≤
        total (regularAggregateFlag H B) := by
  simp only [regularAggregateFlag, sumFlag_all, sumFlag_middle, sumFlag_total]
  exact ⟨Finset.sum_le_sum_of_subset hAB,
    Finset.sum_le_sum_of_subset hAB, Finset.sum_le_sum_of_subset hAB⟩

theorem regularAggregateFlag_all_lt_of_ssubset (H : P4)
    {A B : Finset (RegularIndex H)} (hAB : A ⊂ B) :
    (regularAggregateFlag H A).all < (regularAggregateFlag H B).all := by
  have hnBA : ¬ B ⊆ A := by
    intro hBA
    exact hAB.ne (Finset.Subset.antisymm hAB.subset hBA)
  simp only [Finset.subset_iff, not_forall, _root_.not_imp] at hnBA
  obtain ⟨F, hFB, hFA⟩ := hnBA
  simp only [regularAggregateFlag, sumFlag_all]
  exact Finset.sum_lt_sum_of_subset hAB.subset hFB hFA
    (regularCumulativeFlag_positive H F)
    (fun _ _ _ => Nat.zero_le _)

/-! ## State-local phase semantics

The numerical receipt is indexed by the exact aggregate raw flag.  These
lemmas keep that state intact while the algebraic route repeatedly replaces a
routeable batch by a strict universal sub-batch.
-/

/-- Raw-coordinate monotonicity of the aggregate flag. -/
theorem regularAggregateFlag_raw_mono (H : P4)
    {A B : Finset (RegularIndex H)} (hAB : A ⊆ B) :
    RawBelow (regularAggregateFlag H A) (regularAggregateFlag H B) := by
  refine ⟨?_, ?_, ?_⟩
  · change (∑ F ∈ A, (regularCumulativeFlag H F).all) ≤
      ∑ F ∈ B, (regularCumulativeFlag H F).all
    exact Finset.sum_le_sum_of_subset hAB
  · change (∑ F ∈ A, (regularCumulativeFlag H F).yz) ≤
      ∑ F ∈ B, (regularCumulativeFlag H F).yz
    exact Finset.sum_le_sum_of_subset hAB
  · change (∑ F ∈ A, (regularCumulativeFlag H F).zOnly) ≤
      ∑ F ∈ B, (regularCumulativeFlag H F).zOnly
    exact Finset.sum_le_sum_of_subset hAB

/-- An additive phase potential commutes with aggregation. -/
theorem sum_phasePotential_eval (q : Potential) (H : P4)
    (A : Finset (RegularIndex H)) :
    (∑ F ∈ A, q.eval (regularCumulativeFlag H F)) =
      q.eval (regularAggregateFlag H A) := by
  simp only [Potential.eval, Finset.sum_add_distrib, ← Finset.mul_sum,
    regularAggregateFlag, sumFlag_total, sumFlag_middle, sumFlag_all]

end

end ProximityPrize.SubmissionLower.LocatorBatchPhase6800
end PackedLocator_LocatorBatchPhase6800

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier43 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800SourceSound. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier44 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800Kernels. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier45 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorFixedStage. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier46 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorFixed. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier47 : True := by trivial
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier48 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridCells. -/
section PackedLocator_LocatorHybridCells
/-
LOCATOR HYBRID CELLS (port of ContactRouterCellCosts6750Research + the pure
flag arithmetic of ContactHybridTailProvider6751Research §1 from pr359).

Cells are parameterised by (t y r) with the atoms
  a = cellA t y = t - y,  b = cellB y r = y - r - 1,  s = cellS r = r - 2,
so that (for 2 ≤ r < y ≤ t) t = a+b+s+3, y = b+s+3, r = s+2 and the stage
support is `support a b s`.  `w` is the Locator's `RCN327.w = 131071`.
-/
namespace ProximityPrize.SubmissionLower.LocatorHybridCells
open scoped Classical BigOperators
open RCN095 RCN198 RCN206 RCN287 RCN327 RCN263 RCN237 RCN264 RCN275 RCN084
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ### Cell atoms and flags -/

def cellA (t y : Nat) : Nat := t - y
def cellB (y r : Nat) : Nat := y - r - 1
def cellS (r : Nat) : Nat := r - 2

def cellSupport (t y r : Nat) : ResidualSupportParameters :=
  support (cellA t y) (cellB y r) (cellS r)

def cellFirstTail (t y r : Nat) : FlagDegree :=
  reducedResidualAgreementFlag (cellSupport t y r) (w + 1)

def cellDirection (t y r : Nat) : FlagDegree :=
  RCN206.directionFlag (cellA t y) (cellB y r) (cellS r)

def cellRational (t y r : Nat) : FlagDegree :=
  ⟨(w + 1) * cellA t y + (cellDirection t y r).zOnly,
    (w + 1) * cellB y r + (cellDirection t y r).yz + 1,
    (w + 1) * cellS r + (cellDirection t y r).all⟩

def cellMovingFiber (t y r : Nat) : FlagDegree :=
  RCN206.fiberFlag (cellA t y) (cellB y r) (cellS r)

def cellMovingCut (t y r : Nat) : FlagDegree :=
  cellRational t y r + ⟨0, w + 1, 2 * (w + 1)⟩

/-! ### Pure flag arithmetic (pr359 §1)

All lemmas are subtraction-free: they are stated over the cell atoms
a = cellA t y, b = cellB y r, s = cellS r. -/

theorem flag_ext {f g : FlagDegree} (h1 : f.zOnly = g.zOnly)
    (h2 : f.yz = g.yz) (h3 : f.all = g.all) : f = g := by
  cases f; cases g; simp_all

/-- cellMovingCut = center + (w+1) • surfaceFlag — the flag under which
    exists_firstTail_cut_budgets bounds the movingCost sum. -/
theorem cellMovingCut_eq_center_add (t y r : Nat) :
    cellMovingCut t y r =
      center (cellA t y) (cellB y r) (cellS r) +
        (w + 1) • RCN206.surfaceFlag (cellA t y) (cellB y r) (cellS r) := by
  refine flag_ext ?_ ?_ ?_ <;>
    simp only [center, direction, unitYZFlag, cellMovingCut, cellRational,
      cellDirection, RCN206.directionFlag, RCN206.surfaceFlag,
      add_zOnly, add_yz, add_all, nsmul_zOnly, nsmul_yz, nsmul_all] <;> ring

/-- weightedCost is monotone under coordinate-wise flag dominance. -/
theorem weightedCost_mono
    {Omega : Type} [Field Omega]
    {G T H : MvPolynomial (Fin 3) Omega}
    {surfaceFlag firstTailFlag : FlagDegree}
    (B : PrimeFlagBudgetFamily (G := G) (T := T) (H := H)
      surfaceFlag firstTailFlag)
    (C : RegularComponent Omega G T H)
    {f g : FlagDegree}
    (hz : f.zOnly ≤ g.zOnly) (hy : f.yz ≤ g.yz) (ha : f.all ≤ g.all) :
    B.weightedCost f C ≤ B.weightedCost g C := by
  simp only [PrimeFlagBudgetFamily.weightedCost]
  gcongr

/-! ### Numeric gates for the cell coordinates -/

/-- The rational coordinate's yz-column in closed form. -/
theorem cellRational_yz (t y r : Nat) :
    (cellRational t y r).yz = 131074 * cellB y r + 2 := by
  simp only [cellRational, cellDirection, RCN206.directionFlag, w]
  omega

/-- In the hybrid branch `r + 2 ≤ y` the atom `b = cellB y r` is positive, so any
    error cap below 131075 passes the rational gate. -/
theorem rationalGate_of_le (t y r errorCap : Nat) (hb : r + 2 ≤ y)
    (hcap : errorCap + 1 ≤ 131076) :
    errorCap + 1 ≤ (cellRational t y r).yz := by
  rw [cellRational_yz]
  have hB : 1 ≤ cellB y r := by
    simp only [cellB]
    omega
  have := Nat.mul_le_mul_left 131074 hB
  omega

/-! ### Closed forms in the atoms (a, b, s) = (cellA t y, cellB y r, cellS r)

These match the subtraction-free shapes `sharpABS / rationalABS / hybABS /
mfibABS / mcutABS` used elsewhere in the Locator, so the hybrid bound can be
rewritten into that form by `hybridBound_eq`. -/

end
end ProximityPrize.SubmissionLower.LocatorHybridCells
end PackedLocator_LocatorHybridCells

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridCellsC1. -/
section PackedLocator_LocatorHybridCellsC1
/-
LOCATOR HYBRID CELLS — C1 VARIANT.

C1 drops the half-tail offset from the hybrid coordinate:

  cellHybridCoordinateC1 t y r = cellRational t y r      (was  cellRational + ⟨0, (w+1)/2, 3·((w+1)/2)⟩)

which is affordable once the *flag* route is restricted to components of local
multiplicity at least 6.  Components of multiplicity 1..5 are charged instead
through the moving engine at cut level `w + mult`, so the moving term's outer
factor grows from `w + 1` to `w + 5`.  The branch condition gains `3 ≤ r`
(equivalently `1 ≤ cellS r`); at `r = 2` the padded two-tail cost is already
cheaper than the current hybrid cost, so nothing is lost there.

This file only ADDS the C1 pieces on top of `LocatorHybridCells`; every flag and
lemma that is unchanged (cellA/cellB/cellS, cellSupport, cellSharpTail,
cellRational, cellMovingFiber, cellMovingCut, cellMovingCut_eq_center_add,
weightedCost_mono, the closed forms) is reused verbatim.
-/
namespace ProximityPrize.SubmissionLower.LocatorHybridCellsC1
open scoped Classical BigOperators
open RCN095 RCN198 RCN206 RCN287 RCN327 RCN263 RCN237 RCN264 RCN275 RCN084
open LocatorHybridCells
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ### The C1 hybrid coordinate -/

/-- C1: the hybrid coordinate is the bare rational coordinate. -/
def cellHybridCoordinateC1 (t y r : Nat) : FlagDegree := cellRational t y r

/-! ### Absorption at the bare rational coordinate, threshold `6 ≤ mult`

The three lemmas below replace `LocatorHybridCells.sharp_absorbs_all` /
`sharp_absorbs_ysall` / `sharp_absorbs_total`.  The offsets `196608` and
`262144` are gone; in exchange `2 ≤ mult` becomes `6 ≤ mult` and the branch
positivity hypotheses `1 ≤ s`, `1 ≤ b + s`, `1 ≤ a + b + s` are required.  All
three follow from `r + 2 ≤ y` and `3 ≤ r`. -/

/-- z-cumulative absorption.
    sharp.all = (2s+3)·(131072+delay);  rational.all = 131072·s + (2s+3). -/
theorem sharp_absorbs_all_C1 (s delay mult : ℕ) (hs : 1 ≤ s)
    (hdm : delay ≤ mult) (hm6 : 6 ≤ mult) :
    (2 * s + 3) * (131072 + delay) ≤ mult * (131072 * s + (2 * s + 3)) := by
  have key : 131072 * (2 * s + 3) ≤ mult * (131072 * s) := by
    calc 131072 * (2 * s + 3) ≤ 131072 * (6 * s) := by omega
      _ = 6 * (131072 * s) := by ring
      _ ≤ mult * (131072 * s) := Nat.mul_le_mul_right _ hm6
  calc
    (2 * s + 3) * (131072 + delay) ≤ (2 * s + 3) * (131072 + mult) :=
      Nat.mul_le_mul_left _ (by omega)
    _ = 131072 * (2 * s + 3) + mult * (2 * s + 3) := by ring
    _ ≤ mult * (131072 * s) + mult * (2 * s + 3) := Nat.add_le_add_right key _
    _ = mult * (131072 * s + (2 * s + 3)) := by ring

/-- yz-cumulative absorption, with `B = b + s`.
    sharp.(yz+all) = 1 + (2B+4)·(131072+delay);  rational.(yz+all) = 131072·B + 2B + 5. -/
theorem sharp_absorbs_ysall_C1 (B delay mult : ℕ) (hB : 1 ≤ B)
    (hdm : delay ≤ mult) (hm6 : 6 ≤ mult) :
    1 + (2 * B + 4) * (131072 + delay) ≤ mult * (131072 * B + 2 * B + 5) := by
  have key : 1 + 131072 * (2 * B + 4) ≤ mult * (131072 * B) + mult := by
    have h6 : 6 * (131072 * B) + 6 ≤ mult * (131072 * B) + mult := by
      have := Nat.mul_le_mul_right (131072 * B) hm6
      omega
    have hB' : 262144 * B + 524289 ≤ 786432 * B + 6 := by
      have : (524288 : ℕ) ≤ 524288 * B := by
        calc (524288 : ℕ) = 524288 * 1 := by ring
          _ ≤ 524288 * B := Nat.mul_le_mul_left _ hB
      omega
    calc 1 + 131072 * (2 * B + 4) = 262144 * B + 524289 := by ring
      _ ≤ 786432 * B + 6 := hB'
      _ = 6 * (131072 * B) + 6 := by ring
      _ ≤ mult * (131072 * B) + mult := h6
  calc
    1 + (2 * B + 4) * (131072 + delay) ≤ 1 + (2 * B + 4) * (131072 + mult) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
    _ = (1 + 131072 * (2 * B + 4)) + mult * (2 * B + 4) := by ring
    _ ≤ (mult * (131072 * B) + mult) + mult * (2 * B + 4) :=
      Nat.add_le_add_right key _
    _ = mult * (131072 * B + 2 * B + 5) := by ring

/-- total-cumulative absorption; the `yz` shape with `A = a + b + s`. -/
theorem sharp_absorbs_total_C1 (A delay mult : ℕ) (hA : 1 ≤ A)
    (hdm : delay ≤ mult) (hm6 : 6 ≤ mult) :
    1 + (2 * A + 4) * (131072 + delay) ≤ mult * (131072 * A + 2 * A + 5) :=
  sharp_absorbs_ysall_C1 A delay mult hA hdm hm6

/-! ### The multiplicity 1..5 route fits inside `mult` copies of the coordinate

`weightedCost` is linear in the *raw* flag components, so the moving route's flag
part must be dominated componentwise (not just cumulatively). -/

/-- The single numeric gate: in the hybrid branch `r + 2 ≤ y` we have `b ≥ 1`, so
any error cap below `131076` passes. -/
theorem hybridC1Gate_of_le (t y r errorCap : Nat) (hb : r + 2 ≤ y)
    (hcap : errorCap + 1 ≤ 131076) :
    errorCap + 1 ≤ (cellHybridCoordinateC1 t y r).yz :=
  rationalGate_of_le t y r errorCap hb hcap

/-! ### The C1 cell cost -/

end
end ProximityPrize.SubmissionLower.LocatorHybridCellsC1
end PackedLocator_LocatorHybridCellsC1

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier49 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridTailProvider. -/
section PackedLocator_LocatorHybridTailProvider
/-
LOCATOR HYBRID TAIL PROVIDER (port of ContactHybridTailProvider6751Research, pr359).

Covers the `r + 2 ≤ y` ("hybrid second-surface") branch of `cellRegularCost`.
The delayed branch keeps the Locator's reduced-tail discharge (Q2.lean) verbatim.

§0 defines the *bounded* provider `HybridTailMultiplicityProvider`: it is
pr359's refactored `DelayedTailMultiplicityProvider` (an extra
`divisorBound` optParam and a single field `cost_sum_le : ∑ cost ≤ divisorBound`
in place of `cost_le`/`divisor_le`), kept as a NEW structure so that the
existing B3.lean structure and its constructors (Q2.lean, GZ.lean) stay
untouched.  `stage_card_le_divisorBound` is the generalized
`stage_card_le_flagMixed`.

Conclusion shape of §3:

  Nonempty (HybridTailMultiplicityProvider
    (tailFlag1 := cellSharpTail t y r) (tailFlag2 := cellHybridCoordinate t y r) S
    (flagMixed flag (cellSharpTail t y r) (cellHybridCoordinate t y r)
      + (w + 1) * flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r)))

Caller-side obligations (discharged in LocatorHybridTailRealization.lean):
  B            : sharp unit family (activeNestedUnitFamily on T1 in the sharp
                 flag DIRECTLY — no congruent-cut transport)
  budget/hcost/hmovingSum : outputs of exists_firstTail_cut_budgets
  hresultants  : sharp-family certificate (activeNestedWeightedCertificate on T1)
  htangent     : the tangent count vs B.yzCost
  htangentGate / hrationalGate : numeric gates errors+1 ≤ hybrid.yz / rational.yz
                 (rational.yz = 131074·b + 2 ≥ 131076 whenever b ≥ 1, i.e. r+2 ≤ y).
-/
namespace ProximityPrize.SubmissionLower.LocatorHybridTailProvider
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

/-! ### 0. The bounded provider (pr359's refactored DelayedTailMultiplicityProvider) -/

section BoundedProvider
variable {K0 Omega Iota : Type} [Field K0] [Field Omega] [IsAlgClosed Omega]
  {phi : Polynomial K0 →+* Omega} {Gamma0 : Finset K0} {x0 : Iota → K0}
  {pchar errorCap d : ℕ} [CharP Omega pchar]
  {flag0 tailFlag1 tailFlag2 : FlagDegree}
  {support0 : RCN275.ResidualSupportParameters}

structure HybridTailMultiplicityProvider
    (S : ResidualStage phi Gamma0 x0 pchar errorCap flag0 d support0)
    (divisorBound : optParam ℕ (flagMixed flag0 tailFlag1 tailFlag2)) where
  budgetFamily : PrimeFlagBudgetFamily
    (G := S.G) (T := globalTailCut phi S.F (d + 1))
    (H := regularitySurface phi S.F) flag0 tailFlag1
  multiplicity : FirstTailComponent S → ℕ
  cost : FirstTailComponent S → ℕ
  one_le_multiplicity : ∀ C, 1 ≤ multiplicity C
  tangentYZGate : errorCap + 1 ≤ tailFlag2.yz
  cost_sum_le : (∑ C, cost C) ≤ divisorBound
  componentBound : ∀ C,
    (componentSeeds Omega S.G (globalTailCut phi S.F (d + 1))
      (regularitySurface phi S.F) Gamma0
      (selectedPoint phi S.selected) C).card ≤ cost C
  dichotomy : ∀ C,
    (∃ delay, 1 ≤ delay ∧ delay ≤ multiplicity C ∧
      globalTailCut phi S.F (d + 1 + delay) ∉ C.1) ∨
    ((∀ delay, globalTailCut phi S.F (d + 1 + delay) ∈ C.1) ∧
      (componentSeeds Omega S.G (globalTailCut phi S.F (d + 1))
        (regularitySurface phi S.F) Gamma0
        (selectedPoint phi S.selected) C).card ≤
          (errorCap + 1) * budgetFamily.yzCost C)

/-- The generalized `stage_card_le_flagMixed`: any bounded provider bounds the
seed count by its `divisorBound`. -/
theorem stage_card_le_divisorBound
    (S : ResidualStage phi Gamma0 x0 pchar errorCap flag0 d support0)
    {divisorBound : ℕ}
    (P : HybridTailMultiplicityProvider
      (tailFlag1 := tailFlag1) (tailFlag2 := tailFlag2) S divisorBound) :
    Gamma0.card ≤ divisorBound := by
  classical
  let T1 := globalTailCut phi S.F (d + 1)
  let H := regularitySurface phi S.F
  let point := selectedPoint phi S.selected
  have hG : ∀ gamma ∈ Gamma0,
      MvPolynomial.eval (point gamma) S.G = 0 := S.on_component
  have hT1 : ∀ gamma ∈ Gamma0,
      MvPolynomial.eval (point gamma) T1 = 0 := by
    intro gamma hgamma
    exact selected_globalTailCut_zero phi S.F S.selected gamma d
      (S.degree_le gamma hgamma) (S.solution gamma hgamma)
  have hH : ∀ gamma ∈ Gamma0,
      MvPolynomial.eval (point gamma) H ≠ 0 := by
    intro gamma hgamma
    exact selectedPoint_evaluation phi S.selected gamma
      (MvPolynomial.pderiv (2:Fin 4) S.F) |>.symm ▸ S.regular gamma hgamma
  have hcover : Gamma0.card ≤
      ∑ C : RegularComponent Omega S.G T1 H,
        (componentSeeds Omega S.G T1 H Gamma0 point C).card :=
    card_le_sum_componentSeeds Omega S.G T1 H Gamma0 point hG hT1 hH
  calc
    Gamma0.card ≤ ∑ C : RegularComponent Omega S.G T1 H,
        (componentSeeds Omega S.G T1 H Gamma0 point C).card := hcover
    _ ≤ ∑ C : RegularComponent Omega S.G T1 H, P.cost C :=
      Finset.sum_le_sum (fun C _ ↦ P.componentBound C)
    _ ≤ divisorBound := P.cost_sum_le

end BoundedProvider

variable {K I : Type} [Field K]
local instance  _root_.ProximityPrize.SubmissionLower.LocatorHybridTailProvider.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.LocatorHybridTailProvider.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable {stageErrorCap : ℕ}

/-! ### 1. L1 — the delayed cut lands in mult • hybrid (mult ≥ 2)

Direct containment (no mod-G reduction): the (w+1+delay)-th tail cut lies in the
sharp flag at degree w+1+delay, and the three cumulative absorptions of
LocatorHybridCells push that into `mult • cellHybridCoordinate` whenever
1 ≤ delay ≤ mult and 2 ≤ mult. -/

/-! ### 2. L2 — the multiplicity-1 moving count

For a component whose (w+2)-cut is proper, the seeds are bounded by
wc(rational) + (w+1)·movingCost, via the filteredCut decomposition of the (w+2)
cut and the MovingPoleBudget zero bound at C := center, k := w+1. -/

/-! ### 3. The hybrid provider from a local DVR family -/

end
end ProximityPrize.SubmissionLower.LocatorHybridTailProvider
end PackedLocator_LocatorHybridTailProvider

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier50 : True := by trivial
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier51 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorFactorReplacement. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier52 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorDerivativeChain. -/
section PackedLocator_LocatorDerivativeChain

/-!
# Derivative chain for singular seeds

For an irreducible factor `F` with positive `R`-degree, a seed at which both `F`
and `∂_R F` specialise to zero is either a regular seed of some iterated
`R`-derivative `∂_R^j F` (`1 ≤ j`), or a zero of the `R`-free polynomial
`∂_R^m F` obtained when the `R`-degree is exhausted.  Regular seeds of a
derivative are counted by the coprime pair `(∂_R^j F, F)`; the `R`-free tail is
counted by the singular-seed bound at slope cap `1`, whose characteristic gate is
`2 * ((D - 1) / w) * L < p`.
-/

namespace ProximityPrize.SubmissionLower.LocatorDerivativeChain

open scoped Classical BigOperators
open RCN174 RCN319 RCN081 RCN082 RCN167 RCN286 RCN052 RCN260 RCN318 RCN267 RCN313 RCN135 RCN138 RCN136 RCN238 RCN293 RCN231 RCN243

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

variable {K : Type} [Field K]
local instance  _root_.ProximityPrize.SubmissionLower.LocatorDerivativeChain.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.LocatorDerivativeChain.instStrongNormalizationMonoidMvPolynomialFinOfNatNat_proximityPrize : StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

/-- Iterated `R`-derivative. -/
def dR (j : ℕ) (F : MvPolynomial (Fin 4) K) : MvPolynomial (Fin 4) K :=
  (MvPolynomial.pderiv (2 : Fin 4))^[j] F

@[simp] theorem dR_zero (F : MvPolynomial (Fin 4) K) : dR 0 F = F := rfl

theorem dR_succ (j : ℕ) (F : MvPolynomial (Fin 4) K) :
    dR (j + 1) F = MvPolynomial.pderiv (2 : Fin 4) (dR j F) := by
  unfold dR
  exact Function.iterate_succ_apply' _ _ _

/-- The `R`-derivative stays inside every coefficient box. -/
theorem pderiv_R_mem_box (Q : MvPolynomial (Fin 4) K) (D w L s : ℕ)
    (hbox : Q ∈ globalCoefficientBox K D w L s) :
    MvPolynomial.pderiv (2 : Fin 4) Q ∈ globalCoefficientBox K D w L s := by
  intro d hd
  have hmem := support_before_pderiv (2 : Fin 4) Q d hd
  obtain ⟨ht, hs, hc⟩ := hbox hmem
  have h0 : ((d + Finsupp.single (2 : Fin 4) 1 : Fin 4 →₀ ℕ) : Fin 4 → ℕ) 0 = d 0 := by
    simp [Finsupp.single_apply]
  have h1 : ((d + Finsupp.single (2 : Fin 4) 1 : Fin 4 →₀ ℕ) : Fin 4 → ℕ) 1 = d 1 := by
    simp [Finsupp.single_apply]
  have h2 : ((d + Finsupp.single (2 : Fin 4) 1 : Fin 4 →₀ ℕ) : Fin 4 → ℕ) 2 = d 2 + 1 := by
    simp [Finsupp.single_apply]
  have h3 : ((d + Finsupp.single (2 : Fin 4) 1 : Fin 4 →₀ ℕ) : Fin 4 → ℕ) 3 = d 3 := by
    simp [Finsupp.single_apply]
  simp only [h0, h1, h2, h3] at ht hs hc
  have hw1 : (w - 1) * d 2 ≤ (w - 1) * (d 2 + 1) := Nat.mul_le_mul_left _ (by omega)
  exact ⟨by omega, by omega, by omega⟩

theorem dR_mem_box (j : ℕ) (Q : MvPolynomial (Fin 4) K) (D w L s : ℕ)
    (hbox : Q ∈ globalCoefficientBox K D w L s) :
    dR j Q ∈ globalCoefficientBox K D w L s := by
  induction j with
  | zero => simpa using hbox
  | succ k ih =>
      rw [dR_succ]
      exact pderiv_R_mem_box _ D w L s ih

theorem dR_R_degree_le (j : ℕ) (F : MvPolynomial (Fin 4) K) :
    (dR j F).degreeOf 2 ≤ F.degreeOf 2 - j := by
  induction j with
  | zero => simp
  | succ k ih =>
      rw [dR_succ]
      have h := pderiv_same_degree_bound (2 : Fin 4) (dR k F) (F.degreeOf 2 - k) ih
      omega

/-- A box with slope cap `s` and no `R`-dependence lies in the slope-`1` box. -/
theorem mem_box_slope_one (Q : MvPolynomial (Fin 4) K) (D w L s : ℕ)
    (hbox : Q ∈ globalCoefficientBox K D w L s) (hR : Q.degreeOf 2 = 0) :
    Q ∈ globalCoefficientBox K D w L 1 := by
  intro d hd
  obtain ⟨ht, _, hc⟩ := hbox hd
  have hd2 : d 2 ≤ Q.degreeOf 2 := MvPolynomial.monomial_le_degreeOf (2 : Fin 4) hd
  exact ⟨ht, by omega, hc⟩

/-- Exhaustion index of the `R`-degree along the derivative chain. -/
theorem exists_dR_R_degree_zero (F : MvPolynomial (Fin 4) K) :
    ∃ j, (dR j F).degreeOf 2 = 0 :=
  ⟨F.degreeOf 2, Nat.eq_zero_of_le_zero (by simpa using dR_R_degree_le (F.degreeOf 2) F)⟩

def chainLength (F : MvPolynomial (Fin 4) K) : ℕ :=
  Nat.find (exists_dR_R_degree_zero F)

theorem chainLength_spec (F : MvPolynomial (Fin 4) K) :
    (dR (chainLength F) F).degreeOf 2 = 0 :=
  Nat.find_spec (exists_dR_R_degree_zero F)

theorem chainLength_le (F : MvPolynomial (Fin 4) K) : chainLength F ≤ F.degreeOf 2 :=
  Nat.find_min' (exists_dR_R_degree_zero F)
    (Nat.eq_zero_of_le_zero (by simpa using dR_R_degree_le (F.degreeOf 2) F))

theorem dR_R_degree_pos_of_lt_chainLength (F : MvPolynomial (Fin 4) K) (j : ℕ)
    (hj : j < chainLength F) : 0 < (dR j F).degreeOf 2 :=
  Nat.pos_of_ne_zero (Nat.find_min (exists_dR_R_degree_zero F) hj)

theorem chainLength_pos (F : MvPolynomial (Fin 4) K) (hpos : 0 < F.degreeOf 2) :
    1 ≤ chainLength F := by
  by_contra h
  have h0 : chainLength F = 0 := by omega
  have := chainLength_spec F
  rw [h0] at this
  simp at this
  omega

theorem dR_ne_zero (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0) (p : ℕ) [CharP K p]
    (hsmall : F.degreeOf 2 < p) (j : ℕ) (hj : j ≤ chainLength F) : dR j F ≠ 0 := by
  induction j with
  | zero => simpa using hF
  | succ k ih =>
      rw [dR_succ]
      have hk : k < chainLength F := by omega
      have hpos := dR_R_degree_pos_of_lt_chainLength F k hk
      have hle : (dR k F).degreeOf 2 < p := by
        have := dR_R_degree_le k F
        omega
      exact R_derivative_nonzero (dR k F) p hpos hle




/-- A regular seed of `G` is a regular seed of one of its irreducible factors
of positive `R`-degree. -/
theorem exists_regular_positive_factor (G : MvPolynomial (Fin 4) K) (hG : G ≠ 0)
    (P : Polynomial K) (γ : K) (hreg : RegularSolution G P γ) :
    ∃ F' ∈ positiveRFactors G, RegularSolution F' P γ := by
  classical
  let ψ : MvPolynomial (Fin 4) K →+* Polynomial K := (specialization K P γ).toRingHom
  obtain ⟨F', hmem, hzero⟩ := exists_normalized_factor_of_map_zero ψ G hG hreg.1
  have hdiv : F' ∣ G := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hmem
  have hregF' : ψ (MvPolynomial.pderiv (2 : Fin 4) F') ≠ 0 :=
    factor_derivative_regular_at_zero ψ G F' hdiv hzero hreg.2
  have hpos : 0 < F'.degreeOf 2 := by
    apply Nat.pos_of_ne_zero
    intro hzeroDeg
    apply hregF'
    rw [pderiv_zero_of_degree_zero (2 : Fin 4) F' hzeroDeg, map_zero]
  have hactive : F' ∈ activeFactors G := by
    unfold activeFactors
    exact Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hmem, by omega⟩
  refine ⟨F', ?_, hzero, hregF'⟩
  unfold positiveRFactors
  exact Finset.mem_filter.mpr ⟨hactive, hpos⟩

/-- Every seed of `Q` is a seed of an active irreducible factor of `Q`. -/
theorem exists_active_factor_of_solution (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (P : Polynomial K) (γ : K) (hsol : specialization K P γ Q = 0) :
    ∃ F ∈ activeFactors Q, specialization K P γ F = 0 := by
  classical
  let φ := polynomialEmbedding K
  let v : Fin 3 → GenericField K := fun i => initialPoint K P γ i.succ
  have heval (F : MvPolynomial (Fin 4) K) :
      MvPolynomial.eval v (surfaceMap φ F) = 0 ↔ specialization K P γ F = 0 := by
    simpa only [canonical_geometricSurfaceMap] using
      (actual_generic_initial_zero_iff K P γ F)
  obtain ⟨F, hF, hz⟩ := exists_active_factor_of_surface_zero φ
    (polynomialEmbedding_injective K) Q hQ v ((heval Q).mpr hsol)
  exact ⟨F, hF, (heval F).mp hz⟩

theorem irreducible_not_dvd_dR (F : MvPolynomial (Fin 4) K) (hF : Irreducible F)
    (p : ℕ) [CharP K p] (hpos : 0 < F.degreeOf 2) (hsmall : F.degreeOf 2 < p)
    (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ chainLength F) : ¬ F ∣ dR j F := by
  intro hdiv
  have hne : dR j F ≠ 0 := dR_ne_zero F hF.ne_zero p hsmall j hj
  have hle := degreeOf_le_of_dvd (2 : Fin 4) F (dR j F) hdiv hne
  have hdeg := dR_R_degree_le j F
  omega

theorem isRelPrime_dR (F : MvPolynomial (Fin 4) K) (hF : Irreducible F)
    (p : ℕ) [CharP K p] (hpos : 0 < F.degreeOf 2) (hsmall : F.degreeOf 2 < p)
    (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ chainLength F) : IsRelPrime (dR j F) F :=
  (hF.isRelPrime_iff_not_dvd.mpr (irreducible_not_dvd_dR F hF p hpos hsmall j hj1 hj)).symm

section Counting

variable {Iota : Type}
local instance  _root_.ProximityPrize.SubmissionLower.LocatorDerivativeChain.instDecidableEq_proximityPrize_1 : DecidableEq Iota := Classical.decEq Iota

/-- Seeds that are regular for `dR j F` and at which `F` vanishes. -/
def chainSeeds (F : MvPolynomial (Fin 4) K) (j : ℕ)
    (selected : K → Polynomial K) (Gamma : Finset K) : Finset K :=
  Gamma.filter fun γ => RegularSolution (dR j F) (selected γ) γ ∧
    specialization K (selected γ) γ F = 0

/-- Seeds of the `R`-free tail of the chain of `F`. -/
def tailSeeds (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) : Finset K :=
  Gamma.filter fun γ => specialization K (selected γ) γ (dR (chainLength F) F) = 0

/-- Product of the `R`-free active factors of `Q`. -/
def rfreeProduct (Q : MvPolynomial (Fin 4) K) : MvPolynomial (Fin 4) K :=
  ∏ F ∈ (activeFactors Q).filter (fun F => F.degreeOf 2 = 0), F

def rfreeSeeds (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) : Finset K :=
  Gamma.filter fun γ => specialization K (selected γ) γ (rfreeProduct Q) = 0

theorem tailSeeds_subset (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) :
    tailSeeds F selected Gamma ⊆ Gamma := Finset.filter_subset _ _

theorem rfreeSeeds_subset (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) :
    rfreeSeeds Q selected Gamma ⊆ Gamma := Finset.filter_subset _ _

theorem rfreeProduct_dvd (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) :
    rfreeProduct Q ∣ Q := by
  classical
  unfold rfreeProduct
  exact (Finset.prod_dvd_prod_of_subset _ (activeFactors Q) id
    (Finset.filter_subset _ _)).trans (activeFactors_product_dvd Q hQ)

theorem rfreeProduct_ne_zero (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) :
    rfreeProduct Q ≠ 0 :=
  ne_zero_of_dvd_ne_zero hQ (rfreeProduct_dvd Q hQ)

theorem rfreeProduct_R_degree (Q : MvPolynomial (Fin 4) K) :
    (rfreeProduct Q).degreeOf 2 = 0 := by
  classical
  unfold rfreeProduct
  apply Nat.eq_zero_of_le_zero
  refine (MvPolynomial.degreeOf_prod_le _ _ _).trans ?_
  apply Nat.le_of_eq
  apply Finset.sum_eq_zero
  intro F hF
  exact (Finset.mem_filter.mp hF).2




/-- The chain seeds at stage `j` are covered by the regular pair seeds of
`(dR j F, F)`. -/
theorem chainSeeds_subset_regularPairSeeds (F : MvPolynomial (Fin 4) K) (j : ℕ)
    (hne : dR j F ≠ 0) (selected : K → Polynomial K) (Gamma : Finset K) :
    chainSeeds F j selected Gamma ⊆
      Finset.univ.biUnion fun F' : RegularIndex (dR j F) =>
        regularPairSeeds (dR j F) F selected Gamma F' := by
  classical
  intro γ hγ
  obtain ⟨hγΓ, hreg, hFzero⟩ := Finset.mem_filter.mp hγ
  obtain ⟨F', hF'mem, hF'reg⟩ :=
    exists_regular_positive_factor (dR j F) hne (selected γ) γ hreg
  apply Finset.mem_biUnion.mpr ⟨⟨F', hF'mem⟩, Finset.mem_univ _, ?_⟩
  exact Finset.mem_filter.mpr ⟨hγΓ, hF'reg, hFzero⟩

/-- Seeds of a nonzero `R`-free polynomial in the slope-`1` box are bounded by
the singular-seed count of the slope-`1` Tight parameters. -/
theorem rfree_seed_count_le
    (S : TightParameters) (J : MvPolynomial (Fin 4) K) (hJ : J ≠ 0)
    (p : ℕ) [CharP K p]
    (hbox : J ∈ globalCoefficientBox K S.D S.w S.L S.s) (hJR : J.degreeOf 2 = 0) (hSs : S.s = 1)
    (hp : 1 < p) (hw : 1 ≤ S.w) (hchar : S.w < p) (hDw : S.w < S.kappa * S.D)
    (hj : 1 ≤ S.algebraicCap) (hjYSmall : S.implicitYCap < p) (hjZSmall : S.algebraicCap < p)
    (hmixedSmall : 2 * S.implicitYCap * S.algebraicCap < p)
    (hwa : S.w < S.a) (han : S.a ≤ S.n)
    (selected : K → Polynomial K) (Delta : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K) (hinj : Set.InjOn x nodes)
    (hnodes : nodes.card = S.n)
    (hdegree : ∀ γ ∈ Delta, (selected γ).natDegree ≤ S.w)
    (hsol : ∀ γ ∈ Delta, specialization K (selected γ) γ J = 0)
    (hagreement : ∀ γ ∈ Delta, S.a ≤ (nodes.filter (fun i =>
      (selected γ).eval (x i) = u0 i + γ * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Delta S.w S.errors) :
    Delta.card ≤ S.countCap := by
  classical
  have hs1 : 1 ≤ S.s := by omega
  have hsp : S.s < p := by omega
  have hcover := card_le_regular_sum_add_singular J J hJ S.D S.w S.L S.s p
    hs1 hsp hw (by simpa [TightParameters.kappa] using hDw)
    (by simpa [TightParameters.algebraicCap, TightParameters.kappa] using hj)
    (by simpa [TightParameters.algebraicCap, TightParameters.kappa] using hjZSmall)
    hbox selected Delta hsol hsol
  have hregZero : (∑ F' : RegularIndex J, (regularPairSeeds J J selected Delta F').card) = 0 := by
    apply Finset.sum_eq_zero
    intro F' _
    exfalso
    obtain ⟨_, hdvd, hpos⟩ := positiveRFactors_spec J F'.1 F'.2
    have := degreeOf_le_of_dvd (2 : Fin 4) F'.1 J hdvd hJ
    omega
  have hsingularOld := RCN292.TightParameters.singularSeeds_count_le_countCap
    S J hJ hbox hs1 hsp hw hchar hDw hj hjYSmall hjZSmall hmixedSmall
    hwa han selected Delta nodes x u0 u1 hinj hnodes hdegree hagreement hnoPencil
  have hsingular : (RCN052.singularSeeds J selected Delta).card ≤ S.countCap := by
    change (RCN291.singularSeeds J selected Delta).card ≤ S.countCap
    exact hsingularOld
  omega

end Counting

section Assembly

variable {Iota : Type}
local instance  _root_.ProximityPrize.SubmissionLower.LocatorDerivativeChain.instDecidableEq_proximityPrize_2 : DecidableEq Iota := Classical.decEq Iota

end Assembly

end

end ProximityPrize.SubmissionLower.LocatorDerivativeChain
end PackedLocator_LocatorDerivativeChain

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier53 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorFixedChain. -/
section PackedLocator_LocatorFixedChain
/-!
# Derivative chain on the fixed stage

`LocatorDerivativeChain.residual_chain_count_le` counts the seeds of a
polynomial `Q` by its regular seeds (through a coprime partner `T`), the
derivative-chain pairs `(∂_R^j F, F)` of its positive-slope factors, and the
R-free tails.  On the fixed stage the regular seeds of the common divisor `H`
are already charged by the phase certificate through
`LocatorFixedConsumer.initial_A_regularSeeds_sum_le`, so this file restates that
lemma with `T := Q` and the regular block replaced by a hypothesis: no second
polynomial of the selected pair is needed.  The chain pairs are coprime by the
R-degree drop (`isRelPrime_dR`) and, as in `chainSeeds_card_le`, the
differentiated left factor only needs slope `s - 1`; the tails use
`card_le_regular_sum_add_singular J J`.  The only new mathematics is the
inclusion `regularPairSeeds Q Q ⊆ regularSeeds Q`.
-/

namespace ProximityPrize.SubmissionLower.LocatorFixedChain

open scoped Classical BigOperators
open RCN174 RCN319 RCN081 RCN082 RCN167 RCN286 RCN052 RCN260 RCN318 RCN267 RCN313 RCN135
  RCN138 RCN136 RCN238 RCN293 RCN231 RCN243 RCN140 LocatorDerivativeChain

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

variable {K : Type} [Field K]
local instance  _root_.ProximityPrize.SubmissionLower.LocatorFixedChain.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.LocatorFixedChain.instStrongNormalizationMonoidMvPolynomialFinOfNatNat_proximityPrize : StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
variable {Iota : Type}
local instance  _root_.ProximityPrize.SubmissionLower.LocatorFixedChain.instDecidableEq_proximityPrize_1 : DecidableEq Iota := Classical.decEq Iota

/-- With `T := Q`, the regular pair seeds of `(Q, Q)` are the regular seeds of the
factors of `Q` (RCN140.regularSeeds, the set the grid bounds by `bound`). -/
theorem regularPairSeeds_self_subset (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) (F : RegularIndex Q) :
    regularPairSeeds Q Q selected Gamma F ⊆ regularSeeds Q selected Gamma F := by
  intro γ hγ
  simp only [regularPairSeeds, regularSeeds, Finset.mem_filter] at hγ ⊢
  exact ⟨hγ.1, hγ.2.1⟩

end

end ProximityPrize.SubmissionLower.LocatorFixedChain
end PackedLocator_LocatorFixedChain

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier54 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorFixedConsumer. -/

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridTailProviderC1. -/
section PackedLocator_LocatorHybridTailProviderC1
/-
LOCATOR HYBRID TAIL PROVIDER — C1 VARIANT.

Same architecture as `LocatorHybridTailProvider`, with the C1 trade:

  * the FLAG route (charge `mult · weightedCost hybrid`) is restricted to
    components of local multiplicity at least 6, which lets the coordinate drop
    from `cellRational + ⟨0,(w+1)/2,3·((w+1)/2)⟩` all the way to `cellRational`;
  * components of multiplicity 1..5 go through the MOVING engine at cut level
    `w + mult` (the dichotomy's `delay` satisfies `delay ≤ mult`), charging
    `weightedCost (cellRationalAt (w + mult)) + (w + mult) · movingCost`;
  * the moving term's outer factor therefore becomes `w + 5` instead of `w + 1`.

The structure `HybridTailMultiplicityProvider` and `stage_card_le_divisorBound`
are reused unchanged from `LocatorHybridTailProvider`.
-/
namespace ProximityPrize.SubmissionLower.LocatorHybridTailProviderC1
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

variable {K I : Type} [Field K]
local instance  _root_.ProximityPrize.SubmissionLower.LocatorHybridTailProviderC1.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.LocatorHybridTailProviderC1.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable {stageErrorCap : ℕ}

/-! ### 0. Arithmetic helpers -/

/-- `sharp_absorbs_total_C1` in the `(a, b + s)` shape used by the containment proof. -/
theorem sharp_absorbs_total_abs (a B delay mult : ℕ) (hA : 1 ≤ a + B)
    (hdm : delay ≤ mult) (hm6 : 6 ≤ mult) :
    1 + (2 * a + 2 * B + 4) * (131072 + delay) ≤
      mult * (131074 * a + 131072 * B + 2 * B + 5) := by
  have h := sharp_absorbs_total_C1 (a + B) delay mult hA hdm hm6
  have e1 : 2 * (a + B) + 4 = 2 * a + 2 * B + 4 := by ring
  have e2 : 131072 * (a + B) + 2 * (a + B) + 5 =
      131074 * a + 131072 * B + 2 * B + 5 := by ring
  rw [e1, e2] at h
  exact h

/-! ### 1. L1 (C1) — the delayed cut lands in `mult • cellRational` for `mult ≥ 6` -/

theorem laterTail_in_hybridFlagC1
    (t y r : Nat) (hr3 : 3 ≤ r) (_hry : r < y)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (delay mult : ℕ) (_hd : 1 ≤ delay) (hdm : delay ≤ mult) (hm6 : 6 ≤ mult) :
    PolynomialInFlag (mult • cellHybridCoordinateC1 t y r)
      (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)) := by
  have hs1 : 1 ≤ cellS r := by simp only [cellS]; omega
  have hB1 : 1 ≤ cellB y r + cellS r := by omega
  have hA1 : 1 ≤ cellA t y + (cellB y r + cellS r) := by omega
  have hsy : (cellSupport t y r).s < (cellSupport t y r).ys := by
    simp only [cellSupport, cellA, cellB, cellS, RCN198.support]
    omega
  have hsharp : PolynomialInFlag
      (sharpResidualAgreementFlag (cellSupport t y r) (w + 1 + delay))
      (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)) := by
    exact surfaceMap_agreement_in_sharp_flag hsy (polynomialEmbedding K)
      ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
      (w + 1 + delay) (tailSelector (w + 1 + delay)) 0 0 0
  intro exponent hexp
  have h := hsharp exponent hexp
  obtain ⟨hall, hys, htot⟩ := h
  have hallV : (sharpResidualAgreementFlag (cellSupport t y r)
      (w + 1 + delay)).all = (2 * cellS r + 3) * (131072 + delay) := by
    have e1 : ∀ m : ℕ, 2 * (m + 2) - 1 = 2 * m + 3 := fun m => by omega
    have e2 : ∀ m2 m3 : ℕ,
        2 * (m2 + m3 + 3 - (m3 + 2)) - 1 = 2 * m2 + 1 := fun m2 m3 => by omega
    have e3 : ∀ m1 m2 m3 : ℕ,
        m1 + m2 + m3 + 3 - (m2 + m3 + 3) = m1 := fun m1 m2 m3 => by omega
    simp only [sharpResidualAgreementFlag, sharpAgreementDirection,
      cellSupport, RCN198.support, w, e3, e2, e1]
  have hysV : (sharpResidualAgreementFlag (cellSupport t y r)
        (w + 1 + delay)).yz +
      (sharpResidualAgreementFlag (cellSupport t y r)
        (w + 1 + delay)).all =
      1 + (2 * (cellB y r + cellS r) + 4) * (131072 + delay) := by
    have e1 : ∀ m : ℕ, 2 * (m + 2) - 1 = 2 * m + 3 := fun m => by omega
    have e2 : ∀ m2 m3 : ℕ,
        2 * (m2 + m3 + 3 - (m3 + 2)) - 1 = 2 * m2 + 1 := fun m2 m3 => by omega
    have e3 : ∀ m1 m2 m3 : ℕ,
        m1 + m2 + m3 + 3 - (m2 + m3 + 3) = m1 := fun m1 m2 m3 => by omega
    simp only [sharpResidualAgreementFlag, sharpAgreementDirection,
      cellSupport, RCN198.support, w, e3, e2, e1]
    all_goals ring
  have htotV : (sharpResidualAgreementFlag (cellSupport t y r)
        (w + 1 + delay)).zOnly +
      (sharpResidualAgreementFlag (cellSupport t y r)
        (w + 1 + delay)).yz +
      (sharpResidualAgreementFlag (cellSupport t y r)
        (w + 1 + delay)).all =
      1 + (2 * cellA t y + 2 * (cellB y r + cellS r) + 4) *
        (131072 + delay) := by
    have e1 : ∀ m : ℕ, 2 * (m + 2) - 1 = 2 * m + 3 := fun m => by omega
    have e2 : ∀ m2 m3 : ℕ,
        2 * (m2 + m3 + 3 - (m3 + 2)) - 1 = 2 * m2 + 1 := fun m2 m3 => by omega
    have e3 : ∀ m1 m2 m3 : ℕ,
        m1 + m2 + m3 + 3 - (m2 + m3 + 3) = m1 := fun m1 m2 m3 => by omega
    simp only [sharpResidualAgreementFlag, sharpAgreementDirection,
      cellSupport, RCN198.support, w, e3, e2, e1]
    all_goals ring
  have hhallV : (mult • cellHybridCoordinateC1 t y r).all =
      mult * (131072 * cellS r + (2 * cellS r + 3)) := by
    simp only [cellHybridCoordinateC1, cellRational, cellDirection,
      RCN206.directionFlag, nsmul_all, w]
  have hhysV : (mult • cellHybridCoordinateC1 t y r).yz +
      (mult • cellHybridCoordinateC1 t y r).all =
      mult * (131072 * (cellB y r + cellS r) +
        2 * (cellB y r + cellS r) + 5) := by
    simp only [cellHybridCoordinateC1, cellRational, cellDirection,
      RCN206.directionFlag, nsmul_yz, nsmul_all, w]
    ring
  have hhtotV : (mult • cellHybridCoordinateC1 t y r).zOnly +
      (mult • cellHybridCoordinateC1 t y r).yz +
      (mult • cellHybridCoordinateC1 t y r).all =
      mult * (131074 * cellA t y + 131072 * (cellB y r + cellS r) +
        2 * (cellB y r + cellS r) + 5) := by
    simp only [cellHybridCoordinateC1, cellRational, cellDirection,
      RCN206.directionFlag, nsmul_zOnly, nsmul_yz, nsmul_all, w]
    ring
  refine ⟨?_, ?_, ?_⟩
  · exact (hallV ▸ hall).trans (hhallV ▸
      sharp_absorbs_all_C1 (cellS r) delay mult hs1 hdm hm6)
  · exact (hysV ▸ hys).trans (hhysV ▸
      sharp_absorbs_ysall_C1 (cellB y r + cellS r) delay mult hB1 hdm hm6)
  · exact (htotV ▸ htot).trans (hhtotV ▸
      sharp_absorbs_total_abs (cellA t y) (cellB y r + cellS r) delay mult
        hA1 hdm hm6)

/-! ### 2. L2 (C1) — the moving count at an arbitrary delay -/

/-! ### 3. The C1 provider from a local DVR family -/

end
end ProximityPrize.SubmissionLower.LocatorHybridTailProviderC1
end PackedLocator_LocatorHybridTailProviderC1

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridTransportC2. -/
section PackedLocator_LocatorHybridTransportC2
/-
C2 FOUNDATION: transporting the unit family across a congruent cut, and the
moving-budget existence at an ARBITRARY first-tail flag.

C2 replaces the sharp first tail `sharpResidualAgreementFlag (support a b s) (w+1)`
by the reduced one `reducedResidualAgreementFlag (support a b s) (w+1)`, which is
strictly `Below` it (same `yz + all` and total, `all` smaller by `w + 1`).  The
reduced geometry lives over the components of `reducedFirstCut`, so it has to be
transported to the components of `globalTailCut (w+1)`.

`PrimeFlagBudgetFamily.ofCongruentCut` (B1.lean:108) already transports the
budget family, and `RCN335` uses it for the certificate.  What is missing for the
hybrid moving route is the transport of the whole `AdaptiveUnitProjectionFamily`,
because `exists_moving_pole_budget_family` needs the projections themselves in
order to produce a `MovingPoleBudget` whose costs agree with the family's.

§1 supplies that transport.  Every field of `AdaptiveUnitProjectionFamily`
mentions the component only through `C.1`, and `regularComponentEquiv h C` has
`.1 = C.1` definitionally, so the transport is a precomposition.

§2 generalises `RCN085.exists_firstTail_cut_budgets` (J3.lean:13) in the
first-tail flag.  J3 hard-codes the sharp flag purely to state the three
`z / yz / all` sum bounds through `mixed_sharp_le_padded`; the hybrid route uses
only the cost equalities and the moving sum, both of which are flag-agnostic.
-/

namespace ProximityPrize.SubmissionLower.LocatorHybridTransportC2
open scoped Classical BigOperators
open RCN136 RCN313 RCN238 RCN243 RCN264 RCN341 RCN046 RCN095 RCN199 RCN200 RCN207 RCN198 RCN203 RCN201 RCN275 RCN287 RCN086 RCN085
open RCN066 RCN135 RCN159 RCN074 RCN237 RCN244 RCN327 RCN263 RCN206 RCN002 RCN344
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 300000

/-! ### 1. Transport of a unit family across a congruent cut -/

section Transport
variable {Omega : Type} [Field Omega] [IsAlgClosed Omega]
  {G T T' H : MvPolynomial (Fin 3) Omega}

/-- An `AdaptiveUnitProjectionFamily` over the components of `T'` transports to
the components of `T` whenever `G ∣ T - T'`, for any choice of `base`.  All the
structure's fields see the component only through `C.1`, and the equivalence
preserves `C.1` definitionally. -/
def unitFamilyOfCongruentCut (h : G ∣ T - T')
    {base' : ∀ C : RegularComponent Omega G T' H, SeparableLiteralCoordinate C.1}
    {p q : FlagDegree}
    (U : AdaptiveUnitProjectionFamily base' p q)
    (base : ∀ C : RegularComponent Omega G T H, SeparableLiteralCoordinate C.1) :
    AdaptiveUnitProjectionFamily base p q where
  zProjection C := U.zProjection (regularComponentEquiv h C)
  yzProjection C := U.yzProjection (regularComponentEquiv h C)
  allProjection C := U.allProjection (regularComponentEquiv h C)
  zValue C := U.zValue (regularComponentEquiv h C)
  allTranscendental C := U.allTranscendental (regularComponentEquiv h C)
  zPole_eq C := U.zPole_eq (regularComponentEquiv h C)
  yzPole_eq C := U.yzPole_eq (regularComponentEquiv h C)
  allPole_eq C := U.allPole_eq (regularComponentEquiv h C)
  sum_zDegree_le := by
    refine Eq.trans_le ?_ U.sum_zDegree_le
    exact Fintype.sum_equiv (regularComponentEquiv h) _ _ (fun _ => rfl)
  sum_yzDegree_le := by
    refine Eq.trans_le ?_ U.sum_yzDegree_le
    exact Fintype.sum_equiv (regularComponentEquiv h) _ _ (fun _ => rfl)
  sum_allDegree_le := by
    refine Eq.trans_le ?_ U.sum_allDegree_le
    exact Fintype.sum_equiv (regularComponentEquiv h) _ _ (fun _ => rfl)

/-- The transported unit family carries exactly the costs of the transported
budget family, so the hybrid provider can use the two interchangeably. -/
theorem unitFamilyOfCongruentCut_costs (h : G ∣ T - T')
    {base' : ∀ C : RegularComponent Omega G T' H, SeparableLiteralCoordinate C.1}
    {p q : FlagDegree}
    (U : AdaptiveUnitProjectionFamily base' p q)
    (base : ∀ C : RegularComponent Omega G T H, SeparableLiteralCoordinate C.1)
    (C : RegularComponent Omega G T H) :
    (unitFamilyOfCongruentCut h U base).toPrimeFlagBudgetFamily.zCost C =
        (PrimeFlagBudgetFamily.ofCongruentCut h
          U.toPrimeFlagBudgetFamily).zCost C ∧
      (unitFamilyOfCongruentCut h U base).toPrimeFlagBudgetFamily.yzCost C =
        (PrimeFlagBudgetFamily.ofCongruentCut h
          U.toPrimeFlagBudgetFamily).yzCost C ∧
      (unitFamilyOfCongruentCut h U base).toPrimeFlagBudgetFamily.allCost C =
        (PrimeFlagBudgetFamily.ofCongruentCut h
          U.toPrimeFlagBudgetFamily).allCost C := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

end Transport

/-! ### 2. Moving budgets at an arbitrary first-tail flag -/

section Budgets
variable {K Ω E : Type} [Field K] [Field Ω] [IsAlgClosed Ω]
  [Field E] [IsAlgClosed E] [Algebra Ω E] [Algebra (RatFunc Ω) E]
  [IsScalarTower Ω (RatFunc Ω) E]

/-- `RCN085.exists_firstTail_cut_budgets` with the first-tail flag left free.
Only the cost equalities and the moving sum are produced; the three `z / yz /
all` sum bounds of J3 are exactly the parts that needed the sharp flag, and the
hybrid route never uses them. -/
theorem exists_firstTail_moving_budgets
    (φ : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K)
    (G T : MvPolynomial (Fin 3) Ω) (a b s w : ℕ) (hw : 1 ≤ w)
    (hT : T = globalTailCut φ F (w + 1))
    (hF : ResidualSupportData (support a b s) F) (flag : FlagDegree)
    (hG : G ≠ 0) (hdiv : G ∣ surfaceMap φ F) (hGflag : PolynomialInFlag flag G)
    (base : ∀ C : RegularComponent Ω G T (regularitySurface φ F),
      SeparableLiteralCoordinate C.1)
    (tailFlag : FlagDegree)
    (unit : AdaptiveUnitProjectionFamily base flag tailFlag)
    (pchar : ℕ) [CharP E pchar]
    (hmix : 2 * (flag.zOnly + flag.yz + flag.all) * (a + b + s + 4) < pchar) :
    ∃ budget : ∀ C : RegularComponent Ω G T (regularitySurface φ F),
      MovingPoleBudget C.1 (regularitySurface φ F) (surfaceMap φ (polyG K F)),
      (∀ C, (budget C).zCost = unit.toPrimeFlagBudgetFamily.zCost C ∧
        (budget C).yzCost = unit.toPrimeFlagBudgetFamily.yzCost C ∧
        (budget C).allCost = unit.toPrimeFlagBudgetFamily.allCost C) ∧
      (∑ C, (budget C).movingCost) ≤ flagMixed flag
        (RCN206.fiberFlag a b s)
        (center a b s + (w + 1) • RCN206.surfaceFlag a b s) := by
  classical
  obtain ⟨coeffs, cflags, heq, hcoeff, hclass⟩ := globalTailCut_certificate
    φ a b s F hF.coordinate_bounds.2.1 hF.ys_weight hF.total_weight w hw
  obtain ⟨hHflag, hGcontact⟩ := surfaceMap_HG_flags
    φ a b s F hF.coordinate_bounds.2.1 hF.ys_weight hF.total_weight
  have hderiv : regularitySurface φ F ∈
      Ideal.span ({G, MvPolynomial.pderiv (1 : Fin 3) G} :
        Set (MvPolynomial (Fin 3) Ω)) := by
    rw [regularitySurface, ← RCN267.surfaceMap_pderiv_R]
    exact RCN076.pderiv_mem_span_of_dvd G (surfaceMap φ F) hdiv
  have hT' : T = filteredCut w coeffs (surfaceMap φ (polyH K F))
      (surfaceMap φ (polyG K F)) := hT.trans heq
  clear hT
  subst T
  obtain ⟨budget, hcost, hz, hyz, ha, hm⟩ :=
    exists_moving_pole_budget_family (E := E)
      G (regularitySurface φ F) (surfaceMap φ (polyG K F)) w coeffs
      base flag tailFlag unit hG hderiv hGflag
      a b s (center a b s) hHflag hGcontact cflags hcoeff hclass pchar
      (by convert hmix using 1 <;> ring)
  refine ⟨budget, hcost, hm.trans ?_⟩
  rw [mixed_affine_third, mixed_affine_third]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ w)) _

end Budgets

end
end ProximityPrize.SubmissionLower.LocatorHybridTransportC2
end PackedLocator_LocatorHybridTransportC2

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridTailProviderC2. -/
section PackedLocator_LocatorHybridTailProviderC2
/-
LOCATOR HYBRID TAIL PROVIDER — C2 (first-tail flag left free).

C1's provider proof never touches the sharp flag except through the type of its
budget family, so this file re-states it with the first-tail flag `tail1` as a
parameter.  Instantiating `tail1 := cellSharpTail t y r` recovers C1 exactly;
instantiating `tail1 := cellFirstTail t y r` (the REDUCED agreement flag, which
is strictly `Below` the sharp one) is the C2 tightening, worth about 1.29% on
the binding cells.

The C2 instantiation needs the reduced geometry transported to the components of
`globalTailCut (w+1)`; `LocatorHybridTransportC2` supplies the missing piece
(the unit-family transport and the moving budgets at a free first-tail flag),
while `RCN332` already supplies `reducedBudgetFamily`, `reducedBaseOrd` and
`transportedWeightedResultantsGeneral`.
-/
namespace ProximityPrize.SubmissionLower.LocatorHybridTailProviderC2
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorHybridTailProviderC1 LocatorHybridTransportC2
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

variable {K I : Type} [Field K]
local instance  _root_.ProximityPrize.SubmissionLower.LocatorHybridTailProviderC2.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.LocatorHybridTailProviderC2.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable {stageErrorCap : ℕ}

end
end ProximityPrize.SubmissionLower.LocatorHybridTailProviderC2
end PackedLocator_LocatorHybridTailProviderC2

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridTailRealizationC2. -/
section PackedLocator_LocatorHybridTailRealizationC2
/-
LOCATOR HYBRID TAIL REALIZATION — C2 VARIANT.

C2 runs the hybrid provider on the REDUCED first tail
`cellFirstTail t y r = reducedResidualAgreementFlag (cellSupport t y r) (w+1)`
instead of the sharp one.  Three pieces come from `RCN332` unchanged:

  reducedBudgetFamily                  the budget family over the T1-components
  reducedBaseOrd                       the separable base, transported
  transportedWeightedResultantsGeneral the certificate at the reduced flag

and the missing fourth — a `MovingPoleBudget` whose costs agree with that budget
family — is built here from `LocatorHybridTransportC2`: the reduced unit family
is transported to the T1-components, and `exists_firstTail_moving_budgets`
consumes it at the reduced first-tail flag.

The provider itself is `exists_hybridTailMultiplicityProviderGen_of_localDVR`,
the C1 proof with the first-tail flag left free.
-/
namespace ProximityPrize.SubmissionLower.LocatorHybridTailRealizationC2
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open RCN331 RCN027 RCN030 RCN029 RCN037 RCN038 RCN042 RCN002 RCN344 RCN277 RCN003 RCN314 RCN315 RCN093 RCN046 RCN001
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorHybridTailProviderC1 LocatorHybridTailProviderC2 LocatorHybridTransportC2
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 800000

variable {K I : Type} [Field K]
local instance  _root_.ProximityPrize.SubmissionLower.LocatorHybridTailRealizationC2.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.LocatorHybridTailRealizationC2.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable {stageErrorCap : ℕ}
variable {t y r : Nat}

end
end ProximityPrize.SubmissionLower.LocatorHybridTailRealizationC2
end PackedLocator_LocatorHybridTailRealizationC2

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridIdentityC2. -/

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridGatesC2. -/

/-! Packed from ProximityPrize.SubmissionLower.LocatorFixedHybridC2. -/

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridRealizeC2. -/

/-! Packed from ProximityPrize.SubmissionLower.LocatorFixedOwnBoundC2. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier55 : True := by trivial
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier56 : True := by trivial
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier57 : True := by trivial
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier58 : True := by trivial
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier59 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSourceArithmetic. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier60 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSingletonSource. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier61 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSelection. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier62 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorCaps. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier63 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSelectedCaps. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier64 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorCover. -/
section PackedLocator_LocatorCover
namespace ProximityPrize.SubmissionLower.LocatorCover
open RCN259
noncomputable section
variable {R S I:Type*} [CommRing R] [GCDMonoid R]
 [CommRing S] [IsDomain S]
local instance _root_.ProximityPrize.SubmissionLower.LocatorCover.instDecidableEq_proximityPrize :DecidableEq S:=Classical.decEq S
local instance _root_.ProximityPrize.SubmissionLower.LocatorCover.instDecidableEq_proximityPrize_1 :DecidableEq I:=Classical.decEq I
theorem quotient_vanish (phi:R →+* S) (a b:R)
    (ha:phi a = 0) (hb:phi b = 0) (hg:phi (gcd12 a b) ≠ 0) :
    phi (quotientA a b) = 0 ∧ phi (quotientB a b) = 0:=by
  rw [a_eq_gcd12_mul_quotientA a b, map_mul] at ha
  rw [b_eq_gcd12_mul_quotientB a b, map_mul] at hb
  exact ⟨(mul_eq_zero.mp ha).resolve_left hg, (mul_eq_zero.mp hb).resolve_left hg⟩
def fixed (phi:I → R →+* S) (seeds:Finset I) (a b:R):Finset I:=by
  classical
  exact seeds.filter (fun i => phi i (gcd12 a b) = 0)
def residual (phi:I → R →+* S) (seeds:Finset I) (a b:R):Finset I:=by
  classical
  exact seeds.filter (fun i => phi i (gcd12 a b) ≠ 0)
theorem partition_card (phi:I → R →+* S) (seeds:Finset I) (a b:R) :
    (fixed phi seeds a b).card + (residual phi seeds a b).card = seeds.card:=by
  classical
  simpa only [fixed, residual] using
    Finset.card_filter_add_card_filter_not (s:=seeds)
      (fun i => phi i (gcd12 a b) = 0)
theorem fixed_vanish (phi:I → R →+* S) (seeds:Finset I) (a b:R)
    (i:I) (hi:i ∈ fixed phi seeds a b):phi i (gcd12 a b) = 0:=by
  classical
  have hm:i ∈ seeds ∧ phi i (gcd12 a b) = 0:=by
    simpa only [fixed, Finset.mem_filter] using hi
  exact hm.2
theorem residual_vanish (phi:I → R →+* S) (seeds:Finset I) (a b:R)
    (ha:∀ i ∈ seeds, phi i a = 0) (hb:∀ i ∈ seeds, phi i b = 0)
    (i:I) (hi:i ∈ residual phi seeds a b) :
    phi i (quotientA a b) = 0 ∧ phi i (quotientB a b) = 0:=by
  classical
  have hm:i ∈ seeds ∧ phi i (gcd12 a b) ≠ 0:=by
    simpa only [residual, Finset.mem_filter] using hi
  exact quotient_vanish (phi i) a b (ha i hm.1) (hb i hm.1) hm.2
end
end ProximityPrize.SubmissionLower.LocatorCover
end PackedLocator_LocatorCover

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier65 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorFixedBridge. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier66 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800Bridge. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier67 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800Composition. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier68 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptCellCore. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier69 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData01. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier70 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData02. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier71 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData03. -/

end Compact_PackedLocatorTail

section Compact_AsymmetricLocator
namespace ProximityPrize.SubmissionLower.AsymmetricHelper
open scoped Classical BigOperators
open UniqueFactorizationMonoid RCN081 RCN156 RCN234 RCN260 LocatorCoprimeQuotient
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
variable {K I : Type} [Field K]
local instance  _root_.ProximityPrize.SubmissionLower.AsymmetricHelper.instDecidableEq_proximityPrize_2 : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.AsymmetricHelper.instDecidableEq_proximityPrize_3 : DecidableEq I := Classical.decEq I

def leftRegularNumerator (P : UnequalParameters) : ℕ :=
  (P.n - P.w) * RCN294.dot P.leftAgreement P.mixedCost +
    (P.errors + 1) * P.gap * P.mixedCost.z

def leftRegularCountCap (P : UnequalParameters) : ℕ :=
  leftRegularNumerator P / P.gap

theorem regularSeeds_count_le_left_intersection
    (P:UnequalParameters) (H Q:MvPolynomial (Fin 4) K)
    (F:RCN266.RegularIndex H) (hrel:IsRelPrime F.1 Q)
    (p:ℕ) [CharP K p]
    (hFY:F.1.degreeOf 1 ≤ P.leftY) (hFR:F.1.degreeOf 2 ≤ P.leftR)
    (hFZ:F.1.degreeOf 3 ≤ P.leftZ)
    (hQY:Q.degreeOf 1 ≤ P.rightY) (hQR:Q.degreeOf 2 ≤ P.rightR)
    (hQZ:Q.degreeOf 3 ≤ P.rightZ)
    (hleftR:1 ≤ P.leftR)
    (hleftYSmall:P.leftY < p) (hleftRSmall:P.leftR < p)
    (hleftZSmall:P.leftZ < p)
    (hmixedYSmall:P.mixedCost.y < p) (hmixedRSmall:P.mixedCost.r < p)
    (hmixedZSmall:P.mixedCost.z < p)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (nodes:Finset I) (x u0 u1:I → K) (hinj:Set.InjOn x nodes)
    (hnodes:nodes.card = P.n)
    (hw:1 ≤ P.w) (hchar:P.w < p) (hwa:P.w < P.a) (han:P.a ≤ P.n)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ P.w)
    (hagreement:∀ gamma ∈ Gamma, P.a ≤
      (nodes.filter (fun i => (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hno:RCN238.NoLargeSelectedPencil selected Gamma P.w P.errors)
    (hQzero:∀ gamma ∈ RCN140.regularSeeds H selected Gamma F,
      RCN319.specialization K (selected gamma) gamma Q = 0) :
    (RCN140.regularSeeds H selected Gamma F).card ≤ leftRegularCountCap P:=by
  let Fself:=regularIndexSelf H F
  have hcount:=regularPairSeeds_bound_left P F.1 Q hrel Fself p
    hFY hFR hFZ hQY hQR hQZ hleftR hleftYSmall hleftRSmall hleftZSmall
    hmixedYSmall hmixedRSmall hmixedZSmall
    selected Gamma nodes x u0 u1 hinj hnodes hw hchar hwa han hdegree hagreement hno
  have heq:RCN052.regularPairSeeds F.1 Q selected Gamma Fself =
      RCN140.regularSeeds H selected Gamma F:=by
    ext gamma
    simp only [RCN052.regularPairSeeds, RCN140.regularSeeds, Finset.mem_filter]
    constructor
    · intro h
      exact ⟨h.1, h.2.1⟩
    · intro h
      exact ⟨h.1, h.2, hQzero gamma (Finset.mem_filter.mpr h)⟩
  rw [heq] at hcount
  have hv:=regularVector_le_mixedCost P F.1 hFY hFR hFZ
  have hdot:RCN294.dot P.leftAgreement (RCN052.regularVector P F.1) ≤
      RCN294.dot P.leftAgreement P.mixedCost :=
    Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul_left P.leftAgreement.y hv.1)
        (Nat.mul_le_mul_left P.leftAgreement.r hv.2.1))
      (Nat.mul_le_mul_left P.leftAgreement.z hv.2.2)
  unfold leftRegularCountCap
  apply (Nat.le_div_iff_mul_le (by unfold UnequalParameters.gap; omega)).mpr
  exact hcount.trans (Nat.add_le_add (Nat.mul_le_mul_left (P.n - P.w) hdot)
    (Nat.mul_le_mul_left ((P.errors + 1) * P.gap) hv.2.2))

end
end ProximityPrize.SubmissionLower.AsymmetricHelper

end Compact_AsymmetricLocator

section Compact_AsymmetricLinear
namespace ProximityPrize.SubmissionLower.AsymmetricHelper
open RCN260
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- A linear allowance for a carrier confined to a fixed degree box. -/
theorem leftRegularCountCap_le_linear (P : UnequalParameters)
    (ay ar az qT qM qR : ℕ) (hgap : 0 < P.gap)
    (hy : P.leftAgreement.y ≤ ay) (hr : P.leftAgreement.r ≤ ar)
    (hz : P.leftAgreement.z ≤ az)
    (hT : (P.n-P.w)*(ay*P.rightR+ar*P.rightY) ≤ P.gap*qT)
    (hM : (P.n-P.w)*(ar*P.rightZ+az*P.rightR) +
      (P.errors+1)*P.gap*P.rightR ≤ P.gap*qM)
    (hR : (P.n-P.w)*(ay*P.rightZ+az*P.rightY) +
      (P.errors+1)*P.gap*P.rightY ≤ P.gap*qR) :
    leftRegularCountCap P ≤ qT*P.leftZ+qM*P.leftY+qR*P.leftR := by
  have hd : RCN294.dot P.leftAgreement P.mixedCost ≤
      ay*P.mixedCost.y+ar*P.mixedCost.r+az*P.mixedCost.z := by
    unfold RCN294.dot
    exact Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul_right _ hy) (Nat.mul_le_mul_right _ hr))
      (Nat.mul_le_mul_right _ hz)
  have hn : leftRegularNumerator P ≤
      (P.n-P.w)*(ay*P.mixedCost.y+ar*P.mixedCost.r+az*P.mixedCost.z) +
        (P.errors+1)*P.gap*P.mixedCost.z :=
    Nat.add_le_add_right (Nat.mul_le_mul_left _ hd) _
  have he : (P.n-P.w)*(ay*P.mixedCost.y+ar*P.mixedCost.r+az*P.mixedCost.z) +
        (P.errors+1)*P.gap*P.mixedCost.z =
      ((P.n-P.w)*(ay*P.rightR+ar*P.rightY))*P.leftZ +
      ((P.n-P.w)*(ar*P.rightZ+az*P.rightR)+(P.errors+1)*P.gap*P.rightR)*P.leftY +
      ((P.n-P.w)*(ay*P.rightZ+az*P.rightY)+(P.errors+1)*P.gap*P.rightY)*P.leftR := by
    simp only [UnequalParameters.mixedCost]
    ring
  rw [he] at hn
  have hh := Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_right P.leftZ hT) (Nat.mul_le_mul_right P.leftY hM))
    (Nat.mul_le_mul_right P.leftR hR)
  have hb : leftRegularNumerator P ≤
      P.gap*(qT*P.leftZ+qM*P.leftY+qR*P.leftR) := by
    calc
      _ ≤ _ := hn.trans hh
      _ = _ := by ring
  have hdiv := Nat.div_le_div_right (c := P.gap) hb
  simpa only [leftRegularCountCap, Nat.mul_div_right _ hgap] using hdiv

end ProximityPrize.SubmissionLower.AsymmetricHelper

end Compact_AsymmetricLinear

section Compact_Helpers80791
/-! Error-80791 phase ingredient, adapted from the promoted shared-product machinery.
No protocol claim is asserted in this module. -/
set_option Elab.async false

section Adapted_LocatorGenericHelperFactorSwitch
namespace ProximityPrize.SubmissionLower.Lower80791.FactorSwitch

open ProximityPrize.Benchmark
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN260 RCN266 RCN319
open LocatorCoprimeQuotient LocatorLowQuotient

open scoped Classical

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

local instance  _root_.ProximityPrize.SubmissionLower.Lower80791.FactorSwitch.instDecidableEqK : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.Lower80791.FactorSwitch.instDecidableEqI : DecidableEq I := Classical.decEq I
local instance  _root_.ProximityPrize.SubmissionLower.Lower80791.FactorSwitch.instCharPKOfNatNat : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

end

end ProximityPrize.SubmissionLower.Lower80791.FactorSwitch

end Adapted_LocatorGenericHelperFactorSwitch

section Adapted_LocatorGenericPowerRoute
namespace ProximityPrize.SubmissionLower.Lower80791.PowerRoute

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN260 RCN266 RCN319
open LocatorCoprimeQuotient LocatorLowQuotient
open LocatorArbitraryPowerAvoidance LocatorArbitraryPowerContact
open Lower80791.FactorSwitch

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

local instance  _root_.ProximityPrize.SubmissionLower.Lower80791.PowerRoute.instDecidableEqK : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.Lower80791.PowerRoute.instDecidableEqI : DecidableEq I := Classical.decEq I
local instance  _root_.ProximityPrize.SubmissionLower.Lower80791.PowerRoute.instCharPKOfNatNat : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

end

end ProximityPrize.SubmissionLower.Lower80791.PowerRoute

end Adapted_LocatorGenericPowerRoute

section Adapted_LocatorBatchPowerRoute
namespace ProximityPrize.SubmissionLower.Lower80791.BatchPowerRoute

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN260 RCN266 RCN319
open LocatorLowQuotient LocatorCoprimeQuotient
  LocatorArbitraryPowerAvoidance LocatorArbitraryPowerContact
  Lower80791.FactorSwitch Lower80791.PowerRoute
  LocatorBatchProductRoute

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

local instance  _root_.ProximityPrize.SubmissionLower.Lower80791.BatchPowerRoute.instDecidableEqK : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.Lower80791.BatchPowerRoute.instDecidableEqI : DecidableEq I := Classical.decEq I
local instance  _root_.ProximityPrize.SubmissionLower.Lower80791.BatchPowerRoute.instCharPKOfNatNat : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

/-! ## Contact-thinned consumer (lever S1): the band hypothesis is the thin budget. -/

end

end ProximityPrize.SubmissionLower.Lower80791.BatchPowerRoute

end Adapted_LocatorBatchPowerRoute

end Compact_Helpers80791

section Compact_Oracle80791
/-! Error-80791 phase ingredient, adapted from the promoted shared-product machinery.
No protocol claim is asserted in this module. -/
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Lower80791.Oracle
open RCN095 LocatorFactorAggregate LocatorLowQuotient LocatorArbitraryPowerAvoidance
open Lower80791.PowerRoute Lower80791.FactorSwitch
open LocatorPhase6800Oracle (Potential rawFlag sumFlag RawBelow RawStrictSlopeBelow)
set_option autoImplicit false
set_option maxRecDepth 100000
/-- The cumulative boxes used by a power source. -/
structure SourceNumbers where
  totalCap : ℕ
  middleCap : ℕ
  slopeCap : ℕ
  gap : ℕ
  deriving DecidableEq, Repr

def SourceNumbers.fuel (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  min (s.totalCap / total p)
    (min (s.middleCap / middle p) (s.slopeCap / p.all))

def SourceNumbers.band (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  powerBandBudget 50283 (total p) (middle p) p.all
    (s.totalCap - total p) (s.middleCap - middle p)
    (s.slopeCap - p.all) (s.fuel p)

/-- Lever S1.  The product of the routed factors has contact weight at least
`131071 * middle p - p.all` (`contact_ge_ys` with the exact aggregate weights), and the
source's kernel degree satisfies `D + slopeCap ≤ 131071 * (middleCap + 1)`; so the level-1
contact cap of the band ladder is at most `contactCap`, and it drops by `50283 + contactDec`
per level.  `bandThin` is the ladder charged on the rows that can carry a monomial. -/
def contactDec (p : FlagDegree) : ℕ := 131071 * middle p - p.all

def SourceNumbers.contactCap (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  (131071 * (s.middleCap + 1) - s.slopeCap) - contactDec p

def SourceNumbers.bandThin (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  powerBandBudgetThin 131071 (s.contactCap p) 50283 (contactDec p)
    (total p) (middle p) p.all
    (s.totalCap - total p) (s.middleCap - middle p)
    (s.slopeCap - p.all) (s.fuel p)

def SourceNumbers.Routeable (s : SourceNumbers) (p : FlagDegree) : Prop :=
  1 ≤ p.all ∧ total p ≤ s.totalCap ∧ middle p ≤ s.middleCap ∧
    p.all ≤ s.slopeCap ∧ (s.band p < s.gap ∨ s.bandThin p < s.gap)

instance  _root_.ProximityPrize.SubmissionLower.Lower80791.Oracle.instDecidableRouteable (s : SourceNumbers) (p : FlagDegree) : Decidable (s.Routeable p) :=
  by unfold SourceNumbers.Routeable; infer_instance

end ProximityPrize.SubmissionLower.Lower80791.Oracle

end Compact_Oracle80791

section Compact_BatchPhase80791
/-! Error-80791 phase ingredient, adapted from the promoted shared-product machinery.
No protocol claim is asserted in this module. -/
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Lower80791.BatchPhase

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN071 RCN081 RCN095 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156
  RCN180 RCN234 RCN238 RCN260 RCN266
open LocatorFactorAggregate LocatorArbitraryPowerAvoidance
  LocatorBatchProductRoute Lower80791.BatchPowerRoute
  Lower80791.FactorSwitch Lower80791.Oracle

open LocatorPhase6800Oracle (Potential sumFlag sumFlag_all sumFlag_middle sumFlag_total RawBelow RawStrictSlopeBelow)
open LocatorBatchPhase6800 (regularAggregateFlag regularAggregateFlag_all
  regularAggregateFlag_middle regularAggregateFlag_total regularAggregateFlag_mono
  regularAggregateFlag_all_lt_of_ssubset regularAggregateFlag_raw_mono sum_phasePotential_eval)

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

local instance  _root_.ProximityPrize.SubmissionLower.Lower80791.BatchPhase.instDecidableEqK : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.Lower80791.BatchPhase.instDecidableEqI : DecidableEq I := Classical.decEq I

/-! ## State-local phase semantics

The numerical receipt is indexed by the exact aggregate raw flag.  These
lemmas keep that state intact while the algebraic route repeatedly replaces a
routeable batch by a strict universal sub-batch.
-/

end

end ProximityPrize.SubmissionLower.Lower80791.BatchPhase

end Compact_BatchPhase80791

section Compact_ClosedRank
/-! Symbolic rank arithmetic for large first-jet interpolation profiles.
The purpose is to replace long finite evaluations by polynomial identities. -/
namespace ProximityPrize.SubmissionLower.ClosedRank
open scoped BigOperators
open LocatorFastKernelArithmetic
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem rectangularCount_twice (a b h L : ℕ)
    (hb : h + (a - 1) + (b - 1) ≤ L) :
    2 * (rectangularCount a b h L : ℤ) =
      (a : ℤ) * b * (2 * (L + 1 - (h : ℤ)) - a - b + 2) := by
  by_cases ha : a = 0
  · simp [ha, rectangularCount]
  by_cases hzero : b = 0
  · simp [hzero, rectangularCount]
  have ha1 : 1 ≤ a := by omega
  have hb1 : 1 ≤ b := by omega
  have htA : a * (a - 1) / 2 * 2 = a * (a - 1) :=
    Nat.div_mul_cancel (Nat.two_dvd_mul_sub_one a)
  have htB : b * (b - 1) / 2 * 2 = b * (b - 1) :=
    Nat.div_mul_cancel (Nat.two_dvd_mul_sub_one b)
  have hmass : b * (a * (a - 1) / 2) + a * (b * (b - 1) / 2) ≤
      a * b * (L + 1 - h) := by
    have hx := Nat.mul_le_mul_left (a * b)
      (show (a - 1) + (b - 1) ≤ 2 * (L + 1 - h) by omega)
    have hi := congrArg (fun x => b*x) htA
    have hj := congrArg (fun x => a*x) htB
    nlinarith only [hx, hi, hj]
  have htAi : (a * (a - 1) / 2 : ℕ) * (2 : ℤ) = (a : ℤ) * (a - 1) := by
    exact_mod_cast htA
  have htBi : (b * (b - 1) / 2 : ℕ) * (2 : ℤ) = (b : ℤ) * (b - 1) := by
    exact_mod_cast htB
  unfold rectangularCount
  simp only [Nat.cast_sub hmass, Nat.cast_add, Nat.cast_mul,
    Nat.cast_sub (show h ≤ L + 1 by omega), Nat.cast_one]
  nlinarith only [congrArg (fun x : ℤ => b*x) htAi, congrArg (fun x : ℤ => a*x) htBi]

theorem rectangularCount_shift_le (a b h L : ℕ)
    (hb : (a - 1) + (b - 1) ≤ L) :
    rectangularCount (a-h) (b-h) h L ≤ rectangularCount a b 0 L := by
  by_cases ha : a ≤ h
  · simp [Nat.sub_eq_zero_of_le ha, rectangularCount]
  by_cases hb' : b ≤ h
  · simp [Nat.sub_eq_zero_of_le hb', rectangularCount]
  have hshape : h + (a-h-1) + (b-h-1) ≤ L := by omega
  rw [← rectangularSum_eq_rectangularCount _ _ _ _ hshape,
    ← rectangularSum_eq_rectangularCount a b 0 L (by omega)]
  calc
    _ ≤ ∑ i ∈ Finset.range (a-h), ∑ j ∈ Finset.range (b-h), (L+1-0-i-j) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      omega
    _ ≤ ∑ i ∈ Finset.range a, ∑ j ∈ Finset.range b, (L+1-0-i-j) := by
      apply le_trans (Finset.sum_le_sum (fun i _ =>
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le b h))
          (fun _ _ _ => Nat.zero_le _)))
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le a h))
        (fun _ _ _ => Nat.zero_le _)

def rankRow (m L s r : ℕ) : ℕ :=
  let h := min (r+1) (m-r)
  rectangularCount (r+1) (s+1) 0 L - rectangularCount (r+1-h) (s+1-h) h L

theorem rankRow_twice (m L s r : ℕ) (hr : r < m)
    (hshape : m+s ≤ L+1) (hs : 2*s ≤ m) :
    2 * (rankRow m L s r : ℤ) =
      (r+1 : ℤ)*(s+1)*(2*L+2-r-s) -
      if r < m-s then 0 else
        (2*r+1-m : ℤ)*(s+1-m+r)*(2*L+2-r-s) := by
  let h := min (r+1) (m-r)
  have hl : r+s ≤ L := by omega
  have hle := rectangularCount_shift_le (r+1) (s+1) h L (by omega)
  have hsource := rectangularCount_twice (r+1) (s+1) 0 L (by omega)
  have hsource' : 2 * (rectangularCount (r+1) (s+1) 0 L : ℤ) =
      (r+1 : ℤ)*(s+1)*(2*L+2-r-s) := by
    push_cast at hsource
    nlinarith only [hsource]
  unfold rankRow
  change 2 * ((rectangularCount (r+1) (s+1) 0 L -
    rectangularCount (r+1-h) (s+1-h) h L : ℕ) : ℤ) = _
  rw [Nat.cast_sub hle, mul_sub, hsource']
  by_cases hearly : r < m-s
  · rw [if_pos hearly]
    have hzero : r+1-h = 0 ∨ s+1-h = 0 := by
      dsimp [h]
      omega
    rcases hzero with hzero | hzero <;> simp [hzero, rectangularCount]
  · rw [if_neg hearly]
    have heqh : h = m-r := by dsimp [h]; omega
    have hhr : h ≤ r+1 := by omega
    have hhs : h ≤ s+1 := by omega
    have hkernel := rectangularCount_twice (r+1-h) (s+1-h) h L (by omega)
    simp only [Nat.cast_sub hhr, Nat.cast_sub hhs, Nat.cast_add, Nat.cast_one] at hkernel
    have hhcast : (h : ℤ) = m-r := by rw [heqh, Nat.cast_sub (by omega : r ≤ m)]
    rw [hhcast] at hkernel
    nlinarith only [hkernel]

def sourceTwice (L s r : ℤ) : ℤ := (r+1)*(s+1)*(2*L+2-r-s)
def removedTwice (m L s j : ℤ) : ℤ := (m+1-2*j)*(s+1-j)*(2*L+2-m-s+j)

def sourceTwelve (m L s : ℤ) : ℤ :=
  (s+1)*m*(m+1)*(6*(L+1)-2*(m-1)-3*s)

def removedPartialTwelve (m L s k : ℤ) : ℤ :=
  let c := 2*L+2-m-s
  let p0 := (m+1)*(s+1)
  let p1 := -(m+2*s+3)
  6*p0*c*k + 3*(p0+p1*c)*k*(k+1) +
    (p1+2*c)*k*(k+1)*(2*k+1) + 3*k*k*(k+1)*(k+1)

theorem sum_sourceTwice (m : ℕ) (L s : ℤ) :
    6 * (∑ r ∈ Finset.range m, sourceTwice L s r) = sourceTwelve m L s := by
  induction m with
  | zero => simp [sourceTwelve]
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    simp only [Nat.cast_add, Nat.cast_one]
    unfold sourceTwice sourceTwelve
    ring

theorem sum_removedTwice (k : ℕ) (m L s : ℤ) :
    6 * (∑ j ∈ Finset.range k, removedTwice m L s (j+1)) =
      removedPartialTwelve m L s k := by
  induction k with
  | zero => simp [removedPartialTwelve]
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    simp only [Nat.cast_add, Nat.cast_one]
    unfold removedTwice removedPartialTwelve
    ring

theorem sum_removed_rows (m L s : ℕ) (hs : s ≤ m) :
    (∑ r ∈ Finset.range m, if r < m-s then (0 : ℤ) else
      removedTwice m L s ((m : ℤ)-r)) =
      ∑ j ∈ Finset.range s, removedTwice m L s (j+1) := by
  let f : ℕ → ℤ := fun r => if r < m-s then 0 else removedTwice m L s ((m : ℤ)-r)
  change (∑ r ∈ Finset.range m, f r) = _
  have hsplit := Finset.sum_range_add f (m-s) s
  rw [Nat.sub_add_cancel hs] at hsplit
  rw [hsplit]
  have hzero : (∑ r ∈ Finset.range (m-s), f r) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    simp [f, Finset.mem_range.mp hr]
  rw [hzero, zero_add]
  calc
    _ = ∑ j ∈ Finset.range s, f (m-s+(s-1-j)) :=
      (Finset.sum_range_reflect (fun r => f (m-s+r)) s).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have hlate : ¬ m-s+(s-1-j) < m-s := by omega
      have hindex : (m : ℤ) - (m-s+(s-1-j) : ℕ) = (j : ℤ)+1 := by
        have heq : m-s+(s-1-j)+j+1 = m := by omega
        have heqi : ((m-s+(s-1-j) : ℕ) : ℤ) + j + 1 = m := by exact_mod_cast heq
        omega
      simp only [f, if_neg hlate, hindex]

theorem fastLocalRankBound_twelve (m L s : ℕ)
    (hshape : m+s ≤ L+1) (hs : 2*s ≤ m) :
    12 * (fastLocalRankBound m L s : ℤ) =
      sourceTwelve m L s - removedPartialTwelve m L s s := by
  have hfast : fastLocalRankBound m L s = ∑ r ∈ Finset.range m, rankRow m L s r := by
    unfold fastLocalRankBound
    rw [LocatorLowQuotient.kernelSumRange_eq]
    apply Finset.sum_congr rfl
    intro r hr
    have hr' := Finset.mem_range.mp hr
    have hmin : min r L = r := min_eq_left (by omega)
    simp only [hmin, rankRow]
  have hrow (r : ℕ) (hr : r ∈ Finset.range m) :
      2*(rankRow m L s r : ℤ) = sourceTwice L s r -
        (if r < m-s then 0 else removedTwice m L s ((m : ℤ)-r)) := by
    rw [rankRow_twice m L s r (Finset.mem_range.mp hr) hshape hs]
    split_ifs <;> simp only [sourceTwice, removedTwice] <;> ring
  have hsum : 2*(fastLocalRankBound m L s : ℤ) =
      (∑ r ∈ Finset.range m, sourceTwice L s r) -
        ∑ j ∈ Finset.range s, removedTwice m L s (j+1) := by
    rw [hfast, Nat.cast_sum, Finset.mul_sum]
    rw [Finset.sum_congr rfl hrow, Finset.sum_sub_distrib,
      sum_removed_rows m L s (by omega)]
  have hscaled := congrArg (fun z : ℤ => 6*z) hsum
  rw [mul_sub, sum_sourceTwice, sum_removedTwice] at hscaled
  nlinarith only [hscaled]

def closedLocalRankBound (m L s : ℕ) : ℕ :=
  ((sourceTwelve m L s - removedPartialTwelve m L s s) / 12).toNat

theorem fastLocalRankBound_eq_closed (m L s : ℕ)
    (hshape : m+s ≤ L+1) (hs : 2*s ≤ m) :
    fastLocalRankBound m L s = closedLocalRankBound m L s := by
  unfold closedLocalRankBound
  rw [← fastLocalRankBound_twelve m L s hshape hs]
  simp

theorem localRankBound_eq_closed (m L s : ℕ)
    (hshape : m+s ≤ L+1) (hs : 2*s ≤ m) :
    RCN119.localRankBound m L s = closedLocalRankBound m L s := by
  rw [localRankBound_eq_fastLocalRankBound m L s hshape,
    fastLocalRankBound_eq_closed m L s hshape hs]

end ProximityPrize.SubmissionLower.ClosedRank

end Compact_ClosedRank

section Compact_OneResidueLower
/-! The closed one-residue expression is still a lower bound after residue
crossings: discard only the extra positive columns. This avoids a large finite
sum while giving a conservative source dimension. -/
namespace ProximityPrize.SubmissionLower.OneResidueLower
open scoped BigOperators
open RCN100 RCN302 LocatorFastKernelArithmetic LocatorLowQuotient
set_option autoImplicit false
set_option maxHeartbeats 2000000

end ProximityPrize.SubmissionLower.OneResidueLower

end Compact_OneResidueLower

section Compact_Kernels80791
/-! Checked kernel ingredients for the proposed error-80791 certificate.
These receipts alone do not assert a protocol claim. -/
namespace ProximityPrize.SubmissionLower.Kernels80791
open ProximityPrize.Benchmark
open scoped BigOperators
open RCN100 RCN119 RCN180 LocatorFastKernelArithmetic LocatorLowQuotient
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace A

end A

namespace B

end B

namespace T

end T

namespace Source00

end Source00

namespace Source01

end Source01

namespace Source02

end Source02

namespace Source03

end Source03

namespace Source04

end Source04

namespace Source05

end Source05

end ProximityPrize.SubmissionLower.Kernels80791

end Compact_Kernels80791

section Compact_Sources80791
/-! Error-80791 phase ingredient, adapted from the promoted shared-product machinery.
No protocol claim is asserted in this module. -/
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Lower80791.SourceSound

open RCN095 RCN223 RCN260 RCN294 LocatorFactorAggregate
open Lower80791.FactorSwitch Lower80791.PowerRoute
open Lower80791.Oracle
open LocatorPhase6800Oracle (Potential)

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Phase00

end Phase00

namespace Phase01

end Phase01

namespace Phase02

end Phase02

namespace Phase03

end Phase03

namespace Phase04

end Phase04

namespace Phase05

end Phase05

end ProximityPrize.SubmissionLower.Lower80791.SourceSound

end Compact_Sources80791

section Compact_SecondJetHybridProvider
/-! The existing C2 local-DVR argument with an explicit active component set
and a separately proved moving-degree total. Components outside the set must
have no selected seeds; all original normal and tangent charges are retained. -/
namespace ProximityPrize.SubmissionLower.SecondJetHybridProvider
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorHybridTailProviderC1 LocatorHybridTransportC2
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

variable {K I : Type} [Field K]
local instance  _root_.ProximityPrize.SubmissionLower.SecondJetHybridProvider.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.SecondJetHybridProvider.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable {stageErrorCap : ℕ}

end
end ProximityPrize.SubmissionLower.SecondJetHybridProvider

end Compact_SecondJetHybridProvider

section Compact_TriangularKernel
/-! Linear algebra for checking a kernel family one initial component at a
time. This is intended for the second-jet construction, whose lowest epsilon
coefficient has an injective diagonal map. -/
namespace ProximityPrize.SubmissionLower.TriangularKernel
noncomputable section
set_option autoImplicit false

variable {K : Type*} [Field K] {n : ℕ}
variable {V W : Fin n → Type*}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
variable [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]

theorem eq_zero_of_triangular
    (F : (∀ i, V i) →ₗ[K] (∀ i, W i))
    (D : ∀ i, V i →ₗ[K] W i)
    (hD : ∀ i, Function.Injective (D i))
    (hdiag : ∀ v i, (∀ j, j.val < i.val → v j = 0) →
      F v i = D i (v i))
    (v : ∀ i, V i) (hv : F v = 0) : v = 0 := by
  have hall : ∀ k : ℕ, ∀ i : Fin n, i.val = k → v i = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hi
      apply hD i
      calc
        D i (v i) = F v i := (hdiag v i (fun j hj =>
          ih j.val (by omega) j rfl)).symm
        _ = 0 := congrFun hv i
        _ = D i 0 := (map_zero (D i)).symm
  funext i
  exact hall i.val i rfl

theorem injective_of_triangular
    (F : (∀ i, V i) →ₗ[K] (∀ i, W i))
    (D : ∀ i, V i →ₗ[K] W i)
    (hD : ∀ i, Function.Injective (D i))
    (hdiag : ∀ v i, (∀ j, j.val < i.val → v j = 0) →
      F v i = D i (v i)) : Function.Injective F := by
  intro v u h
  apply sub_eq_zero.mp
  apply eq_zero_of_triangular F D hD hdiag (v-u)
  rw [map_sub, h, sub_self]

end
end ProximityPrize.SubmissionLower.TriangularKernel

end Compact_TriangularKernel

section Compact_SecondJetBasis
/-! A triangular polynomial family for second-jet interpolation. The outer
polynomial variable is epsilon; the inner one is the second Hasse derivative.
This module checks independence before imposing the finite support bounds. -/
namespace ProximityPrize.SubmissionLower.SecondJetBasis
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

variable {K B : Type*} [Field K] [CommRing B] [IsDomain B] [Algebra K B]
abbrev Jet (B : Type*) [CommRing B] := Polynomial (Polynomial B)

def lift : B →ₐ[K] Jet B :=
  (Polynomial.CAlgHom (R := K) (A := Polynomial B)).comp
    (Polynomial.CAlgHom (R := K) (A := B))

def factor (v : B) (r h a b : ℕ) : Jet B :=
  Polynomial.X^r *
    (Polynomial.C (Polynomial.X^h) *
      (Polynomial.C (Polynomial.C v) +
        Polynomial.X * Polynomial.C Polynomial.X)^a *
      Polynomial.C (Polynomial.C v)^b)

def term (v : B) (r h a b : ℕ) : B →ₗ[K] Jet B :=
  (LinearMap.mulLeft K (factor v r h a b)).comp lift.toLinearMap

variable {m s : ℕ}

def truncate : Jet B →ₗ[K] (Fin m → Fin s → B) :=
  LinearMap.pi (fun r => LinearMap.pi (fun h =>
    ((Polynomial.lcoeff B h.val).restrictScalars K).comp
      ((Polynomial.lcoeff (Polynomial B) r.val).restrictScalars K)))

theorem truncate_apply (P : Jet B) (r : Fin m) (h : Fin s) :
    truncate (K := K) P r h = (P.coeff r.val).coeff h.val := rfl

/-- The chosen exponents attain the requested contact without exceeding the
available second-derivative degree. -/
theorem exponent_budget (m r s h : ℕ) (hr : r ≤ m) (hh : h ≤ s) :
    let q := max ((m-r+1)/2) (m-r-(s-h))
    let a := min q (s-h)
    let b := q-a
    a+b = q ∧ h+a ≤ s ∧ m ≤ r+2*a+b := by
  dsimp
  omega

end
end ProximityPrize.SubmissionLower.SecondJetBasis

end Compact_SecondJetBasis

section Compact_SecondJetTruncate
/-! Truncation preserves the triangular kernel construction and its contact.
The concrete finite monomial support bounds are still separate obligations. -/
namespace ProximityPrize.SubmissionLower.SecondJetBasis
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K B : Type*} [Field K] [CommRing B] [IsDomain B] [Algebra K B]

def truncateOuter (m : ℕ) : Jet B →ₗ[K] Jet B :=
  (Polynomial.modByMonicHom (Polynomial.X^m : Jet B)).restrictScalars K

theorem truncateOuter_coeff (m : ℕ) (P : Jet B) (r : ℕ) (hr : r < m) :
    (truncateOuter (K := K) m P).coeff r = P.coeff r := by
  change (P %ₘ Polynomial.X^m).coeff r = P.coeff r
  have heq := Polynomial.modByMonic_add_div P (Polynomial.X^m)
  have hc := congrArg (fun Q : Jet B => Q.coeff r) heq
  simpa only [Polynomial.coeff_add, Polynomial.coeff_X_pow_mul',
    if_neg (Nat.not_le.mpr hr), add_zero] using hc

theorem truncateOuter_coeff_high (m : ℕ) (P : Jet B) (r : ℕ) (hr : m ≤ r) :
    (truncateOuter (K := K) m P).coeff r = 0 := by
  change (P %ₘ Polynomial.X^m).coeff r = 0
  apply Polynomial.coeff_eq_zero_of_degree_lt
  apply (Polynomial.degree_modByMonic_lt P (Polynomial.monic_X_pow m)).trans_le
  simp only [Polynomial.degree_X_pow]
  exact_mod_cast hr

theorem truncate_truncateOuter {m s : ℕ} (P : Jet B) :
    truncate (K := K) (m := m) (s := s) (truncateOuter (K := K) m P) =
      truncate (K := K) (m := m) (s := s) P := by
  funext r h
  exact congrArg (fun Q : Polynomial B => Q.coeff h.val)
    (truncateOuter_coeff (K := K) m P r.val r.isLt)

theorem truncateOuter_contact {C : Type*} [CommRing C]
    (φ : Jet B →+* C) (t : C) (m : ℕ) (P : Jet B)
    (hε : φ Polynomial.X = t) (hP : t^m ∣ φ P) :
    t^m ∣ φ (truncateOuter (K := K) m P) := by
  have hd : t^m ∣ φ ((Polynomial.X^m : Jet B) * (P /ₘ Polynomial.X^m)) := by
    simp only [map_mul, map_pow, hε]
    exact dvd_mul_right _ _
  have heq := congrArg φ (Polynomial.modByMonic_add_div P (Polynomial.X^m))
  rw [map_add] at heq
  have hsub := dvd_sub hP hd
  rwa [← heq, add_sub_cancel_right] at hsub

end
end ProximityPrize.SubmissionLower.SecondJetBasis

end Compact_SecondJetTruncate

section Compact_SecondJetSupport
/-! Support bounds for the explicit second-jet kernel family. Variables are
ordered epsilon, S, A, R, Z, matching two successive `finSuccEquiv`s. -/
namespace ProximityPrize.SubmissionLower.SecondJetSupport
open scoped BigOperators Pointwise
open MvPolynomial
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]
abbrev Poly := MvPolynomial (Fin 5) K

def Box (lo a r s t : ℕ) (P : Poly (K := K)) : Prop :=
  ∀ d ∈ P.support, lo ≤ d 0 ∧ d 2 ≤ a ∧ d 3 ≤ r ∧ d 1 ≤ s ∧
    d 1+d 2+d 3+d 4 ≤ t

def flatEquiv : Poly (K := K) ≃ₐ[K] SecondJetBasis.Jet (MvPolynomial (Fin 3) K) :=
  (MvPolynomial.finSuccEquiv K 4).trans (Polynomial.mapAlgEquiv (MvPolynomial.finSuccEquiv K 3))

theorem flatEquiv_X (j : Fin 5) :
    flatEquiv (K := K) (MvPolynomial.X j) =
      ![Polynomial.X, Polynomial.C Polynomial.X,
        Polynomial.C (Polynomial.C (MvPolynomial.X 0)),
        Polynomial.C (Polynomial.C (MvPolynomial.X 1)),
        Polynomial.C (Polynomial.C (MvPolynomial.X 2))] j := by
  have h0 : flatEquiv (K := K) (MvPolynomial.X 0) = Polynomial.X := by
    change Polynomial.map _ ((MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X 0)) = _
    rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X]
  have hs (i : Fin 4) : flatEquiv (K := K) (MvPolynomial.X i.succ) =
      Polynomial.C ((MvPolynomial.finSuccEquiv K 3) (MvPolynomial.X i)) := by
    change Polynomial.map _ ((MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X i.succ)) = _
    rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
    rfl
  fin_cases j
  · exact h0
  · change flatEquiv (K := K) (MvPolynomial.X (0 : Fin 4).succ) = Polynomial.C Polynomial.X
    rw [hs, MvPolynomial.finSuccEquiv_X_zero]
  · change flatEquiv (K := K) (MvPolynomial.X ((0 : Fin 3).succ).succ) = _
    rw [hs, MvPolynomial.finSuccEquiv_X_succ]
    rfl
  · change flatEquiv (K := K) (MvPolynomial.X ((1 : Fin 3).succ).succ) = _
    rw [hs, MvPolynomial.finSuccEquiv_X_succ]
    rfl
  · change flatEquiv (K := K) (MvPolynomial.X ((2 : Fin 3).succ).succ) = _
    rw [hs, MvPolynomial.finSuccEquiv_X_succ]
    rfl

theorem flatEquiv_coeff (P : Poly (K := K)) (r h : ℕ) (d : Fin 3 →₀ ℕ) :
    MvPolynomial.coeff d (((flatEquiv (K := K) P).coeff r).coeff h) =
      MvPolynomial.coeff ((d.cons h).cons r) P := by
  simp only [flatEquiv, AlgEquiv.trans_apply, Polynomial.coe_mapAlgEquiv, Polynomial.coeff_map]
  change MvPolynomial.coeff d (((MvPolynomial.finSuccEquiv K 3)
    (((MvPolynomial.finSuccEquiv K 4) P).coeff r)).coeff h) = _
  rw [MvPolynomial.finSuccEquiv_coeff_coeff, MvPolynomial.finSuccEquiv_coeff_coeff]

def truncFlat (m : ℕ) : Poly (K := K) →ₗ[K] Poly (K := K) :=
  (flatEquiv (K := K)).symm.toLinearMap.comp
    ((SecondJetBasis.truncateOuter (K := K) m).comp (flatEquiv (K := K)).toLinearMap)

theorem flatEquiv_truncFlat (m : ℕ) (P : Poly (K := K)) :
    flatEquiv (K := K) (truncFlat (K := K) m P) =
      SecondJetBasis.truncateOuter (K := K) m (flatEquiv (K := K) P) := by
  simp [truncFlat]

theorem coeff_truncFlat_cons (m r h : ℕ) (d : Fin 3 →₀ ℕ) (P : Poly (K := K)) :
    MvPolynomial.coeff ((d.cons h).cons r) (truncFlat (K := K) m P) =
      if r < m then MvPolynomial.coeff ((d.cons h).cons r) P else 0 := by
  rw [← flatEquiv_coeff, flatEquiv_truncFlat]
  by_cases hr : r < m
  · rw [if_pos hr, SecondJetBasis.truncateOuter_coeff m _ r hr, flatEquiv_coeff]
  · rw [if_neg hr, SecondJetBasis.truncateOuter_coeff_high m _ r (by omega)]
    simp

theorem support_truncFlat (m : ℕ) (P : Poly (K := K)) (d : Fin 5 →₀ ℕ)
    (hd : d ∈ (truncFlat (K := K) m P).support) : d 0 < m ∧ d ∈ P.support := by
  have heq : ((d.tail.tail).cons (d.tail 0)).cons (d 0) = d := by
    rw [Finsupp.cons_tail, Finsupp.cons_tail]
  have hne := MvPolynomial.mem_support_iff.mp hd
  rw [← heq, coeff_truncFlat_cons] at hne
  split_ifs at hne with h
  · refine ⟨h, MvPolynomial.mem_support_iff.mpr ?_⟩
    simpa only [heq] using hne
  · exact False.elim (hne rfl)

def Allowed (m L s1 s2 : ℕ) (d : Fin 5 →₀ ℕ) : Prop :=
  d 0 < m ∧ d 2 ≤ d 0 ∧ d 3 ≤ s1 ∧ d 1 ≤ s2 ∧ d 1+d 2+d 3+d 4 ≤ L

end
end ProximityPrize.SubmissionLower.SecondJetSupport

end Compact_SecondJetSupport

section Compact_SecondJetLocal
/-! The explicit local substitution A = R - epsilon*S + epsilon^2*T.
Here S is the second Hasse derivative, and T records the remaining contact. -/
namespace ProximityPrize.SubmissionLower.SecondJetLocal
open scoped BigOperators
open SecondJetBasis SecondJetSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]
abbrev Base := MvPolynomial (Fin 3) K
abbrev Target := Polynomial (MvPolynomial (Fin 4) K)

def baseEval : Base (K := K) →ₐ[K] Target (K := K) :=
  MvPolynomial.aeval ![
    Polynomial.C (MvPolynomial.X 2)-Polynomial.X*Polynomial.C (MvPolynomial.X 0)+
      Polynomial.X^2*Polynomial.C (MvPolynomial.X 1),
    Polynomial.C (MvPolynomial.X 2), Polynomial.C (MvPolynomial.X 3)]

def innerEval : Polynomial (Base (K := K)) →ₐ[K] Target (K := K) :=
  Polynomial.eval₂AlgHom baseEval (Polynomial.C (MvPolynomial.X 0)) (fun _ => Commute.all _ _)

def contact : Jet (Base (K := K)) →ₐ[K] Target (K := K) :=
  Polynomial.eval₂AlgHom innerEval Polynomial.X (fun _ => Commute.all _ _)

@[simp] theorem contact_X : contact (K := K) Polynomial.X = Polynomial.X := by
  simp [contact]

@[simp] theorem contact_C_C (p : Base (K := K)) :
    contact (K := K) (Polynomial.C (Polynomial.C p)) = baseEval (K := K) p := by
  simp [contact, innerEval]

@[simp] theorem contact_C_X :
    contact (K := K) (Polynomial.C Polynomial.X) = Polynomial.C (MvPolynomial.X 0) := by
  simp [contact, innerEval]

def v : Base (K := K) := MvPolynomial.X 0-MvPolynomial.X 1

theorem v_ne_zero : v (K := K) ≠ 0 := by
  unfold v
  apply sub_ne_zero.mpr
  intro h
  have hh := MvPolynomial.X_injective h
  exact (by decide : (0 : Fin 3) ≠ 1) hh

theorem contact_v : contact (K := K) (Polynomial.C (Polynomial.C v)) =
    (Polynomial.X : Target (K := K)) * (-(Polynomial.C (MvPolynomial.X (0 : Fin 4)) : Target (K := K))+
      Polynomial.X*Polynomial.C (MvPolynomial.X 1)) := by
  rw [contact_C_C]
  simp only [v, map_sub, baseEval, MvPolynomial.aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem contact_u : contact (K := K)
    (Polynomial.C (Polynomial.C v)+Polynomial.X*Polynomial.C Polynomial.X) =
      Polynomial.X^2*Polynomial.C (MvPolynomial.X 1) := by
  rw [map_add, map_mul, contact_v, contact_X, contact_C_X]
  ring

end
end ProximityPrize.SubmissionLower.SecondJetLocal

end Compact_SecondJetLocal

section Compact_FiniteMonomials
/-! Finite coefficient families embedded into a multivariate polynomial ring. -/
namespace ProximityPrize.SubmissionLower.FiniteMonomials
open scoped BigOperators
noncomputable section
set_option autoImplicit false
variable {K σ I : Type*} [Field K] [Fintype I]
local instance  _root_.ProximityPrize.SubmissionLower.FiniteMonomials.instDecidableEq_proximityPrize : DecidableEq σ := Classical.decEq σ
local instance  _root_.ProximityPrize.SubmissionLower.FiniteMonomials.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I

def reconstruct (e : I → σ →₀ ℕ) : (I → K) →ₗ[K] MvPolynomial σ K :=
  ∑ i, (MvPolynomial.monomial (e i)).comp (LinearMap.proj i)

theorem reconstruct_apply (e : I → σ →₀ ℕ) (c : I → K) :
    reconstruct e c = ∑ i, MvPolynomial.monomial (e i) (c i) := by
  simp [reconstruct]

theorem coeff_reconstruct (e : I → σ →₀ ℕ) (he : Function.Injective e)
    (c : I → K) (i : I) : MvPolynomial.coeff (e i) (reconstruct e c) = c i := by
  classical
  rw [reconstruct_apply, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, he.eq_iff]
  simp

theorem reconstruct_injective (e : I → σ →₀ ℕ) (he : Function.Injective e) :
    Function.Injective (reconstruct (K := K) e) := by
  intro c d h
  funext i
  have hh := congrArg (MvPolynomial.coeff (e i)) h
  simpa only [coeff_reconstruct e he] using hh

theorem coeff_reconstruct_of_notmem (e : I → σ →₀ ℕ) (c : I → K)
    (d : σ →₀ ℕ) (hd : d ∉ Set.range e) :
    MvPolynomial.coeff d (reconstruct e c) = 0 := by
  classical
  rw [reconstruct_apply, MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [MvPolynomial.coeff_monomial, if_neg (fun h => hd ⟨i,h⟩)]

theorem mem_range_iff (e : I → σ →₀ ℕ) (he : Function.Injective e)
    (P : MvPolynomial σ K) : P ∈ (reconstruct (K := K) e).range ↔
      ∀ d ∈ P.support, d ∈ Set.range e := by
  classical
  constructor
  · rintro ⟨c,rfl⟩ d hd
    by_contra hn
    exact MvPolynomial.mem_support_iff.mp hd (coeff_reconstruct_of_notmem e c d hn)
  · intro h
    refine ⟨fun i => P.coeff (e i), ?_⟩
    ext d
    by_cases hd : d ∈ Set.range e
    · obtain ⟨i,rfl⟩ := hd
      exact coeff_reconstruct e he _ i
    · rw [coeff_reconstruct_of_notmem e _ d hd]
      exact (MvPolynomial.notMem_support_iff.mp (fun hs => hd (h d hs))).symm

end
end ProximityPrize.SubmissionLower.FiniteMonomials

end Compact_FiniteMonomials

section Compact_SecondJetSpace
/-! The finite source space for the local second-jet map. -/
namespace ProximityPrize.SubmissionLower.SecondJetSpace
open scoped BigOperators
open SecondJetBasis SecondJetSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

def bound (m L s1 s2 : ℕ) : Fin 5 → ℕ := ![m,s2+1,m,s1+1,L+1]

def Index (m L s1 s2 : ℕ) :=
  {d : ∀ k, Fin (bound m L s1 s2 k) //
    (d 2).val ≤ (d 0).val ∧ (d 1).val+(d 2).val+(d 3).val+(d 4).val ≤ L}

instance  _root_.ProximityPrize.SubmissionLower.SecondJetSpace.instFintypeIndex (m L s1 s2 : ℕ) : Fintype (Index m L s1 s2) := by
  unfold Index
  infer_instance

def exponent {m L s1 s2 : ℕ} (d : Index m L s1 s2) : Fin 5 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun k => (d.val k).val)

@[simp] theorem exponent_apply {m L s1 s2 : ℕ} (d : Index m L s1 s2) (k : Fin 5) :
    exponent d k = (d.val k).val := by simp [exponent]

theorem exponent_injective (m L s1 s2 : ℕ) :
    Function.Injective (exponent (m := m) (L := L) (s1 := s1) (s2 := s2)) := by
  intro d e h
  apply Subtype.ext
  funext k
  apply Fin.ext
  simpa only [exponent_apply] using congrArg (fun f : Fin 5 →₀ ℕ => f k) h

theorem exponent_allowed {m L s1 s2 : ℕ} (d : Index m L s1 s2) :
    Allowed m L s1 s2 (exponent d) := by
  have h0 : (d.val 0).val < m := (d.val 0).isLt
  have h1 : (d.val 1).val < s2+1 := (d.val 1).isLt
  have h3 : (d.val 3).val < s1+1 := (d.val 3).isLt
  simp only [Allowed, exponent_apply]
  exact ⟨h0,d.property.1,by omega,by omega,d.property.2⟩

theorem mem_range_exponent (m L s1 s2 : ℕ) (d : Fin 5 →₀ ℕ) :
    d ∈ Set.range (exponent (m := m) (L := L) (s1 := s1) (s2 := s2)) ↔
      Allowed m L s1 s2 d := by
  constructor
  · rintro ⟨e,rfl⟩
    exact exponent_allowed e
  · intro h
    dsimp only [Allowed] at h
    have hb : ∀ k, d k < bound m L s1 s2 k := by
      intro k
      fin_cases k
      · exact h.1
      · change d 1 < s2+1
        omega
      · change d 2 < m
        omega
      · change d 3 < s1+1
        omega
      · change d 4 < L+1
        omega
    let e : Index m L s1 s2 := ⟨fun k => ⟨d k,hb k⟩,h.2.1,h.2.2.2.2⟩
    refine ⟨e,?_⟩
    ext k
    simp [e]

def sourceMap (m L s1 s2 : ℕ) : (Index m L s1 s2 → K) →ₗ[K]
    Jet (MvPolynomial (Fin 3) K) :=
  (flatEquiv (K := K)).toLinearMap.comp (FiniteMonomials.reconstruct exponent)

def source (m L s1 s2 : ℕ) : Submodule K (Jet (MvPolynomial (Fin 3) K)) :=
  (sourceMap (K := K) m L s1 s2).range

instance source_finite (m L s1 s2 : ℕ) : FiniteDimensional K (source (K := K) m L s1 s2) := by
  unfold source
  infer_instance

end
end ProximityPrize.SubmissionLower.SecondJetSpace

end Compact_SecondJetSpace

section Compact_SecondJetFacetSupport
/-! A shared R/S degree bound for the second-jet kernel family. -/
namespace ProximityPrize.SubmissionLower.SecondJetFacetSupport
open scoped BigOperators Pointwise
open MvPolynomial SecondJetSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

end
end ProximityPrize.SubmissionLower.SecondJetFacetSupport

end Compact_SecondJetFacetSupport

section Compact_SecondJetFacetSpace
/-! The second-jet source space with a shared R/S degree cap. -/
namespace ProximityPrize.SubmissionLower.SecondJetFacetSpace
open scoped BigOperators
open SecondJetBasis SecondJetSupport SecondJetFacetSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

def Index (m L B s : ℕ) :=
  {d : SecondJetSpace.Index m L B s // (d.val 1).val+(d.val 3).val ≤ B}

instance  _root_.ProximityPrize.SubmissionLower.SecondJetFacetSpace.instFintypeIndex (m L B s : ℕ) : Fintype (Index m L B s) := by
  unfold Index
  infer_instance

def exponent {m L B s : ℕ} (d : Index m L B s) : Fin 5 →₀ ℕ :=
  SecondJetSpace.exponent d.val

def sourceMap (m L B s : ℕ) : (Index m L B s → K) →ₗ[K]
    Jet (MvPolynomial (Fin 3) K) :=
  (flatEquiv (K := K)).toLinearMap.comp (FiniteMonomials.reconstruct exponent)

def source (m L B s : ℕ) : Submodule K (Jet (MvPolynomial (Fin 3) K)) :=
  (sourceMap (K := K) m L B s).range

instance source_finite (m L B s : ℕ) : FiniteDimensional K (source (K := K) m L B s) := by
  unfold source
  infer_instance

end
end ProximityPrize.SubmissionLower.SecondJetFacetSpace

end Compact_SecondJetFacetSpace

section Compact_SecondJetGlobalSupport
/-! Global-to-local substitution preserving the shared derivative cap.
Global variables are X, S, Y, R, Z; local variables epsilon, S, A, R, Z. -/
namespace ProximityPrize.SubmissionLower.SecondJetGlobalSupport
open scoped BigOperators Pointwise
open MvPolynomial SecondJetSupport SecondJetBasis
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

def LocalBound (B s L : ℕ) (P : Poly (K := K)) : Prop :=
  ∀ d ∈ P.support, d 2 ≤ d 0 ∧ d 1+d 3 ≤ B ∧ d 1 ≤ s ∧ d 1+d 2+d 3+d 4 ≤ L

theorem LocalBound.mono {B s L B' s' L' : ℕ} {P : Poly (K := K)}
    (h : LocalBound B s L P) (hB : B ≤ B') (hs : s ≤ s') (hL : L ≤ L') :
    LocalBound B' s' L' P := by
  intro d hd
  have hh := h d hd
  exact ⟨hh.1,hh.2.1.trans hB,hh.2.2.1.trans hs,hh.2.2.2.trans hL⟩

theorem LocalBound.mul {B s L B' s' L' : ℕ} {P Q : Poly (K := K)}
    (hP : LocalBound B s L P) (hQ : LocalBound B' s' L' Q) :
    LocalBound (B+B') (s+s') (L+L') (P*Q) := by
  intro d hd
  obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hd)
  have hp := hP u hu
  have hq := hQ v hv
  simp only [Finsupp.add_apply]
  omega

theorem LocalBound.add {B s L : ℕ} {P Q : Poly (K := K)}
    (hP : LocalBound B s L P) (hQ : LocalBound B s L Q) : LocalBound B s L (P+Q) := by
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
  · exact hP d h
  · exact hQ d h

theorem local_C (c : K) : LocalBound 0 0 0 (MvPolynomial.C c : Poly (K := K)) := by
  intro d hd
  have hd0 : d = 0 := Finset.mem_singleton.mp (MvPolynomial.support_C_subset hd)
  subst d
  simp

theorem LocalBound.pow {B s L : ℕ} {P : Poly (K := K)}
    (hP : LocalBound B s L P) (n : ℕ) : LocalBound (n*B) (n*s) (n*L) (P^n) := by
  induction n with
  | zero => simpa using (local_C (K := K) 1)
  | succ n ih => simpa only [pow_succ, Nat.succ_mul] using ih.mul hP

def localize (x u0 u1 : K) : Poly (K := K) →ₐ[K] Poly (K := K) :=
  MvPolynomial.aeval ![MvPolynomial.C x+MvPolynomial.X 0,MvPolynomial.X 1,
    MvPolynomial.C u0+MvPolynomial.C u1*MvPolynomial.X 4+
      MvPolynomial.X 0*MvPolynomial.X 2,MvPolynomial.X 3,MvPolynomial.X 4]

theorem local_X (j : Fin 5) (hj : j ≠ 2) :
    LocalBound (if j=1 ∨ j=3 then 1 else 0) (if j=1 then 1 else 0)
      (if j=0 then 0 else 1) (MvPolynomial.X j : Poly (K := K)) := by
  intro d hd
  simp only [MvPolynomial.support_X, Finset.mem_singleton] at hd
  subst d
  fin_cases j <;> norm_num [Finsupp.single_apply, Fin.ext_iff] at *

theorem local_epsilon_A : LocalBound 0 0 1
    (MvPolynomial.X 0*MvPolynomial.X 2 : Poly (K := K)) := by
  intro d hd
  rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul] at hd
  have hd' := MvPolynomial.support_monomial_subset hd
  have hd0 := Finset.mem_singleton.mp hd'
  subst d
  norm_num [Finsupp.add_apply, Finsupp.single_apply, Fin.ext_iff]

theorem localize_X (x u0 u1 : K) (j : Fin 5) :
    LocalBound (if j=1 ∨ j=3 then 1 else 0) (if j=1 then 1 else 0)
      (if j=0 then 0 else 1) (localize x u0 u1 (MvPolynomial.X j)) := by
  have hE : LocalBound 0 0 0 (MvPolynomial.X 0 : Poly (K := K)) := by
    simpa using local_X (K := K) 0 (by decide)
  have hZ : LocalBound 0 0 1 (MvPolynomial.X 4 : Poly (K := K)) := by
    simpa using local_X (K := K) 4 (by decide)
  fin_cases j
  · simpa [localize] using (local_C x).add hE
  · simpa [localize] using local_X (K := K) 1 (by decide)
  · have hU : LocalBound 0 0 1 (MvPolynomial.C u0+MvPolynomial.C u1*MvPolynomial.X 4 : Poly (K := K)) :=
      ((local_C u0).mono (by omega) (by omega) (by omega)).add
        ((local_C u1).mul hZ)
    simpa [localize] using hU.add (local_epsilon_A (K := K))
  · simpa [localize] using local_X (K := K) 3 (by decide)
  · simpa [localize] using hZ

theorem localize_monomial (x u0 u1 : K) (d : Fin 5 →₀ ℕ) (c : K) :
    LocalBound (d 1+d 3) (d 1) (d 1+d 2+d 3+d 4)
      (localize x u0 u1 (MvPolynomial.monomial d c)) := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
  · simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, map_mul, map_pow,
      map_C]
    have h0 := (localize_X x u0 u1 0).pow (d 0)
    have h1 := (localize_X x u0 u1 1).pow (d 1)
    have h2 := (localize_X x u0 u1 2).pow (d 2)
    have h3 := (localize_X x u0 u1 3).pow (d 3)
    have h4 := (localize_X x u0 u1 4).pow (d 4)
    simpa [Nat.add_assoc] using (local_C c).mul (h0.mul (h1.mul (h2.mul (h3.mul h4))))
  · intro i
    simp

end
end ProximityPrize.SubmissionLower.SecondJetGlobalSupport

end Compact_SecondJetGlobalSupport

section Compact_SecondJetRank
/-! Finite independent kernel vectors for the local second-jet contact map. -/
namespace ProximityPrize.SubmissionLower.SecondJetRank
open scoped BigOperators
open SecondJetBasis SecondJetSupport SecondJetLocal SecondJetSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

def q (m s2 r h : ℕ) := max ((m-r+1)/2) (m-r-(s2-h))
def a (m s2 r h : ℕ) := min (q m s2 r h) (s2-h)
def b (m s2 r h : ℕ) := q m s2 r h-a m s2 r h

theorem budgets (m s2 r h : ℕ) (hr : r ≤ m) (hh : h ≤ s2) :
    a m s2 r h+b m s2 r h=q m s2 r h ∧ h+a m s2 r h ≤ s2 ∧
      m ≤ r+2*a m s2 r h+b m s2 r h :=
  exponent_budget m r s2 h hr hh

def Block (m L s1 s2 r h : ℕ) :=
  {d : Fin 3 → Fin (L+1) //
    (d 0).val+q m s2 r h ≤ r ∧ (d 1).val+q m s2 r h ≤ s1 ∧
      (d 0).val+(d 1).val+(d 2).val+h+q m s2 r h ≤ L}

instance  _root_.ProximityPrize.SubmissionLower.SecondJetRank.instFintypeBlock (m L s1 s2 r h : ℕ) : Fintype (Block m L s1 s2 r h) := by
  unfold Block
  infer_instance

def blockExponent {m L s1 s2 r h : ℕ} (d : Block m L s1 s2 r h) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun k => (d.val k).val)

@[simp] theorem blockExponent_apply {m L s1 s2 r h : ℕ}
    (d : Block m L s1 s2 r h) (k : Fin 3) : blockExponent d k = (d.val k).val := by
  simp [blockExponent]

theorem blockExponent_injective (m L s1 s2 r h : ℕ) :
    Function.Injective (blockExponent (m := m) (L := L) (s1 := s1) (s2 := s2) (r := r) (h := h)) := by
  intro d e hde
  apply Subtype.ext
  funext k
  apply Fin.ext
  simpa only [blockExponent_apply] using congrArg (fun f : Fin 3 →₀ ℕ => f k) hde

theorem block_monomial (m L s1 s2 r h : ℕ) (d : Block m L s1 s2 r h) :
    MvPolynomial.monomial (blockExponent d) (1 : K) =
      MvPolynomial.X 0^(d.val 0).val * MvPolynomial.X 1^(d.val 1).val *
        MvPolynomial.X 2^(d.val 2).val := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
  · simp [Fin.prod_univ_three]
  · intro i
    simp

def contactMap (m : ℕ) : Jet (Base (K := K)) →ₗ[K] Target (K := K) :=
  ((Polynomial.modByMonicHom (Polynomial.X^m : Target (K := K))).restrictScalars K).comp
    (contact (K := K)).toLinearMap

end
end ProximityPrize.SubmissionLower.SecondJetRank

end Compact_SecondJetRank

section Compact_SecondJetFacetRank
/-! Local rank saving with a shared R/S degree cap. -/
namespace ProximityPrize.SubmissionLower.SecondJetFacetRank
open scoped BigOperators
open SecondJetBasis SecondJetSupport SecondJetLocal SecondJetFacetSpace
open SecondJetRank (q a b budgets Block blockExponent blockExponent_injective block_monomial contactMap)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

end
end ProximityPrize.SubmissionLower.SecondJetFacetRank

end Compact_SecondJetFacetRank

section Compact_SecondJetCounts
/-! Efficient counting interfaces for the local second-jet source and kernel.
The finite index types used in the rank proof are never evaluated directly. -/
namespace ProximityPrize.SubmissionLower.SecondJetCounts
open scoped BigOperators
open SecondJetSpace SecondJetRank
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

abbrev BlockSumIndex (m L s1 s2 r h : ℕ) :=
  Σ i : Fin (r-q m s2 r h+1), Σ j : Fin (s1-q m s2 r h+1),
    Fin (L+1-h-q m s2 r h-i.val-j.val)

def blockEquiv (m L s1 s2 r h : ℕ) (hr : q m s2 r h ≤ r) (hs : q m s2 r h ≤ s1) :
    Block m L s1 s2 r h ≃ BlockSumIndex m L s1 s2 r h where
  toFun d := by
    have hd := d.property
    exact ⟨⟨(d.val 0).val,by omega⟩,⟨(d.val 1).val,by omega⟩,
      ⟨(d.val 2).val,by dsimp; omega⟩⟩
  invFun u := by
    rcases u with ⟨i,j,z⟩
    have hi := i.isLt
    have hj := j.isLt
    have hz := z.isLt
    let iv : Fin (L+1) := ⟨i.val,by omega⟩
    let jv : Fin (L+1) := ⟨j.val,by omega⟩
    let zv : Fin (L+1) := ⟨z.val,by omega⟩
    refine ⟨![iv,jv,zv],?_,?_,?_⟩
    · change i.val+q m s2 r h ≤ r
      omega
    · change j.val+q m s2 r h ≤ s1
      omega
    · change i.val+j.val+z.val+h+q m s2 r h ≤ L
      omega
  left_inv d := by
    apply Subtype.ext
    funext k
    apply Fin.ext
    fin_cases k <;> rfl
  right_inv u := by
    rcases u with ⟨i,j,z⟩
    rfl

theorem card_block_of_le (m L s1 s2 r h : ℕ)
    (hr : q m s2 r h ≤ r) (hs : q m s2 r h ≤ s1) :
    Fintype.card (Block m L s1 s2 r h) =
      ∑ i : Fin (r-q m s2 r h+1), ∑ j : Fin (s1-q m s2 r h+1),
        (L+1-h-q m s2 r h-i.val-j.val) := by
  rw [Fintype.card_congr (blockEquiv m L s1 s2 r h hr hs)]
  simp [BlockSumIndex]

theorem card_block_of_not_le (m L s1 s2 r h : ℕ)
    (hq : ¬ (q m s2 r h ≤ r ∧ q m s2 r h ≤ s1)) :
    Fintype.card (Block m L s1 s2 r h) = 0 := by
  letI : IsEmpty (Block m L s1 s2 r h) := ⟨fun d => by have hd := d.property; omega⟩
  simp

def rectangle (A B C : ℕ) :=
  A*B*C-B*(A*(A-1)/2)-A*(B*(B-1)/2)

theorem sum_fin_val (n : ℕ) : (∑ i : Fin n, i.val) = n*(n-1)/2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i), Finset.sum_range_id]

theorem sum_rectangle (A B C : ℕ) (h : ∀ i : Fin A, ∀ j : Fin B, i.val+j.val ≤ C) :
    (∑ i : Fin A, ∑ j : Fin B, (C-i.val-j.val)) = rectangle A B C := by
  have hs : (∑ i : Fin A, ∑ j : Fin B, ((C-i.val-j.val)+i.val+j.val)) = A*(B*C) := by
    calc
      _ = ∑ _i : Fin A, ∑ _j : Fin B, C := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        have hij := h i j
        omega
      _ = _ := by simp
  have hs' : (∑ i : Fin A, ∑ j : Fin B, (C-i.val-j.val)) +
      B*(A*(A-1)/2)+A*(B*(B-1)/2) = A*(B*C) := by
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum, sum_fin_val] using hs
  unfold rectangle
  rw [mul_assoc]
  omega

theorem card_block_closed (m L s1 s2 r h : ℕ) (hL : m+s1+s2 ≤ L)
    (hrm : r < m) (hhs : h ≤ s2) :
    Fintype.card (Block m L s1 s2 r h) =
      if q m s2 r h ≤ r ∧ q m s2 r h ≤ s1 then
        rectangle (r-q m s2 r h+1) (s1-q m s2 r h+1) (L+1-h-q m s2 r h)
      else 0 := by
  split_ifs with hq
  · rw [card_block_of_le m L s1 s2 r h hq.1 hq.2]
    apply sum_rectangle
    intro i j
    have hi := i.isLt
    have hj := j.isLt
    omega
  · exact card_block_of_not_le m L s1 s2 r h hq

def kernelCell (m L s1 s2 r h : ℕ) : ℕ :=
  if q m s2 r h ≤ r ∧ q m s2 r h ≤ s1 then
    rectangle (r-q m s2 r h+1) (s1-q m s2 r h+1) (L+1-h-q m s2 r h)
  else 0

variable {K : Type*} [Field K]

end
end ProximityPrize.SubmissionLower.SecondJetCounts

end Compact_SecondJetCounts

section Compact_SecondJetFacetCounts
/-! Closed rank counts for the shared R/S degree cap. -/
namespace ProximityPrize.SubmissionLower.SecondJetFacetCounts
open scoped BigOperators
open SecondJetFacetSpace SecondJetFacetRank
open SecondJetRank (Block)
open SecondJetCounts (rectangle sum_rectangle kernelCell card_block_closed)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

variable {K : Type*} [Field K]

end
end ProximityPrize.SubmissionLower.SecondJetFacetCounts

end Compact_SecondJetFacetCounts

section Compact_SecondJetGlobalMap
/-! Global interpolation from finite monomial families and the checked local
rank bound. Concrete coefficient counts and specialization are separate. -/
namespace ProximityPrize.SubmissionLower.SecondJetGlobalMap
open scoped BigOperators
open SecondJetSupport SecondJetBasis SecondJetGlobalSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K I N : Type*} [Field K] [Fintype I] [Fintype N]

def coefficientLocal (e : I → Fin 5 →₀ ℕ) (m : ℕ) (x u0 u1 : K) :
    (I → K) →ₗ[K] Jet (MvPolynomial (Fin 3) K) :=
  (truncateOuter (K := K) m).comp ((flatEquiv (K := K)).toLinearMap.comp
    ((localize x u0 u1).toLinearMap.comp (FiniteMonomials.reconstruct e)))

theorem untruncate_contact {C : Type*} [CommRing C]
    (φ : Jet (MvPolynomial (Fin 3) K) →+* C) (t : C) (m : ℕ)
    (P : Jet (MvPolynomial (Fin 3) K)) (hε : φ Polynomial.X = t)
    (hP : t^m ∣ φ (truncateOuter (K := K) m P)) : t^m ∣ φ P := by
  have hd : t^m ∣ φ ((Polynomial.X^m : Jet (MvPolynomial (Fin 3) K)) *
      (P /ₘ Polynomial.X^m)) := by
    simp only [map_mul, map_pow, hε]
    exact dvd_mul_right _ _
  have heq := congrArg φ (Polynomial.modByMonic_add_div P (Polynomial.X^m))
  rw [map_add] at heq
  exact heq ▸ dvd_add hP hd

end
end ProximityPrize.SubmissionLower.SecondJetGlobalMap

end Compact_SecondJetGlobalMap

section Compact_SecondJetGlobalIndex
/-! Finite coefficient indices for the weighted global second-jet space. -/
namespace ProximityPrize.SubmissionLower.SecondJetGlobalIndex
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

variable {K N : Type*} [Field K] [Fintype N]

end
end ProximityPrize.SubmissionLower.SecondJetGlobalIndex

end Compact_SecondJetGlobalIndex

section Compact_SecondJetGlobalCounts
/-! Closed coefficient counts for the weighted global second-jet space. -/
namespace ProximityPrize.SubmissionLower.SecondJetGlobalCounts
open scoped BigOperators
open SecondJetGlobalIndex
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem sum_range_square_mul_six (n : ℕ) :
    (∑ i ∈ Finset.range n, i^2)*6 = n*(n-1)*(2*n-1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    cases n with
    | zero => simp
    | succ n =>
      have h1 : 2*(n+1)-1 = 2*n+1 := by omega
      have h2 : 2*(n+1+1)-1 = 2*n+3 := by omega
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, h1] at ih
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, h2]
      nlinarith [ih]

theorem sum_fin_square (n : ℕ) :
    (∑ i : Fin n, i.val^2) = n*(n-1)*(2*n-1)/6 := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i^2), ← sum_range_square_mul_six]
  exact (Nat.mul_div_cancel _ (by decide : 0 < 6)).symm

def weightedCell (q w C n : ℕ) : ℕ :=
  n*q*C+w*(n*(n-1)*(2*n-1)/6)-(q+w*C)*(n*(n-1)/2)

theorem sum_weighted_cell (q w C n : ℕ)
    (hq : ∀ y : Fin n, w*y.val ≤ q) (hC : ∀ y : Fin n, y.val ≤ C) :
    (∑ y : Fin n, (q-w*y.val)*(C-y.val)) = weightedCell q w C n := by
  have hcell : ∀ y : Fin n,
      (q-w*y.val)*(C-y.val)+(q+w*C)*y.val = q*C+w*y.val^2 := by
    intro y
    have hqy : q = q-w*y.val+w*y.val := (Nat.sub_add_cancel (hq y)).symm
    have hCy : C = C-y.val+y.val := (Nat.sub_add_cancel (hC y)).symm
    calc
      _ = (q-w*y.val)*(C-y.val)+((q-w*y.val+w*y.val)+w*(C-y.val+y.val))*y.val := by
        conv_lhs => arg 2; arg 1; rw [hqy, hCy]
      _ = (q-w*y.val+w*y.val)*(C-y.val+y.val)+w*y.val^2 := by ring
      _ = _ := by rw [← hqy, ← hCy]
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun y _ => hcell y)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, SecondJetCounts.sum_fin_val, sum_fin_square] at hs
  unfold weightedCell
  rw [mul_comm n q, mul_assoc]
  omega

end
end ProximityPrize.SubmissionLower.SecondJetGlobalCounts

end Compact_SecondJetGlobalCounts

section Compact_SecondJetFacetReceipt
/-! Checked local-rank receipt for the shared R/S degree cap. -/
namespace ProximityPrize.SubmissionLower.SecondJetFacetReceipt
open SecondJetFacetCounts SecondJetFacetRank
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

variable {K : Type*} [Field K]

end ProximityPrize.SubmissionLower.SecondJetFacetReceipt

end Compact_SecondJetFacetReceipt

section Compact_SecondJetGlobalReceipt
/-! Concrete global second-jet interpolation receipt at the proposed 68.04
agreement threshold. The geometric counting argument is not included. -/
namespace ProximityPrize.SubmissionLower.SecondJetGlobalReceipt
open scoped BigOperators
open SecondJetGlobalIndex SecondJetGlobalCounts
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

variable {K N : Type*} [Field K] [Fintype N]

end ProximityPrize.SubmissionLower.SecondJetGlobalReceipt

end Compact_SecondJetGlobalReceipt

section Compact_SecondJetDifferentiation
/-! Differentiation in S loses at most one unit of second-jet contact.
The flat target variables are epsilon, S, T, R, Z. -/
namespace ProximityPrize.SubmissionLower.SecondJetDifferentiation
open scoped BigOperators
open MvPolynomial SecondJetSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

def substitute : Poly (K := K) →ₐ[K] Poly (K := K) :=
  MvPolynomial.aeval ![MvPolynomial.X 0,MvPolynomial.X 1,
    MvPolynomial.X 3-MvPolynomial.X 0*MvPolynomial.X 1+
      MvPolynomial.X 0^2*MvPolynomial.X 2,MvPolynomial.X 3,MvPolynomial.X 4]

theorem chain_X (j : Fin 5) :
    MvPolynomial.X 0*substitute (K := K) (pderiv 1 (MvPolynomial.X j)) =
      MvPolynomial.X 0*pderiv 1 (substitute (K := K) (MvPolynomial.X j))+
        pderiv 2 (substitute (K := K) (MvPolynomial.X j)) := by
  fin_cases j <;> simp [substitute, pderiv_mul, pderiv_pow, Pi.single_apply] <;> ring

theorem chain_rule (P : Poly (K := K)) :
    MvPolynomial.X 0*substitute (K := K) (pderiv 1 P) =
      MvPolynomial.X 0*pderiv 1 (substitute (K := K) P)+
        pderiv 2 (substitute (K := K) P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [substitute]
  | add P Q hP hQ =>
    simp only [map_add]
    linear_combination hP+hQ
  | mul_X P j hP =>
    have hX := chain_X (K := K) j
    simp only [pderiv_mul, map_add, map_mul]
    linear_combination substitute (K := K) (MvPolynomial.X j)*hP + substitute (K := K) P*hX

theorem pderiv_preserves_epsilon (P : Poly (K := K)) (j : Fin 5) (hj : j ≠ 0) (m : ℕ)
    (hP : MvPolynomial.X 0^m ∣ P) : MvPolynomial.X 0^m ∣ pderiv j P := by
  obtain ⟨Q,rfl⟩ := hP
  rw [pderiv_mul, pderiv_pow, pderiv_X_of_ne (Ne.symm hj)]
  simp only [mul_zero, zero_mul, zero_add]
  exact dvd_mul_right _ _

theorem derivative_contact (P : Poly (K := K)) (m : ℕ)
    (hP : MvPolynomial.X 0^(m+1) ∣ substitute (K := K) P) :
    MvPolynomial.X 0^m ∣ substitute (K := K) (pderiv 1 P) := by
  have hs := pderiv_preserves_epsilon (substitute (K := K) P) 1 (by decide) (m+1) hP
  have ht := pderiv_preserves_epsilon (substitute (K := K) P) 2 (by decide) (m+1) hP
  have hh : MvPolynomial.X 0^(m+1) ∣
      MvPolynomial.X 0*substitute (K := K) (pderiv 1 P) := by
    rw [chain_rule]
    exact dvd_add (dvd_mul_of_dvd_right hs _) ht
  rw [pow_succ'] at hh
  exact (mul_dvd_mul_iff_left (MvPolynomial.X_ne_zero (0 : Fin 5))).mp hh

theorem iterate_derivative_contact (P : Poly (K := K)) (m d : ℕ)
    (hP : MvPolynomial.X 0^(m+d) ∣ substitute (K := K) P) :
    MvPolynomial.X 0^m ∣ substitute (K := K) ((pderiv 1)^[d] P) := by
  induction d generalizing P with
  | zero => simpa using hP
  | succ d ih =>
    have hfirst := derivative_contact P (m+d) (by simpa only [Nat.add_assoc] using hP)
    simpa only [Function.iterate_succ_apply] using ih (pderiv 1 P) hfirst

theorem substitute_contact (P : Poly (K := K)) :
    (MvPolynomial.finSuccEquiv K 4) (substitute (K := K) P) =
      SecondJetLocal.contact (K := K) (flatEquiv (K := K) P) := by
  have h0 : (MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X (0 : Fin 5)) = Polynomial.X :=
    MvPolynomial.finSuccEquiv_X_zero
  have h1 : (MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X (1 : Fin 5)) =
      Polynomial.C (MvPolynomial.X (0 : Fin 4)) := MvPolynomial.finSuccEquiv_X_succ (j := 0)
  have h2 : (MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X (2 : Fin 5)) =
      Polynomial.C (MvPolynomial.X (1 : Fin 4)) := MvPolynomial.finSuccEquiv_X_succ (j := 1)
  have h3 : (MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X (3 : Fin 5)) =
      Polynomial.C (MvPolynomial.X (2 : Fin 4)) := MvPolynomial.finSuccEquiv_X_succ (j := 2)
  have h4 : (MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X (4 : Fin 5)) =
      Polynomial.C (MvPolynomial.X (3 : Fin 4)) := MvPolynomial.finSuccEquiv_X_succ (j := 3)
  have h : (MvPolynomial.finSuccEquiv K 4).toAlgHom.comp (substitute (K := K)) =
      (SecondJetLocal.contact (K := K)).comp (flatEquiv (K := K)).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro j
    fin_cases j <;>
      simp [substitute, SecondJetSupport.flatEquiv_X, SecondJetLocal.baseEval,
        h0, h1, h2, h3, h4] <;> ring
  exact DFunLike.congr_fun h P

end
end ProximityPrize.SubmissionLower.SecondJetDifferentiation

end Compact_SecondJetDifferentiation

section Compact_SecondJetGlobalDifferentiation
/-! Support and local-contact behavior of global S derivatives. -/
namespace ProximityPrize.SubmissionLower.SecondJetGlobalDifferentiation
open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetDifferentiation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

theorem support_pderiv (P : Poly (K := K)) (d : Fin 5 →₀ ℕ)
    (hd : d ∈ (pderiv 1 P).support) : d+Finsupp.single 1 1 ∈ P.support := by
  have h := MvPolynomial.mem_support_iff.mp hd
  rw [MvPolynomial.coeff_pderiv] at h
  apply MvPolynomial.mem_support_iff.mpr
  intro hz
  exact h (by rw [hz, zero_mul])

theorem support_iterate (P : Poly (K := K)) (n : ℕ) (d : Fin 5 →₀ ℕ)
    (hd : d ∈ ((pderiv 1)^[n] P).support) : d+Finsupp.single 1 n ∈ P.support := by
  induction n generalizing d with
  | zero => simpa using hd
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at hd
    have hh := ih (d+Finsupp.single 1 1) (support_pderiv _ d hd)
    have he : d+Finsupp.single 1 1+Finsupp.single 1 n = d+Finsupp.single 1 (n+1) := by
      rw [add_assoc, ← Finsupp.single_add, Nat.add_comm 1 n]
    rwa [he] at hh

theorem localize_pderiv (x u0 u1 : K) (P : Poly (K := K)) :
    localize x u0 u1 (pderiv 1 P) = pderiv 1 (localize x u0 u1 P) := by
  have hX (j : Fin 5) : localize x u0 u1 (pderiv 1 (MvPolynomial.X j)) =
      pderiv 1 (localize x u0 u1 (MvPolynomial.X j)) := by
    fin_cases j <;> simp [localize, pderiv_mul, Pi.single_apply]
  induction P using MvPolynomial.induction_on with
  | C c => simp [localize]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P j hP => simp only [pderiv_mul, map_add, map_mul, hP, hX]

theorem localize_iterate (x u0 u1 : K) (P : Poly (K := K)) (n : ℕ) :
    localize x u0 u1 ((pderiv 1)^[n] P) = (pderiv 1)^[n] (localize x u0 u1 P) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', localize_pderiv, ih]

theorem local_derivative_contact (x u0 u1 : K) (P : Poly (K := K)) (m d : ℕ)
    (hP : MvPolynomial.X 0^(m+d) ∣ substitute (K := K) (localize x u0 u1 P)) :
    MvPolynomial.X 0^m ∣ substitute (K := K) (localize x u0 u1 ((pderiv 1)^[d] P)) := by
  rw [localize_iterate]
  exact iterate_derivative_contact (localize x u0 u1 P) m d hP

theorem nested_to_flat_contact (P : Poly (K := K)) (m : ℕ)
    (hP : Polynomial.X^m ∣ SecondJetLocal.contact (K := K) (flatEquiv (K := K) P)) :
    MvPolynomial.X 0^m ∣ substitute (K := K) P := by
  obtain ⟨Q,hQ⟩ := hP
  refine ⟨(MvPolynomial.finSuccEquiv K 4).symm Q,?_⟩
  apply (MvPolynomial.finSuccEquiv K 4).injective
  rw [substitute_contact, map_mul, map_pow, MvPolynomial.finSuccEquiv_X_zero,
    AlgEquiv.apply_symm_apply]
  exact hQ

end
end ProximityPrize.SubmissionLower.SecondJetGlobalDifferentiation

end Compact_SecondJetGlobalDifferentiation

section Compact_SecondJet6804
/-! A concrete interpolant and its first three S derivatives have enough
contact and sufficiently small weight at 181353 agreements. -/
namespace ProximityPrize.SubmissionLower.SecondJet6804
open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetDifferentiation
open SecondJetGlobalDifferentiation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K N : Type*} [Field K] [Fintype N]

end
end ProximityPrize.SubmissionLower.SecondJet6804

end Compact_SecondJet6804

section Compact_SecondJetContact
/-! The contact identity behind the exploratory second-derivative space.
This establishes the local algebra only, not the rank calculations or a
stronger protocol claim. Hasse derivatives avoid a characteristic-two
exception in the identity itself. -/
namespace ProximityPrize.SubmissionLower.SecondJetContact
open Polynomial
noncomputable section
set_option autoImplicit false

variable {K : Type*} [CommRing K]

theorem second_contact_residue (q : Polynomial K) :
    (Polynomial.X : Polynomial K)^3 ∣
      q - C (q.coeff 0) - Polynomial.X*q.derivative + Polynomial.X^2*hasseDeriv 2 q := by
  rw [X_pow_dvd_iff]
  intro d hd
  interval_cases d <;>
    simp [coeff_sub, coeff_add, coeff_X_pow_mul', coeff_X_mul,
      coeff_derivative, hasseDeriv_coeff] <;> ring

theorem exists_second_contact_expansion (q : Polynomial K) :
    ∃ U : Polynomial K,
      q - C (q.coeff 0) =
        Polynomial.X * (q.derivative - Polynomial.X*hasseDeriv 2 q + Polynomial.X^2*U) := by
  obtain ⟨U, hU⟩ := second_contact_residue q
  refine ⟨U, ?_⟩
  linear_combination hU

theorem taylor_second_contact (f : Polynomial K) (x : K) :
    ∃ U : Polynomial K,
      taylor x f - C (f.eval x) =
        Polynomial.X * ((taylor x f).derivative - Polynomial.X*hasseDeriv 2 (taylor x f) + Polynomial.X^2*U) := by
  simpa only [taylor_coeff_zero] using exists_second_contact_expansion (taylor x f)

end
end ProximityPrize.SubmissionLower.SecondJetContact

end Compact_SecondJetContact

section Compact_SecondJetSpecialize
/-! From formal second-jet contact to ordinary polynomial root multiplicity. -/
namespace ProximityPrize.SubmissionLower.SecondJetSpecialize
open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetDifferentiation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K : Type*} [Field K]

theorem hasse_taylor (f : Polynomial K) (x : K) (n : ℕ) :
    Polynomial.hasseDeriv n (Polynomial.taylor x f) =
      Polynomial.taylor x (Polynomial.hasseDeriv n f) := by
  ext i
  rw [Polynomial.hasseDeriv_coeff, Polynomial.taylor_coeff, Polynomial.taylor_coeff]
  have hc := congrArg (fun T : Polynomial K →ₗ[K] Polynomial K => (T f).eval x)
    (Polynomial.hasseDeriv_comp (R := K) i n)
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, Polynomial.eval_smul,
    nsmul_eq_mul] at hc
  rw [hc]
  simp [Nat.choose_symm_add, mul_comm]

theorem derivative_taylor (f : Polynomial K) (x : K) :
    (Polynomial.taylor x f).derivative = Polynomial.taylor x f.derivative := by
  simpa only [Polynomial.hasseDeriv_one] using hasse_taylor f x 1

def specialize (f : Polynomial K) (z : K) : Poly (K := K) →ₐ[K] Polynomial K :=
  MvPolynomial.aeval ![Polynomial.X,Polynomial.hasseDeriv 2 f,f,f.derivative,Polynomial.C z]

def realize (q U : Polynomial K) (z : K) : Poly (K := K) →ₐ[K] Polynomial K :=
  MvPolynomial.aeval ![Polynomial.X,Polynomial.hasseDeriv 2 q,U,q.derivative,Polynomial.C z]

theorem realize_contact (f U : Polynomial K) (x u0 u1 z : K)
    (hagree : f.eval x = u0+u1*z)
    (hU : Polynomial.taylor x f-Polynomial.C (f.eval x) =
      Polynomial.X*((Polynomial.taylor x f).derivative-
        Polynomial.X*Polynomial.hasseDeriv 2 (Polynomial.taylor x f)+Polynomial.X^2*U))
    (P : Poly (K := K)) :
    realize (Polynomial.taylor x f) U z (substitute (K := K) (localize x u0 u1 P)) =
      Polynomial.taylor x (specialize f z P) := by
  have heq : (realize (Polynomial.taylor x f) U z).comp
      ((substitute (K := K)).comp (localize x u0 u1)) =
      (Polynomial.taylorAlgHom x).comp (specialize f z) := by
    apply MvPolynomial.algHom_ext
    intro j
    fin_cases j <;>
      simp [realize, substitute, localize, specialize, hasse_taylor, derivative_taylor]
    · ring
    · rw [hagree, map_add, map_mul] at hU
      simp only [derivative_taylor, hasse_taylor] at hU
      linear_combination -hU
  exact DFunLike.congr_fun heq P

theorem root_contact (P : Poly (K := K)) (f : Polynomial K) (x u0 u1 z : K) (m : ℕ)
    (hagree : f.eval x = u0+u1*z)
    (hP : MvPolynomial.X 0^m ∣ substitute (K := K) (localize x u0 u1 P)) :
    (Polynomial.X-Polynomial.C x)^m ∣ specialize f z P := by
  obtain ⟨U,hU⟩ := SecondJetContact.taylor_second_contact f x
  have hd := map_dvd (realize (Polynomial.taylor x f) U z).toRingHom hP
  change realize (Polynomial.taylor x f) U z (MvPolynomial.X 0^m) ∣
    realize (Polynomial.taylor x f) U z (substitute (K := K) (localize x u0 u1 P)) at hd
  rw [map_pow, realize_contact f U x u0 u1 z hagree hU P] at hd
  have hx : realize (Polynomial.taylor x f) U z (MvPolynomial.X 0) = Polynomial.X := by
    simp [realize]
  rw [hx] at hd
  obtain ⟨Q,hQ⟩ := hd
  refine ⟨(Polynomial.taylorEquiv x).symm Q,?_⟩
  apply Polynomial.taylor_injective x
  rw [Polynomial.taylor_mul, Polynomial.taylor_pow]
  have hh : Polynomial.taylor x (Polynomial.X-Polynomial.C x) = Polynomial.X := by simp
  rw [hh]
  change Polynomial.taylor x (specialize f z P) = Polynomial.X^m*
    ((Polynomial.taylorEquiv x) ((Polynomial.taylorEquiv x).symm Q))
  rw [AlgEquiv.apply_symm_apply]
  exact hQ

theorem monomial_degree (f : Polynomial K) (z : K) (w : ℕ) (hf : f.natDegree ≤ w)
    (d : Fin 5 →₀ ℕ) (c : K) :
    (specialize f z (MvPolynomial.monomial d c)).natDegree ≤
      d 0+w*d 2+(w-1)*d 3+(w-2)*d 1 := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
  · simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, map_mul, map_pow]
    have hc : (specialize f z (MvPolynomial.C c)).natDegree ≤ 0 := by simp [specialize]
    have h0 : (specialize f z (MvPolynomial.X 0)^d 0).natDegree ≤ d 0 := by simp [specialize]
    have hs : (Polynomial.hasseDeriv 2 f).natDegree ≤ w-2 :=
      (Polynomial.natDegree_hasseDeriv_le f 2).trans (Nat.sub_le_sub_right hf 2)
    have hr : f.derivative.natDegree ≤ w-1 :=
      (Polynomial.natDegree_derivative_le f).trans (Nat.sub_le_sub_right hf 1)
    have h1 : (specialize f z (MvPolynomial.X 1)^d 1).natDegree ≤ d 1*(w-2) := by
      simpa [specialize] using Polynomial.natDegree_pow_le_of_le (d 1) hs
    have h2 : (specialize f z (MvPolynomial.X 2)^d 2).natDegree ≤ d 2*w := by
      simpa [specialize] using Polynomial.natDegree_pow_le_of_le (d 2) hf
    have h3 : (specialize f z (MvPolynomial.X 3)^d 3).natDegree ≤ d 3*(w-1) := by
      simpa [specialize] using Polynomial.natDegree_pow_le_of_le (d 3) hr
    have h4 : (specialize f z (MvPolynomial.X 4)^d 4).natDegree ≤ 0 := by simp [specialize]
    have hh := Polynomial.natDegree_mul_le_of_le hc (Polynomial.natDegree_mul_le_of_le h0
      (Polynomial.natDegree_mul_le_of_le h1 (Polynomial.natDegree_mul_le_of_le h2
        (Polynomial.natDegree_mul_le_of_le h3 h4))))
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm] using hh
  · intro i
    simp

theorem specialization_degree (P : Poly (K := K)) (f : Polynomial K) (z : K) (w D : ℕ)
    (hf : f.natDegree ≤ w) (hD : 0 < D)
    (hP : ∀ d ∈ P.support, d 0+w*d 2+(w-1)*d 3+(w-2)*d 1 < D) :
    (specialize f z P).natDegree < D := by
  classical
  have hterms : ∀ d ∈ P.support,
      (specialize f z (MvPolynomial.monomial d (MvPolynomial.coeff d P))).natDegree ≤ D-1 := by
    intro d hd
    have hw := hP d hd
    have hh := monomial_degree f z w hf d (MvPolynomial.coeff d P)
    omega
  rw [MvPolynomial.as_sum P, map_sum]
  have hh := Polynomial.natDegree_sum_le_of_forall_le P.support
    (fun d => specialize f z (MvPolynomial.monomial d (MvPolynomial.coeff d P))) hterms
  exact lt_of_le_of_lt hh (by omega)

end
end ProximityPrize.SubmissionLower.SecondJetSpecialize

end Compact_SecondJetSpecialize

section Compact_SecondJetVanish
/-! A second-jet interpolant vanishes on every codeword with enough agreements. -/
namespace ProximityPrize.SubmissionLower.SecondJetVanish
open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetDifferentiation SecondJetSpecialize
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K N : Type*} [Field K]
local instance  _root_.ProximityPrize.SubmissionLower.SecondJetVanish.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.SecondJetVanish.instDecidableEq_proximityPrize_1 : DecidableEq N := Classical.decEq N

theorem eq_zero_of_contact_degree (P : Poly (K := K)) (f : Polynomial K) (z : K)
    (nodes : N ↪ K) (u0 u1 : N → K) (S : Finset N) (m : ℕ)
    (hcontact : ∀ i ∈ S, MvPolynomial.X 0^m ∣ substitute (K := K)
      (localize (nodes i) (u0 i) (u1 i) P))
    (hvalues : ∀ i ∈ S, f.eval (nodes i) = u0 i+u1 i*z)
    (hdegree : (specialize f z P).natDegree < m*S.card) : specialize f z P = 0 := by
  classical
  by_contra hn
  have hmult : ∀ i ∈ S, m ≤ (specialize f z P).rootMultiplicity (nodes i) := by
    intro i hi
    exact (Polynomial.le_rootMultiplicity_iff hn).mpr
      (root_contact P f (nodes i) (u0 i) (u1 i) z m (hvalues i hi) (hcontact i hi))
  have hh := BCHKSSubstitutionVanish.mul_card_le_natDegree_of_rootMultiplicity
    (specialize f z P) nodes S m hmult
  exact (Nat.not_le_of_gt hdegree) hh

variable [Fintype N]

end
end ProximityPrize.SubmissionLower.SecondJetVanish

end Compact_SecondJetVanish

section Compact_SecondJetCoefficients
/-! Viewing the interpolant as a polynomial in its second derivative variable.
Coefficient variables are X, Y, R, Z. -/
namespace ProximityPrize.SubmissionLower.SecondJetCoefficients
open MvPolynomial SecondJetSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

def asS : Poly (K := K) ≃ₐ[K] Polynomial (MvPolynomial (Fin 4) K) :=
  (MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 5) 1)).trans (MvPolynomial.finSuccEquiv K 4)

def liftExponent (j : ℕ) (d : Fin 4 →₀ ℕ) : Fin 5 →₀ ℕ :=
  Finsupp.mapDomain (Equiv.swap (0 : Fin 5) 1) (d.cons j)

theorem swap_lift (j : ℕ) (d : Fin 4 →₀ ℕ) :
    Finsupp.mapDomain (Equiv.swap (0 : Fin 5) 1) (liftExponent j d) = d.cons j := by
  ext i
  simp [liftExponent, Finsupp.mapDomain_equiv_apply]

theorem lift_coordinates (j : ℕ) (d : Fin 4 →₀ ℕ) :
    liftExponent j d 0 = d 0 ∧ liftExponent j d 1 = j ∧
      liftExponent j d 2 = d 1 ∧ liftExponent j d 3 = d 2 ∧ liftExponent j d 4 = d 3 := by
  simp [liftExponent, Finsupp.mapDomain_equiv_apply, Equiv.swap_apply_def, Fin.ext_iff]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem asS_coeff (P : Poly (K := K)) (j : ℕ) (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d ((asS (K := K) P).coeff j) =
      MvPolynomial.coeff (liftExponent j d) P := by
  change MvPolynomial.coeff d (((MvPolynomial.finSuccEquiv K 4)
    (MvPolynomial.rename (Equiv.swap (0 : Fin 5) 1) P)).coeff j) = _
  rw [MvPolynomial.finSuccEquiv_coeff_coeff, ← swap_lift j d,
    MvPolynomial.coeff_rename_mapDomain _ (Equiv.swap (0 : Fin 5) 1).injective]

theorem coefficient_support (P : Poly (K := K)) (j : ℕ) (d : Fin 4 →₀ ℕ)
    (hd : d ∈ ((asS (K := K) P).coeff j).support) : liftExponent j d ∈ P.support := by
  simpa only [MvPolynomial.mem_support_iff, asS_coeff] using hd

end
end ProximityPrize.SubmissionLower.SecondJetCoefficients

end Compact_SecondJetCoefficients

section Compact_RootMultiplicityValuation
/-! Coefficient bounds after removing a rational root. This is the local
valuation ingredient for a proposed root-multiplicity height estimate. -/
namespace ProximityPrize.SubmissionLower.RootMultiplicityValuation
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {L : Type*} [Field L]
abbrev Value := WithZero (Multiplicative ℤ)

def polyValue (v : Valuation L Value) (P : Polynomial L) : Value :=
  P.support.sup (fun i => v (P.coeff i))

end
end ProximityPrize.SubmissionLower.RootMultiplicityValuation

end Compact_RootMultiplicityValuation

section Compact_RootMultiplicityHeight
/-! A rational root of high multiplicity has bounded height. The coefficient
pole bound is summed over places using the principal-divisor identity. -/
namespace ProximityPrize.SubmissionLower.RootMultiplicityHeight
open scoped Classical BigOperators WithZero
open RCN026 RCN187 RootMultiplicityValuation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosed K]
  [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

theorem log_sum_zero_of_contains (c : L) (hc : c ≠ 0) (W : Finset (Place K L))
    (hW : placesFor K L c hc ⊆ W) : (∑ v ∈ W, (v.val c).log) = 0 := by
  classical
  have hz : (∑ v ∈ placesFor K L c hc, (v.val c).log) = 0 := by
    simpa only [order, Finset.sum_neg_distrib, neg_eq_zero] using
      sum_placesFor_order_zero K L c hc
  calc
    (∑ v ∈ W, (v.val c).log) = ∑ v ∈ placesFor K L c hc, (v.val c).log := by
      symm
      apply Finset.sum_subset hW
      intro v hv hnot
      have ho : order K L v c = 0 := by
        by_contra h
        exact hnot (placesFor_covers K L c hc v h)
      simpa only [order, neg_eq_zero] using ho
    _ = 0 := hz

end
end ProximityPrize.SubmissionLower.RootMultiplicityHeight

end Compact_RootMultiplicityHeight

section Compact_RootMultiplicityFlag
/-! Interface from bounded polynomial coefficients to the moving-coordinate
height bound used in the lower submission's flag geometry. -/
namespace ProximityPrize.SubmissionLower.RootMultiplicityFlag
open scoped Classical BigOperators WithZero
open RCN026 RCN095 RCN187 RCN204
open RCN344 (constant_value_le_one)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosed K]
  [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

end
end ProximityPrize.SubmissionLower.RootMultiplicityFlag

end Compact_RootMultiplicityFlag

section Compact_SecondJetFlagCoefficients
/-! Frozen coefficient flags for the second-jet interpolant. -/
namespace ProximityPrize.SubmissionLower.SecondJetFlagCoefficients
open scoped BigOperators
open MvPolynomial RCN095 SecondJetCoefficients SecondJetSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K : Type*} [Field K]

def freeze (x : K) : MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 3) K :=
  MvPolynomial.aeval ![MvPolynomial.C x,MvPolynomial.X 0,MvPolynomial.X 1,MvPolynomial.X 2]

theorem freeze_monomial (x : K) (d : Fin 4 →₀ ℕ) (c : K) :
    freeze x (MvPolynomial.monomial d c) = MvPolynomial.monomial d.tail (c*x^d 0) := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
  · rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
    · simp [freeze, Fin.prod_univ_four, Fin.prod_univ_three, Finsupp.tail_apply,
        map_mul, map_pow, mul_assoc]
    · intro i
      simp
  · intro i
    simp

theorem freeze_inFlag (P : MvPolynomial (Fin 4) K) (x : K) (p : FlagDegree)
    (hP : ∀ d ∈ P.support, InFlag p d.tail) : PolynomialInFlag p (freeze x P) := by
  rw [MvPolynomial.as_sum P, map_sum]
  intro e he
  obtain ⟨d,hd,hed⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum he)
  rw [freeze_monomial] at hed
  have heq : e = d.tail := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hed)
  subst e
  exact hP d hd

end
end ProximityPrize.SubmissionLower.SecondJetFlagCoefficients

end Compact_SecondJetFlagCoefficients

section Compact_RootMultiplicityWeightedValuation
/-! Weighted coefficient bounds retain the degree of the remaining factor.
This is a valuation lemma, not a lower-track protocol claim. -/
namespace ProximityPrize.SubmissionLower.RootMultiplicityWeightedValuation
open scoped BigOperators WithZero
open RootMultiplicityValuation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {L : Type*} [Field L]

theorem weighted_sub_le (v : Valuation L Value) (x y : L) (b B : Value)
    (hx : v x*b ≤ B) (hy : v y*b ≤ B) : v (x-y)*b ≤ B := by
  exact (mul_le_mul_left (v.map_sub x y) b).trans (by rw [max_mul]; exact max_le hx hy)

theorem weighted_add_le (v : Valuation L Value) (x y : L) (b B : Value)
    (hx : v x*b ≤ B) (hy : v y*b ≤ B) : v (x+y)*b ≤ B := by
  exact (mul_le_mul_left (v.map_add x y) b).trans (by rw [max_mul]; exact max_le hx hy)

theorem coeff_bound_large (v : Valuation L Value) (b : Value) (t : L)
    (Q : Polynomial L) (B : Value) (ht : b ≤ v t)
    (hP : ∀ i, v (((Polynomial.X-Polynomial.C t)*Q).coeff i)*b^i ≤ B) :
    ∀ i, v (Q.coeff i)*b^i*v t ≤ B := by
  intro i
  induction i with
  | zero =>
    simpa [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul, map_mul,
      mul_comm] using hP 0
  | succ i ih =>
    have hprev : v (Q.coeff i)*b^(i+1) ≤ B := by
      rw [pow_succ, ← mul_assoc]
      exact (mul_le_mul_right ht _).trans ih
    have heq : t*Q.coeff (i+1) = Q.coeff i-((Polynomial.X-Polynomial.C t)*Q).coeff (i+1) := by
      simp only [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul]
      ring
    have hb := weighted_sub_le v _ _ _ _ hprev (hP (i+1))
    rw [← heq, map_mul] at hb
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hb

theorem coeff_bound_small (v : Valuation L Value) (b : Value) (t : L)
    (Q : Polynomial L) (B : Value) (ht : v t ≤ b)
    (hP : ∀ i, v (((Polynomial.X-Polynomial.C t)*Q).coeff i)*b^i ≤ B) :
    ∀ i, v (Q.coeff i)*b^i*b ≤ B := by
  have hbound : ∀ n i : ℕ, Q.natDegree+1 ≤ i+n → v (Q.coeff i)*b^i*b ≤ B := by
    intro n
    induction n with
    | zero =>
      intro i hi
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero, zero_mul, zero_mul]
      exact zero_le
    | succ n ih =>
      intro i hi
      have hnext := ih (i+1) (by omega)
      have hmul : v (t*Q.coeff (i+1))*b^(i+1) ≤ B := by
        rw [map_mul]
        have hb := (mul_le_mul_right ht (v (Q.coeff (i+1))*b^(i+1))).trans hnext
        simpa only [mul_comm, mul_left_comm, mul_assoc] using hb
      have heq : Q.coeff i = ((Polynomial.X-Polynomial.C t)*Q).coeff (i+1)+t*Q.coeff (i+1) := by
        simp only [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul]
        ring
      rw [mul_assoc, ← pow_succ, heq]
      exact weighted_add_le v _ _ _ _ (hP (i+1)) hmul
  exact fun i => hbound (Q.natDegree+1) i (by omega)

theorem coeff_bound_linear_factor (v : Valuation L Value) (b : Value) (t : L)
    (Q : Polynomial L) (B : Value)
    (hP : ∀ i, v (((Polynomial.X-Polynomial.C t)*Q).coeff i)*b^i ≤ B) :
    ∀ i, v (Q.coeff i)*b^i*max b (v t) ≤ B := by
  by_cases ht : b ≤ v t
  · rw [max_eq_right ht]
    exact coeff_bound_large v b t Q B ht hP
  · rw [max_eq_left (le_of_not_ge ht)]
    exact coeff_bound_small v b t Q B (le_of_not_ge ht) hP

def weightedValue (v : Valuation L Value) (b : Value) (P : Polynomial L) : Value :=
  P.support.sup (fun i => v (P.coeff i)*b^i)

theorem coeff_le_weightedValue (v : Valuation L Value) (b : Value) (P : Polynomial L) (i : ℕ) :
    v (P.coeff i)*b^i ≤ weightedValue v b P := by
  classical
  by_cases hi : i ∈ P.support
  · exact Finset.le_sup (f := fun i => v (P.coeff i)*b^i) hi
  · have hz : P.coeff i = 0 := by simpa only [Polynomial.mem_support_iff, not_not] using hi
    rw [hz, map_zero, zero_mul]
    exact zero_le

theorem weightedValue_le (v : Valuation L Value) (b : Value) (P : Polynomial L) (B : Value)
    (h : ∀ i, v (P.coeff i)*b^i ≤ B) : weightedValue v b P ≤ B := by
  exact Finset.sup_le (fun i _ => h i)

theorem weightedValue_linear_factor (v : Valuation L Value) (b : Value) (t : L) (Q : Polynomial L) :
    weightedValue v b Q*max b (v t) ≤ weightedValue v b ((Polynomial.X-Polynomial.C t)*Q) := by
  classical
  by_cases hQ : Q = 0
  · subst Q
    simp [weightedValue]
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Q.support
    (Polynomial.support_nonempty.mpr hQ) (fun i => v (Q.coeff i)*b^i)
  change Q.support.sup (fun i => v (Q.coeff i)*b^i)*_ ≤ _
  rw [hi]
  exact coeff_bound_linear_factor v b t Q _ (coeff_le_weightedValue v b _) i

theorem weightedValue_pow_factor (v : Valuation L Value) (b : Value) (t : L)
    (Q : Polynomial L) (d : ℕ) :
    weightedValue v b Q*(max b (v t))^d ≤
      weightedValue v b ((Polynomial.X-Polynomial.C t)^d*Q) := by
  induction d with
  | zero => simp
  | succ d ih =>
    calc
      weightedValue v b Q*(max b (v t))^(d+1) =
          (weightedValue v b Q*(max b (v t))^d)*max b (v t) := by rw [pow_succ, mul_assoc]
      _ ≤ weightedValue v b ((Polynomial.X-Polynomial.C t)^d*Q)*max b (v t) :=
        mul_le_mul_left ih _
      _ ≤ weightedValue v b ((Polynomial.X-Polynomial.C t)*((Polynomial.X-Polynomial.C t)^d*Q)) :=
        weightedValue_linear_factor v b t _
      _ = weightedValue v b ((Polynomial.X-Polynomial.C t)^(d+1)*Q) := by
        rw [pow_succ']; congr 1; ring

theorem coeff_bound_pow_factor (v : Valuation L Value) (b : Value) (t : L)
    (Q : Polynomial L) (d : ℕ) (B : Value)
    (hP : ∀ i, v (((Polynomial.X-Polynomial.C t)^d*Q).coeff i)*b^i ≤ B) (i : ℕ) :
    v (Q.coeff i)*b^i*(max b (v t))^d ≤ B := by
  exact (mul_le_mul_left (coeff_le_weightedValue v b Q i) _).trans
    ((weightedValue_pow_factor v b t Q d).trans (weightedValue_le v b _ B hP))

end
end ProximityPrize.SubmissionLower.RootMultiplicityWeightedValuation

end Compact_RootMultiplicityWeightedValuation

section Compact_RootMultiplicityWeightedHeight
/-! Weighted root height, including the contribution of the remaining degree.
All coefficient and budget hypotheses are explicit. This module does not
construct a new interpolation space or establish a protocol claim. -/
namespace ProximityPrize.SubmissionLower.RootMultiplicityWeightedHeight
open scoped Classical BigOperators WithZero
open RCN026 RCN187 RootMultiplicityValuation RootMultiplicityHeight
open RootMultiplicityWeightedValuation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {L : Type*} [Field L]

theorem log_max_exp (v : Valuation L Value) (t : L) (lambda : ℤ) (hl : 0 ≤ lambda) :
    (max (WithZero.exp lambda) (v t)).log = max lambda (poleOrder v t) := by
  by_cases ht : v t = 0
  · simp [ht, poleOrder, max_eq_left hl]
  by_cases h : WithZero.exp lambda ≤ v t
  · have hlog : lambda ≤ (v t).log := by
      rw [← WithZero.exp_log ht] at h
      exact WithZero.exp_le_exp.mp h
    rw [max_eq_right h]
    simp only [poleOrder, max_eq_right (hl.trans hlog), max_eq_right hlog]
  · have hv : v t ≤ WithZero.exp lambda := le_of_not_ge h
    have hlog := (WithZero.log_le_iff_le_exp ht).mpr hv
    rw [max_eq_left hv]
    simp only [WithZero.log_exp, poleOrder, max_eq_left (max_le hl hlog)]

theorem coeff_weighted_of_affine (v : Valuation L Value) (P : Polynomial L)
    (B lambda : ℤ)
    (hP : ∀ i, v (P.coeff i) ≤ WithZero.exp (B-(i : ℤ)*lambda)) :
    ∀ i, v (P.coeff i)*(WithZero.exp lambda)^i ≤ WithZero.exp B := by
  intro i
  calc
    v (P.coeff i)*(WithZero.exp lambda)^i ≤
        WithZero.exp (B-(i : ℤ)*lambda)*(WithZero.exp lambda)^i :=
      mul_le_mul_left (hP i) _
    _ = WithZero.exp B := by
      rw [← WithZero.exp_nsmul, ← WithZero.exp_add]
      simp

theorem coeff_log_bound_pow_factor (v : Valuation L Value) (t : L)
    (Q : Polynomial L) (d : ℕ) (B lambda : ℤ) (hl : 0 ≤ lambda)
    (hP : ∀ i, v (((Polynomial.X-Polynomial.C t)^d*Q).coeff i)*
      (WithZero.exp lambda)^i ≤ WithZero.exp B)
    (i : ℕ) (hi : Q.coeff i ≠ 0) :
    (v (Q.coeff i)).log+(i : ℤ)*lambda+
      (d : ℤ)*max lambda (poleOrder v t) ≤ B := by
  have hv : v (Q.coeff i) ≠ 0 := v.ne_zero_iff.mpr hi
  have hb : (WithZero.exp lambda : Value) ≠ 0 := WithZero.exp_ne_zero
  have ht : max (WithZero.exp lambda) (v t) ≠ 0 := by
    intro h
    have hle := le_max_left (WithZero.exp lambda) (v t)
    rw [h] at hle
    exact hb (le_antisymm hle zero_le)
  have hh := (WithZero.log_le_iff_le_exp
    (mul_ne_zero (mul_ne_zero hv (pow_ne_zero i hb)) (pow_ne_zero d ht))).mpr
    (RootMultiplicityWeightedValuation.coeff_bound_pow_factor
      v (WithZero.exp lambda) t Q d (WithZero.exp B) hP i)
  simpa only [WithZero.log_mul (mul_ne_zero hv (pow_ne_zero i hb)) (pow_ne_zero d ht),
    WithZero.log_mul hv (pow_ne_zero i hb), WithZero.log_pow, WithZero.log_exp,
    nsmul_eq_mul, log_max_exp v t lambda hl] using hh

theorem finite_log_height_bound {ι : Type*} (W : Finset ι)
    (v : ι → Valuation L Value) (t : L) (Q : Polynomial L) (d : ℕ)
    (B lambda : ι → ℤ) (hl : ∀ w ∈ W, 0 ≤ lambda w)
    (hP : ∀ w ∈ W, ∀ i, v w (((Polynomial.X-Polynomial.C t)^d*Q).coeff i)*
      (WithZero.exp (lambda w))^i ≤ WithZero.exp (B w))
    (i : ℕ) (hi : Q.coeff i ≠ 0)
    (hbalance : (∑ w ∈ W, (v w (Q.coeff i)).log) = 0) :
    (i : ℤ)*(∑ w ∈ W, lambda w)+
      (d : ℤ)*(∑ w ∈ W, max (lambda w) (poleOrder (v w) t)) ≤ ∑ w ∈ W, B w := by
  have hsum := Finset.sum_le_sum (fun w hw =>
    coeff_log_bound_pow_factor (v w) t Q d (B w) (lambda w) (hl w hw) (hP w hw) i hi)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, hbalance, zero_add] using hsum

section FunctionField
variable (K : Type*) [Field K] [Algebra K L] [IsAlgClosed K]
  [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

/-- A moving-pole estimate using the affine coefficient bound with weight
`2*alpha-beta`. Its budget hypothesis retains the cofactor degree exactly. -/
theorem moving_height_bound (P : Polynomial L) (hP : P ≠ 0) (t : L) (d : ℕ)
    (hd : (Polynomial.X-Polynomial.C t)^d ∣ P)
    (B alpha beta : Place K L → ℤ) (C : ℤ)
    (ha : ∀ v, 0 ≤ alpha v) (hba : ∀ v, beta v ≤ alpha v)
    (hcoeff : ∀ v (i : ℕ), v.val (P.coeff i) ≤
      WithZero.exp (B v-(i : ℤ)*(2*alpha v-beta v)))
    (hbudget : ∀ V : Finset (Place K L),
      (∑ v ∈ V, (B v+(d : ℤ)*beta v-
        ((P.natDegree-d : ℕ) : ℤ)*(2*alpha v-beta v))) ≤ C)
    (W : Finset (Place K L)) :
    (d : ℤ)*(∑ v ∈ W, max (2*alpha v) (beta v+poleOrder v.val t)) ≤ C := by
  obtain ⟨Q, rfl⟩ := hd
  have hQ : Q ≠ 0 := right_ne_zero_of_mul hP
  have hf : (Polynomial.X-Polynomial.C t)^d ≠ 0 := left_ne_zero_of_mul hP
  have hi : Q.coeff Q.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
  have hdeg : ((Polynomial.X-Polynomial.C t)^d*Q).natDegree-d = Q.natDegree := by
    rw [Polynomial.natDegree_mul hf hQ, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
    omega
  simp only [hdeg] at hbudget
  let V := W ∪ placesFor K L (Q.coeff Q.natDegree) hi
  have hbalance := log_sum_zero_of_contains K L (Q.coeff Q.natDegree) hi V
    Finset.subset_union_right
  have hl : ∀ v, 0 ≤ 2*alpha v-beta v := by intro v; have := ha v; have := hba v; omega
  have hh := finite_log_height_bound V (fun v => v.val) t Q d B
    (fun v => 2*alpha v-beta v) (fun v _ => hl v)
    (fun v _ => coeff_weighted_of_affine v.val _ _ _ (hcoeff v)) Q.natDegree hi hbalance
  have heq (v : Place K L) :
      max (2*alpha v) (beta v+poleOrder v.val t) =
        beta v+max (2*alpha v-beta v) (poleOrder v.val t) := by omega
  have hbound : (d : ℤ)*(∑ v ∈ V, max (2*alpha v) (beta v+poleOrder v.val t)) ≤ C := by
    have hbud := hbudget V
    simp_rw [heq]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hbud ⊢
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hh
    nlinarith
  apply le_trans _ hbound
  apply mul_le_mul_of_nonneg_left _ (Int.natCast_nonneg d)
  apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
  intro v _ _
  exact (by have := ha v; omega : 0 ≤ 2*alpha v).trans (le_max_left _ _)

/-- A lower bound on the polynomial degree is enough to reserve a uniform
cofactor contribution in a family of component budgets. -/
theorem moving_height_bound_of_degree (P : Polynomial L) (hP : P ≠ 0)
    (t : L) (d n0 : ℕ) (hn : n0 ≤ P.natDegree)
    (hd : (Polynomial.X-Polynomial.C t)^d ∣ P)
    (B alpha beta : Place K L → ℤ) (C : ℤ)
    (ha : ∀ v, 0 ≤ alpha v) (hba : ∀ v, beta v ≤ alpha v)
    (hcoeff : ∀ v (i : ℕ), v.val (P.coeff i) ≤
      WithZero.exp (B v-(i : ℤ)*(2*alpha v-beta v)))
    (hbudget : ∀ V : Finset (Place K L),
      (∑ v ∈ V, (B v+(d : ℤ)*beta v-
        ((n0-d : ℕ) : ℤ)*(2*alpha v-beta v))) ≤ C)
    (W : Finset (Place K L)) :
    (d : ℤ)*(∑ v ∈ W, max (2*alpha v) (beta v+poleOrder v.val t)) ≤ C := by
  apply moving_height_bound K P hP t d hd B alpha beta C ha hba hcoeff _ W
  intro V
  apply le_trans _ (hbudget V)
  apply Finset.sum_le_sum
  intro v _
  have hl : 0 ≤ 2*alpha v-beta v := by have := ha v; have := hba v; omega
  have hsub : ((n0-d : ℕ) : ℤ) ≤ ((P.natDegree-d : ℕ) : ℤ) := by
    exact_mod_cast Nat.sub_le_sub_right hn d
  exact sub_le_sub_left (mul_le_mul_of_nonneg_right hsub hl) _

end FunctionField
end
end ProximityPrize.SubmissionLower.RootMultiplicityWeightedHeight

end Compact_RootMultiplicityWeightedHeight

section Compact_SecondJetRelaxedFlag
/-! The weighted R+2S source gives affine coefficient pole budgets. The final
height application still requires a nonzero component polynomial, its root
multiplicity, and a geometric budget for the resulting flag. -/
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedFlag
open scoped BigOperators WithZero
open ProximityPrize.SubmissionLower.RootMultiplicityValuation
open MvPolynomial RCN095 RCN026 RCN187 RCN204
open SecondJetCoefficients SecondJetSupport SecondJetFlagCoefficients
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K L : Type*} [Field K] [Field L]

def coefficientFlag (B U T j : ℕ) : FlagDegree := ⟨T-U,U-B+j,B-2*j⟩

def budgetFlag (B U T d n0 : ℕ) : FlagDegree := ⟨T-U,U-B+n0,B-2*(n0-d)⟩

theorem coefficient_bounds (P : Poly (K := K)) (B U T : ℕ)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T)
    (j : ℕ) (e : Fin 4 →₀ ℕ) (he : e ∈ ((asS (K := K) P).coeff j).support) :
    2*j+e 2 ≤ B ∧ j+e 1+e 2 ≤ U ∧ j+e 1+e 2+e 3 ≤ T := by
  have hh := hP _ (coefficient_support P j e he)
  obtain ⟨h0,h1,h2,h3,h4⟩ := lift_coordinates j e
  rwa [h1,h2,h3,h4] at hh

theorem frozen_coefficient_flag (P : Poly (K := K)) (x : K) (B U T : ℕ)
    (hBU : B ≤ U) (hUT : U ≤ T)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T) (j : ℕ) :
    PolynomialInFlag (coefficientFlag B U T j) (freeze x ((asS (K := K) P).coeff j)) := by
  apply freeze_inFlag
  intro e he
  have hb := coefficient_bounds P B U T hP j e he
  change e 2 ≤ B-2*j ∧ e 1+e 2 ≤ U-B+j+(B-2*j) ∧
    e 1+e 2+e 3 ≤ T-U+(U-B+j)+(B-2*j)
  omega

theorem coefficient_flag_pole (v : Valuation L Value) (x : Fin 3 → L)
    (B U T j : ℕ) (hj : 2*j ≤ B) :
    flagPole v x (coefficientFlag B U T j) =
      flagPole v x (coefficientFlag B U T 0) -
        (j : ℤ)*(2*flagPole v x unitAllFlag-flagPole v x unitYZFlag) := by
  simp only [flagPole, coefficientFlag, unitAllFlag, unitYZFlag, Nat.mul_zero, Nat.sub_zero, Nat.add_zero]
  rw [Nat.cast_sub hj]
  push_cast
  ring

theorem budget_flag_pole (v : Valuation L Value) (x : Fin 3 → L)
    (B U T d n0 : ℕ) (hd : d ≤ n0) (hB : 2*(n0-d) ≤ B) :
    flagPole v x (budgetFlag B U T d n0) =
      flagPole v x (coefficientFlag B U T 0) + (d : ℤ)*flagPole v x unitYZFlag -
        ((n0-d : ℕ) : ℤ)*(2*flagPole v x unitAllFlag-flagPole v x unitYZFlag) := by
  simp only [flagPole, budgetFlag, coefficientFlag, unitAllFlag, unitYZFlag, Nat.mul_zero, Nat.sub_zero, Nat.add_zero]
  simp only [Nat.cast_sub hB, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hd, Nat.cast_add]
  ring

theorem frozen_coefficient_valuation (P : Poly (K := K)) (freezeX : K)
    (B U T : ℕ) (hBU : B ≤ U) (hUT : U ≤ T)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T)
    (v : Valuation L Value) (coeff : K →+* L) (hc : ∀ c, v (coeff c) ≤ 1)
    (x : Fin 3 → L) (j : ℕ) :
    v (MvPolynomial.eval₂Hom coeff x (freeze freezeX ((asS (K := K) P).coeff j))) ≤
      WithZero.exp (flagPole v x (coefficientFlag B U T 0) -
        (j : ℤ)*(2*flagPole v x unitAllFlag-flagPole v x unitYZFlag)) := by
  by_cases hz : (asS (K := K) P).coeff j = 0
  · simp only [hz, map_zero]
    exact zero_le
  have hs : ((asS (K := K) P).coeff j).support.Nonempty :=
    MvPolynomial.support_nonempty.mpr hz
  obtain ⟨e,he⟩ := hs
  have hj : 2*j ≤ B := by have := coefficient_bounds P B U T hP j e he; omega
  rw [← coefficient_flag_pole v x B U T j hj]
  exact valuation_eval_le_flag v coeff hc x (coefficientFlag B U T j) _
    (frozen_coefficient_flag P freezeX B U T hBU hUT hP j)

section FunctionField
variable [Algebra K L] [IsAlgClosed K]
  [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

/-- The numerical weighted flag used by the scout is sufficient for the generic
moving-height theorem. Nonvanishing and multiplicity are explicit premises. -/
theorem moving_bound (P : Poly (K := K)) (freezeX : K) (B U T d n0 : ℕ)
    (hBU : B ≤ U) (hUT : U ≤ T) (hdn : d ≤ n0) (hB : 2*(n0-d) ≤ B)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T)
    (x : Fin 3 → L) (Q : Polynomial L)
    (hQcoeff : ∀ j, Q.coeff j = MvPolynomial.eval₂Hom (algebraMap K L) x
      (freeze freezeX ((asS (K := K) P).coeff j)))
    (hQ : Q ≠ 0) (hn : n0 ≤ Q.natDegree) (t : L)
    (hd : (Polynomial.X-Polynomial.C t)^d ∣ Q) (C : ℤ)
    (hbudget : ∀ V : Finset (Place K L),
      (∑ v ∈ V, flagPole v.val x (budgetFlag B U T d n0)) ≤ C)
    (V : Finset (Place K L)) :
    (d : ℤ)*(∑ v ∈ V, max (2*flagPole v.val x unitAllFlag)
      (flagPole v.val x unitYZFlag+poleOrder v.val t)) ≤ C := by
  apply RootMultiplicityWeightedHeight.moving_height_bound_of_degree K Q hQ t d n0 hn hd
    (fun v => flagPole v.val x (coefficientFlag B U T 0))
    (fun v => flagPole v.val x unitAllFlag) (fun v => flagPole v.val x unitYZFlag) C
    (fun v => flagPole_nonneg v.val x unitAllFlag) ?_ ?_ ?_ V
  · intro v
    rw [flagPole_unitYZ, flagPole_unitAll]
    exact le_max_right _ _
  · intro v j
    rw [hQcoeff j]
    exact frozen_coefficient_valuation P freezeX B U T hBU hUT hP v.val
      (algebraMap K L) (RCN344.constant_value_le_one K L v) x j
  · intro W
    convert hbudget W using 1
    apply Finset.sum_congr rfl
    intro v _
    exact (budget_flag_pole v.val x B U T d n0 hdn hB).symm

end FunctionField

end
end ProximityPrize.SubmissionLower.SecondJetRelaxedFlag

end Compact_SecondJetRelaxedFlag

section Compact_SecondJetSurfaceMap
/-! Transporting coefficient flags to the generic carrier surface. -/
namespace ProximityPrize.SubmissionLower.SecondJetSurfaceMap
open MvPolynomial SecondJetSupport SecondJetCoefficients SecondJetFlagCoefficients
open RCN136
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K E : Type*} [Field K] [Field E]

theorem coefficient_map (f : K →+* E) (P : Poly (K := K)) (j : ℕ) :
    (asS (MvPolynomial.map f P)).coeff j = MvPolynomial.map f ((asS P).coeff j) := by
  ext e
  rw [asS_coeff,MvPolynomial.coeff_map,MvPolynomial.coeff_map,asS_coeff]

theorem freeze_map_eq_surface (φ : Polynomial K →+* E) (P : MvPolynomial (Fin 4) K) :
    freeze (φ Polynomial.X) (MvPolynomial.map (φ.comp Polynomial.C) P) = surfaceMap φ P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [freeze]
  | add P Q hp hq => simp only [map_add,hp,hq]
  | mul_X P i hp =>
    simp only [map_mul,hp,MvPolynomial.map_X]
    congr 1
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [freeze]
    · rw [surfaceMap_X_succ]
      fin_cases j <;> simp [freeze]

theorem frozen_mapped_coefficient (φ : Polynomial K →+* E) (P : Poly (K := K)) (j : ℕ) :
    freeze (φ Polynomial.X) ((asS (MvPolynomial.map (φ.comp Polynomial.C) P)).coeff j) =
      surfaceMap φ ((asS P).coeff j) := by
  rw [coefficient_map,freeze_map_eq_surface]

theorem mapped_support_bounds (f : K →+* E) (P : Poly (K := K)) (B U T : ℕ)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T) :
    ∀ e ∈ (MvPolynomial.map f P).support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T := by
  intro e he
  exact hP e (MvPolynomial.support_map_subset f P he)

end
end ProximityPrize.SubmissionLower.SecondJetSurfaceMap

end Compact_SecondJetSurfaceMap

section Compact_SecondJetCoefficientSpecialization
/-! Coefficient and evaluation identities for the second-derivative variable. -/
namespace ProximityPrize.SubmissionLower.SecondJetCoefficientSpecialization
open MvPolynomial SecondJetSupport SecondJetCoefficients SecondJetSpecialize
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

theorem lift_succ (j : ℕ) (d : Fin 4 →₀ ℕ) :
    liftExponent (j+1) d = liftExponent j d+Finsupp.single 1 1 := by
  ext i
  obtain ⟨h0,h1,h2,h3,h4⟩ := lift_coordinates j d
  obtain ⟨g0,g1,g2,g3,g4⟩ := lift_coordinates (j+1) d
  fin_cases i <;> simp [Finsupp.add_apply,Finsupp.single_apply,h0,h1,h2,h3,h4,g0,g1,g2,g3,g4]

theorem asS_pderiv (P : Poly (K := K)) :
    asS (pderiv 1 P) = (asS P).derivative := by
  ext j d
  rw [asS_coeff, MvPolynomial.coeff_pderiv, Polynomial.coeff_derivative]
  rw [show ((j : MvPolynomial (Fin 4) K)+1) = MvPolynomial.C (j+1 : K) by simp,
    mul_comm ((asS P).coeff (j+1)) (MvPolynomial.C (j+1 : K)),
    MvPolynomial.coeff_C_mul, asS_coeff]
  rw [← lift_succ, (lift_coordinates j d).2.1]
  simp [mul_comm]

theorem asS_iterate (P : Poly (K := K)) (d : ℕ) :
    asS ((pderiv 1)^[d] P) = (Polynomial.derivative)^[d] (asS P) := by
  induction d with
  | zero => rfl
  | succ d ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', asS_pderiv, ih]

def coefficientSpecialize (f : Polynomial K) (z : K) :
    MvPolynomial (Fin 4) K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval ![Polynomial.X,f,f.derivative,Polynomial.C z]

def evaluateS (f : Polynomial K) (z : K) :
    Polynomial (MvPolynomial (Fin 4) K) →ₐ[K] Polynomial K :=
  { Polynomial.eval₂RingHom (coefficientSpecialize f z).toRingHom (Polynomial.hasseDeriv 2 f) with
    commutes' := by intro c; simp [coefficientSpecialize] }

theorem specialize_eq (P : Poly (K := K)) (f : Polynomial K) (z : K) :
    specialize f z P = (asS P).eval₂ (coefficientSpecialize f z).toRingHom
      (Polynomial.hasseDeriv 2 f) := by
  have heq : specialize f z = (evaluateS f z).comp (asS (K := K)).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    have h1 (A : Polynomial (MvPolynomial (Fin 4) K)) (g : Fin 4 → Polynomial (MvPolynomial (Fin 4) K)) :
        Fin.cases A g (1 : Fin 5) = g 0 := rfl
    have h2 (A : Polynomial (MvPolynomial (Fin 4) K)) (g : Fin 4 → Polynomial (MvPolynomial (Fin 4) K)) :
        Fin.cases A g (2 : Fin 5) = g 1 := rfl
    have h3 (A : Polynomial (MvPolynomial (Fin 4) K)) (g : Fin 4 → Polynomial (MvPolynomial (Fin 4) K)) :
        Fin.cases A g (3 : Fin 5) = g 2 := rfl
    have h4 (A : Polynomial (MvPolynomial (Fin 4) K)) (g : Fin 4 → Polynomial (MvPolynomial (Fin 4) K)) :
        Fin.cases A g (4 : Fin 5) = g 3 := rfl
    fin_cases i <;> simp [specialize, asS, coefficientSpecialize, evaluateS,
      Equiv.swap_apply_def, MvPolynomial.finSuccEquiv_apply, h1,h2,h3,h4]
  exact DFunLike.congr_fun heq P

end
end ProximityPrize.SubmissionLower.SecondJetCoefficientSpecialization

end Compact_SecondJetCoefficientSpecialization

section Compact_SecondJetClearedHelper
/-! Clearing the second-derivative denominator preserves the interpolant's
vanishing on every regular codeword carried by F. -/
namespace ProximityPrize.SubmissionLower.SecondJetClearedHelper
open scoped BigOperators
open MvPolynomial SecondJetSupport SecondJetCoefficients SecondJetSpecialize
open SecondJetCoefficientSpecialization
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K : Type*} [Field K]

def cleared {R : Type*} [CommRing R] (P : Polynomial R) (n : ℕ) (H G : R) : R :=
  ∑ j : Fin (n+1), P.coeff j.val*H^(n-j.val)*G^j.val

theorem map_cleared {R T : Type*} [CommRing R] [CommRing T] (φ : R →+* T)
    (P : Polynomial R) (n : ℕ) (H G : R) :
    φ (cleared P n H G) = cleared (P.map φ) n (φ H) (φ G) := by
  simp [cleared,Polynomial.coeff_map]

theorem cleared_eval {R : Type*} [CommRing R] (P : Polynomial R) (n : ℕ)
    (hn : P.natDegree ≤ n) (H G t : R) (hrel : H*t = G) :
    cleared P n H G = H^n*P.eval t := by
  rw [Polynomial.eval_eq_sum_range' (by omega : P.natDegree < n+1)]
  rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ => P.coeff j*t^j)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← hrel,mul_pow]
  have hh : H^(n-j.val)*H^j.val = H^n := by rw [← pow_add,Nat.sub_add_cancel (Nat.le_of_lt_succ j.isLt)]
  calc
    _ = P.coeff j.val*(H^(n-j.val)*H^j.val)*t^j.val := by ring
    _ = _ := by rw [hh]; ring

theorem coefficientSpecialize_eq (f : Polynomial K) (z : K) :
    (coefficientSpecialize f z).toRingHom = RCN319.specialization K f z := by
  rfl

theorem hasse_two (f : Polynomial K) :
    (2 : Polynomial K)*Polynomial.hasseDeriv 2 f = f.derivative.derivative := by
  have hh := congrFun (Polynomial.factorial_smul_hasseDeriv (R := K) (k := 2)) f
  simpa [Function.iterate_succ_apply',nsmul_eq_mul] using hh

def helper (P : Poly (K := K)) (F : MvPolynomial (Fin 4) K) (n d : ℕ) :
    MvPolynomial (Fin 4) K :=
  cleared (asS ((pderiv 1)^[d] P)) n (2*RCN313.polyH K F) (RCN313.polyG K F)

theorem helper_vanish (P : Poly (K := K)) (F : MvPolynomial (Fin 4) K)
    (n d : ℕ) (hn : (asS ((pderiv 1)^[d] P)).natDegree ≤ n)
    (f : Polynomial K) (z : K)
    (hF : RCN319.specialization K f z F = 0)
    (hP : specialize f z ((pderiv 1)^[d] P) = 0) :
    RCN319.specialization K f z (helper P F n d) = 0 := by
  have hrel : RCN319.specialization K f z (2*RCN313.polyH K F)*Polynomial.hasseDeriv 2 f =
      RCN319.specialization K f z (RCN313.polyG K F) := by
    rw [map_mul,map_ofNat]
    calc
      _ = RCN319.specialization K f z (RCN313.polyH K F)*
          ((2 : Polynomial K)*Polynomial.hasseDeriv 2 f) := by ring
      _ = _ := by rw [hasse_two]; exact RCN231.solution_slope_identity K F f z hF
  change (RCN319.specialization K f z).toRingHom
    (cleared (asS ((pderiv 1)^[d] P)) n (2*RCN313.polyH K F) (RCN313.polyG K F)) = 0
  rw [map_cleared]
  simp only [AlgHom.toRingHom_eq_coe,RingHom.coe_coe]
  rw [cleared_eval _ n (Polynomial.natDegree_map_le.trans hn) _ _ _ hrel]
  have hv : ((asS ((pderiv 1)^[d] P)).map (RCN319.specialization K f z)).eval
      (Polynomial.hasseDeriv 2 f) = 0 := by
    rw [Polynomial.eval_map,← coefficientSpecialize_eq,← specialize_eq]
    exact hP
  rw [hv,mul_zero]

end
end ProximityPrize.SubmissionLower.SecondJetClearedHelper

end Compact_SecondJetClearedHelper

section Compact_SecondJetHelperWeights
/-! Exact cumulative degree bounds for the cleared helper. The S-coefficient
slope cancels the numerator's excess weight over the denominator. -/
namespace ProximityPrize.SubmissionLower.SecondJetHelperWeights
open scoped BigOperators
open MvPolynomial SecondJetSupport SecondJetCoefficients SecondJetCoefficientSpecialization
open SecondJetClearedHelper RCN234 RCN156
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K : Type*} [Field K]

theorem derivative_coefficient_bounds (P : Poly (K := K)) (B U L d j : ℕ)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ L)
    (e : Fin 4 →₀ ℕ) (he : e ∈ ((asS ((pderiv 1)^[d] P)).coeff j).support) :
    2*(j+d)+e 2 ≤ B ∧ j+d+e 1+e 2 ≤ U ∧ j+d+e 1+e 2+e 3 ≤ L := by
  have hb := hP _ (SecondJetGlobalDifferentiation.support_iterate P d _
    (coefficient_support ((pderiv 1)^[d] P) j e he))
  obtain ⟨h0,h1,h2,h3,h4⟩ := lift_coordinates j e
  simpa [Finsupp.add_apply,Finsupp.single_apply,h0,h1,h2,h3,h4] using hb

theorem derivative_coefficient_weights (P : Poly (K := K)) (B U L d j : ℕ)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ L) :
    wt residualSWeights ((asS ((pderiv 1)^[d] P)).coeff j) ≤ B-2*d-2*j ∧
    wt residualYSWeights ((asS ((pderiv 1)^[d] P)).coeff j) ≤ U-d-j ∧
    wt residualTotalWeights ((asS ((pderiv 1)^[d] P)).coeff j) ≤ L-d-j := by
  refine ⟨?_,?_,?_⟩
  all_goals
    apply (RCN081.weightedTotalDegree_le_iff _ _ _).mpr
    intro e he
    have hb := derivative_coefficient_bounds P B U L d j hP e he
  · simp [residualSWeights,RCN081.weight_fin4]
    omega
  · simp [residualYSWeights,RCN081.weight_fin4]
    omega
  · simp [residualTotalWeights,RCN081.weight_fin4]
    omega

theorem asS_derivative_degree (P : Poly (K := K)) (s d : ℕ)
    (hP : ∀ e ∈ P.support, e 1 ≤ s) :
    (asS ((pderiv 1)^[d] P)).natDegree ≤ s-d := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  by_contra hn
  obtain ⟨e,he⟩ := MvPolynomial.support_nonempty.mpr hn
  have hb := hP _ (SecondJetGlobalDifferentiation.support_iterate P d _
    (coefficient_support ((pderiv 1)^[d] P) j e he))
  have h1 := (lift_coordinates j e).2.1
  simp [Finsupp.add_apply,Finsupp.single_apply,h1] at hb
  omega

theorem cleared_weight (weights : Fin 4 → ℕ) (P : Polynomial (MvPolynomial (Fin 4) K))
    (n C slope Hcap : ℕ) (H G : MvPolynomial (Fin 4) K)
    (hC : slope*n ≤ C)
    (hP : ∀ j : Fin (n+1), wt weights (P.coeff j.val) ≤ C-slope*j.val)
    (hH : wt weights H ≤ Hcap) (hG : wt weights G ≤ Hcap+slope) :
    wt weights (cleared P n H G) ≤ C+n*Hcap := by
  unfold cleared
  apply RCN235.wt_finset_sum_le
  intro j _
  have hj := j.isLt
  have hp := hP j
  have hh := (wt_pow_le weights H (n-j.val)).trans (Nat.mul_le_mul_left _ hH)
  have hg := (wt_pow_le weights G j.val).trans (Nat.mul_le_mul_left _ hG)
  have ht := (wt_mul_le weights (P.coeff j.val*H^(n-j.val)) (G^j.val)).trans
    (Nat.add_le_add ((wt_mul_le weights (P.coeff j.val) (H^(n-j.val))).trans
      (Nat.add_le_add hp hh)) hg)
  have hjn : j.val ≤ n := by omega
  have hjC : slope*j.val ≤ C := (Nat.mul_le_mul_left slope hjn).trans hC
  have hc : C-slope*j.val+slope*j.val = C := Nat.sub_add_cancel hjC
  have hn : n-j.val+j.val = n := Nat.sub_add_cancel hjn
  nlinarith

theorem helper_weights (P : Poly (K := K)) (F : MvPolynomial (Fin 4) K)
    (B U L s d capT capY capR : ℕ) (hsB : 2*s ≤ B) (hsU : s ≤ U) (hsL : s ≤ L)
    (hd : d ≤ s) (hR : 1 ≤ capR) (hY : 1 ≤ capY) (hT : 1 ≤ capT)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ L)
    (hF : wt residualSWeights F ≤ capR ∧ wt residualYSWeights F ≤ capY ∧
      wt residualTotalWeights F ≤ capT) :
    wt residualSWeights (helper P F (s-d) d) ≤ B-2*d+(s-d)*(capR-1) ∧
    wt residualYSWeights (helper P F (s-d) d) ≤ U-d+(s-d)*(capY-1) ∧
    wt residualTotalWeights (helper P F (s-d) d) ≤ L-d+(s-d)*(capT-1) := by
  have hw (weights : Fin 4 → ℕ) (cap : ℕ) (hR1 : weights 2 = 1)
      (hFcap : wt weights F ≤ cap) : wt weights (2*RCN313.polyH K F) ≤ cap-1 := by
    have hh := wt_polyH_le weights F cap hFcap
    have hm := wt_mul_le weights (2 : MvPolynomial (Fin 4) K) (RCN313.polyH K F)
    have hc : wt weights (2 : MvPolynomial (Fin 4) K) = 0 := wt_natCast weights 2
    rw [hR1] at hh
    omega
  refine ⟨?_,?_,?_⟩
  · apply cleared_weight residualSWeights _ (s-d) (B-2*d) 2 (capR-1) _ _ (by omega)
      (fun j => (derivative_coefficient_weights P B U L d j.val hP).1)
      (hw _ capR rfl hF.1)
    have hg := wt_polyG_le residualSWeights rfl F capR hF.1
    change wt residualSWeights (RCN313.polyG K F) ≤ capR-1+2
    change wt residualSWeights (RCN313.polyG K F) ≤ capR+1 at hg
    omega
  · apply cleared_weight residualYSWeights _ (s-d) (U-d) 1 (capY-1) _ _ (by omega)
      (fun j => by simpa using (derivative_coefficient_weights P B U L d j.val hP).2.1)
      (hw _ capY rfl hF.2.1)
    have hg := RCN179.wt_polyG_le_of_R_le_Y residualYSWeights rfl F capY (by decide) hY hF.2.1
    omega
  · apply cleared_weight residualTotalWeights _ (s-d) (L-d) 1 (capT-1) _ _ (by omega)
      (fun j => by simpa using (derivative_coefficient_weights P B U L d j.val hP).2.2)
      (hw _ capT rfl hF.2.2)
    have hg := RCN179.wt_polyG_le_of_R_le_Y residualTotalWeights rfl F capT (by decide) hT hF.2.2
    omega

end
end ProximityPrize.SubmissionLower.SecondJetHelperWeights

end Compact_SecondJetHelperWeights

section Compact_RootMultiplicityDichotomy
/-! The algebraic split behind the second-jet helper/height argument. -/
namespace ProximityPrize.SubmissionLower.RootMultiplicityDichotomy
noncomputable section
set_option autoImplicit false
variable {L : Type*} [Field L]

theorem derivative_or_high_multiplicity (P : Polynomial L) (hP : P ≠ 0)
    (t : L) (k : ℕ) (hk : (k.factorial : L) ≠ 0) :
    (∃ d ≤ k, ((Polynomial.derivative)^[d] P).eval t ≠ 0) ∨
      (Polynomial.X-Polynomial.C t)^(k+1) ∣ P := by
  classical
  rcases Classical.em (∀ d ≤ k, ((Polynomial.derivative)^[d] P).eval t = 0) with hroot | hroot
  · right
    have hm := Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors
      hP hroot (mem_nonZeroDivisors_iff_ne_zero.mpr hk)
    exact (pow_dvd_pow (Polynomial.X-Polynomial.C t) hm).trans (P.pow_rootMultiplicity_dvd t)
  · left
    push_neg at hroot
    exact hroot

end
end ProximityPrize.SubmissionLower.RootMultiplicityDichotomy

end Compact_RootMultiplicityDichotomy

section Compact_SecondJetCarrierDichotomy
/-! Over a carrier field, either a cleared derivative is proper or the
interpolant has the required high-multiplicity root. -/
namespace ProximityPrize.SubmissionLower.SecondJetCarrierDichotomy
open MvPolynomial SecondJetSupport SecondJetCoefficients
open SecondJetCoefficientSpecialization SecondJetClearedHelper SecondJetHelperWeights
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K E : Type*} [Field K] [Field E]

def ratio (φ : MvPolynomial (Fin 4) K →+* E) (F : MvPolynomial (Fin 4) K) : E :=
  φ (RCN313.polyG K F)/φ (2*RCN313.polyH K F)

theorem mapped_helper (P : Poly (K := K)) (F : MvPolynomial (Fin 4) K)
    (φ : MvPolynomial (Fin 4) K →+* E) (s d : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s) (hH : φ (2*RCN313.polyH K F) ≠ 0) :
    φ (helper P F (s-d) d) = φ (2*RCN313.polyH K F)^(s-d)*
      ((Polynomial.derivative)^[d] ((asS P).map φ)).eval (ratio φ F) := by
  rw [helper,map_cleared]
  have hdegree : ((asS ((pderiv 1)^[d] P)).map φ).natDegree ≤ s-d :=
    Polynomial.natDegree_map_le.trans (asS_derivative_degree P s d hS)
  have hrel : φ (2*RCN313.polyH K F)*ratio φ F = φ (RCN313.polyG K F) := by
    unfold ratio
    field_simp
  rw [cleared_eval _ (s-d) hdegree _ _ _ hrel,asS_iterate,← Polynomial.iterate_derivative_map]

theorem helper_or_multiplicity (P : Poly (K := K)) (F : MvPolynomial (Fin 4) K)
    (φ : MvPolynomial (Fin 4) K →+* E) (s k : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s) (hF : φ F = 0)
    (hH : φ (2*RCN313.polyH K F) ≠ 0)
    (hP : (asS P).map φ ≠ 0) (hk : (k.factorial : E) ≠ 0) :
    (∃ d ≤ k, ¬ F ∣ helper P F (s-d) d) ∨
      (Polynomial.X-Polynomial.C (ratio φ F))^(k+1) ∣ (asS P).map φ := by
  rcases RootMultiplicityDichotomy.derivative_or_high_multiplicity
    ((asS P).map φ) hP (ratio φ F) k hk with hder | hroot
  · left
    obtain ⟨d,hd,hne⟩ := hder
    refine ⟨d,hd,?_⟩
    intro hdiv
    have hh := map_dvd φ hdiv
    rw [hF,zero_dvd_iff,mapped_helper P F φ s d hS hH] at hh
    exact (mul_ne_zero (pow_ne_zero _ hH) hne) hh
  · exact Or.inr hroot

theorem multiplicity_of_helpers_dvd (P : Poly (K := K)) (F : MvPolynomial (Fin 4) K)
    (φ : MvPolynomial (Fin 4) K →+* E) (s k : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s) (hF : φ F = 0)
    (hH : φ (2*RCN313.polyH K F) ≠ 0)
    (hP : (asS P).map φ ≠ 0) (hk : (k.factorial : E) ≠ 0)
    (hdiv : ∀ d ≤ k, F ∣ helper P F (s-d) d) :
    (Polynomial.X-Polynomial.C (ratio φ F))^(k+1) ∣ (asS P).map φ := by
  rcases helper_or_multiplicity P F φ s k hS hF hH hP hk with h | h
  · obtain ⟨d,hd,hn⟩ := h
    exact False.elim (hn (hdiv d hd))
  · exact h

end
end ProximityPrize.SubmissionLower.SecondJetCarrierDichotomy

end Compact_SecondJetCarrierDichotomy

section Compact_SecondJetCoefficientAvoidance
/-! The conservative coefficient avoidance gate makes every nonzero S
coefficient proper with respect to a carrier of larger Z degree. -/
namespace ProximityPrize.SubmissionLower.SecondJetCoefficientAvoidance
open MvPolynomial SecondJetSupport SecondJetCoefficients
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {K : Type*} [Field K]

theorem map_degree_preserved {R T : Type*} [CommRing R] [CommRing T]
    (P : Polynomial R) (φ : R →+* T) (hC : φ P.leadingCoeff ≠ 0) :
    P.map φ ≠ 0 ∧ (P.map φ).natDegree = P.natDegree := by
  constructor
  · intro hz
    have hh := congrArg (fun Q : Polynomial T => Q.coeff P.natDegree) hz
    simp only [Polynomial.coeff_map,Polynomial.coeff_zero,Polynomial.coeff_natDegree] at hh
    exact hC hh
  · exact Polynomial.natDegree_map_eq_iff.mpr (Or.inl hC)

end
end ProximityPrize.SubmissionLower.SecondJetCoefficientAvoidance

end Compact_SecondJetCoefficientAvoidance

section Compact_SecondJetComponentRoots
/-! The fixed leading coefficient isolates exactly the components on which
mapped degree and high root multiplicity are retained. -/
namespace ProximityPrize.SubmissionLower.SecondJetComponentRoots
open MvPolynomial SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open RCN002 RCN136
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K E : Type} [Field K] [Field E]

def coefficientMap (φ : Polynomial K →+* E) (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime] :
    MvPolynomial (Fin 4) K →+* CoordinateField E C :=
  (coordinateEvaluation E C).toRingHom.comp (surfaceMap φ)

def componentPolynomial (φ : Polynomial K →+* E) (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (P : Poly (K := K)) : Polynomial (CoordinateField E C) :=
  (asS P).map (coefficientMap φ C)

theorem evaluation_zero_iff (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (Q : MvPolynomial (Fin 3) E) : coordinateEvaluation E C Q = 0 ↔ Q ∈ C := by
  change Q ∈ RingHom.ker (coordinateEvaluation E C).toRingHom ↔ Q ∈ C
  rw [coordinateEvaluation_ker]

theorem degree_retained (φ : Polynomial K →+* E) (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (P : Poly (K := K)) (hlead : surfaceMap φ (asS P).leadingCoeff ∉ C) :
    componentPolynomial φ C P ≠ 0 ∧ (componentPolynomial φ C P).natDegree = (asS P).natDegree := by
  apply SecondJetCoefficientAvoidance.map_degree_preserved
  change coordinateEvaluation E C (surfaceMap φ (asS P).leadingCoeff) ≠ 0
  exact fun hz => hlead ((evaluation_zero_iff C _).mp hz)

theorem coefficients (φ : Polynomial K →+* E) (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (P : Poly (K := K)) (j : ℕ) :
    (componentPolynomial φ C P).coeff j =
      MvPolynomial.eval₂Hom (algebraMap E (CoordinateField E C)) (coordinate E C)
        (SecondJetFlagCoefficients.freeze (φ Polynomial.X)
          ((asS (MvPolynomial.map (φ.comp Polynomial.C) P)).coeff j)) := by
  rw [SecondJetSurfaceMap.frozen_mapped_coefficient]
  rw [componentPolynomial,Polynomial.coeff_map]
  change coordinateEvaluation E C _ = _
  rw [coordinateEvaluation_eq_aeval]
  exact (MvPolynomial.aeval_eq_eval₂Hom _ _)

theorem roots_retained (φ : Polynomial K →+* E) (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (P : Poly (K := K)) (F : MvPolynomial (Fin 4) K) (s k : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hF : surfaceMap φ F ∈ C) (hH : surfaceMap φ (RCN313.polyH K F) ∉ C)
    (hlead : surfaceMap φ (asS P).leadingCoeff ∉ C)
    (hdiv : ∀ d ≤ k, F ∣ helper P F (s-d) d)
    (h2 : (2 : E) ≠ 0) (hfact : (k.factorial : E) ≠ 0) :
    (Polynomial.X-Polynomial.C (RCN064.movingRatio C
      (surfaceMap φ (RCN313.polyH K F)) (surfaceMap φ (RCN313.polyG K F))/2))^(k+1) ∣
      componentPolynomial φ C P := by
  have hf : coefficientMap φ C F = 0 := (evaluation_zero_iff C _).mpr hF
  have hh : coordinateEvaluation E C (surfaceMap φ (RCN313.polyH K F)) ≠ 0 :=
    fun hz => hH ((evaluation_zero_iff C _).mp hz)
  have h2e : (2 : CoordinateField E C) ≠ 0 := by
    simpa only [map_ofNat,map_zero] using (algebraMap E (CoordinateField E C)).injective.ne h2
  have hfe : (k.factorial : CoordinateField E C) ≠ 0 := by
    simpa only [map_natCast,map_zero] using (algebraMap E (CoordinateField E C)).injective.ne hfact
  have hden : coefficientMap φ C (2*RCN313.polyH K F) ≠ 0 := by
    rw [map_mul,map_ofNat]
    exact mul_ne_zero h2e hh
  have hr := SecondJetCarrierDichotomy.multiplicity_of_helpers_dvd P F (coefficientMap φ C)
    s k hS hf hden (degree_retained φ C P hlead).1 hfe hdiv
  have heq : SecondJetCarrierDichotomy.ratio (coefficientMap φ C) F =
      RCN064.movingRatio C (surfaceMap φ (RCN313.polyH K F))
        (surfaceMap φ (RCN313.polyG K F))/2 := by
    simp only [SecondJetCarrierDichotomy.ratio,coefficientMap,RingHom.comp_apply,
      RCN064.movingRatio,map_mul,map_ofNat,AlgHom.toRingHom_eq_coe,RingHom.coe_coe]
    field_simp
    <;> ring
  rwa [heq] at hr

end
end ProximityPrize.SubmissionLower.SecondJetComponentRoots

end Compact_SecondJetComponentRoots

section Compact_SecondJetMovingDegree
/-! Turning the weighted root-height estimate into the integer degree of a
separable moving coordinate; no rounding is charged per component. -/
namespace ProximityPrize.SubmissionLower.SecondJetMovingDegree
open scoped BigOperators
open RCN026 RCN095 RCN187 RCN204 RCN344
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosed K]

variable [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

end
end ProximityPrize.SubmissionLower.SecondJetMovingDegree

end Compact_SecondJetMovingDegree

section Compact_SecondJetPoleScaling
/-! A nonzero constant factor in the second derivative does not change poles. -/
namespace ProximityPrize.SubmissionLower.SecondJetPoleScaling
open RCN026 RCN187
noncomputable section
set_option autoImplicit false
variable {K E : Type*} [Field K] [Field E] [Algebra K E]

theorem pole_div_constant (v : Place K E) (a : K) (ha : a ≠ 0) (x : E) :
    poleOrder v.val (x/algebraMap K E a) = poleOrder v.val x := by
  letI : v.val.IsTrivialOn K := v.property.2
  have hc : v.val (algebraMap K E a) = 1 := Valuation.IsTrivialOn.eq_one a ha
  simp only [poleOrder,Valuation.map_div,hc,div_one]

theorem pole_half (v : Place K E) (h2 : (2 : K) ≠ 0) (x : E) :
    poleOrder v.val (x/2) = poleOrder v.val x := by
  simpa only [map_ofNat] using pole_div_constant v 2 h2 x

end
end ProximityPrize.SubmissionLower.SecondJetPoleScaling

end Compact_SecondJetPoleScaling

section Compact_SecondJetActiveMovingBudget
/-! Moving budgets for the retained components, using their actual integer
projection degrees and the second-jet weighted root bound. -/
namespace ProximityPrize.SubmissionLower.SecondJetActiveMovingBudget
open scoped BigOperators
open RCN005 RCN006 RCN064 RCN002 RCN095 RCN187 RCN204 RCN207 RCN264 RCN341 RCN046 RCN199
open RCN344 (SeparableCoordinate coordinateDegree)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
variable {K : Type} [Field K] [IsAlgClosed K]

end
end ProximityPrize.SubmissionLower.SecondJetActiveMovingBudget

end Compact_SecondJetActiveMovingBudget

section Compact_SecondJetRetainedBudgets
/-! The weighted moving-degree estimate on the actual first-tail components,
assuming the proper derivative-helper alternatives have been excluded. -/
namespace ProximityPrize.SubmissionLower.SecondJetRetainedBudgets
open scoped Classical BigOperators
open MvPolynomial SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open RCN002 RCN136 RCN264 RCN341 RCN046 RCN095 RCN199
open RCN344 (coordinateDegree)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
variable {K E : Type} [Field K] [Field E] [IsAlgClosed E]

end
end ProximityPrize.SubmissionLower.SecondJetRetainedBudgets

end Compact_SecondJetRetainedBudgets

section Compact_SecondJetExceptionalComponents
/-! Components containing a fixed coefficient have no seeds after excluding
that coefficient's vanishing codewords. -/
namespace ProximityPrize.SubmissionLower.SecondJetExceptionalComponents
open MvPolynomial RCN264
open scoped Classical
noncomputable section
set_option autoImplicit false
variable {K : Type} [Field K] {Seed : Type*}
local instance  _root_.ProximityPrize.SubmissionLower.SecondJetExceptionalComponents.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.SecondJetExceptionalComponents.instDecidableEq_proximityPrize_1 : DecidableEq Seed := Classical.decEq Seed

theorem component_empty_of_nonvanishing (F A H T : MvPolynomial (Fin 3) K)
    (Gamma : Finset Seed) (point : Seed → Fin 3 → K)
    (C : RegularComponent K F A H) (hT : T ∈ C.1)
    (hne : ∀ x ∈ Gamma, MvPolynomial.eval (point x) T ≠ 0) :
    (componentSeeds K F A H Gamma point C).card = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxG := componentSeeds_subset K F A H Gamma point C hx
  have hpoint := componentSeeds_on_prime K F A H Gamma point C x hx
  have hz := hpoint hT
  exact hne x hxG hz

end
end ProximityPrize.SubmissionLower.SecondJetExceptionalComponents

end Compact_SecondJetExceptionalComponents

section Compact_SecondJetRetainedStage
/-! A scaled C2 stage bound from the actual second-jet component budgets.
The selected seeds avoid the global leading coefficient. Keeping the scaling
through the estimate permits summing geometric factors before rounding. -/
namespace ProximityPrize.SubmissionLower.SecondJetRetainedStage
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorHybridTailProviderC1 LocatorHybridTransportC2
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

variable {K I : Type} [Field K]
local instance  _root_.ProximityPrize.SubmissionLower.SecondJetRetainedStage.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.SecondJetRetainedStage.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable {stageErrorCap : ℕ}

end
end ProximityPrize.SubmissionLower.SecondJetRetainedStage

end Compact_SecondJetRetainedStage

section Compact_C2Geometry80788
/-! C2 geometric ingredients retuned to error 80788.
Adapted from the promoted submission. These are not a protocol claim. -/
set_option Elab.async false

section Adapted_LocatorFixedStage
namespace ProximityPrize.SubmissionLower.Lower80788.FixedStage
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN135 RCN136 RCN174 RCN159 RCN086 RCN095 RCN275 RCN198 RCN263 RCN146 RCN087 RCN203 RCN084 RCN313 RCN074 RCN335
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
def w:ℕ:=131071
def prime:ℕ:=2130706433
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
local instance _root_.ProximityPrize.SubmissionLower.Lower80788.FixedStage.instDecidableEqK :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.Lower80788.FixedStage.instDecidableEqI :DecidableEq I:=Classical.decEq I
local instance _root_.ProximityPrize.SubmissionLower.Lower80788.FixedStage.instDecidableEqGenericFieldK :DecidableEq (GenericField K):=Classical.decEq _
local instance _root_.ProximityPrize.SubmissionLower.Lower80788.FixedStage.instCharPKPrime :CharP K prime:=by
  simpa [prime,RCN223.prime] using
    RCN128.challenge_field_characteristic6600
def firstTail (a b s:ℕ):FlagDegree:=
  reducedResidualAgreementFlag (RCN198.support a b s) (w + 1)
def secondTail (a b s:ℕ):FlagDegree:=
  reducedResidualAgreementFlag (RCN198.support a b s) (w + 2)
theorem tail_support_formula (a b s d:ℕ) :
    reducedResidualAgreementFlag (RCN198.support a b s) d=
      ⟨2 * a * d,1 + 2 * (b + 1) * d,2 * (s + 1) * d⟩:=by
  have ht:a + b + s + 3 - (b + s + 3) =a:=by omega
  have hy:b + s + 3 - (s + 2) =b + 1:=by omega
  have hs:2 * (s + 2) - 2=2 * (s + 1):=by omega
  simp only [reducedResidualAgreementFlag,reducedAgreementDirection,RCN198.support]
  rw [ht,hy,hs]
theorem identityDegree_linear (flag:FlagDegree) (a b s:ℕ) :
    identityCurveDegree flag a b s w=
      flag.zOnly * (393219 + 262146 * s) +
      flag.yz * (786438 + 524292 * s) +
      flag.all * (1048586 + 262146 * a + 524292 * b + 524292 * s):=by
  simp only [identityCurveDegree,paddedCut,
    RCN206.centreFlag,
    RCN206.directionFlag,
    flagMixed,unitZFlag,unitYZFlag,add_zOnly,add_yz,add_all,
    nsmul_zOnly,nsmul_yz,nsmul_all,w]
  ring
theorem identity_positive (flag:FlagDegree) (a b s:ℕ)
    (hpos:0 < flag.zOnly + flag.yz + flag.all) :
    1 ≤ identityCurveDegree flag a b s w:=by
  rw [identityDegree_linear]
  have hz:=Nat.mul_le_mul_left flag.zOnly
    (show 1 ≤ 393219 + 262146 * s by omega)
  have hy:=Nat.mul_le_mul_left flag.yz
    (show 1 ≤ 786438 + 524292 * s by omega)
  have ha:=Nat.mul_le_mul_left flag.all
    (show 1 ≤ 1048586 + 262146 * a + 524292 * b + 524292 * s by omega)
  simp only [Nat.mul_one] at hz hy ha
  omega
end
end ProximityPrize.SubmissionLower.Lower80788.FixedStage

end Adapted_LocatorFixedStage

section Adapted_LocatorFixed
namespace ProximityPrize.SubmissionLower.Lower80788.Fixed
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN174 RCN319 RCN286 RCN081 RCN135 RCN095 RCN238 RCN243 RCN222 RCN266 RCN221 RCN268 RCN140 RCN275 RCN130 RCN156 RCN159 RCN234 RCN137 RCN198 RCN263 LocatorFactorAggregate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
local instance _root_.ProximityPrize.SubmissionLower.Lower80788.Fixed.instDecidableEqK :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.Lower80788.Fixed.instDecidableEqI :DecidableEq I:=Classical.decEq I
local instance _root_.ProximityPrize.SubmissionLower.Lower80788.Fixed.instDecidableEqGenericFieldK :DecidableEq (GenericField K):=Classical.decEq _
local instance _root_.ProximityPrize.SubmissionLower.Lower80788.Fixed.instCharPKOfNatNat :CharP K 2130706433:=by
  simpa [RCN223.prime] using
    RCN128.challenge_field_characteristic6600
def padB (p:FlagDegree):ℕ:=padY p - padS p - 1
def padSlope (p:FlagDegree):ℕ:=padS p - 2

end
end ProximityPrize.SubmissionLower.Lower80788.Fixed

end Adapted_LocatorFixed

section Adapted_LocatorHybridIdentityC2
namespace ProximityPrize.SubmissionLower.Lower80788.HybridIdentityC2

open RCN095 RCN146 RCN203 RCN206 LocatorFactorAggregate LocatorHybridCost
open LocatorHybridCostC1 LocatorHybridCostC2 RCN198

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-! ### Row constants for 6800 -/

def w : ℕ := 131071

/-- Local restatement of `Lower80788.FixedStage.identityDegree_linear`. -/
theorem identityDegree_linear (flag : FlagDegree) (a b s : ℕ) :
    identityCurveDegree flag a b s w =
      flag.zOnly * (393219 + 262146 * s) +
      flag.yz * (786438 + 524292 * s) +
      flag.all * (1048586 + 262146 * a + 524292 * b + 524292 * s) := by
  simp only [identityCurveDegree, paddedCut,
    RCN206.centreFlag, RCN206.directionFlag,
    flagMixed, unitZFlag, unitYZFlag, add_zOnly, add_yz, add_all,
    nsmul_zOnly, nsmul_yz, nsmul_all, w]
  ring

/-! ### Subtraction-free C2 tails in the support coordinates `a, b, s` -/

/-- The reduced first tail at `w + 1 = 131072`. -/
def reducedABS (a b s : ℕ) : FlagDegree :=
  ⟨2 * a * 131072, 1 + (2 * b + 2) * 131072, (2 * s + 2) * 131072⟩
def rationalABS (a b s : ℕ) : FlagDegree :=
  ⟨131072 * a + 2 * a, 131072 * b + 2 * b + 2, 131072 * s + 2 * s + 3⟩
def mfibABS (a b s : ℕ) : FlagDegree := ⟨a, b + 1, s + 3⟩
def mcutABS (a b s : ℕ) : FlagDegree := rationalABS a b s + ⟨0, 131072, 262144⟩

/-! ### Slack polynomials for `errors = 80788` (regenerated for the C2 cost) -/

end ProximityPrize.SubmissionLower.Lower80788.HybridIdentityC2

end Adapted_LocatorHybridIdentityC2

section Adapted_LocatorHybridGatesC2
namespace ProximityPrize.SubmissionLower.Lower80788.HybridGatesC2
open RCN095 LocatorHybridCells LocatorHybridCellsC1

end ProximityPrize.SubmissionLower.Lower80788.HybridGatesC2

end Adapted_LocatorHybridGatesC2

section Adapted_LocatorFixedHybridC2
namespace ProximityPrize.SubmissionLower.Lower80788.FixedHybridC2
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN174 RCN319 RCN286 RCN081 RCN135 RCN095 RCN238 RCN243 RCN222 RCN266 RCN221 RCN268 RCN140 RCN275 RCN130 RCN156 RCN159 RCN234 RCN137 RCN198 RCN263 RCN146 RCN287 RCN136 RCN086 RCN087 RCN203 RCN084 RCN313 RCN074 RCN335
open LocatorFactorAggregate LocatorHybridCost LocatorHybridCostC1 LocatorHybridCostC2
open Lower80788.HybridIdentityC2 LocatorHybridCells LocatorHybridCellsC1
open LocatorHybridTailProvider LocatorHybridTailProviderC1 LocatorHybridTailProviderC2
open Lower80788.HybridGatesC2 Lower80788.Fixed
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
local instance  _root_.ProximityPrize.SubmissionLower.Lower80788.FixedHybridC2.instDecidableEqK : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.Lower80788.FixedHybridC2.instDecidableEqI : DecidableEq I := Classical.decEq I
local instance  _root_.ProximityPrize.SubmissionLower.Lower80788.FixedHybridC2.instDecidableEqGenericFieldK : DecidableEq (GenericField K) := Classical.decEq _
local instance  _root_.ProximityPrize.SubmissionLower.Lower80788.FixedHybridC2.instCharPKOfNatNat : CharP K 2130706433 := by
  simpa [RCN223.prime] using
    RCN128.challenge_field_characteristic6600

end
end ProximityPrize.SubmissionLower.Lower80788.FixedHybridC2

end Adapted_LocatorFixedHybridC2

section Adapted_LocatorHybridRealizeC2
namespace ProximityPrize.SubmissionLower.Lower80788.HybridRealizeC2
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open RCN331 RCN027 RCN030 RCN029 RCN037 RCN038 RCN042 RCN002 RCN344 RCN277 RCN003 RCN314 RCN315 RCN093 RCN046 RCN001
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorFactorAggregate LocatorHybridCost LocatorHybridCostC1 LocatorHybridCostC2
open LocatorHybridTailProviderC1 LocatorHybridTailProviderC2
open LocatorHybridTailRealizationC2 Lower80788.HybridGatesC2
open Lower80788.Fixed Lower80788.FixedHybridC2
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
local instance  _root_.ProximityPrize.SubmissionLower.Lower80788.HybridRealizeC2.instDecidableEqK : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.Lower80788.HybridRealizeC2.instDecidableEqI : DecidableEq I := Classical.decEq I
local instance  _root_.ProximityPrize.SubmissionLower.Lower80788.HybridRealizeC2.instDecidableEqGenericFieldK : DecidableEq (GenericField K) := Classical.decEq _
local instance  _root_.ProximityPrize.SubmissionLower.Lower80788.HybridRealizeC2.instCharPKOfNatNat : CharP K 2130706433 := by
  simpa [RCN223.prime] using
    RCN128.challenge_field_characteristic6600

end
end ProximityPrize.SubmissionLower.Lower80788.HybridRealizeC2

end Adapted_LocatorHybridRealizeC2

section Adapted_LocatorFixedOwnBoundC2
namespace ProximityPrize.SubmissionLower.Lower80788.FixedOwnBoundC2
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN174 RCN275 RCN238 RCN243 RCN266 RCN140 RCN130 RCN156 RCN234 RCN159 RCN137 RCN198 RCN095
open LocatorFactorAggregate LocatorHybridCostC2 Lower80788.Fixed Lower80788.FixedHybridC2
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
local instance _root_.ProximityPrize.SubmissionLower.Lower80788.FixedOwnBoundC2.instDecidableEqK :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.Lower80788.FixedOwnBoundC2.instDecidableEqI :DecidableEq I:=Classical.decEq I
local instance _root_.ProximityPrize.SubmissionLower.Lower80788.FixedOwnBoundC2.instCharPKOfNatNat :CharP K 2130706433:=by
  simpa [RCN223.prime] using
    RCN128.challenge_field_characteristic6600

end
end ProximityPrize.SubmissionLower.Lower80788.FixedOwnBoundC2

end Adapted_LocatorFixedOwnBoundC2

end Compact_C2Geometry80788

section Compact_SecondJetIdentity
/-! The identity-tail branch at 80791 errors is covered by the normal C2
cost alone. These are polynomial identities over naturals, with all slack
coefficients nonnegative. -/
namespace ProximityPrize.SubmissionLower.SecondJetIdentity
open RCN146 RCN086 RCN095 RCN198 RCN206 RCN263 RCN327 LocatorHybridCells LocatorHybridCellsC1
open Lower80788.HybridIdentityC2
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem cell_first_eq (t y r : ℕ) :
    cellFirstTail t y r = reducedABS (cellA t y) (cellB y r) (cellS r) := by
  unfold cellFirstTail cellSupport
  rw [Lower80788.FixedStage.tail_support_formula]
  simp only [RCN327.w,reducedABS]
  congr 1 <;> ring

theorem cell_normal_eq (t y r : ℕ) :
    cellHybridCoordinateC1 t y r = rationalABS (cellA t y) (cellB y r) (cellS r) := by
  simp only [cellHybridCoordinateC1,cellRational,cellDirection,directionFlag,rationalABS,RCN327.w]
  congr 1 <;> ring

end
end ProximityPrize.SubmissionLower.SecondJetIdentity

end Compact_SecondJetIdentity

section Compact_SecondJetFixedStage
/-! A scaled C2 stage bound from the actual second-jet component budgets.
The selected seeds avoid the global leading coefficient. Keeping the scaling
through the estimate permits summing geometric factors before rounding. -/
namespace ProximityPrize.SubmissionLower.SecondJetFixedStage
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorHybridTailProviderC1 LocatorHybridTransportC2
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open RCN084 RCN146 RCN087 RCN335 RCN174 RCN275 RCN234 RCN156
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance  _root_.ProximityPrize.SubmissionLower.SecondJetFixedStage.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.SecondJetFixedStage.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I
local instance  _root_.ProximityPrize.SubmissionLower.SecondJetFixedStage.instCharPGenericFieldOfNatNat : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree}

end
end ProximityPrize.SubmissionLower.SecondJetFixedStage

end Compact_SecondJetFixedStage

section Compact_SecondJetRegularGeometry
/-! A scaled C2 stage bound from the actual second-jet component budgets.
The selected seeds avoid the global leading coefficient. Keeping the scaling
through the estimate permits summing geometric factors before rounding. -/
namespace ProximityPrize.SubmissionLower.SecondJetRegularGeometry
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorHybridTailProviderC1 LocatorHybridTransportC2
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open RCN084 RCN146 RCN087 RCN335 RCN174 RCN275 RCN234 RCN156
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance  _root_.ProximityPrize.SubmissionLower.SecondJetRegularGeometry.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.SecondJetRegularGeometry.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I
local instance  _root_.ProximityPrize.SubmissionLower.SecondJetRegularGeometry.instCharPGenericFieldOfNatNat : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree}

open RCN081 RCN130 RCN221 RCN222 RCN137 RCN238 RCN275

end
end ProximityPrize.SubmissionLower.SecondJetRegularGeometry

end Compact_SecondJetRegularGeometry

section Compact_SecondJetProperCounting
/-! The proper intersection bound stated directly for a regular irreducible
carrier, so it can count one global exceptional set or a proper helper branch. -/

namespace ProximityPrize.SubmissionLower.SecondJetProperCounting
open scoped Classical BigOperators
open RCN260 RCN318 RCN294 RCN286 RCN169 RCN167 RCN290 RCN082 RCN081 RCN174
  RCN319 RCN136 RCN137 RCN138 RCN135 RCN222 RCN243 RCN068 RCN238 RCN001 RCN052
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K : Type} [Field K] {ι : Type*}
local instance  _root_.ProximityPrize.SubmissionLower.SecondJetProperCounting.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.SecondJetProperCounting.instDecidableEq_proximityPrize_1 : DecidableEq ι := Classical.decEq ι

theorem regular_seed_bound_left
   (P:UnequalParameters) (F T:MvPolynomial (Fin 4) K)
   (hFirr:Irreducible F) (hFRpos:0 < F.degreeOf 2) (hrel:IsRelPrime F T)
   (p:ℕ) [CharP K p]
   (hFY:F.degreeOf 1 ≤ P.leftY)
   (hFR:F.degreeOf 2 ≤ P.leftR)
   (hFZ:F.degreeOf 3 ≤ P.leftZ)
   (hTY:T.degreeOf 1 ≤ P.rightY)
   (hTR:T.degreeOf 2 ≤ P.rightR)
   (hTZ:T.degreeOf 3 ≤ P.rightZ)
   (hleftR:1 ≤ P.leftR)
   (hleftYSmall:P.leftY < p) (hleftRSmall:P.leftR < p)
   (hleftZSmall:P.leftZ < p)
   (hmixedYSmall:P.mixedCost.y < p)
   (hmixedRSmall:P.mixedCost.r < p)
   (hmixedZSmall:P.mixedCost.z < p)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (hnodes:nodes.card=P.n)
   (hw:1 ≤ P.w) (hchar:P.w < p) (hwa:P.w < P.a)
   (han:P.a ≤ P.n)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ P.w)
   (hagreement:∀ gamma∈Gamma,
     P.a ≤ (nodes.filter (fun i =>
       (selected gamma).eval (x i)=u₀ i+gamma*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma P.w P.errors)
   (hsolution:∀ gamma∈Gamma,specialization K (selected gamma) gamma F=0)
   (hregular:∀ gamma∈Gamma,specialization K (selected gamma) gamma (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hTsolution:∀ gamma∈Gamma,specialization K (selected gamma) gamma T=0):
   Gamma.card*P.gap ≤
     (P.n-P.w)*dot P.leftAgreement (regularVector P F)+
       (P.errors+1)*P.gap*(regularVector P F).z:=by
 classical
 let phi:=polynomialEmbedding K
 let Delta:=Gamma
 let carrierCap:RCN051.DegreeVector:=
   ⟨P.leftY,P.leftR,P.leftZ⟩
 let cutCap:RCN051.DegreeVector:=
   ⟨P.rightY,P.rightR,P.rightZ⟩
 have hFne:F≠0:=hFirr.ne_zero
 have hDeltaSub:Delta ⊆ Gamma:=Finset.Subset.refl _
 have hDeltaData (gamma:K) (hgamma:gamma∈Delta):
     RegularSolution F (selected gamma) gamma∧
       specialization K (selected gamma) gamma T=0:=
   ⟨⟨hsolution gamma hgamma,hregular gamma hgamma⟩,hTsolution gamma hgamma⟩
 have hproper (g:GeometricFactor K F):¬g.1∣surfaceMap phi T:=by
   have hg := surfaceFactors_spec phi F g.1 g.2
   have hpos:0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3:=by omega
   have hgeo:g.1∣geometricSurfaceMap K (GenericField K) F:=by
     simpa only [canonical_geometricSurfaceMap] using hg.2
   intro hgT
   apply hFirr.not_isUnit
   apply hrel (dvd_refl F)
   apply (geometric_factor_dvd_iff K (GenericField K) F T hFirr hpos g.1 hg.1 hgeo).mp
   simpa only [canonical_geometricSurfaceMap] using hgT
 have hcover:=card_le_sum_geometricSeeds K F hFne selected Delta
   (fun gamma hgamma => (hDeltaData gamma hgamma).1.1)
 letI:CharP (GenericField K) p:=genericField_charP K p
 have hsingle (g:GeometricFactor K F):
     (geometricSeeds K F selected Delta g).card*P.gap ≤
       (P.n-P.w)*(∑ i:Fin 3,
         regularCapAt P.leftAgreement i*
           coordinateMixedDegree (GenericField K) g.1
             (surfaceMap phi T) i)+
         (P.errors+1)*P.gap*
           coordinateMixedDegree (GenericField K) g.1
             (surfaceMap phi T) 2:=by
   have hgSpec:=surfaceFactors_spec phi F g.1 g.2
   have hsub:=geometricSeeds_subset K F selected Delta g
   have hgCaps:HasCaps g.1 carrierCap:=by
     intro i
     have hi:=geometricFactor_degree_le K F hFne g i
     fin_cases i
     · exact hi.trans hFY
     · exact hi.trans hFR
     · exact hi.trans hFZ
   have hTCaps:HasCaps (surfaceMap phi T) cutCap:=by
     intro i
     fin_cases i
     · exact (surfaceMap_degreeOf_le phi T 0).trans hTY
     · exact (surfaceMap_degreeOf_le phi T 1).trans hTR
     · exact (surfaceMap_degreeOf_le phi T 2).trans hTZ
   have hcarrierSmall:∀ i,capAt carrierCap i < p:=by
     intro i
     fin_cases i
     · exact hleftYSmall
     · exact hleftRSmall
     · exact hleftZSmall
   have hgates:=actual_characteristic_gates g.1 (surfaceMap phi T)
     carrierCap cutCap p hgCaps hTCaps hcarrierSmall
     (by simpa [carrierCap,cutCap,RCN051.mixed,
         RCN051.unitY,UnequalParameters.mixedCost,
         capAt,Nat.add_comm,Nat.mul_comm] using hmixedYSmall)
     (by simpa [carrierCap,cutCap,RCN051.mixed,
         RCN051.unitR,UnequalParameters.mixedCost,
         capAt,Nat.add_comm,Nat.mul_comm] using hmixedRSmall)
     (by simpa [carrierCap,cutCap,RCN051.mixed,
         RCN051.unitZ,UnequalParameters.mixedCost,
         capAt,Nat.add_comm,Nat.mul_comm] using hmixedZSmall)
   have hregular:∀ gamma∈geometricSeeds K F selected Delta g,
       MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
         (RCN231.polynomialPoint (phi.comp Polynomial.C)
           (selected gamma) gamma (phi Polynomial.X))
         (MvPolynomial.pderiv (2:Fin 4) F)≠0:=by
     intro gamma hgamma
     exact selectedPoint_regular_of_specialization K F selected gamma
       (hDeltaData gamma (hsub hgamma)).1.2
   have hTpoint:∀ gamma∈geometricSeeds K F selected Delta g,
       MvPolynomial.eval (selectedPoint phi selected gamma) (surfaceMap phi T)=0:=by
     intro gamma hgamma
     rw [selectedPoint_surface_evaluation,
       (hDeltaData gamma (hsub hgamma)).2,map_zero]
   have hcap (node:ι):∀ j,
       (agreementPolynomial phi F P.w (x node) (u₀ node) (u₁ node)).degreeOf j ≤
         regularCapAt P.leftAgreement j:=by
     have h:=surface_agreement_caps phi F P.leftY P.leftR P.leftZ hleftR
       hFY hFR hFZ P.w (fun j => (j.factorial:K)⁻¹)
       (x node) (u₀ node) (u₁ node)
     intro j
     have hj:
         (agreementPolynomial phi F P.w (x node) (u₀ node) (u₁ node)).degreeOf j ≤
           capAt (agreementCaps P.leftY P.leftR P.leftZ P.w) j:=by
       simpa [agreementPolynomial] using h j
     fin_cases j <;> exact hj
   have hcount:=proper_cut_seed_bound phi F g.1 (surfaceMap phi T)
     hgSpec.1 hgSpec.2 (hproper g)
     selected (geometricSeeds K F selected Delta g) nodes x u₀ u₁ hinj
     p P.w P.a P.errors hw hchar hwa (by simpa [hnodes] using han)
     hgates.1 hgates.2
     (fun gamma hgamma => hdegree gamma (hDeltaSub (hsub hgamma)))
     (fun gamma hgamma => (hDeltaData gamma (hsub hgamma)).1.1)
     hregular (fun gamma hgamma => (Finset.mem_filter.mp hgamma).2)
     hTpoint
     (fun gamma hgamma => hagreement gamma (hDeltaSub (hsub hgamma)))
     (noLargeSelectedPencil_mono selected Gamma _ P.w P.errors
       (fun _ hgamma => hDeltaSub (hsub hgamma)) hnoPencil)
     (regularCapAt P.leftAgreement) (fun node _ => hcap node)
   simpa [hnodes,UnequalParameters.gap] using hcount
 have hbudget (i:Fin 3):=
   sum_coordinateMixedDegree_geometricFactors_le P F T hFne hTY hTR hTZ i
 have hfubini:
     (∑ g:GeometricFactor K F,∑ i:Fin 3,
         regularCapAt P.leftAgreement i*
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i)=
       ∑ i:Fin 3,regularCapAt P.leftAgreement i*
         (∑ g:GeometricFactor K F,
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i):=by
   rw [Finset.sum_comm]
   apply Finset.sum_congr rfl
   intro i _
   rw [Finset.mul_sum]
 calc
   Delta.card*P.gap ≤
       (∑ g:GeometricFactor K F,
         (geometricSeeds K F selected Delta g).card)*P.gap:=
     Nat.mul_le_mul_right P.gap hcover
   _=∑ g:GeometricFactor K F,
       (geometricSeeds K F selected Delta g).card*P.gap:=by
     rw [Finset.sum_mul]
   _ ≤ ∑ g:GeometricFactor K F,
       ((P.n-P.w)*(∑ i:Fin 3,regularCapAt P.leftAgreement i*
         coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i)+
         (P.errors+1)*P.gap*
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) 2):=
     Finset.sum_le_sum (fun g _ => hsingle g)
   _=(P.n-P.w)*(∑ i:Fin 3,regularCapAt P.leftAgreement i*
         (∑ g:GeometricFactor K F,
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i))+
       (P.errors+1)*P.gap*
         (∑ g:GeometricFactor K F,
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) 2):=by
     rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum,hfubini]
   _ ≤ (P.n-P.w)*(∑ i:Fin 3,
         regularCapAt P.leftAgreement i*regularCapAt (regularVector P F) i)+
       (P.errors+1)*P.gap*regularCapAt (regularVector P F) 2:=
     Nat.add_le_add
       (Nat.mul_le_mul_left _ (Finset.sum_le_sum
         (fun i _ => Nat.mul_le_mul_left _ (hbudget i))))
       (Nat.mul_le_mul_left _ (hbudget 2))
   _=(P.n-P.w)*dot P.leftAgreement (regularVector P F)+
       (P.errors+1)*P.gap*(regularVector P F).z:=by
     simp [Fin.sum_univ_three,regularCapAt,dot]

end
end ProximityPrize.SubmissionLower.SecondJetProperCounting

end Compact_SecondJetProperCounting

section Compact_SecondJetPairBounds
/-! Degree and numerical interfaces for the global proper-intersection count. -/
namespace ProximityPrize.SubmissionLower.SecondJetPairBounds
open MvPolynomial RCN260 RCN052 RCN294 RCN234 RCN156
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {K : Type} [Field K]

theorem degree_caps_of_weights (Q : MvPolynomial (Fin 4) K) (r y t : ℕ)
    (hw : wt residualSWeights Q ≤ r ∧ wt residualYSWeights Q ≤ y ∧
      wt residualTotalWeights Q ≤ t) :
    Q.degreeOf 1 ≤ y ∧ Q.degreeOf 2 ≤ r ∧ Q.degreeOf 3 ≤ t := by
  refine ⟨?_,?_,?_⟩
  all_goals
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
  · have h := (RCN081.weightedTotalDegree_le_iff _ _ _).mp hw.2.1 e he
    simp only [residualYSWeights,RCN081.weight_fin4] at h
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,Fin.isValue,Nat.mul_zero,Nat.mul_one,Nat.zero_add,Nat.add_zero] at h
    omega
  · have h := (RCN081.weightedTotalDegree_le_iff _ _ _).mp hw.1 e he
    simpa [residualSWeights,RCN081.weight_fin4] using h
  · have h := (RCN081.weightedTotalDegree_le_iff _ _ _).mp hw.2.2 e he
    simp [residualTotalWeights,RCN081.weight_fin4] at h
    omega

theorem leading_degree_caps (P : SecondJetSupport.Poly (K := K)) (B U L : ℕ)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ L) :
    (SecondJetCoefficients.asS P).leadingCoeff.degreeOf 1 ≤ U ∧
    (SecondJetCoefficients.asS P).leadingCoeff.degreeOf 2 ≤ B ∧
    (SecondJetCoefficients.asS P).leadingCoeff.degreeOf 3 ≤ L := by
  apply degree_caps_of_weights
  have h := SecondJetHelperWeights.derivative_coefficient_weights P B U L 0
    (SecondJetCoefficients.asS P).natDegree hP
  simp only [Function.iterate_zero,id_eq,Nat.mul_zero,Nat.sub_zero] at h
  change wt residualSWeights ((SecondJetCoefficients.asS P).coeff _) ≤ B ∧
    wt residualYSWeights ((SecondJetCoefficients.asS P).coeff _) ≤ U ∧
    wt residualTotalWeights ((SecondJetCoefficients.asS P).coeff _) ≤ L
  omega

end
end ProximityPrize.SubmissionLower.SecondJetPairBounds

end Compact_SecondJetPairBounds

section Compact_SecondJetRegularData
/-! A common context for counting the retained seeds and the one global
proper-helper or leading-coefficient exceptional set. -/
namespace ProximityPrize.SubmissionLower.SecondJetRegularData
open scoped Classical BigOperators
open MvPolynomial RCN135 RCN136 RCN319 RCN238 RCN243 RCN260 RCN174 RCN275 RCN327
open RCN156 RCN234 LocatorHybridCells LocatorHybridCellsC1 RCN130 RCN095
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance  _root_.ProximityPrize.SubmissionLower.SecondJetRegularData.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.SecondJetRegularData.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I

namespace Data
variable {nodes : I ↪ K} {u0 u1 : I → K}

end Data
end
end ProximityPrize.SubmissionLower.SecondJetRegularData

end Compact_SecondJetRegularData

section Compact_SecondJetWeightedContact
/-! A second contact-two generator for weighted second-jet spaces.
The generator J = R*(A-R) + epsilon*A*S has the same contact as U, but
its leading coefficient contains an additional R. This checks the algebraic
ingredient found by the weighted-space matrix experiments. It does not assert
a new interpolation rank receipt or a stronger protocol claim. -/
namespace ProximityPrize.SubmissionLower.SecondJetWeightedContact
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

variable {B C : Type*} [CommRing B] [CommRing C]

def V (a r : B) : Polynomial B := Polynomial.C (a-r)
def U (a r s : B) : Polynomial B :=
  V a r + Polynomial.X*Polynomial.C s
def J (a r s : B) : Polynomial B :=
  Polynomial.C r*V a r + Polynomial.X*Polynomial.C (a*s)

theorem J_eq (a r s : B) :
    J a r s = Polynomial.C r*U a r s +
      Polynomial.X*Polynomial.C s*V a r := by
  simp only [J, U, V, map_sub, map_mul]
  ring

theorem contact_J (a r s : B) (φ : Polynomial B →+* C) (ε : C)
    (hε : φ Polynomial.X = ε)
    (hU : ε^2 ∣ φ (U a r s)) (hV : ε ∣ φ (V a r)) :
    ε^2 ∣ φ (J a r s) := by
  obtain ⟨u, hu⟩ := hU
  obtain ⟨v, hv⟩ := hV
  refine ⟨φ (Polynomial.C r)*u + φ (Polynomial.C s)*v, ?_⟩
  rw [J_eq, map_add, map_mul, map_mul, map_mul, hε, hu, hv]
  ring

def family (a r s z : B) (ρ h u v i j ℓ : ℕ) : Polynomial B :=
  Polynomial.X^ρ * (Polynomial.C (s^h) *
    U a r s^(u-ℓ) * J a r s^ℓ * V a r^v *
    Polynomial.C (a^i*r^(j-ℓ)*z))

theorem family_contact (a r s z : B) (ρ h u v i j ℓ : ℕ)
    (hℓ : ℓ ≤ u) (φ : Polynomial B →+* C) (ε : C)
    (hε : φ Polynomial.X = ε)
    (hU : ε^2 ∣ φ (U a r s)) (hV : ε ∣ φ (V a r)) :
    ε^(ρ+2*u+v) ∣ φ (family a r s z ρ h u v i j ℓ) := by
  have hJ := contact_J a r s φ ε hε hU hV
  obtain ⟨cu, hu⟩ := hU
  obtain ⟨cv, hv⟩ := hV
  obtain ⟨cj, hj⟩ := hJ
  refine ⟨φ (Polynomial.C (s^h))*cu^(u-ℓ)*cj^ℓ*cv^v*
    φ (Polynomial.C (a^i*r^(j-ℓ)*z)), ?_⟩
  simp only [family, map_mul, map_pow, hε, hu, hv, hj, mul_pow]
  have he : ρ+2*u+v = ρ+2*(u-ℓ)+2*ℓ+v := by omega
  rw [he]
  simp only [pow_add, pow_mul]
  ring

theorem family_coeff_lt (a r s z : B) (ρ h u v i j ℓ d : ℕ)
    (hd : d < ρ) : (family a r s z ρ h u v i j ℓ).coeff d = 0 := by
  simp [family, Polynomial.coeff_X_pow_mul', Nat.not_le.mpr hd]

theorem family_coeff_self (a r s z : B) (ρ h u v i j ℓ : ℕ)
    (hu : ℓ ≤ u) (hj : ℓ ≤ j) :
    (family a r s z ρ h u v i j ℓ).coeff ρ =
      s^h*(a-r)^(u+v)*(a^i*r^j*z) := by
  obtain ⟨u', rfl⟩ := Nat.exists_eq_add_of_le hu
  obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le hj
  simp only [family, Polynomial.coeff_X_pow_mul', Nat.sub_self, if_pos (le_refl ρ)]
  simp [Polynomial.coeff_zero_eq_eval_zero, U, J, V, pow_add]
  rw [mul_pow]
  ring

end
end ProximityPrize.SubmissionLower.SecondJetWeightedContact

end Compact_SecondJetWeightedContact

section Compact_SecondJetWeightedBasis
/-! Independence of the U/J/V family with J powers selected per monomial.
This proves independence only. Finite support and counting remain separate. -/
namespace ProximityPrize.SubmissionLower.SecondJetWeightedBasis
open scoped BigOperators
open SecondJetBasis SecondJetSupport SecondJetRank SecondJetLocal
open MvPolynomial
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K : Type*} [Field K]

theorem C_smul_base (c : K) (v : Base (K := K)) :
    Polynomial.C (c • v) = c • (Polynomial.C v : Polynomial (Base (K := K))) :=
  map_smul (Polynomial.CAlgHom (R := K) (A := Base (K := K))) c v

/-- The inner polynomial variable is S and the outer variable is epsilon. -/
def weightedTerm (r h a b : ℕ) (e : Fin 3 →₀ ℕ) : Jet (Base (K := K)) :=
  SecondJetWeightedContact.family
    (Polynomial.C (MvPolynomial.X 0)) (Polynomial.C (MvPolynomial.X 1))
    Polynomial.X (Polynomial.C (MvPolynomial.X 2^(e 2)))
    r h a b (e 0) (e 1) (min a (e 1))

theorem weightedTerm_coeff_lt (r h a b : ℕ) (e : Fin 3 →₀ ℕ)
    (d : ℕ) (hd : d < r) : (weightedTerm (K := K) r h a b e).coeff d = 0 :=
  SecondJetWeightedContact.family_coeff_lt _ _ _ _ _ _ _ _ _ _ _ _ hd

theorem weightedTerm_coeff_self (r h a b : ℕ) (e : Fin 3 →₀ ℕ) :
    (weightedTerm (K := K) r h a b e).coeff r = Polynomial.X^h *
      Polynomial.C (SecondJetLocal.v^(a+b)*MvPolynomial.monomial e (1 : K)) := by
  rw [weightedTerm, SecondJetWeightedContact.family_coeff_self _ _ _ _ _ _ _ _ _ _ _
    (min_le_left _ _) (min_le_right _ _)]
  have hm : MvPolynomial.monomial e (1 : K) =
      MvPolynomial.X 0^(e 0)*MvPolynomial.X 1^(e 1)*MvPolynomial.X 2^(e 2) := by
    rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
    · simp [Fin.prod_univ_three]
    · intro i; simp
  rw [hm]
  simp only [SecondJetLocal.v, map_sub, map_mul, map_pow, mul_assoc]

variable {m s : ℕ} {I : Fin m → Fin s → Type*} [∀ r h, Fintype (I r h)]
abbrev Parameters := ∀ r : Fin m, ∀ h : Fin s, I r h → K

def weightedMake (a b : Fin m → Fin s → ℕ)
    (e : ∀ r h, I r h → Fin 3 →₀ ℕ) : Parameters (K := K) (I := I) →ₗ[K] Jet (Base (K := K)) :=
  ∑ r, ∑ h, ∑ i, LinearMap.smulRight
    (((LinearMap.proj i : (I r h → K) →ₗ[K] K).comp
      (LinearMap.proj h : (∀ h, I r h → K) →ₗ[K] (I r h → K))).comp (LinearMap.proj r : Parameters (K := K) (I := I) →ₗ[K] (∀ h, I r h → K)))
    (weightedTerm r.val h.val (a r h) (b r h) (e r h i))

theorem weightedMake_apply (a b : Fin m → Fin s → ℕ)
    (e : ∀ r h, I r h → Fin 3 →₀ ℕ) (p : Parameters (K := K) (I := I)) :
    weightedMake a b e p = ∑ r, ∑ h, ∑ i,
      p r h i • weightedTerm r.val h.val (a r h) (b r h) (e r h i) := by
  simp [weightedMake]

theorem weightedMake_initial (a b : Fin m → Fin s → ℕ)
    (e : ∀ r h, I r h → Fin 3 →₀ ℕ) (p : Parameters (K := K) (I := I)) (r : Fin m)
    (hp : ∀ j, j.val < r.val → p j = 0) :
    (weightedMake a b e p).coeff r.val = ∑ h, Polynomial.X^h.val *
      Polynomial.C (SecondJetLocal.v^(a r h+b r h)*FiniteMonomials.reconstruct (e r h) (p r h)) := by
  rw [weightedMake_apply, Polynomial.finsetSum_coeff, Finset.sum_eq_single r]
  · simp_rw [Polynomial.finsetSum_coeff, Polynomial.coeff_smul, weightedTerm_coeff_self]
    apply Finset.sum_congr rfl
    intro h _
    rw [FiniteMonomials.reconstruct_apply, Finset.mul_sum, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hm : MvPolynomial.monomial (e r h i) (p r h i) =
        p r h i • MvPolynomial.monomial (e r h i) (1 : K) := by
      simpa only [smul_eq_mul, mul_one] using
        (map_smul (MvPolynomial.monomial (e r h i)) (p r h i) (1 : K))
    rw [hm]
    simp only [mul_smul_comm, C_smul_base]
  · intro j _ hj
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_smul]
    apply Finset.sum_eq_zero
    intro h _
    apply Finset.sum_eq_zero
    intro i _
    by_cases hlt : j.val < r.val
    · simp [hp j hlt]
    · rw [weightedTerm_coeff_lt]
      · simp
      · have hne : j.val ≠ r.val := fun he => hj (Fin.ext he)
        omega
  · simp

theorem truncate_weightedMake_initial (a b : Fin m → Fin s → ℕ)
    (e : ∀ r h, I r h → Fin 3 →₀ ℕ) (p : Parameters (K := K) (I := I)) (r : Fin m)
    (hp : ∀ j, j.val < r.val → p j = 0) :
    truncate (K := K) (m := m) (s := s) (weightedMake a b e p) r =
      fun h => SecondJetLocal.v^(a r h+b r h)*FiniteMonomials.reconstruct (e r h) (p r h) := by
  funext h
  rw [truncate_apply, weightedMake_initial a b e p r hp, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_mul_C, Polynomial.coeff_X_pow, Fin.val_inj]
  simp

theorem truncate_weightedMake_injective (a b : Fin m → Fin s → ℕ)
    (e : ∀ r h, I r h → Fin 3 →₀ ℕ) (he : ∀ r h, Function.Injective (e r h)) :
    Function.Injective ((truncate (K := K) (m := m) (s := s)).comp (weightedMake a b e)) := by
  let D : ∀ r : Fin m, (∀ h : Fin s, I r h → K) →ₗ[K] (Fin s → Base (K := K)) := fun r =>
    LinearMap.pi (fun h => (LinearMap.mulLeft K (SecondJetLocal.v^(a r h+b r h))).comp
      ((FiniteMonomials.reconstruct (e r h)).comp (LinearMap.proj h)))
  apply TriangularKernel.injective_of_triangular _ D
  · intro r p q hpq
    funext h i
    have hh := congrFun hpq h
    change SecondJetLocal.v^(a r h+b r h)*FiniteMonomials.reconstruct (e r h) (p h) =
      SecondJetLocal.v^(a r h+b r h)*FiniteMonomials.reconstruct (e r h) (q h) at hh
    have hz := mul_left_cancel₀ (pow_ne_zero _ (SecondJetLocal.v_ne_zero (K := K))) hh
    exact congrFun (FiniteMonomials.reconstruct_injective (e r h) (he r h) hz) i
  · intro p r hp
    exact truncate_weightedMake_initial a b e p r hp

theorem truncateOuter_weightedMake_injective (a b : Fin m → Fin s → ℕ)
    (e : ∀ r h, I r h → Fin 3 →₀ ℕ) (he : ∀ r h, Function.Injective (e r h)) :
    Function.Injective ((truncateOuter (K := K) m).comp (weightedMake a b e)) := by
  intro p q hpq
  apply truncate_weightedMake_injective a b e he
  have hh := congrArg (truncate (K := K) (m := m) (s := s)) hpq
  simpa only [LinearMap.comp_apply, truncate_truncateOuter] using hh

/-- Every concretely embedded and vanishing instance of this independent family
saves its full cardinality in the local rank bound. -/
theorem finite_source_rank {T : Type*} [AddCommGroup T] [Module K T]
    (W : Submodule K (Jet (Base (K := K)))) [FiniteDimensional K W]
    (f : W →ₗ[K] T) (a b : Fin m → Fin s → ℕ)
    (e : ∀ r h, I r h → Fin 3 →₀ ℕ) (he : ∀ r h, Function.Injective (e r h))
    (hW : ∀ p, truncateOuter (K := K) m (weightedMake a b e p) ∈ W)
    (hzero : ∀ p, f ⟨truncateOuter (K := K) m (weightedMake a b e p), hW p⟩ = 0) :
    Module.finrank K f.range + (∑ r : Fin m, ∑ h : Fin s, Fintype.card (I r h)) ≤
      Module.finrank K W := by
  let g := (truncateOuter (K := K) m).comp (weightedMake a b e)
  have hg : Function.Injective g := truncateOuter_weightedMake_injective a b e he
  let gw : Parameters (K := K) (I := I) →ₗ[K] W := g.codRestrict W hW
  let gk : Parameters (K := K) (I := I) →ₗ[K] f.ker := gw.codRestrict f.ker hzero
  have hi : Function.Injective gk := by
    intro p q hpq
    apply hg
    exact congrArg (fun x : f.ker => (x.val : Jet (Base (K := K)))) hpq
  letI : AddCommGroup W := inferInstance
  letI : Module K W := W.module
  letI : FiniteDimensional K f.ker := inferInstance
  have hdim := LinearMap.finrank_le_finrank_of_injective hi
  have hsum := f.finrank_range_add_finrank_ker
  have hd : Module.finrank K (Parameters (K := K) (I := I)) =
      ∑ r : Fin m, ∑ h : Fin s, Fintype.card (I r h) := by
    simp [Parameters, Module.finrank_pi_fintype]
  rw [hd] at hdim
  omega

end
end ProximityPrize.SubmissionLower.SecondJetWeightedBasis

end Compact_SecondJetWeightedBasis

section Compact_SecondJetWeightedSupport
/-! Signed linear support bounds for the weighted second-jet kernel family. -/
namespace ProximityPrize.SubmissionLower.SecondJetWeightedSupport
open scoped BigOperators Pointwise
open MvPolynomial SecondJetSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K : Type*} [Field K]

def weight (w : Fin 5 → ℤ) (e : Fin 5 →₀ ℕ) : ℤ := ∑ j, (e j : ℤ)*w j

def LinearBound (w : Fin 5 → ℤ) (b : ℤ) (P : Poly (K := K)) : Prop :=
  ∀ e ∈ P.support, weight w e ≤ b

theorem weight_add (w : Fin 5 → ℤ) (e f : Fin 5 →₀ ℕ) :
    weight w (e+f) = weight w e+weight w f := by
  simp [weight, Finsupp.add_apply, add_mul, Finset.sum_add_distrib]

theorem LinearBound.mono {w : Fin 5 → ℤ} {b c : ℤ} {P : Poly (K := K)}
    (h : LinearBound w b P) (hbc : b ≤ c) : LinearBound w c P :=
  fun e he => (h e he).trans hbc

theorem LinearBound.mul {w : Fin 5 → ℤ} {b c : ℤ} {P Q : Poly (K := K)}
    (hP : LinearBound w b P) (hQ : LinearBound w c Q) : LinearBound w (b+c) (P*Q) := by
  intro e he
  obtain ⟨f,hf,g,hg,rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q he)
  rw [weight_add]
  exact add_le_add (hP f hf) (hQ g hg)

theorem LinearBound.add {w : Fin 5 → ℤ} {b : ℤ} {P Q : Poly (K := K)}
    (hP : LinearBound w b P) (hQ : LinearBound w b Q) : LinearBound w b (P+Q) := by
  intro e he
  rcases Finset.mem_union.mp (MvPolynomial.support_add he) with h | h
  · exact hP e h
  · exact hQ e h

theorem LinearBound.neg {w : Fin 5 → ℤ} {b : ℤ} {P : Poly (K := K)}
    (hP : LinearBound w b P) : LinearBound w b (-P) := by
  simpa only [LinearBound, MvPolynomial.support_neg] using hP

theorem linear_one (w : Fin 5 → ℤ) : LinearBound w 0 (1 : Poly (K := K)) := by
  intro e he
  simp only [MvPolynomial.support_one, Finset.mem_singleton] at he
  subst e
  simp [weight]

theorem LinearBound.pow {w : Fin 5 → ℤ} {b : ℤ} {P : Poly (K := K)}
    (hP : LinearBound w b P) (n : ℕ) : LinearBound w ((n : ℤ)*b) (P^n) := by
  induction n with
  | zero => simpa using linear_one (K := K) w
  | succ n ih => simpa only [pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using ih.mul hP

theorem linear_X (w : Fin 5 → ℤ) (j : Fin 5) :
    LinearBound w (w j) (MvPolynomial.X j : Poly (K := K)) := by
  intro e he
  simp only [MvPolynomial.support_X, Finset.mem_singleton] at he
  subst e
  simp [weight, Finsupp.single_apply]

def weightedVector (r h a b i j z l : ℕ) : Poly (K := K) :=
  MvPolynomial.X 0^r * MvPolynomial.X 1^h *
    (MvPolynomial.X 2-MvPolynomial.X 3+MvPolynomial.X 0*MvPolynomial.X 1)^(a-l) *
    (MvPolynomial.X 3*(MvPolynomial.X 2-MvPolynomial.X 3)+
      MvPolynomial.X 0*MvPolynomial.X 2*MvPolynomial.X 1)^l *
    (MvPolynomial.X 2-MvPolynomial.X 3)^b *
    MvPolynomial.X 2^i * MvPolynomial.X 3^(j-l) * MvPolynomial.X 4^z

theorem weightedVector_bound (w : Fin 5 → ℤ) (r h a b i j z l : ℕ) :
    LinearBound w ((r : ℤ)*w 0+(h : ℤ)*w 1+
      ((a-l : ℕ) : ℤ)*max (max (w 2) (w 3)) (w 0+w 1)+
      (l : ℤ)*max (w 3+max (w 2) (w 3)) (w 0+w 2+w 1)+
      (b : ℤ)*max (w 2) (w 3)+(i : ℤ)*w 2+((j-l : ℕ) : ℤ)*w 3+(z : ℤ)*w 4)
      (weightedVector (K := K) r h a b i j z l) := by
  have hE := linear_X (K := K) w 0
  have hS := linear_X (K := K) w 1
  have hA := linear_X (K := K) w 2
  have hR := linear_X (K := K) w 3
  have hZ := linear_X (K := K) w 4
  have hV : LinearBound w (max (w 2) (w 3))
      (MvPolynomial.X 2-MvPolynomial.X 3 : Poly (K := K)) := by
    rw [sub_eq_add_neg]
    exact (hA.mono (le_max_left _ _)).add (hR.neg.mono (le_max_right _ _))
  have hU := (hV.mono (le_max_left _ (w 0+w 1))).add
    ((hE.mul hS).mono (le_max_right _ _))
  have hJ := ((hR.mul hV).mono (le_max_left _ (w 0+w 2+w 1))).add
    (((hE.mul hA).mul hS).mono (le_max_right _ _))
  exact (((((((hE.pow r).mul (hS.pow h)).mul (hU.pow (a-l))).mul (hJ.pow l)).mul
    (hV.pow b)).mul (hA.pow i)).mul (hR.pow (j-l))).mul (hZ.pow z)

theorem weightedVector_support (r h a b i j z l : ℕ) (hla : l ≤ a) (hlj : l ≤ j)
    (e : Fin 5 →₀ ℕ) (he : e ∈ (weightedVector (K := K) r h a b i j z l).support) :
    r ≤ e 0 ∧ e 2 ≤ i+a+b ∧ e 3 ≤ j+a+b ∧ h ≤ e 1 ∧ e 1 ≤ h+a ∧
      e 1+e 2+e 3 ≤ i+j+h+a+b ∧ e 1+e 2+e 3+e 4 ≤ i+j+h+a+b+z ∧
      2*e 1+e 3 ≤ 2*h+2*a+b+j-l := by
  have h0 := weightedVector_bound (K := K) ![-1,0,0,0,0] r h a b i j z l e he
  have hA := weightedVector_bound (K := K) ![0,0,1,0,0] r h a b i j z l e he
  have hR := weightedVector_bound (K := K) ![0,0,0,1,0] r h a b i j z l e he
  have hSlo := weightedVector_bound (K := K) ![0,-1,0,0,0] r h a b i j z l e he
  have hShi := weightedVector_bound (K := K) ![0,1,0,0,0] r h a b i j z l e he
  have hM := weightedVector_bound (K := K) ![0,1,1,1,0] r h a b i j z l e he
  have hT := weightedVector_bound (K := K) ![0,1,1,1,1] r h a b i j z l e he
  have hB := weightedVector_bound (K := K) ![0,2,0,1,0] r h a b i j z l e he
  norm_num [weight, Fin.sum_univ_five, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] at h0 hA hR hSlo hShi hM hT hB
  omega

end
end ProximityPrize.SubmissionLower.SecondJetWeightedSupport

end Compact_SecondJetWeightedSupport

section Compact_SecondJetWeightedLocal
/-! The weighted independent family in flat coordinates and under contact. -/
namespace ProximityPrize.SubmissionLower.SecondJetWeightedLocal
open SecondJetBasis SecondJetSupport SecondJetLocal SecondJetWeightedBasis
open SecondJetWeightedSupport MvPolynomial
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K : Type*} [Field K]

theorem flatEquiv_weightedVector (r h a b : ℕ) (e : Fin 3 →₀ ℕ) :
    flatEquiv (K := K) (weightedVector (K := K) r h a b (e 0) (e 1) (e 2) (min a (e 1))) =
      weightedTerm (K := K) r h a b e := by
  simp only [weightedVector, map_mul, map_pow, map_add, map_sub, flatEquiv_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four]
  simp only [Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  simp only [weightedTerm, SecondJetWeightedContact.family, SecondJetWeightedContact.U,
    SecondJetWeightedContact.V, SecondJetWeightedContact.J, map_mul, map_pow, map_add, map_sub]
  ring

theorem weightedTerm_vanishes (m r h a b : ℕ) (e : Fin 3 →₀ ℕ)
    (horder : m ≤ r+2*a+b) :
    Polynomial.X^m ∣ contact (K := K) (weightedTerm (K := K) r h a b e) := by
  apply (pow_dvd_pow Polynomial.X horder).trans
  unfold weightedTerm
  apply SecondJetWeightedContact.family_contact _ _ _ _ _ _ _ _ _ _ _
    (min_le_left _ _) (contact (K := K)).toRingHom Polynomial.X contact_X
  · have hu : (Polynomial.X : Target (K := K))^2 ∣ contact (K := K)
        (Polynomial.C (Polynomial.C SecondJetLocal.v)+Polynomial.X*Polynomial.C Polynomial.X) :=
      ⟨Polynomial.C (MvPolynomial.X 1), contact_u⟩
    simpa only [SecondJetWeightedContact.U, SecondJetWeightedContact.V,
      SecondJetLocal.v, map_sub, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hu
  · have hv : (Polynomial.X : Target (K := K)) ∣
        contact (K := K) (Polynomial.C (Polynomial.C SecondJetLocal.v)) := by
      rw [contact_v]
      exact dvd_mul_right _ _
    simpa only [SecondJetWeightedContact.V, SecondJetLocal.v, map_sub, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hv

end
end ProximityPrize.SubmissionLower.SecondJetWeightedLocal

end Compact_SecondJetWeightedLocal

section Compact_SecondJetRelaxedSpace
/-! The clipped local source for degree-sensitive weighted second jets. -/
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedSpace
open scoped BigOperators
open SecondJetBasis SecondJetSupport SecondJetWeightedSupport SecondJetWeightedLocal
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

def Index (m L B s U : ℕ) (caps : ℕ → ℕ) :=
  {d : SecondJetSpace.Index m L B s // 2*(d.val 1).val+(d.val 3).val ≤ B ∧
    (d.val 1).val+(d.val 2).val+(d.val 3).val ≤ U ∧
    (d.val 1).val+(d.val 2).val+(d.val 3).val ≤ caps (d.val 1).val}

instance  _root_.ProximityPrize.SubmissionLower.SecondJetRelaxedSpace.instFintypeIndex (m L B s U : ℕ) (caps : ℕ → ℕ) : Fintype (Index m L B s U caps) := by
  unfold Index
  infer_instance

def exponent {m L B s U : ℕ} {caps : ℕ → ℕ} (d : Index m L B s U caps) : Fin 5 →₀ ℕ :=
  SecondJetSpace.exponent d.val

theorem exponent_injective (m L B s U : ℕ) (caps : ℕ → ℕ) :
    Function.Injective (exponent (m := m) (L := L) (B := B) (s := s) (U := U) (caps := caps)) :=
  (SecondJetSpace.exponent_injective m L B s).comp Subtype.val_injective

theorem mem_range_exponent (m L B s U : ℕ) (caps : ℕ → ℕ) (d : Fin 5 →₀ ℕ) :
    d ∈ Set.range (exponent (m := m) (L := L) (B := B) (s := s) (U := U) (caps := caps)) ↔
      Allowed m L B s d ∧ 2*d 1+d 3 ≤ B ∧ d 1+d 2+d 3 ≤ U ∧ d 1+d 2+d 3 ≤ caps (d 1) := by
  constructor
  · rintro ⟨e,rfl⟩
    exact ⟨SecondJetSpace.exponent_allowed e.val,e.property⟩
  · rintro ⟨hd, hrs⟩
    obtain ⟨e,he⟩ := (SecondJetSpace.mem_range_exponent m L B s d).mpr hd
    have hrs' : 2*(e.val 1).val+(e.val 3).val ≤ B ∧ (e.val 1).val+(e.val 2).val+(e.val 3).val ≤ U ∧ (e.val 1).val+(e.val 2).val+(e.val 3).val ≤ caps (e.val 1).val := by
      simpa only [← he, SecondJetSpace.exponent_apply] using hrs
    exact ⟨⟨e,hrs'⟩,he⟩

def sourceMap (m L B s U : ℕ) (caps : ℕ → ℕ) : (Index m L B s U caps → K) →ₗ[K]
    Jet (MvPolynomial (Fin 3) K) :=
  (flatEquiv (K := K)).toLinearMap.comp (FiniteMonomials.reconstruct exponent)

def source (m L B s U : ℕ) (caps : ℕ → ℕ) : Submodule K (Jet (MvPolynomial (Fin 3) K)) :=
  (sourceMap (K := K) m L B s U caps).range

instance source_finite (m L B s U : ℕ) (caps : ℕ → ℕ) : FiniteDimensional K (source (K := K) m L B s U caps) := by
  unfold source
  infer_instance

theorem sourceMap_injective (m L B s U : ℕ) (caps : ℕ → ℕ) :
    Function.Injective (sourceMap (K := K) m L B s U caps) :=
  (flatEquiv (K := K)).injective.comp
    (FiniteMonomials.reconstruct_injective _ (exponent_injective m L B s U caps))

theorem finrank_source (m L B s U : ℕ) (caps : ℕ → ℕ) :
    Module.finrank K (source (K := K) m L B s U caps) = Fintype.card (Index m L B s U caps) := by
  unfold source
  rw [← (LinearEquiv.ofInjective (sourceMap (K := K) m L B s U caps)
    (sourceMap_injective m L B s U caps)).finrank_eq]
  simp

theorem mem_source_iff (m L B s U : ℕ) (caps : ℕ → ℕ) (P : Jet (MvPolynomial (Fin 3) K)) :
    P ∈ source (K := K) m L B s U caps ↔
      ∀ d ∈ ((flatEquiv (K := K)).symm P).support,
        Allowed m L B s d ∧ 2*d 1+d 3 ≤ B ∧ d 1+d 2+d 3 ≤ U ∧ d 1+d 2+d 3 ≤ caps (d 1) := by
  have hm : P ∈ source (K := K) m L B s U caps ↔
      (flatEquiv (K := K)).symm P ∈ (FiniteMonomials.reconstruct (K := K)
        (exponent (m := m) (L := L) (B := B) (s := s) (U := U) (caps := caps))).range := by
    constructor
    · rintro ⟨c,hc⟩
      refine ⟨c,?_⟩
      have h := congrArg (flatEquiv (K := K)).symm hc
      simpa [sourceMap] using h
    · rintro ⟨c,hc⟩
      refine ⟨c,?_⟩
      have h := congrArg (flatEquiv (K := K)) hc
      simpa [sourceMap] using h
  rw [hm, FiniteMonomials.mem_range_iff _ (exponent_injective m L B s U caps)]
  simp only [mem_range_exponent]

theorem truncated_weightedTerm_mem (m L B s U : ℕ) (caps : ℕ → ℕ)
    (r h a b : ℕ) (e : Fin 3 →₀ ℕ)
    (hi : e 0+a+b ≤ r) (hS : h+a ≤ s)
    (hB : 2*h+2*a+b+e 1-min a (e 1) ≤ B)
    (hU : e 0+e 1+h+a+b ≤ U)
    (hL : e 0+e 1+h+a+b+e 2 ≤ L)
    (hcaps : ∀ j, h ≤ j → j ≤ h+a → e 0+e 1+h+a+b ≤ caps j) :
    truncateOuter (K := K) m (SecondJetWeightedBasis.weightedTerm r h a b e) ∈
      source (K := K) m L B s U caps := by
  rw [← flatEquiv_weightedVector, ← flatEquiv_truncFlat, mem_source_iff]
  simp only [AlgEquiv.symm_apply_apply]
  intro d hd
  have ht := support_truncFlat m _ d hd
  obtain ⟨h0,hA,hR,hlo,hhi,hM,hT,hRS⟩ := weightedVector_support r h a b
    (e 0) (e 1) (e 2) (min a (e 1)) (min_le_left _ _) (min_le_right _ _) d ht.2
  refine ⟨?_,hRS.trans hB,hM.trans hU,hM.trans (hcaps (d 1) hlo hhi)⟩
  dsimp only [Allowed]
  exact ⟨ht.1,by omega,by omega,by omega,hT.trans hL⟩

end
end ProximityPrize.SubmissionLower.SecondJetRelaxedSpace

end Compact_SecondJetRelaxedSpace

section Compact_SecondJetClippedRectangle
/-! A clipped rectangle is an ordinary rectangle minus its small reflected
corner. The closed expression only sums over the removed corner. -/
namespace ProximityPrize.SubmissionLower.SecondJetClippedRectangle
open scoped BigOperators
open SecondJetCounts
set_option autoImplicit false
set_option maxHeartbeats 4000000

def corner (A B H : ℕ) : ℕ := A+B-2-H

def clippedRectangle (A B C H : ℕ) : ℕ :=
  rectangle A B C - ∑ i ∈ Finset.range (corner A B H),
    ∑ j ∈ Finset.range (corner A B H),
      if i+j < corner A B H then C-(A-1-i)-(B-1-j) else 0

theorem outside_sum (A B C H : ℕ) (hA : 0 < A) (hB : 0 < B)
    (hkA : corner A B H ≤ A) (hkB : corner A B H ≤ B) :
    (∑ i ∈ Finset.range A, ∑ j ∈ Finset.range B, if H < i+j then C-i-j else 0) =
      ∑ i ∈ Finset.range (corner A B H), ∑ j ∈ Finset.range (corner A B H),
        if i+j < corner A B H then C-(A-1-i)-(B-1-j) else 0 := by
  classical
  let s := ((Finset.range A) ×ˢ (Finset.range B)).filter (fun p => H < p.1+p.2)
  let t := ((Finset.range (corner A B H)) ×ˢ (Finset.range (corner A B H))).filter
    (fun p => p.1+p.2 < corner A B H)
  have heq : (∑ p ∈ s, (C-p.1-p.2)) =
      ∑ p ∈ t, (C-(A-1-p.1)-(B-1-p.2)) := by
    apply Finset.sum_bij (fun p _ => (A-1-p.1,B-1-p.2))
    · intro p hp
      simp only [s, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      simp only [t, Finset.mem_filter, Finset.mem_product, Finset.mem_range, corner,
        Prod.fst, Prod.snd]
      dsimp [corner] at hkA hkB
      omega
    · intro p hp q hq hpq
      simp only [s, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp hq
      have h1 := congrArg Prod.fst hpq
      have h2 := congrArg Prod.snd hpq
      apply Prod.ext <;> dsimp at h1 h2 ⊢ <;> omega
    · intro p hp
      simp only [t, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      refine ⟨(A-1-p.1,B-1-p.2),?_,?_⟩
      · simp only [s, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Prod.fst, Prod.snd]
        dsimp [corner] at hp hkA hkB
        omega
      · apply Prod.ext <;> dsimp <;> omega
    · intro p hp
      have hpmem : (p.1 < A ∧ p.2 < B) ∧ H < p.1+p.2 := by
        simpa only [s, Finset.mem_filter, Finset.mem_product, Finset.mem_range] using hp
      change C-p.1-p.2 = C-(A-1-(A-1-p.1))-(B-1-(B-1-p.2))
      omega
  simpa only [s,t,Finset.sum_filter,Finset.sum_product] using heq

theorem sum_clipped_rectangle (A B C H : ℕ) (hA : 0 < A) (hB : 0 < B)
    (hkA : corner A B H ≤ A) (hkB : corner A B H ≤ B)
    (hC : ∀ i : Fin A, ∀ j : Fin B, i.val+j.val ≤ C) :
    (∑ i : Fin A, ∑ j : Fin B, if i.val+j.val ≤ H then C-i.val-j.val else 0) =
      clippedRectangle A B C H := by
  have hsum :
      (∑ i : Fin A, ∑ j : Fin B, if i.val+j.val ≤ H then C-i.val-j.val else 0) +
      (∑ i : Fin A, ∑ j : Fin B, if H < i.val+j.val then C-i.val-j.val else 0) =
        rectangle A B C := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ i : Fin A, ∑ j : Fin B, (C-i.val-j.val) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : i.val+j.val ≤ H <;> simp [h, Nat.not_lt_of_ge, Nat.lt_of_not_ge]
      _ = _ := sum_rectangle A B C hC
  have hout := outside_sum A B C H hA hB hkA hkB
  have houtside :
      (∑ i : Fin A, ∑ j : Fin B, if H < i.val+j.val then C-i.val-j.val else 0) =
      ∑ i ∈ Finset.range A, ∑ j ∈ Finset.range B, if H < i+j then C-i-j else 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ∑ j : Fin B, if H < i+j.val then C-i-j.val else 0)]
    apply Finset.sum_congr rfl
    intro i _
    exact Fin.sum_univ_eq_sum_range (fun j : ℕ => if H < i+j then C-i-j else 0) B
  rw [houtside, hout] at hsum
  unfold clippedRectangle
  omega

end ProximityPrize.SubmissionLower.SecondJetClippedRectangle

end Compact_SecondJetClippedRectangle

section Compact_SecondJetRelaxedSourceCounts
/-! Closed source counts when the varying middle caps contain the uniform cap. -/
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedSourceCounts
open scoped BigOperators
open SecondJetRelaxedSpace SecondJetClippedRectangle
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

abbrev SourceSumIndex (m L B s U : ℕ) :=
  Σ r : Fin m, Σ h : Fin (s+1), Σ i : Fin (r.val+1), Σ j : Fin (B-2*h.val+1),
    Fin (if h.val+i.val+j.val ≤ U then L+1-h.val-i.val-j.val else 0)

def sourceEquiv (m L B s U : ℕ) (caps : ℕ → ℕ) (hsB : 2*s ≤ B)
    (hcaps : ∀ h, h ≤ s → U ≤ caps h) :
    Index m L B s U caps ≃ SourceSumIndex m L B s U where
  toFun d := by
    have hi := d.val.property.1
    have ht := d.val.property.2
    have hd := d.property
    refine ⟨d.val.val 0,d.val.val 1,⟨(d.val.val 2).val,by omega⟩,
      ⟨(d.val.val 3).val,by change (d.val.val 3).val < B-2*(d.val.val 1).val+1; omega⟩,
      ⟨(d.val.val 4).val,?_⟩⟩
    change (d.val.val 4).val <
      if (d.val.val 1).val+(d.val.val 2).val+(d.val.val 3).val ≤ U then
        L+1-(d.val.val 1).val-(d.val.val 2).val-(d.val.val 3).val else 0
    rw [if_pos hd.2.1]
    omega
  invFun u := by
    rcases u with ⟨r,h,i,j,z⟩
    have hh := h.isLt
    have hi := i.isLt
    have hj := j.isLt
    have hz := z.isLt
    have hU : h.val+i.val+j.val ≤ U := by
      by_contra hn
      simp only [if_neg hn] at hz
      omega
    simp only [if_pos hU] at hz
    let iv : Fin m := ⟨i.val,by have hr := r.isLt; omega⟩
    let jv : Fin (B+1) := ⟨j.val,by omega⟩
    let zv : Fin (L+1) := ⟨z.val,by omega⟩
    let d : ∀ k, Fin (SecondJetSpace.bound m L B s k) :=
      Fin.cases r (Fin.cases h (Fin.cases iv (Fin.cases jv (Fin.cases zv (fun i => Fin.elim0 i)))))
    refine ⟨⟨d,?_,?_⟩,?_,?_,?_⟩
    · change i.val ≤ r.val
      omega
    · change h.val+i.val+j.val+z.val ≤ L
      omega
    · change 2*h.val+j.val ≤ B
      omega
    · exact hU
    · exact hU.trans (hcaps h.val (by omega))
  left_inv d := by
    apply Subtype.ext
    apply Subtype.ext
    funext k
    apply Fin.ext
    fin_cases k <;> rfl
  right_inv u := by
    rcases u with ⟨r,h,i,j,z⟩
    rfl

theorem card_source (m L B s U : ℕ) (caps : ℕ → ℕ) (hsB : 2*s ≤ B)
    (hcaps : ∀ h, h ≤ s → U ≤ caps h) :
    Fintype.card (Index m L B s U caps) =
      ∑ r : Fin m, ∑ h : Fin (s+1), ∑ i : Fin (r.val+1), ∑ j : Fin (B-2*h.val+1),
        if h.val+i.val+j.val ≤ U then L+1-h.val-i.val-j.val else 0 := by
  rw [Fintype.card_congr (sourceEquiv m L B s U caps hsB hcaps)]
  simp [SourceSumIndex]

def sourceCount (m L B s U : ℕ) : ℕ :=
  ∑ r : Fin m, ∑ h : Fin (s+1),
    clippedRectangle (r.val+1) (B-2*h.val+1) (L+1-h.val) (U-h.val)

theorem card_source_closed (m L B s U : ℕ) (caps : ℕ → ℕ)
    (hsB : 2*s ≤ B) (hBm : B ≤ m) (hU : m+s ≤ U) (hL : m+B+s ≤ L)
    (hcaps : ∀ h, h ≤ s → U ≤ caps h) :
    Fintype.card (Index m L B s U caps) = sourceCount m L B s U := by
  rw [card_source m L B s U caps hsB hcaps]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro h _
  have hr := r.isLt
  have hh := h.isLt
  have heq :
      (∑ i : Fin (r.val+1), ∑ j : Fin (B-2*h.val+1),
        if h.val+i.val+j.val ≤ U then L+1-h.val-i.val-j.val else 0) =
      ∑ i : Fin (r.val+1), ∑ j : Fin (B-2*h.val+1),
        if i.val+j.val ≤ U-h.val then (L+1-h.val)-i.val-j.val else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hc : (h.val+i.val+j.val ≤ U) ↔ (i.val+j.val ≤ U-h.val) := by omega
    simp only [hc]
  rw [heq]
  apply sum_clipped_rectangle
  · omega
  · omega
  · dsimp [corner]
    omega
  · dsimp [corner]
    omega
  · intro i j
    have hi := i.isLt
    have hj := j.isLt
    omega

end
end ProximityPrize.SubmissionLower.SecondJetRelaxedSourceCounts

end Compact_SecondJetRelaxedSourceCounts

section Compact_SecondJetRelaxedRank
/-! A rank bound for the clipped second-jet space using the independent U/J/V
family. Its finite cardinalities are explicit; numerical receipts are separate. -/
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedRank
open scoped BigOperators
open SecondJetBasis SecondJetSupport SecondJetLocal SecondJetRelaxedSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K : Type*} [Field K]

def q (m s r h : ℕ) := max ((m-r+1)/2) (m-r-(s-h))
def a (m s r h : ℕ) := m-r-q m s r h
def b (m s r h : ℕ) := q m s r h-a m s r h

theorem budgets (m s r h : ℕ) (hr : r ≤ m) (hh : h ≤ s) :
    a m s r h+b m s r h = q m s r h ∧ h+a m s r h ≤ s ∧
      r+2*a m s r h+b m s r h = m := by
  dsimp [a,b,q]
  omega

def Block (m L B s U : ℕ) (caps : ℕ → ℕ) (r h : ℕ) :=
  {e : Fin 3 → Fin (L+1) //
    (e 0).val+q m s r h ≤ r ∧ (e 1).val+q m s r h+2*h ≤ B ∧
    m-r+2*h ≤ B ∧ (e 0).val+(e 1).val+h+q m s r h ≤ U ∧
    (e 0).val+(e 1).val+h+q m s r h+(e 2).val ≤ L ∧
    ∀ j : Fin (a m s r h+1),
      (e 0).val+(e 1).val+h+q m s r h ≤ caps (h+j.val)}

instance  _root_.ProximityPrize.SubmissionLower.SecondJetRelaxedRank.instFintypeBlock (m L B s U : ℕ) (caps : ℕ → ℕ) (r h : ℕ) :
    Fintype (Block m L B s U caps r h) := by
  unfold Block
  infer_instance

def exponent {m L B s U : ℕ} {caps : ℕ → ℕ} {r h : ℕ}
    (e : Block m L B s U caps r h) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => (e.val j).val)

@[simp] theorem exponent_apply {m L B s U : ℕ} {caps : ℕ → ℕ} {r h : ℕ}
    (e : Block m L B s U caps r h) (j : Fin 3) : exponent e j = (e.val j).val := by
  simp [exponent]

theorem exponent_injective (m L B s U : ℕ) (caps : ℕ → ℕ) (r h : ℕ) :
    Function.Injective (exponent (m := m) (L := L) (B := B) (s := s) (U := U)
      (caps := caps) (r := r) (h := h)) := by
  intro e f hef
  apply Subtype.ext
  funext j
  apply Fin.ext
  simpa only [exponent_apply] using congrArg (fun g : Fin 3 →₀ ℕ => g j) hef

abbrev Parameters (m L B s U : ℕ) (caps : ℕ → ℕ) :=
  ∀ r : Fin m, ∀ h : Fin (s+1), Block m L B s U caps r.val h.val → K

def make (m L B s U : ℕ) (caps : ℕ → ℕ) :
    Parameters (K := K) m L B s U caps →ₗ[K] Jet (Base (K := K)) :=
  (truncateOuter (K := K) m).comp (SecondJetWeightedBasis.weightedMake
    (fun r h => a m s r.val h.val) (fun r h => b m s r.val h.val)
    (fun _ _ => exponent))

theorem make_mem_source (m L B s U : ℕ) (caps : ℕ → ℕ)
    (p : Parameters (K := K) m L B s U caps) :
    make m L B s U caps p ∈ source (K := K) m L B s U caps := by
  simp only [make, LinearMap.comp_apply, SecondJetWeightedBasis.weightedMake_apply, map_sum, map_smul]
  apply Submodule.sum_mem
  intro r _
  apply Submodule.sum_mem
  intro h _
  apply Submodule.sum_mem
  intro e _
  apply Submodule.smul_mem
  have hb := budgets m s r.val h.val (Nat.le_of_lt r.isLt) (Nat.le_of_lt_succ h.isLt)
  have he := e.property
  apply truncated_weightedTerm_mem
  · simp only [exponent_apply]
    omega
  · exact hb.2.1
  · simp only [exponent_apply]
    omega
  · simp only [exponent_apply]
    omega
  · simp only [exponent_apply]
    omega
  · intro j hj hj'
    have hd := he.2.2.2.2.2 (⟨j-h.val, by omega⟩ : Fin (a m s r.val h.val+1))
    simp only [exponent_apply]
    dsimp at hd
    have hjj : h.val+(j-h.val)=j := by omega
    rw [hjj] at hd
    omega

def restrictedMap (m L B s U : ℕ) (caps : ℕ → ℕ) :
    source (K := K) m L B s U caps →ₗ[K] Target (K := K) :=
  (SecondJetRank.contactMap (K := K) m).comp (source (K := K) m L B s U caps).subtype

theorem make_zero (m L B s U : ℕ) (caps : ℕ → ℕ)
    (p : Parameters (K := K) m L B s U caps) :
    SecondJetRank.contactMap (K := K) m (make m L B s U caps p) = 0 := by
  change contact (K := K) (make m L B s U caps p) %ₘ Polynomial.X^m = 0
  apply (Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_pow m)).mpr
  change Polynomial.X^m ∣ contact (K := K) (truncateOuter (K := K) m _)
  apply truncateOuter_contact (K := K) (contact (K := K)).toRingHom Polynomial.X m _ contact_X
  change Polynomial.X^m ∣ contact (K := K) _
  rw [SecondJetWeightedBasis.weightedMake_apply, map_sum]
  apply Finset.dvd_sum
  intro r _
  rw [map_sum]
  apply Finset.dvd_sum
  intro h _
  rw [map_sum]
  apply Finset.dvd_sum
  intro e _
  rw [map_smul, Algebra.smul_def]
  apply dvd_mul_of_dvd_right
  apply SecondJetWeightedLocal.weightedTerm_vanishes
  exact le_of_eq (budgets m s r.val h.val (Nat.le_of_lt r.isLt)
    (Nat.le_of_lt_succ h.isLt)).2.2.symm

theorem local_rank_bound (m L B s U : ℕ) (caps : ℕ → ℕ) :
    Module.finrank K (restrictedMap (K := K) m L B s U caps).range +
      (∑ r : Fin m, ∑ h : Fin (s+1), Fintype.card (Block m L B s U caps r.val h.val)) ≤
        Fintype.card (Index m L B s U caps) := by
  have h := SecondJetWeightedBasis.finite_source_rank
    (source (K := K) m L B s U caps) (restrictedMap (K := K) m L B s U caps)
    (fun r h => a m s r.val h.val) (fun r h => b m s r.val h.val)
    (fun _ _ => exponent) (fun r h => exponent_injective m L B s U caps r.val h.val)
    (make_mem_source m L B s U caps) (make_zero m L B s U caps)
  rwa [finrank_source] at h

end
end ProximityPrize.SubmissionLower.SecondJetRelaxedRank

end Compact_SecondJetRelaxedRank

section Compact_SecondJetRelaxedKernelCounts
/-! Closed kernel counts for the independent weighted second-jet family. -/
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedKernelCounts
open scoped BigOperators
open SecondJetRelaxedRank SecondJetClippedRectangle
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000

abbrev BlockSumIndex (m L B s U r h : ℕ) :=
  Σ i : Fin (r-q m s r h+1), Σ j : Fin (B-2*h-q m s r h+1),
    Fin (if h+q m s r h+i.val+j.val ≤ U then L+1-h-q m s r h-i.val-j.val else 0)

def blockEquiv (m L B s U : ℕ) (caps : ℕ → ℕ) (r h : ℕ)
    (hrm : r ≤ m) (hhs : h ≤ s)
    (hr : q m s r h ≤ r) (hB : m-r+2*h ≤ B)
    (hcaps : ∀ h, h ≤ s → U ≤ caps h) :
    Block m L B s U caps r h ≃ BlockSumIndex m L B s U r h where
  toFun d := by
    have hd := d.property
    refine ⟨⟨(d.val 0).val,by omega⟩,⟨(d.val 1).val,by omega⟩,
      ⟨(d.val 2).val,?_⟩⟩
    change (d.val 2).val < if h+q m s r h+(d.val 0).val+(d.val 1).val ≤ U then
      L+1-h-q m s r h-(d.val 0).val-(d.val 1).val else 0
    rw [if_pos (by omega)]
    omega
  invFun u := by
    rcases u with ⟨i,j,z⟩
    have hi := i.isLt
    have hj := j.isLt
    have hz := z.isLt
    have hU : h+q m s r h+i.val+j.val ≤ U := by
      by_contra hn
      simp only [if_neg hn] at hz
      omega
    simp only [if_pos hU] at hz
    have hb := budgets m s r h hrm hhs
    let iv : Fin (L+1) := ⟨i.val,by omega⟩
    let jv : Fin (L+1) := ⟨j.val,by omega⟩
    let zv : Fin (L+1) := ⟨z.val,by omega⟩
    refine ⟨![iv,jv,zv],?_,?_,?_,?_,?_,?_⟩
    · change i.val+q m s r h ≤ r
      omega
    · change j.val+q m s r h+2*h ≤ B
      omega
    · exact hB
    · change i.val+j.val+h+q m s r h ≤ U
      omega
    · change i.val+j.val+h+q m s r h+z.val ≤ L
      omega
    · intro t
      change i.val+j.val+h+q m s r h ≤ caps (h+t.val)
      have ht := t.isLt
      have hc := hcaps (h+t.val) (by omega)
      omega
  left_inv d := by
    apply Subtype.ext
    funext k
    apply Fin.ext
    fin_cases k <;> rfl
  right_inv u := by
    rcases u with ⟨i,j,z⟩
    rfl

theorem card_block_of_le (m L B s U : ℕ) (caps : ℕ → ℕ) (r h : ℕ)
    (hrm : r ≤ m) (hhs : h ≤ s)
    (hr : q m s r h ≤ r) (hB : m-r+2*h ≤ B)
    (hcaps : ∀ h, h ≤ s → U ≤ caps h) :
    Fintype.card (Block m L B s U caps r h) =
      ∑ i : Fin (r-q m s r h+1), ∑ j : Fin (B-2*h-q m s r h+1),
        if h+q m s r h+i.val+j.val ≤ U then L+1-h-q m s r h-i.val-j.val else 0 := by
  rw [Fintype.card_congr (blockEquiv m L B s U caps r h hrm hhs hr hB hcaps)]
  simp [BlockSumIndex]

theorem card_block_of_not_le (m L B s U : ℕ) (caps : ℕ → ℕ) (r h : ℕ)
    (hq : ¬ (q m s r h ≤ r ∧ m-r+2*h ≤ B)) :
    Fintype.card (Block m L B s U caps r h) = 0 := by
  letI : IsEmpty (Block m L B s U caps r h) := ⟨fun d => by have hd := d.property; omega⟩
  simp

def kernelCell (m L B s U r h : ℕ) : ℕ :=
  if q m s r h ≤ r ∧ m-r+2*h ≤ B then
    clippedRectangle (r-q m s r h+1) (B-2*h-q m s r h+1)
      (L+1-h-q m s r h) (U-h-q m s r h)
  else 0

theorem card_block_closed (m L B s U : ℕ) (caps : ℕ → ℕ) (r h : ℕ)
    (hBm : B ≤ m) (hU : m+s ≤ U) (hL : m+B+s ≤ L)
    (hrm : r < m) (hhs : h ≤ s)
    (hcaps : ∀ h, h ≤ s → U ≤ caps h) :
    Fintype.card (Block m L B s U caps r h) = kernelCell m L B s U r h := by
  unfold kernelCell
  split_ifs with hq
  · rw [card_block_of_le m L B s U caps r h (by omega) hhs hq.1 hq.2 hcaps]
    have hb := budgets m s r h (by omega) hhs
    have heq :
        (∑ i : Fin (r-q m s r h+1), ∑ j : Fin (B-2*h-q m s r h+1),
          if h+q m s r h+i.val+j.val ≤ U then L+1-h-q m s r h-i.val-j.val else 0) =
        ∑ i : Fin (r-q m s r h+1), ∑ j : Fin (B-2*h-q m s r h+1),
          if i.val+j.val ≤ U-h-q m s r h then (L+1-h-q m s r h)-i.val-j.val else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      have hc : (h+q m s r h+i.val+j.val ≤ U) ↔
          (i.val+j.val ≤ U-h-q m s r h) := by omega
      simp only [hc]
    rw [heq]
    apply sum_clipped_rectangle
    · omega
    · omega
    · dsimp [corner]
      omega
    · dsimp [corner]
      omega
    · intro i j
      have hi := i.isLt
      have hj := j.isLt
      omega
  · exact card_block_of_not_le m L B s U caps r h hq

def kernelCount (m L B s U : ℕ) : ℕ :=
  ∑ r : Fin m, ∑ h : Fin (s+1), kernelCell m L B s U r.val h.val

theorem card_kernel_sum (m L B s U : ℕ) (caps : ℕ → ℕ)
    (hBm : B ≤ m) (hU : m+s ≤ U) (hL : m+B+s ≤ L)
    (hcaps : ∀ h, h ≤ s → U ≤ caps h) :
    (∑ r : Fin m, ∑ h : Fin (s+1), Fintype.card (Block m L B s U caps r.val h.val)) =
      kernelCount m L B s U := by
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro h _
  exact card_block_closed m L B s U caps r.val h.val hBm hU hL r.isLt
    (Nat.le_of_lt_succ h.isLt) hcaps

end
end ProximityPrize.SubmissionLower.SecondJetRelaxedKernelCounts

end Compact_SecondJetRelaxedKernelCounts

section Compact_SecondJetRelaxedGlobalSupport
/-! Localization preserves the degree-sensitive clipped second-jet source. -/
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedGlobalSupport
open scoped BigOperators
open MvPolynomial SecondJetSupport SecondJetBasis SecondJetGlobalSupport
open SecondJetWeightedSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K : Type*} [Field K]

theorem linear_C (w : Fin 5 → ℤ) (c : K) : LinearBound w 0 (MvPolynomial.C c) := by
  intro e he
  have he0 : e = 0 := Finset.mem_singleton.mp (MvPolynomial.support_C_subset he)
  subst e
  simp [weight]

theorem localize_X_bound (w : Fin 5 → ℤ) (hw0 : w 0 = 0) (hw4 : w 4 = 0)
    (hw2 : 0 ≤ w 2) (x u0 u1 : K) (j : Fin 5) :
    LinearBound w (w j) (localize x u0 u1 (MvPolynomial.X j)) := by
  have hE := linear_X (K := K) w 0
  have hZ := linear_X (K := K) w 4
  fin_cases j
  · simpa [localize, hw0] using (linear_C w x).add (hE.mono (by omega))
  · simpa [localize] using linear_X (K := K) w 1
  · have hU : LinearBound w (w 2)
        (MvPolynomial.C u0+MvPolynomial.C u1*MvPolynomial.X 4 : Poly (K := K)) :=
      ((linear_C w u0).mono hw2).add (((linear_C w u1).mul hZ).mono (by omega))
    have hA := linear_X (K := K) w 2
    simpa [localize] using hU.add ((hE.mul hA).mono (by omega))
  · simpa [localize] using linear_X (K := K) w 3
  · simpa [localize] using hZ

theorem localize_monomial_bound (w : Fin 5 → ℤ) (hw0 : w 0 = 0) (hw4 : w 4 = 0)
    (hw2 : 0 ≤ w 2) (x u0 u1 : K) (e : Fin 5 →₀ ℕ) (c : K) :
    LinearBound w (weight w e) (localize x u0 u1 (MvPolynomial.monomial e c)) := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
  · simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, map_mul, map_pow, map_C]
    have h0 := (localize_X_bound w hw0 hw4 hw2 x u0 u1 0).pow (e 0)
    have h1 := (localize_X_bound w hw0 hw4 hw2 x u0 u1 1).pow (e 1)
    have h2 := (localize_X_bound w hw0 hw4 hw2 x u0 u1 2).pow (e 2)
    have h3 := (localize_X_bound w hw0 hw4 hw2 x u0 u1 3).pow (e 3)
    have h4 := (localize_X_bound w hw0 hw4 hw2 x u0 u1 4).pow (e 4)
    simpa [weight, Fin.sum_univ_five, add_assoc] using
      (linear_C w c).mul (h0.mul (h1.mul (h2.mul (h3.mul h4))))
  · intro i
    simp

theorem localize_support (x u0 u1 : K) (e d : Fin 5 →₀ ℕ) (c : K)
    (hd : d ∈ (localize x u0 u1 (MvPolynomial.monomial e c)).support) :
    d 1 = e 1 ∧ 2*d 1+d 3 ≤ 2*e 1+e 3 ∧ d 1+d 2+d 3 ≤ e 1+e 2+e 3 := by
  have hs := localize_monomial_bound ![0,1,0,0,0] (by rfl) (by rfl) (by decide) x u0 u1 e c d hd
  have hl := localize_monomial_bound ![0,-1,0,0,0] (by rfl) (by rfl) (by decide) x u0 u1 e c d hd
  have hB := localize_monomial_bound ![0,2,0,1,0] (by rfl) (by rfl) (by decide) x u0 u1 e c d hd
  have hM := localize_monomial_bound ![0,1,1,1,0] (by rfl) (by rfl) (by decide) x u0 u1 e c d hd
  norm_num [weight, Fin.sum_univ_five, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four] at hs hl hB hM
  omega

/-- The global weighted cutoff induces the local middle-degree cap used by
all three numerical profiles. -/
theorem middle_cap (e : Fin 5 →₀ ℕ) (w B D : ℕ) (hw : 2 ≤ w)
    (hB : 2*e 1+e 3 ≤ B)
    (hD : e 0+w*e 2+(w-1)*e 3+(w-2)*e 1 < D) :
    e 1+e 2+e 3 ≤ (D+B-1)/w := by
  apply (Nat.le_div_iff_mul_le (by omega : 0 < w)).mpr
  have h1 : w-1+1=w := by omega
  have h2 : w-2+2=w := by omega
  have hh : (e 1+e 2+e 3)*w < D+B := by nlinarith
  omega

theorem truncated_local_monomial_mem (x u0 u1 : K) (m L B s U w : ℕ)
    (D : ℕ → ℕ) (hw : 2 ≤ w) (e : Fin 5 →₀ ℕ) (c : K)
    (hB : 2*e 1+e 3 ≤ B) (hs : e 1 ≤ s)
    (hU : e 1+e 2+e 3 ≤ U) (hL : e 1+e 2+e 3+e 4 ≤ L)
    (hD : e 0+w*e 2+(w-1)*e 3+(w-2)*e 1 < D (e 1)) :
    truncateOuter (K := K) m (flatEquiv (K := K)
      (localize x u0 u1 (MvPolynomial.monomial e c))) ∈
        SecondJetRelaxedSpace.source (K := K) m L B s U (fun h => (D h+B-1)/w) := by
  rw [← flatEquiv_truncFlat, SecondJetRelaxedSpace.mem_source_iff]
  simp only [AlgEquiv.symm_apply_apply]
  intro d hd
  obtain ⟨hm,hd'⟩ := support_truncFlat m _ d hd
  have hb := localize_monomial x u0 u1 e c d hd'
  obtain ⟨hS,hRS,hM⟩ := localize_support x u0 u1 e d c hd'
  have hcap := middle_cap e w B (D (e 1)) hw hB hD
  refine ⟨⟨hm,hb.1,by omega,by omega,hb.2.2.2.trans hL⟩,hRS.trans hB,hM.trans hU,?_⟩
  simpa only [hS] using hM.trans hcap

end
end ProximityPrize.SubmissionLower.SecondJetRelaxedGlobalSupport

end Compact_SecondJetRelaxedGlobalSupport

section Compact_SecondJetRelaxedGlobalMap
/-! Global interpolation from the clipped weighted local rank bound. -/
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedGlobalMap
open scoped BigOperators
open SecondJetSupport SecondJetBasis SecondJetGlobalSupport
open SecondJetGlobalMap (coefficientLocal untruncate_contact)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K I N : Type*} [Field K] [Fintype I] [Fintype N]

def rankBound (m L B s U : ℕ) (caps : ℕ → ℕ) : ℕ :=
  Fintype.card (SecondJetRelaxedSpace.Index m L B s U caps) -
    ∑ r : Fin m, ∑ h : Fin (s+1),
      Fintype.card (SecondJetRelaxedRank.Block m L B s U caps r.val h.val)

theorem local_rank_le_count (m L B s U : ℕ) (caps : ℕ → ℕ) :
    Module.finrank K (SecondJetRelaxedRank.restrictedMap (K := K) m L B s U caps).range ≤
      rankBound m L B s U caps := by
  have hh := SecondJetRelaxedRank.local_rank_bound (K := K) m L B s U caps
  unfold rankBound
  omega

theorem coefficientLocal_mem (e : I → Fin 5 →₀ ℕ) (m L B s U w : ℕ) (D : ℕ → ℕ)
    (hw : 2 ≤ w) (x u0 u1 : K)
    (hB : ∀ i, 2*e i 1+e i 3 ≤ B) (hs : ∀ i, e i 1 ≤ s)
    (hU : ∀ i, e i 1+e i 2+e i 3 ≤ U)
    (hL : ∀ i, e i 1+e i 2+e i 3+e i 4 ≤ L)
    (hD : ∀ i, e i 0+w*e i 2+(w-1)*e i 3+(w-2)*e i 1 < D (e i 1)) (c : I → K) :
    coefficientLocal e m x u0 u1 c ∈
      SecondJetRelaxedSpace.source (K := K) m L B s U (fun h => (D h+B-1)/w) := by
  change truncateOuter (K := K) m (flatEquiv (K := K)
    (localize x u0 u1 (FiniteMonomials.reconstruct e c))) ∈ _
  rw [FiniteMonomials.reconstruct_apply]
  simp_rw [map_sum]
  apply Submodule.sum_mem
  intro i _
  exact SecondJetRelaxedGlobalSupport.truncated_local_monomial_mem
    x u0 u1 m L B s U w D hw (e i) (c i) (hB i) (hs i) (hU i) (hL i) (hD i)

theorem exists_global_contact (e : I → Fin 5 →₀ ℕ) (he : Function.Injective e)
    (m L B s U w : ℕ) (D : ℕ → ℕ) (hw : 2 ≤ w)
    (hB : ∀ i, 2*e i 1+e i 3 ≤ B) (hs : ∀ i, e i 1 ≤ s)
    (hU : ∀ i, e i 1+e i 2+e i 3 ≤ U)
    (hL : ∀ i, e i 1+e i 2+e i 3+e i 4 ≤ L)
    (hD : ∀ i, e i 0+w*e i 2+(w-1)*e i 3+(w-2)*e i 1 < D (e i 1))
    (x u0 u1 : N → K)
    (hcard : Fintype.card N*rankBound m L B s U (fun h => (D h+B-1)/w) < Fintype.card I) :
    ∃ P : Poly (K := K), P ≠ 0 ∧ (∀ d ∈ P.support, d ∈ Set.range e) ∧
      ∀ n, Polynomial.X^m ∣ SecondJetLocal.contact (K := K)
        (flatEquiv (K := K) (localize (x n) (u0 n) (u1 n) P)) := by
  classical
  let caps := fun h => (D h+B-1)/w
  let f := SecondJetRelaxedRank.restrictedMap (K := K) m L B s U caps
  letI : AddCommGroup f.range := inferInstance
  letI : Module K f.range := f.range.module
  letI : FiniteDimensional K f.range := by
    change FiniteDimensional K (SecondJetRelaxedRank.restrictedMap (K := K) m L B s U caps).range
    infer_instance
  let ell (n : N) : (I → K) →ₗ[K] SecondJetRelaxedSpace.source (K := K) m L B s U caps :=
    (coefficientLocal e m (x n) (u0 n) (u1 n)).codRestrict _
      (coefficientLocal_mem e m L B s U w D hw (x n) (u0 n) (u1 n) hB hs hU hL hD)
  let g : (I → K) →ₗ[K] (N → f.range) :=
    LinearMap.pi (fun n => f.rangeRestrict.comp (ell n))
  have hdim : Module.finrank K (N → f.range) ≤ Fintype.card N*rankBound m L B s U caps := by
    rw [Module.finrank_pi_fintype]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    exact Nat.mul_le_mul_left _ (local_rank_le_count m L B s U caps)
  dsimp only [caps] at hdim
  have hrange := g.range.finrank_le
  have hsum := g.finrank_range_add_finrank_ker
  have hpos : 0 < Module.finrank K g.ker := by
    have hdimI : Module.finrank K (I → K) = Fintype.card I := by simp
    omega
  have hne : g.ker ≠ ⊥ := by
    intro h
    rw [h] at hpos
    simp at hpos
  obtain ⟨c,hc,hc0⟩ := (Submodule.ne_bot_iff _).mp hne
  have hcz : g c = 0 := LinearMap.mem_ker.mp hc
  refine ⟨FiniteMonomials.reconstruct e c,?_,?_,?_⟩
  · intro hz
    apply hc0
    apply FiniteMonomials.reconstruct_injective e he
    simpa only [map_zero] using hz
  · exact (FiniteMonomials.mem_range_iff e he _).mp ⟨c,rfl⟩
  · intro n
    have hz := congrArg Subtype.val (congrFun hcz n)
    change SecondJetRank.contactMap (K := K) m (coefficientLocal e m (x n) (u0 n) (u1 n) c) = 0 at hz
    have hd : Polynomial.X^m ∣ SecondJetLocal.contact (K := K)
        (coefficientLocal e m (x n) (u0 n) (u1 n) c) :=
      (Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_pow m)).mp hz
    exact untruncate_contact (SecondJetLocal.contact (K := K)).toRingHom Polynomial.X m _
      SecondJetLocal.contact_X hd

end
end ProximityPrize.SubmissionLower.SecondJetRelaxedGlobalMap

end Compact_SecondJetRelaxedGlobalMap

section Compact_SecondJetRelaxedCounts
/-! The closed local rank expression used by the concrete interpolation receipts. -/
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedCounts
open scoped BigOperators
open SecondJetRelaxedSourceCounts SecondJetRelaxedKernelCounts
noncomputable section
set_option autoImplicit false

def rankBound (m L B s U : ℕ) : ℕ := sourceCount m L B s U-kernelCount m L B s U

theorem rankBound_eq_closed (m L B s U : ℕ) (caps : ℕ → ℕ)
    (hsB : 2*s ≤ B) (hBm : B ≤ m) (hU : m+s ≤ U) (hL : m+B+s ≤ L)
    (hcaps : ∀ h, h ≤ s → U ≤ caps h) :
    SecondJetRelaxedGlobalMap.rankBound m L B s U caps = rankBound m L B s U := by
  unfold SecondJetRelaxedGlobalMap.rankBound rankBound
  rw [card_source_closed m L B s U caps hsB hBm hU hL hcaps,
    card_kernel_sum m L B s U caps hBm hU hL hcaps]

variable {K : Type*} [Field K]

end
end ProximityPrize.SubmissionLower.SecondJetRelaxedCounts

end Compact_SecondJetRelaxedCounts

section Compact_SecondJetRelaxedGlobalIndex
/-! A finite global monomial family with separate weight budgets by S degree. -/
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedGlobalIndex
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

def budget (D : ℕ → ℕ) (w h r : ℕ) := D h-(w-2)*h-(w-1)*r
def yCount (D : ℕ → ℕ) (w U h r : ℕ) :=
  min ((budget D w h r-1)/w+1) (U+1-h-r)
abbrev Index (D : ℕ → ℕ) (w L B s U : ℕ) :=
  Σ h : Fin (s+1), Σ r : Fin (B-2*h.val+1), Σ y : Fin (yCount D w U h.val r.val),
    Fin (budget D w h.val r.val-w*y.val) × Fin (L+1-h.val-r.val-y.val)

def exponent {D : ℕ → ℕ} {w L B s U : ℕ} (i : Index D w L B s U) : Fin 5 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    ![i.2.2.2.1.val,i.1.val,i.2.2.1.val,i.2.1.val,i.2.2.2.2.val]

theorem exponent_injective (D : ℕ → ℕ) (w L B s U : ℕ) :
    Function.Injective (exponent (D := D) (w := w) (L := L) (B := B) (s := s) (U := U)) := by
  rintro ⟨h,r,y,x,z⟩ ⟨h',r',y',x',z'⟩ he
  have hv : ∀ k : Fin 5, ![x.val,h.val,y.val,r.val,z.val] k =
      ![x'.val,h'.val,y'.val,r'.val,z'.val] k := by
    intro k
    simpa [exponent] using congrArg (fun d : Fin 5 →₀ ℕ => d k) he
  have hh : h = h' := Fin.ext (hv 1)
  subst h'
  have hr : r = r' := Fin.ext (hv 3)
  subst r'
  have hy : y = y' := Fin.ext (hv 2)
  subst y'
  have hx : x = x' := Fin.ext (hv 0)
  have hz : z = z' := Fin.ext (hv 4)
  subst x'
  subst z'
  rfl

theorem exponent_bounds (D : ℕ → ℕ) (w L B s U : ℕ) (hsB : 2*s ≤ B)
    (i : Index D w L B s U) :
    2*exponent i 1+exponent i 3 ≤ B ∧ exponent i 1 ≤ s ∧
      exponent i 1+exponent i 2+exponent i 3 ≤ U ∧
      exponent i 1+exponent i 2+exponent i 3+exponent i 4 ≤ L ∧
      exponent i 0+w*exponent i 2+(w-1)*exponent i 3+(w-2)*exponent i 1 < D (exponent i 1) := by
  rcases i with ⟨h,r,y,x,z⟩
  have hh := h.isLt
  have hr := r.isLt
  have hy := y.isLt
  have hx := x.isLt
  have hz := z.isLt
  simp only [budget] at hx
  simp only [yCount] at hy
  simp [exponent]
  omega

theorem card_index (D : ℕ → ℕ) (w L B s U : ℕ) :
    Fintype.card (Index D w L B s U) =
      ∑ h : Fin (s+1), ∑ r : Fin (B-2*h.val+1), ∑ y : Fin (yCount D w U h.val r.val),
        (budget D w h.val r.val-w*y.val)*(L+1-h.val-r.val-y.val) := by
  simp [Index]

variable {K N : Type*} [Field K] [Fintype N]
theorem exists_weighted_global_contact (D : ℕ → ℕ) (w L B s U m : ℕ)
    (hsB : 2*s ≤ B) (hw : 2 ≤ w) (x u0 u1 : N → K)
    (hcard : Fintype.card N*SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (D h+B-1)/w) < Fintype.card (Index D w L B s U)) :
    ∃ P : SecondJetSupport.Poly (K := K), P ≠ 0 ∧
      (∀ d ∈ P.support, 2*d 1+d 3 ≤ B ∧ d 1 ≤ s ∧ d 1+d 2+d 3 ≤ U ∧
        d 1+d 2+d 3+d 4 ≤ L ∧ d 0+w*d 2+(w-1)*d 3+(w-2)*d 1 < D (d 1)) ∧
      ∀ n, Polynomial.X^m ∣ SecondJetLocal.contact (K := K)
        (SecondJetSupport.flatEquiv (K := K)
          (SecondJetGlobalSupport.localize (x n) (u0 n) (u1 n) P)) := by
  obtain ⟨P,hP,hPex,hcontact⟩ := SecondJetRelaxedGlobalMap.exists_global_contact
    exponent (exponent_injective D w L B s U) m L B s U w D hw
    (fun i => (exponent_bounds D w L B s U hsB i).1)
    (fun i => (exponent_bounds D w L B s U hsB i).2.1)
    (fun i => (exponent_bounds D w L B s U hsB i).2.2.1)
    (fun i => (exponent_bounds D w L B s U hsB i).2.2.2.1)
    (fun i => (exponent_bounds D w L B s U hsB i).2.2.2.2) x u0 u1 hcard
  refine ⟨P,hP,?_,hcontact⟩
  intro d hd
  obtain ⟨i,rfl⟩ := hPex d hd
  exact exponent_bounds D w L B s U hsB i

end
end ProximityPrize.SubmissionLower.SecondJetRelaxedGlobalIndex

end Compact_SecondJetRelaxedGlobalIndex

section Compact_SecondJetRelaxedGlobalCounts
/-! Closed coefficient sums for the relaxed global monomial family. -/
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedGlobalCounts
open scoped BigOperators
open SecondJetRelaxedGlobalIndex
open SecondJetGlobalCounts (weightedCell sum_weighted_cell)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem y_weight_le (D : ℕ → ℕ) (w U h r : ℕ) (y : Fin (yCount D w U h r)) :
    w*y.val ≤ budget D w h r := by
  have hy : y.val ≤ (budget D w h r-1)/w := by
    have hh := y.isLt
    unfold yCount at hh
    omega
  calc
    w*y.val ≤ w*((budget D w h r-1)/w) := Nat.mul_le_mul_left w hy
    _ ≤ budget D w h r-1 := by
      simpa only [mul_comm] using Nat.div_mul_le_self (budget D w h r-1) w
    _ ≤ budget D w h r := Nat.sub_le _ _

def coefficientCount (D : ℕ → ℕ) (w L B s U : ℕ) : ℕ :=
  ∑ h : Fin (s+1), ∑ r : Fin (B-2*h.val+1),
    weightedCell (budget D w h.val r.val) w (L+1-h.val-r.val) (yCount D w U h.val r.val)

theorem card_index_closed (D : ℕ → ℕ) (w L B s U : ℕ) (hUL : U ≤ L) :
    Fintype.card (Index D w L B s U) = coefficientCount D w L B s U := by
  rw [card_index]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro r _
  apply sum_weighted_cell
  · exact y_weight_le D w U h.val r.val
  · intro y
    have hy := y.isLt
    unfold yCount at hy
    omega

end
end ProximityPrize.SubmissionLower.SecondJetRelaxedGlobalCounts

end Compact_SecondJetRelaxedGlobalCounts

section Compact_SecondJetRelaxedDifferentiation
/-! Degree-sensitive S budgets preserve the required derivative vanishings.
This module is conditional on the source support and contact hypotheses; it
makes no claim that the new interpolation source has positive nullity. -/
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedDifferentiation
open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetDifferentiation
open SecondJetGlobalDifferentiation SecondJetSpecialize
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K N : Type*} [Field K]

/-- Low S coefficients reserve their own derivative order. Higher coefficients
reserve the common requested order. The cutoff is strictly above that order. -/
def reserve (k n0 h : ℕ) : ℕ := if h < n0 then h else k

theorem reserve_ge_order (k n0 h d : ℕ) (hdk : d ≤ k) (hdh : d ≤ h) :
    d ≤ reserve k n0 h := by
  unfold reserve
  split <;> assumption

theorem derivative_weight (P : Poly (K := K)) (m a w k n0 d : ℕ)
    (hwa : w-2 ≤ a) (hdm : d ≤ m) (hdk : d ≤ k)
    (hP : ∀ e ∈ P.support,
      e 0+w*e 2+(w-1)*e 3+(w-2)*e 1+
        reserve k n0 (e 1)*(a-(w-2)) < m*a)
    (e : Fin 5 →₀ ℕ) (he : e ∈ ((pderiv 1)^[d] P).support) :
    e 0+w*e 2+(w-1)*e 3+(w-2)*e 1 < (m-d)*a := by
  have hh := hP _ (support_iterate P d e he)
  simp [Finsupp.add_apply, Finsupp.single_apply, Fin.ext_iff] at hh
  have hr := reserve_ge_order k n0 (e 1+d) d hdk (by omega)
  have hp := Nat.mul_le_mul_right (a-(w-2)) hr
  have ha : a-(w-2)+(w-2) = a := Nat.sub_add_cancel hwa
  have hm : (m-d)*a+d*a = m*a := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hdm]
  nlinarith

/-- Every requested derivative vanishes after codeword specialization whenever
its contact and degree-sensitive support bounds are supplied. -/
theorem derivative_vanish (P : Poly (K := K)) (m a w k n0 d : ℕ)
    (ha : 0 < a) (hwa : w-2 ≤ a) (hdm : d < m) (hdk : d ≤ k)
    (hP : ∀ e ∈ P.support,
      e 0+w*e 2+(w-1)*e 3+(w-2)*e 1+
        reserve k n0 (e 1)*(a-(w-2)) < m*a)
    (nodes : N ↪ K) (u0 u1 : N → K)
    (hcontact : ∀ i, MvPolynomial.X 0^m ∣ substitute (K := K)
      (localize (nodes i) (u0 i) (u1 i) P))
    (f : Polynomial K) (hf : f.natDegree ≤ w) (z : K) (S : Finset N)
    (hS : a ≤ S.card) (hvalues : ∀ i ∈ S, f.eval (nodes i) = u0 i+u1 i*z) :
    specialize f z ((pderiv 1)^[d] P) = 0 := by
  refine SecondJetVanish.eq_zero_of_contact_degree _ f z nodes u0 u1 S (m-d) ?_ hvalues ?_
  · intro i _
    apply local_derivative_contact (nodes i) (u0 i) (u1 i) P (m-d) d
    simpa only [Nat.sub_add_cancel (Nat.le_of_lt hdm)] using hcontact i
  · have hd := specialization_degree ((pderiv 1)^[d] P) f z w ((m-d)*a) hf (Nat.mul_pos (Nat.sub_pos_of_lt hdm) ha)
      (derivative_weight P m a w k n0 d hwa (Nat.le_of_lt hdm) hdk hP)
    exact hd.trans_le (Nat.mul_le_mul_left (m-d) hS)

end
end ProximityPrize.SubmissionLower.SecondJetRelaxedDifferentiation

end Compact_SecondJetRelaxedDifferentiation

section Compact_SecondJetRelaxedCoefficientsReceipt
/-! Exact global coefficient dimensions for the three exploratory profiles.
Local rank values and geometric use are separate obligations. -/
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedCoefficientsReceipt
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
open SecondJetRelaxedDifferentiation
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

end ProximityPrize.SubmissionLower.SecondJetRelaxedCoefficientsReceipt

end Compact_SecondJetRelaxedCoefficientsReceipt

section Compact_SecondJetRelaxedRanksReceipt
/-! Kernel-checked concrete local rank counts. The geometric use of the
resulting interpolants is a separate theorem obligation. -/
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedRanksReceipt
open SecondJetRelaxedCounts SecondJetRelaxedCoefficientsReceipt
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

end ProximityPrize.SubmissionLower.SecondJetRelaxedRanksReceipt

end Compact_SecondJetRelaxedRanksReceipt

section Compact_SecondJetRelaxedInterpolation
/-! The three concrete relaxed second-jet interpolants. Their nonzero source,
all requested derivative vanishings, and degree budgets are unconditional
consequences of the checked dimensions. Geometric counting is separate. -/
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedInterpolation
open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetSpecialize SecondJetDifferentiation
open SecondJetRelaxedCoefficientsReceipt SecondJetRelaxedDifferentiation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K N : Type*} [Field K] [Fintype N]

end
end ProximityPrize.SubmissionLower.SecondJetRelaxedInterpolation

end Compact_SecondJetRelaxedInterpolation

section Compact_SecondJetLeadingCoefficient
/-! The low-degree alternative: if higher S coefficients vanish on a codeword,
the surviving leading coefficient has enough contact to vanish as well. -/
namespace ProximityPrize.SubmissionLower.SecondJetLeadingCoefficient
open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetSpecialize
open SecondJetCoefficients SecondJetCoefficientSpecialization SecondJetDifferentiation
open SecondJetRelaxedDifferentiation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K N : Type*} [Field K]

end
end ProximityPrize.SubmissionLower.SecondJetLeadingCoefficient

end Compact_SecondJetLeadingCoefficient

section Compact_SecondJetProperAlternatives
/-! The actual proper-helper alternatives for a relaxed interpolant. If none
applies, its global S degree is large and every cleared derivative is divisible
by the carrier, precisely the hypotheses of the retained-component theorem. -/
namespace ProximityPrize.SubmissionLower.SecondJetProperAlternatives
open MvPolynomial SecondJetSupport SecondJetCoefficients SecondJetCoefficientSpecialization
open SecondJetClearedHelper SecondJetHelperWeights SecondJetRelaxedInterpolation
open SecondJetRelaxedCoefficientsReceipt RCN234 RCN156
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
variable {K N : Type*} [Field K] [Fintype N]

end
end ProximityPrize.SubmissionLower.SecondJetProperAlternatives

end Compact_SecondJetProperAlternatives

section Compact_SecondJetRounding
/-! Scale once and round only after summing all geometric components. -/
namespace ProximityPrize.SubmissionLower.SecondJetRounding
set_option autoImplicit false

end ProximityPrize.SubmissionLower.SecondJetRounding

end Compact_SecondJetRounding

section Compact_SecondJetCombinedCount
/-! The full second-jet count for a regular irreducible carrier. All geometric
cases are included; the remaining profile-specific inequalities are numeric. -/
namespace ProximityPrize.SubmissionLower.SecondJetCombinedCount
open scoped Classical
open MvPolynomial RCN135 RCN136 RCN319 RCN327 RCN238 RCN222
open SecondJetRegularData SecondJetRegularData.Data SecondJetCoefficients
open SecondJetRelaxedInterpolation SecondJetProperAlternatives SecondJetExceptionalComponents
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance  _root_.ProximityPrize.SubmissionLower.SecondJetCombinedCount.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.SecondJetCombinedCount.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I
variable {nodes : I ↪ K} {u0 u1 : I → K}

end
end ProximityPrize.SubmissionLower.SecondJetCombinedCount

end Compact_SecondJetCombinedCount

section Compact_SecondJetNumericGeometry
/-! Arithmetic interfaces for the three geometric profiles. -/
namespace ProximityPrize.SubmissionLower.SecondJetNumericGeometry
open RCN260 RCN095 RCN294
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

end ProximityPrize.SubmissionLower.SecondJetNumericGeometry

end Compact_SecondJetNumericGeometry

section Compact_SecondJetOwnShape
/-! Connecting an actual carrier's cumulative flag to its numerical cell. -/
namespace ProximityPrize.SubmissionLower.SecondJetOwnShape
open MvPolynomial RCN130 RCN234 RCN156 RCN095 RCN347 RCN135
open SecondJetRegularData SecondJetRegularData.Data LocatorHybridCells LocatorHybridCellsC1
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}

theorem factorial_ne (d : ℕ) (hd : d < 2130706433) : (d.factorial : K) ≠ 0 :=
  factorial_cast_ne_zero_below_characteristic 2130706433 d hd

theorem two_ne : (2 : K) ≠ 0 := by
  have h := factorial_ne (K := K) 2 (by decide)
  simpa only [show Nat.factorial 2 = 2 by decide,Nat.cast_ofNat] using h

end
end ProximityPrize.SubmissionLower.SecondJetOwnShape

end Compact_SecondJetOwnShape

section Compact_SecondJetUniformReceipts
/-! Common characteristic and exceptional-count receipts for all three
second-jet profiles. The maximum source caps are (47,157,2233,21). -/
namespace ProximityPrize.SubmissionLower.SecondJetUniformReceipts
open SecondJetNumericGeometry RCN260 RCN294
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

end ProximityPrize.SubmissionLower.SecondJetUniformReceipts

end Compact_SecondJetUniformReceipts

section Compact_SecondJetProperReceipts
/-! Exact nonnegative slack identities put every proper-helper branch under
its normal C2 cost. No finite enumeration or native evaluation is involved. -/
namespace ProximityPrize.SubmissionLower.SecondJetProperReceipts
open SecondJetNumericGeometry RCN260 RCN095 RCN294
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

end ProximityPrize.SubmissionLower.SecondJetProperReceipts

end Compact_SecondJetProperReceipts

section Compact_SecondJetProfileBounds
/-! Concrete second-jet bounds, with all profile arithmetic, exceptional
counts, characteristic conditions, and interpolation hypotheses discharged. -/
namespace ProximityPrize.SubmissionLower.SecondJetProfileBounds
open RCN135 SecondJetRegularData SecondJetRegularData.Data SecondJetOwnShape
open SecondJetNumericGeometry SecondJetUniformReceipts SecondJetRelaxedInterpolation
open SecondJetProperReceipts
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}
local instance  _root_.ProximityPrize.SubmissionLower.SecondJetProfileBounds.instCharPGenericFieldOfNatNat : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433

end
end ProximityPrize.SubmissionLower.SecondJetProfileBounds

end Compact_SecondJetProfileBounds

section Compact_SecondJetAffineCeiling
/-! Affine upper bounds for the rounded moving cost. They allow checking a
piecewise affine base certificate with no residue-class enumeration. -/
namespace ProximityPrize.SubmissionLower.SecondJetAffineCeiling
open RCN095
set_option autoImplicit false
set_option maxHeartbeats 2000000

end ProximityPrize.SubmissionLower.SecondJetAffineCeiling

end Compact_SecondJetAffineCeiling

section Compact_SecondJetSingleCap
/-! Affine, conservatively rounded costs for the three concrete profiles. -/
namespace ProximityPrize.SubmissionLower.SecondJetSingleCap
open RCN095 LocatorFactorAggregate SecondJetRegularData SecondJetRegularData.Data
open SecondJetOwnShape SecondJetAffineCeiling
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}

end
end ProximityPrize.SubmissionLower.SecondJetSingleCap

end Compact_SecondJetSingleCap

section Compact_SecondJetRowIntervals
/-! Interval checking for arbitrary finite piecewise-affine rows, including
activation jumps of a second-jet profile. -/
namespace ProximityPrize.SubmissionLower.SecondJetRowIntervals
open LocatorPhase6800Oracle
set_option autoImplicit false
set_option maxHeartbeats 3000000

def pickTail (z : ℕ) (a : BaseSegment) : List BaseSegment → BaseSegment
  | [] => a
  | s::ss => pickTail z (if s.start ≤ z then s else a) ss

def baseSlopeAt (q : BaseRow) (lo : ℕ) : ℕ :=
  match q.segments with
  | [] => 0
  | a::ss => (pickTail lo a ss).slope

def BaseCell (q : BaseRow) (lo hi : ℕ) : Prop :=
  lo=hi ∨ (3 ≤ lo ∧ match q.segments with
    | [] => True
    | a::ss => a.start ≤ lo ∧ ∀ s ∈ ss, s.start ≤ lo ∨ hi < s.start)
instance  _root_.ProximityPrize.SubmissionLower.SecondJetRowIntervals.instDecidableBaseCell (q : BaseRow) (lo hi : ℕ) : Decidable (BaseCell q lo hi) := by
  unfold BaseCell
  cases q.segments <;> infer_instance

theorem fold_pick (z : ℕ) (a : BaseSegment) (ss : List BaseSegment) :
    ss.foldl (fun best next => if next.start ≤ z then next else best) a = pickTail z a ss := by
  induction ss generalizing a with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.foldl_cons,pickTail]
    exact ih _

theorem pick_stable (lo hi z : ℕ) (a : BaseSegment) (ss : List BaseSegment)
    (h : ∀ s ∈ ss, s.start ≤ lo ∨ hi < s.start) (hz : lo ≤ z) (hhi : z ≤ hi) :
    pickTail z a ss = pickTail lo a ss := by
  induction ss generalizing a with
  | nil => rfl
  | cons s ss ih =>
    have hs := h s (by simp)
    have hss : ∀ s ∈ ss, s.start ≤ lo ∨ hi < s.start := fun s hs => h s (by simp [hs])
    rcases hs with hs | hs
    · simp only [pickTail,if_pos hs,if_pos (hs.trans hz)]
      exact ih _ hss
    · simp only [pickTail,if_neg (show ¬s.start ≤ z by omega),if_neg (show ¬s.start ≤ lo by omega)]
      exact ih _ hss

theorem pick_start (lo : ℕ) (a : BaseSegment) (ss : List BaseSegment) (ha : a.start ≤ lo) :
    (pickTail lo a ss).start ≤ lo := by
  induction ss generalizing a with
  | nil => exact ha
  | cons s ss ih =>
    simp only [pickTail]
    split
    · exact ih _ (by assumption)
    · exact ih _ ha

theorem segment_evalAt_shift (s : BaseSegment) (lo z : ℕ)
    (hs : s.start ≤ lo) (hz : lo ≤ z) :
    s.evalAt z = s.evalAt lo+s.slope*(z-lo) := by
  have hsplit : z-s.start = (lo-s.start)+(z-lo) := by omega
  simp only [BaseSegment.evalAt,hsplit,Nat.mul_add]
  omega

theorem baseAt_affine (q : BaseRow) (lo hi z : ℕ)
    (hcell : BaseCell q lo hi) (hlo : lo ≤ z) (hhi : z ≤ hi) :
    q.evalAt z = q.evalAt lo+baseSlopeAt q lo*(z-lo) := by
  rcases hcell with heq | ⟨hlo3,hcell⟩
  · have hz : z=lo := by omega
    subst z
    simp
  · have hz3 : 3 ≤ z := hlo3.trans hlo
    simp only [BaseRow.evalAt,if_neg (show z≠0 by omega),if_neg (show z≠1 by omega),
      if_neg (show z≠2 by omega),if_neg (show lo≠0 by omega),if_neg (show lo≠1 by omega),
      if_neg (show lo≠2 by omega)]
    cases hs : q.segments with
    | nil => simp [hs,evalBaseSegments,baseSlopeAt]
    | cons a ss =>
      rw [hs] at hcell
      simp only at hcell
      simp only [hs,evalBaseSegments,baseSlopeAt,fold_pick]
      rw [pick_stable lo hi z a ss hcell.2 hlo hhi]
      exact segment_evalAt_shift _ lo z (pick_start lo a ss hcell.1) hlo

end ProximityPrize.SubmissionLower.SecondJetRowIntervals

end Compact_SecondJetRowIntervals


