-- Prove2me | Definitions.Def_Yukon_7bbabdcd59dd969674982fa1
-- name    : Yukon_7bbabdcd59dd969674982fa1
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T05:26:24.501802+00:00
-- url     : https://prove2.me/theorems/850882ab-1b1a-459c-9aad-07ed14839dae
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberOrdinaryLow6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberOrdinaryLow6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberOrdinaryLow6814.lean
--
--   yukon-proof-operation:foundation-direct-6c5a848635b0a2f27114ad33ed68837488b8aec26f79881f91770074e31bd0e4
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMzZiZjYwNDFkZjEzMDdmNDg2OWE3MTk4OTY0M2I3ZTQ2YWFiNGY2OTQwOTNkNWQ3MmExNGFjMjI3NjRmMjhkYSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTZjNWE4NDg2MzViMGEyZjI3MTE0YWQzM2VkNjg4Mzc0ODhiOGFlYzI2Zjc5ODgxZjkxNzcwMDc0ZTMxYmQwZTQiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl83YmJhYmRjZDU5ZGQ5Njk2NzQ5ODJmYTEiLCJ2IjoyfQ]

import Definitions.Def_Yukon_82ec8558eda6e86dee0d6566

















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.MovingFiberOrdinaryLow6814
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN135 RCN136 RCN174 RCN159 RCN086 RCN095 RCN275 RCN198 RCN263 RCN149 RCN087 RCN203 RCN084 RCN313 RCN074 RCN335
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
def n:ℕ:=262144
def w:ℕ:=131071
def errors:ℕ:=80889
def agreements:ℕ:=181255
def gap:ℕ:=50184
def prime:ℕ:=2130706433
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
local instance _root_.ProximityPrize.SubmissionLower.MovingFiberOrdinaryLow6814.instDecidableEqK :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.MovingFiberOrdinaryLow6814.instDecidableEqI :DecidableEq I:=Classical.decEq I
local instance _root_.ProximityPrize.SubmissionLower.MovingFiberOrdinaryLow6814.instDecidableEqGenericFieldK :DecidableEq (GenericField K):=Classical.decEq _
local instance _root_.ProximityPrize.SubmissionLower.MovingFiberOrdinaryLow6814.instCharPKPrime :CharP K prime:=by
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
theorem tangent_gate (a b s:ℕ) :
    errors + 1 ≤ (secondTail a b s).yz:=by
  rw [secondTail,tail_support_formula]
  change errors + 1 ≤ 1 + 2 * (b + 1) * (w + 2)
  have hb:2 * (w + 2) ≤ 2 * (b + 1) * (w + 2):=by
    have h:=Nat.mul_le_mul_right (w + 2)
      (Nat.mul_le_mul_left 2 (show 1 ≤ b + 1 by omega))
    simpa only [Nat.mul_one] using h
  exact (by norm_num [errors,w]:errors + 1 ≤ 1 + 2 * (w + 2)).trans
    (Nat.add_le_add_left hb 1)
theorem flag_characteristic (a b s:ℕ) (flag:FlagDegree)
    (hS:s + 2 ≤ 32) (hY:b + s + 3 ≤ 149) (hT:a + b + s + 3 ≤ 8121)
    (hflag:flag.all ≤ s + 2 ∧ flag.yz + flag.all ≤ b + s + 3 ∧
      flag.zOnly + flag.yz + flag.all ≤ a + b + s + 3) :
    flag.yz + flag.all < prime ∧ flag.all < prime ∧
      flag.zOnly + flag.yz + flag.all < prime:=by
  dsimp [prime]
  omega
def FixedStageBound (D a b s:ℕ):Prop:=
  ∀ {Gamma:Finset K} {flag:FlagDegree},
    (S:ResidualStage (polynomialEmbedding K) Gamma IRSProfile.domain
      prime errors flag w (RCN198.support a b s)) →
    S.nodes.card=agreements + errors →
    (∀ gamma ∈ Gamma,agreements ≤ (S.agreementFiber gamma).card) →
    S.F ∈ RCN174.globalCoefficientBox K D w (a + b + s + 3) (s + 2) →
    (flag.all ≤ s + 2 ∧ flag.yz + flag.all ≤ b + s + 3 ∧
      flag.zOnly + flag.yz + flag.all ≤ a + b + s + 3) →
    Gamma.card ≤ flagMixed flag (firstTail a b s) (secondTail a b s)
theorem fixedStageBound (D a b s:ℕ)
    (hDlow:w + 1 ≤ D) (hDhigh:D < prime)
    (hS:s + 2 ≤ 32) (hY:b + s + 3 ≤ 149) (hT:a + b + s + 3 ≤ 8121)
    (hlow : s = 0 ∨ b = 0) :
    FixedStageBound D a b s:=by
  intro Gamma flag S hnodes hagreement hbox hflag
  have hDchar:D < prime:=hDhigh
  have hflagChar:=flag_characteristic a b s flag hS hY hT hflag
  by_cases hTail:S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1)
  · have hTailNumerator:S.G ∣ surfaceMap (polynomialEmbedding K)
        (numerator K S.F (w + 1)) :=
      (globalTailCut_dvd_iff (polynomialEmbedding K)
        (polynomialEmbedding_injective K) S.F (w + 1) S.G).mp hTail
    have hprovider:=RCN146.actual_identityCurveCountProvider S agreements hnodes
      hagreement (by norm_num [agreements,w]) hTailNumerator
      D (a + b + s + 3) (s + 2)
      (by norm_num [w]) hDlow hDchar hbox hflagChar
      (MovingFiberPaddedIdentity6814.low_identity_mixed_gate b s flag hS hY hlow hflag.1 hflag.2.1)
    have hpositive:1 ≤ ProximityPrize.SubmissionLower.RCN146.identityCurveDegree flag a b s w:=by
      apply Lower80788.FixedStage.identity_positive
      have hy:0 < S.G.degreeOf 1:=S.y_dependent
      have hdeg:=degreeOf_le_flag_total S.G flag S.flag_support 1
      omega
    have hinc:=identity_surface_seed_bound S agreements
      (ProximityPrize.SubmissionLower.RCN146.identityCurveDegree flag a b s w) hprovider hagreement
      (by norm_num [agreements,w])
      (by rw [hnodes] <;> norm_num [agreements,errors]) hpositive
    have hscaled:Gamma.card * gap ≤
        gap * flagMixed flag (firstTail a b s) (secondTail a b s):=by
      calc
        Gamma.card * gap=Gamma.card * (agreements - w):=rfl
        _ ≤ (S.nodes.card - w) * (errors + 1) *
            ProximityPrize.SubmissionLower.RCN146.identityCurveDegree flag a b s w:=hinc
        _= (n - w) * (errors + 1) * ProximityPrize.SubmissionLower.RCN146.identityCurveDegree flag a b s w:=by
          rw [hnodes] <;> norm_num [n,agreements,errors]
        _ ≤ gap * flagMixed flag (firstTail a b s) (secondTail a b s) :=
          MovingFiberPaddedIdentity6814.identity_absorption flag a b s
    apply Nat.le_of_mul_le_mul_right ?_ (by norm_num [gap]:0 < gap)
    simpa only [Nat.mul_comm] using hscaled
  · have hprovider:=exists_delayedTailMultiplicityProvider_of_reducedGeneral
      (stageErrorCap:=errors) agreements S hTail hflagChar
      (MovingFiberPaddedIdentity6814.low_provider_mixed_gate b s flag hS hY hlow hflag.1 hflag.2.1)
      D (a + b + s + 3) (s + 2) hnodes hagreement
      (by norm_num [RCN327.w,agreements])
      (by simpa only [RCN327.w,w] using hDlow)
      hDchar hbox (tangent_gate a b s)
    exact stage_card_le_flagMixed S hprovider.some
end

end ProximityPrize.SubmissionLower.MovingFiberOrdinaryLow6814


