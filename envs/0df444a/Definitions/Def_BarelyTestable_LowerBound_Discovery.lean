-- Prove2me | Definitions.Def_BarelyTestable_LowerBound_Discovery
-- name    : BarelyTestable_LowerBound_Discovery
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:22:49.993299+00:00
-- url     : https://prove2.me/theorems/87c15377-f2e6-4c5a-8fdd-983ccbc1a21c
-- title:
--   Center discovery and acceptance under the hard distributions
-- statement:
--   A transcript discovers a center if it contains a slice-$01$ query $(X',Y,01)$ and a slice-$11$ query $(X,Y',11)$ with
--
--   $$\alpha(X)=\beta(Y).$$
--
--   The query order and the unused halves $X',Y'$ are unrestricted. Discovery probability is the finite product probability of this event in the actual run. Acceptance probability is the probability that some finite run returns accept. The same labels and table are fixed throughout each run, including repeated queries. These quantities use the operational history-based procedure, not an independently chosen function of the oracle.
-- source:
--   Diptaksho Palit, Yuichi Yoshida, STOC 2027 submission #722 (October 2026), §3.3, center discovery before Lemma 3.19, p. 25–26 (printed = PDF page); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/722.pdf; PDF SHA256 a095e6ef801edf5b0ce3967efca977e04b7a0b4374e874116509d73837bd14f3

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Construction
import Definitions.Def_BarelyTestable_LowerBound_Protocol

set_option autoImplicit false

namespace BarelyTestable.LowerBound

/-- The 01 query supplies Y; the 11 query supplies X. Their other halves need not coincide. -/
def Discovers {m : ℕ} (φA φB : LabelMap m) (h : History (Coord m)) : Prop :=
  ∃ p ∈ h, ∃ p' ∈ h,
    actionA ∉ p.1 ∧ actionB ∈ p.1 ∧ actionA ∈ p'.1 ∧ actionB ∈ p'.1 ∧
      Center φA φB (xPart p'.1) (yPart p.1)

noncomputable def discoveryProbability {m : ℕ} (A : Procedure (Coord m)) (q : ℕ) (sign : Bool) : ℝ :=
  uniformProb (fun r : Sample m => Discovers r.1 r.2.1 (run A (hard r sign) q []).1)

noncomputable def acceptanceProbability {m : ℕ} (A : Procedure (Coord m)) (sign : Bool) : ℝ :=
  uniformProb (fun r : Sample m => Accepts A (hard r sign))

end BarelyTestable.LowerBound


