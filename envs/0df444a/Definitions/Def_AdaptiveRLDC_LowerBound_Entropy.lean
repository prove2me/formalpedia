-- Prove2me | Definitions.Def_AdaptiveRLDC_LowerBound_Entropy
-- name    : AdaptiveRLDC_LowerBound_Entropy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T14:56:04.494976+00:00
-- url     : https://prove2.me/theorems/ffb77a5a-54d1-400a-8864-27a88d09e5a0
-- title:
--   Base-two finite entropy interface
-- statement:
--   Logarithms in the source are base two. The shared finite-weight Shannon and conditional entropy definitions are reused and converted from nats to bits by division by $\ln2$:
--   $$H_2(\mu)=H_{\rm nat}(\mu)/\ln2,\qquad H_2(A\mid B)=H_{\rm nat}(A\mid B)/\ln2.$$
--   The conditional quantity is computed from an actual joint law, with the chain-rule representation equivalent to the source average of conditional entropies. Binary entropy itself is the published exact function $h_2(t)=-t\log_2t-(1-t)\log_2(1-t)$. Zero weights contribute zero. These are transparent units conversions, with no additional regularity hypotheses.
-- source:
--   Guy Goldberg, Tom Gur, Sidhant Saraogi, Lower Bounds for Adaptive Relaxed Locally Decodable Codes via the Capped Horvitz–Thompson Estimator, STOC 2027 submission #1071 (October 2026), Definitions 3.3–3.5, printed p.14, PDF p.15; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1071.pdf; sha256 fc1b12e269801cef0033faea9f18d9873b62d5b18dbd21242a4daefc43048a5b. Title-page date November 3, 2026; submission status does not assert acceptance.

import Mathlib
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_AdaptiveRLDC_LowerBound_FiniteWeights

open scoped BigOperators
noncomputable section

namespace AdaptiveRLDC.LowerBound

open Classical

/-- Definitions 3.3–3.5: source logarithms are base two, with 0 log 0=0. -/
def logTwo (t : ℝ) : ℝ := Real.log t / Real.log 2

/-- Convert the published general finite-weight Shannon entropy from nats to bits. -/
def entropy {A : Type} [Fintype A] (μ : A → ℝ) : ℝ :=
  OAI.EntropyRateDimension.FiniteEntropy.entropy Finset.univ μ / Real.log 2

/-- Convert the published joint-law conditional entropy from nats to bits. -/
def conditionalEntropy {A B : Type} [Fintype A] [Fintype B] (joint : A × B → ℝ) : ℝ :=
  OAI.EntropyRateDimension.FiniteEntropy.conditionalEntropy Finset.univ joint
    Prod.fst Prod.snd / Real.log 2

end AdaptiveRLDC.LowerBound


