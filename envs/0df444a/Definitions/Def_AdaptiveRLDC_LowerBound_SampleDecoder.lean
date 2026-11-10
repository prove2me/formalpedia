-- Prove2me | Definitions.Def_AdaptiveRLDC_LowerBound_SampleDecoder
-- name    : AdaptiveRLDC_LowerBound_SampleDecoder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T14:56:06.667297+00:00
-- url     : https://prove2.me/theorems/ebc04454-3176-4ceb-ab81-20185f9f57bd
-- title:
--   Observable sample-based decoder and per-coordinate error
-- statement:
--   A sampled view consists of a set $W\subseteq[n]$ and a function giving exactly the bits indexed by $W$. A sample decoder is a single deterministic map from such views to a binary message. For fixed $C$, $p\in(0,1]$ and $e\in(0,1/2)$, correctness means
--   $$\forall x,i,\quad\Pr_W[A(W,C(x)|_W)_i\ne x_i]\le e.$$
--   The sampling law includes each coordinate independently with probability $p$, independently of the fixed message. No simultaneous recovery guarantee is imposed. Completing the view by zero outside $W$ is an explicit auxiliary operation and does not expose any unsampled codeword bits. Existence quantifies only over maps with this observable domain.
-- source:
--   Guy Goldberg, Tom Gur, Sidhant Saraogi, Lower Bounds for Adaptive Relaxed Locally Decodable Codes via the Capped Horvitz–Thompson Estimator, STOC 2027 submission #1071 (October 2026), Definition 5.2, printed p.27, PDF p.28; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1071.pdf; sha256 fc1b12e269801cef0033faea9f18d9873b62d5b18dbd21242a4daefc43048a5b. Title-page date November 3, 2026; submission status does not assert acceptance.

import Mathlib
import Definitions.Def_AdaptiveRLDC_LowerBound_FiniteWeights

open scoped BigOperators
noncomputable section

namespace AdaptiveRLDC.LowerBound

open Classical

/-- Definition 5.2: the input contains exactly a sampled set and its bits. -/
abbrev SampleView (n : ℕ) := Σ W : Sets n, (W → Bool)

abbrev SampleDecoder (k n : ℕ) := SampleView n → Cube k

def sampledView {n : ℕ} (c : Cube n) (W : Sets n) : SampleView n :=
  ⟨W, fun i => c i.val⟩

/-- Complete only the observed view with a fixed zero off the sample; no hidden oracle. -/
def completeView {n : ℕ} (v : SampleView n) : Cube n :=
  fun i => if h : i ∈ v.1 then v.2 ⟨i,h⟩ else false

/-- All randomness is W, sampled independently of the fixed message. Error is per bit. -/
def IsSampleDecoder {k n : ℕ} (C : Cube k → Cube n) (p ε : ℝ)
    (A : SampleDecoder k n) : Prop :=
  0 < p ∧ p ≤ 1 ∧ 0 < ε ∧ ε < 1/2 ∧
    ∀ x i, eventMass (sampleWeight p) (fun W => A (sampledView (C x) W) i ≠ x i) ≤ ε

def HasSampleDecoder {k n : ℕ} (C : Cube k → Cube n) (p ε : ℝ) : Prop :=
  ∃ A : SampleDecoder k n, IsSampleDecoder C p ε A

end AdaptiveRLDC.LowerBound


