-- Prove2me | Definitions.Def_AdaptiveRLDC_LowerBound_ConstructionParameters
-- name    : AdaptiveRLDC_LowerBound_ConstructionParameters
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T14:57:21.806891+00:00
-- url     : https://prove2.me/theorems/8dc115d9-1c9e-4a90-b8f5-65c8a0c546ed
-- title:
--   Exact sampling and threshold parameters
-- statement:
--   For $\Lambda=\alpha+\beta-1>0$ and $\varepsilon>0$, define
--   $$\lambda=\alpha/\Lambda,\quad d=\lfloor(\lambda+\varepsilon)q\rfloor+1,\quad r=n^{1/d},\quad p=\min(1,Dq^2\log_2n/r).$$
--   The scale at index $j\in[d]$ is $m_j=qn^{j/d}/n$. The testing threshold is $\theta=(1-\beta+\alpha(1-q/d))/2$, and $\eta=\varepsilon\Lambda/(\lambda+\varepsilon)$. These quantities are computed from input parameters, with natural floors used only in their nonnegative source regimes. The gap inequality is a result of these definitions, not a hypothesis.
-- source:
--   Guy Goldberg, Tom Gur, Sidhant Saraogi, Lower Bounds for Adaptive Relaxed Locally Decodable Codes via the Capped Horvitz–Thompson Estimator, STOC 2027 submission #1071 (October 2026), Lemma 5.4; Construction 5.7, printed p.28, PDF p.29; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1071.pdf; sha256 fc1b12e269801cef0033faea9f18d9873b62d5b18dbd21242a4daefc43048a5b. Title-page date November 3, 2026; submission status does not assert acceptance. Exact per-concept locations: Lemma 5.4 printed p.28/PDF p.29; Construction 5.7 printed p.30/PDF p.31.

import Mathlib
import Definitions.Def_AdaptiveRLDC_LowerBound_Entropy

open scoped BigOperators
noncomputable section

namespace AdaptiveRLDC.LowerBound

open Classical

/-- The exact parameters of Lemma 5.4 and Construction 5.7. -/
def lambda (α β : ℝ) : ℝ := α / (α + β - 1)

def constructionD (ε α β : ℝ) (q : ℕ) : ℕ := ⌊(lambda α β + ε) * (q : ℝ)⌋₊ + 1

def spreadRate (n d : ℕ) : ℝ := (n : ℝ) ^ (1 / (d : ℝ))

def samplingRate (D ε α β : ℝ) (n q : ℕ) : ℝ :=
  min 1 (D * (q : ℝ)^2 * logTwo n / spreadRate n (constructionD ε α β q))

def scaleMass (n q d j : ℕ) : ℝ := (q : ℝ) * (n : ℝ) ^ ((j : ℝ) / (d : ℝ)) / (n : ℝ)

def threshold (α β : ℝ) (q d : ℕ) : ℝ := (1 - β + α * (1 - (q : ℝ)/(d : ℝ))) / 2

def gap (ε α β : ℝ) : ℝ := ε * (α + β - 1) / (lambda α β + ε)

end AdaptiveRLDC.LowerBound


