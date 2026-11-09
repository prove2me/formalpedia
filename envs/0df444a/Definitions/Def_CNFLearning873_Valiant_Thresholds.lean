-- Prove2me | Definitions.Def_CNFLearning873_Valiant_Thresholds
-- name    : CNFLearning873_Valiant_Thresholds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T05:06:10.437636+00:00
-- url     : https://prove2.me/theorems/07feef7b-53ce-45c3-b327-2000aadc590c
-- title:
--   Local lemma condition and computed rarity and sample thresholds
-- statement:
--   Let $k,d,n$ be natural numbers, $t\ge1$, $0<\varepsilon,\delta<1$, and $r=\lceil t\rceil$. Write $\log_2$ for the base-two logarithm. Define the source condition (2) and the quantities in (4):
--
--   $$k\ge(1+1/t)\log_2d+2\log_2k+t-3\log_2t+5,$$
--   $$A=d^r(2k)^{k(1+r)}n^r/\varepsilon,\quad M=\lceil8^k\ln A\rceil,$$
--   $$\lambda=\frac{\varepsilon}{2t d^r(2k)^{k(1+r)}n^r M^k},\qquad\tau=\lambda/(4M).$$
--
--   For $n\ge k$, the deterministic sample choice is the maximum of one and the ceiling of $\tau^{-1}(k\ln(2n)+\ln(1/\delta))$. For $n<k$ it is zero, and the candidate and rare families are empty. The growth scale is $n^r\varepsilon^{-1}(\ln(n/\varepsilon))^{k+1}\ln(n/\delta)$. No probability estimate or resource bound is a field of these definitions.
-- source:
--   Weiming Feng, Yixiao Yu, Yiyao Zhang, STOC 2027 submission #873 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/873.pdf, Theorem 4.1, (2), p.12; (4), p.13; proof p.14 (PDF pp.12–14)

import Definitions.Def_CNFLearning873_Valiant_SolutionLaw

namespace CNFLearning873.Valiant

noncomputable def log₂ (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- Equation (2), p.12 = PDF p.12; all logarithms here are base two. -/
def LLLCondition (k d : ℕ) (t : ℝ) : Prop :=
  (1 + 1 / t) * log₂ d + 2 * log₂ k + t - 3 * log₂ t + 5 ≤ (k : ℝ)

noncomputable def r (t : ℝ) : ℕ := Nat.ceil t

/-- Equation (4), p.13 = PDF p.13. The ceiling encloses 8^k ln A. -/
noncomputable def parameterA (n k d : ℕ) (t ε : ℝ) : ℝ :=
  (d : ℝ) ^ r t * (2 * (k : ℝ)) ^ (k * (1 + r t)) * (n : ℝ) ^ r t / ε

noncomputable def parameterM (n k d : ℕ) (t ε : ℝ) : ℕ :=
  Nat.ceil ((8 : ℝ) ^ k * Real.log (parameterA n k d t ε))

noncomputable def parameterLambda (n k d : ℕ) (t ε : ℝ) : ℝ :=
  ε / (2 * t * (d : ℝ) ^ r t * (2 * (k : ℝ)) ^ (k * (1 + r t)) *
    (n : ℝ) ^ r t * (parameterM n k d t ε : ℝ) ^ k)

noncomputable def parameterTau (n k d : ℕ) (t ε : ℝ) : ℝ :=
  parameterLambda n k d t ε / (4 * (parameterM n k d t ε : ℝ))

noncomputable def rare {n : ℕ} (F : CNF n) (h : (solutions F).Nonempty)
    (k d : ℕ) (t ε : ℝ) : CNF n := by
  classical
  exact if n < k then ∅ else
    (candidates n k).filter fun c => q F h c < parameterTau n k d t ε

noncomputable def sampleThreshold (n k d : ℕ) (t ε δ : ℝ) : ℝ :=
  (parameterTau n k d t ε)⁻¹ * ((k : ℝ) * Real.log (2 * (n : ℝ)) + Real.log (1 / δ))

/-- The n<k branch never evaluates a logarithm or divides by n. -/
noncomputable def chosenSamples (n k d : ℕ) (t ε δ : ℝ) : ℕ :=
  if n < k then 0 else max 1 (Nat.ceil (sampleThreshold n k d t ε δ))

noncomputable def sampleScale (n k : ℕ) (t ε δ : ℝ) : ℝ :=
  (n : ℝ) ^ r t / ε * Real.log ((n : ℝ) / ε) ^ (k + 1) * Real.log ((n : ℝ) / δ)

end CNFLearning873.Valiant


