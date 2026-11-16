-- Prove2me | Definitions.Def_CNFLearning873_Valiant_Supplement_OracleParameters
-- name    : CNFLearning873_Valiant_Supplement_OracleParameters
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:38:24.917319+00:00
-- url     : https://prove2.me/theorems/8640fa88-d39c-4665-8588-b7cfae3ddd28
-- title:
--   Parameters and scales for the oracle learner
-- statement:
--   All displayed logarithms here are base two. For the algorithm of pp.27–30, set
--
--   $$r=\frac n{(\log_2 n)^2},\qquad\ell=\left\lceil100kdn\log_2\frac n{\varepsilon\delta}\right\rceil,\qquad T=\left\lceil10^6k^2d\frac n\varepsilon\log_2^4\frac n{\varepsilon\delta}\right\rceil.$$
--
--   There are at most $Q=100n\ell^2+n\ell$ integer draws; use rejection limit $L=\lceil\log_2(3Q/\delta)\rceil$. Explicit numerical scales represent the sample, oracle-call, query-size and time conclusions; a polynomial envelope is $(1+n+1/\varepsilon+\log_2(1/\delta))^p$. The good-sample event says every Valiant survivor has violation probability at most $\varepsilon/(1000\ell(\log_2 n)^2)$. No asymptotic bound is assumed by any definition. The theorem domains have $n\ge3$, positive accuracy and confidence parameters below one.
-- source:
--   Weiming Feng, Yixiao Yu, Yiyao Zhang, STOC 2027 submission #873 (October 2026), Theorem 6.5, Complexity paragraph, and Lemma 6.7, printed pp.27–30 = 1-based PDF pp.27–30; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/873.pdf

import Definitions.Def_CNFLearning873_Valiant_Learner

noncomputable section

namespace CNFLearning873.Valiant.Supplement

/-- All logarithms in the algorithm's displayed parameters are base two. -/
def radius (n : ℕ) : ℝ := n / log₂ n ^ 2

def rounds (n k d : ℕ) (ε δ : ℝ) : ℕ :=
  Nat.ceil (100 * (k : ℝ) * d * n * log₂ ((n : ℝ) / (ε * δ)))

def learningSamples (n k d : ℕ) (ε δ : ℝ) : ℕ :=
  Nat.ceil (10 ^ 6 * (k : ℝ) ^ 2 * d * (n / ε) * log₂ ((n : ℝ) / (ε * δ)) ^ 4)

def drawsBound (n ℓ : ℕ) : ℕ := 100 * n * ℓ ^ 2 + n * ℓ

def rejectionLimit (n ℓ : ℕ) (δ : ℝ) : ℕ :=
  Nat.ceil (log₂ (3 * (drawsBound n ℓ : ℝ) / δ))

/-- Explicit polynomial envelope; its degree and coefficient are quantified in the theorems. -/
def polynomialScale (n : ℕ) (ε δ : ℝ) (p : ℕ) : ℝ :=
  (1 + (n : ℝ) + 1 / ε + log₂ (1 / δ)) ^ p

def sampleScale65 (n : ℕ) (ε δ : ℝ) : ℝ :=
  (n : ℝ) / ε * log₂ ((n : ℝ) / (ε * δ)) ^ 4

def oracleExponent (n : ℕ) : ℝ := (n : ℝ) / log₂ n

def timeExponent (n : ℕ) : ℝ :=
  (n : ℝ) * log₂ (log₂ n) / Real.sqrt (log₂ n)

def queryScale (n k : ℕ) (ε δ : ℝ) : ℝ :=
  (n : ℝ) ^ k + n * log₂ ((n : ℝ) / (ε * δ))

/-- The good-learning-sample event of Lemma 6.7. -/
def GoodSamples {n T : ℕ} (F : CNF n) (h : (solutions F).Nonempty)
    (k ℓ : ℕ) (ε : ℝ) (xs : Fin T → Assignment n) : Prop :=
  ∀ c ∈ output k xs, q F h c ≤ ε / (1000 * (ℓ : ℝ) * log₂ n ^ 2)

end CNFLearning873.Valiant.Supplement


