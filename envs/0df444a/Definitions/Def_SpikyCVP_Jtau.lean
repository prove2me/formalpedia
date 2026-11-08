-- Prove2me | Definitions.Def_SpikyCVP_Jtau
-- name    : SpikyCVP_Jtau
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:38:12.02992+00:00
-- url     : https://prove2.me/theorems/87c47540-401a-443c-b488-03e79f5f2208
-- title:
--   The function $J_\tau(a,b)$
-- statement:
--   For $0<\tau\le 1/2$, $1<p<2$ and $a,b\in\mathbb R$,
--
--   $$J_\tau(a,b)=\big((1-\tau)a^2+\tau b^2\big)^{p/2}-(1-\tau)|a|^p-\tau|b|^p .$$
--
--   It measures how far the $p$-th power of a weighted quadratic mean exceeds the weighted mean of $p$-th powers. It appears in the overlap bound for two posteriors (Lemma 4.4), where the exponent of the overlap integral is $-\sum_j J_\tau(\cdot,\cdot)/r^p$.
--
--   **Formalization Note** For $0\le\tau\le1$ the base is nonnegative, so the real power is the usual one.
-- source:
--   Aggarwal, Morolia, How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector Problem, STOC 2027 submission (manuscript sha256 535c3bcc…), Lemma 2.2, p.11 (PDF p.13); proof of Lemma 4.4, p.21 (PDF p.23)

import Mathlib

namespace SpikyCVP

/-- `Jτ(a, b) := ((1 − τ)a² + τb²)^{p/2} − (1 − τ)|a|^p − τ|b|^p`. Aggarwal, Morolia, *How to Round Spiky
Balls into Submission; And Faster Algorithms For The Closest Vector Problem*, STOC 2027 submission
(manuscript sha256 535c3bcc…), Lemma 2.2, p.11 (PDF p.13), used again in the proof of Lemma 4.4, p.21.

**Formalization Note.** For `0 ≤ τ ≤ 1` the base `(1 − τ)a² + τb²` is nonnegative, so `Real.rpow` is the
usual power. -/
noncomputable def Jtau (τ p a b : ℝ) : ℝ :=
  ((1 - τ) * a ^ 2 + τ * b ^ 2) ^ (p / 2) - (1 - τ) * |a| ^ p - τ * |b| ^ p

end SpikyCVP


