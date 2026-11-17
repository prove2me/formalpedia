-- Prove2me | Definitions.Def_IntroDelayAMDP_Supplement_LinParams
-- name    : IntroDelayAMDP_Supplement_LinParams
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:49:11.381179+00:00
-- url     : https://prove2.me/theorems/935d39e3-2d46-4314-95fb-69e84ab5f476
-- title:
--   Parameter record of Algorithms 3 and 5
-- statement:
--   The inputs $\lambda,m_0,\nu,\eta,\theta$ of Algorithms 3 and 5: the regularization $\lambda$ of the regions, the level $m_0$ in the truncation levels $M_j=\lceil m_0/\hat p_j\rceil$, the cap $\nu$ on the unfinished estimates per layer, the learning rate $\eta$, and the probability threshold $\theta$. Their values are given by `linParams`.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Algorithm 3, p.19; Algorithm 5, p.59

import Mathlib

namespace IntroDelayAMDP.Supplement

/-- **The parameter record of Algorithms 3 and 5** (Algorithm 3, "Input: Parameters `λ, m₀, ν, η, θ`",
printed p.19, PDF p.21; Algorithm 5, printed p.59, PDF p.61, of
Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)). Their values are fixed by
`linParams` (App. B.1). -/
structure LinParams where
  /-- the regularization `λ` -/
  lam : ℝ
  /-- `m₀` (truncation levels `M_j = ⌈m₀/p̂_j⌉`) -/
  m0 : ℕ
  /-- the cap `ν` on the unfinished estimates of a layer -/
  nu : ℕ
  /-- the learning rate `η` -/
  eta : ℝ
  /-- the probability threshold `θ` -/
  theta : ℝ

end IntroDelayAMDP.Supplement


