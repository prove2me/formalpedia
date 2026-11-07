-- Prove2me | Definitions.Def_IntroDelayAMDP_AlgParams
-- name    : IntroDelayAMDP_AlgParams
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:43:59.76421+00:00
-- url     : https://prove2.me/theorems/fd3be660-b944-4829-8513-a060a001e268
-- title:
--   Parameter record of Algorithm 1
-- statement:
--   The record of the reals $\iota,\nu,c_1,\eta,\gamma,\theta,\beta$ and the natural number $M$ that Algorithm 1 takes as input. Their values are fixed by the parameter choice of App. A.1.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Algorithm 1, p.16; App. A.1, p.30

import Mathlib

namespace IntroDelayAMDP

/-- **The parameter record of Algorithm 1** (App. A.1, printed p.30). Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), printed p.30: the
reals `ι, ν, c₁, η, γ, θ, β` and the natural number `M` that Algorithm 1 takes as input
("Input: Confidence parameter δ; parameters η, γ, θ, M, ν, c1", Algorithm 1, p.16). Their values
are fixed by `tabParams`. -/
structure AlgParams where
  /-- `ι = 2 log(CSAHK/δ)` -/
  iota : ℝ
  /-- the cap `ν` on the unfinished estimates of a pair -/
  nu : ℝ
  /-- the bonus constant `c₁` -/
  c1 : ℝ
  /-- the learning rate `η` -/
  eta : ℝ
  /-- the random-stop probability `γ` -/
  gamma : ℝ
  /-- the threshold `θ` -/
  theta : ℝ
  /-- the cap `M` on the attempts of an estimate -/
  M : ℕ
  /-- the confidence level `β = log(16S²AK/δ)` of Eq. (16) -/
  beta : ℝ

end IntroDelayAMDP


