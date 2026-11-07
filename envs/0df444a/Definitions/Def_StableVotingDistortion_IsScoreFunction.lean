-- Prove2me | Definitions.Def_StableVotingDistortion_IsScoreFunction
-- name    : StableVotingDistortion_IsScoreFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T01:59:58.464832+00:00
-- url     : https://prove2.me/theorems/2e3d4ca9-7b9c-4bd4-b29b-62234aa9f9ec
-- title:
--   The score-function conditions (26)
-- statement:
--   Fix $\lambda\in(0,1)$. The function $\phi:[0,1]\to\mathbb R$ satisfies **(26)** if
--
--   1. $\phi$ is continuous and nonincreasing;
--   2. $\int_0^1\phi=0$ and $\phi(1)=-1$;
--   3. $\phi>0$ on $[0,\lambda)$;
--   4. $\phi(r)\le\lambda-r$ on $[0,1]$.
--
--   These are the standing assumptions of §6.3 on the score function, whose negative $-\phi$ is the score of a rank.
--
--   **Formalization Note** $\phi$ is a function on $\mathbb R$ constrained only on $[0,1]$. The condition $\lambda\in(0,1)$ is the first field.
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.3, Equation (26), p.26

import Mathlib

set_option autoImplicit false

namespace StableVotingDistortion

/-- The standing assumptions of §6.3: `λ ∈ (0, 1)` and the conditions (26) on `ϕ : [0, 1] → ℝ`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.3, Equation (26), p.26: "Throughout this section, fix λ ∈ (0, 1) and let ϕ : [0, 1] → R be a
function satisfying the basic score-function properties from Section 6.1, normalized so that
ϕ(1) = −1: ϕ is continuous and nonincreasing, ∫_0^1 ϕ = 0, ϕ(1) = −1, ϕ > 0 on [0, λ),
ϕ(r) ≤ λ − r on [0, 1]. (26)"

**Formalization Note.** `ϕ` is a function `ℝ → ℝ`, constrained only on `[0, 1]`. -/
structure IsScoreFunction (lam : ℝ) (ϕ : ℝ → ℝ) : Prop where
  /-- `λ ∈ (0, 1)`. -/
  lam_mem : lam ∈ Set.Ioo (0 : ℝ) 1
  /-- `ϕ` is continuous on `[0, 1]`. -/
  continuousOn : ContinuousOn ϕ (Set.Icc 0 1)
  /-- `ϕ` is nonincreasing on `[0, 1]`. -/
  antitoneOn : AntitoneOn ϕ (Set.Icc 0 1)
  /-- `∫_0^1 ϕ = 0`. -/
  integral_eq_zero : ∫ r in (0 : ℝ)..1, ϕ r = 0
  /-- `ϕ(1) = −1`. -/
  at_one : ϕ 1 = -1
  /-- `ϕ > 0` on `[0, λ)`. -/
  pos : ∀ r ∈ Set.Ico 0 lam, 0 < ϕ r
  /-- `ϕ(r) ≤ λ − r` on `[0, 1]`. -/
  le_lam_sub : ∀ r ∈ Set.Icc (0 : ℝ) 1, ϕ r ≤ lam - r

end StableVotingDistortion


