-- Prove2me | Definitions.Def_StableVotingDistortion_scorePrimitives
-- name    : StableVotingDistortion_scorePrimitives
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:00:13.698793+00:00
-- url     : https://prove2.me/theorems/75541b6f-7db2-4cdf-a4c3-44ab27b2b095
-- title:
--   $J$, $\delta_p$, $K_p$, $\sigma$, $g_\phi$ and the potential $W_x$
-- statement:
--   For a score function $\phi$:
--   $$J(r)=\int_0^r\phi,\quad \delta_p(q)=J(1-p+q)-J(q),\quad K_p(q,z)=J(z-p+q)-J(z)-J(q),$$
--   $$\sigma(x)=\lambda-x-\phi(x),\qquad g_\phi(r)=\frac{\phi(0)-\phi(r)}{1+\phi(0)},$$
--   and the potential
--   $$W_x(z)=\begin{cases}0,&z\le\lambda,\\ \lambda-z-\dfrac{\lambda-x}{\phi(x)}\phi(z),&z>\lambda.\end{cases}$$
--
--   $\delta_p$ and $K_p$ bound the score of a block of mass $p$, $g_\phi$ is the activation function with score function $-\phi$, and $W_x$ is used for $x\in[0,\lambda)$.
--
--   **Formalization Note** Under (26), $\phi(0)>0$, and $\phi(x)>0$ for $x<\lambda$, so the divisions are by positive numbers where the mission uses them.
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Equation (23), p.21; §6.2, p.24; §6.3, p.26; Equations (34), (36), p.29; App. C.1, p.43

import Mathlib

set_option autoImplicit false

namespace StableVotingDistortion

/-- `J(r) = ∫_0^r ϕ`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.1, Equation (23), p.21; used in §6.2, p.24 and §6.3. -/
noncomputable def J (ϕ : ℝ → ℝ) (r : ℝ) : ℝ := ∫ u in (0 : ℝ)..r, ϕ u

/-- `δ_p(q) = J(1 − p + q) − J(q)`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.2, p.24; Equation (36), p.29. -/
noncomputable def deltaP (ϕ : ℝ → ℝ) (p q : ℝ) : ℝ := J ϕ (1 - p + q) - J ϕ q

/-- `K_p(q, z) = J(z − p + q) − J(z) − J(q)`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Equation (36), p.29. -/
noncomputable def KP (ϕ : ℝ → ℝ) (p q z : ℝ) : ℝ := J ϕ (z - p + q) - J ϕ z - J ϕ q

/-- `σ(x) = λ − x − ϕ(x)`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), App. C.1, p.43. -/
def sigma (lam : ℝ) (ϕ : ℝ → ℝ) (x : ℝ) : ℝ := lam - x - ϕ x

/-- `g_ϕ(r) = (ϕ(0) − ϕ(r)) / (1 + ϕ(0))`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.3, p.26.

**Formalization Note.** Under (26), `ϕ(0) > 0`, so the denominator is positive. -/
noncomputable def gPhi (ϕ : ℝ → ℝ) (r : ℝ) : ℝ := (ϕ 0 - ϕ r) / (1 + ϕ 0)

/-- The potential `W_x(z)`, which is `0` for `z ≤ λ` and `λ − z − ((λ − x)/ϕ(x)) ϕ(z)` for `z > λ`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Equation (34), p.29.

**Formalization Note.** The paper indexes `W_x` by `x ∈ [0, λ)`, where `ϕ(x) > 0` by (26). -/
noncomputable def Wx (lam : ℝ) (ϕ : ℝ → ℝ) (x z : ℝ) : ℝ :=
  if z ≤ lam then 0 else lam - z - (lam - x) / ϕ x * ϕ z

end StableVotingDistortion


