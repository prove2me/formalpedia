-- Prove2me | Definitions.Def_BalkemaDeHaan_FiniteT_Pi0
-- name    : BalkemaDeHaan_FiniteT_Pi0
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:05:30.137259+00:00
-- url     : https://prove2.me/theorems/60d46679-a338-45ba-b6b6-7812d8434168
-- title:
--   Π_{0,c} for every real c, and the auxiliary function σ(u) = ∫₀¹∫₀ᵗ e^{−us} ds dt
-- statement:
--   For a real parameter $c$, the distribution function $\Pi_{0,c}$ on $\mathbb R$ is
--   $$
--   \Pi_{0,c}(x) =
--   \begin{cases}
--   0, & x < 0,\\
--   1 - e^{-x}, & x \ge 0,\ c = 0,\\
--   1 - (1 + cx)^{-1/c}, & x \ge 0,\ c > 0,\\
--   1 - (1 + cx)^{-1/c}, & 0 \le x \le |c|^{-1},\ c < 0,\\
--   1, & x > |c|^{-1},\ c < 0.
--   \end{cases}
--   $$
--   For $c > 0$ this is $\Gamma_{c^{-1}}(cx)$ with $\Gamma_\alpha(y) = 1 - (1+y)^{-\alpha}$ (a generalized Pareto law), for $c = 0$ it is the standard exponential law $\Pi$, and for $c < 0$ it is a law with bounded support $[0, |c|^{-1}]$.
--
--   The second object is the auxiliary function of the proof of Lemma 4,
--   $$
--   \sigma(u) = \int_0^1 \int_0^t e^{-us}\, ds\, dt, \qquad u \in \mathbb R,
--   $$
--   which equals $u^{-2}(e^{-u} - 1 + u)$ for $u \ne 0$ and $1/2$ at $u = 0$.
--
--   The family $(\Pi_{0,c})_{c \in \mathbb R}$ is the set of comparison laws in the paper's finite-$t$ approximation theorem (Theorem 7) and its Corollary.
--
--   **Formalization Note** The paper (p. 801) gives the formula for $c < 0$ only on $0 \le x \le |c|^{-1}$; the value $1$ for $x > |c|^{-1}$ is the completion forced by "distribution function" and used in the proof of Lemma 4 ("$\Pi_{0,c}(x)$ is constant on both components of $\{c > -1\}\setminus R$"). At $x = |c|^{-1}$ the formula already gives $1$, so the completion is continuous. The case $c = 0$ is a separate branch (the formula with $1/0 = 0$ would be junk). The power is `Real.rpow` with a nonnegative base on every branch where it is used. `sigma` is defined by the double interval integral; its closed form is a theorem of the mission.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 793 (PDF 2), Π_{0,c} = Γ_{c^{-1}}(cx), Π_{0,0} = Π; p. 801 (PDF 10), Π_{0,c} for c < 0; p. 803 (PDF 12), σ in the proof of Lemma 4

import Mathlib

namespace BalkemaDeHaan.FiniteT

/-- The limit distribution functions `Π_{0,c}` of Balkema–de Haan (1974), for every real `c`.
For `c > 0` (p. 793): `Π_{0,c}(x) = Γ_{c⁻¹}(c x) = 1 - (1 + c x)^{-1/c}` for `x ≥ 0`;
for `c = 0` (p. 793): `Π_{0,0}(x) = Π(x) = 1 - e^{-x}` for `x ≥ 0`;
for `c < 0` (p. 801): `Π_{0,c}(x) = 1 - (1 + c x)^{-1/c}` for `0 ≤ x ≤ |c|⁻¹`, and (completion,
not printed) `Π_{0,c}(x) = 1` for `x > |c|⁻¹`.
All of them vanish for `x < 0` (p. 793). -/
noncomputable def pi0 (c x : ℝ) : ℝ :=
  if x < 0 then 0
  else if c = 0 then 1 - Real.exp (-x)
  else if 0 < c then 1 - (1 + c * x) ^ (-1 / c)
  else if x ≤ |c|⁻¹ then 1 - (1 + c * x) ^ (-1 / c)
  else 1

/-- The auxiliary function of the proof of Lemma 4 (p. 803):
`σ(u) = ∫₀¹ ∫₀ᵗ e^{-u s} ds dt`, which equals `u⁻²(e^{-u} - 1 + u)` for `u ≠ 0`. -/
noncomputable def sigma (u : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..t, Real.exp (-(u * s))

end BalkemaDeHaan.FiniteT


