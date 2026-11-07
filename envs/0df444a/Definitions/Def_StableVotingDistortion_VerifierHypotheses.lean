-- Prove2me | Definitions.Def_StableVotingDistortion_VerifierHypotheses
-- name    : StableVotingDistortion_VerifierHypotheses
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:01:30.724742+00:00
-- url     : https://prove2.me/theorems/c1758b76-4f49-42a1-ba3a-b453a1262a5b
-- title:
--   Conditions (25), (37), (38) and the hypotheses of the Verifier Lemma
-- statement:
--   For a mass $p$: **(25)** is $p[J(1-p+q)-J(q)]\le(\lambda-q)J(p)$ for $0\le q\le\min\{p,\lambda\}$.
--
--   **(37)** is, for every $x\in[0,\lambda)$,
--   $$q+\beta(p)\delta_p(q)+c(p,x)\le\lambda\quad(0\le q\le\min\{p,x\}),\qquad q+\beta(p)K_p(q,x)+c(p,x)\le0\quad(0\le q\le p\le x).$$
--
--   **(38)** is, for every $x\in[0,\lambda)$,
--   $$\phi(x)[q+\beta(p)\delta_p(q)+W_x(q)-\lambda]\le(-\phi(q))_+c(p,x)\quad(0\le q\le p),$$
--   $$\phi(x)[q+\beta(p)K_p(q,z)+W_x(q)-W_x(z)]\le(-\phi(z))_+c(p,x)\quad(0\le q\le p\le z\le1).$$
--
--   The **hypotheses of the Verifier Lemma** on $(\lambda,\phi,\beta,c)$ are: $\lambda\in(0,1)$ and (26); $\phi(r)+r$ nonincreasing on $[\lambda,1]$; $\beta\ge0$ on $(0,1)$; $c\ge0$ on $(0,1)\times[0,\lambda)$; and (37), (38) for every $p\in(0,1)$. They refer to no election.
--
--   **Formalization Note** No measurability or continuity of $\beta$ or $c$ is assumed, as on the page; both are total functions constrained only on their printed domains. $(y)_+$ is `max y 0`.
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.2, Equation (25), p.24; §6.3.1, Equations (37), (38), p.30; Lemma 8, p.31

import Mathlib
import Definitions.Def_StableVotingDistortion_IsScoreFunction
import Definitions.Def_StableVotingDistortion_scorePrimitives

set_option autoImplicit false

namespace StableVotingDistortion

/-- Equation (25) at the mass `p`: `p [J(1 − p + q) − J(q)] ≤ (λ − q) J(p)` for `0 ≤ q ≤ min{p, λ}`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.2, Equation (25), p.24. -/
def Eq25 (lam : ℝ) (ϕ : ℝ → ℝ) (p : ℝ) : Prop :=
  ∀ q, 0 ≤ q → q ≤ min p lam → p * (J ϕ (1 - p + q) - J ϕ q) ≤ (lam - q) * J ϕ p

/-- Equation (37) at the mass `p`, for every `x ∈ [0, λ)`:
`q + β(p) δ_p(q) + c(p, x) ≤ λ` for `0 ≤ q ≤ min{p, x}`, and
`q + β(p) K_p(q, x) + c(p, x) ≤ 0` for `0 ≤ q ≤ p ≤ x`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.3.1, Equation (37), p.30. -/
def Eq37 (lam : ℝ) (ϕ β : ℝ → ℝ) (c : ℝ → ℝ → ℝ) (p : ℝ) : Prop :=
  ∀ x ∈ Set.Ico 0 lam,
    (∀ q, 0 ≤ q → q ≤ min p x → q + β p * deltaP ϕ p q + c p x ≤ lam) ∧
    (∀ q, 0 ≤ q → q ≤ p → p ≤ x → q + β p * KP ϕ p q x + c p x ≤ 0)

/-- Equation (38) at the mass `p`, for every `x ∈ [0, λ)`:
`ϕ(x) [q + β(p) δ_p(q) + W_x(q) − λ] ≤ (−ϕ(q))₊ c(p, x)` for `0 ≤ q ≤ p`, and
`ϕ(x) [q + β(p) K_p(q, z) + W_x(q) − W_x(z)] ≤ (−ϕ(z))₊ c(p, x)` for `0 ≤ q ≤ p ≤ z ≤ 1`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.3.1, Equation (38), p.30.

**Formalization Note.** `(y)₊` is `max y 0`; it multiplies `c(p, x)`. -/
def Eq38 (lam : ℝ) (ϕ β : ℝ → ℝ) (c : ℝ → ℝ → ℝ) (p : ℝ) : Prop :=
  ∀ x ∈ Set.Ico 0 lam,
    (∀ q, 0 ≤ q → q ≤ p →
      ϕ x * (q + β p * deltaP ϕ p q + Wx lam ϕ x q - lam) ≤ max (-ϕ q) 0 * c p x) ∧
    (∀ q z, 0 ≤ q → q ≤ p → p ≤ z → z ≤ 1 →
      ϕ x * (q + β p * KP ϕ p q z + Wx lam ϕ x q - Wx lam ϕ x z) ≤ max (-ϕ z) 0 * c p x)

/-- The hypotheses of the Verifier Lemma (Lemma 8) on `λ, ϕ, β, c`: `λ ∈ (0, 1)` and (26), `ϕ(r) + r`
nonincreasing on `[λ, 1]`, `β : (0, 1) → ℝ≥0`, `c : (0, 1) × [0, λ) → ℝ≥0`, and (37), (38) for every
`p ∈ (0, 1)` and `x ∈ [0, λ)`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Lemma 8, p.31: "Let ϕ satisfy Equation (26) and let ϕ(r) + r be nonincreasing on [λ, 1]. Let
β : (0, 1) → R≥0 and c : (0, 1) × [0, λ) → R≥0 satisfy Equations (37) and (38) for every p ∈ (0, 1) and
x ∈ [0, λ)."

**Formalization Note.** `β` and `c` are total functions, constrained only on their printed domains.
No measurability or continuity of `β` or `c` is assumed; the page assumes none. -/
structure VerifierHypotheses (lam : ℝ) (ϕ β : ℝ → ℝ) (c : ℝ → ℝ → ℝ) : Prop where
  /-- `λ ∈ (0, 1)` and (26). -/
  score : IsScoreFunction lam ϕ
  /-- `ϕ(r) + r` is nonincreasing on `[λ, 1]`. -/
  antitoneOn_add : AntitoneOn (fun r => ϕ r + r) (Set.Icc lam 1)
  /-- `β ≥ 0` on `(0, 1)`. -/
  beta_nonneg : ∀ p ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ β p
  /-- `c ≥ 0` on `(0, 1) × [0, λ)`. -/
  c_nonneg : ∀ p ∈ Set.Ioo (0 : ℝ) 1, ∀ x ∈ Set.Ico 0 lam, 0 ≤ c p x
  /-- Equation (37) for every `p ∈ (0, 1)`. -/
  eq37 : ∀ p ∈ Set.Ioo (0 : ℝ) 1, Eq37 lam ϕ β c p
  /-- Equation (38) for every `p ∈ (0, 1)`. -/
  eq38 : ∀ p ∈ Set.Ioo (0 : ℝ) 1, Eq38 lam ϕ β c p

end StableVotingDistortion


