-- Prove2me | Definitions.Def_TechBreakthrough_Model_E
-- name    : TechBreakthrough_Model_E
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:34:26.298295+00:00
-- url     : https://prove2.me/theorems/9be9bc71-0d6c-4b27-a0f9-39c131e01653
-- title:
--   Fundamental pairs, the constant $\gamma$, the vector field $E$, candidates
-- statement:
--   A **fundamental pair** is $h_1,h_2\in C^2(\mathcal I)$, positive, solving $\mathcal Lu-ru=0$, with $h_1$ strictly increasing and $h_2$ strictly decreasing. With $S'(x)=\exp(-\int_c^x2\mu/\sigma^2)$ and $\gamma$ the ratio (12), the vector field on $J_E=\{(x,m)\in J:x\ge x_R\}\setminus D$ is
--
--   $$E(x,m)=\frac{H(m)\sigma^2(x)}{2L(x)h_2(x)}\Big\{\frac{\gamma S'(x)}{D(x,m)}[R(x)h_2(m)-G(m)h_2(x)]+R'(x)h_2(x)-R(x)h_2'(x)\Big\},$$
--
--   with $L=\mathcal LR-rR$, $D(x,m)=h_1(m)h_2(x)-h_1(x)h_2(m)$, $H=f/(1-F)$.
--
--   A **candidate from $m_0$** is a $C^1$ function $b$ on $[m_0,\beta)$ with $m_0>x_R$, $E(x_R,m_0)>0$, $b(m_0)=x_R$, $b'=E(b,\cdot)$, whose graph over $(m_0,\beta)$ stays in $J_E^+=E^{-1}((0,\infty))$. The free boundary of Theorem 1 is such a candidate.
--
--   **Formalization Note** $\gamma$ is the ratio evaluated at $c$; `fundamental_solutions` shows that it does not depend on the point. $E$ has Lean's junk values off $J_E$, and it is only used on $J_E$. The page's $J_E^+=\{m_x>m>x\}$ equals $E^{-1}((0,\infty))$ by its own remark (p.24).
-- source:
--   Décamps, Gensbittel & Mariotti, Investment Timing and Technological Breakthroughs, arXiv:2106.05112v1, pp.10, 20–21, 23–24; (12), (13), (33)–(36)

import Definitions.Def_TechBreakthrough_Model_stopRegion

namespace TechBreakthrough

namespace Model

variable (M : Model)

/-- `(h₁, h₂)` is a pair of positive fundamental solutions of `Lu − ru = 0` in `C²(𝓘)`, `h₁`
strictly increasing and `h₂` strictly decreasing, arXiv:2106.05112v1, p.10. -/
structure IsFundamentalPair (h₁ h₂ : ℝ → ℝ) : Prop where
  contDiffOn₁ : ContDiffOn ℝ 2 h₁ M.I
  contDiffOn₂ : ContDiffOn ℝ 2 h₂ M.I
  pos₁ : ∀ x ∈ M.I, 0 < h₁ x
  pos₂ : ∀ x ∈ M.I, 0 < h₂ x
  ode₁ : ∀ x ∈ M.I, M.gen h₁ x - M.r * h₁ x = 0
  ode₂ : ∀ x ∈ M.I, M.gen h₂ x - M.r * h₂ x = 0
  strictMonoOn : StrictMonoOn h₁ M.I
  strictAntiOn : StrictAntiOn h₂ M.I

/-- The derivative `S′(x) = exp(−∫_c^x 2μ/σ²)` of the scale function (13),
arXiv:2106.05112v1, p.10. -/
noncomputable def scaleDeriv (c x : ℝ) : ℝ :=
  Real.exp (-∫ z in c..x, 2 * M.μ z / M.σ z ^ 2)

/-- The ratio of (12), arXiv:2106.05112v1, p.10, at the point `x`. -/
noncomputable def wronskianRatio (c : ℝ) (h₁ h₂ : ℝ → ℝ) (x : ℝ) : ℝ :=
  (deriv h₁ x * h₂ x - h₁ x * deriv h₂ x) / M.scaleDeriv c x

/-- The constant `γ` of (12), arXiv:2106.05112v1, p.10: the ratio of (12), evaluated at `c`. That
the ratio does not depend on the point is part of the milestone
`TechBreakthrough.fundamental_solutions`. -/
noncomputable def gamma (c : ℝ) (h₁ h₂ : ℝ → ℝ) : ℝ := M.wronskianRatio c h₁ h₂ c

/-- `L(x) = LR(x) − rR(x)`, arXiv:2106.05112v1, (34), p.21. -/
noncomputable def gap (x : ℝ) : ℝ := M.gen M.R x - M.r * M.R x

/-- `H(m) = f(m)/(1 − F(m))`, arXiv:2106.05112v1, (36), p.21. -/
noncomputable def hazard (m : ℝ) : ℝ := M.f m / (1 - M.F m)

/-- The vector field `E` of (33), with `D(x, m) = h₁(m)h₂(x) − h₁(x)h₂(m)` of (35),
arXiv:2106.05112v1, pp.20–21.

**Formalization Note** `E` is used only on `J_E` (`Model.domainE`), where the page shows that the
denominators do not vanish. -/
noncomputable def E (c : ℝ) (h₁ h₂ : ℝ → ℝ) (x m : ℝ) : ℝ :=
  M.hazard m * M.σ x ^ 2 / (2 * M.gap x * h₂ x) *
    (M.gamma c h₁ h₂ * M.scaleDeriv c x / (h₁ m * h₂ x - h₁ x * h₂ m) *
        (M.R x * h₂ m - M.G m * h₂ x) +
      deriv M.R x * h₂ x - M.R x * deriv h₂ x)

/-- `J_E = {(x, m) ∈ J : x ≥ x_R} \ D`, the domain of `E`, arXiv:2106.05112v1, p.20. -/
def domainE (xR : ℝ) : Set (ℝ × ℝ) := {z ∈ M.domain | xR ≤ z.1 ∧ z.1 < z.2}

/-- `b` is a **candidate for the free boundary from `m₀`**, arXiv:2106.05112v1, p.24: `m₀ > x_R` with
`E(x_R, m₀) > 0` (that is, `m₀ ∈ (x_R, m_{x_R})`, by Lemma 5), `b` is `C¹` on `[m₀, β)`, `b(m₀) = x_R`,
`b′ = E(b, ·)` on `[m₀, β)`, and the graph of `b` over `(m₀, β)` stays in
`J_E⁺ = E⁻¹((0, ∞))`.

**Formalization Note** The page's `J_E⁺ = {(x, m) ∈ J_E : m_x > m > x}` equals `E⁻¹((0, ∞))` by
Lemma 5 (ii) (p.24); that form avoids the curve `x ↦ m_x` in the definition. -/
structure IsCandidate (c : ℝ) (h₁ h₂ : ℝ → ℝ) (xR m₀ : ℝ) (b : ℝ → ℝ) : Prop where
  xR_lt : xR < m₀
  mem : m₀ ∈ M.I
  E_pos : 0 < M.E c h₁ h₂ xR m₀
  contDiffOn : ContDiffOn ℝ 1 b (M.fromLevel m₀)
  initial : b m₀ = xR
  ode : ∀ m ∈ M.fromLevel m₀,
    HasDerivWithinAt b (M.E c h₁ h₂ (b m) m) (M.fromLevel m₀) m
  graph : ∀ m ∈ M.fromLevel m₀, m₀ < m →
    (b m, m) ∈ M.domainE xR ∧ 0 < M.E c h₁ h₂ (b m) m

end Model

end TechBreakthrough


