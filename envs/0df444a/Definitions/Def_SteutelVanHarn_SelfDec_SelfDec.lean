-- Prove2me | Definitions.Def_SteutelVanHarn_SelfDec_SelfDec
-- name    : SteutelVanHarn_SelfDec_SelfDec
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:50:15.624829+00:00
-- url     : https://prove2.me/theorems/aed23476-61f9-436f-b598-46bf06bb2129
-- title:
--   Definition 2.1 — discrete self-decomposability; the canonical form (2.4)
-- statement:
--   Let $(p_n)$ be a distribution on $\mathbb N_0$ with p.g.f. $P$.
--
--   1. (**Definition 2.1**) $(p_n)$ is **discrete self-decomposable** if for every $\alpha\in(0,1)$ there is a p.g.f. $P_\alpha$ of a distribution on $\mathbb N_0$ such that
--   $$
--   P(z)=P(1-\alpha+\alpha z)\,P_\alpha(z)\qquad(|z|\le1).\tag{2.1}
--   $$
--   Here $P(1-\alpha+\alpha z)$ is the p.g.f. of the $\alpha$-thinning $\alpha\circ X$ of a random variable $X$ with p.g.f. $P$, so (2.1) is the discrete analogue of the classical relation $\varphi(t)=\varphi(\alpha t)\varphi_\alpha(t)$ for characteristic functions.
--   2. $P$ has the **canonical form (2.4)** with parameters $\lambda$ and $(g_n)$ if $\lambda>0$, $(g_n)$ is a distribution on $\mathbb N_0$ with $g_0=0$, and for every $0\le z<1$ the integral below is finite and
--   $$
--   P(z)=\exp\Big\{-\lambda\int_z^1\frac{1-G(u)}{1-u}\,du\Big\}.\tag{2.4}
--   $$
--
--   Theorem 2.2 of the paper shows that, under $0<p_0<1$, discrete self-decomposability is equivalent to the form (2.4).
--
--   **Formalization Note** (2.1) is required for real $z\in[0,1]$ instead of $|z|\le1$; this is equivalent, since p.g.f.'s agreeing on $[0,1]$ have equal coefficients. The integral in (2.4) is improper at $u=1$; its finiteness (integrability of the integrand on $(z,1)$) is a stated clause, because Lean's integral of a non-integrable function is $0$.
-- source:
--   Steutel & van Harn, Discrete analogues of self-decomposability and stability, Memorandum COSOR 78-07, TH Eindhoven (1978), p. 2, §2, Definition 2.1, (2.1), (2.3); p. 3, Theorem 2.2, (2.4)

import Definitions.Def_SteutelVanHarn_SelfDec_InfDiv

namespace SteutelVanHarn.SelfDec

/-- Definition 2.1 (p. 2): a distribution `p` on `ℕ₀` with p.g.f. `P` is discrete self-decomposable
if for every `α ∈ (0, 1)` there is a p.g.f. `P_α` with `P(z) = P(1 - α + α z) P_α(z)`.

Formalization Note: the paper requires (2.1) for `|z| ≤ 1`; here it is required for real
`z ∈ [0, 1]`, which is equivalent, since p.g.f.'s agreeing on `[0, 1]` have equal coefficients. -/
def IsDiscreteSelfDec (p : ℕ → ℝ) : Prop :=
  IsDistribution p ∧
    ∀ α ∈ Set.Ioo (0 : ℝ) 1, ∃ q : ℕ → ℝ, IsDistribution q ∧
      ∀ z ∈ Set.Icc (0 : ℝ) 1, pgf p z = pgf p (1 - α + α * z) * pgf q z

/-- The canonical form (2.4) of Theorem 2.2 (p. 3): `λ > 0`, `g` is a distribution on `ℕ₀` with
`g 0 = 0`, and for `z ∈ [0, 1)` the integral `∫_z^1 (1 - G(u))/(1 - u) du` is finite and
`P(z) = exp{-λ ∫_z^1 (1 - G(u))/(1 - u) du}`.

Formalization Note: the integral is improper at `u = 1`; its finiteness (integrability on
`(z, 1)`) is stated explicitly, because Lean's integral of a non-integrable function is `0`. -/
def HasForm24 (p : ℕ → ℝ) (lam : ℝ) (g : ℕ → ℝ) : Prop :=
  0 < lam ∧ IsDistribution g ∧ g 0 = 0 ∧
    ∀ z ∈ Set.Ico (0 : ℝ) 1,
      MeasureTheory.IntegrableOn (fun u => (1 - pgf g u) / (1 - u)) (Set.Ioo z 1) ∧
      pgf p z = Real.exp (-(lam * ∫ u in z..1, (1 - pgf g u) / (1 - u)))

end SteutelVanHarn.SelfDec


