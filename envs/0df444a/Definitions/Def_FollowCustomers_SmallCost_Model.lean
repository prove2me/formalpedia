-- Prove2me | Definitions.Def_FollowCustomers_SmallCost_Model
-- name    : FollowCustomers_SmallCost_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:11.354683+00:00
-- url     : https://prove2.me/theorems/3ecc0b1b-310e-4cac-8948-05d7ead49a4c
-- title:
--   §2–§3.4, pp. 5–13 — repositioning duopoly: λ, πs, πd, value functions, conditions (5)–(9), threshold system (14)–(15), solution branches as K → 0
-- statement:
--   This definition file sets up the dynamic repositioning duopoly of Ning and Villas-Boas.
--
--   **Parameters.** A parameter tuple $P=(r,\sigma^2,\delta)$ consists of the firms' common discount rate $r$, the variance $\sigma^2$ of the driftless Brownian motion that moves the consumers' ideal point $x_t$ on $[0,1]$, and the weight $\delta$ of the repositionable attribute $x$ relative to the fixed attribute $z$ in consumer utility $v-\delta x_t-z-p$. The **standing assumptions** are
--   $$r>0,\qquad \sigma^2>0,\qquad \delta>0 .$$
--
--   **Primitives.** With $\lambda=\sqrt{2r/\sigma^2}$, the instantaneous profit of a firm when both firms are on the same side is $\pi_s=\tfrac12$, and when they are on different sides and the firm is at distance $x$ from the consumers it is
--   $$\pi_d(x)=\tfrac12\Big(1+\frac{\delta(1-2x)}{3}\Big)^2 .$$
--   For constants $A,B,C$ the value functions are
--   $$V_d(x)=\frac{\pi_d(x)}{r}+\frac{4\delta^2}{9r\lambda^2}+Ae^{\lambda x}+Be^{-\lambda x},\qquad V_s(x)=\frac{\pi_s}{r}+C\big(e^{\lambda x}+e^{-\lambda x}\big).$$
--
--   **Equilibrium conditions.** For a repositioning cost $K$ and thresholds $\underline x$ (the lowest distance at which firms on the same side reposition with positive hazard) and $x^*$ (the distance at which a firm on the other side repositions), the value-matching and smooth-pasting conditions are
--   $$V_d(1-\underline x)-K=V_s(\underline x),\quad -V_d'(1-\underline x)=V_s'(\underline x),\quad V_d(x^*)=V_s(1-x^*)-K,\quad V_d'(x^*)=-V_s'(1-x^*),\quad V_d(1-x^*)=V_s(1-x^*).$$
--
--   **Threshold system.** With $G=e^{\lambda(x^*+\underline x-1)}$, equations (14) and (15) are
--   $$G=\frac{\pi_d(x^*)-\pi_s+\pi_d'(x^*)/\lambda+rK+\frac{4\delta^2}{9\lambda^2}}{\pi_d(1-\underline x)-\pi_s+\pi_d'(1-\underline x)/\lambda-rK+\frac{4\delta^2}{9\lambda^2}},\qquad G=\frac{\pi_d(1-\underline x)-\pi_s-\pi_d'(1-\underline x)/\lambda-rK+\frac{4\delta^2}{9\lambda^2}}{\pi_d(x^*)-\pi_s-\pi_d'(x^*)/\lambda+rK+\frac{4\delta^2}{9\lambda^2}} .$$
--   A **threshold pair** at cost $K$ is a solution $(\underline x,x^*)$ of (14)–(15) in the region
--   $$\tfrac12<\underline x<x^*<1,\qquad \delta(2x^*-1)<3 .$$
--   A **solution branch** is a pair of functions $K\mapsto(\underline x(K),x^*(K))$ that is a threshold pair for every sufficiently small $K>0$.
--
--   **Appendix abbreviations.** The prices $p^*=(3+\delta-2\delta x^*)/3$ at $x^*$ and $\underline p=(3-\delta+2\delta\underline x)/3$ at $1-\underline x$, their sum $y=p^*+\underline p$, equations (x) and (xi)
--   $$G(\underline p^2-1)-(p^{*2}-1)+\tfrac{4\delta}{3\lambda}(p^*-G\underline p)+\tfrac{8\delta^2}{9\lambda^2}(G-1)=2rK(1+G),$$
--   $$G(p^{*2}-1)-(\underline p^2-1)+\tfrac{4\delta}{3\lambda}(Gp^*-\underline p)+\tfrac{8\delta^2}{9\lambda^2}(G-1)=-2rK(1+G),$$
--   and the constants $\sqrt[3]{9\sigma^2/(4\delta)}$ and $\sqrt[3]{\delta\sigma^4/18}$ of the expansions (16)–(18).
--
--   These objects are the common vocabulary of every statement of the mission: the goal and its milestones are all about solution branches of (14)–(15).
--
--   **Formalization Note.** The variance $\sigma^2$ is the parameter `σ2`. Primes are `deriv` of the corresponding function evaluated at the point; $\pi_d'$ is `deriv (pid P)`, not a hand-coded formula. Equations (14)–(15) are kept in the paper's ratio form: since the left side $G$ is positive, a zero denominator makes the equation false rather than trivially true. The region is an addition to the printed system: $\tfrac12<\underline x<x^*<1$ is the paper's own description of the thresholds (pp. 8–9, 13), and $\delta(2x^*-1)<3$ keeps the far firm's price $p^*$ positive, so that $\pi_d$ is the interior Hotelling profit at every distance the differentiated firms visit. The cube roots are real powers `^ (1/3)` of positive numbers.
-- source:
--   Ning & Villas-Boas, Following the Customers: Dynamic Competitive Repositioning, SSRN 3695318 (December 2020), pp. 5–13 (PDF 7–15), §2, §3.2–3.4, (1)–(9), (14)–(15); Appendix p. 30 (PDF 32), definitions of p*, p̲, G, y and (x)–(xi); p. 14 (PDF 16), constants of (16)–(18)

import Mathlib

namespace FollowCustomers.SmallCost

/-- The primitive parameters of the repositioning duopoly (Ning & Villas-Boas, §2):
the discount rate `r`, the variance `σ2` (= σ²) of the Brownian motion driving the
consumers' ideal point, and the weight `δ` of the repositionable attribute. -/
structure Params where
  r : ℝ
  σ2 : ℝ
  δ : ℝ

/-- Standing assumptions of §2: `r > 0`, `σ² > 0`, `δ > 0`. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.r ∧ 0 < P.σ2 ∧ 0 < P.δ

/-- `λ = √(2r/σ²)`, equation (2). -/
noncomputable def lam (P : Params) : ℝ :=
  Real.sqrt (2 * P.r / P.σ2)

/-- Instantaneous profit when both firms are on the same side, `π_s = 1/2` (p. 7). -/
noncomputable def pis : ℝ := 1 / 2

/-- Instantaneous profit of a firm at distance `x` from the consumers when the firms are on
different sides, `π_d(x) = ½ (1 + δ(1 − 2x)/3)²` (p. 7). -/
noncomputable def pid (P : Params) (x : ℝ) : ℝ :=
  1 / 2 * (1 + P.δ * (1 - 2 * x) / 3) ^ 2

/-- Value function with the firms on different sides, equation (2), with constants `A`, `B`. -/
noncomputable def Vd (P : Params) (A B x : ℝ) : ℝ :=
  pid P x / P.r + 4 * P.δ ^ 2 / (9 * P.r * lam P ^ 2)
    + A * Real.exp (lam P * x) + B * Real.exp (-(lam P * x))

/-- Value function with the firms on the same side, equation (4) with `C = D`. -/
noncomputable def Vs (P : Params) (C x : ℝ) : ℝ :=
  pis / P.r + C * (Real.exp (lam P * x) + Real.exp (-(lam P * x)))

/-- Value matching and smooth pasting, conditions (5)–(9). Primes are `deriv` of the value
function, evaluated at the point. -/
def Conditions (P : Params) (K xl xs A B C : ℝ) : Prop :=
  Vd P A B (1 - xl) - K = Vs P C xl ∧
  -deriv (Vd P A B) (1 - xl) = deriv (Vs P C) xl ∧
  Vd P A B xs = Vs P C (1 - xs) - K ∧
  deriv (Vd P A B) xs = -deriv (Vs P C) (1 - xs) ∧
  Vd P A B (1 - xs) = Vs P C (1 - xs)

/-- Numerator of the right side of (14). -/
noncomputable def num14 (P : Params) (K xs : ℝ) : ℝ :=
  pid P xs - pis + deriv (pid P) xs / lam P + P.r * K + 4 * P.δ ^ 2 / (9 * lam P ^ 2)

/-- Denominator of the right side of (14). -/
noncomputable def den14 (P : Params) (K xl : ℝ) : ℝ :=
  pid P (1 - xl) - pis + deriv (pid P) (1 - xl) / lam P - P.r * K
    + 4 * P.δ ^ 2 / (9 * lam P ^ 2)

/-- Numerator of the right side of (15). -/
noncomputable def num15 (P : Params) (K xl : ℝ) : ℝ :=
  pid P (1 - xl) - pis - deriv (pid P) (1 - xl) / lam P - P.r * K
    + 4 * P.δ ^ 2 / (9 * lam P ^ 2)

/-- Denominator of the right side of (15). -/
noncomputable def den15 (P : Params) (K xs : ℝ) : ℝ :=
  pid P xs - pis - deriv (pid P) xs / lam P + P.r * K + 4 * P.δ ^ 2 / (9 * lam P ^ 2)

/-- `G = e^{λ(x* + x̲ − 1)}` (Appendix, p. 30). -/
noncomputable def Gf (P : Params) (xl xs : ℝ) : ℝ :=
  Real.exp (lam P * (xs + xl - 1))

/-- Equation (14), in the paper's ratio form. -/
def Eq14 (P : Params) (K xl xs : ℝ) : Prop :=
  Gf P xl xs = num14 P K xs / den14 P K xl

/-- Equation (15), in the paper's ratio form. -/
def Eq15 (P : Params) (K xl xs : ℝ) : Prop :=
  Gf P xl xs = num15 P K xl / den15 P K xs

/-- The region of thresholds: `1/2 < x̲ < x* < 1` and `δ(2x* − 1) < 3`. -/
def Region (P : Params) (xl xs : ℝ) : Prop :=
  1 / 2 < xl ∧ xl < xs ∧ xs < 1 ∧ P.δ * (2 * xs - 1) < 3

/-- `(x̲, x*)` solves the system (14)–(15) inside the region. -/
def IsThresholdPair (P : Params) (K xl xs : ℝ) : Prop :=
  Eq14 P K xl xs ∧ Eq15 P K xl xs ∧ Region P xl xs

/-- A solution branch as `K → 0⁺`: for every sufficiently small `K > 0`,
`(xl K, xs K)` is a threshold pair. -/
def IsBranch (P : Params) (xl xs : ℝ → ℝ) : Prop :=
  ∀ᶠ K in nhdsWithin (0 : ℝ) (Set.Ioi 0), IsThresholdPair P K (xl K) (xs K)

/-- The price at `x*`, `p* = (3 + δ − 2δx*)/3` (p. 30). -/
noncomputable def pstar (P : Params) (xs : ℝ) : ℝ :=
  (3 + P.δ - 2 * P.δ * xs) / 3

/-- The price at `1 − x̲`, `p̲ = (3 − δ + 2δx̲)/3` (p. 30). -/
noncomputable def plow (P : Params) (xl : ℝ) : ℝ :=
  (3 - P.δ + 2 * P.δ * xl) / 3

/-- `y = p* + p̲` (p. 30). -/
noncomputable def yf (P : Params) (xl xs : ℝ) : ℝ :=
  pstar P xs + plow P xl

/-- Equation (x), p. 30. -/
def EqX (P : Params) (K xl xs : ℝ) : Prop :=
  Gf P xl xs * (plow P xl ^ 2 - 1) - (pstar P xs ^ 2 - 1)
    + 4 * P.δ / (3 * lam P) * (pstar P xs - Gf P xl xs * plow P xl)
    + 8 * P.δ ^ 2 / (9 * lam P ^ 2) * (Gf P xl xs - 1)
    = 2 * P.r * K * (1 + Gf P xl xs)

/-- Equation (xi), p. 30. -/
def EqXI (P : Params) (K xl xs : ℝ) : Prop :=
  Gf P xl xs * (pstar P xs ^ 2 - 1) - (plow P xl ^ 2 - 1)
    + 4 * P.δ / (3 * lam P) * (Gf P xl xs * pstar P xs - plow P xl)
    + 8 * P.δ ^ 2 / (9 * lam P ^ 2) * (Gf P xl xs - 1)
    = -(2 * P.r * K * (1 + Gf P xl xs))

/-- The leading coefficient `∛(9σ²/(4δ))` of (16)–(17). -/
noncomputable def coefA (P : Params) : ℝ :=
  (9 * P.σ2 / (4 * P.δ)) ^ ((1 : ℝ) / 3)

/-- The coefficient `∛(δσ⁴/18)` of (16)–(18). -/
noncomputable def coefB (P : Params) : ℝ :=
  (P.δ * P.σ2 ^ 2 / 18) ^ ((1 : ℝ) / 3)

end FollowCustomers.SmallCost


