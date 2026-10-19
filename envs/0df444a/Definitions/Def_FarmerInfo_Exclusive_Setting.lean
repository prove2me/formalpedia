-- Prove2me | Definitions.Def_FarmerInfo_Exclusive_Setting
-- name    : FarmerInfo_Exclusive_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:12.643655+00:00
-- url     : https://prove2.me/theorems/c86cd94b-5fe2-4276-9e20-642c451228a3
-- title:
--   §3–§4.2 — Gaussian Cournot farmer game, Bayesian Nash equilibrium, welfare, and closed forms
-- statement:
--   The base model has $n$ ex-ante identical farmers, inverse demand $P(Q)=a-bQ+u$, cost $cq_i$, private signals $x_i=u+\epsilon_i$, and a public signal $y=u+\epsilon_r$. The independent Gaussian shocks have variances $1/\alpha$, $1/\gamma$, and $1/\beta$, respectively. An informed set $I$ receives $y$; every farmer receives only its own private signal.
--
--   A strategy is any measurable function of the farmer’s observation whose realized quantity is square-integrable. Bayesian Nash equilibrium means that no admissible unilateral deviation raises ex-ante expected profit. Total farmer welfare is the sum of these expected profits. The module also defines the coefficients of Proposition 1 and the closed-form quantities of Lemma 2 and Appendix A.
--
--   **Formalization Note** The quantity constraint printed in (2)–(3) is incompatible with the Gaussian affine equilibrium in Proposition 1; this module uses the unconstrained game that the paper’s calculations solve. The three precisions are positive, and the closed forms take a real extension of the number informed.
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (version of June 27, 2019), pp. 8–14, 35, equations (1)–(7), Lemma 1, Lemma 2, Proposition 2, Appendix A

import Mathlib

namespace FarmerInfo.Exclusive

open MeasureTheory ProbabilityTheory Finset

noncomputable section

/-- Zhou et al., SSRN 3369334 (2019), pp. 8–9: the primitives of the farmer game. -/
structure Model where
  a : ℝ
  b : ℝ
  c : ℝ
  α : ℝ
  β : ℝ
  γ : ℝ
  n : ℕ

namespace Model

/-- §3, pp. 8–9: the base model's population and positive precisions. -/
def Standing (M : Model) : Prop :=
  4 ≤ M.n ∧ 0 < M.a ∧ 0 < M.b ∧ 0 < M.α ∧ 0 < M.β ∧ 0 < M.γ

/-- The independent intercept shock, private noises, and public noise. -/
abbrev Ω (M : Model) : Type := ℝ × (Fin M.n → ℝ) × ℝ

/-- §3, pp. 8–9: independent centered Gaussian shocks, with variances 1/α, 1/γ, 1/β. -/
def P (M : Model) : Measure M.Ω :=
  (gaussianReal 0 (M.α⁻¹).toNNReal).prod
    ((Measure.pi fun _ : Fin M.n => gaussianReal 0 (M.γ⁻¹).toNNReal).prod
      (gaussianReal 0 (M.β⁻¹).toNNReal))

/-- §3, p. 8: the uncertain demand intercept. -/
def u (M : Model) (ω : M.Ω) : ℝ := ω.1

/-- §3, p. 8: farmer i's private signal. -/
def x (M : Model) (i : Fin M.n) (ω : M.Ω) : ℝ := ω.1 + ω.2.1 i

/-- §3, p. 9: the public signal. -/
def y (M : Model) (ω : M.Ω) : ℝ := ω.1 + ω.2.2

/-- §3, pp. 9–10: the observation of farmer i; only informed farmers see y. -/
def obs (M : Model) (I : Finset (Fin M.n)) (i : Fin M.n) (ω : M.Ω) : ℝ × ℝ :=
  if i ∈ I then (M.x i ω, M.y ω) else (M.x i ω, 0)

/-- The strategy produces a real quantity from the farmer's own observation. -/
abbrev Strategy : Type := ℝ × ℝ → ℝ

/-- §3, pp. 9–10: measurable square-integrable decisions. -/
def Admissible (M : Model) (I : Finset (Fin M.n)) (i : Fin M.n)
    (f : Strategy) : Prop :=
  Measurable f ∧ MemLp (fun ω : M.Ω => f (M.obs I i ω)) 2 M.P

/-- Equations (1)–(3): realized Cournot profit with cost c per unit. -/
def profit (M : Model) (I : Finset (Fin M.n))
    (σ : Fin M.n → Strategy) (i : Fin M.n) (ω : M.Ω) : ℝ :=
  (M.a - M.b * (∑ k : Fin M.n, σ k (M.obs I k ω)) + M.u ω) *
    σ i (M.obs I i ω) - M.c * σ i (M.obs I i ω)

/-- Equations (2)–(3): ex-ante Bayesian Nash equilibrium among all admissible strategies. -/
def IsBNE (M : Model) (I : Finset (Fin M.n)) (σ : Fin M.n → Strategy) : Prop :=
  (∀ i, M.Admissible I i (σ i)) ∧
  ∀ i f, M.Admissible I i f →
    ∫ ω, M.profit I (Function.update σ i f) i ω ∂M.P ≤
      ∫ ω, M.profit I σ i ω ∂M.P

/-- Equation (5): total ex-ante expected farmer profit. -/
def welfare (M : Model) (I : Finset (Fin M.n)) (σ : Fin M.n → Strategy) : ℝ :=
  ∑ i : Fin M.n, ∫ ω, M.profit I σ i ω ∂M.P

/-- Lemma 1(1), p. 10: posterior coefficient of x_i. -/
def kI (M : Model) : ℝ := M.γ / (M.α + M.β + M.γ)

/-- Lemma 1(1), p. 10: posterior coefficient of y. -/
def mI (M : Model) : ℝ := M.β / (M.α + M.β + M.γ)

/-- Lemma 1(2), p. 10: posterior coefficient without y. -/
def kJ (M : Model) : ℝ := M.γ / (M.α + M.γ)

/-- Proposition 1, equation (7), p. 12: Ψ as a function of real n₁. -/
def Psi (M : Model) (n1 : ℝ) : ℝ :=
  4 * (n1 + 1) * M.α ^ 2 + ((M.n : ℝ) + 1) * M.γ *
    ((n1 + 1) * M.γ + 2 * M.β) +
    2 * (n1 + 1) * M.α * (((M.n : ℝ) + 2) * M.γ + 2 * M.β)

/-- Proposition 1, equation (7), p. 12. -/
def A0 (M : Model) : ℝ := (M.a - M.c) / (M.b * ((M.n : ℝ) + 1))

/-- Proposition 1, equation (7), p. 12. -/
def B0 (M : Model) : ℝ := M.A0

/-- Proposition 1, equation (7), p. 12. -/
def A1 (M : Model) (n1 : ℝ) : ℝ :=
  M.γ * (2 * M.α + M.γ) * (n1 + 1) / (M.b * M.Psi n1)

/-- Proposition 1, equation (7), p. 12. -/
def A2 (M : Model) (n1 : ℝ) : ℝ :=
  2 * M.β * (2 * M.α + M.γ) / (M.b * M.Psi n1)

/-- Proposition 1, equation (7), p. 12. -/
def B1 (M : Model) (n1 : ℝ) : ℝ :=
  M.γ * ((n1 + 1) * (2 * M.α + M.γ) + 2 * M.β) / (M.b * M.Psi n1)

/-- Proposition 1, equation (6), p. 12: the linear equilibrium candidate. -/
def linProfile (M : Model) (I : Finset (Fin M.n)) : Fin M.n → Strategy :=
  fun i p => if i ∈ I then M.A0 + M.A1 (I.card : ℝ) * p.1 +
    M.A2 (I.card : ℝ) * p.2 else M.B0 + M.B1 (I.card : ℝ) * p.1

/-- Lemma 2, p. 14: expected profit of an informed farmer. -/
def WI (M : Model) (n1 : ℝ) : ℝ :=
  M.b * (M.A0 ^ 2 + M.A1 n1 ^ 2 * (1 / M.α + 1 / M.γ) +
    M.A2 n1 ^ 2 * (1 / M.α + 1 / M.β) +
    2 * M.A1 n1 * M.A2 n1 * (1 / M.α))

/-- Lemma 2, p. 14: expected profit of an uninformed farmer. -/
def WJ (M : Model) (n1 : ℝ) : ℝ :=
  M.b * (M.B0 ^ 2 + M.B1 n1 ^ 2 * (1 / M.α + 1 / M.γ))

/-- §4.2, p. 14: closed-form total welfare, extended to real n₁ for Appendix A. -/
def W (M : Model) (n1 : ℝ) : ℝ :=
  n1 * M.WI n1 + ((M.n : ℝ) - n1) * M.WJ n1

/-- Proposition 2, p. 14: the threshold polynomial V(n, β; γ). -/
def V (M : Model) : ℝ :=
  let n : ℝ := M.n
  16 * M.α ^ 4 + 16 * M.α ^ 3 * (M.β + 3 * M.γ) +
  4 * M.α ^ 2 * M.γ * ((7 + n) * M.β + (12 + 2 * n - n ^ 2) * M.γ) +
  4 * M.α * M.γ ^ 2 * ((4 + n) * M.β + (5 + 2 * n - n ^ 2) * M.γ) -
  (n ^ 2 - 2 * n - 3) * M.γ ^ 3 * (M.β + M.γ)

/-- Appendix A, p. 35: numerator of dW/dn₁. -/
def Omega_n (M : Model) (n1 : ℝ) : ℝ :=
  let n : ℝ := M.n
  (-4 : ℝ) * M.β * (
    16 * (n1 - 1) * M.α ^ 4 +
    8 * M.α ^ 3 * (4 * (n1 - 1) * M.β + (-5 + 3 * n1 + 2 * n1 * n) * M.γ) +
    M.γ ^ 2 * (2 * (n - 3) * M.β ^ 2 +
      (-7 - n1 + n + 3 * n1 * n) * M.β * M.γ +
      2 * (n1 * n - 1) * M.γ ^ 2) +
    4 * M.α ^ 2 * (4 * (n1 - 1) * M.β ^ 2 +
      (-15 + 9 * n1 + 4 * n1 * n) * M.β * M.γ +
      3 * (-3 + n1 + 2 * n1 * n) * M.γ ^ 2) +
    2 * M.α * M.γ * (2 * (-5 + 3 * n1) * M.β ^ 2 +
      (-18 + 4 * n1 + n + 7 * n1 * n) * M.β * M.γ +
      (-7 + n1 + 6 * n1 * n) * M.γ ^ 2))

/-- Appendix A, p. 35: denominator of dW/dn₁. -/
def Omega_d (M : Model) (n1 : ℝ) : ℝ :=
  let n : ℝ := M.n
  M.b * (4 * (1 + n1) * M.α ^ 2 +
    (1 + n) * M.γ * (2 * M.β + M.γ + n1 * M.γ) +
    2 * (1 + n1) * M.α * (2 * M.β + (2 + n) * M.γ)) ^ 3

end Model
end
end FarmerInfo.Exclusive


