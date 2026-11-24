-- Prove2me | Definitions.Def_CoVaRMC_Batching_Supplement_Model
-- name    : CoVaRMC_Batching_Supplement_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T02:12:46.612783+00:00
-- url     : https://prove2.me/theorems/360a2846-a9ac-4242-8921-94718be69182
-- title:
--   §4.1–4.3, pp. 13–20 — delta-gamma pair (17)–(18), g*, roots r_ℓ, λ, q_ℓ, Y_ℓ, P_ε, Q(y, x), Q(x), Assumption 2, two-stage sample, ṽ_α, F̃_{n₂} (25)–(26) and Ỹ^IS
-- statement:
--   **Delta-gamma pair (§4.1, p. 14).** Let $Z=(Z_1,\dots,Z_d)$ be i.i.d. standard normal risk factors, $d\ge 1$. The two portfolio losses are
--   $$X=c_1+\sum_{j=1}^d\big(\delta_{1j}Z_j+\gamma_{1j}Z_j^2\big),\qquad Y=c_2+\sum_{j=1}^d\big(\delta_{2j}Z_j+\gamma_{2j}Z_j^2\big).\tag{17–18}$$
--   Write $W=(Z_1,\dots,Z_{d-1})$ for the first $d-1$ factors. Given $W$, $X=g(Z_d)$ with $g(z)=\xi_1+\delta_{1d}z+\gamma_{1d}z^2$ and $\xi_1=c_1+\sum_{j<d}(\delta_{1j}Z_j+\gamma_{1j}Z_j^2)$ (21)–(22).
--
--   **IS quantities (§4.2.1, pp. 14–16).** For $\gamma_{1d}>0$ let $g^*=\min_z g(z)=\xi_1-\delta_{1d}^2/(4\gamma_{1d})$. For $x>g^*$ the equation $g(z)=x$ has the roots
--   $$r_{1,2}=\frac{-\delta_{1d}\mp\lambda}{2\gamma_{1d}},\qquad \lambda=\sqrt{\delta_{1d}^2+4\gamma_{1d}(x-\xi_1)}=|g'(r_\ell)|,$$
--   and $q_\ell=f_d(r_\ell)/\lambda$, with $f_d$ the standard normal density, and $Y_\ell=c_2+\sum_{j<d}(\delta_{2j}Z_j+\gamma_{2j}Z_j^2)+\delta_{2d}r_\ell+\gamma_{2d}r_\ell^2$. For $x\le g^*$, $q_\ell=0$ (and $Y_\ell=+\infty$). Further $P_\varepsilon=\Pr\{|X-x|\le\varepsilon\mid Z_1,\dots,Z_{d-1}\}$, and the ratio $\Pr\{Y\le y,|X-x|\le\varepsilon\}/\Pr\{|X-x|\le\varepsilon\}$ whose limit as $\varepsilon\to0$ is $\Pr\{Y\le y\mid X=x\}$ by (3).
--
--   **Q and Assumption 2 (§4.3, pp. 19–20).** $Q(y,x)=I\{Y_1\le y\}q_1+I\{Y_2\le y\}q_2$ and $Q(x)=q_1+q_2$, with expectations $\mathrm E[Q(y,x)]$, $\mathrm E[Q(x)]$ over $W\sim N(0,I_{d-1})$. **Assumption 2**: $\mathrm E[Q(x)]$ and, for $y\in\mathcal Y$, $\mathrm E[Q(y,x)]$ are twice differentiable functions of $x\in\mathbb R$.
--
--   **IS-inspired estimator (§4.2.2, pp. 18–20).** Step 1 draws $n_1$ i.i.d. copies of $Z$ and sets $\tilde v_\alpha=X_{(\lceil\alpha n_1\rceil)}$. Step 2 draws, independently, $n_2$ i.i.d. copies $W_1,\dots,W_{n_2}$ of $W$, and
--   $$\tilde F_{n_2}(y,\tilde v_\alpha)=\frac{\frac1{n_2}\sum_{k=1}^{n_2}Q_k(y,\tilde v_\alpha)}{\frac1{n_2}\sum_{k=1}^{n_2}Q_k(\tilde v_\alpha)},\qquad \tilde Y^{\mathrm{IS}}=\inf\{y\in\mathbb R:\tilde F_{n_2}(y,\tilde v_\alpha)\ge\beta\}.\tag{25–26}$$
--
--   These objects are the setting of Theorems 4–6 and Lemmas 5–7 of the paper; the joint density, VaR, CoVaR and Assumption 1 come from the published `CoVaRMC.Batching.Setting`.
--
--   **Formalization Note** There are $d=d'+1$ factors: $W$ is `Fin d' → ℝ` and $Z_d$ is a real `z`. The law of $W$ is the product of `gaussianReal 0 1`, and $f_d$ is `gaussianPDFReal 0 1`. Where the paper sets $Y_\ell=+\infty$ (for $x\le g^*$), $q_\ell=0$ makes both summands of $Q(y,x)$ vanish, so no extended reals are used. Assumption 2 also records that both expectations are finite (integrable), which the paper's "twice differentiable function" presupposes. The two-stage sample is one sequence of independent pairs (first-stage $Z$, second-stage $W$), of which the first $n_1$, resp. $n_2$, are used. $\tilde v_\alpha$ uses the published order statistic and the base `rankIdx` (0-based index $\lceil\alpha n_1\rceil-1$); it is $0$ when $n_1=0$. $\tilde F_{n_2}$ is $0$ when every $\tilde q$ vanishes (Lean's $0/0=0$), and then $\tilde Y^{\mathrm{IS}}=\inf\emptyset=0$. $\tilde Y^{\mathrm{IS}}$ is defined by the paper's own identity on p. 20 rather than by the weighted sort of Step 3 (p. 19), which picks the first $m$ with $\pi_m>\beta$ and so differs from the infimum only when a partial weight sum equals $\beta$ exactly.
-- source:
--   Huang, Lin, Hong, Monte-Carlo Estimation of CoVaR, arXiv:2210.06148v1, pp. 13–20: Equations (17)–(18), (21)–(22); §4.2.1 (P_ε, g*, r_ℓ, λ, q_ℓ, Y_ℓ), Lemma 5; §4.2.2 Steps 1–3, Equation (25); §4.3 Q(y, x), Q(x), Equation (26), Assumption 2, the identity Ỹ^IS = inf{y : F̃_{n2}(y, ṽ_α) ≥ β} (p. 20)

import Mathlib
import Definitions.Def_ImpactInvesting_Portfolio_OrderStat
import Definitions.Def_CoVaRMC_Batching_Setting

namespace CoVaRMC.Batching.Supplement

open MeasureTheory ProbabilityTheory

/-! # The delta-gamma pair and the IS-inspired estimator (§4, pp. 13–20)

Huang, Lin, Hong, *Monte-Carlo Estimation of CoVaR*, arXiv:2210.06148v1, §4.2–4.3.
There are `d = d' + 1` risk factors: the first `d'` are `W = (Z_1, …, Z_{d-1}) : Fin d' → ℝ`, the
last is `Z_d = z : ℝ`. -/

/-- Equations (17)–(18), p. 14: the coefficients of the delta-gamma pair
`X = c₁ + ∑_{j=1}^d (δ_{1j} Z_j + γ_{1j} Z_j²)`, `Y = c₂ + ∑_{j=1}^d (δ_{2j} Z_j + γ_{2j} Z_j²)`,
the coefficients of the last factor `Z_d` stored separately. -/
structure DeltaGamma (d' : ℕ) where
  c1 : ℝ
  c2 : ℝ
  δ1 : Fin d' → ℝ
  γ1 : Fin d' → ℝ
  δ2 : Fin d' → ℝ
  γ2 : Fin d' → ℝ
  δ1d : ℝ
  γ1d : ℝ
  δ2d : ℝ
  γ2d : ℝ

namespace DeltaGamma

variable {d' : ℕ} (M : DeltaGamma d')

/-- p. 15: `ξ₁ = c₁ + ∑_{j=1}^{d-1} (δ_{1j} Z_j + γ_{1j} Z_j²)`. -/
noncomputable def xi1 (w : Fin d' → ℝ) : ℝ :=
  M.c1 + ∑ j, (M.δ1 j * w j + M.γ1 j * w j ^ 2)

/-- p. 16: `c₂ + ∑_{j=1}^{d-1} (δ_{2j} Z_j + γ_{2j} Z_j²)`, the part of `Y` fixed by `W`. -/
noncomputable def eta (w : Fin d' → ℝ) : ℝ :=
  M.c2 + ∑ j, (M.δ2 j * w j + M.γ2 j * w j ^ 2)

/-- Equations (17), (21), (22): `X = g_W(Z_d) = ξ₁ + δ_{1d} Z_d + γ_{1d} Z_d²`. -/
noncomputable def X (w : Fin d' → ℝ) (z : ℝ) : ℝ :=
  M.xi1 w + M.δ1d * z + M.γ1d * z ^ 2

/-- Equation (18): `Y = c₂ + ∑_{j<d} (δ_{2j} Z_j + γ_{2j} Z_j²) + δ_{2d} Z_d + γ_{2d} Z_d²`. -/
noncomputable def Y (w : Fin d' → ℝ) (z : ℝ) : ℝ :=
  M.eta w + M.δ2d * z + M.γ2d * z ^ 2

/-- p. 15: `g* = min_z g(z) = ξ₁ - δ_{1d}² / (4 γ_{1d})` (meaningful for `γ_{1d} > 0`). -/
noncomputable def gStar (w : Fin d' → ℝ) : ℝ :=
  M.xi1 w - M.δ1d ^ 2 / (4 * M.γ1d)

/-- pp. 15, 18: `λ = |g'(r_ℓ)| = √(δ_{1d}² + 4 γ_{1d} (x - ξ₁))` (used for `x > g*`). -/
noncomputable def lam (w : Fin d' → ℝ) (x : ℝ) : ℝ :=
  √(M.δ1d ^ 2 + 4 * M.γ1d * (x - M.xi1 w))

/-- p. 18: the smaller root `r₁ = (-δ_{1d} - λ) / (2 γ_{1d})` of `g(z) = x` (used for `x > g*`). -/
noncomputable def r1 (w : Fin d' → ℝ) (x : ℝ) : ℝ :=
  (-M.δ1d - M.lam w x) / (2 * M.γ1d)

/-- p. 18: the larger root `r₂ = (-δ_{1d} + λ) / (2 γ_{1d})` of `g(z) = x` (used for `x > g*`). -/
noncomputable def r2 (w : Fin d' → ℝ) (x : ℝ) : ℝ :=
  (-M.δ1d + M.lam w x) / (2 * M.γ1d)

/-- p. 16: `Y₁ = c₂ + ∑_{j<d} (δ_{2j} Z_j + γ_{2j} Z_j²) + δ_{2d} r₁ + γ_{2d} r₁²` (for `x > g*`). -/
noncomputable def Y1 (w : Fin d' → ℝ) (x : ℝ) : ℝ :=
  M.eta w + M.δ2d * M.r1 w x + M.γ2d * M.r1 w x ^ 2

/-- p. 16: `Y₂ = c₂ + ∑_{j<d} (δ_{2j} Z_j + γ_{2j} Z_j²) + δ_{2d} r₂ + γ_{2d} r₂²` (for `x > g*`). -/
noncomputable def Y2 (w : Fin d' → ℝ) (x : ℝ) : ℝ :=
  M.eta w + M.δ2d * M.r2 w x + M.γ2d * M.r2 w x ^ 2

/-- Lemma 5, p. 15, and Step 2, p. 18: `q₁ = f_d(r₁)/λ` when `x > g*`, `q₁ = 0` when `x ≤ g*`;
`f_d` is the standard normal density. -/
noncomputable def q1 (w : Fin d' → ℝ) (x : ℝ) : ℝ :=
  if M.gStar w < x then gaussianPDFReal 0 1 (M.r1 w x) / M.lam w x else 0

/-- Lemma 5, p. 15, and Step 2, p. 18: `q₂ = f_d(r₂)/λ` when `x > g*`, `q₂ = 0` when `x ≤ g*`. -/
noncomputable def q2 (w : Fin d' → ℝ) (x : ℝ) : ℝ :=
  if M.gStar w < x then gaussianPDFReal 0 1 (M.r2 w x) / M.lam w x else 0

/-- p. 19: `Q(y, x) = I{Y₁ ≤ y} q₁ + I{Y₂ ≤ y} q₂`. When `x ≤ g*` the paper sets `Y_ℓ = +∞` and
`q_ℓ = 0`; both summands are then `0`, as here (`q_ℓ = 0` whatever `Y_ℓ` is). -/
noncomputable def Qy (y x : ℝ) (w : Fin d' → ℝ) : ℝ :=
  (if M.Y1 w x ≤ y then M.q1 w x else 0) + (if M.Y2 w x ≤ y then M.q2 w x else 0)

/-- p. 19: `Q(x) = q₁ + q₂`. -/
noncomputable def Qx (x : ℝ) (w : Fin d' → ℝ) : ℝ :=
  M.q1 w x + M.q2 w x

end DeltaGamma

/-- The law of `W = (Z_1, …, Z_{d-1})`: i.i.d. standard normal coordinates. -/
noncomputable def stdW (d' : ℕ) : Measure (Fin d' → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

/-- The law of `Z = (W, Z_d)`: `d = d' + 1` i.i.d. standard normal factors. -/
noncomputable def lawZ (d' : ℕ) : Measure ((Fin d' → ℝ) × ℝ) :=
  (stdW d').prod (gaussianReal 0 1)

/-- The law of the pair of losses `(X, Y)` of the delta-gamma model under `Z ~ N(0, I_d)`. -/
noncomputable def lawXY {d' : ℕ} (M : DeltaGamma d') : Measure (ℝ × ℝ) :=
  (lawZ d').map (fun p => (M.X p.1 p.2, M.Y p.1 p.2))

/-- p. 14: `P_ε = Pr{|X - x| ≤ ε | Z_1, …, Z_{d-1}}`, at `W = w`. -/
noncomputable def Peps {d' : ℕ} (M : DeltaGamma d') (x : ℝ) (w : Fin d' → ℝ) (ε : ℝ) : ℝ :=
  (gaussianReal 0 1 {z | |M.X w z - x| ≤ ε}).toReal

/-- p. 14 / Equation (3): the ratio `Pr{Y ≤ y, |X - x| ≤ ε} / Pr{|X - x| ≤ ε}` under `Z ~ N(0, I_d)`,
whose limit as `ε → 0⁺` is `Pr{Y ≤ y | X = x}`. -/
noncomputable def condRatio {d' : ℕ} (M : DeltaGamma d') (y x ε : ℝ) : ℝ :=
  (lawZ d' {p | M.Y p.1 p.2 ≤ y ∧ |M.X p.1 p.2 - x| ≤ ε}).toReal /
    (lawZ d' {p | |M.X p.1 p.2 - x| ≤ ε}).toReal

/-- p. 19: `E[Q(y, x)]`, the expectation over `W ~ N(0, I_{d-1})`. -/
noncomputable def EQy {d' : ℕ} (M : DeltaGamma d') (y x : ℝ) : ℝ :=
  ∫ w, M.Qy y x w ∂(stdW d')

/-- p. 19: `E[Q(x)]`, the expectation over `W ~ N(0, I_{d-1})`. -/
noncomputable def EQ {d' : ℕ} (M : DeltaGamma d') (x : ℝ) : ℝ :=
  ∫ w, M.Qx x w ∂(stdW d')

/-- Assumption 2, p. 20: `E[Q(x)]` and, for `y ∈ 𝒴`, `E[Q(y, x)]` are (finite and) twice
differentiable functions of `x ∈ ℝ`. Finiteness is stated as integrability. -/
def Assumption2 {d' : ℕ} (M : DeltaGamma d') (𝒴 : Set ℝ) : Prop :=
  (∀ x, Integrable (M.Qx x) (stdW d')) ∧
  (∀ y ∈ 𝒴, ∀ x, Integrable (M.Qy y x) (stdW d')) ∧
  Differentiable ℝ (EQ M) ∧ Differentiable ℝ (deriv (EQ M)) ∧
  ∀ y ∈ 𝒴, Differentiable ℝ (EQy M y) ∧ Differentiable ℝ (deriv (EQy M y))

/-- §4.2.2, Steps 1–2: the two-stage sample on one probability space. `Z1 i` (first stage) are
i.i.d. `N(0, I_d)` draws of `(W, Z_d)`, `W2 k` (second stage) are i.i.d. `N(0, I_{d-1})` draws of
`(Z_1, …, Z_{d-1})`, and the two stages are independent: the pairs `(Z1 i, W2 i)` are independent
across `i`, each with the product law. -/
def IsTwoStageSample {d' : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z1 : ℕ → Ω → (Fin d' → ℝ) × ℝ) (W2 : ℕ → Ω → Fin d' → ℝ) : Prop :=
  (∀ i, Measurable (fun ω => (Z1 i ω, W2 i ω))) ∧
  iIndepFun (fun i ω => (Z1 i ω, W2 i ω)) P ∧
  ∀ i, P.map (fun ω => (Z1 i ω, W2 i ω)) = (lawZ d').prod (stdW d')

/-- Step 1, p. 18: `ṽ_α = X_{(⌈α n₁⌉)}`, the `⌈α n₁⌉`-th order statistic of the first-stage losses
`X(Z1 0), …, X(Z1 (n₁-1))`; `0` when `n₁ = 0`. -/
noncomputable def vTilde {d' : ℕ} (M : DeltaGamma d') {Ω : Type*}
    (Z1 : ℕ → Ω → (Fin d' → ℝ) × ℝ) (α : ℝ) (n1 : ℕ) (ω : Ω) : ℝ :=
  if h : 0 < n1 then
    ImpactInvesting.Portfolio.orderStat (fun i : Fin n1 => M.X (Z1 i ω).1 (Z1 i ω).2)
      (CoVaRMC.Batching.rankIdx α n1 h)
  else 0

/-- Equations (25)–(26), p. 19: `F̃_{n₂}(y, x) = ((1/n₂) ∑_{k=1}^{n₂} Q_k(y, x)) / ((1/n₂) ∑_{k=1}^{n₂} Q_k(x))`
over the second-stage draws `W2 0, …, W2 (n₂-1)` (Lean's `0/0 = 0` when every `q̃` vanishes). -/
noncomputable def Ftilde {d' : ℕ} (M : DeltaGamma d') {Ω : Type*} (W2 : ℕ → Ω → Fin d' → ℝ)
    (n2 : ℕ) (y x : ℝ) (ω : Ω) : ℝ :=
  ((n2 : ℝ)⁻¹ * ∑ k ∈ Finset.range n2, M.Qy y x (W2 k ω)) /
    ((n2 : ℝ)⁻¹ * ∑ k ∈ Finset.range n2, M.Qx x (W2 k ω))

/-- p. 20: `Ỹ^IS = inf{y ∈ ℝ : F̃_{n₂}(y, ṽ_α) ≥ β}`, the IS-inspired estimator of `CoVaR_{α,β}`
(Lean's `sInf ∅ = 0` on the event that every `q̃` vanishes). -/
noncomputable def YIS {d' : ℕ} (M : DeltaGamma d') {Ω : Type*} (Z1 : ℕ → Ω → (Fin d' → ℝ) × ℝ)
    (W2 : ℕ → Ω → Fin d' → ℝ) (α β : ℝ) (n1 n2 : ℕ) (ω : Ω) : ℝ :=
  sInf {y : ℝ | β ≤ Ftilde M W2 n2 y (vTilde M Z1 α n1 ω) ω}

end CoVaRMC.Batching.Supplement


