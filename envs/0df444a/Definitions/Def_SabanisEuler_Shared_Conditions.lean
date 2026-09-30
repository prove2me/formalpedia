-- Prove2me | Definitions.Def_SabanisEuler_Shared_Conditions
-- name    : SabanisEuler_Shared_Conditions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T22:48:32.191833+00:00
-- url     : https://prove2.me/theorems/b0406f02-e7f1-4b7a-a712-9960fcbd387e
-- title:
--   Conditions A-1–A-6 on (2.1) and B-2, B-3 on the scheme coefficients
-- statement:
--   The standing conditions of Sabanis (2016), §2, on the coefficients $b:[0,\infty)\times\mathbb R^d\to\mathbb R^d$, $\sigma:[0,\infty)\times\mathbb R^d\to\mathbb R^{d\times d_1}$ of the SDE (2.1), on the coefficient sequences $b_n,\sigma_n$ of the scheme (2.2), and on the initial value $X(0)=\xi$. Here $p_0,p_1\ge2$, $T>0$, $xy$ is the scalar product and $|\cdot|$ the Euclidean (resp. Hilbert–Schmidt) norm.
--
--   1. **A-1.** $x\mapsto b(t,x)$ is continuous for every $t\in[0,T]$.
--   2. **A-2.** For every $R\ge0$ there is a constant $N_R$ with $\sup_{|x|\le R}|b(t,x)|\le N_R$ for all $t\in[0,T]$.
--   3. **A-3.** For every $R>0$ there is $L_R>0$ such that for all $t\in[0,T]$ and $|x|,|y|\le R$,
--   $$2(x-y)(b(t,x)-b(t,y))+(p_1-1)|\sigma(t,x)-\sigma(t,y)|^2\le L_R|x-y|^2.$$
--   4. **A-4.** There is $K>0$ with $2xb(t,x)+(p_0-1)|\sigma(t,x)|^2\le K(1+|x|^2)$ for all $t\in[0,T]$, $x\in\mathbb R^d$.
--   5. **A-5.** $\mathbb E[|X(0)|^{p_0}]<\infty$.
--   6. **A-6** (for a given exponent $l$). $l>0$, and there is $L>0$ such that for all $t\in[0,T]$ and all $x,y\in\mathbb R^d$,
--   $$2(x-y)(b(t,x)-b(t,y))+(p_1-1)|\sigma(t,x)-\sigma(t,y)|^2\le L|x-y|^2,\qquad |b(t,x)-b(t,y)|\le L(1+|x|^l+|y|^l)|x-y|.$$
--   7. **B-2** (for a given $\alpha$). There is a constant $C$ such that for every $n\ge1$, $t\in[0,T]$, $x\in\mathbb R^d$,
--   $$|b_n(t,x)|\le\min\big(Cn^{\alpha}(1+|x|),|b(t,x)|\big),\qquad|\sigma_n(t,x)|^2\le\min\big(Cn^{\alpha}(1+|x|^2),|\sigma(t,x)|^2\big).$$
--   8. **B-3.** There is $K>0$ such that for every $n\ge1$, $t\in[0,T]$, $x\in\mathbb R^d$, $2xb_n(t,x)+(p_0-1)|\sigma_n(t,x)|^2\le K(1+|x|^2)$.
--
--   A-1–A-5 are local monotonicity, coercivity and moment conditions on the SDE; A-6 is the global monotonicity condition with a drift that is locally Lipschitz with polynomially growing constant; B-2 and B-3 say that the scheme's coefficients grow at most like $n^\alpha$ times a linear function while never exceeding the original coefficients, and satisfy the coercivity condition uniformly in $n$.
--
--   **Formalization Note** Each condition is a separate proposition carrying its own existential constant (the two $K$'s of A-4 and B-3 are unrelated). The exponent $l$ of A-6 is a parameter, because the tamed coefficients (2.11)–(2.12) and the 𝔭-condition use the same $l$; $|x|^l$ is the real power. The range $\alpha\in(0,1/2]$ of B-2 is imposed by the theorems that use it. Condition B-1 of the paper is not needed by the statements of this mission and is not formalized here.
--
--   **Shared definition.** Serves chunks `02-rate` (conditions A-1–A-6, B-2, B-3, eqs. (2.4)–(2.5), pp. 3–5; previously `SabanisEuler.Rate.Conditions`) and `03-uniform-rate` (same conditions and pages; previously `SabanisEuler.UniformRate.Conditions`). Both copies were identical up to their namespace: A-1–A-5, A-6 with the exponent $l$ as a parameter, B-2 with $\alpha$ as a parameter, B-3, each with its own existential constant. Chunk `01-lp-convergence` keeps its own conditions item, which has B-1 in place of A-6.
-- source:
--   Sabanis, Euler approximations with varying coefficients, arXiv:1308.1796v4, pp. 3-5, conditions A-1–A-6, B-2, B-3, eqs. (2.4)–(2.5); shared by chunks 02-rate and 03-uniform-rate

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace SabanisEuler.Shared

open EthierKurtz

variable {d d₁ : ℕ}

/-- Sabanis (2016), p. 3, A-1: `b(t, x)` is continuous in `x` for every `t ∈ [0, T]`. -/
def CondA1 (T : ℝ≥0) (b : ℝ≥0 × SDEState d → SDEState d) : Prop :=
  ∀ t ≤ T, Continuous (fun x => b (t, x))

/-- Sabanis (2016), p. 3, A-2: for every `R ≥ 0` there is a constant `N_R` with
`sup_{|x| ≤ R} |b(t, x)| ≤ N_R` for all `t ∈ [0, T]`. -/
def CondA2 (T : ℝ≥0) (b : ℝ≥0 × SDEState d → SDEState d) : Prop :=
  ∀ R : ℝ, 0 ≤ R → ∃ N : ℝ, ∀ t ≤ T, ∀ x : SDEState d, ‖x‖ ≤ R → ‖b (t, x)‖ ≤ N

/-- Sabanis (2016), p. 3, A-3 (local monotonicity): for every `R > 0` there is `L_R > 0`
with `2 (x - y)·(b(t, x) - b(t, y)) + (p₁ - 1) |σ(t, x) - σ(t, y)|² ≤ L_R |x - y|²` for all
`t ∈ [0, T]` and `|x|, |y| ≤ R`. -/
def CondA3 (T : ℝ≥0) (p₁ : ℝ) (b : ℝ≥0 × SDEState d → SDEState d)
    (σ : ℝ≥0 × SDEState d → Diffusion d d₁) : Prop :=
  ∀ R : ℝ, 0 < R → ∃ L : ℝ, 0 < L ∧ ∀ t ≤ T, ∀ x y : SDEState d, ‖x‖ ≤ R → ‖y‖ ≤ R →
    2 * inner ℝ (x - y) (b (t, x) - b (t, y)) + (p₁ - 1) * ‖σ (t, x) - σ (t, y)‖ ^ 2
      ≤ L * ‖x - y‖ ^ 2

/-- Sabanis (2016), p. 3, A-4 (coercivity): there is `K > 0` with
`2 x·b(t, x) + (p₀ - 1) |σ(t, x)|² ≤ K (1 + |x|²)` for all `t ∈ [0, T]`, `x ∈ ℝ^d`. -/
def CondA4 (T : ℝ≥0) (p₀ : ℝ) (b : ℝ≥0 × SDEState d → SDEState d)
    (σ : ℝ≥0 × SDEState d → Diffusion d d₁) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ t ≤ T, ∀ x : SDEState d,
    2 * inner ℝ x (b (t, x)) + (p₀ - 1) * ‖σ (t, x)‖ ^ 2 ≤ K * (1 + ‖x‖ ^ 2)

/-- Sabanis (2016), p. 3, A-5: `𝔼[|X(0)|^{p₀}] < ∞` (expectation as a lower Lebesgue
integral in `[0, ∞]`). -/
def CondA5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (p₀ : ℝ) (ξ : Ω → SDEState d) :
    Prop :=
  ∫⁻ ω, ‖ξ ω‖ₑ ^ p₀ ∂P < ⊤

/-- Sabanis (2016), p. 5, A-6 (global monotonicity, polynomial Lipschitz drift), for a given
exponent `l`: `l > 0`, and there is `L > 0` such that for all `t ∈ [0, T]` and all
`x, y ∈ ℝ^d`,
`2 (x - y)·(b(t, x) - b(t, y)) + (p₁ - 1) |σ(t, x) - σ(t, y)|² ≤ L |x - y|²` and
`|b(t, x) - b(t, y)| ≤ L (1 + |x|^l + |y|^l) |x - y|`.
The exponent `l` is a parameter because the tamed coefficients (2.11)–(2.12) and the
p-condition use the same `l`. -/
def CondA6 (T : ℝ≥0) (p₁ l : ℝ) (b : ℝ≥0 × SDEState d → SDEState d)
    (σ : ℝ≥0 × SDEState d → Diffusion d d₁) : Prop :=
  0 < l ∧ ∃ L : ℝ, 0 < L ∧ ∀ t ≤ T, ∀ x y : SDEState d,
    2 * inner ℝ (x - y) (b (t, x) - b (t, y)) + (p₁ - 1) * ‖σ (t, x) - σ (t, y)‖ ^ 2
      ≤ L * ‖x - y‖ ^ 2 ∧
    ‖b (t, x) - b (t, y)‖ ≤ L * (1 + ‖x‖ ^ l + ‖y‖ ^ l) * ‖x - y‖

/-- Sabanis (2016), p. 3, B-2, eq. (2.4), for a given exponent `α`: there is a constant `C`
such that for every `n ≥ 1`, `t ∈ [0, T]`, `x ∈ ℝ^d`,
`|bₙ(t, x)| ≤ min(C n^α (1 + |x|), |b(t, x)|)` and
`|σₙ(t, x)|² ≤ min(C n^α (1 + |x|²), |σ(t, x)|²)`.
The range `α ∈ (0, 1/2]` is imposed by the theorems that use this condition. -/
def CondB2 (T : ℝ≥0) (α : ℝ) (b : ℝ≥0 × SDEState d → SDEState d)
    (σ : ℝ≥0 × SDEState d → Diffusion d d₁) (bₙ : ℕ → ℝ≥0 × SDEState d → SDEState d)
    (σₙ : ℕ → ℝ≥0 × SDEState d → Diffusion d d₁) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ t ≤ T, ∀ x : SDEState d,
    ‖bₙ n (t, x)‖ ≤ min (C * (n : ℝ) ^ α * (1 + ‖x‖)) ‖b (t, x)‖ ∧
    ‖σₙ n (t, x)‖ ^ 2 ≤ min (C * (n : ℝ) ^ α * (1 + ‖x‖ ^ 2)) (‖σ (t, x)‖ ^ 2)

/-- Sabanis (2016), p. 4, B-3, eq. (2.5): there is `K > 0` such that for every `n ≥ 1`,
`2 x·bₙ(t, x) + (p₀ - 1) |σₙ(t, x)|² ≤ K (1 + |x|²)` for all `t ∈ [0, T]`, `x ∈ ℝ^d`. -/
def CondB3 (T : ℝ≥0) (p₀ : ℝ) (bₙ : ℕ → ℝ≥0 × SDEState d → SDEState d)
    (σₙ : ℕ → ℝ≥0 × SDEState d → Diffusion d d₁) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n → ∀ t ≤ T, ∀ x : SDEState d,
    2 * inner ℝ x (bₙ n (t, x)) + (p₀ - 1) * ‖σₙ n (t, x)‖ ^ 2 ≤ K * (1 + ‖x‖ ^ 2)

end SabanisEuler.Shared


