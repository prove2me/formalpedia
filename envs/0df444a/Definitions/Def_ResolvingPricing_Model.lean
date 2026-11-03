-- Prove2me | Definitions.Def_ResolvingPricing_Model
-- name    : ResolvingPricing_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:56.365977+00:00
-- url     : https://prove2.me/theorems/3b1ea74c-04ba-49a4-8802-ffc7fb35984c
-- title:
--   Single-product price-based revenue management model and Assumptions A1–A5
-- statement:
--   A seller sells one product over a finite horizon. In each period it chooses a **demand rate** $\lambda$ in an interval $[\underline d,\bar d]$ and posts the price $g(\lambda)=f^{-1}(\lambda)$, where $f$ is the mean demand function. The realized demand is $\lambda+\xi$, where the **demand noise** $\xi$ has law $Q(\lambda)$ (the paper's $Q(f^{-1}(\lambda))$). The **revenue rate** is
--   $$r(\lambda)=\lambda\, f^{-1}(\lambda),\qquad \lambda\in[\underline d,\bar d],$$
--   with maximizer $\lambda^u$ and maximum $r^u=r(\lambda^u)$. The model carries constants $m,M,C,L,B_\xi$.
--
--   The **assumptions** (A1–A5 of the paper, plus nonnegative demand) are:
--   1. $0\le\underline d<\bar d$; prices are nonnegative and $f^{-1}$ is strictly decreasing (A1).
--   2. $r''\le -m$ on $[\underline d,\bar d]$ with $m>0$, so $r$ is strictly concave there, and $\lambda^u\in(\underline d,\bar d)$ maximizes $r$ (A2).
--   3. $r'''$ exists with $|r'''|\le M$, and $|r(\lambda)-r(\lambda')|\le C|\lambda-\lambda'|$ with $C>0$ (A3).
--   4. Each $Q(\lambda)$ is a probability measure with mean $0$ and $|\xi|\le B_\xi$ almost surely (A4).
--   5. $\mathcal W_2(Q(\lambda),Q(\lambda'))\le L|\lambda-\lambda'|$ with $L>0$ (A5), where $\mathcal W_2$ is the $L^2$-Wasserstein distance.
--   6. Demand is nonnegative: $\lambda+\xi\ge0$ for $Q(\lambda)$-almost every $\xi$.
--
--   The definition also provides the one-sided derivatives $r',r'',r'''$ on $[\underline d,\bar d]$ and the fluid rate $\tilde r(x)=r(\min\{x,\lambda^u\})$ for $x\ge\underline d$, extended by $\tilde r(x)=x\,f^{-1}(\underline d)$ below $\underline d$ (used in Lemma 2).
--
--   This is the model in which every statement of the mission is posed.
--
--   **Formalization Note** Prices are encoded by demand rates, the paper's own parametrization in its Bellman equation (5). A1 is stated on $f^{-1}$ as strict decrease on $(\underline d,\bar d]$, which covers $\bar p=+\infty$. Derivatives are `iteratedDerivWithin` on $[\underline d,\bar d]$, with the differentiability of $r,r',r''$ stated explicitly; strict concavity is not a separate condition because it follows from $r''\le-m<0$. $\mathcal W_2$ is the published `WassersteinDRO.StrongDuality.wasserstein 2`, valued in $[0,\infty]$. The conditional part of A4 (the law of the noise given the past) is part of the definition of a run.
-- source:
--   Y. Wang, H. Wang, Constant Regret Resolving Heuristics for Price-Based Revenue Management, Oper. Res. 70(6):3538–3557 (2022), doi:10.1287/opre.2021.2219, §1 p.3538 (model (1)–(3)); §3 p.3541 (Assumptions A1–A5, λᵘ and rᵘ); Table 1 p.3542; Lemma 2 p.3544 (r(min{x, λᵘ}))

import Mathlib
import Definitions.Def_WassersteinDRO_StrongDuality_wasserstein

open MeasureTheory

namespace ResolvingPricing

/-- **The single-product price-based revenue management model (data).**
Y. Wang, H. Wang, *Constant Regret Resolving Heuristics for Price-Based Revenue Management*,
Oper. Res. 70(6) (2022), §1, p.3538 (model (1)–(3)) and §3, p.3541 (Assumptions A1–A5).

* `dlo`, `dhi` are the demand-rate bounds `d̲ = f(p̄)` and `d̄ = f(p̲)`;
* `g` is the inverse demand function `f⁻¹`: the price posted to obtain the demand rate `λ`;
* `Q λ` is the law of the demand noise when the posted price is `f⁻¹(λ)` (the paper's `Q(f⁻¹(λ))`);
* `m`, `M`, `C`, `L`, `Bξ` are the constants of A2, A3 (both `M` and the Lipschitz constant `C`),
  A5 and A4;
* `lamU` is the unconstrained maximizer `λᵘ` of the revenue rate.

**Formalization Note.** Prices are encoded by demand rates: a policy picks `λ ∈ [d̲, d̄]` and posts
the price `g λ = f⁻¹(λ)`; this is the paper's own parametrization in (5). The noise law is indexed by
the demand rate, so `Q λ` is the paper's `Q(f⁻¹(λ))`. The constants and `λᵘ` are data; their
properties are the fields of `Model.Assumptions`. -/
structure Model where
  /-- `d̲`, the lowest demand rate. -/
  dlo : ℝ
  /-- `d̄`, the highest demand rate. -/
  dhi : ℝ
  /-- `f⁻¹`, the price as a function of the demand rate. -/
  g : ℝ → ℝ
  /-- `Q(f⁻¹(λ))`, the law of the demand noise at demand rate `λ`. -/
  Q : ℝ → Measure ℝ
  /-- The strong-concavity constant `m` of A2. -/
  m : ℝ
  /-- The bound `M` on `|r‴|` of A3. -/
  M : ℝ
  /-- The Lipschitz constant `C` of `r` in A3. -/
  C : ℝ
  /-- The Wasserstein-Lipschitz constant `L` of A5. -/
  L : ℝ
  /-- The almost-sure bound `B_ξ` on the noise of A4. -/
  Bξ : ℝ
  /-- `λᵘ`, the maximizer of the revenue rate. -/
  lamU : ℝ

namespace Model

/-- The demand-rate domain `𝒟 = [d̲, d̄]`. -/
def D (P : Model) : Set ℝ := Set.Icc P.dlo P.dhi

/-- The revenue rate `r(λ) = λ f⁻¹(λ)` (A2, p.3541). -/
def r (P : Model) (d : ℝ) : ℝ := d * P.g d

/-- `r′`, the first derivative of `r` within `[d̲, d̄]` (one-sided at the endpoints). -/
noncomputable def r1 (P : Model) : ℝ → ℝ := iteratedDerivWithin 1 P.r P.D

/-- `r″`, the second derivative of `r` within `[d̲, d̄]`. -/
noncomputable def r2 (P : Model) : ℝ → ℝ := iteratedDerivWithin 2 P.r P.D

/-- `r‴`, the third derivative of `r` within `[d̲, d̄]`. -/
noncomputable def r3 (P : Model) : ℝ → ℝ := iteratedDerivWithin 3 P.r P.D

/-- `rᵘ = r(λᵘ)`, the unconstrained optimal revenue rate (p.3541). -/
def ru (P : Model) : ℝ := P.r P.lamU

/-- The fluid revenue rate `r(min{x, λᵘ})` at normalized inventory `x`, used in Lemma 2, extended
below `d̲` by `x f⁻¹(d̲)` (the revenue of selling all `x` per period at the highest price).

**Formalization Note.** For `x ≥ d̲` this is the paper's `r(min{x, λᵘ})`. For `0 ≤ x < d̲` the printed
term evaluates `r` outside its domain `[d̲, d̄]`; this extension is the correction used in Lemma 2. -/
noncomputable def rtilde (P : Model) (x : ℝ) : ℝ :=
  if P.dlo ≤ x then P.r (min x P.lamU) else x * P.g P.dlo

/-- **Assumptions A1–A5 of the single-product model**, Wang & Wang, Oper. Res. 70(6) (2022), §3,
p.3541, together with the nonnegativity of demand implicit in (1), p.3538.

1. *Domain.* `0 ≤ d̲ < d̄` (`f` takes values in `ℝ₊` and is strictly decreasing).
2. *A1 (monotonicity).* Prices are nonnegative (`𝒫 ⊂ ℝ₊`, §1) and `f⁻¹` is strictly decreasing.
3. *A2 (strict concavity).* `r″ ≤ −m` on `[d̲, d̄]` with `m > 0` (so `r` is strictly concave there), and
   the maximizer `λᵘ` of `r` over `[d̲, d̄]` lies in `(d̲, d̄)`.
4. *A3 (smoothness).* `r‴` exists and `|r‴| ≤ M` on `[d̲, d̄]`; `|r(λ) − r(λ′)| ≤ C|λ − λ′|` with `C > 0`.
5. *A4 (martingale difference noise).* At each demand rate the noise law is a probability measure
   with mean `0` and `|ξ| ≤ B_ξ` almost surely.
6. *A5 (bounded Wasserstein distance).* `𝒲₂(Q(p), Q(p′)) ≤ L|f(p) − f(p′)|` with `L > 0`.
7. *Nonnegative demand.* `λ + ξ ≥ 0` almost surely under `Q(f⁻¹(λ))`.

**Formalization Note.** A1 is stated on `f⁻¹`: `StrictAntiOn g (Ioc d̲ d̄)` (open at `d̲` because with
`p̄ = +∞` the price at `d̲` is not a real number; when `d̲ > 0` the value `g d̲` is pinned by the
continuity of `r` at `d̲`, and when `d̲ = 0` it only enters through `r(0) = 0`). The derivatives are
`iteratedDerivWithin k r [d̲, d̄]`, and "the third derivative exists" is the differentiability of
`r`, `r′`, `r″` within `[d̲, d̄]`. A2's strict concavity of `r` is not a separate field: it follows from
`r″ ≤ −m < 0` and these differentiability conditions. `𝒲₂` is the published `WassersteinDRO.StrongDuality.wasserstein 2`
in `ℝ≥0∞`; `|f(p) − f(p′)| = |λ − λ′|` because `λ = f(p)`. The conditional part of A4 (the law of
`ξ_t` given the past is `Q(p_t)`) is a field of `Run`. -/
structure Assumptions (P : Model) : Prop where
  dlo_nonneg : 0 ≤ P.dlo
  dlo_lt_dhi : P.dlo < P.dhi
  /-- A1, with `𝒫 ⊂ ℝ₊`. -/
  g_nonneg : ∀ d ∈ P.D, 0 ≤ P.g d
  /-- A1. -/
  g_strictAnti : StrictAntiOn P.g (Set.Ioc P.dlo P.dhi)
  /-- A2. -/
  m_pos : 0 < P.m
  /-- A2–A3: `r`, `r′`, `r″` are differentiable within `[d̲, d̄]`. -/
  r_differentiable : ∀ k ≤ 2, DifferentiableOn ℝ (iteratedDerivWithin k P.r P.D) P.D
  r2_le : ∀ d ∈ P.D, P.r2 d ≤ -P.m
  lamU_mem : P.lamU ∈ Set.Ioo P.dlo P.dhi
  lamU_isMax : IsMaxOn P.r P.D P.lamU
  /-- A3. -/
  r3_le : ∀ d ∈ P.D, |P.r3 d| ≤ P.M
  C_pos : 0 < P.C
  r_lipschitz : ∀ d ∈ P.D, ∀ d' ∈ P.D, |P.r d - P.r d'| ≤ P.C * |d - d'|
  /-- A4. -/
  Q_prob : ∀ d ∈ P.D, IsProbabilityMeasure (P.Q d)
  Q_mean : ∀ d ∈ P.D, ∫ e, e ∂(P.Q d) = 0
  Q_bdd : ∀ d ∈ P.D, ∀ᵐ e ∂(P.Q d), |e| ≤ P.Bξ
  /-- A5. -/
  L_pos : 0 < P.L
  Q_wasserstein : ∀ d ∈ P.D, ∀ d' ∈ P.D,
    WassersteinDRO.StrongDuality.wasserstein 2 (P.Q d) (P.Q d') ≤ ENNReal.ofReal (P.L * |d - d'|)
  /-- Nonnegative demand, implicit in (1). -/
  demand_nonneg : ∀ d ∈ P.D, ∀ᵐ e ∂(P.Q d), 0 ≤ d + e

end Model

end ResolvingPricing


