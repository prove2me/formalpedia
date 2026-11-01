-- Prove2me | Definitions.Def_CovariateSAA_Assumptions
-- name    : CovariateSAA_Assumptions
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:29:11.025442+00:00
-- url     : https://prove2.me/theorems/67fa0565-47c1-41be-8839-fe5cbfba3612
-- title:
--   Uniform convergence in probability and Assumptions 1–5
-- statement:
--   Let $(\Omega,P)$ carry the data of the covariate model and let $P_X$ be the covariate distribution. Write $\xrightarrow{p}$ for convergence in probability.
--
--   **Uniform convergence in probability.** Random functions $h_n(\cdot)$ converge to $h$ in probability uniformly on $\mathcal Z$ when $\sup_{z\in\mathcal Z}|h_n(z)-h(z)|\xrightarrow{p}0$, that is, for every $\kappa>0$,
--   $$
--   P\bigl\{\exists z\in\mathcal Z : |h_n(z)-h(z)|>\kappa\bigr\}\to 0 .
--   $$
--
--   1. **Assumption 1.** For each $z\in\mathcal Z$, $|c(z,\bar y)-c(z,y)|\le L(z)\|\bar y-y\|$ for all $y,\bar y\in\mathcal Y$, with Lipschitz constants $L(z)\ge0$ and $\sup_{z\in\mathcal Z}L(z)<+\infty$.
--   2. **Assumption 2.** For a.e. $x$, $g^*_n(\cdot;x)\to g(\cdot;x)$ in probability uniformly on $\mathcal Z$.
--   3. **Assumption 3.** $\frac1n\sum_{i=1}^n\|Q^*(x^i)\|^4$ and $\frac1n\sum_{i=1}^n\|[Q^*(x^i)]^{-1}\|^2$ converge in probability to finite constants (the paper's $\mathbb E[\|Q^*(X)\|^4]$ and $\mathbb E[\|[Q^*(X)]^{-1}\|^2]$).
--   4. **Assumption 4.** $\frac1n\sum_{i=1}^n\|\varepsilon^i\|^4$ converges in probability to a finite constant (the paper's $\mathbb E[\|\varepsilon\|^4]$).
--   5. **Assumption 5.** (5a) $\hat f_n(x)\xrightarrow{p}f^*(x)$ for a.e. $x$; (5b) $\frac1n\sum_{i=1}^n\|f^*(x^i)-\hat f_n(x^i)\|^2\xrightarrow{p}0$; (5c) $\hat Q_n(x)\xrightarrow{p}Q^*(x)$ for a.e. $x$; (5d) $\frac1n\sum_{i=1}^n\|[\hat Q_n(x^i)]^{-1}-[Q^*(x^i)]^{-1}\|^2\xrightarrow{p}0$.
--
--   Proposition 4 and Theorem 5 are stated under these assumptions.
--
--   **Formalization Note** Convergence in probability is `TendstoInMeasure`, which evaluates $P$ on arbitrary sets (outer measure), so no measurability is required. The limits in Assumptions 3–4 are unnamed real constants, so an infinite moment cannot be mistaken for the Bochner-integral default value $0$. "a.e. $x$" is $P_X$-almost every $x$. The Lipschitz constant $L$ is an explicit argument of Assumption 1.
-- source:
--   Kannan, Bayraksan & Luedtke, Data-Driven Sample Average Approximation with Covariate Information, arXiv:2207.13554v1, Assumption 1 p.9, Assumptions 2–5 p.11, uniform convergence in probability p.11–12

import Mathlib
import Definitions.Def_CovariateSAA_Setting

open MeasureTheory Filter Topology

namespace CovariateSAA

variable {dx dy dz : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- Uniform convergence in probability on a set `Z` (arXiv:2207.13554v1, Assumption 2, p.11,
and Proposition 4, p.12): the random functions `h n ω` converge to `h₀` in probability
uniformly on `Z`, i.e. `sup_{z ∈ Z} |h_n(z) − h₀(z)| →p 0`. Written in event form: for every
`κ > 0`, `P{∃ z ∈ Z, |h_n(z) − h₀(z)| > κ} → 0`.

**Formalization Note** The event `{sup_{z∈Z} |h_n(z) − h₀(z)| > κ}` equals
`{∃ z ∈ Z, |h_n(z) − h₀(z)| > κ}`, so this is the paper's notion without the real `⨆` (which
Lean sets to `0` on unbounded sets). `P` is applied to arbitrary sets (outer measure); no
measurability of the event is required. -/
def UnifTendstoInProb {E : Type*} (P : Measure Ω) (h : ℕ → Ω → E → ℝ) (h₀ : E → ℝ)
    (Z : Set E) : Prop :=
  ∀ κ : ℝ, 0 < κ → Tendsto (fun n => P {ω | ∃ z ∈ Z, κ < |h n ω z - h₀ z|}) atTop (𝓝 0)

/-- Assumption 1 (arXiv:2207.13554v1, p.9): for each `z ∈ 𝒵`, `c(z, ·)` is Lipschitz on `𝒴`,
`|c(z, ȳ) − c(z, y)| ≤ L(z) ‖ȳ − y‖` for all `y, ȳ ∈ 𝒴`, with `sup_{z ∈ 𝒵} L(z) < +∞`.

**Formalization Note** `ȳ` is written `y'`. The Lipschitz constant `L` is an explicit argument;
`sup_{z∈𝒵} L(z) < +∞` is `BddAbove (L '' Z)`. A Lipschitz constant is nonnegative, which is stated
because a negative `L z` is otherwise allowed when `𝒴` has at most one point, and it makes
Lemma 1 false. -/
def Assumption1 (c : Vec dz → Vec dy → ℝ) (Z : Set (Vec dz)) (𝒴 : Set (Vec dy))
    (L : Vec dz → ℝ) : Prop :=
  BddAbove (L '' Z) ∧ (∀ z ∈ Z, 0 ≤ L z) ∧
    ∀ z ∈ Z, ∀ y ∈ 𝒴, ∀ y' ∈ 𝒴, |c z y' - c z y| ≤ L z * ‖y' - y‖

/-- Assumption 2 (arXiv:2207.13554v1, p.11): for `P_X`-a.e. `x`, the FI-SAA objectives
`g*_n(·; x)` of (2) converge in probability to `g(·; x)` of (1) uniformly on `𝒵`. -/
def Assumption2 (P : Measure Ω) (PX : Measure (Vec dx)) (Pε : Measure (Vec dy))
    (D : Data dx dy Ω) (c : Vec dz → Vec dy → ℝ) (Z : Set (Vec dz)) : Prop :=
  ∀ᵐ x ∂PX, UnifTendstoInProb P (fun n ω z => gFI D c x n ω z) (gTrue D Pε c x) Z

/-- Assumption 3 (arXiv:2207.13554v1, p.11): the weak LLNs
`(1/n) Σ ‖Q*(xⁱ)‖⁴ →p E[‖Q*(X)‖⁴]` and `(1/n) Σ ‖[Q*(xⁱ)]⁻¹‖² →p E[‖[Q*(X)]⁻¹‖²]`.

**Formalization Note** The limits are finite real constants `m` that are not named: the paper's
expectations are such constants, and naming them by a Bochner integral would silently turn an
infinite moment into `0`. `[·]⁻¹` is `Ring.inverse`; norms are operator norms. -/
def Assumption3 (P : Measure Ω) (D : Data dx dy Ω) : Prop :=
  (∃ m : ℝ, TendstoInMeasure P
      (fun n ω => empMean n (fun i => ‖D.Qstar (D.xs i ω)‖ ^ 4)) atTop (fun _ => m)) ∧
  (∃ m : ℝ, TendstoInMeasure P
      (fun n ω => empMean n (fun i => ‖Ring.inverse (D.Qstar (D.xs i ω))‖ ^ 2)) atTop
      (fun _ => m))

/-- Assumption 4 (arXiv:2207.13554v1, p.11): the weak LLN `(1/n) Σ ‖εⁱ‖⁴ →p E[‖ε‖⁴]`, the limit
being a finite real constant (see `Assumption3`). -/
def Assumption4 (P : Measure Ω) (D : Data dx dy Ω) : Prop :=
  ∃ m : ℝ, TendstoInMeasure P
    (fun n ω => empMean n (fun i => ‖D.eps i ω‖ ^ 4)) atTop (fun _ => m)

/-- Assumption 5 (arXiv:2207.13554v1, p.11): consistency of the regression estimates,
(5a) `f̂_n(x) →p f*(x)` for a.e. `x`;
(5b) `(1/n) Σ ‖f*(xⁱ) − f̂_n(xⁱ)‖² →p 0`;
(5c) `Q̂_n(x) →p Q*(x)` for a.e. `x` (operator norm);
(5d) `(1/n) Σ ‖[Q̂_n(xⁱ)]⁻¹ − [Q*(xⁱ)]⁻¹‖² →p 0`. -/
def Assumption5 (P : Measure Ω) (PX : Measure (Vec dx)) (D : Data dx dy Ω) : Prop :=
  (∀ᵐ x ∂PX, TendstoInMeasure P (fun n ω => D.fhat n ω x) atTop (fun _ => D.fstar x)) ∧
  TendstoInMeasure P
    (fun n ω => empMean n (fun i => ‖D.fstar (D.xs i ω) - D.fhat n ω (D.xs i ω)‖ ^ 2)) atTop
    (fun _ => 0) ∧
  (∀ᵐ x ∂PX, TendstoInMeasure P (fun n ω => D.Qhat n ω x) atTop (fun _ => D.Qstar x)) ∧
  TendstoInMeasure P
    (fun n ω => empMean n (fun i =>
      ‖Ring.inverse (D.Qhat n ω (D.xs i ω)) - Ring.inverse (D.Qstar (D.xs i ω))‖ ^ 2)) atTop
    (fun _ => 0)

end CovariateSAA


