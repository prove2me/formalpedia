-- Prove2me | Definitions.Def_OnlineCarpoolingLei_Oblivious_ConvexOrder
-- name    : OnlineCarpoolingLei_Oblivious_ConvexOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:42:01.798206+00:00
-- url     : https://prove2.me/theorems/860d13d1-c8d0-4b50-9e78-b60249da2856
-- title:
--   Convex domination by $\gamma=N(0,50I_n)$, forcing sets $B_x$ and admissible selections (Definitions 3.1–3.2)
-- statement:
--   Let $\gamma=N(0,50I_n)$ be the centered Gaussian measure on $\mathbb R^n$ with covariance $50$ times the identity, and let $\mathcal C_+$ be the class of finite, nonnegative, convex functions $f:\mathbb R^n\to[0,\infty)$ that are integrable under $\gamma$.
--
--   **Definition 3.1.** For a finitely supported probability measure $\mu$ on $\mathbb R^n$, write $\mu\preceq_{cx}\gamma$ if
--   $$\int f\,d\mu\le\int f\,d\gamma\qquad\text{for every }f\in\mathcal C_+ .$$
--
--   Fix an edge $e=\mathbf 1_u-\mathbf 1_v$. A **selection** for $\mu$ is a function $p:\operatorname{supp}\mu\to[0,1]$; $p(x)$ is the probability of moving from $x$ to $x+e$ rather than to $x-e$, and
--   $$\mu^{p,e}=\sum_{x\in\operatorname{supp}\mu}\mu(\{x\})\big(p(x)\,\delta_{x+e}+(1-p(x))\,\delta_{x-e}\big).\tag{3.1}$$
--   The **forcing sets** are
--   $$B_x=\{0\}\ \text{if}\ \langle x,e\rangle>27,\qquad B_x=\{1\}\ \text{if}\ \langle x,e\rangle<-27,\qquad B_x=[0,1]\ \text{if}\ |\langle x,e\rangle|\le27,\tag{3.2}$$
--   and $B=\prod_{x\in\operatorname{supp}\mu}B_x$.
--
--   **Definition 3.2.** A selection $p\in B$ is **admissible** for $(\mu,e)$ if $\mu^{p,e}\preceq_{cx}\gamma$.
--
--   The forcing sets make the endpoint with smaller discrepancy receive whenever the two discrepancies differ by more than $27$; domination by $\gamma$ is what yields subgaussian tails. Theorem 3.3 asserts that admissible selections exist.
--
--   **Formalization Note** A finitely supported probability measure is given by its weights `μ : (Fin n → ℝ) →₀ ℝ` (nonnegative, summing to $1$, predicate `IsFinProb`); its support is the set of points of positive mass and $\int f\,d\mu=\sum_{x\in\operatorname{supp}\mu}\mu(\{x\})f(x)$ (`lawInt`). `toMeasure μ` is the corresponding measure $\sum_x\mu(\{x\})\delta_x$. $\gamma$ is the product of $n$ copies of $N(0,50)$. Selections are real functions on the support subtype, so the set of selections is the finite-dimensional space $\mathbb R^{\operatorname{supp}\mu}$ with its product topology. The value $27$ itself gives $B_x=[0,1]$.
-- source:
--   Yuhao Lei, STOC 2027 submission #416 (October 2026), Section 2, p.5 (PDF p.5) (γ = N(0, 50 I_n)); Section 3.1, Definitions 3.1 and 3.2, (3.1), (3.2), p.5 (PDF p.5)

import Mathlib
import Definitions.Def_OnlineCarpoolingLei_Oblivious_Model

/-!
Yuhao Lei, *Online carpooling against an oblivious adversary*, STOC 2027 submission #416
(October 2026), §2 (p.5) and §3.1 (p.5): the Gaussian `γ = N(0, 50 Iₙ)`, the test class `C₊`,
Definition 3.1 (`μ ⪯cx γ`), selections, (3.1) `μ^{p,e}`, (3.2) the forcing sets `B_x`, the box
`B`, and Definition 3.2 (admissible selections).

A finitely supported probability measure on `ℝⁿ` is encoded by its weights
`μ : (Fin n → ℝ) →₀ ℝ` (nonnegative, summing to one); its support `μ.support` is the set of
points of positive mass, and `∫ f dμ = ∑_{x ∈ supp μ} μ({x}) f(x)`.
-/

namespace OnlineCarpoolingLei.Oblivious

open MeasureTheory ProbabilityTheory

/-- The centered Gaussian measure `γ = N(0, 50 Iₙ)` on `ℝⁿ`: product of `n` copies of `N(0, 50)`. -/
noncomputable def gamma (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ : Fin n => gaussianReal 0 50

/-- `C₊`: finite (real-valued), nonnegative, convex functions on `ℝⁿ` that are `γ`-integrable. -/
def IsCPlus {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧ ConvexOn ℝ Set.univ f ∧ Integrable f (gamma n)

/-- Weights `μ` describe a finitely supported probability measure on `ℝⁿ`. -/
def IsFinProb {n : ℕ} (μ : (Fin n → ℝ) →₀ ℝ) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ ∑ x ∈ μ.support, μ x = 1

/-- `∫ f dμ = ∑_{x ∈ supp μ} μ({x}) f(x)` for finitely supported weights. -/
def lawInt {n : ℕ} (μ : (Fin n → ℝ) →₀ ℝ) (f : (Fin n → ℝ) → ℝ) : ℝ :=
  ∑ x ∈ μ.support, μ x * f x

/-- Definition 3.1: `μ ⪯cx γ` iff `∫ f dμ ≤ ∫ f dγ` for every `f ∈ C₊`. -/
def CxLeGamma {n : ℕ} (μ : (Fin n → ℝ) →₀ ℝ) : Prop :=
  ∀ f : (Fin n → ℝ) → ℝ, IsCPlus f → lawInt μ f ≤ ∫ x, f x ∂gamma n

/-- The measure `∑_{x ∈ supp μ} μ({x}) δ_x` described by the weights `μ`. -/
noncomputable def toMeasure {n : ℕ} (μ : (Fin n → ℝ) →₀ ℝ) : Measure (Fin n → ℝ) :=
  ∑ x ∈ μ.support, ENNReal.ofReal (μ x) • Measure.dirac x

/-- (3.2) The forcing set `B_x`: `{0}` if `⟨x,e⟩ > 27`, `{1}` if `⟨x,e⟩ < −27`, and `[0,1]`
if `|⟨x,e⟩| ≤ 27`. -/
def forced {n : ℕ} (e : Edge n) (x : Fin n → ℝ) : Set ℝ :=
  if 27 < ip x e.vecR then {0} else if ip x e.vecR < -27 then {1} else Set.Icc 0 1

/-- The box `B = ∏_{x ∈ supp μ} B_x` of selections `p : supp μ → ℝ`. -/
def selBox {n : ℕ} (μ : (Fin n → ℝ) →₀ ℝ) (e : Edge n) : Set (μ.support → ℝ) :=
  {p | ∀ x, p x ∈ forced e x.1}

/-- (3.1) `μ^{p,e} = ∑_{x ∈ supp μ} μ({x}) (p(x) δ_{x+e} + (1 − p(x)) δ_{x−e})`, as weights. -/
noncomputable def pushSel {n : ℕ} (μ : (Fin n → ℝ) →₀ ℝ) (e : Edge n) (p : μ.support → ℝ) :
    (Fin n → ℝ) →₀ ℝ :=
  ∑ x : μ.support,
    (Finsupp.single (x.1 + e.vecR) (μ x.1 * p x) +
      Finsupp.single (x.1 - e.vecR) (μ x.1 * (1 - p x)))

/-- Definition 3.2: the set of selections `p ∈ B` that are admissible for `(μ, e)`, i.e.
`μ^{p,e} ⪯cx γ`. -/
def admissible {n : ℕ} (μ : (Fin n → ℝ) →₀ ℝ) (e : Edge n) : Set (μ.support → ℝ) :=
  {p | p ∈ selBox μ e ∧ CxLeGamma (pushSel μ e p)}

end OnlineCarpoolingLei.Oblivious


