-- Prove2me | Definitions.Def_ChanceDetEquiv_EModel_Model
-- name    : ChanceDetEquiv_EModel_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:40:45.954859+00:00
-- url     : https://prove2.me/theorems/750f351a-5f20-4e40-86c4-969141794f51
-- title:
--   'E Model' (18), (19b), (21), (27), (29), (30), (34): chance constraints under x = Db, μ_b, μ_c, K_α, σ_i²(D), μ_i(D), the system (29), V(D)
-- statement:
--   This file fixes the objects of Charnes and Cooper's expected-value ('E') model of chance-constrained programming.
--
--   Let $(\Omega,\mathcal F,P)$ be a probability space. The data are a **constant** $m\times n$ matrix $A$ with rows $a_1',\dots,a_m'$, a random right-hand side $b:\Omega\to\mathbb R^m$ and random objective coefficients $c:\Omega\to\mathbb R^n$. A **linear decision rule** is an $n\times m$ real matrix $D$; it sets $x=Db$.
--
--   1. **Means** (19b), (21): $\mu_b=Eb$, $\mu_c=Ec$, componentwise, and $\hat b=b-\mu_b$.
--   2. **The constant $K_\alpha$** (27): $K_\alpha=\Phi^{-1}(\alpha)$, the $\alpha$-quantile of the standard normal law, so that $F^{-1}(\alpha)=-K_\alpha$ for the upper-tail function $F(t)=P(z\ge t)$ of an $N(0,1)$ variate $z$.
--   3. **Chance constraints of (18)**, row by row: $D$ is feasible when
--   $$P\big(a_i'Db\le b_i\big)\ge\alpha_i\qquad(i=1,\dots,m).$$
--   4. **Objectives**: $E(c'Db)$ is maximized in (18); its deterministic mean $\mu_c'D\mu_b$ is negated and minimized in (29).
--   5. **Moment functions** (30): $\sigma_i^2(D)=E(a_i'Db-b_i)^2$, $\mu_i(D)=\mu_{b_i}-a_i'D\mu_b$, and the centred second moment $E[\hat b_i-a_i'D\hat b]^2$ that appears in (22)–(28d).
--   6. **The system (29)** in the variables $(D,v)$, $v\in\mathbb R^m$: for every $i$,
--   $$\mu_i(D)-v_i\ge0,\qquad -K_{\alpha_i}^2\sigma_i^2(D)+K_{\alpha_i}^2\mu_i^2(D)+v_i^2\ge0,\qquad v_i\ge0.$$
--   7. **Normality**: for every decision rule $D$ and every row $i$ the variate $a_i'Db-b_i$ has a normal law $N(\mu,s)$ with $s\ge0$.
--   8. **The V-model functional** (34): $V(D)=E(c'Db-z^0)^2$ for a given real $z^0=c^{0\prime}x^0$.
--
--   These are the objects on which the mission's goal theorem, the equivalence of (18) with the convex program (29), is stated.
--
--   **Formalization Note** Expectations are Bochner integrals, which are $0$ for non-integrable functions; every theorem using them assumes the integrability it needs. $\sigma_i^2(D)$ is the raw second moment exactly as (30) prints it (the footnote to (30) calls it a variance; the identity $\sigma_i^2-\mu_i^2=E[\hat b_i-a_i'D\hat b]^2$ is a separate milestone). $K_\alpha$ uses the published `Cohen2019.Robust.PhiInvReal`, which is meaningful only for $0<\alpha<1$. Normality allows variance $0$ (a point mass), as footnote † of p. 28 does. Probabilities are `P.real`.
-- source:
--   Charnes and Cooper, Deterministic Equivalents for Optimizing and Satisficing under Chance Constraints, Oper. Res. 11 (1963), p. 19 Eq. (3); p. 20 Eq. (5); p. 25 Eq. (18); p. 26 Eqs. (19b), (21); p. 27 Eq. (27) and normality assumption; p. 28 Eqs. (29), (30); p. 30 Eq. (34)

import Mathlib
import Definitions.Def_Cohen2019_Robust_Phi

namespace ChanceDetEquiv.EModel

open MeasureTheory ProbabilityTheory Matrix

/-- **Mean vector** (19b), (21): `μ_b = Eb`, `μ_c = Ec`, componentwise expectations.
Charnes and Cooper, Deterministic Equivalents for Optimizing and Satisficing under Chance
Constraints, Oper. Res. 11 (1963), p. 26, Eqs. (19b), (21).

**Formalization Note.** The expectation is the Bochner integral; it is `0` for a non-integrable
component, so every statement using `meanVec` assumes integrability. -/
noncomputable def meanVec {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {k : ℕ}
    (b : Ω → Fin k → ℝ) : Fin k → ℝ :=
  fun j => ∫ ω, b ω j ∂P

/-- **The constant `K_α`** of (27), p. 27: `F_i⁻¹(α_i) ≡ −K_{α_i}`, where `F_i` is the upper-tail
function `t ↦ P(z_i ≥ t)` of the `N(0,1)` variate `z_i`; hence `K_α = Φ⁻¹(α)`, the standard normal
`α`-quantile, positive for `½ < α < 1`.

**Formalization Note.** `Cohen2019.Robust.PhiInvReal α = inf {t | α ≤ Φ t}`; it is a junk value
outside `0 < α < 1`, so every statement using `K` assumes `½ < α < 1`. -/
noncomputable def K (α : ℝ) : ℝ := Cohen2019.Robust.PhiInvReal α

/-- **The row-wise chance constraints of (18)** under the decision rule `x = Db` of (5):
for every row `i`, `P(a_i'Db ≤ b_i) ≥ α_i` (p. 19, Eq. (3); p. 25, Eq. (18); p. 20, Eq. (5)).
`A` is a constant `m × n` matrix, `b : Ω → ℝ^m` is random, `D` is an `n × m` matrix, and
`a_i'Db = (A (D b))_i`. -/
def IsChanceFeasible18 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Ω → Fin m → ℝ) (α : Fin m → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) : Prop :=
  ∀ i : Fin m, α i ≤ P.real {ω | (A *ᵥ (D *ᵥ b ω)) i ≤ b ω i}

/-- **Objective of (18)**: `E(c'x)` with `x = Db`, i.e. `E(c'Db)` (p. 25, Eq. (18); p. 26,
Eq. (19a)). -/
noncomputable def expectedObjective {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {m n : ℕ}
    (b : Ω → Fin m → ℝ) (c : Ω → Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ∫ ω, c ω ⬝ᵥ (D *ᵥ b ω) ∂P

/-- **Mean functional from (19a)**: `μ_c'Dμ_b` (p. 26, after (19b)).
Program (29) minimizes the negative of this quantity. -/
noncomputable def detObjective {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {m n : ℕ}
    (b : Ω → Fin m → ℝ) (c : Ω → Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  meanVec P c ⬝ᵥ (D *ᵥ meanVec P b)

/-- **`σ_i²(D)` of (30)**, p. 28, as printed: the raw second moment `E(a_i'Db − b_i)²`. -/
noncomputable def sigmaSq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Ω → Fin m → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (i : Fin m) : ℝ :=
  ∫ ω, ((A *ᵥ (D *ᵥ b ω)) i - b ω i) ^ 2 ∂P

/-- **`μ_i(D)` of (29)–(30)**, p. 28: `μ_i(D) = μ_{b_i} − a_i'Dμ_b`; (30) defines its square
`μ_i²(D) = (μ_{b_i} − a_i'Dμ_b)²`. -/
noncomputable def muRow {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Ω → Fin m → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (i : Fin m) : ℝ :=
  meanVec P b i - (A *ᵥ (D *ᵥ meanVec P b)) i

/-- **`E[b̂_i − a_i'Db̂]²`** of (22)–(28d), pp. 27–28, with `b̂ = b − μ_b` of (21): the variance of
the variate `a_i'Db − b_i`. -/
noncomputable def centeredSecondMoment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Ω → Fin m → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (i : Fin m) : ℝ :=
  ∫ ω, ((b ω i - meanVec P b i) - (A *ᵥ (D *ᵥ (b ω - meanVec P b))) i) ^ 2 ∂P

/-- **The constraint system (29)**, p. 28, in the variables `(D, v)`: for every `i = 1, …, m`,
`μ_i(D) − v_i ≥ 0`, `−K²_{α_i} σ_i²(D) + K²_{α_i} μ_i²(D) + v_i² ≥ 0`, `v_i ≥ 0`. -/
def Sys29 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Ω → Fin m → ℝ) (α : Fin m → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (v : Fin m → ℝ) : Prop :=
  ∀ i : Fin m,
    0 ≤ muRow P A b D i - v i ∧
    0 ≤ -(K (α i)) ^ 2 * sigmaSq P A b D i + (K (α i)) ^ 2 * (muRow P A b D i) ^ 2 + (v i) ^ 2 ∧
    0 ≤ v i

/-- **Normality assumption**, p. 27: "we assume that the variate `(a_i'Db − b_i)` is normally
distributed". For every decision rule `D` and every row `i`, the law of `ω ↦ a_i'Db(ω) − b_i(ω)`
is a normal law `N(μ, s)`, with variance `s ≥ 0`; `s = 0` (a point mass) is allowed, as footnote †
of p. 28 accommodates zero variances. -/
def RowsNormal {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Ω → Fin m → ℝ) : Prop :=
  ∀ (D : Matrix (Fin n) (Fin m) ℝ) (i : Fin m), ∃ (μ : ℝ) (s : NNReal),
    P.map (fun ω => (A *ᵥ (D *ᵥ b ω)) i - b ω i) = gaussianReal μ s

/-- **`V(D)` of (34)**, p. 30: `V(D) = E(c'Db − c⁰'x⁰)²`, where `z⁰ = c⁰'x⁰` is a given real
number (the preferred value of the functional). -/
noncomputable def VObjective {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {m n : ℕ}
    (b : Ω → Fin m → ℝ) (c : Ω → Fin n → ℝ) (z0 : ℝ) (D : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ∫ ω, (c ω ⬝ᵥ (D *ᵥ b ω) - z0) ^ 2 ∂P

end ChanceDetEquiv.EModel


