-- Prove2me | Definitions.Def_CovariateSAA_Setting
-- name    : CovariateSAA_Setting
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:28:12.668293+00:00
-- url     : https://prove2.me/theorems/332d26d9-8df8-4501-8ef0-52c61979f4a3
-- title:
--   The covariate model, residuals, and the true, FI-SAA and ER-SAA problems
-- statement:
--   A decision maker chooses $z\in\mathcal Z\subseteq\mathbb R^{d_z}$ to minimize the cost $c(z,Y)$ of a random vector $Y\in\mathbb R^{d_y}$ after observing covariates $X=x\in\mathbb R^{d_x}$. The model is
--   $$
--   Y = f^*(X) + Q^*(X)\,\varepsilon,
--   $$
--   with regression function $f^*$, matrix function $Q^*$ and errors $\varepsilon\sim P_\varepsilon$.
--
--   The **data** are covariate observations $x^i$ and errors $\varepsilon^i$, $i=1,2,\dots$, on a sample space $\Omega$, with responses $y^i := f^*(x^i) + Q^*(x^i)\varepsilon^i$, together with **regression estimates** $\hat f_n$, $\hat Q_n$ computed from the first $n$ data points. The module defines:
--
--   1. the **empirical residuals** $\hat\varepsilon^i_n := [\hat Q_n(x^i)]^{-1}\bigl(y^i - \hat f_n(x^i)\bigr)$;
--   2. the **deviation sequence** $\tilde\varepsilon^i_n(x) := \bigl(\hat f_n(x) + \hat Q_n(x)\hat\varepsilon^i_n\bigr) - \bigl(f^*(x) + Q^*(x)\varepsilon^i\bigr)$;
--   3. the **true objective** $g(z;x) := \mathbb E\bigl[c(z, f^*(x)+Q^*(x)\varepsilon)\bigr]$, the expectation over $\varepsilon\sim P_\varepsilon$, with optimal value $v^*(x)$ and solution set $S^*(x)$ over $\mathcal Z$ (problem (1));
--   4. the **full-information SAA objective** $g^*_n(z;x) := \frac1n\sum_{i=1}^n c\bigl(z, f^*(x)+Q^*(x)\varepsilon^i\bigr)$ (problem (2));
--   5. the **empirical residuals-based SAA (ER-SAA) objective**
--   $$
--   \hat g^{ER}_n(z;x) := \frac1n\sum_{i=1}^n c\Bigl(z, \operatorname{proj}_{\mathcal Y}\bigl(\hat f_n(x) + \hat Q_n(x)\hat\varepsilon^i_n\bigr)\Bigr),
--   $$
--   with optimal value $\hat v^{ER}_n(x)$ and solution set $\hat S^{ER}_n(x)$ over $\mathcal Z$ (problem (4)).
--
--   These are the objects of every statement in the mission: the ER-SAA problem is the data-driven approximation of the true problem whose consistency Theorem 5 establishes.
--
--   **Formalization Note** Vectors live in `EuclideanSpace ℝ (Fin d)`. $Q^*(x)$ and $\hat Q_n(x)$ are continuous linear maps of $\mathbb R^{d_y}$, whose norm is the operator norm (the paper's induced matrix norm), and $[\cdot]^{-1}$ is `Ring.inverse` (the inverse for a nonsingular operator, $0$ otherwise). Data are one sequence indexed from $0$, so `xs i` is the paper's $x^{i+1}$; sample $i\in[n]$ is `i : Fin n`. The projection is passed as a map `proj`; the expectation is a Bochner integral, which is the paper's expectation under the integrability every statement assumes.
-- source:
--   Kannan, Bayraksan & Luedtke, Data-Driven Sample Average Approximation with Covariate Information, arXiv:2207.13554v1, §2, model and (1) p.5, (2) p.5, residuals and (4) p.6, deviation sequence p.9

import Mathlib
import Definitions.Def_CovariateSAA_Optim

open MeasureTheory

namespace CovariateSAA

/-- `ℝ^d` with the Euclidean norm (arXiv:2207.13554v1, Notation, p.8). Covariates live in
`Vec d_x`, the random vector `Y`, the errors `ε` and the scenarios in `Vec d_y`, decisions in
`Vec d_z`. -/
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The data of the covariate model of Kannan, Bayraksan & Luedtke, *Data-Driven Sample Average
Approximation with Covariate Information*, arXiv:2207.13554v1, §2, pp.5–6: the regression
function `f*`, the matrix function `Q*` of the model `Y = f*(X) + Q*(X) ε`, the data
`(xⁱ, εⁱ)` as random variables on a sample space `Ω`, and the regression estimates `f̂_n`, `Q̂_n`
fitted from the first `n` data points.

**Formalization Note** `Q*(x)` and `Q̂_n(x)` are continuous linear maps `ℝ^{d_y} → ℝ^{d_y}`,
whose norm is the operator norm (the paper's "induced matrix norm", p.8). The data form one
sequence indexed from `0`: `xs i ω` and `eps i ω` are the paper's `x^{i+1}`, `ε^{i+1}`. The
estimates may depend on the whole sample point `ω`. -/
structure Data (dx dy : ℕ) (Ω : Type*) where
  /-- the regression function `f*` -/
  fstar : Vec dx → Vec dy
  /-- the matrix function `Q*` -/
  Qstar : Vec dx → (Vec dy →L[ℝ] Vec dy)
  /-- the covariate observations `xⁱ` (index `i` is the paper's `i + 1`) -/
  xs : ℕ → Ω → Vec dx
  /-- the error realizations `εⁱ` (index `i` is the paper's `i + 1`) -/
  eps : ℕ → Ω → Vec dy
  /-- the regression estimate `f̂_n` of `f*` computed from the first `n` data points -/
  fhat : ℕ → Ω → Vec dx → Vec dy
  /-- the regression estimate `Q̂_n` of `Q*` computed from the first `n` data points -/
  Qhat : ℕ → Ω → Vec dx → (Vec dy →L[ℝ] Vec dy)

variable {dx dy dz : ℕ} {Ω : Type*}

/-- The empirical mean `(1/n) Σ_{i=1}^n a_i` (arXiv:2207.13554v1, (2), (4) and throughout).
At `n = 0` it is `0`. -/
noncomputable def empMean (n : ℕ) (a : Fin n → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, a i

/-- The response observations `yⁱ := f*(xⁱ) + Q*(xⁱ) εⁱ` (model `Y = f*(X) + Q*(X)ε`,
arXiv:2207.13554v1, p.5). -/
def yobs (D : Data dx dy Ω) (i : ℕ) (ω : Ω) : Vec dy :=
  D.fstar (D.xs i ω) + D.Qstar (D.xs i ω) (D.eps i ω)

/-- The empirical residuals `ε̂ⁱ_n := [Q̂_n(xⁱ)]⁻¹ (yⁱ − f̂_n(xⁱ))` (arXiv:2207.13554v1, p.6).

**Formalization Note** `[·]⁻¹` is `Ring.inverse`, which is the inverse for a nonsingular
operator and `0` otherwise; the paper assumes `Q̂_n` nonsingular. -/
noncomputable def residual (D : Data dx dy Ω) (n : ℕ) (ω : Ω) (i : Fin n) : Vec dy :=
  Ring.inverse (D.Qhat n ω (D.xs i ω)) (yobs D i ω - D.fhat n ω (D.xs i ω))

/-- The `i`-th FI-SAA scenario `f*(x) + Q*(x) εⁱ` (arXiv:2207.13554v1, (2), p.5). -/
def fiScenario (D : Data dx dy Ω) (x : Vec dx) (ω : Ω) (i : ℕ) : Vec dy :=
  D.fstar x + D.Qstar x (D.eps i ω)

/-- The `i`-th ER-SAA scenario before projection, `f̂_n(x) + Q̂_n(x) ε̂ⁱ_n`
(arXiv:2207.13554v1, (4), p.6). -/
noncomputable def erScenario (D : Data dx dy Ω) (x : Vec dx) (n : ℕ) (ω : Ω) (i : Fin n) :
    Vec dy :=
  D.fhat n ω x + D.Qhat n ω x (residual D n ω i)

/-- The deviation sequence `ε̃ⁱ_n(x) := (f̂_n(x) + Q̂_n(x) ε̂ⁱ_n) − (f*(x) + Q*(x) εⁱ)`
(arXiv:2207.13554v1, p.9). -/
noncomputable def epsTilde (D : Data dx dy Ω) (x : Vec dx) (n : ℕ) (ω : Ω) (i : Fin n) :
    Vec dy :=
  erScenario D x n ω i - fiScenario D x ω i

/-- The true objective `g(z; x) := E[c(z, f*(x) + Q*(x) ε)]`, the expectation taken with
respect to the error distribution `P_ε` (arXiv:2207.13554v1, (1), p.5).

**Formalization Note** A Bochner integral; it is the paper's expectation when
`e ↦ c(z, f*(x) + Q*(x)e)` is `P_ε`-integrable, the paper's standing assumption (p.5). -/
noncomputable def gTrue (D : Data dx dy Ω) (Pε : Measure (Vec dy))
    (c : Vec dz → Vec dy → ℝ) (x : Vec dx) (z : Vec dz) : ℝ :=
  ∫ e, c z (D.fstar x + D.Qstar x e) ∂Pε

/-- The full-information SAA objective `g*_n(z; x) := (1/n) Σ_{i=1}^n c(z, f*(x) + Q*(x)εⁱ)`
(arXiv:2207.13554v1, (2), p.5). -/
noncomputable def gFI (D : Data dx dy Ω) (c : Vec dz → Vec dy → ℝ) (x : Vec dx) (n : ℕ)
    (ω : Ω) (z : Vec dz) : ℝ :=
  empMean n (fun i => c z (fiScenario D x ω i))

/-- The ER-SAA objective
`ĝ^ER_n(z; x) := (1/n) Σ_{i=1}^n c(z, proj_𝒴(f̂_n(x) + Q̂_n(x) ε̂ⁱ_n))`
(arXiv:2207.13554v1, (4), p.6). `proj` stands for `proj_𝒴`. -/
noncomputable def gER (D : Data dx dy Ω) (c : Vec dz → Vec dy → ℝ) (proj : Vec dy → Vec dy)
    (x : Vec dx) (n : ℕ) (ω : Ω) (z : Vec dz) : ℝ :=
  empMean n (fun i => c z (proj (erScenario D x n ω i)))

/-- The optimal value `v*(x) := min_{z ∈ 𝒵} g(z; x)` of the true problem (1), p.5. -/
noncomputable def vStar (D : Data dx dy Ω) (Pε : Measure (Vec dy))
    (c : Vec dz → Vec dy → ℝ) (Z : Set (Vec dz)) (x : Vec dx) : ℝ :=
  minVal (gTrue D Pε c x) Z

/-- The optimal solution set `S*(x)` of the true problem (1), p.5. -/
def SStar (D : Data dx dy Ω) (Pε : Measure (Vec dy))
    (c : Vec dz → Vec dy → ℝ) (Z : Set (Vec dz)) (x : Vec dx) : Set (Vec dz) :=
  argminSet (gTrue D Pε c x) Z

/-- The optimal value `v̂^ER_n(x) := min_{z ∈ 𝒵} ĝ^ER_n(z; x)` of the ER-SAA problem (4), p.6. -/
noncomputable def vER (D : Data dx dy Ω) (c : Vec dz → Vec dy → ℝ) (proj : Vec dy → Vec dy)
    (Z : Set (Vec dz)) (x : Vec dx) (n : ℕ) (ω : Ω) : ℝ :=
  minVal (gER D c proj x n ω) Z

/-- The optimal solution set `Ŝ^ER_n(x)` of the ER-SAA problem (4), p.6. -/
def SER (D : Data dx dy Ω) (c : Vec dz → Vec dy → ℝ) (proj : Vec dy → Vec dy)
    (Z : Set (Vec dz)) (x : Vec dx) (n : ℕ) (ω : Ω) : Set (Vec dz) :=
  argminSet (gER D c proj x n ω) Z

end CovariateSAA


