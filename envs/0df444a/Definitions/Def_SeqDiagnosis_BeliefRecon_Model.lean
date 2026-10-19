-- Prove2me | Definitions.Def_SeqDiagnosis_BeliefRecon_Model
-- name    : SeqDiagnosis_BeliefRecon_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:17.892833+00:00
-- url     : https://prove2.me/theorems/c39e682f-542f-4148-91a5-3439b668148c
-- title:
--   §2–§3, pp. 5–10 — exponential tilting, diagnostic matrices, statistic, and reconstruction map
-- statement:
--   The model has $N+1$ class densities $f_0,\ldots,f_N$, a natural statistic $h(y)\in\mathbb R^p$, and tilt vectors $\beta_1,\ldots,\beta_N$. The baseline is class $0$. The **diagnostic parameter matrix** $\mathbb B$ has row $j$ equal to $\beta_j^{\mathsf T}$. With a factorization $\mathbb B=\mathbb R\mathbb P$, the diagnostic statistic after $t$ observations is
--
--   $$x_t=\mathbb P\sum_{m=1}^t h(y_m)/t.$$
--
--   The exponential-tilting condition is imposed on the given densities:
--
--   $$f_j(y)=f_0(y)\exp\{\beta_{j0}+\beta_j^{\mathsf T}h(y)\},\qquad \beta_{j0}=-\log\int\exp\{\beta_j^{\mathsf T}h(y)\}f_0(y)\,d\mu(y).$$
--
--   The reconstruction map $\mathcal T^t(x,\theta)$ uses equation (3) for nonbaseline coordinates and sets coordinate zero to one minus their sum. $\Omega_t$ is the set of attainable $x_t$; its image under $\mathcal T^t$ is the set $\mathcal F_t^\theta$ of Definition 2.
--
--   The model keeps the normalizer computed from $\beta_j$ separate from the normalizer computed from row $j$ of $\mathbb R\mathbb P$. Their equality follows from the factorization and is one of the milestones.
--
--   **Formalization Note** Observations live in a measurable type with reference measure $\mu$. Every density is measurable; $f_0$ is positive on the admitted observation space and integrates to one; the tilted baseline functions are integrable. These explicit conditions make the real integrals and Bayes denominators well defined. Row `i : Fin N` denotes paper class $i+1$.
-- source:
--   Wang, Optimal Sequential Multi-class Diagnosis, arXiv:1506.08915v4, pp. 5–10 (PDF 5–10), §2–§3, (2), Definitions 1–2, (3)

import Mathlib
import Definitions.Def_SeqDiagnosis_BeliefRecon_Bayes

open MeasureTheory Matrix

namespace SeqDiagnosis.BeliefRecon

/-- The class densities, natural statistic, and exponential-tilt parameters. Row `i : Fin N`
corresponds to class `i.succ`; class zero is the baseline. -/
structure Model (Y : Type*) [MeasurableSpace Y] (N p : ℕ) where
  μ : Measure Y
  f : Fin (N + 1) → Y → ℝ
  h : Y → Fin p → ℝ
  beta : Fin N → Fin p → ℝ

/-- The diagnostic parameter matrix of Definition 1. -/
def Model.Bmat {Y : Type*} [MeasurableSpace Y] {N p : ℕ}
    (M : Model Y N p) : Matrix (Fin N) (Fin p) ℝ :=
  Matrix.of M.beta

/-- The normalizing constant in exponential-tilting condition (2). -/
noncomputable def Model.normConst {Y : Type*} [MeasurableSpace Y] {N p : ℕ}
    (M : Model Y N p) (b : Fin p → ℝ) : ℝ :=
  -Real.log (∫ y, Real.exp (b ⬝ᵥ M.h y) * M.f 0 y ∂M.μ)

/-- Equation (2), imposed on the given densities. -/
def Model.ETM {Y : Type*} [MeasurableSpace Y] {N p : ℕ}
    (M : Model Y N p) : Prop :=
  ∀ (i : Fin N) (y : Y),
    M.f i.succ y = M.f 0 y * Real.exp (M.normConst (M.beta i) + M.beta i ⬝ᵥ M.h y)

/-- Positivity on the observation support and the integrability needed for real normalizers. -/
def Model.Standing {Y : Type*} [MeasurableSpace Y] {N p : ℕ}
    (M : Model Y N p) : Prop :=
  (∀ i, Measurable (M.f i)) ∧ (∀ y, 0 < M.f 0 y) ∧
    (∫ y, M.f 0 y ∂M.μ) = 1 ∧
    ∀ i : Fin N, Integrable (fun y => Real.exp (M.beta i ⬝ᵥ M.h y) * M.f 0 y) M.μ

/-- The diagnostic statistic `x_t = P (∑ₘ h(yₘ))/t`. -/
noncomputable def diagStat {Y : Type*} [MeasurableSpace Y] {N p r : ℕ}
    (M : Model Y N p) (P : Matrix (Fin r) (Fin p) ℝ) (ys : List Y) :
    Fin r → ℝ :=
  (ys.length : ℝ)⁻¹ • (P *ᵥ (ys.map M.h).sum)

/-- The normalizer in (3), evaluated at a row of the rank decomposition `R * P`. -/
noncomputable def betaZero {Y : Type*} [MeasurableSpace Y] {N p r : ℕ}
    (M : Model Y N p) (R : Matrix (Fin N) (Fin r) ℝ)
    (P : Matrix (Fin r) (Fin p) ℝ) (i : Fin N) : ℝ :=
  M.normConst ((R * P) i)

/-- Equation (3) in all class coordinates, with class zero defined by subtraction. -/
noncomputable def Tcal {Y : Type*} [MeasurableSpace Y] {N p r : ℕ}
    (M : Model Y N p) (R : Matrix (Fin N) (Fin r) ℝ)
    (P : Matrix (Fin r) (Fin p) ℝ) (t : ℕ) (x : Fin r → ℝ)
    (θ : Fin (N + 1) → ℝ) : Fin (N + 1) → ℝ :=
  let w : Fin N → ℝ := fun i => θ i.succ * Real.exp ((t : ℝ) * (betaZero M R P i + (R *ᵥ x) i))
  let T : Fin N → ℝ := fun j => w j / (θ 0 + ∑ i, w i)
  Fin.cases (1 - ∑ j, T j) T

/-- The set Ω_t of diagnostic statistics attainable from `t` observations. -/
def Omega {Y : Type*} [MeasurableSpace Y] {N p r : ℕ}
    (M : Model Y N p) (P : Matrix (Fin r) (Fin p) ℝ) (t : ℕ) :
    Set (Fin r → ℝ) :=
  {x | ∃ ys : List Y, ys.length = t ∧ diagStat M P ys = x}

/-- The image of Ω_t under the reconstruction map, Definition 2. -/
def beliefManifold {Y : Type*} [MeasurableSpace Y] {N p r : ℕ}
    (M : Model Y N p) (R : Matrix (Fin N) (Fin r) ℝ)
    (P : Matrix (Fin r) (Fin p) ℝ) (θ : Fin (N + 1) → ℝ) (t : ℕ) :
    Set (Fin (N + 1) → ℝ) :=
  (fun x => Tcal M R P t x θ) '' Omega M P t

end SeqDiagnosis.BeliefRecon


