-- Prove2me | Definitions.Def_LargeDelaySGD_MeanSquare_Supplement_Constrained
-- name    : LargeDelaySGD_MeanSquare_Supplement_Constrained
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T08:06:45.769367+00:00
-- url     : https://prove2.me/theorems/04f0c927-bf9c-4768-a7e7-9546ffc500bb
-- title:
--   §4, pp. 8–19 — projection, solution set X*, constrained Assumption 1, (VC), energy (7), Assumption 4, DAGD, lazy-projection DASGD, mean-field flow (17), affine interpolation
-- statement:
--   Objects of the constrained problem of §4. Let $\mathcal X\subseteq\mathbb R^d$ be the feasible set and $F(x;\omega)$ a random function with objective $f(x)=\mathbb E[F(x;\omega)]$ (the published `objective`) and stochastic gradient $\nabla F(x;\omega)$ (the published `stochGrad`).
--
--   1. **Projection.** $\mathrm{pr}_{\mathcal X}(y)$ is the nearest point of $\mathcal X$ to $y$ (the published Euclidean projection `projOnto`).
--   2. **Mean gradient.** $\nabla f(x)=\mathbb E[\nabla F(x;\omega)]$ (Remark 1).
--   3. **Solution set.** $\mathcal X^*=\{x\in\mathcal X: f(x)\le f(z)\ \text{for all } z\in\mathcal X\}$.
--   4. **Assumption 1 on $\mathcal X$.** For almost every $\omega$, $F(\cdot;\omega)$ is differentiable at every point of $\mathcal X$; $\sup_{x\in\mathcal X}\mathbb E\|\nabla F(x;\omega)\|_2^2<\infty$; and $x\mapsto\mathbb E[\nabla F(x;\omega)]$ is Lipschitz on $\mathcal X$.
--   5. **Assumption 3 (VC).** For all $x^*\in\mathcal X^*$ and $x\in\mathcal X$, $\mathbb E[\langle\nabla F(x;\omega),x-x^*\rangle]\ge0$, with equality only if $x\in\mathcal X^*$.
--   6. **Energy (7).** For $x^*\in\mathcal X^*$,
--   $$E_{x^*}(y)=\|x^*\|_2^2-\|\mathrm{pr}_{\mathcal X}(y)\|_2^2+2\langle y,\mathrm{pr}_{\mathcal X}(y)-x^*\rangle,\qquad E(y)=\inf_{x^*\in\mathcal X^*}E_{x^*}(y).$$
--   7. **Assumption 4** (as printed): for every sequence $(y_n)$, $E(y_n)\to0$ implies $\mathrm{dist}(\mathrm{pr}_{\mathcal X}(y_n),\mathcal X^*)\to0$. **Energy reciprocity** is the converse implication, announced on p. 14 and used in the proofs.
--   8. **DAGD (Algorithm 5).** From any $y_0\in\mathbb R^d$: $x_n=\mathrm{pr}_{\mathcal X}(y_n)$, $y_{n+1}=y_n-\alpha_{n+1}\nabla f(x_{s(n)})$.
--   9. **DASGD with lazy projection (Algorithm 4).** From any $Y_0\in\mathbb R^d$: $X_n=\mathrm{pr}_{\mathcal X}(Y_n)$, $Y_{n+1}=Y_n-\alpha_{n+1}\nabla F(X_{s(n)},\omega_{n+1})$.
--   10. **Mean-field flow (17).** A semiflow $P$ on $\mathbb R^d$ whose trajectories solve $\dot y=-\nabla f(\mathrm{pr}_{\mathcal X}(y))$, $P(0,y)=y$.
--   11. **Affine interpolation.** With $\tau_0=0$ and $\tau_n=\sum_{r=1}^n\alpha_r$, $A(t)=Y_n+\frac{t-\tau_n}{\alpha_{n+1}}(Y_{n+1}-Y_n)$ for $\tau_n\le t\le\tau_{n+1}$.
--
--   These are the objects in which Lemmas 3–6, Propositions 1–2 and Theorems 2–3 are stated.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`. $F$ is an ambient representative of the source's $F:\mathcal X\times\Omega\to\mathbb R$; every analytic condition is imposed on $\mathcal X$ only. The fields `integrable` and `measurable_grad` (joint measurability of $\nabla F$ on $\mathcal X\times\Xi$) are disclosed implicit hypotheses. The infimum defining $E$ is a real infimum over $\mathcal X^*$; under Assumption 1 the set $\mathcal X^*$ is nonempty and compact and every $E_{x^*}(y)\ge\|\mathrm{pr}_{\mathcal X}(y)-x^*\|_2^2\ge0$, so it is the true infimum. The semiflow is characterized by its ODE: every trajectory has right derivative $-\nabla f(\mathrm{pr}_{\mathcal X}(P(t,y)))$ at each $t\ge0$. The interpolation index is the largest $n$ with $\tau_n\le t$; it is the true index when the steps are positive and not summable, as under Assumption 2.
-- source:
--   Z. Zhou, P. Mertikopoulos, N. Bambos, P. W. Glynn, Y. Ye, Distributed Stochastic Optimization with Large Delays, arXiv:2107.02919v1 (SHA-256 20dd663845757ad1e06f51c4ae62f8fd6623aa921b66be496b00befa51d9a327), (Opt) and (1), pp. 4–5; Assumption 1, p. 5; Algorithm 4, p. 8; §4 and Assumption 3, p. 11; Algorithm 5 and Definition 1 (7), p. 13; footnote 11, p. 13; Assumption 4, p. 14; ODE (17), p. 17; affine interpolation, p. 19; Definition 3, p. 22

import Mathlib
import Definitions.Def_LargeDelaySGD_MeanSquare_Model
import Definitions.Def_SolodovSvaiterVI_Alg21_projOnto

namespace LargeDelaySGD.MeanSquare.Supplement

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

variable {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]

/-- The Euclidean projection `pr_X` onto the feasible set `X` (Algorithms 4–5, pp. 8, 13). It is the
published `SolodovSvaiterVI.Alg21.projOnto`, the nearest point of `X`; on a nonempty compact
convex `X` (§4, p. 11) the nearest point exists and is unique. -/
noncomputable abbrev proj (X : Set (EuclideanSpace ℝ (Fin d))) (y : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  SolodovSvaiterVI.Alg21.projOnto X y

/-- The mean gradient `∇f(x) = E[∇F(x; ω)]` (Remark 1, p. 5). In the constrained problem `f` is
only defined on `X`, and the paper identifies its gradient with this expectation. -/
noncomputable def meanGrad (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (μ : Measure Ξ)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  ∫ ξ, stochGrad F x ξ ∂μ

/-- The solution set `X*` of (Opt), p. 4: the minimizers of `f = E[F]` over `X`. -/
def solutionSet (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (μ : Measure Ξ)
    (X : Set (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | x ∈ X ∧ ∀ z ∈ X, objective F μ x ≤ objective F μ z}

/-- Assumption 1 (p. 5) for the constrained problem of §4: every condition is imposed on the
feasible set `X` only. `F` is an ambient representative of the source's `F : X × Ω → ℝ`; its
values and analytic behaviour off `X` are unrestricted. The fields `integrable` (the expectation
in (1) exists on `X`) and `measurable_grad` (joint measurability of `∇F` on `X × Ξ`, so that the
iterates are random variables) are the disclosed implicit hypotheses. -/
structure ConstrainedAssumption1 (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (μ : Measure Ξ)
    (X : Set (EuclideanSpace ℝ (Fin d))) : Prop where
  integrable : ∀ x ∈ X, Integrable (F x) μ
  measurable_grad : Measurable (fun p : X × Ξ => stochGrad F (p.1 : EuclideanSpace ℝ (Fin d)) p.2)
  differentiable : ∀ᵐ ξ ∂μ, ∀ x ∈ X, DifferentiableAt ℝ (fun y => F y ξ) x
  memLp : ∀ x ∈ X, MemLp (stochGrad F x) 2 μ
  second_moment : ∃ B : ℝ, ∀ x ∈ X, ∫ ξ, ‖stochGrad F x ξ‖ ^ 2 ∂μ ≤ B
  lipschitz : ∃ L : ℝ≥0, LipschitzOnWith L (meanGrad F μ) X

/-- Assumption 3 (VC), p. 11: for every `x* ∈ X*` and every `x ∈ X`,
`E[⟨∇F(x; ω), x − x*⟩] ≥ 0`, with equality only if `x ∈ X*`. -/
def VariationallyCoherent (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (μ : Measure Ξ)
    (X : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ xs ∈ solutionSet F μ X, ∀ x ∈ X,
    0 ≤ ∫ ξ, inner ℝ (stochGrad F x ξ) (x - xs) ∂μ ∧
      (∫ ξ, inner ℝ (stochGrad F x ξ) (x - xs) ∂μ = 0 → x ∈ solutionSet F μ X)

/-- The fixed-minimizer energy `E_{x*}(y) = ‖x*‖² − ‖pr_X(y)‖² + 2⟨y, pr_X(y) − x*⟩`, (7), p. 13. -/
noncomputable def energyAt (X : Set (EuclideanSpace ℝ (Fin d))) (xs y : EuclideanSpace ℝ (Fin d)) :
    ℝ :=
  ‖xs‖ ^ 2 - ‖proj X y‖ ^ 2 + 2 * inner ℝ y (proj X y - xs)

/-- The energy `E(y) = inf_{x* ∈ X*} E_{x*}(y)`, Definition 1, (7), p. 13. Here `Xs` is the
solution set; on a nonempty compact `Xs ⊆ X` the infimum is over a nonempty set bounded below by
`0` (each `E_{x*}(y) ≥ ‖pr_X(y) − x*‖²`), so the real infimum is the true one. -/
noncomputable def energy (X Xs : Set (EuclideanSpace ℝ (Fin d))) (y : EuclideanSpace ℝ (Fin d)) :
    ℝ :=
  ⨅ xs : Xs, energyAt X (xs : EuclideanSpace ℝ (Fin d)) y

/-- Assumption 4, p. 14, in its printed direction: for every sequence `y_n`, `E(y_n) → 0` implies
`pr_X(y_n) → X*`, i.e. `dist(pr_X(y_n), X*) → 0` (footnote 11, p. 13). -/
def Assumption4 (X Xs : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ y : ℕ → EuclideanSpace ℝ (Fin d),
    Tendsto (fun n => energy X Xs (y n)) atTop (𝓝 0) →
      Tendsto (fun n => Metric.infDist (proj X (y n)) Xs) atTop (𝓝 0)

/-- Energy reciprocity, the converse of Lemma 3 (2) that the text before Assumption 4 announces
("the converse of Statement 2", p. 14) and that footnote 15 (p. 32) and the proof of Lemma 5
(p. 36) use: `pr_X(y_n) → X*` implies `E(y_n) → 0`. Used only in the corrected Lemma 5 (2). -/
def EnergyReciprocity (X Xs : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ y : ℕ → EuclideanSpace ℝ (Fin d),
    Tendsto (fun n => Metric.infDist (proj X (y n)) Xs) atTop (𝓝 0) →
      Tendsto (fun n => energy X Xs (y n)) atTop (𝓝 0)

/-- Algorithm 5 (DAGD), p. 13: `x_n = pr_X(y_n)` and `y_{n+1} = y_n − α_{n+1} ∇f(x_{s(n)})`, from
an arbitrary initial `y₀ ∈ ℝ^d`, with the exact (mean) gradient. -/
def IsDAGD (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (μ : Measure Ξ)
    (X : Set (EuclideanSpace ℝ (Fin d))) (α : ℕ → ℝ) (s : ℕ → ℕ) (y₀ : EuclideanSpace ℝ (Fin d))
    (y : ℕ → EuclideanSpace ℝ (Fin d)) : Prop :=
  y 0 = y₀ ∧ ∀ n, y (n + 1) = y n - α (n + 1) • meanGrad F μ (proj X (y (s n)))

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Algorithm 4 (DASGD with lazy projection), p. 8: `X_n = pr_X(Y_n)` and
`Y_{n+1} = Y_n − α_{n+1} ∇F(X_{s(n)}, ω_{n+1})`, from an arbitrary initial `Y₀ ∈ ℝ^d`. -/
def IsLazyDASGD (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (X : Set (EuclideanSpace ℝ (Fin d)))
    (α : ℕ → ℝ) (s : ℕ → ℕ) (ω : ℕ → Ω → Ξ) (Y₀ : EuclideanSpace ℝ (Fin d))
    (Y : ℕ → Ω → EuclideanSpace ℝ (Fin d)) : Prop :=
  (∀ a, Y 0 a = Y₀) ∧
    ∀ n a, Y (n + 1) a = Y n a - α (n + 1) • stochGrad F (proj X (Y (s n) a)) (ω (n + 1) a)

/-- `P` is the semiflow of the mean-field ODE (17), p. 17: `ẏ = −∇f(pr_X(y))`, `P(0, y) = y`
(the flow axioms of Definition 3, p. 22, are those of a Mathlib `Flow ℝ≥0`). Each trajectory
`t ↦ P(t, y)` has right derivative `−∇f(pr_X(P(t, y)))` at every `t ≥ 0`. The drift is globally
Lipschitz under Assumption 1, so this semiflow exists and is unique. -/
def IsMeanFieldFlow (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (μ : Measure Ξ)
    (X : Set (EuclideanSpace ℝ (Fin d))) (P : Flow ℝ≥0 (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ (y : EuclideanSpace ℝ (Fin d)) (t : ℝ≥0),
    HasDerivWithinAt (fun τ : ℝ => P (Real.toNNReal τ) y) (-meanGrad F μ (proj X (P t y)))
      (Set.Ici (t : ℝ)) (t : ℝ)

/-- The interpolation times `τ_n = Σ_{r=1}^n α_r`, `τ_0 = 0` (p. 19). -/
noncomputable def interpTime (α : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ r ∈ Finset.range n, α (r + 1)

/-- The index `n` with `τ_n ≤ t < τ_{n+1}`, the largest `n` with `τ_n ≤ t`. -/
noncomputable def interpIndex (α : ℕ → ℝ) (t : ℝ≥0) : ℕ :=
  sSup {n : ℕ | interpTime α n ≤ t}

/-- The affine interpolation curve `A(t)` of the iterates `Y_0, Y_1, …` at times
`0, α_1, α_1 + α_2, …` (p. 19): for `τ_n ≤ t ≤ τ_{n+1}`,
`A(t) = Y_n + ((t − τ_n)/α_{n+1}) (Y_{n+1} − Y_n)`. Under Assumption 2 the steps are positive and
not summable, so `interpIndex` is the true index. -/
noncomputable def affineInterp (α : ℕ → ℝ) (Y : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℝ≥0) :
    EuclideanSpace ℝ (Fin d) :=
  let n := interpIndex α t
  Y n + (((t : ℝ) - interpTime α n) / α (n + 1)) • (Y (n + 1) - Y n)

end LargeDelaySGD.MeanSquare.Supplement


