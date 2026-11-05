-- Prove2me | Definitions.Def_VolunteerNotify_IsExAnte
-- name    : VolunteerNotify_IsExAnte
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:38:41.560741+00:00
-- url     : https://prove2.me/theorems/b4fedc8f-632b-41ba-8b56-d3c4f6423b45
-- title:
--   (5) — the ex ante solution $x^*$ and its candidates $x^*_{LP}$, $x^*_{AA}$, $x^*_{SQ}$
-- statement:
--   The ex ante solution of the source is the best of three candidates.
--
--   1. $x^*_{LP}$ is an optimal solution of (LP).
--   2. $x^*_{AA}$ is the output of the Frank–Wolfe variant with step size $1/m$, for some $m\ge 1$: set $x^0=0$; for $i=1,\dots,m$ let $y^i=\arg\max_{z\in\mathcal P}\langle z,\nabla f(x^{i-1})\rangle$ and $x^i=x^{i-1}+\tfrac1m y^i$; return $x^m$.
--   3. $x^*_{SQ}$ solves the sequential programs (SQ-$v$): for $v=1,\dots,V$, row $v$ maximizes
--   $$
--   \sum_{t=1}^T\sum_{s=1}^S\lambda_{s,t}\Bigl(\prod_{u<v}(1-p_{u,s}x^{SQ}_{u,s,t})\Bigr)p_{v,s}x_{v,s,t}
--   $$
--   subject to constraints (1) and (2) for $v$.
--
--   Then
--   $$
--   x^*:=\arg\max_{x\in\{x^*_{LP},x^*_{AA},x^*_{SQ}\}} f(x). \tag{5}
--   $$
--   This is the object the sparse notification policy sparsifies; the goal theorem is false for a general point of $\mathcal P$.
--
--   **Formalization Note** `IsExAnte I x` holds of every value of (5), because the optimizers, the Frank–Wolfe run and the argmax tie-break are not unique. $\langle z,\nabla f(x)\rangle$ is `fderiv ℝ (f I) x z`.
-- source:
--   Manshadi, Rodilitz, Online Policies for Efficient Volunteer Crowdsourcing, arXiv:2002.08474v7, (LP), p.11; (AA) and Frank–Wolfe variant, p.13; (SQ-v), (5), p.14

import Mathlib
import Definitions.Def_VolunteerNotify_lpValue
import Definitions.Def_VolunteerNotify_f

namespace VolunteerNotify

variable {V S T : ℕ}

/-- `x*_LP`: an optimal solution of (LP), Manshadi–Rodilitz, arXiv:2002.08474v7, pp.11–12. -/
def IsLPSolution (I : Instance V S T) (x : Decision V S T) : Prop :=
  x ∈ feasibleSet I ∧ ∀ y ∈ feasibleSet I, lpObjective I y ≤ lpObjective I x

/-- `x*_AA`: an output of the Frank–Wolfe variant with step size `1/m`, arXiv:2002.08474v7, p.13:
`x⁰ = 0`; for `i` from `1` to `m`, `yⁱ = argmax_{z ∈ P} ⟨z, ∇f(xⁱ⁻¹)⟩` and
`xⁱ = xⁱ⁻¹ + (1/m) yⁱ`; return `xᵐ`.

**Formalization Note.** `⟨z, ∇f(x)⟩` is `fderiv ℝ (f I) x z`, and `f` is a polynomial, so this is
the true directional derivative. Any tie-break of each `argmax` is allowed. -/
def IsFrankWolfeOutput (I : Instance V S T) (m : ℕ) (x : Decision V S T) : Prop :=
  ∃ xs ys : ℕ → Decision V S T,
    xs 0 = 0 ∧
    (∀ i < m,
      ys (i + 1) ∈ feasibleSet I ∧
      (∀ z ∈ feasibleSet I, fderiv ℝ (f I) (xs i) z ≤ fderiv ℝ (f I) (xs i) (ys (i + 1))) ∧
      xs (i + 1) = xs i + (1 / (m : ℝ)) • ys (i + 1)) ∧
    x = xs m

/-- The objective of (SQ-v), arXiv:2002.08474v7, p.14, at the row `y`, given the rows `u < v` of
`x`: `∑_t ∑_s λ_{s,t} (∏_{u<v} (1 − p_{u,s} x^{SQ}_{u,s,t})) p_{v,s} y_{s,t}`. -/
noncomputable def sqObjective (I : Instance V S T) (x : Decision V S T) (v : Fin V)
    (y : Fin S → Fin T → ℝ) : ℝ :=
  ∑ t, ∑ s, I.lam s t * (∏ u ∈ Finset.Iio v, (1 - I.p u s * x u s t)) * I.p v s * y s t

/-- `x*_SQ`: a solution of the `V` sequential linear programs (SQ-v), arXiv:2002.08474v7, p.14.
Row `v` is feasible for (SQ-v) and optimal given the rows `u < v`. -/
def IsSQSolution (I : Instance V S T) (x : Decision V S T) : Prop :=
  ∀ v, RowFeasible I (x v) ∧
    ∀ y, RowFeasible I y → sqObjective I x v y ≤ sqObjective I x v (x v)

/-- `x*` of (5), arXiv:2002.08474v7, p.14: `x* := argmax_{x ∈ {x*_LP, x*_AA, x*_SQ}} f(x)`.

**Formalization Note.** The candidates need not be unique, so this predicate holds of every value
of (5) over any optimizer of (LP), any `m ≥ 1` and run of Frank–Wolfe, any solution of (SQ-v) and
any tie-break of the argmax. -/
def IsExAnte (I : Instance V S T) (x : Decision V S T) : Prop :=
  ∃ (xLP xAA xSQ : Decision V S T) (m : ℕ), 1 ≤ m ∧
    IsLPSolution I xLP ∧ IsFrankWolfeOutput I m xAA ∧ IsSQSolution I xSQ ∧
    (x = xLP ∨ x = xAA ∨ x = xSQ) ∧
    f I xLP ≤ f I x ∧ f I xAA ≤ f I x ∧ f I xSQ ≤ f I x

end VolunteerNotify


