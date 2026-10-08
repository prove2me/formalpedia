-- Prove2me | Definitions.Def_LogBarrierIPM_Curvature_PuiseuxLP
-- name    : LogBarrierIPM_Curvature_PuiseuxLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:21:34.694157+00:00
-- url     : https://prove2.me/theorems/dffc8f3a-7b87-4789-bc80-d7f1d83e2a0e
-- title:
--   A Puiseux linear program $\mathrm{LP}(\mathbf A,\mathbf b,\mathbf c)$ evaluated at $t$, and its central-path point with parameter $t^\lambda$
-- statement:
--   Let $\mathbf A\in\mathbb K^{m\times n}$, $\mathbf b\in\mathbb K^m$, $\mathbf c\in\mathbb K^n$ be the data of a linear program $\mathrm{LP}(\mathbf A,\mathbf b,\mathbf c)$ over the Puiseux field $\mathbb K$. Substituting a real number for $t$ gives the real data $A(t)$, $b(t)$, $c(t)$ and the parametric family of real linear programs $\mathrm{LP}(A(t),b(t),c(t))$.
--
--   A primal-dual point over $\mathbb K$ is $\mathbf z=(\mathbf x,\mathbf w,\mathbf s,\mathbf y)\in\mathbb K^n\times\mathbb K^m\times\mathbb K^n\times\mathbb K^m$; it evaluates to $\mathbf z(t)\in\mathbb R^{2N}$ and has valuation $\mathrm{val}(\mathbf z)=(\mathrm{val}\,\mathbf x,\mathrm{val}\,\mathbf w,\mathrm{val}\,\mathbf s,\mathrm{val}\,\mathbf y)\in\mathbb T^{2N}$.
--
--   For $\lambda\in\mathbb R$, $\mathbf z$ is the **point of the central path of $\mathrm{LP}(\mathbf A,\mathbf b,\mathbf c)$ with parameter $\boldsymbol\mu=t^\lambda$** when it solves system (1) over $\mathbb K$:
--   $$\mathbf A\mathbf x+\mathbf w=\mathbf b,\quad \mathbf s-\mathbf A^\top\mathbf y=\mathbf c,\quad \mathbf x\mathbf s=t^\lambda e,\quad \mathbf w\mathbf y=t^\lambda e,\quad \mathbf x,\mathbf w,\mathbf y,\mathbf s>0 .$$
--   Its valuation is then the point $\mathcal C^{\mathrm{trop}}(\lambda)=\mathrm{val}(\mathbf z)$ of the tropical central path.
--
--   **Formalization Note** In $\mathbb K$, $\mathbf f=\mathbf g$ holds exactly when $\mathbf f(t)=\mathbf g(t)$ for all sufficiently large $t$, evaluation is compatible with sums and products, and $\mathbf f\le\mathbf g$ holds exactly when $\mathbf f(t)\le\mathbf g(t)$ for all large $t$ (p. 7). System (1) over $\mathbb K$ is therefore stated as: for all sufficiently large real $t$, $\mathbf z(t)$ solves system (1) for $A(t)$, $b(t)$, $c(t)$ and $\mu=t^\lambda$ (the evaluation of the monomial $t^\lambda$). This avoids defining the field operations of $\mathbb K$.
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 7 (order of K via evaluation); p. 16 (tropical central path C^trop(λ) = val of the central path at μ with val μ = λ); p. 22 (LP(A(t), b(t), c(t)), central path C_t, proof of Proposition 24)

import Mathlib
import Definitions.Def_LogBarrierIPM_Curvature_Puiseux
import Definitions.Def_LogBarrierIPM_Curvature_SlackCentralPath

open Filter

namespace LogBarrierIPM.Curvature

/-- A primal-dual point `(x, w, s, y) ∈ 𝕂^n × 𝕂^m × 𝕂^n × 𝕂^m` over the Puiseux field. -/
abbrev PuiseuxSlackPoint (n m : ℕ) :=
  (Fin n → Puiseux) × (Fin m → Puiseux) × (Fin n → Puiseux) × (Fin m → Puiseux)

/-- The real matrix `A(t)` obtained by evaluating every entry of `A ∈ 𝕂^{m×n}` at `t`. -/
noncomputable def evalMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) Puiseux) (t : ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  fun i j => (A i j).eval t

/-- The real vector `b(t)` obtained by evaluating every coordinate of `b ∈ 𝕂^m` at `t`. -/
noncomputable def evalFun {m : ℕ} (b : Fin m → Puiseux) (t : ℝ) : Fin m → ℝ :=
  fun i => (b i).eval t

/-- The real point `z(t)` obtained by evaluating a Puiseux primal-dual point at `t`. -/
noncomputable def evalPoint {n m : ℕ} (z : PuiseuxSlackPoint n m) (t : ℝ) : SlackPoint n m :=
  (evalFun z.1 t, evalFun z.2.1 t, evalFun z.2.2.1 t, evalFun z.2.2.2 t)

/-- The tropical point `val(z) = (val x, val w, val s, val y) ∈ 𝕋^{2N}` of a Puiseux primal-dual
point. -/
noncomputable def valPoint {n m : ℕ} (z : PuiseuxSlackPoint n m) :
    Fin ((n + m) + (n + m)) → WithBot ℝ :=
  Fin.append (Fin.append (fun j => (z.1 j).val) (fun i => (z.2.1 i).val))
    (Fin.append (fun j => (z.2.2.1 j).val) (fun i => (z.2.2.2 i).val))

/-- `z` is the point of the central path of the Puiseux linear program `LP(A, b, c)` with parameter
`μ = t^λ` (§4.1): `z` solves system (1) over `𝕂`. Equalities, products and strict positivity in
`𝕂` hold if and only if they hold for the evaluations at every sufficiently large real `t`
(p. 7), so this is stated as: for all sufficiently large `t`, `z(t)` solves (1) for
`A(t), b(t), c(t)` and `μ = t^λ`. Then `val z = C^trop(λ)` is the point of the tropical central
path at `λ` (p. 16). -/
def IsPuiseuxCentralPathPoint {m n : ℕ} (A : Matrix (Fin m) (Fin n) Puiseux) (b : Fin m → Puiseux)
    (c : Fin n → Puiseux) (lam : ℝ) (z : PuiseuxSlackPoint n m) : Prop :=
  ∀ᶠ t in atTop, IsSlackCentralPathPoint (evalMatrix A t) (evalFun b t) (evalFun c t) (t ^ lam)
    (evalPoint z t)

end LogBarrierIPM.Curvature


