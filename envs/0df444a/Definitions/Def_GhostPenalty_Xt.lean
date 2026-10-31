-- Prove2me | Definitions.Def_GhostPenalty_Xt
-- name    : GhostPenalty_Xt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:36:09.118792+00:00
-- url     : https://prove2.me/theorems/162b4049-ac7d-4f45-851d-a78e47ba0b1b
-- title:
--   Feasible set $\widetilde X(x)$ of the subproblem $(\mathrm P_x)$
-- statement:
--   The direction-finding subproblem at $x\in K$ is
--   $$\operatorname*{minimize}_d\ \tilde f(d;x)\quad\text{s.t.}\quad \tilde g(d;x)\le\kappa(x)e,\ \ \|d\|_\infty\le\beta,\ \ d\in K-x, \tag{$\mathrm P_x$}$$
--   and its feasible set is
--   $$\widetilde X(x)\triangleq\{d\in\mathbb R^n:\ \tilde g(d;x)\le\kappa(x)e,\ \|d\|_\infty\le\beta,\ d\in K-x\}.$$
--
--   **Formalization Note** The vector inequality is componentwise; $d\in K-x$ is $x+d\in K$.
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, (Pₓ), p.6, and p.7

import Mathlib
import Definitions.Def_GhostPenalty_kappa

namespace GhostPenalty

/-- **Feasible set `X̃(x)` of the direction-finding subproblem (Pₓ).**
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, §3, (Pₓ), p.6, and p.7:
"minimize_d `f̃(d;x)` s.t. `g̃(d;x) ≤ κ(x)e`, `‖d‖∞ ≤ β`, `d ∈ K − x` (Pₓ)" and
"`X̃(x) ≜ {d ∈ ℝⁿ : g̃(d;x) ≤ κ(x)e, ‖d‖∞ ≤ β, d ∈ K − x}`".

**Formalization Note.** `g̃(d;x) ≤ κ(x)e` is componentwise; `‖d‖∞ ≤ β` is `box n β`;
`d ∈ K − x` is `x + d ∈ K`. -/
def Xt {n m : ℕ} (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gt : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (lam ρ β : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {d | (∀ i, gt i d x ≤ kappa g gt K lam ρ x) ∧ d ∈ box n β ∧ x + d ∈ K}

end GhostPenalty


