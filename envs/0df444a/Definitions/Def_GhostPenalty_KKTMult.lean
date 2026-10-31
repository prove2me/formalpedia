-- Prove2me | Definitions.Def_GhostPenalty_KKTMult
-- name    : GhostPenalty_KKTMult
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:36:16.496555+00:00
-- url     : https://prove2.me/theorems/6d2a6115-069e-43f9-ada6-8a6829ac3ca5
-- title:
--   KKT multipliers $\Lambda(x)$ of $(\mathrm P_x)$ at $d(x)$
-- statement:
--   For $x\in K$, the KKT conditions of $(\mathrm P_x)$ at its solution $d(x)$, keeping only the multipliers of the constraints $\tilde g(d;x)\le\kappa(x)e$, are
--   $$0\in\nabla_1\tilde f(d(x);x)+\nabla_1\tilde g(d(x);x)\,\xi+N_{\beta\mathbb B^n_\infty\cap(K-x)}(d(x)),\qquad \xi\in N_{\mathbb R^m_-}\big(\tilde g(d(x);x)-\kappa(x)e\big),$$
--   i.e. $\xi\ge 0$ and $\xi^T(\tilde g(d(x);x)-\kappa(x)e)=0$. The set of such $\xi\in\mathbb R^m$ is denoted $\Lambda(x)$; $d(x)$ is a **KKT point** of $(\mathrm P_x)$ when $\Lambda(x)\neq\emptyset$.
--
--   **Formalization Note** $\nabla_1\tilde g(d;x)\xi=\sum_i\xi_i\nabla_1\tilde g_i(d;x)$. The normal cone is the published `normalCone` of $\beta\mathbb B^n_\infty\cap\{u: x+u\in K\}$ at $d(x)$, a point of that set whenever $x\in K$ and $d$ solves the subproblem.
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, pp.12–13; (18), p.14

import Mathlib
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone
import Definitions.Def_GhostPenalty_negOrthantNormalCone
import Definitions.Def_GhostPenalty_kappa

namespace GhostPenalty

open FirstOrderOpt.ConvexTheory

/-- **KKT multipliers of the subproblem (Pₓ) at its solution `d(x)`.**
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, §3, pp.12–13: "we are interested only in the multipliers corresponding to the
constraints `g̃(d;x) ≤ κ(x)e`, and therefore we find it expedient to write the KKT conditions as
`0 ∈ ∇₁f̃(d(x);x) + ∇₁g̃(d(x);x)ξ + N_{βBⁿ∞∩(K−x)}(d(x))`, with the KKT multipliers `ξ` satisfying
the conditions `ξ ≥ 0` and `ξᵀ(g̃(d(x);x) − κ(x)e) = 0`"; on p.14 written as
"`ξ^ν ∈ N_{ℝᵐ₋}(g̃(d(x^ν);x^ν) − κ(x^ν)e)`".

`KKTMult … d x` is the set `Λ(x)` of such `ξ ∈ ℝᵐ`; `d(x)` is a KKT point of (Pₓ) iff `Λ(x)` is
nonempty.

**Formalization Note.** `∇₁g̃(d;x)ξ = ∑_i ξ_i ∇₁g̃_i(d;x)`; "`0 ∈ v + N`" is "`-v ∈ N`". The
complementarity is `negOrthantNormalCone` (which includes feasibility `g̃(d(x);x) ≤ κ(x)e`; with
`ξ ≥ 0` and feasibility, `ξᵀ(g̃ − κe) = 0` is equivalent to componentwise complementarity).
`N_{βBⁿ∞∩(K−x)}` is the published `normalCone` of `box n β ∩ {u | x + u ∈ K}`; it is only used
with `x ∈ K` and `d` a solution map, so that `d(x)` lies in that set. -/
def KKTMult {n m : ℕ} (ft : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gt : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (lam ρ β : ℝ)
    (d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) :
    Set (Fin m → ℝ) :=
  {ξ | ξ ∈ negOrthantNormalCone (fun i => gt i (d x) x - kappa g gt K lam ρ x) ∧
    -(gradient (fun u => ft u x) (d x) + ∑ i, ξ i • gradient (fun u => gt i u x) (d x)) ∈
      normalCone (box n β ∩ {u | x + u ∈ K}) (d x)}

end GhostPenalty


