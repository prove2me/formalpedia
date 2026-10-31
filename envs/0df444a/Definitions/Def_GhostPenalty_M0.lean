-- Prove2me | Definitions.Def_GhostPenalty_M0
-- name    : GhostPenalty_M0
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:34:45.691002+00:00
-- url     : https://prove2.me/theorems/90ef029f-9a36-4deb-a6db-084188cc7f6c
-- title:
--   Fritz-John multiplier set $M_0(x)$
-- statement:
--   For $x\in\mathbb R^n$, with $e\in\mathbb R^m$ the vector of ones,
--   $$M_0(x)\triangleq\{\xi\ :\ \xi\in N_{\mathbb R^m_-}\big(g(x)-\max_i\{g_i(x)_+\}e\big),\ 0\in\nabla g(x)\xi+N_K(x)\}.$$
--   Since $g(x)-\max_i\{g_i(x)_+\}e\le 0$, the first condition says $\xi\ge 0$ and $\xi_i=0$ unless $g_i(x)=\max_j\{g_j(x)_+\}$. For $x\in K$ always $0\in M_0(x)$; $M_0(x)\ne\{0\}$ is the Fritz-John condition at feasible points and stationarity of the violation problem at infeasible ones.
--
--   **Formalization Note** $N_K(x)$ is the published `normalCone` used with $x\in K$.
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, §2, p.5

import Mathlib
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone
import Definitions.Def_GhostPenalty_negOrthantNormalCone
import Definitions.Def_GhostPenalty_posMax

namespace GhostPenalty

open FirstOrderOpt.ConvexTheory

/-- **The Fritz-John multiplier set `M0(x)`.**
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, §2, p.5:
"`M0(x) ≜ { ξ | ξ ∈ N_{ℝᵐ₋}(g(x) − max_i{g_i(x)+} e), 0 ∈ ∇g(x)ξ + N_K(x) }`, where … `∇g` is the
transposed Jacobian of `g`", with `e ∈ ℝᵐ` the vector of ones (p.6).

**Formalization Note.** `∇g(x)ξ = ∑_i ξ_i ∇g_i(x)`; "`0 ∈ v + N_K(x)`" is "`-v ∈ N_K(x)`".
`N_K(x)` is the published `normalCone`, used together with `x ∈ K` (the classical normal cone
is empty off `K`). The point `g(x) − max_i{g_i(x)₊} e` always lies in `ℝᵐ₋`, so the orthant
part is `ξ ≥ 0, ξ_i (g_i(x) − max_j{g_j(x)₊}) = 0`. For `x ∈ K`, `0 ∈ M0(x)`. -/
def M0 {n m : ℕ} (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) : Set (Fin m → ℝ) :=
  {ξ | ξ ∈ negOrthantNormalCone (fun i => g i x - posMax g x) ∧ x ∈ K ∧
    -(∑ i, ξ i • gradient (g i) x) ∈ normalCone K x}

end GhostPenalty


