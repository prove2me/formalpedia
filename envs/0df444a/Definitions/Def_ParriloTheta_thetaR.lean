-- Prove2me | Definitions.Def_ParriloTheta_thetaR
-- name    : ParriloTheta_thetaR
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:52.002019+00:00
-- url     : https://prove2.me/theorems/ef4dad15-a22d-4d8c-b8e5-71e6a4414ef6
-- title:
--   The bound $\vartheta^{(r)}(G)$
-- statement:
--   For a graph $G$ on a finite vertex set and $r\in\mathbb N$, de Klerk and Pasechnik's bound is
--   $$
--   \vartheta^{(r)}(G)=\min\{t\in\mathbb R:\ t(A_G+I)-J\in\mathcal K^{(r)}\}.
--   $$
--   It satisfies $\alpha(G)\le\vartheta^{(r+1)}(G)\le\vartheta^{(r)}(G)$, and the minimum is attained. The bound is *exact at order $r$* when $\vartheta^{(r)}(G)=\alpha(G)$.
--
--   **Formalization Note** The minimum is the infimum `sInf` of the feasible set in $\mathbb R$. For a nonempty graph that set is nonempty and bounded below by $\alpha(G)$, so no junk value arises. For the graph with no vertices every $t$ is feasible and Lean's value is $0=\alpha$.
-- source:
--   Laurent & Vargas, Exactness of Parrilo's conic approximations for copositive matrices and associated low order bounds for the stability number of a graph, arXiv:2109.12876v1, eq. (1.6), p.2

import Mathlib
import Definitions.Def_ParriloTheta_InK

namespace ParriloTheta

open Classical in
/-- **The bound `ϑ^(r)(G)` of de Klerk and Pasechnik.**
Laurent & Vargas, arXiv:2109.12876v1, eq. (1.6), p.2:
"ϑ(r)(G) = min{t : t(AG + I) − J ∈ K(r)_n}", with the remark "Note the minimum is indeed attained
in program (1.6)".

`thetaR r G` is the infimum of the reals `t` with `t(A_G + I) − J ∈ K^(r)`.

**Formalization Note.** The minimum is written as `sInf` over `ℝ`. For a nonempty finite vertex
set the feasible set is nonempty (it contains every `t ≥ |V|`) and bounded below by `α(G)`, so the
`sInf` is the paper's minimum and takes no junk value. For the empty graph every `t` is feasible
and Lean's `sInf` of the unbounded set is `0 = α(∅)`. `A_G` uses classical decidability. -/
noncomputable def thetaR {V : Type*} [Fintype V] (r : ℕ) (G : SimpleGraph V) : ℝ :=
  sInf {t : ℝ | InK r (t • (G.adjMatrix ℝ + 1) - Matrix.of (fun _ _ => (1 : ℝ)))}

end ParriloTheta


