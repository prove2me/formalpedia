-- Prove2me | Definitions.Def_MFGPlanning_Existence_Scheme
-- name    : MFGPlanning_Existence_Scheme
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:39:31.804701+00:00
-- url     : https://prove2.me/theorems/235a9b07-53bc-454f-9103-ea031d3d0ebd
-- title:
--   The fully discrete planning scheme (18)
-- statement:
--   With the grid operators of the mission and $(V_h[M])_{i,j} = V(M_{i,j})$ as in (24), a pair of families $U = (U^n_{i,j})$, $M = (M^n_{i,j})$, $n = 0,\dots,N_T$, solves the **fully discrete planning scheme** (18) when
--   $$\frac{U^{n+1}_{i,j}-U^n_{i,j}}{\Delta t} - \nu(\Delta_hU^{n+1})_{i,j} + g(x_{i,j},[D_hU^{n+1}]_{i,j}) = V(M^n_{i,j}),$$
--   $$\frac{M^{n+1}_{i,j}-M^n_{i,j}}{\Delta t} + \nu(\Delta_hM^n)_{i,j} + \mathcal B_{i,j}(U^{n+1},M^n) = 0,$$
--   for $n = 0,\dots,N_T-1$ and all $i,j$; $M^n\in\mathcal K$ for $n = 0,\dots,N_T$; and $M^{N_T} = m_T$, $M^0 = m_0$.
--
--   The first line is a semi-implicit discretization of the backward Hamilton–Jacobi equation, the second of the forward Fokker–Planck equation; the two boundary conditions in time make it a *planning* problem.
--
--   **Formalization Note** Time level $n$ is the index `n : Fin (NT+1)`; the equations for $0\le n<N_T$ use `n.castSucc` (level $n$) and `n.succ` (level $n+1$). The right-hand side is $V(M^n_{i,j})$ with $V = W'$, i.e. the local coupling $(V_h[M])_{i,j} = V(M_{i,j})$ assumed in (24).
-- source:
--   Achdou, Camilli, Capuzzo-Dolcetta, Mean field games: numerical methods for the planning problem, hal-00465404v1 (2010), §2.1, p. 6, (18); §3.1, p. 6, (24)

import Mathlib
import Definitions.Def_MFGPlanning_Existence_Grid

namespace MFGPlanning.Existence

variable (d : Data)

/-- `(U, M)` solves the fully discrete planning scheme (18), p. 6, with `(V_h[M])_{i,j} = V(M_{i,j})`
((24), p. 6): for `n = 0, …, N_T − 1` and all grid points,
`(U^{n+1} − U^n)/Δt − ν Δ_h U^{n+1} + g(x, [D_h U^{n+1}]) = V(M^n)`,
`(M^{n+1} − M^n)/Δt + ν Δ_h M^n + 𝓑(U^{n+1}, M^n) = 0`; `M^n ∈ 𝒦` for `n = 0, …, N_T`;
`M^{N_T} = m_T`, `M^0 = m_0`. Time level `n` is the index `n : Fin (N_T + 1)`. -/
def IsPlanningSol (U M : Fin (d.NT + 1) → d.Pt → ℝ) : Prop :=
  (∀ (n : Fin d.NT) (p : d.Pt),
      (U n.succ p - U n.castSucc p) / d.dt - d.ν * lap d (U n.succ) p + d.g p (Dh d (U n.succ) p)
        = d.V (M n.castSucc p)) ∧
  (∀ (n : Fin d.NT) (p : d.Pt),
      (M n.succ p - M n.castSucc p) / d.dt + d.ν * lap d (M n.castSucc) p
        + B d (U n.succ) (M n.castSucc) p = 0) ∧
  (∀ n, InK d (M n)) ∧
  M (Fin.last d.NT) = d.mT ∧ M 0 = d.m0

end MFGPlanning.Existence


