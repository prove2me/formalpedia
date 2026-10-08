-- Prove2me | Definitions.Def_MFGPlanning_Penalized_Scheme
-- name    : MFGPlanning_Penalized_Scheme
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:38:41.364252+00:00
-- url     : https://prove2.me/theorems/0fdc11a5-fbd9-495d-b20a-4bf01cb8528e
-- title:
--   The discrete planning scheme (18) and the penalized scheme (20)–(23)
-- statement:
--   Let $U = (U^n)_{0 \le n \le N_T}$ and $M = (M^n)_{0 \le n \le N_T}$ be families of grid functions.
--
--   **The planning scheme (18)** (equivalently (43)–(46)): for $n = 0, \dots, N_T - 1$ and all grid points,
--   $$
--   \frac{U^{n+1}_{i,j} - U^n_{i,j}}{\Delta t} - \nu(\Delta_hU^{n+1})_{i,j} + g(x_{i,j}, [D_hU^{n+1}]_{i,j}) = V(M^n_{i,j}),
--   $$
--   $$
--   \frac{M^{n+1}_{i,j} - M^n_{i,j}}{\Delta t} + \nu(\Delta_hM^n)_{i,j} + \mathcal B_{i,j}(U^{n+1}, M^n) = 0,
--   $$
--   together with $M^n \in \mathcal K$ for $n = 0, \dots, N_T$, $M^{N_T} = m_T$ and $M^0 = m_0$.
--
--   **The penalized scheme (20)–(23)**, for $\varepsilon > 0$: the same two equations for $n = 0, \dots, N_T - 1$, with $M^n \in \mathcal K$ for $n = 0, \dots, N_T - 1$, and the time conditions
--   $$
--   U^0_{i,j} = \frac{1}{\varepsilon}\big(M^0_{i,j} - (m_0)_{i,j}\big), \qquad M^{N_T}_{i,j} = (m_T)_{i,j}.
--   $$
--   The penalized scheme replaces the initial condition $M^0 = m_0$ of the planning problem by a penalty coupling $U^0$ to $M^0$.
--
--   **Formalization Note** Time levels are the indices of `Fin (NT + 1)`; level $n+1$ is `n.succ` and level $n$ is `n.castSucc` for `n : Fin NT`. The discrete coupling $V_h[M]$ is $V(M_{i,j})$, as (24) prescribes. The right side of (20) is printed $(V_h[M^n])$ without $\varepsilon$; it is the scheme's own $M^{\varepsilon,n}$.
-- source:
--   Achdou, Camilli, Capuzzo-Dolcetta, Mean field games: numerical methods for the planning problem, hal-00465404v1 (2010), §2.1 (18), p. 6; §2.2 (20)–(23), p. 6; (43)–(46), p. 12

import Mathlib
import Definitions.Def_MFGPlanning_Penalized_Grid

namespace MFGPlanning.Penalized

/-- (U, M) solves the semi-implicit planning scheme (18), p. 6 (= (43)–(46), p. 12), with
V_h[M] = V(M) as in (24). Time levels n = 0, …, N_T are the indices of `Fin (NT + 1)`:
* for n = 0, …, N_T − 1 and all grid points, the discrete HJB equation
  (U^{n+1} − U^n)/Δt − ν Δ_hU^{n+1} + g(x, [D_hU^{n+1}]) = V(M^n);
* the discrete Fokker–Planck equation
  (M^{n+1} − M^n)/Δt + ν Δ_hM^n + B(U^{n+1}, M^n) = 0;
* M^n ∈ K for n = 0, …, N_T;
* M^{N_T} = m_T and M^0 = m_0. -/
def IsPlanningSol (d : Data) (U M : Fin (d.NT + 1) → Pt d → ℝ) : Prop :=
  (∀ (n : Fin d.NT) (p : Pt d),
      (U n.succ p - U n.castSucc p) / d.Δt - d.ν * lap d (U n.succ) p
        + d.g p (Dh d (U n.succ) p) = d.V (M n.castSucc p)) ∧
  (∀ (n : Fin d.NT) (p : Pt d),
      (M n.succ p - M n.castSucc p) / d.Δt + d.ν * lap d (M n.castSucc) p
        + B d (U n.succ) (M n.castSucc) p = 0) ∧
  (∀ n, InK d (M n)) ∧
  M (Fin.last d.NT) = d.mT ∧ M 0 = d.m0

/-- (U, M) = (U^{ε,n}, M^{ε,n}) solves the penalized scheme (20)–(23), p. 6:
* (20) for n = 0, …, N_T − 1: (U^{n+1} − U^n)/Δt − ν Δ_hU^{n+1} + g(x, [D_hU^{n+1}]) = V(M^{ε,n})
  (the page prints V_h[M^n] without ε; the coupling is the scheme's own M^{ε,n});
* (21) (M^{n+1} − M^n)/Δt + ν Δ_hM^n + B(U^{n+1}, M^n) = 0;
* (22) M^n ∈ K for n = 0, …, N_T − 1;
* (23) U^0 = (M^0 − m_0)/ε and M^{N_T} = m_T. -/
def IsPenalizedSol (d : Data) (ε : ℝ) (U M : Fin (d.NT + 1) → Pt d → ℝ) : Prop :=
  (∀ (n : Fin d.NT) (p : Pt d),
      (U n.succ p - U n.castSucc p) / d.Δt - d.ν * lap d (U n.succ) p
        + d.g p (Dh d (U n.succ) p) = d.V (M n.castSucc p)) ∧
  (∀ (n : Fin d.NT) (p : Pt d),
      (M n.succ p - M n.castSucc p) / d.Δt + d.ν * lap d (M n.castSucc) p
        + B d (U n.succ) (M n.castSucc) p = 0) ∧
  (∀ n : Fin d.NT, InK d (M n.castSucc)) ∧
  (∀ p, U 0 p = (M 0 p - d.m0 p) / ε) ∧ M (Fin.last d.NT) = d.mT

end MFGPlanning.Penalized


