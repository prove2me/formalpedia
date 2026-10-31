-- Prove2me | Definitions.Def_RobustToDynamics_gamma
-- name    : RobustToDynamics_gamma
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:36.633395+00:00
-- url     : https://prove2.me/theorems/674cc562-b679-41f0-b5ca-0da1e86aeb02
-- title:
--   The shrinkage factor $\gamma=1-1/\max_i(M_{ii}+\sum_{j\ne i}|M_{ij}|)$ of (2.17)
-- statement:
--   For a real $n\times n$ matrix $M$, display (2.17) sets
--   $$
--   \gamma=1-\frac{1}{\max_{i\in\{1,\dots,n\}}\bigl\{M_{ii}+\sum_{j\neq i}|M_{ij}|\bigr\}}.
--   $$
--   For the Lyapunov solution $M$ of (2.14), $\gamma\in[0,1)$ and $G^TMG\preceq\gamma M$: one step of the dynamics shrinks every ellipsoid $E(\alpha)$ to $E(\gamma\alpha)$.
--
--   **Formalization Note** For $n=0$ the maximum over the empty index set is taken to be $1$, so $\gamma=0$.
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, Theorem 2.7, proof, Step 3, display (2.17), p.15

import Mathlib

open Matrix

namespace RobustToDynamics

/-- **The shrinkage factor `γ` of (2.17).**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, Theorem 2.7, proof,
Step 3, display (2.17), p.15:
"γ = 1 − 1 / max_{i∈{1,...,n}}{Mii + ∑_{j≠i} |Mi,j|}".

**Formalization Note.** The maximum is over `i : Fin n` (`Finset.sup'`). For `n = 0` the index set
is empty and the maximum is taken to be `1` by convention, so `γ = 0`; every statement of the
mission is trivial in dimension `0`. -/
noncomputable def gamma {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  1 - 1 / (if h : (Finset.univ : Finset (Fin n)).Nonempty then
      Finset.univ.sup' h (fun i => M i i + ∑ j ∈ Finset.univ.erase i, |M i j|)
    else 1)

end RobustToDynamics


