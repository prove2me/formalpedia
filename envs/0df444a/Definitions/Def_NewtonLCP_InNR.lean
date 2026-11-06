-- Prove2me | Definitions.Def_NewtonLCP_InNR
-- name    : NewtonLCP_InNR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:30:36.646407+00:00
-- url     : https://prove2.me/theorems/322ef2b5-b7c6-406d-b1cc-56bd62526cd5
-- title:
--   The Rump-norm neighbourhood $\mathcal N^R(\beta)$
-- statement:
--   For LCP$(M,q)$ with $M\in\mathcal P_\star$ and $\beta\ge0$, the **Rump-norm neighbourhood of the central path** is
--
--   $$\mathcal N^R(\beta)=\{(x,s,\mu):(x,s)\in\mathcal F_{>0}(M,q),\ \mu>0,\ \|Q_{H_{x,\mu}}\mathrm{err}(x,s,\mu)\|_2\le\beta\},$$
--
--   where $H_{x,\mu}$ is the Newton matrix and $Q_H$ the diagonal matrix of Rump weights.
--
--   Since $q_H\ge1_n$, $\mathcal N^R(\beta)\subseteq\mathcal N^2(\beta)$; Theorem 6.4 shows that two Newton steps keep the iterates in $\mathcal N^R(\beta)$.
--
--   **Formalization Note** The predicate is defined for every $M$; the theorems using it assume $M\in\mathcal P_\star(\kappa)$.
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab…), Definition 5.5, p.15

import Mathlib
import Definitions.Def_NewtonLCP_NewtonStep
import Definitions.Def_NewtonLCP_RumpWeight

open Matrix

namespace NewtonLCP

/-!
# The Rump-norm neighbourhood `N^R(β)`

Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab…40f8), Definition 5.5, p.15.

`N^R(β) = {(x, s, µ) : (x, s) ∈ F_{>0}, µ > 0, ‖Q_{H_{x,µ}} err(x, s, µ)‖₂ ≤ β}`, where
`H_{x,µ}` is the Newton matrix (Definition 4.1) and `Q_H = diag(q_H)` the Rump weights
(Definition 5.2).

**Formalization Note.** The paper states the definition for an instance with `M ∈ P⋆`; the
predicate is defined for every `M`, and the theorems that use it assume `M ∈ P⋆(κ)`.
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `(x, s, µ) ∈ N^R(β)` for LCP(M, q) (Definition 5.5). -/
def InNR (M : Matrix ι ι ℝ) (q : ι → ℝ) (β : ℝ) (x s : ι → ℝ) (mu : ℝ) : Prop :=
  (x, s) ∈ FeasPos M q ∧ 0 < mu ∧
    l2norm (fun i => rumpWeight (newtonMatrix M x mu) i * err x s mu i) ≤ β

end NewtonLCP


