-- Prove2me | Definitions.Def_FreedmanTail_Qlam
-- name    : FreedmanTail_Qlam
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:07:55.947717+00:00
-- url     : https://prove2.me/theorems/e08dc46d-f0d8-457f-8b16-14dd1f3e7cb5
-- title:
--   Freedman's transformation $Q_\lambda(v, y) = \exp\{\lambda y - e(\lambda) v\}$
-- statement:
--   For $\lambda \in \mathbb R$, $v \in [0, \infty]$ and $y \in \mathbb R$ define
--   $$Q_\lambda(v, y) = \exp\{\lambda y - e(\lambda) v\} \quad (v < \infty), \qquad Q_\lambda(\infty, y) = 0 ,$$
--   where $e(\lambda) = e^\lambda - 1 - \lambda$. Evaluated along the process, $Q_\lambda(T_n, S_n)$ is the expectation-decreasing process from which all of Freedman's upper bounds follow.
--
--   **Formalization Note** The value lies in $[0, \infty]$ (it is always finite) so that its conditional expectations and integrals need no integrability argument. The value $0$ at $v = \infty$ is the limit of $\exp\{\lambda y - e(\lambda)v\}$ as $v \to \infty$ for $\lambda > 0$; for $\lambda = 0$ it is a convention.
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975) 100–118, doi:10.1214/aop/1176996452, (1.2) Definition (d), p. 101

import Mathlib
import Definitions.Def_FreedmanTail_eFun

open scoped ENNReal

namespace FreedmanTail

/-- **The transformation `Q_λ(v, y) = exp{λy − e(λ)v}`.**
Freedman, *On Tail Probabilities for Martingales*, Ann. Probab. 3 (1975) 100–118,
(1.2) Definition (d), p. 101: "(d) Q_λ(v, y) = exp{λy − e(λ)v}".

`Qlam l v y` for `v ∈ [0, ∞]`, `y ∈ ℝ`: `exp(l·y − e(l)·v)` (as an element of `ℝ≥0∞`) when
`v < ∞`, and `0` when `v = ∞`.

**Formalization Note.** The variance clock `v = T_n` takes values in `[0, ∞]` because the
conditional variances `V_n` may be infinite (no integrability is assumed). At `v = ∞` the value
is the limit `0` of `exp{λy − e(λ)v}` as `v → ∞` for `λ > 0`; for `λ = 0` (where `e(0) = 0`)
the value `0` at `v = ∞` is a convention, the paper's formula being `exp{0 − 0·∞}`. The value
lies in `ℝ≥0∞` so that conditional expectations and integrals of `Q_λ` need no integrability
argument; it is always finite. -/
noncomputable def Qlam (l : ℝ) (v : ℝ≥0∞) (y : ℝ) : ℝ≥0∞ :=
  if v = ⊤ then 0 else ENNReal.ofReal (Real.exp (l * y - eFun l * v.toReal))

end FreedmanTail


