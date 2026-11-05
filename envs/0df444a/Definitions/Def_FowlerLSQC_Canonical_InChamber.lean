-- Prove2me | Definitions.Def_FowlerLSQC_Canonical_InChamber
-- name    : FowlerLSQC_Canonical_InChamber
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:34:52.591873+00:00
-- url     : https://prove2.me/theorems/1119f705-813f-4f37-963a-c6e42c03695b
-- title:
--   The uniqueness conditions on $\vec\theta$
-- statement:
--   A parameter vector $\vec\theta=(\theta_1,\theta_2,\theta_3)\in\mathbb R^3$ satisfies the **uniqueness conditions** of a canonical decomposition when
--   $$
--   \theta_1\ge\theta_2,\qquad \tfrac\pi2-\theta_1\ge\theta_2,\qquad \theta_2\ge\theta_3,\qquad \theta_3\ge0,
--   $$
--   and, if $\theta_3=0$, also $\tfrac\pi2-\theta_1\ge\theta_1$.
--
--   These five conditions single out one representative of each class of locally equivalent non-local parameters (a Weyl chamber). The last clause matters: without it, $(\theta_1,\theta_2,0)$ and $(\pi/2-\theta_1,\theta_2,0)$ would both satisfy the conditions although they describe the same gate up to local operations.
--
--   **Formalization Note** `θ 0, θ 1, θ 2` are $\theta_1,\theta_2,\theta_3$. The predicate is exactly the five printed conditions.
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, §4.2, p.49 (PDF p.67); §4.4, p.53 (PDF p.71)

import Mathlib

namespace FowlerLSQC.Canonical

/-- Fowler, *Towards Large-Scale Quantum Computation*, arXiv:quant-ph/0506126v1, §4.2, p.49
(PDF p.67), repeated in §4.4, p.53 (PDF p.71): the conditions that make the non-local parameters
of a canonical decomposition unique,
`θ1 ≥ θ2`, `π/2 − θ1 ≥ θ2`, `θ2 ≥ θ3`, `θ3 ≥ 0`, and `π/2 − θ1 ≥ θ1` if `θ3 = 0`.

**Formalization Note.** `θ 0, θ 1, θ 2` are the book's `θ1, θ2, θ3`. The five conditions are
exactly the printed ones; nothing is added (`θ1 < π/2` and the other bounds follow). -/
def InChamber (θ : Fin 3 → ℝ) : Prop :=
  θ 1 ≤ θ 0 ∧ θ 1 ≤ Real.pi / 2 - θ 0 ∧ θ 2 ≤ θ 1 ∧ 0 ≤ θ 2 ∧
    (θ 2 = 0 → θ 0 ≤ Real.pi / 2 - θ 0)

end FowlerLSQC.Canonical


