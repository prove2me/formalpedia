-- Prove2me | Definitions.Def_BauerleRiederMDP_PartialObs_bellmanQ
-- name    : BauerleRiederMDP_PartialObs_bellmanQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:01:58.598212+00:00
-- url     : https://prove2.me/theorems/d76b8eea-ee5f-4a55-bd2a-67f31a790d50
-- title:
--   The Bellman integrand $\int\!\int v((1+i)(x+a\cdot z),\Phi(\rho,z))\,Q^R(dz|y)\,\rho(dy)$
-- statement:
--   For a function $v$ on $E_X\times\mathbb P(E_Y)$, a state $(x,\rho)$ and an action $a\in\mathbb R^d$, let
--   $$
--   L v(x,\rho,a):=\int\!\!\int v\big((1+i)(x+a\cdot z),\Phi(\rho,z)\big)\,Q^R(dz\mid y)\,\rho(dy).
--   $$
--   This is the expected value of $v$ after one stage of the filtered model; the Bellman equation of Theorem 6.1.1 is $J_n(x,\rho)=\sup_{a\in D(x)} L J_{n-1}(x,\rho,a)$.
--
--   **Formalization Note** Both integrals are extended-real ($\int f^+-\int f^-$).
-- source:
--   Bäuerle & Rieder (2011), Theorem 6.1.1 b), p.177 (PDF 190)

import Mathlib
import Definitions.Def_BauerleRiederMDP_PartialObs_Market_Phi
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_eint

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BauerleRiederMDP.PartialObs

/-- **The expected next-stage value of an action in the filtered terminal wealth model.**
Bäuerle & Rieder (2011), Theorem 6.1.1 b), p.177 (PDF 190): for a function `v` on
`E_X × IP(E_Y)`, state `(x, ρ)` and action `a`,

`bellmanQ M i v x ρ a = ∫ ∫ v((1 + i)(x + a · z), Φ(ρ, z)) Q^R(dz|y) ρ(dy)`,

the quantity maximized over `a ∈ D(x)` in the Bellman equation (with `v = J_{n−1}`).

**Formalization Note.** Both integrals are `eint` (extended-real, positive minus negative
part); the inner one is over `Q^R(·|y)`, the outer one over `ρ`. -/
noncomputable def bellmanQ {EY : Type*} [MeasurableSpace EY] {d : ℕ} (M : Market EY d) (i : ℝ)
    (v : ℝ → ProbabilityMeasure EY → EReal) (x : ℝ) (ρ : ProbabilityMeasure EY)
    (a : Fin d → ℝ) : EReal :=
  BauerleRiederMDP.RegimeSwitching.eint (ρ : Measure EY) (fun y => BauerleRiederMDP.RegimeSwitching.eint (M.QR y)
    (fun z => v ((1 + i) * (x + a ⬝ᵥ z)) (M.Phi ρ z)))

end BauerleRiederMDP.PartialObs


