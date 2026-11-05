-- Prove2me | Definitions.Def_BauerleRiederMDP_PartialObs_IsMaximizer
-- name    : BauerleRiederMDP_PartialObs_IsMaximizer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:02:51.349792+00:00
-- url     : https://prove2.me/theorems/4400dd0c-5daf-4ad9-b7b6-735115c3dc23
-- title:
--   A maximizer of $v$ in the filtered terminal wealth model
-- statement:
--   A decision rule $f:E_X\times\mathbb P(E_Y)\to\mathbb R^d$ is a maximizer of $v$ if it is measurable, $f(x,\rho)\in D(x)$ for all $(x,\rho)\in E$, and for every $(x,\rho)\in E$ the action $f(x,\rho)$ is a maximum point of
--   $$
--   a\mapsto\int\!\!\int v\big((1+i)(x+a\cdot z),\Phi(\rho,z)\big)\,Q^R(dz\mid y)\,\rho(dy),\qquad a\in D(x).
--   $$
--   This is Definition 2.3.6 ($T_f v=Tv$) for the filtered model of Section 6.1.
-- source:
--   Bäuerle & Rieder (2011), Definition 2.3.6, p.21 (PDF 36); Theorem 6.1.1 d), p.177 (PDF 190)

import Mathlib
import Definitions.Def_BauerleRiederMDP_PartialObs_bellmanQ
import Definitions.Def_BauerleRiederMDP_PartialObs_Dset

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BauerleRiederMDP.PartialObs

/-- **A maximizer of `v`** in the filtered terminal wealth model.
Bäuerle & Rieder (2011), Definition 2.3.6, p.21 (PDF 36) (a decision rule `f` is a maximizer of `v` if
`T_f v = T v`), in the filtered model of §6.1 as used in Theorem 6.1.1 d), p.177 (PDF 190):
"There exists a maximizer `f*_n` of `J_{n−1}`".

`IsMaximizer M i domU v f`: `f : E_X × IP(E_Y) → ℝ^d` is a decision rule (measurable, with
`f(x, ρ) ∈ D(x)` for all `(x, ρ) ∈ E`) and `f(x, ρ)` attains
`sup_{a ∈ D(x)} ∫ ∫ v((1 + i)(x + a · z), Φ(ρ, z)) Q^R(dz|y) ρ(dy)` at every `(x, ρ) ∈ E`. -/
def IsMaximizer {EY : Type*} [MeasurableSpace EY] {d : ℕ} (M : Market EY d) (i : ℝ)
    (domU : Set ℝ) (v : ℝ → ProbabilityMeasure EY → EReal)
    (f : ℝ × ProbabilityMeasure EY → Fin d → ℝ) : Prop :=
  Measurable f ∧ ∀ x ∈ domU, ∀ ρ : ProbabilityMeasure EY,
    f (x, ρ) ∈ Dset M i domU x ∧
      ∀ a ∈ Dset M i domU x, bellmanQ M i v x ρ a ≤ bellmanQ M i v x ρ (f (x, ρ))

end BauerleRiederMDP.PartialObs


