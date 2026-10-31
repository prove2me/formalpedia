-- Prove2me | Definitions.Def_RBMSensitivity_IsMarkovSemigroup
-- name    : RBMSensitivity_IsMarkovSemigroup
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:27:43.537835+00:00
-- url     : https://prove2.me/theorems/9a24f1ed-982c-4189-9b23-e2784688530a
-- title:
--   A Markov transition semigroup
-- statement:
--   A family $\{\mathcal P_t,t\ge 0\}$ of Markov kernels on a measurable space with $\mathcal P_0$ the identity and $\mathcal P_{s+t}=\mathcal P_s\mathcal P_t$ for all $s,t\ge 0$.
--
--   It is the setting of the asymptotic coupling theorem.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Theorem 8.1, p.33

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- A Markov transition semigroup `{P_t, t ≥ 0}` on `S`: arXiv:1907.00472v2, Theorem 8.1, p.33. Each
`P_t` is a Markov kernel, `P_0` is the identity, and `P_{s+t} = P_t ∘ P_s`. -/
def IsMarkovSemigroup {S : Type*} [MeasurableSpace S] (Pt : ℝ≥0 → Kernel S S) : Prop :=
  (∀ t, IsMarkovKernel (Pt t)) ∧ Pt 0 = Kernel.id ∧ ∀ s t, Pt (s + t) = Pt t ∘ₖ Pt s

end RBMSensitivity


