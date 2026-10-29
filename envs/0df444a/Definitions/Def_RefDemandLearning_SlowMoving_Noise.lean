-- Prove2me | Definitions.Def_RefDemandLearning_SlowMoving_Noise
-- name    : RefDemandLearning_SlowMoving_Noise
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T05:22:09.569583+00:00
-- url     : https://prove2.me/theorems/53e107d0-c342-4a3a-bbb4-5717f1257d9a
-- title:
--   Independent real noise with a local moment generating function
-- statement:
--   On a probability space $(\Omega,\mathcal F,P)$, let $(\varepsilon_n)_{n\ge0}$ be measurable real random variables. The admissibility predicate says that the whole family is independent, every coordinate has the same law as $\varepsilon_0$, and
--   $$\mathbb E\varepsilon_0=0,\qquad \mathbb E\varepsilon_0^2<\infty,\qquad \exists m_0>0\;\forall |m|\le m_0:\ \mathbb E e^{m\varepsilon_0}<\infty.$$
--   The first moment, second moment and exponential moments are expressed using integrability, preventing nonintegrable functions from acquiring default integral values. This permits arbitrary iid local-MGF laws, including zero noise. No boundedness, Gaussianity, positive variance or global sub-Gaussian assumption is made.
--
--   **Formalization Note.** This generic noise predicate is separate from the pricing model. A probability-measure instance is supplied by each theorem using it. Index zero is the paper's first shock. The law and $m_0$ are not inputs to the seller's policy.
-- source:
--   den Boer and Keskin, Dynamic Pricing with Demand Learning and Reference Effects, DOI https://doi.org/10.1287/mnsc.2021.4234, supplied April 19, 2021 artifact, Section 2, printed/PDF p. 7, standing assumptions following (2.1)

import Mathlib

set_option autoImplicit false
open MeasureTheory ProbabilityTheory

namespace RefDemandLearning.SlowMoving

/-- A generic iid real noise process with the local MGF condition. Index 0 is source time 1. -/
def AdmissibleNoise {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ε : ℕ → Ω → ℝ) : Prop :=
  (∀ n, Measurable (ε n)) ∧ iIndepFun ε P ∧
  (∀ n, IdentDistrib (ε n) (ε 0) P P) ∧
  Integrable (ε 0) P ∧ (∫ ω, ε 0 ω ∂P) = 0 ∧
  Integrable (fun ω => (ε 0 ω) ^ 2) P ∧
  ∃ m₀ : ℝ, 0 < m₀ ∧ ∀ m : ℝ, |m| ≤ m₀ →
    Integrable (fun ω => Real.exp (m * ε 0 ω)) P

end RefDemandLearning.SlowMoving


