-- Prove2me | Definitions.Def_SmithHitAndRun_SymMixing_IsSymmetricMixingKernel
-- name    : SmithHitAndRun_SymMixing_IsSymmetricMixingKernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:59:03.867955+00:00
-- url     : https://prove2.me/theorems/f118ed24-1810-4137-9855-84bec9925069
-- title:
--   Symmetric transition density under Assumption (a)
-- statement:
--   Let $(S,V)$ be a measurable space with content measure $V$, and let $P(x,A)$ be the one-step law of a homogeneous Markov chain. A **symmetric mixing kernel** has a jointly measurable nonnegative transition density $f(y\mid x)$ satisfying, for every $x\in S$ and measurable $A\subseteq S$,
--   $$
--   P(x,A)=\int_A f(y\mid x)\,V(dy),\qquad f(y\mid x)=f(x\mid y)\quad(x,y\in S).
--   $$
--   The density identity is Assumption (a); the pointwise symmetry is the consequence Smith states for a symmetric mixing algorithm immediately after that assumption. This definition supplies the common hypothesis of Lemma 1 and Theorems 1–2. **Formalization Note** Strict positivity, Assumption (b), is separate. Since $P$ is a Markov kernel, the density integrates to one in each starting state; no extra normalization premise is inserted.
-- source:
--   Smith, Efficient Monte Carlo Procedures for Generating Points Uniformly Distributed over Bounded Regions, Oper. Res. 32(6) (1984), p. 1299, Assumption (a) and following symmetry sentence

import Mathlib.Probability.Kernel.SetIntegral

open MeasureTheory ProbabilityTheory

namespace SmithHitAndRun.SymMixing

/-- Assumption (a) for the transition kernel, together with the pointwise symmetry of the
transition density asserted for symmetric mixing algorithms on Smith's p. 1299. The strictly
positive density in Assumption (b) is stated separately where needed. -/
def IsSymmetricMixingKernel {α : Type*} [MeasurableSpace α]
    (V : Measure α) (P : Kernel α α) (f : α → α → ENNReal) : Prop :=
  Measurable (Function.uncurry f) ∧
  (∀ x A, MeasurableSet A → P x A = ∫⁻ y in A, f y x ∂V) ∧
  (∀ x y, f y x = f x y)

end SmithHitAndRun.SymMixing


