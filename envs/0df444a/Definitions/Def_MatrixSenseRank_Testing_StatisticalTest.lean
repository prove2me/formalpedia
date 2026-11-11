-- Prove2me | Definitions.Def_MatrixSenseRank_Testing_StatisticalTest
-- name    : MatrixSenseRank_Testing_StatisticalTest
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T13:46:14.532633+00:00
-- url     : https://prove2.me/theorems/f6be6fdd-b156-47a1-a002-e797d6510147
-- title:
--   Measurable finite-sample Boolean tests
-- statement:
--   For a measurable observation space $E$ and a natural sample count $T$, a statistical test is a measurable probability kernel from $E^T$ to $\{\mathrm{false},\mathrm{true}\}$. True denotes acceptance. Its average acceptance probability under independent observations with common probability law $\mu$ is
--   $$\operatorname{Acc}(K,\mu)=\int_{E^T}K(s,\{\mathrm{true}\})\,d\mu^{\otimes T}(s).$$
--   The kernel includes arbitrary private randomization. Its only defining requirements are measurability and total mass one; it contains no statistical correctness assertion. This general test object supports both the label-only sparsity test and its matrix-observation composition.
--
--   **Formalization Note** The object is a subtype of Mathlib's `Kernel` with `IsMarkovKernel`. Kernel masses are converted to real numbers; they are finite and in $[0,1]$. Thus every acceptance integral under a probability law is integrable. Sample indices are `Fin T`.
-- source:
--   Yiqiao Bao, Anindya De, Shivam Nadimpalli, Rocco A. Servedio, Chenyang Sun, Nathan White, STOC 2027 submission #380 (October 2026), §1.2, printed pp. 2–3 / PDF pp. 3–4; §6, Theorems 3 and 14, printed pp. 26–28 / PDF pp. 27–29; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/380.pdf; PDF SHA-256 6e4e46ced4dfe65bbe94e4cec3e8230032914efef9d87b0f544bbea151a00c3b.

import Mathlib

set_option autoImplicit false
open MeasureTheory ProbabilityTheory

namespace MatrixSenseRank.Testing

/-- A measurable probability kernel from an actual T-tuple to a Boolean decision.
True means accept. Mathlib's Markov-kernel condition asserts only total mass one. -/
abbrev StatisticalTest (α : Type) [MeasurableSpace α] (T : ℕ) :=
  {test : Kernel (Fin T → α) Bool // IsMarkovKernel test}

/-- Conditional acceptance probability, including any internal randomization. -/
noncomputable def StatisticalTest.accept {α : Type} [MeasurableSpace α] {T : ℕ}
    (test : StatisticalTest α T) (s : Fin T → α) : ℝ :=
  (test.val s {true}).toReal

/-- Average over i.i.d. observations and the kernel's Boolean decision. -/
noncomputable def acceptance {α : Type} [MeasurableSpace α] {T : ℕ}
    (test : StatisticalTest α T) (μ : Measure α) : ℝ :=
  ∫ s, test.accept s ∂Measure.pi (fun _ : Fin T => μ)

end MatrixSenseRank.Testing


