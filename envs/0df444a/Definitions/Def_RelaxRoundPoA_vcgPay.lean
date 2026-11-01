-- Prove2me | Definitions.Def_RelaxRoundPoA_vcgPay
-- name    : RelaxRoundPoA_vcgPay
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:59.007393+00:00
-- url     : https://prove2.me/theorems/dbd404f5-5168-450a-8e86-7546eac68160
-- title:
--   VCG (Clarke pivot) expected payment
-- statement:
--   Let $M=(f,p)$ be an exact declared welfare maximizer over $F$. The **VCG payment** of agent $i$ on bid profile $b$ is, in expectation,
--
--   $$
--   p_i^{\mathrm{VCG}}(b)=\sup_{y\in F}\sum_{j\ne i}b_j(y)\;-\;\mathbf E\Bigl[\sum_{j\ne i}b_j\bigl(f(b)\bigr)\Bigr],
--   $$
--
--   the best declared welfare the other agents could get, minus what they get at the outcome. The first term does not depend on agent $i$'s bid, which makes the resulting mechanism truthful.
--
--   **Formalization Note** The supremum is a real supremum. When $M$ is an exact maximizer over $F$, the set of values is nonempty and bounded above by the maximal declared welfare, so the supremum is the true one (not a junk value); it equals the Clarke pivot maximum when that is attained.
-- source:
--   Dütting, Kesselheim, Tardos, Algorithms as Mechanisms: The Price of Anarchy of Relax-and-Round, arXiv:1511.09208v1, §3, proof of Lemma 1, p.8

import Mathlib
import Definitions.Def_RelaxRoundPoA_Mechanism

open MeasureTheory NNReal

namespace RelaxRoundPoA

/-- **VCG (Clarke pivot) expected payment for an exact maximizer.**
Dütting, Kesselheim, Tardos, arXiv:1511.09208v1, §3, p.8 (proof of Lemma 1): "The allocation
function `f` optimizes exactly over its outcome space. Therefore, it can be used to implement a
truthful mechanism `M^VCG = (f, p^VCG)` by applying VCG payments."

`vcgPay M Feas b i` is agent `i`'s expected VCG payment on bid profile `b`: the best declared
welfare of the other agents over the feasible outcomes, minus their expected declared welfare at the
outcome of `M`:
`p_i^VCG(b) = sup_{y∈Feas} ∑_{j≠i} b_j(y) − E[∑_{j≠i} b_j(f(b))]`.

**Formalization Note** The supremum is a real `sSup`. When `M` is an exact maximizer over `Feas`
(`IsExactMaximizer`), the set `{∑_{j≠i} b_j(y) : y ∈ Feas}` is nonempty and bounded above by the
maximal declared welfare, so the `sSup` is the true supremum, never the junk value `0`; it equals
the Clarke pivot maximum whenever that is attained. -/
noncomputable def vcgPay {N : Type*} [Fintype N] [DecidableEq N] {Ω' : Type*} [MeasurableSpace Ω']
    (M : Mechanism N Ω') (Feas : Set Ω') (b : N → Ω' → ℝ≥0) (i : N) : ℝ :=
  sSup ((fun y => ∑ j ∈ Finset.univ.erase i, (b j y : ℝ)) '' Feas) -
    ∫ x, ∑ j ∈ Finset.univ.erase i, (b j x : ℝ) ∂(M.outcome b)

end RelaxRoundPoA


