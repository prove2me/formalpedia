-- Prove2me | Definitions.Def_PrivBayesTest_errExp
-- name    : PrivBayesTest_errExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:58.257223+00:00
-- url     : https://prove2.me/theorems/c3c76944-0fa3-4b5f-95b6-a2df83250179
-- title:
--   Optimal $\varepsilon$-DP error exponent at sample size $n$
-- statement:
--   Fix $\varepsilon$, probability measures $P,Q$ on $\mathcal X$ and a prior $(\pi_0,\pi_1)$. A test $T$ on $n$ samples is **$\varepsilon$-differentially private** (Definition 1.1) if $\Pr[T(x)\in S]\le e^{\varepsilon}\Pr[T(x')\in S]$ for every set of outputs $S$ and all $x,x'\in\mathcal X^n$ differing in exactly one coordinate. The **optimal error exponent at sample size $n$** is
--
--   $$
--   E_n \;=\; \sup_{T\ \varepsilon\text{-DP}} \; -\frac1n \log P_e^{(n)}(T),
--   $$
--
--   the supremum over all $\varepsilon$-DP tests (Markov kernels from $\mathcal X^n$ to the two outputs). Theorem 3.1 states that $E_n\to C_\varepsilon(P;Q)$.
--
--   **Formalization Note** Values are extended reals, $-\log 0=+\infty$. The factor $1/n$ is the real number $n^{-1}$ (equal to $0$ at $n=0$, which does not affect limits). Differential privacy is the published `PrivLearn.Generic.IsDP`, which does not require probability measures; tests are therefore required to be Markov kernels.
-- source:
--   Jacobsen, Optimal Error Exponents for Private Bayesian Hypothesis Testing, STOC 2027 submission (manuscript sha256 abff2fdd66827f43…124ef), Theorem 3.1, p.13; Definition 1.1, p.2

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_PrivBayesTest_bayesRisk

open MeasureTheory ProbabilityTheory

namespace PrivBayesTest

/-- The **optimal ε-DP error exponent at sample size `n`**,
`sup_{M ε-DP} −(1/n) log P_e^{(n)}(M)`, the sequence whose limit is the subject of Theorem 3.1 of
Jacobsen, *Optimal Error Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), Theorem 3.1, p.13.

The supremum ranges over all ε-differentially private tests on `n` samples: Markov kernels
`κ : Xⁿ → Bool` (`true` = "`P`") satisfying `PrivLearn.Generic.IsDP` (Definition 1.1, p.2:
`Pr[κ(x) ∈ S] ≤ e^ε Pr[κ(x′) ∈ S]` for all events `S` and all `x, x′` differing in exactly one
coordinate).

**Formalization Note** Values in `EReal`; `−log 0 = +∞`. The factor `1/n` is the real `(n : ℝ)⁻¹`
(`0` at `n = 0`, a term that does not affect limits). The tests are required to be Markov kernels:
`IsDP` alone does not say that the output laws are probability measures. Tests `T ∘ M` with an
arbitrary output space `Y` are covered, since `T ∘ M` is itself an ε-DP Markov kernel to `Bool`
(post-processing) and conversely. -/
noncomputable def errExp {X : Type*} [MeasurableSpace X] (ε : ℝ) (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (π₀ π₁ : ℝ) (n : ℕ) : EReal :=
  ⨆ (κ : Kernel (Fin n → X) Bool) (_ : IsMarkovKernel κ)
    (_ : PrivLearn.Generic.IsDP (fun z => κ z) ε),
    (((n : ℝ)⁻¹ : ℝ) : EReal) * -ENNReal.log (bayesRisk P Q π₀ π₁ κ)

end PrivBayesTest


