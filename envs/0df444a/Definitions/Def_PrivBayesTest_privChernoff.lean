-- Prove2me | Definitions.Def_PrivBayesTest_privChernoff
-- name    : PrivBayesTest_privChernoff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:08.98748+00:00
-- url     : https://prove2.me/theorems/51456915-a4fe-4ac1-b3b3-a462bb062413
-- title:
--   Private Chernoff information $C_\varepsilon(P;Q)$ (Definition 1.2)
-- statement:
--   For $\varepsilon>0$ and probability measures $P,Q$ on $\mathcal X$, let
--
--   $$
--   c_n \;=\; \sup_{M\ \varepsilon\text{-DP}} \frac1n\, C\big(M(P^n);\,M(Q^n)\big),
--   $$
--
--   where the supremum ranges over every measurable output space $\mathcal Y$ and every $\varepsilon$-DP mechanism $M$ (Markov kernel) from $\mathcal X^n$ to $\mathcal Y$, and $C$ is the Chernoff information. The **private Chernoff information** is
--
--   $$
--   C_\varepsilon(P;Q) \;=\; \lim_{n\to\infty} c_n .
--   $$
--
--   It is the largest Chernoff information per sample that an $\varepsilon$-DP mechanism can preserve, and Theorem 3.1 shows it is the optimal private error exponent.
--
--   **Formalization Note** The output spaces range over all types in the lowest universe with an arbitrary $\sigma$-algebra, which contains $\mathbb R$ (the output space of the Laplace mechanism). The limit is Lean's `limUnder`, a junk value if $(c_n)$ does not converge; the printed definition presupposes the limit, and Theorems 1.3 and 3.1 of the mission state the convergence explicitly. Values are extended reals.
-- source:
--   Jacobsen, Optimal Error Exponents for Private Bayesian Hypothesis Testing, STOC 2027 submission (manuscript sha256 abff2fdd66827f43…124ef), Definition 1.2, eq. (3), p.5

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_PrivBayesTest_chernoff
import Definitions.Def_PrivBayesTest_outLaw

open MeasureTheory ProbabilityTheory Filter

namespace PrivBayesTest

/-- The sequence inside Definition 1.2 of Jacobsen, *Optimal Error Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), Definition 1.2, eq. (3), p.5:
`n ↦ sup_{M ε-DP} (1/n) C(M(Pⁿ); M(Qⁿ))`.

The supremum ranges over every output space `Y` (a type with any σ-algebra) and every ε-DP
mechanism on `n` samples, i.e. every Markov kernel `κ : Xⁿ → Y` with `PrivLearn.Generic.IsDP`
(Definition 1.1, p.2, replace-one neighbours).

**Formalization Note** Output spaces range over `Y : Type` (universe 0) with an arbitrary
`MeasurableSpace`; this contains every output space the paper uses (`ℝ` for the Laplace mechanism).
Values in `EReal`; `(n : ℝ)⁻¹ = 0` at `n = 0`. Mechanisms are required to be Markov kernels. -/
noncomputable def chernoffSeq {X : Type*} [MeasurableSpace X] (ε : ℝ) (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (n : ℕ) : EReal :=
  ⨆ (Y : Type) (_ : MeasurableSpace Y) (κ : Kernel (Fin n → X) Y) (_ : IsMarkovKernel κ)
    (_ : PrivLearn.Generic.IsDP (fun z => κ z) ε),
    (((n : ℝ)⁻¹ : ℝ) : EReal) * chernoff (outLaw κ P) (outLaw κ Q)

/-- The **private Chernoff information** `C_ε(P; Q) := lim_{n→∞} sup_{M ε-DP} (1/n) C(M(Pⁿ); M(Qⁿ))`
of Jacobsen, *Optimal Error Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), Definition 1.2, eq. (3), p.5.

**Formalization Note** The limit is Lean's `limUnder atTop` of `chernoffSeq` in `EReal`, which is
a junk value when the sequence does not converge. The printed definition presupposes that the limit
exists; every theorem of the mission that uses `privChernoff` and needs the limit states the
convergence of `chernoffSeq` explicitly (Theorem 1.3, Theorem 3.1). -/
noncomputable def privChernoff {X : Type*} [MeasurableSpace X] (ε : ℝ) (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] : EReal :=
  limUnder atTop (chernoffSeq ε P Q)

end PrivBayesTest


