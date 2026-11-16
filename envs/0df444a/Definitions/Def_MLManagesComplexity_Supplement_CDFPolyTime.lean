-- Prove2me | Definitions.Def_MLManagesComplexity_Supplement_CDFPolyTime
-- name    : MLManagesComplexity_Supplement_CDFPolyTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:05:11.979567+00:00
-- url     : https://prove2.me/theorems/2b422b05-c710-4077-b8b0-d50825b79153
-- title:
--   Rationals by numerator and denominator; a lexicographic CDF computable in polynomial time
-- statement:
--   A rational number $q$ is written in binary as its numerator in lowest terms (a sign bit followed by the absolute value in self-delimiting binary) followed by its positive denominator in self-delimiting binary; call this string $\langle q\rangle$. Different rationals have different codes.
--
--   Let $\mu=(\mu_n)_{n\in\mathbb N}$ be a family of distributions, $\mu_n$ on $\{0,1\}^n$, and let $F_{\mu_n}(x)=\sum_{z\le x}\mu_n(z)$ be the cumulative distribution function in the lexicographic order. The CDF of $\mu$ is **computable in polynomial time** if there is a single function $M:\{0,1\}^*\to\{0,1\}^*$ computable in polynomial time such that for every $n$ and every $x\in\{0,1\}^n$
--
--   $$
--   M(x)=\langle q\rangle\quad\text{for a rational } q \text{ with } q=F_{\mu_n}(x).
--   $$
--
--   This is condition 1 of Theorem A.1: values are exact rationals represented by numerator and denominator.
--
--   **Formalization Note** Polynomial time is the published `QAlgorithms.Complexity.PolyTimeComputable` (Mathlib multi-stack Turing machines with a polynomial step bound, on bit strings). Polynomial time is a property of a family, so one machine serves every length $n$; the input $x$ determines $n$. An output that is not a valid code never counts as correct.
-- source:
--   Fortnow, How Does Machine Learning Manage Complexity?, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), Theorem A.1 condition 1 and the sentence after it, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_PPADSIS_SubexpSIS_Encoding
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_MLManagesComplexity_lexCDF

set_option autoImplicit false

namespace MLManagesComplexity.Supplement

/-- The binary code of a **rational number given by numerator and denominator** (Fortnow,
*How Does Machine Learning Manage Complexity?*, arXiv:2604.07233 (version of 2026-10-31,
sha256 4874d83f…), Theorem A.1, printed p.15, PDF p.16: "Here values are rationals represented by
numerator and denominator"): the numerator of `q` in lowest terms as a self-delimiting signed
binary integer (published `PPADSIS.SubexpSIS.encInt`), followed by its (positive) denominator as a
self-delimiting binary natural number (published `PPADSIS.SubexpSIS.encNat`).

**Formalization Note** The code is injective on `ℚ` (both parts are prefix-free and `q` is
written in lowest terms with a positive denominator), so a machine output equal to `encRat q`
determines `q`; an output that is not of this form never counts as a correct value. Reducing a
fraction to lowest terms takes polynomial time, so asking for the reduced pair loses nothing. -/
def encRat (q : ℚ) : List Bool :=
  PPADSIS.SubexpSIS.encInt q.num ++ PPADSIS.SubexpSIS.encNat q.den

/-- The **lexicographic CDF of a family is computable in polynomial time** (Fortnow,
arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), Theorem A.1 condition 1, printed
p.15, PDF p.16: "The cumulative distribution function F_µ(x) = ∑_{z≤x} µ(z) is computable in
polynomial time, where ≤ is the lexicographic order on {0, 1}^n"): there is one function
`M : {0,1}* → {0,1}*` computable in polynomial time (published
`QAlgorithms.Complexity.PolyTimeComputable`, a Mathlib multi-stack Turing machine with a polynomial
time bound) such that for every length `n` and every `x ∈ {0,1}^n`, `M(x)` is the code `encRat q`
of a rational `q` equal to `F_{µ_n}(x)` (published `MLManagesComplexity.lexCDF`).

**Formalization Note** Polynomial time is a property of a family, so `µ` is a family
`(µ_n)_n` (`MLManagesComplexity.DistFamily`) and one machine serves every `n`. The input is the
string `x₁ … xₙ` itself (`List.ofFn x`), which determines `n`. -/
def CDFPolyTime (μ : DistFamily) : Prop :=
  ∃ M : List Bool → List Bool, QAlgorithms.Complexity.PolyTimeComputable M ∧
    ∀ (n : ℕ) (x : Fin n → Bool), ∃ q : ℚ, M (List.ofFn x) = encRat q ∧ (q : ℝ) = lexCDF (μ n) x

end MLManagesComplexity.Supplement


