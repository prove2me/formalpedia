-- Prove2me | Definitions.Def_MLManagesComplexity_PPolyComputable
-- name    : MLManagesComplexity_PPolyComputable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:40:51.574727+00:00
-- url     : https://prove2.me/theorems/7e5daf87-0b2a-4216-a300-39f664d28c11
-- title:
--   P/poly-computable distribution families
-- statement:
--   A family $\mu=(\mu_n)$ of distributions on $\{0,1\}^n$ is **P/poly-computable** if its cumulative distribution function is computable by polynomial-size Boolean circuits: there is a constant $c$ such that for every $n$ there are a Boolean circuit $C_n$ with $n$ inputs and size at most $(n+2)^c$, and a width $w_n$, such that $C_n$ has $2w_n$ outputs and for every $x\in\{0,1\}^n$ the first $w_n$ output bits (a numerator $a$) and the last $w_n$ output bits (a denominator $b$), read in binary with the most significant bit first, satisfy
--
--   $$
--   b\ne 0 \qquad\text{and}\qquad \frac{a}{b}=F_{\mu_n}(x)=\sum_{y\le x}\mu_n(y).
--   $$
--
--   No relation between the circuits for different $n$ is required (nonuniformity, as in P/poly).
--
--   This is the paper's model of a trained machine-learning model: the weights are the nonuniform advice, and the model's probabilities, through the CDF, are exactly computable.
--
--   **Formalization Note** Circuits are the published `PPADSIS.SubexpSIS.Circuit` (gates constant, NOT, AND, OR; well formed means acyclic with distinct existing output wires; size counts input wires and gates). The bound $(n+2)^c$ in place of $n^c$ describes the same polynomial bounds. Values are exact rationals given by numerator and denominator, as in Theorem A.1.
-- source:
--   Fortnow, How Does Machine Learning Manage Complexity?, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), §3.2, p.4 (PDF p.5); §3.1, p.4 (PDF p.5); Theorem A.1, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_PPADSIS_SubexpSIS_Circuit
import Definitions.Def_MLManagesComplexity_lexCDF

set_option autoImplicit false

open PPADSIS.SubexpSIS

namespace MLManagesComplexity

/-- The output of a Boolean circuit with `2w` output bits, read as a rational number: the
first `w` output bits are the numerator and the last `w` the denominator, each in binary with the
most significant bit first (`valBE`). Evaluated on the input `x ∈ {0,1}^n`. -/
noncomputable def ratOut (C : Circuit) (w : ℕ) {n : ℕ} (x : Fin n → Bool) : ℝ :=
  ((valBE ((C.eval (List.ofFn x)).take w) : ℕ) : ℝ) /
    ((valBE ((C.eval (List.ofFn x)).drop w) : ℕ) : ℝ)

/-- The denominator output by the circuit on `x` is nonzero, so `ratOut C w x` is a genuine
quotient. -/
def ratDefined (C : Circuit) (w : ℕ) {n : ℕ} (x : Fin n → Bool) : Prop :=
  valBE ((C.eval (List.ofFn x)).drop w) ≠ 0

/-- A family `μ` of distributions on `{0,1}^n` is **P/poly-computable** (Fortnow,
arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), §3.2, printed p.4, PDF p.5:
"A distribution μ is polynomial-time computable if the CDF function f(x) = ∑_{y≤x} μ(y) is
computable in polynomial time. […] We also consider P/poly-computable […] distributions where we
replace polynomial time by nonuniform polynomial time"; §3.1, p.4: circuits `Cₙ` with `n`
inputs and at most `n^c` gates; Theorem A.1, p.15: "≤ is the lexicographic order on {0, 1}^n
[…] values are rationals represented by numerator and denominator"): there is an exponent `c`
such that for every `n` a well-formed Boolean circuit with `n` inputs and size at most `(n+2)^c`
outputs, on every `x ∈ {0,1}^n`, a numerator and a nonzero denominator whose quotient is exactly
the lexicographic CDF `F_{μₙ}(x)`.

**Formalization Note** Circuits are the published `PPADSIS.SubexpSIS.Circuit` (gates
const/NOT/AND/OR, well formed = acyclic with distinct existing output wires, size = inputs +
gates). Output bits are numerator then denominator, `w` bits each, big-endian. The size bound
`(n+2)^c` instead of `n^c` describes the same polynomial bounds and is not degenerate at
`n ≤ 1`. No uniformity condition (nonuniform, P/poly). -/
def PPolyComputable (μ : DistFamily) : Prop :=
  ∃ c : ℕ, ∀ n : ℕ, ∃ (C : Circuit) (w : ℕ),
    C.WF ∧ C.nIn = n ∧ C.outs.length = 2 * w ∧ C.size ≤ (n + 2) ^ c ∧
      ∀ x : Fin n → Bool, ratDefined C w x ∧ ratOut C w x = lexCDF (μ n) x

end MLManagesComplexity


