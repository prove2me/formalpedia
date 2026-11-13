-- Prove2me | Definitions.Def_MLManagesComplexity_PolyMaxEntropy
-- name    : MLManagesComplexity_PolyMaxEntropy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:40:30.021213+00:00
-- url     : https://prove2.me/theorems/14f1e4af-2214-4ddd-91aa-f939a4423aa0
-- title:
--   Polynomially-bounded max-entropy and the log-loss $\log_2(1/\mu(x))$
-- statement:
--   The **log-loss** of a family $\mu$ at $x\in\{0,1\}^n$ is $g(x)=\log_2\bigl(1/\mu_n(x)\bigr)$; the **max-entropy** of $\mu_n$ is $\max_x \log_2(1/\mu_n(x))$.
--
--   The family $\mu$ has **polynomially-bounded max-entropy** if there is a constant $k$ such that
--
--   $$
--   \mu_n(x)\ \ge\ 2^{-(n+2)^k}\qquad\text{for every } n \text{ and every } x\in\{0,1\}^n ,
--   $$
--
--   equivalently its max-entropy is at most $(n+2)^k$. In particular every string gets positive probability.
--
--   The paper argues that softmax outputs of neural networks with polynomially bounded weights have this property; it is the hypothesis that keeps $\mathrm{KL}(U\|\mu)$ finite in Theorem 6.3.
--
--   **Formalization Note** Logarithms are base 2 (`Real.logb 2`). The paper writes the bound as $2^{-n^k}$; every family satisfying that bound satisfies $2^{-(n+2)^k}$, and the literal bound at $n=1$ would force $\mu_1$ to be uniform, which "polynomially bounded" does not intend. For a string of probability $0$ Lean's value of $\log_2(1/0)$ is $0$; every statement using the log-loss assumes polynomially-bounded max-entropy, so this value never occurs there.
-- source:
--   Fortnow, How Does Machine Learning Manage Complexity?, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), §3.2, p.4 (PDF p.5); §5.4, p.10 (PDF p.11); Proof of Theorem 6.1, p.10 (PDF p.11): g(x) = log(1/µ(x))

import Mathlib
import Definitions.Def_MLManagesComplexity_lexCDF

set_option autoImplicit false

open AutoregressiveCompression.Main

namespace MLManagesComplexity

/-- The **log-loss** `g(x) = log₂(1/μₙ(x))` of a family `μ` at `x ∈ {0,1}^n` (Fortnow,
arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), Proof of Theorem 6.1, printed p.10,
PDF p.11: "Let g(x) = log(1/μ(x))"; §3, p.4: "All logarithms are taken base 2").

**Formalization Note** `Real.logb 2`, on the real mass. For `μₙ(x) = 0` Lean's value is `0`;
every statement using `logLoss` assumes polynomially-bounded max-entropy, which makes all masses
positive. -/
noncomputable def logLoss (μ : DistFamily) (n : ℕ) (x : Fin n → Bool) : ℝ :=
  Real.logb 2 (1 / mass (μ n) x)

/-- A family `μ` has **polynomially-bounded max-entropy** (Fortnow, arXiv:2604.07233 (version of
2026-10-31, sha256 4874d83f…), §3.2, printed p.4, PDF p.5: "The max-entropy of μ is
max_x log 1/μ(x). Polynomially-bounded max-entropy means the max-entropy is bounded by n^k for
some k, equivalent to saying μ(x) ≥ 2^{−n^k}"; §5.4, printed p.10, PDF p.11: "μ has
polynomially-bounded max-entropy if there is some k such that μ(x) ≥ 2^{−n^k} for all
x ∈ {0, 1}^n"): there is `k` with `μₙ(x) ≥ 2^{−(n+2)^k}` for every `n` and every `x ∈ {0,1}^n`.

**Formalization Note** The bound `2^{−(n+2)^k}` replaces the literal `2^{−n^k}`: every family
with `μₙ(x) ≥ 2^{−n^k}` satisfies it, and the literal bound at `n = 1` (where `n^k = 1`) would
force `μ₁` to be uniform, which "polynomially bounded" does not intend. -/
def PolyMaxEntropy (μ : DistFamily) : Prop :=
  ∃ k : ℕ, ∀ (n : ℕ) (x : Fin n → Bool), (2 : ℝ) ^ (-(((n : ℝ) + 2) ^ k)) ≤ mass (μ n) x

end MLManagesComplexity


