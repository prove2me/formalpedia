-- Prove2me | Definitions.Def_QPACLarge_IsConstructive
-- name    : QPACLarge_IsConstructive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:05:12.788091+00:00
-- url     : https://prove2.me/theorems/d67437d0-ea49-464f-afc3-8a69f0ba3467
-- title:
--   Constructive advantage, Eq. (9)
-- statement:
--   A positive sequence $(\lambda_n)_{n \ge 1}$ is **constructive** if there is a deterministic algorithm that, on input $1^n$, runs in time $\mathrm{poly}(n)$ and outputs a nonnegative integer $s(n)$ such that, for every sufficiently large $n$,
--
--   $$
--   2^{-s(n)} \le \lambda_n \le 4 \cdot 2^{-s(n)}. \tag{9}
--   $$
--
--   Only an approximation of the magnitude of $\lambda_n$ is required. This is the hypothesis on $\lambda$ in Theorem 1.5.
--
--   **Formalization Note** The algorithm is a published polynomial-time computable map on bit strings sending $1^n$ to the self-delimiting binary code `encBin` of $s(n)$. Positivity of $\lambda$ is a separate hypothesis of every statement using this predicate.
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 5, p.34, Eq. (9) (the definition footnote 6 on p.7 refers to)

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding

namespace QPACLarge

open QAlgorithms Filter

/-- **Constructive advantage.**
Oliveira, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 5, p.34, Eq. (9): "We say that a
positive sequence `(λₙ)_{n≥1}` is constructive if there is a deterministic algorithm that, on
input `1ⁿ`, runs in time `poly(n)` and outputs a nonnegative integer `s(n)` such that, for every
sufficiently large `n`, `2^{−s(n)} ≤ λₙ ≤ 4 · 2^{−s(n)}`."

**Formalization Note.** The algorithm is a published polynomial-time computable map
`g : {0,1}* → {0,1}*` (Mathlib `TM2ComputableInPolyTime`) sending `1ⁿ` to the self-delimiting
binary code `encBin (s n)` of `s(n)`. Positivity of the sequence is not part of this predicate; every
statement that uses it assumes `0 < λ n` separately. -/
def IsConstructive (lam : ℕ → ℝ) : Prop :=
  ∃ s : ℕ → ℕ,
    (∃ g : Complexity.Str → Complexity.Str, Complexity.PolyTimeComputable g ∧
      ∀ n : ℕ, g (Complexity.unary n) = LocalHamiltonian.encBin (s n)) ∧
    ∀ᶠ n in atTop, ((2 : ℝ) ^ s n)⁻¹ ≤ lam n ∧ lam n ≤ 4 * ((2 : ℝ) ^ s n)⁻¹

end QPACLarge


