-- Prove2me | Definitions.Def_QiOPoQ_IsAdmissibleRounds
-- name    : QiOPoQ_IsAdmissibleRounds
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:59:49.26594+00:00
-- url     : https://prove2.me/theorems/62bc07ec-97c8-4332-b0c5-04abc064e7d4
-- title:
--   Notation 4.1: the number of parallel repetitions $t(\lambda)$
-- statement:
--   The number $t(\lambda)$ of parallel repetitions is **admissible** if $1^\lambda\mapsto 1^{t(\lambda)}$ is computable in polynomial time, $t(\lambda)\le p(\lambda)$ for a polynomial $p$, and $t=\Omega(\lambda)$: there is a constant $c>0$ with $t(\lambda)\ge c\lambda$ for all large $\lambda$.
--
--   **Formalization Note** The challenger and the verifier have to compute $t$, which is why it is computable from $1^\lambda$. A constant $t$ would make $f_t$ invertible by brute force, so the lower bound is not optional.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Notation 4.1, p.17

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_ClassicalUnaryInput

set_option autoImplicit false

namespace QiOPoQ

open QAlgorithms.Complexity

/-- **Notation 4.1, fourth bullet: the number of parallel repetitions.** arXiv:2609.40289,
Notation 4.1, p.17: "We will denote the number of parallel repetitions by t := t(λ), and will set
t ≤ poly(λ), t ≥ Ω(λ) to ensure negligible soundness error."

**Formalization Note.** `t(λ)` is computable from `1^λ` in polynomial time (the challenger and
the verifier need it), `t ≤ p(λ)` for a polynomial `p`, and `Ω(λ)` is `∃ c > 0, t(λ) ≥ cλ` for all
large `λ`. -/
def IsAdmissibleRounds (t : ℕ → ℕ) : Prop :=
  PolyTimeComputable (fun w => unary (t w.length)) ∧ (∃ p : Polynomial ℕ, ∀ n, t n ≤ p.eval n) ∧
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N, c * n ≤ t n

end QiOPoQ


