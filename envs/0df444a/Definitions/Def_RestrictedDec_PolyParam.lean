-- Prove2me | Definitions.Def_RestrictedDec_PolyParam
-- name    : RestrictedDec_PolyParam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:51:15.495272+00:00
-- url     : https://prove2.me/theorems/2ee72fa1-6751-430c-9e2c-886eb1a51b13
-- title:
--   Public polynomial message length $n(\lambda)$
-- statement:
--   A function $n:\mathbb N\to\mathbb N$ is a **public polynomial message length** if
--
--   1. $n$ is polynomially bounded: $n(\lambda)\le(\lambda+2)^c$ for one constant $c$ and all $\lambda$, and
--   2. one polynomial-time machine computes $1^{n(\lambda)}$ from $1^\lambda$.
--
--   The message space of the mission is $\mathcal M_\lambda=\{0,1\}^{n(\lambda)}$.
--
--   Corollary 2 assumes $n(\lambda)$ polynomially bounded; the paper also assumes throughout that the common message space contains efficiently found messages, which is what lets the constructions and attacks write down $0^n$ and the unit vectors $e_k$.
--
--   **Formalization Note** The bound is the published `NoisyOWMPC.PolyBounded`; the machine model is `PolyTimeComputable` (multi-stack Turing machines) of `QAlgorithms_ClassicalStringComputability`, with $\lambda$ in unary.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), Corollary 2, p.22; §2.1, p.13 (common message space with efficiently found messages)

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_NoisyOWMPC_Negligible
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

/-- A **public polynomial message length** `n(λ)`: `n` is polynomially bounded and one
polynomial-time machine computes `1^{n(λ)}` from `1^λ`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Corollary 2, p.22 ("the message
space {0, 1}^{n(λ)}, where n(λ) is polynomially bounded"); §2.1, p.13 ("a common message space Mλ,
which contains at least two efficiently found distinct equal-length messages").

**Formalization Note.** The computability of `1^{n(λ)}` is the reading of p.13's standing
assumption that messages of `M_λ` can be found efficiently: without it, no polynomial-time party
could produce the all-zero message `0ⁿ` or a unit vector `e_k`. Every polynomial qualifies.
`PolyBounded` is the published `NoisyOWMPC.PolyBounded` (`n λ ≤ (λ + 2)^c`). -/
def PolyParam (n : ℕ → ℕ) : Prop :=
  NoisyOWMPC.PolyBounded n ∧
    ∃ f : Str → Str, PolyTimeComputable f ∧ ∀ lam, f (encNat lam) = List.replicate (n lam) true

end RestrictedDec


