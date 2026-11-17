-- Prove2me | Definitions.Def_RestrictedDec_Supplement_MsgSpace
-- name    : RestrictedDec_Supplement_MsgSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:20:06.7083+00:00
-- url     : https://prove2.me/theorems/16cf4df6-d673-4c15-aa7b-633f397495bd
-- title:
--   Common message space with two efficiently found messages; efficient recognition
-- statement:
--   A **message space** is a family $M=(M_\lambda)_{\lambda\in\mathbb N}$ of sets of bit strings. It **contains two efficiently found distinct equal-length messages** if one polynomial-time machine maps $1^\lambda$ to a pair $(m_0,m_1)$ with
--   $$m_0\neq m_1,\qquad |m_0|=|m_1|,\qquad m_0,m_1\in M_\lambda$$
--   for every $\lambda$. This is the standing assumption on the common message space over which the paper compares encryption schemes.
--
--   A family of sets $X=(X_\lambda)$ is **efficiently recognizable** if one polynomial-time machine decides $x\in X_\lambda$ from $(1^\lambda,x)$. Appendix B assumes this for the valid plaintexts; the CHK compiler uses it for the public identity space of the IBE.
--
--   **Formalization Note** Messages are bit strings and $M_\lambda$ is a predicate on them. Machine inputs and outputs are tuple codes.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), §2.1, p.13; App. B.1, p.35; App. A.3, p.31

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_BeyondDS_tup
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

/-- A **common message space** `M = (M_λ)_λ`, `M λ m` meaning `m ∈ M_λ`, **contains at least two
efficiently found distinct equal-length messages**: one polynomial-time machine maps `1^λ` to
`tup [m₀, m₁]` with `m₀ ≠ m₁`, `|m₀| = |m₁|` and `m₀, m₁ ∈ M_λ`, for every `λ`.
Nguyen–Susilo, *Between CPA and CCA: Security Hierarchies for Restricted Decryption*, STOC 2027
submission (manuscript sha256 6aeac40c…), §2.1, p.13 ("We compare schemes over a common message
space Mλ, which contains at least two efficiently found distinct equal-length messages").

**Formalization Note.** Plaintexts are bit strings `Str`; a message space is a predicate on them,
one per security parameter. `1^λ` is `encNat λ`. -/
def MsgSpace.Found (M : ℕ → Str → Prop) : Prop :=
  ∃ f : Str → Str, PolyTimeComputable f ∧ ∀ lam, ∃ m0 m1 : Str,
    f (encNat lam) = BeyondDS.tup [m0, m1] ∧ m0 ≠ m1 ∧ m0.length = m1.length ∧ M lam m0 ∧ M lam m1

/-- **Efficient recognition** of a λ-indexed set of strings `M`: membership `m ∈ M_λ` is decided by
one polynomial-time machine, uniformly in `λ`. Used for valid plaintexts and for the IBE identity
space.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), App. B.1, p.35 ("We assume
polynomial-time encodings for messages, ciphertexts and encryption randomness, efficient
recognition of valid plaintexts"); App. A.3, p.31 ("a public identity space Iλ"). -/
def Recognizable (M : ℕ → Str → Prop) : Prop :=
  ∃ f : Str → Str, PolyTimeComputable f ∧ ∀ lam m,
    (f (BeyondDS.tup [encNat lam, m]) = BeyondDS.encBool true ↔ M lam m) ∧
    (f (BeyondDS.tup [encNat lam, m]) = BeyondDS.encBool true ∨
      f (BeyondDS.tup [encNat lam, m]) = BeyondDS.encBool false)

end Supplement

end RestrictedDec


