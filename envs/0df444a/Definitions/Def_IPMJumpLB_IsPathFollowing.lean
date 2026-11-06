-- Prove2me | Definitions.Def_IPMJumpLB_IsPathFollowing
-- name    : IPMJumpLB_IsPathFollowing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:33:17.501385+00:00
-- url     : https://prove2.me/theorems/25388fc3-5d4b-429e-a63a-6eeb13073c79
-- title:
--   $\eta$-path-following sequence of length $L$ (Definition 2.3)
-- statement:
--   An **$\eta$-path-following sequence of length $L$** is a sequence $(x^{(\ell)}, s^{(\ell)}, f^{(\ell)})$, $\ell = 0, \dots, L$, of $\eta$-iterates such that for every $\ell \ge 1$ the move from the $(\ell-1)$-st iterate to the $\ell$-th iterate is a jump.
--
--   A lower bound on the length of every such sequence is a lower bound on the number of iterations of every algorithm whose iterates form such a sequence, however each step is computed.
--
--   **Formalization Note** The sequence is a function on $\mathbb N$ whose values at $0, \dots, L$ are constrained; the jump condition is stated for the moves $\ell \to \ell + 1$, $\ell < L$.
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), Definition 2.3, p.4

import Mathlib
import Definitions.Def_IPMJumpLB_FlowInstance
import Definitions.Def_IPMJumpLB_IsEtaIterate
import Definitions.Def_IPMJumpLB_IsJump

namespace IPMJumpLB

/-- Definition 2.3 (Path-following sequence) (Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), p.4): an η-path-following sequence of length
`L` is a sequence of η-iterates `(x⁽ˡ⁾, f⁽ˡ⁾)`, `ℓ = 0, …, L`, such that for every `ℓ ≥ 1` the
move from the `(ℓ − 1)`-st iterate to the `ℓ`-th is a jump.

**Formalization Note** The sequence is a function `ℕ → (V → ℝ) × (E → ℝ)`; only its values at
`0, …, L` are constrained. The jump condition is indexed as `seq ℓ → seq (ℓ + 1)` for `ℓ < L`,
which is the paper's condition for `ℓ + 1 = 1, …, L`. -/
def IsPathFollowing {V E : Type*} [Fintype E] [DecidableEq V] (I : FlowInstance V E) (η : ℝ)
    (L : ℕ) (seq : ℕ → (V → ℝ) × (E → ℝ)) : Prop :=
  (∀ ℓ ≤ L, IsEtaIterate I η (seq ℓ).1 (seq ℓ).2) ∧
    ∀ ℓ < L, IsJump I η (seq ℓ) (seq (ℓ + 1))

end IPMJumpLB


