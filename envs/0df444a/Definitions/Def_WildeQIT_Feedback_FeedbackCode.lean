-- Prove2me | Definitions.Def_WildeQIT_Feedback_FeedbackCode
-- name    : WildeQIT_Feedback_FeedbackCode
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:35:52.761248+00:00
-- url     : https://prove2.me/theorems/641e2f61-c974-4d4c-a248-fb1690ff83ca
-- title:
--   Classical feedback code of block length $n$ with $M$ messages
-- statement:
--   Let $p_{Y|X}$ be a classical channel from a finite input alphabet $\mathcal X$ to a finite output alphabet $\mathcal Y$, used $n$ times, with a noiseless feedback link from the receiver to the sender. A **classical feedback code** with message set $\mathcal M=\{1,\dots,M\}$ consists of
--
--   1. encoding functions: for each message $m$ and each time $i\in\{1,\dots,n\}$, the channel input
--   $$
--   x_i(m,y^{i-1})\in\mathcal X
--   $$
--   is a function of the message $m$ and of all outputs $y_1,\dots,y_{i-1}$ received before time $i$;
--   2. a decoding function $g:\mathcal Y^n\to\mathcal M$.
--
--   Unlike an ordinary channel code, whose codeword $x^n(m)$ is fixed in advance, the codeword of a feedback code adapts to what the receiver has seen. Every ordinary code is a feedback code whose encoder ignores the fed-back outputs.
--
--   **Formalization Note** Times are 0-based, `Fin n`; at time $i$ the fed-back outputs are a word `Fin i → β` of length $i$ (empty at time $0$). Messages are `Fin M`. Encoders and the decoder are deterministic functions, as on the page.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, proof of Theorem 21.5.1, p. 604 (definition of an (n, C − δ, ε) classical feedback code)

import Mathlib.Data.Fin.Basic

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §21.5.1, proof of
Theorem 21.5.1, p. 604: a classical feedback code.
-/

namespace WildeQIT.Feedback

/-- **A classical feedback code of block length `n` with `M` messages.**
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, proof of Theorem 21.5.1,
p. 604: "every symbol `xᵢ(m, Y^{i−1})` of a codeword `xⁿ(m)` is a function of the message
`m ∈ 𝓜` and all of the previously received values `Y₁, …, Y_{i−1}` from the receiver. The
decoder consists of the decoding function `g : 𝒴ⁿ → {1, 2, …, |𝓜|}`."

* `enc m i z` is the channel input `xᵢ(m, z)` sent at time `i` when the message is `m` and the
  receiver has fed back the outputs `z = (y₁, …, y_{i−1})` of the earlier channel uses;
* `dec` is the decoder `g`.

**Formalization Note.** Times are `Fin n`, 0-based: at time `i` the fed-back outputs are a word
`Fin i → β` of length `i` (the outputs at times `0, …, i − 1`); at time `0` it is the empty
word. Messages are `Fin M`. -/
structure FeedbackCode (α β : Type) (n M : ℕ) where
  /-- The encoder: the input `xᵢ(m, y^{i−1})` at time `i`. -/
  enc : Fin M → (i : Fin n) → (Fin i → β) → α
  /-- The decoder `g : 𝒴ⁿ → 𝓜`. -/
  dec : (Fin n → β) → Fin M

end WildeQIT.Feedback


