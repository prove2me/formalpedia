-- Prove2me | Definitions.Def_MixedORAM_PublicRead_RandomAccessCode
-- name    : MixedORAM_PublicRead_RandomAccessCode
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:45:40.509663+00:00
-- url     : https://prove2.me/theorems/ebea5d5a-875d-4098-a2f9-f66d9d9dd62f
-- title:
--   Success probability of a one-message random-access code
-- statement:
--   Let $Z$ (side information) have an arbitrary law and, independently, let $X=(X_1,\dots,X_k)$ be independent uniform $w$-bit words and $J$ uniform on $\{1,\dots,k\}$. An encoder sends the $\beta$-bit message $\mathrm{enc}(X,Z)$, which does not depend on $J$; a decoder outputs $\mathrm{dec}(\mathrm{enc}(X,Z),Z,J)$. The success probability is
--   $$s=\Pr\big[\mathrm{dec}(\mathrm{enc}(X,Z),Z,J)=X_J\big].$$
--
--   **Formalization Note** Encoder and decoder are functions of their inputs; private randomness of either party can be made part of $Z$, which only gives the decoder more information. Indices are $0$-based.
-- source:
--   Ciszewski, Ragnoli, Access Cost Tradeoffs in Mixed-Mode Oblivious RAM, STOC 2027 submission (manuscript sha256 a4f849fd…), p. 14, Lemma A.2

import Mathlib

set_option autoImplicit false

namespace MixedORAM.PublicRead

/-- The **success probability of a one-message random-access code** (Ciszewski, Ragnoli, *Access
Cost Tradeoffs in Mixed-Mode Oblivious RAM*, STOC 2027 submission (manuscript sha256 a4f849fd…),
Lemma A.2, p. 14): side information `Z` has law `μ`; independently, `X₁, …, X_k` are independent
uniform `w`-bit words (a uniform `X : Fin k → BitVec w`) and `J` is uniform on `Fin k` (the paper's
`[k]`). The encoder sends the `β`-bit message `enc X Z`, which does not depend on `J`; the decoder
outputs `dec (enc X Z) Z J`. The value is `Pr[dec (enc X Z) Z J = X_J]`.

Encoder and decoder are functions of their inputs: any private randomness of either party can be
made part of `Z`, which only gives the decoder more information. -/
noncomputable def raeSuccess {ζ : Type} (k w β : ℕ) [NeZero k] (μ : PMF ζ)
    (enc : (Fin k → BitVec w) → ζ → BitVec β) (dec : BitVec β → ζ → Fin k → BitVec w) :
    ENNReal :=
  (μ.bind fun z =>
    (PMF.uniformOfFintype (Fin k → BitVec w)).bind fun X =>
      (PMF.uniformOfFintype (Fin k)).map fun J => decide (dec (enc X z) z J = X J)) true

end MixedORAM.PublicRead


