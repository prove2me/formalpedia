-- Prove2me | Definitions.Def_SeqHolevo_codeVecs
-- name    : SeqHolevo_codeVecs
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:57:50.344327+00:00
-- url     : https://prove2.me/theorems/b3c4b9f3-a236-4264-be50-89c29a5ca2c5
-- title:
--   Channel outputs $|\varphi_{x^n(m)}\rangle$ of a code
-- statement:
--   For a codebook $(x^n(m))_m$, the output of the channel on codeword $m$ is the product state
--
--   $$|\varphi_{x^n(m)}\rangle=|\varphi_{x_1(m)}\rangle\otimes\cdots\otimes|\varphi_{x_n(m)}\rangle .$$
--
--   **Formalization Note** This is the published `productPureCQChannel` (`Intakenext100.P76`), a coefficient vector on the product basis `Fin n → I`.
-- source:
--   Wilde–Guha–Tan–Lloyd, Explicit capacity-achieving receivers for optical communication and quantum reading, arXiv:1202.0518v2, §II, p.2 (Sequential Decoding)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P76

open QAlgorithms.Papers.Independent.Intakenext100.P76 (productPureCQChannel)

namespace SeqHolevo

/-- Wilde–Guha–Tan–Lloyd, *Explicit capacity-achieving receivers for optical communication and quantum reading*, arXiv:1202.0518v2, §II, p.2 (PDF page), "Sequential Decoding": the channel outputs of a code,
`|φ_{xⁿ(m)}⟩ ≡ |φ_{x_1(m)}⟩ ⊗ ⋯ ⊗ |φ_{x_n(m)}⟩`, for the codewords `C m ∈ Xⁿ`.

**Formalization Note.** The pure-state channel `x ↦ |φ_x⟩` is `W : X → I → ℂ` (unit coefficient
vectors on ℓ²(I), any `I : Type`), and the tensor product is the published
`productPureCQChannel W n` (`Intakenext100.P76`), the coefficient vector on the product basis
`Fin n → I`. -/
noncomputable def codeVecs {X : Type*} {I : Type} (W : X → I → ℂ) (n : ℕ) {M : ℕ}
    (C : Fin M → Fin n → X) : Fin M → (Fin n → I) → ℂ :=
  fun i => productPureCQChannel W n (C i)

end SeqHolevo


