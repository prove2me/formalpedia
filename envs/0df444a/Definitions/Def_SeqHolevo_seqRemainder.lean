-- Prove2me | Definitions.Def_SeqHolevo_seqRemainder
-- name    : SeqHolevo_seqRemainder
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:57:35.64391+00:00
-- url     : https://prove2.me/theorems/64fda01d-e5de-499f-b462-d7e08bd31a1e
-- title:
--   State after the first $k$ "no" outcomes of the sequential decoder
-- statement:
--   Given a code with codeword vectors $|\Phi_1\rangle,\dots,|\Phi_M\rangle$, the sequential decoder tests "is it codeword $i$?" with the binary measurement $\{|\Phi_i\rangle\langle\Phi_i|,\ \hat\Pi_i=I-|\Phi_i\rangle\langle\Phi_i|\}$, for $i=1,2,\dots$ in order. Applied to a vector $|\psi\rangle$, the **remainder** after the first $k$ tests answered "no" is
--
--   $$\hat\Pi_k\cdots\hat\Pi_1|\psi\rangle,$$
--
--   computed recursively by $R_0=\psi$, $R_{k+1}=R_k-\langle\Phi_{k+1},R_k\rangle\,\Phi_{k+1}$ (and unchanged once all $M$ codewords have been tested).
--
--   **Formalization Note** Codewords and tests are 0-based in Lean (`Fin M`). For a unit vector $\Phi$, $v\mapsto v-\langle\Phi,v\rangle\Phi$ is exactly $I-|\Phi\rangle\langle\Phi|$.
-- source:
--   Wilde–Guha–Tan–Lloyd, Explicit capacity-achieving receivers for optical communication and quantum reading, arXiv:1202.0518v2, §II, pp.2–3; Appendix B, p.6

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P76

open QAlgorithms.Papers.Independent.Intakenext100.P76 (coefficientInner)

namespace SeqHolevo

/-- Wilde–Guha–Tan–Lloyd, *Explicit capacity-achieving receivers for optical communication and quantum reading*, arXiv:1202.0518v2, §II, pp.2–3, and Appendix B, p.6 (PDF pages): the vector left after the first `k`
"no" outcomes of the sequential decoder, `Π̂_k ⋯ Π̂_1 |ψ⟩` (paper indices), where
`Π̂_i ≡ I^{⊗n} − |φ_{xⁿ(i)}⟩⟨φ_{xⁿ(i)}|` is the "no" projector of the `i`-th test.

For a code given by its codeword vectors `Φ : Fin M → J → ℂ` the recursion is
`R_0 = ψ` and `R_{k+1} = R_k − ⟨Φ_k, R_k⟩ Φ_k` for `k < M` (Lean's 0-based index `k` is the
paper's codeword `k+1`); once all `M` codewords have been tested it stays constant.

**Formalization Note.** For a unit vector `Φ_k`, `v ↦ v − ⟨Φ_k, v⟩ Φ_k` is exactly
`I − |Φ_k⟩⟨Φ_k|`; `coefficientInner` (`Intakenext100.P76`) is conjugate-linear in its first
argument. Messages and tests are 0-based. All vectors involved are finite linear combinations of
square-summable vectors, so every `tsum` converges. -/
noncomputable def seqRemainder {J : Type} {M : ℕ} (Φ : Fin M → J → ℂ) (ψ : J → ℂ) : ℕ → J → ℂ
  | 0 => ψ
  | k + 1 =>
    if h : k < M then
      seqRemainder Φ ψ k - coefficientInner (Φ ⟨k, h⟩) (seqRemainder Φ ψ k) • Φ ⟨k, h⟩
    else seqRemainder Φ ψ k

end SeqHolevo


