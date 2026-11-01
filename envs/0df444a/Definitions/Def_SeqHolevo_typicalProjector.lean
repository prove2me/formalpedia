-- Prove2me | Definitions.Def_SeqHolevo_typicalProjector
-- name    : SeqHolevo_typicalProjector
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:58:54.928395+00:00
-- url     : https://prove2.me/theorems/fec52db9-96e2-4944-99a9-18f3ade4e90d
-- title:
--   Typical projector $\Pi^n_{\rho,\delta}$
-- statement:
--   Let $\rho=\sum_xp_X(x)|u_x\rangle\langle u_x|$ be a spectral decomposition. The **typical projector** onto the weakly typical subspace of $\rho^{\otimes n}$ is
--
--   $$\Pi^n_{\rho,\delta}=\sum_{x^n\in T^{X^n}_\delta}|u_{x^n}\rangle\langle u_{x^n}|,\qquad |u_{x^n}\rangle=|u_{x_1}\rangle\otimes\cdots\otimes|u_{x_n}\rangle .$$
--
--   It is the operator used to smooth the channel in the error analysis of Appendix B.
--
--   **Formalization Note** Coefficient array on the product basis `Fin n → I`; the sum over the typical set is finite for $n\ge1$.
-- source:
--   Wilde–Guha–Tan–Lloyd, Explicit capacity-achieving receivers for optical communication and quantum reading, arXiv:1202.0518v2, Appendix A, p.6

import Mathlib
import Definitions.Def_SeqHolevo_typicalSet

namespace SeqHolevo

/-- Wilde–Guha–Tan–Lloyd, *Explicit capacity-achieving receivers for optical communication and quantum reading*, arXiv:1202.0518v2, Appendix A, p.6 (PDF page): the typical projector
`Π^n_{ρ,δ} ≡ Σ_{xⁿ ∈ T_δ^{Xⁿ}} |xⁿ⟩⟨xⁿ|` onto the weakly typical subspace of `ρ`, where
`ρ = Σ_x p_X(x)|x⟩⟨x|` and `|xⁿ⟩ = |x_1⟩ ⊗ ⋯ ⊗ |x_n⟩`. As a coefficient array on the product basis
`Fin n → I`: `(Π)_{ab} = Σ_{xⁿ ∈ T} u_{xⁿ}(a) conj(u_{xⁿ}(b))` with `u_{xⁿ}(a) = ∏_i u_{x_i}(a_i)`.

**Formalization Note.** `p`, `u` are a spectral decomposition of `ρ` (`IsSpectralDecomp`).
The sum runs over the typical set as a subtype; that set is finite for `n ≥ 1` (each element has
`p_{Xⁿ}(xⁿ) ≥ 2^{−n[H(X)+δ]}` and the probabilities sum to one), so the `tsum` is a finite sum. -/
noncomputable def typicalProjector {I : Type} (p : ℕ → ℝ) (u : ℕ → I → ℂ) (n : ℕ) (δ : ℝ) :
    Matrix (Fin n → I) (Fin n → I) ℂ :=
  fun a b => ∑' xs : typicalSet p n δ,
    (∏ i, u (xs.1 i) (a i)) * star (∏ i, u (xs.1 i) (b i))

end SeqHolevo


