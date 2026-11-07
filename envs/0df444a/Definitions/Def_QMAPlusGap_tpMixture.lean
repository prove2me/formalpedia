-- Prove2me | Definitions.Def_QMAPlusGap_tpMixture
-- name    : QMAPlusGap_tpMixture
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:05:37.644742+00:00
-- url     : https://prove2.me/theorems/7a8ebc8f-a0e2-4ba2-b453-68a7e050bf97
-- title:
--   Tensor-power mixtures $\int(|\psi\rangle\langle\psi|)^{\otimes\ell}d\mu(\psi)$
-- statement:
--   For a finite measure $\mu$ on $\mathbb C^{\iota}$, the tensor-power mixture is the operator on $\mathcal H^{\otimes\ell}$
--   $$
--   \sigma=\int(|\psi\rangle\langle\psi|)^{\otimes\ell}\,d\mu(\psi),\qquad \langle a|\sigma|b\rangle=\int\prod_{r=1}^{\ell}\psi_{a_r}\overline{\psi_{b_r}}\,d\mu(\psi).
--   $$
--   For a probability measure on the unit sphere it is a mixture of identical pure tensor powers, the approximating objects of finite quantum de Finetti theorems.
--
--   **Formalization Note** The integral is taken entry by entry. Every statement uses it with a finite measure concentrated on the unit sphere, where the integrand is continuous and bounded by $1$, so the integral is never Lean's value $0$ for a non-integrable function.
-- source:
--   Miyamoto, Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs, arXiv:2608.07986 (held version, sha256 4667925f…), Lemma 10, p.17; Theorem 12, p.25; Lemma 14, p.27

import Mathlib

set_option autoImplicit false

namespace QMAPlusGap

open MeasureTheory

/-- The **tensor-power mixture** `σ = ∫ (|ψ⟩⟨ψ|)^{⊗ℓ} dμ(ψ)` on `H^{⊗ℓ}`, Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs*, arXiv:2608.07986 (held version, sha256 4667925f…) (Lemma 10, p.17; Theorem 12
(σ_ℓ), p.25; Theorem A.4, p.36; Lemma 14 (ρ̃_P), p.27).

Entrywise, `⟨a|σ|b⟩ = ∫ ∏_r ψ_{a_r} conj(ψ_{b_r}) dμ(ψ)` for basis strings `a, b : Fin ℓ → ι`.

**Formalization Note** The matrix-valued integral is taken entry by entry (Bochner integral of a complex
function). In every statement `μ` is a finite measure concentrated on the unit sphere, where the integrand is
continuous and bounded by `1`, hence integrable: the integral is never Lean's junk value `0` for a
non-integrable function. -/
noncomputable def tpMixture {ι : Type} (ℓ : ℕ) (μ : Measure (ι → ℂ)) :
    Matrix (Fin ℓ → ι) (Fin ℓ → ι) ℂ :=
  Matrix.of fun a b => ∫ ψ, ∏ r : Fin ℓ, (ψ (a r) * star (ψ (b r))) ∂μ

end QMAPlusGap


