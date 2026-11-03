-- Prove2me | Definitions.Def_HolevoEntropyGain_IsEnergySpectrum
-- name    : HolevoEntropyGain_IsEnergySpectrum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:19:00.279624+00:00
-- url     : https://prove2.me/theorems/0d05948e-eab0-4202-a15f-a77cc6e84f53
-- title:
--   Spectral data of the quadratic Hamiltonian $F = R\epsilon R^\top$
-- statement:
--   Let $W$ be a Weyl system with canonical variables $R_1,\dots,R_{2s}$ and $\epsilon$ a real $2s\times2s$ matrix. An orthonormal basis $(e_n)$ of $\ell^2(I)$ and reals $(E_n)$ are **spectral data of $F = R\epsilon R^\top$** if the form $\psi\mapsto\sum_n E_n|\langle e_n,\psi\rangle|^2$, with its maximal domain $\{\psi : \sum_n|E_n||\langle e_n,\psi\rangle|^2<\infty\}$, is the form
--
--   $$
--   q(\psi) = \sum_{j,k}\epsilon_{jk}\,\langle R_j\psi, R_k\psi\rangle \quad\text{on}\quad \bigcap_j D(R_j),
--   $$
--
--   i.e. the two domains coincide and the two forms agree there. Then $F = \sum_n E_n|e_n\rangle\langle e_n|$ is the operator $R\epsilon R^\top$.
--
--   **Formalization Note** Mathlib has no unbounded functional calculus, so $F$ is encoded by an eigenbasis. For real positive definite $\epsilon$ the form $q$ is closed and agrees with the closure of $R\epsilon R^\top$ on Schwartz vectors; $\operatorname{Tr}\exp(-\beta F)<\infty$ forces discrete spectrum, so such data exist (indexed by $I$), and any two give the same $\exp(-\beta F)$. Statements using these data quantify over all of them. Nothing about the Gibbs state is assumed.
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §3, p.5 ("We take F = RǫR⊤, where ǫ is a nondegenerate positive definite matrix")

import Mathlib
import Definitions.Def_HolevoEntropyGain_IsGeneratorValue

open QAlgorithms.RealRegisters (Hilbert)

namespace HolevoEntropyGain

/-- The orthonormal basis `(eₙ)` and the reals `(Eₙ)` are spectral data of the operator `F = RεRᵀ`
(Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §3, p.5, PDF p.5): the form `∑ₙ Eₙ|⟨eₙ, ψ⟩|²`, with its maximal domain, is the form
`∑ⱼₖ εⱼₖ⟨Rⱼψ, Rₖψ⟩` on `⋂ⱼ D(Rⱼ)`.

**Formalization Note** (R10) Mathlib has no unbounded functional calculus. For a real positive definite
`ε` the form on `⋂ⱼ D(Rⱼ)` is closed and agrees with the closure of `RεRᵀ` on Schwartz vectors, and a
closed form determines its operator. (5) forces discrete spectrum, so a basis `(eₙ)` exists, indexed by
`I` since both are orthonormal bases of `Hilbert I`. Any two choices give the same `exp(-βF)`, and the
statements using this structure quantify over all of them. Nothing about the Gibbs state is assumed. -/
structure IsEnergySpectrum {I : Type} {s : ℕ} {Δ : Matrix (Fin (2 * s)) (Fin (2 * s)) ℝ}
    (W : WeylSystem I Δ) (ε : Matrix (Fin (2 * s)) (Fin (2 * s)) ℝ)
    (e : HilbertBasis I ℂ (Hilbert I)) (E : I → ℝ) : Prop where
  /-- The maximal form domain of `∑ₙ Eₙ|eₙ⟩⟨eₙ|` is `⋂ⱼ D(Rⱼ)`. -/
  form_domain : ∀ ψ : Hilbert I,
    Summable (fun n => |E n| * ‖inner ℂ (e n) ψ‖ ^ 2) ↔ ∀ j, ∃ φ, IsGeneratorValue W j ψ φ
  /-- On it the two forms agree. -/
  form_eq : ∀ (ψ : Hilbert I) (R : Fin (2 * s) → Hilbert I), (∀ j, IsGeneratorValue W j ψ (R j)) →
    HasSum (fun n => E n * ‖inner ℂ (e n) ψ‖ ^ 2)
      (∑ j, ∑ k, (ε j k : ℂ) * inner ℂ (R j) (R k)).re

end HolevoEntropyGain


