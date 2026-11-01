-- Prove2me | Definitions.Def_BaconThesis_Multilevel_IsDFSubspace
-- name    : BaconThesis_Multilevel_IsDFSubspace
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:37:38.458074+00:00
-- url     : https://prove2.me/theorems/0897bc9d-0bd5-4c21-83c9-a0c8bc5a0e37
-- title:
--   Decoherence-free subspace of a multilevel atom coupled to the field, eq. (12.3)
-- statement:
--   Consider an $N$-level atom with real level energies $\omega_1,\dots,\omega_N$, system Hamiltonian $H_0=\sum_i \omega_i|i\rangle\langle i|$, and atom–field coupling coefficients $g_{ij}$ ($i>j$). A subspace $S\subseteq\mathbb C^N$ is a **decoherence-free (DF) subspace in the strict sense** if
--
--   1. $S\neq\{0\}$;
--   2. (eq. (12.3)) there are constants $\alpha_1,\alpha_2\in\mathbb C$ such that for every $|\psi\rangle\in S$
--   $$
--   \sum_{i>j=1}^{N} g_{ij}\sigma_{ij}|\psi\rangle = \alpha_1|\psi\rangle, \qquad \sum_{i>j=1}^{N} g^{*}_{ij}\sigma_{ij}|\psi\rangle = \alpha_2|\psi\rangle ;
--   $$
--   3. $H_0$ preserves $S$ in the sense of Definition 5.3.2.
--
--   Condition 2 is the thesis's reduction, via its DFS criterion (Theorem 5.3.1), of the decoherence-free condition for the coupling (12.2) to the two generators of the OSR algebra; condition 3 is the requirement of §5.3.3 that the system Hamiltonian not take states out of the DF subspace, so that states in $S$ evolve unitarily. This is the notion of DF subspace in Lemma 12.1.1.
--
--   **Formalization Note** Levels are indexed by `Fin N` (0-based); $H_0$ is the diagonal matrix of the real energies. The quantized electromagnetic field of (12.1) is not modelled; only the condition (12.3) that the thesis derives from it is stated.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §12.1, eq. (12.3), p.156 (PDF p.173), with Definition 5.3.2, §5.3.3, p.74 (PDF p.91)

import Mathlib
import Definitions.Def_BaconThesis_Multilevel_sumSigma
import Definitions.Def_BaconThesis_Multilevel_PreservesSubspace

open scoped Matrix

namespace BaconThesis.Multilevel

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§12.1, eq. (12.3), p.156 (PDF p.173), with Definition 5.3.2 and §5.3.3, p.74 (PDF p.91): a
**decoherence-free (DF) subspace** of an `N`-level atom with level energies `ω_i` and field
coupling coefficients `g_ij` (`i > j`), in the strict sense of Lemma 12.1.1: a nonzero subspace `S`
such that

1. (12.3) there are constants `α₁, α₂` with `Σ_{i>j} g_ij σ_ij |ψ⟩ = α₁|ψ⟩` and
   `Σ_{i>j} g*_ij σ_ij |ψ⟩ = α₂|ψ⟩` for every `|ψ⟩ ∈ S`, and
2. the system Hamiltonian `H₀ = Σ_i ω_i |i⟩⟨i|` preserves `S` (Definition 5.3.2).

**Formalization Note.** Levels are `Fin N` (0-based); `H₀` is `Matrix.diagonal (fun i => ω i)`
with real `ω`. The quantized-field part of (12.1)–(12.2) is not modelled: the book itself reduces
the DF condition for that coupling to the two eigen-conditions (12.3) on the generators of the OSR
algebra (via Theorem 5.3.1), and those are what is stated. A DF subspace supports at least one
state, so `S ≠ ⊥`. -/
def IsDFSubspace {N : ℕ} (g : Fin N → Fin N → ℂ) (ω : Fin N → ℝ)
    (S : Submodule ℂ (Fin N → ℂ)) : Prop :=
  S ≠ ⊥ ∧
    (∃ α₁ α₂ : ℂ, ∀ ψ ∈ S,
      sumSigma g *ᵥ ψ = α₁ • ψ ∧ sumSigma (fun i j => star (g i j)) *ᵥ ψ = α₂ • ψ) ∧
    PreservesSubspace (Matrix.diagonal fun i => ((ω i : ℝ) : ℂ)) S

end BaconThesis.Multilevel


