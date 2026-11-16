-- Prove2me | Definitions.Def_StationarityTest_Supplement_Metastable
-- name    : StationarityTest_Supplement_Metastable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:46:39.555285+00:00
-- url     : https://prove2.me/theorems/65eb5925-7395-411c-9a31-1519a8e9f9a2
-- title:
--   $\varepsilon$-local metastability $\|\mathcal L_{H,i}[\sigma]\|_1\le\varepsilon$ and the boundary terms $\partial_A H$
-- statement:
--   Let $H=\sum_{\gamma\in\Gamma}h_\gamma P_\gamma$ be a Hamiltonian on $n$ sites and $\beta>0$ an inverse temperature. For each site $i$, let $\mathcal L_{H,i}$ be the [CKG23] Lindbladian of $H$ with energy width $\beta^{-1}$, summed over the single-site Pauli jumps on site $i$ (Definition 2.17), and write $\|X\|_1=\operatorname{tr}\sqrt{X^\dagger X}$ for the trace norm.
--
--   1. (Definitions 1.6 and 6.1.) A state $\sigma$ is **$\varepsilon$-locally metastable** with respect to $H$ if, for every site $i\in[n]$,
--   $$
--   \|\mathcal L_{H,i}[\sigma]\|_1\le\varepsilon .
--   $$
--   2. (Theorem 1.12.) For a set of sites $A\subseteq[n]$, the **boundary terms** of $H$ are the Hamiltonian terms incident on both $A$ and $\bar A=[n]\setminus A$:
--   $$
--   \partial_A H=\sum_{\gamma\in\Gamma:\ \operatorname{supp}P_\gamma\cap A\neq\emptyset,\ \operatorname{supp}P_\gamma\cap\bar A\neq\emptyset}h_\gamma P_\gamma .
--   $$
--
--   The Gibbs state $\rho_H$ is exactly stationary ($\varepsilon=0$); metastable states are the approximately stationary states of the Gibbs sampler, and may be far from $\rho_H$. The boundary operator $\partial_A H$ sets the leading term of the thermal area law.
--
--   **Formalization Note** The trace norm is the published `WildeQIT.traceNorm` and $\mathcal L_{H,i}$ the published `lindbladSite H β i`. Neither full rank of $\sigma$ nor any relation to $\rho_H$ is part of the definition.
-- source:
--   Bergamaschi, The stationarity test: a framework for learning quantum many-body systems from their thermal states, arXiv:2610.01074 (held file sha256 0b7e46fb…), Definition 1.6, (8), p.6; Definition 6.1, (136), p.36; Theorem 1.12, p.8

import Definitions.Def_StationarityTest_Lindbladian
import Definitions.Def_WildeQIT_traceNorm

open Matrix

namespace StationarityTest.Supplement

/-!
# Local metastability and the boundary terms of a Hamiltonian

T. Bergamaschi, *The stationarity test: a framework for learning quantum many-body systems from
their thermal states*, arXiv:2610.01074 (held file sha256 0b7e46fb…), Definition 1.6, (8), p.6;
Definition 6.1, (136), p.36; Theorem 1.12, p.8.

**Formalization Note.** `‖X‖₁` is the trace norm `Re tr √(X†X)` (the published
`WildeQIT.traceNorm`). `L_{H,i}` is the published `lindbladSite H β i`: the [CKG23] Lindbladian
with energy width `σ = β⁻¹` summed over the single-site Pauli jumps on site `i` (Definition 2.17,
p.17); it is meaningful for `β > 0`, which every statement using it assumes. A state is
`ε`-locally metastable when `‖L_{H,i}[σ]‖₁ ≤ ε` for every site `i ∈ [n]`; neither full rank nor
any relation to the Gibbs state is part of the definition. The boundary `∂_A H` of
`H = Σ_{γ∈Γ} h_γ P_γ` keeps the terms whose site support meets both `A` and `Ā = [n] \ A`.
-/

variable {n q k : ℕ}

/-- Definitions 1.6 / 6.1, (8) = (136): `σ` is `ε`-locally metastable with respect to the
Hamiltonian `H` at inverse temperature `β`: `‖L_{H,i}[σ]‖₁ ≤ ε` for every site `i ∈ [n]`. -/
def IsLocallyMetastable (H : Op n q) (β ε : ℝ) (σ : Op n q) : Prop :=
  ∀ i : Fin n, WildeQIT.traceNorm (lindbladSite H β i σ) ≤ ε

/-- The clauses of `Γ` incident on both `A` and `Ā = [n] \ A`: their site support meets both. -/
def boundaryClauses (Γ : Finset (KLocal n q k)) (A : Finset (Fin n)) : Finset (KLocal n q k) :=
  Γ.filter fun γ => (siteSupport γ.1 ∩ A).Nonempty ∧ (siteSupport γ.1 ∩ Aᶜ).Nonempty

/-- Theorem 1.12, p.8: `∂_A H = Σ_{γ ∈ Γ incident on A and Ā} h_γ P_γ`, the Hamiltonian terms
incident on `A` and `Ā`. -/
noncomputable def boundaryHam (Γ : Finset (KLocal n q k)) (h : KLocal n q k → ℝ)
    (A : Finset (Fin n)) : Op n q :=
  ham (boundaryClauses Γ A) h

end StationarityTest.Supplement


