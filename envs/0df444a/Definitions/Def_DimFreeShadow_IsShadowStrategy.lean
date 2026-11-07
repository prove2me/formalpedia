-- Prove2me | Definitions.Def_DimFreeShadow_IsShadowStrategy
-- name    : DimFreeShadow_IsShadowStrategy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:02:03.845203+00:00
-- url     : https://prove2.me/theorems/76651334-a9cf-40c7-849c-2285bb5dd9ac
-- title:
--   Definition 1.1 — shadow-tomography strategy with accuracy $\varepsilon$ and failure probability $\delta$
-- statement:
--   Let $E_1,\dots,E_M$ be effects on a finite-dimensional Hilbert space $\mathcal H$. A $T$-copy **shadow-tomography strategy** consists of a POVM $\{N_z\}_{z\in\mathcal Z}$ on $\mathcal H^{\otimes T}$ and a decoder $g:\mathcal Z\to[0,1]^M$. On an input state $\rho$ the outcome has law $\mathbb P_\rho[Z=z]=\operatorname{Tr}(N_z\rho^{\otimes T})$. The strategy has accuracy $\varepsilon$ and failure probability $\delta$ if
--
--   $$
--   \sup_{\rho\in\mathcal D(\mathcal H)}\mathbb P_\rho\Big[\max_{1\le j\le M}|g_j(Z)-\operatorname{Tr}(E_j\rho)|>\varepsilon\Big]\le\delta .
--   $$
--
--   One measurement and one decoder work for every input state: they may depend on the known list of effects, not on $\rho$. This module defines the failure probability at $\rho$ and the strategy predicate, the object the goal theorem and Corollary 5.7 assert to exist.
--
--   **Formalization Note** The outcome set is a finite type, the form of Theorem 5.8 and Corollary 5.7. Traces enter through their real parts. The supremum bound is stated as a bound at every density matrix.
-- source:
--   Jeronimo, Huang, Liu, Dimension-Free Polylogarithmic Quantum Shadow Tomography, arXiv:2608.06345 (sha256 a1a42249…), Definition 1.1, p.2

import Mathlib
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QAlgorithms_Defs_Ensemble

namespace DimFreeShadow

open ShadowTomography.UpperBound (tensorPow)

/-- **Failure probability of a shadow-tomography strategy** (arXiv:2608.06345, sha256
a1a42249…, Definition 1.1, p.2). For a POVM `{N_z}_{z ∈ Z}` on `H^{⊗T}`, a decoder
`g : Z → ℝ^M`, effects `E₁, …, E_M`, a tolerance `ε` and an input state `ρ`, this is
`P_ρ[max_{1≤j≤M} |g_j(Z) − Tr(E_j ρ)| > ε] = Σ_{z : ∃ j, |g_j(z) − Tr(E_jρ)| > ε} Tr(N_z ρ^{⊗T})`,
with `P_ρ[Z = z] := Tr(N_z ρ^{⊗T})`.

**Formalization Note** `H = ℂ^d` for a finite type `d`; `H^{⊗T}` is indexed by `Fin T → d` and
`ρ^{⊗T}` is the published `ShadowTomography.UpperBound.tensorPow ρ T`. Traces enter through their
real parts (they are real for an effect and a state). The observables are indexed `0, …, M−1`
(`Fin M`). The event `max_j |…| > ε` is written `∃ j, ε < |…|`, which is the same event. -/
noncomputable def failureProb {d Z : Type} [Fintype d] [Fintype Z] {M T : ℕ}
    (E : Fin M → Matrix d d ℂ) (N : Z → Matrix (Fin T → d) (Fin T → d) ℂ)
    (g : Z → Fin M → ℝ) (ε : ℝ) (ρ : Matrix d d ℂ) : ℝ := by
  classical
  exact ∑ z ∈ Finset.univ.filter (fun z => ∃ j, ε < |g z j - (Matrix.trace (E j * ρ)).re|),
    (Matrix.trace (N z * tensorPow ρ T)).re

/-- **Shadow-tomography strategy with accuracy `ε` and failure probability `δ`**
(arXiv:2608.06345, sha256 a1a42249…, Definition 1.1, p.2): "A T-copy shadow-tomography strategy
for E1, …, EM consists of a POVM {Nz}z∈Z on H⊗T and a decoder g: Z → [0, 1]M. … The strategy has
accuracy ε and failure probability δ if sup_{ρ∈D(H)} Pρ[max_{1≤j≤M} |gj(Z) − Tr(Ejρ)| > ε] ≤ δ."
One measurement and one decoder work for every input state.

**Formalization Note** The outcome set `Z` is a finite type (`Theorem 5.8` and `Corollary 5.7`
assert finite-outcome strategies; this is the form the paper constructs). The POVM condition is
the published `QAlgorithms.IsPOVM` (positive semidefinite effects summing to the identity). The
decoder takes values in `[0,1]^M`. "`sup_ρ … ≤ δ`" is "`… ≤ δ` for every density matrix `ρ`"
(`WildeQIT.IsDensityOperator`: positive semidefinite, trace one). -/
def IsShadowStrategy {d Z : Type} [Fintype d] [DecidableEq d] [Fintype Z] {M T : ℕ}
    (E : Fin M → Matrix d d ℂ) (N : Z → Matrix (Fin T → d) (Fin T → d) ℂ)
    (g : Z → Fin M → ℝ) (ε δ : ℝ) : Prop :=
  QAlgorithms.IsPOVM N ∧ (∀ z j, 0 ≤ g z j ∧ g z j ≤ 1) ∧
    ∀ ρ : Matrix d d ℂ, WildeQIT.IsDensityOperator ρ → failureProb E N g ε ρ ≤ δ

end DimFreeShadow


