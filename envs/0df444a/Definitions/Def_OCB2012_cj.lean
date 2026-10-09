-- Prove2me | Definitions.Def_OCB2012_cj
-- name    : OCB2012_cj
-- status  : Definition
-- author  : @Alien60
-- created : 2026-10-09T09:43:39.683465+00:00
-- url     : https://prove2.me/theorems/998b2961-ba61-4769-8e87-9087c86deb36
-- title:
--   Choi–Jamiołkowski matrix $M^{X_1X_2} = [\mathcal I\otimes\mathcal M(|\phi^+\rangle\langle\phi^+|)]^{T}$, partial trace $\mathrm{Tr}_1$, trace preservation
-- statement:
--   Definitions for the Choi–Jamiołkowski (CJ) correspondence used by Oreshkov, Costa and Brukner (2012).
--
--   1. **CJ matrix (p. 3).** For a linear map $\mathcal M : \mathcal L(\mathcal H^{X_1})\to\mathcal L(\mathcal H^{X_2})$,
--   $$M^{X_1X_2} := \big[\mathcal I\otimes\mathcal M(|\phi^+\rangle\langle\phi^+|)\big]^{T},\qquad |\phi^+\rangle = \sum_j |jj\rangle,$$
--   where $|\phi^+\rangle$ is not normalized and $T$ is the full transpose. In the index order $X_1\times X_2$ its entries are $M_{(i,k),(j,l)} = \mathcal M(|j\rangle\langle i|)_{lk}$.
--   2. **Partial trace over the first factor:** $(\mathrm{Tr}_1 M)_{kl} = \sum_i M_{(i,k),(i,l)}$. It complements `ptrace₂` from `OCB2012_defs`.
--   3. **Trace preservation:** $\mathrm{Tr}\,\mathcal M(\rho) = \mathrm{Tr}\,\rho$ for every $\rho$.
--
--   These definitions connect the mission's representation of local operations by CJ matrices to the maps themselves.
-- source:
--   O. Oreshkov, F. Costa, C. Brukner, Quantum correlations with no causal order, Nat. Commun. 3, 1092 (2012), https://arxiv.org/abs/1105.4464v3, p. 3 (definition of the CJ matrix) and Appendix B, Eq. (15)

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs

/-!
# The Choi–Jamiołkowski matrix (Oreshkov–Costa–Brukner 2012, p. 3 and App. B)

O. Oreshkov, F. Costa, Č. Brukner, *Quantum correlations with no causal order*,
Nat. Commun. 3, 1092 (2012), arXiv:1105.4464v3.

For a linear map `𝓜 : L(H^{X1}) → L(H^{X2})` the paper (p. 3) defines its CJ matrix
`M^{X1X2} := [𝓘 ⊗ 𝓜(|φ⁺⟩⟨φ⁺|)]ᵀ`, with `|φ⁺⟩ = ∑ⱼ |jj⟩` (not normalized) and `ᵀ` the full
transpose. Expanding `|φ⁺⟩⟨φ⁺| = ∑_{i,j} |i⟩⟨j| ⊗ |i⟩⟨j|` gives the entries
`M_{(i,k),(j,l)} = 𝓜(|j⟩⟨i|)_{l k}`, in the index order `X1 × X2` used throughout the mission.
-/

namespace OCB2012

open Matrix

noncomputable section

/-- p. 3: the CJ matrix `M^{X1X2} = [𝓘 ⊗ 𝓜(|φ⁺⟩⟨φ⁺|)]ᵀ` of a linear map
`𝓜 : L(H^{X1}) → L(H^{X2})`; entrywise `M_{(i,k),(j,l)} = 𝓜(|j⟩⟨i|)_{l k}`. -/
def cjMatrix {x1 x2 : Type*} [DecidableEq x1]
    (Φ : Matrix x1 x1 ℂ →ₗ[ℂ] Matrix x2 x2 ℂ) : Matrix (x1 × x2) (x1 × x2) ℂ :=
  Matrix.of fun r c => Φ (Matrix.single c.1 r.1 1) c.2 r.2

/-- Partial trace over the first tensor factor:
`(Tr₁ M)_{kl} = ∑ᵢ M_{(i,k),(i,l)}`. -/
def ptrace₁ {α β : Type*} [Fintype α] (M : Matrix (α × β) (α × β) ℂ) : Matrix β β ℂ :=
  Matrix.of fun k l => ∑ i, M (i, k) (i, l)

/-- A linear map is trace preserving: `Tr 𝓜(ρ) = Tr ρ` for every `ρ`. -/
def IsTracePreserving {x1 x2 : Type*} [Fintype x1] [Fintype x2]
    (Φ : Matrix x1 x1 ℂ →ₗ[ℂ] Matrix x2 x2 ℂ) : Prop :=
  ∀ ρ, (Φ ρ).trace = ρ.trace

end

end OCB2012


