-- Prove2me | Definitions.Def_FlexRigidity_dsOut
-- name    : FlexRigidity_dsOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:20:35.535629+00:00
-- url     : https://prove2.me/theorems/18e206d4-39f2-4091-bfa5-043ba842675e
-- title:
--   Direct-sum output states $\sigma^{\oplus,\mathcal G}$, $\sigma^{\oplus,\mathcal P\circ\mathcal G}$
-- statement:
--   For pure inputs $|\sigma^i\rangle_{M_iR_i}$ and $\sigma^\oplus=\frac1n\sum_i|i\rangle\langle i|_I\otimes|\sigma^i\rangle\langle\sigma^i|$, the channel $\Phi^\oplus[\tau]=\sum_i|i\rangle\langle i|_I\otimes\Phi_i[\tau_{ii}]$ gives $\frac1n\sum_i|i\rangle\langle i|\otimes(\Phi_i\otimes\mathrm{id}_{R_i})[|\sigma^i\rangle\langle\sigma^i|]$, for $\Phi=\mathcal G$ or $\mathcal P\circ\mathcal G$.
--
--   **Formalization Note** Each summand keeps its own reference $R_i\cong M_i$; the paper embeds them in a common $R$, which changes no divergence or distribution.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), §5.5, p. 51

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_ObliviousRSP_pureState
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **The direct-sum output states `σ^{⊕,G}`, `σ^{⊕,P∘G}`** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, §5.5, p. 51): for pure inputs `|σ^i⟩_{M_i R_i}`, the
channel `Φ⊕[τ] = Σ_i |i⟩⟨i|_I ⊗ Φ_i[τ_{ii}]` applied to `σ⊕ = (1/n) Σ_i |i⟩⟨i|_I ⊗ |σ^i⟩⟨σ^i|`:
`(1/n) Σ_i |i⟩⟨i| ⊗ (Φ_i ⊗ id_{R_i})[|σ^i⟩⟨σ^i|]`, block diagonal on the summands labelled by `I`.

**Formalization Note** The summand `i` carries its own reference `R_i ≅ M_i` (the paper embeds the
`R_i` in a common `R`; the isometric embedding does not change any divergence or distribution).
`Φ` is `G` or `P ∘ G`. -/
def dsOut {M W : ℕ → Type} [∀ k, Fintype (M k)] (n : ℕ)
    (Φ : (k : ℕ) → Superop (M k) (W k)) (σ : (i : Fin n) → (M i × M i → ℂ)) :
    Matrix (Σ i : Fin n, M i × W i) (Σ i : Fin n, M i × W i) ℂ :=
  Matrix.blockDiagonal' fun i : Fin n =>
    (((1 / (n : ℝ) : ℝ)) : ℂ) • idTensorSuperop (R := M i) (Φ i) (ObliviousRSP.pureState (σ i))

end FlexRigidity


