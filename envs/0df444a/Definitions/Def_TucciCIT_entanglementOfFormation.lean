-- Prove2me | Definitions.Def_TucciCIT_entanglementOfFormation
-- name    : TucciCIT_entanglementOfFormation
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:29:00.265982+00:00
-- url     : https://prove2.me/theorems/f91bbad4-52b0-4f14-b829-b5713e9ddf05
-- title:
--   Entanglement of formation $E_F(|\psi\rangle)$ of a bipartite pure state
-- statement:
--   Let $|\psi\rangle = \sum_{x,y}\psi(x,y)|x, y\rangle$ be a vector of $\mathcal H_x \otimes \mathcal H_y$ with finite bases $S_x$, $S_y$. Its entanglement of formation is
--
--   $$
--   E_F(|\psi\rangle) = S\big[\operatorname{tr}_y(|\psi\rangle\langle\psi|)\big],
--   $$
--
--   the von Neumann entropy (in bits) of the reduced density matrix on $\mathcal H_x$.
--
--   The main theorem of the paper identifies this quantity with the S-tanglement maximized over local unitaries.
--
--   **Formalization Note** This is the pure-state quantity of eq. (2.1), not the mixed-state entanglement of formation of eq. (2.3). The state is given by its amplitude matrix $\psi$; no normalization is imposed in the definition.
-- source:
--   Tucci, Quantum Entanglement and Conditional Information Transmission, arXiv:quant-ph/9909041v2, eq. (2.1), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20

open QAlgorithms.Papers.Independent.Gap48.P20

namespace TucciCIT

/-- Tucci, *Quantum Entanglement and Conditional Information Transmission*,
arXiv:quant-ph/9909041v2, eq. (2.1), p.3 (PDF p.3).

The entanglement of formation of a bipartite **pure** state `|ψ⟩ = Σ_{x,y} ψ(x,y)|x, y⟩`:
`EF(|ψ⟩) = S[tr_y(|ψ⟩⟨ψ|)]`, the von Neumann entropy (bits) of the reduced density matrix on
`H_x` of the projector `|ψ⟩⟨ψ|` on `H_x ⊗ H_y`.

**Formalization Note.** This is the pure-state EF of eq. (2.1), not the mixed-state EF of
eq. (2.3) (a minimum over ensembles), which the paper does not use for this result. The state is
given by its rectangular amplitude matrix `ψ : Matrix X Y ℂ` (`ψ x y = ⟨x, y|ψ⟩`, p.3). The
partial trace over `y` is the platform's `Gap48.P20.redistributionMarginal` with `keep = Prod.fst`,
`forget = Prod.snd`. No normalization is imposed here. -/
noncomputable def entanglementOfFormation {X Y : Type*} [Fintype X] [Fintype Y]
    (ψ : Matrix X Y ℂ) : ℝ :=
  subsystemEntropy (Matrix.of fun i j : X × Y => ψ i.1 i.2 * star (ψ j.1 j.2))
    Prod.fst Prod.snd

end TucciCIT


