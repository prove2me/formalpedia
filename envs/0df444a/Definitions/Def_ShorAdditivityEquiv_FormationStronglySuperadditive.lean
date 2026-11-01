-- Prove2me | Definitions.Def_ShorAdditivityEquiv_FormationStronglySuperadditive
-- name    : ShorAdditivityEquiv_FormationStronglySuperadditive
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:29:23.466315+00:00
-- url     : https://prove2.me/theorems/53ce9b02-454f-471b-ab3e-d999364f86e4
-- title:
--   Statement (iv): strong superadditivity $E_F(\sigma)\ge E_F(\mathrm{Tr}_2\sigma)+E_F(\mathrm{Tr}_1\sigma)$ for all four-party states
-- statement:
--   Statement (iv) of Theorem 1, *the strong superadditivity of the entanglement of formation*: for **every** density matrix $\sigma$ on a four-party system $\mathcal H_{A_1}\otimes\mathcal H_{A_2}\otimes\mathcal H_{B_1}\otimes\mathcal H_{B_2}$ of every finite dimensions,
--   $$
--   E_F(\sigma) \ge E_F(\mathrm{Tr}_2\,\sigma) + E_F(\mathrm{Tr}_1\,\sigma),
--   $$
--   where the entanglement of formation is calculated over the bipartite $A$–$B$ partition, $\mathrm{Tr}_1$ traces out $\mathcal H_{A_1}\otimes\mathcal H_{B_1}$ and $\mathrm{Tr}_2$ traces out $\mathcal H_{A_2}\otimes\mathcal H_{B_2}$. This is a single proposition about all states (later shown to be false); the mission does not assert it or its negation.
--
--   **Formalization Note** The four-party space is indexed by $(A_1\times A_2)\times(B_1\times B_2)$, so the $A\,|\,B$ cut is the outer product and `formation` computes $E_F$ across it. $\mathrm{Tr}_2$ is `trTwo` (onto $A_1\times B_1$), $\mathrm{Tr}_1$ is `trOne` (onto $A_2\times B_2$). The four spaces are nonempty finite types in `Type`.
-- source:
--   Shor, Equivalence of Additivity Questions in Quantum Information Theory, arXiv:quant-ph/0305035v4, Theorem 1 (iv), p. 6; Eq. (14), p. 12

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_ShorAdditivityEquiv_trTwo
import Definitions.Def_ShorAdditivityEquiv_trOne

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P08

namespace ShorAdditivityEquiv

/-- Shor, *Equivalence of Additivity Questions in Quantum Information Theory*, arXiv:quant-ph/0305035v4, Theorem 1 (iv), p.6: "The strong superadditivity of the entanglement of formation.
Suppose we have a density matrix σ over a quadripartite system system
H_{A1} ⊗ H_{A2} ⊗ H_{B1} ⊗ H_{B2}. Then E_F(σ) ≥ E_F(Tr2 σ) + E_F(Tr1 σ), where the entanglement of
formation is calculated over the bipartite A–B partition. Here, the operator Tr1 traces out the
space H_{A1} ⊗ H_{B1}, and Tr2 traces out the space H_{A2} ⊗ H_{B2}."

The proposition asserts this for **every** density matrix on **every** finite quadripartite
system; it is a single global statement.

**Formalization Note.** The quadripartite space is indexed by `(A₁ × A₂) × (B₁ × B₂)`, so the
`A | B` cut is the outer product and `formation` (published P08, Eq. (2)) computes `E_F`
across it. `Tr₂` is `trTwo` (lands on `A₁ × B₁`), `Tr₁` is `trOne` (lands on `A₂ × B₂`). The
four spaces are nonempty finite types in `Type`. -/
def FormationStronglySuperadditive : Prop :=
  ∀ (A₁ A₂ B₁ B₂ : Type) [Fintype A₁] [DecidableEq A₁] [Nonempty A₁] [Fintype A₂]
    [DecidableEq A₂] [Nonempty A₂] [Fintype B₁] [DecidableEq B₁] [Nonempty B₁] [Fintype B₂]
    [DecidableEq B₂] [Nonempty B₂]
    (σ : Matrix ((A₁ × A₂) × (B₁ × B₂)) ((A₁ × A₂) × (B₁ × B₂)) ℂ),
    IsDensityMatrix σ → formation (trTwo σ) + formation (trOne σ) ≤ formation σ

end ShorAdditivityEquiv


