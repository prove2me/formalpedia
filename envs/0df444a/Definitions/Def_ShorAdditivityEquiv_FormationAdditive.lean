-- Prove2me | Definitions.Def_ShorAdditivityEquiv_FormationAdditive
-- name    : ShorAdditivityEquiv_FormationAdditive
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:29:19.35424+00:00
-- url     : https://prove2.me/theorems/cf817a28-47ea-41df-b543-ce9c26abb5d7
-- title:
--   Statement (iii): additivity of the entanglement of formation $E_F(\sigma_1\otimes\sigma_2)=E_F(\sigma_1)+E_F(\sigma_2)$ for all pairs of states
-- statement:
--   Statement (iii) of Theorem 1, *additivity of the entanglement of formation*: for **every** pair of quantum states $\sigma_1$ on $\mathcal H_{A_1}\otimes\mathcal H_{B_1}$ and $\sigma_2$ on $\mathcal H_{A_2}\otimes\mathcal H_{B_2}$, of every finite dimensions,
--   $$
--   E_F(\sigma_1\otimes\sigma_2) = E_F(\sigma_1) + E_F(\sigma_2),
--   $$
--   where $E_F(\sigma)=\min\sum_i p_i H(\mathrm{Tr}_B|v_i\rangle\langle v_i|)$ over pure decompositions $\sum_i p_i|v_i\rangle\langle v_i|=\sigma$ (Eq. (2)), and on the left the entanglement of formation is calculated over the bipartite partition $A_1A_2\,|\,B_1B_2$. This is a single proposition about all states (later shown to be false); the mission does not assert it or its negation.
--
--   **Formalization Note** States are `QAlgorithms.IsDensityMatrix` (positive semidefinite, trace one) on nonempty finite types in `Type`. $E_F$ is the platform's `formation` (P08 bundle), Eq. (2) as an infimum over finite pure-state decompositions, tracing the second factor. $\sigma_1\otimes\sigma_2$ is `tensorState`, regrouped to the $A\,|\,B$ cut.
-- source:
--   Shor, Equivalence of Additivity Questions in Quantum Information Theory, arXiv:quant-ph/0305035v4, Theorem 1 (iii), p. 5; Eq. (2), p. 4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_ShorAdditivityEquiv_tensorState

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P08

namespace ShorAdditivityEquiv

/-- Shor, *Equivalence of Additivity Questions in Quantum Information Theory*, arXiv:quant-ph/0305035v4, Theorem 1 (iii), p.5: "Additivity of the entanglement of formation. Suppose we have
two quantum states σ1 ∈ H_{A1} ⊗ H_{B1} and σ2 ∈ H_{A2} ⊗ H_{B2}. Then
E_F(σ1 ⊗ σ2) = E_F(σ1) + E_F(σ2), where E_F is defined as in Eq. (2). In particular, the
entanglement of formation is calculated over the bipartite A–B partition."

The proposition asserts this for **every** pair of bipartite states of **every** finite
dimensions; it is a single global statement, not a property of one pair.

**Formalization Note.** The spaces are nonempty finite types in `Type`; "quantum state" is
`QAlgorithms.IsDensityMatrix` (positive semidefinite, trace 1). `E_F` is the published
`QAlgorithms.Papers.Independent.Information100.P08.formation`, Eq. (2) as an infimum over
finite pure-state decompositions, tracing the second (`B`) factor. `σ1 ⊗ σ2` is
`tensorState σ₁ σ₂`, the Kronecker product regrouped to the cut `A₁A₂ | B₁B₂`. -/
def FormationAdditive : Prop :=
  ∀ (A₁ B₁ A₂ B₂ : Type) [Fintype A₁] [DecidableEq A₁] [Nonempty A₁] [Fintype B₁]
    [DecidableEq B₁] [Nonempty B₁] [Fintype A₂] [DecidableEq A₂] [Nonempty A₂] [Fintype B₂]
    [DecidableEq B₂] [Nonempty B₂] (σ₁ : Matrix (A₁ × B₁) (A₁ × B₁) ℂ)
    (σ₂ : Matrix (A₂ × B₂) (A₂ × B₂) ℂ),
    IsDensityMatrix σ₁ → IsDensityMatrix σ₂ →
    formation (tensorState σ₁ σ₂) = formation σ₁ + formation σ₂

end ShorAdditivityEquiv


