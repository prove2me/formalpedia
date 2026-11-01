-- Prove2me | Definitions.Def_EntanglementParadigm_marginalAB
-- name    : EntanglementParadigm_marginalAB
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:26:59.117386+00:00
-- url     : https://prove2.me/theorems/5e815664-d85e-4736-8091-32fb8a55e472
-- title:
--   The $A\times B$ marginal $\rho_{AB}$ of a state on $B A' A C$
-- statement:
--   Let $\psi$ be an operator on the finite-dimensional registers $B\otimes A'\otimes A\otimes C$, where $B$ is held by Bob, $A$ and $A'$ by Alice, and $C$ by the receiver Charlie. Its $AB$ marginal is the partial trace over $A'$ and $C$,
--
--   $$
--   \rho_{AB}=\operatorname{Tr}_{A'C}\psi .
--   $$
--
--   This is the operator that side-information must reproduce: a splitting of the purifying system of $\rho_{AB}$ into $A'$ and $C$ is a pure $\psi$ with this marginal.
--
--   **Formalization Note** Registers are ordered $B\times(R\times(A\times C))$, with $R$ the paper's $A'$, and the marginal is ordered $A\times B$. Only $R$ and $C$ are summed, so all off-diagonal $A\times B$ blocks are kept.
-- source:
--   J. Oppenheim, A paradigm for entanglement theory based on quantum communication, arXiv:0801.0458v1, p.2 (the purification and its splitting into $A'$ and $C$)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P75

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

namespace EntanglementParadigm

/-- Oppenheim, arXiv:0801.0458v1, p.2: the reduced state `ρ_AB = Tr_{A′C} |ψ⟩⟨ψ|` of a state on
Bob's register, Alice's ancilla `A′` (here `R`), Alice's share `A` and Charlie's register `C`.

**Formalization Note.** Registers are ordered `B × (R × (A × C))`, the order of
`Intakenext100.P75`, where `R` is the paper's `A′`. The result is ordered `A × B`, the order of
`Dependency50.P19.squashed`. Only `R` and `C` are summed, so the off-diagonal `A × B` blocks are
kept. -/
def marginalAB {A B C R : Type} [Fintype C] [Fintype R]
    (ψ : Mat (B × (R × (A × C)))) : Mat (A × B) :=
  fun x y => ∑ r, ∑ c, ψ (x.2, (r, (x.1, c))) (y.2, (r, (y.1, c)))

end EntanglementParadigm


