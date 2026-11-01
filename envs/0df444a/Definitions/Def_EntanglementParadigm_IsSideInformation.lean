-- Prove2me | Definitions.Def_EntanglementParadigm_IsSideInformation
-- name    : EntanglementParadigm_IsSideInformation
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:28:16.525021+00:00
-- url     : https://prove2.me/theorems/93230801-52f6-4ad0-a92e-3ff4a5f7317a
-- title:
--   Side-information $\rho_{A'C}$ for $\rho_{AB}$: a pure state with marginal $\rho_{AB}$
-- statement:
--   Let $\rho_{AB}$ be a state of Alice and Bob. A state $\psi$ on $B\otimes A'\otimes A\otimes C$ is side-information for $\rho_{AB}$ when
--
--   1. $\psi=|\psi\rangle\langle\psi|$ is pure, with $\||\psi\rangle\|=1$, and
--   2. $\operatorname{Tr}_{A'C}\psi=\rho_{AB}$.
--
--   Thus $A'C$ purifies $\rho_{AB}$: the purifying system $E$ has been split into a part $A'$ given to the sender Alice and a part $C$ given to the receiver Charlie. Its reduction to $A'C$ is the state $\rho_{A'C}$ of the paper, over which Theorem 1 takes its infimum.
--
--   **Formalization Note** Registers are ordered $B\times(R\times(A\times C))$, with $R$ the paper's $A'$. All registers are finite. Nonemptiness of each follows from the unit vector.
-- source:
--   J. Oppenheim, A paradigm for entanglement theory based on quantum communication, arXiv:0801.0458v1, p.2 ("One may therefor want to split ρE into two shares"; "the purity of the total state"), Fig. 1

import Definitions.Def_EntanglementParadigm_marginalAB

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)
open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

namespace EntanglementParadigm

/-- Oppenheim, arXiv:0801.0458v1, p.2: `ψ` is side-information for `ρ_AB`. The state of
Bob's register `B`, Alice's ancilla `A′` (here `R`), Alice's share `A` and Charlie's register `C`
is pure, and its `A × B` marginal is exactly `ρ_AB`: the purifying system `E` of `ρ_AB` has been
split into `A′` and `C` ("the purity of the total state", "`ρ_C` is a splitting of `ρ_E`").

**Formalization Note.** Registers are ordered `B × (R × (A × C))`, with `R` the paper's `A′`.
Every register is finite; nonemptiness follows from `IsPure`, whose vector has norm one. -/
def IsSideInformation {A B C R : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype R]
    (ρ : Mat (A × B)) (ψ : Mat (B × (R × (A × C)))) : Prop :=
  IsPure ψ ∧ marginalAB ψ = ρ

end EntanglementParadigm


