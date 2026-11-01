-- Prove2me | Definitions.Def_DattaDiscord_outcomeProb
-- name    : DattaDiscord_outcomeProb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:21:03.788484+00:00
-- url     : https://prove2.me/theorems/3b811d01-3812-4542-aa75-61071f48bd72
-- title:
--   Outcome probability $p_i=\mathrm{Tr}_{A,B}(\Pi_i\rho_{AB})$
-- statement:
--   Let $A$ and $B$ be finite-dimensional quantum systems and $\rho_{AB}$ an operator on $\mathcal H_A\otimes\mathcal H_B$. When system $B$ is measured and the outcome has POVM element $\Pi$ (an operator on $\mathcal H_B$), its probability is
--
--   $$
--   p=\mathrm{Tr}_{A,B}\big((I_A\otimes\Pi)\,\rho_{AB}\big),
--   $$
--
--   Eq. (1) of the paper, where $\Pi$ acts on the joint system as $I_A\otimes\Pi$.
--
--   **Formalization Note** $\mathcal H_A\otimes\mathcal H_B$ is indexed by `A × B` with $A$ the first factor; $I_A\otimes\Pi$ is `Matrix.kronecker 1 Π`; the value is the real part of the trace, which is real when $\rho_{AB}$ is a density matrix and $\Pi\succeq 0$.
-- source:
--   Datta, A Condition for the Nullity of Quantum Discord, arXiv:1003.5256v2, Eq. (1), p.1

import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_Ensemble

open scoped ComplexConjugate

namespace DattaDiscord

/-- **Outcome probability**, Datta, *A Condition for the Nullity of Quantum Discord*, arXiv:1003.5256v2, Eq. (1), p.1: when `B` is measured with the POVM
element `Π`, the probability of that outcome on the joint state `ρ_AB` is
`p = Tr_{A,B}(Π ρ_AB)`, where `Π` acts on `A ⊗ B` as `I_A ⊗ Π`.

**Formalization Note** `A ⊗ B` is indexed by `A × B` with `A` the first factor, `I_A ⊗ Π` is
`Matrix.kronecker 1 Π`, and the value is the real part of the trace (the trace is real for a
density matrix and a positive semidefinite `Π`). -/
noncomputable def outcomeProb {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    (ρ : Matrix (A × B) (A × B) ℂ) (M : Matrix B B ℂ) : ℝ :=
  (Matrix.trace (Matrix.kronecker (1 : Matrix A A ℂ) M * ρ)).re

end DattaDiscord


