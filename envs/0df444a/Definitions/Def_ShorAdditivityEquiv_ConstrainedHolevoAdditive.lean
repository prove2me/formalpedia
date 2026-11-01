-- Prove2me | Definitions.Def_ShorAdditivityEquiv_ConstrainedHolevoAdditive
-- name    : ShorAdditivityEquiv_ConstrainedHolevoAdditive
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:31:28.468365+00:00
-- url     : https://prove2.me/theorems/2c32193c-cf05-4158-8b36-09a6d7380fe8
-- title:
--   Additivity of the constrained Holevo capacity $\chi_{N_1\otimes N_2}(\rho_1\otimes\rho_2)=\chi_{N_1}(\rho_1)+\chi_{N_2}(\rho_2)$ for all channels and inputs
-- statement:
--   Additivity of the constrained Holevo capacity, as in §3: for **every** pair of quantum channels $N_1$, $N_2$ of every finite dimensions and every pair of density matrices $\rho_1$, $\rho_2$ on their input spaces,
--   $$
--   \chi_{N_1\otimes N_2}(\rho_1\otimes\rho_2) = \chi_{N_1}(\rho_1) + \chi_{N_2}(\rho_2),
--   $$
--   where $\chi_N(\rho)$ is the constrained Holevo capacity of Eq. (3). The paper shows that this is equivalent to the additivity of the entanglement of formation ("the entanglement of formation $E_F$ is additive if and only if the constrained capacity $\chi_N(\rho)$ is").
--
--   **Formalization Note** Same conventions as statement (i); $\rho_1\otimes\rho_2$ is the Kronecker product on $I_1\times I_2$, the input space of `ShorEBAdditivity.tensorChannel N₁ N₂`.
-- source:
--   Shor, Equivalence of Additivity Questions in Quantum Information Theory, arXiv:quant-ph/0305035v4, §3, p. 7

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_ShorEBAdditivity_tensorChannel
import Definitions.Def_ShorAdditivityEquiv_constrainedHolevo

open QAlgorithms
open scoped Kronecker

namespace ShorAdditivityEquiv

/-- Shor, *Equivalence of Additivity Questions in Quantum Information Theory*, arXiv:quant-ph/0305035v4, §3, p.7: additivity of the constrained Holevo capacity, "the constrained capacity
χN(ρ) is [additive]", i.e. `χ_{N1⊗N2}(ρ1 ⊗ ρ2) = χ_{N1}(ρ1) + χ_{N2}(ρ2)` for all channels
`N1`, `N2` and all input density matrices `ρ1`, `ρ2`.

The proposition asserts this for **every** pair of channels of **every** finite dimensions and
every pair of input states; it is a single global statement.

**Formalization Note.** Same conventions as `MinOutputEntropyAdditive`. `ρ₁ ⊗ ρ₂` is the
Kronecker product `ρ₁ ⊗ₖ ρ₂` on `I₁ × I₂`, the input space of
`ShorEBAdditivity.tensorChannel N₁ N₂`. `χ_N(ρ)` is `constrainedHolevo` (Eq. (3)). -/
def ConstrainedHolevoAdditive : Prop :=
  ∀ (I₁ O₁ I₂ O₂ : Type) [Fintype I₁] [DecidableEq I₁] [Nonempty I₁] [Fintype O₁]
    [DecidableEq O₁] [Nonempty O₁] [Fintype I₂] [DecidableEq I₂] [Nonempty I₂] [Fintype O₂]
    [DecidableEq O₂] [Nonempty O₂] (N₁ : Superop I₁ O₁) (N₂ : Superop I₂ O₂)
    (ρ₁ : Matrix I₁ I₁ ℂ) (ρ₂ : Matrix I₂ I₂ ℂ),
    IsChannel N₁ → IsChannel N₂ → IsDensityMatrix ρ₁ → IsDensityMatrix ρ₂ →
    constrainedHolevo (ShorEBAdditivity.tensorChannel N₁ N₂) (ρ₁ ⊗ₖ ρ₂) =
      constrainedHolevo N₁ ρ₁ + constrainedHolevo N₂ ρ₂

end ShorAdditivityEquiv


