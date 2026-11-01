-- Prove2me | Definitions.Def_ShorAdditivityEquiv_HolevoCapacityAdditive
-- name    : ShorAdditivityEquiv_HolevoCapacityAdditive
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:30:56.961634+00:00
-- url     : https://prove2.me/theorems/90bbea18-baa1-40b7-bc53-b750f9c711d5
-- title:
--   Statement (ii): additivity of the Holevo capacity $\chi_{N_1\otimes N_2}=\chi_{N_1}+\chi_{N_2}$ for all pairs of channels
-- statement:
--   Statement (ii) of Theorem 1, *the additivity of the Holevo capacity of a quantum channel*: for **every** pair of quantum channels $N_1$, $N_2$ of every finite dimensions, as in (i),
--   $$
--   \chi_{N_1\otimes N_2} = \chi_{N_1} + \chi_{N_2},
--   $$
--   where $\chi$ is the Holevo capacity of Eq. (1). This is a single proposition about all channels (later shown to be false by Hastings, 2009); the mission does not assert it or its negation.
--
--   **Formalization Note** Same conventions as statement (i): nonempty finite types in `Type`, `QAlgorithms.IsChannel`, `ShorEBAdditivity.tensorChannel`; $\chi$ is `holevoCapacity` (pure-state ensembles).
-- source:
--   Shor, Equivalence of Additivity Questions in Quantum Information Theory, arXiv:quant-ph/0305035v4, Theorem 1 (ii), p. 5

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_ShorEBAdditivity_tensorChannel
import Definitions.Def_ShorAdditivityEquiv_holevoCapacity

open QAlgorithms

namespace ShorAdditivityEquiv

/-- Shor, *Equivalence of Additivity Questions in Quantum Information Theory*, arXiv:quant-ph/0305035v4, Theorem 1 (ii), p.5: "The additivity of the Holevo capacity of a quantum channel,
Assume we have two quantum channels N1 and N2, as in (i). Then χ_{N1⊗N2} = χ_{N1} + χ_{N2},
where χ is defined as in Eq. (1)."

The proposition asserts this for **every** pair of channels of **every** finite dimensions; it
is a single global statement, not a property of one pair.

**Formalization Note.** Same conventions as `MinOutputEntropyAdditive`: nonempty finite types
in `Type`, `QAlgorithms.IsChannel` for "CPT map", `ShorEBAdditivity.tensorChannel` for
`N₁ ⊗ N₂`. `χ` is `holevoCapacity` (Eq. (1), pure-state ensembles, supremum attained). -/
def HolevoCapacityAdditive : Prop :=
  ∀ (I₁ O₁ I₂ O₂ : Type) [Fintype I₁] [DecidableEq I₁] [Nonempty I₁] [Fintype O₁]
    [DecidableEq O₁] [Nonempty O₁] [Fintype I₂] [DecidableEq I₂] [Nonempty I₂] [Fintype O₂]
    [DecidableEq O₂] [Nonempty O₂] (N₁ : Superop I₁ O₁) (N₂ : Superop I₂ O₂),
    IsChannel N₁ → IsChannel N₂ →
    holevoCapacity (ShorEBAdditivity.tensorChannel N₁ N₂) =
      holevoCapacity N₁ + holevoCapacity N₂

end ShorAdditivityEquiv


