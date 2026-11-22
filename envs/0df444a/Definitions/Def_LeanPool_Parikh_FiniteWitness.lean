-- Prove2me | Definitions.Def_LeanPool_Parikh_FiniteWitness
-- name    : LeanPool_Parikh_FiniteWitness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T09:50:33.004358+00:00
-- url     : https://prove2.me/theorems/579556e9-22b0-4554-aa7e-86b7eae88769
-- title:
--   Finite Witness
-- statement:
--   Definitions and structural lemmas for Finite Witness, from Umang Mathur; LeanPool contributors's pinned Parikh's theorem and a certified semilinear grammar compiler development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/FiniteWitness.lean

module
public import Definitions.Def_LeanPool_Parikh_Activation
public import Definitions.Def_LeanPool_Parikh_GrammarImage
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace Parikh
variable {T : Type*} [DecidableEq T]
@[expose] noncomputable def familyWitness (g : ContextFreeGrammar T)
    (bases cycles : Finset (ParseTree T g.NT)) : Witness T := by
  classical
  exact ((bases ×ˢ cycles.powerset).filter fun pair =>
    ContextsActivatable g pair.1 pair.2).toList.map fun pair => contextComponent pair.1 pair.2
end Parikh


