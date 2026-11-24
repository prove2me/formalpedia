-- Prove2me | Definitions.Def_BalanceSpecificaton_ArbitraryEntropy
-- name    : BalanceSpecificaton_ArbitraryEntropy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:01:49.365653+00:00
-- url     : https://prove2.me/theorems/8b1ab5f4-cf7a-4459-a3cc-bf4758a36db5
-- title:
--   Arbitrary Entropy
-- statement:
--   Definitions and structural lemmas for Arbitrary Entropy, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/ArbitraryEntropy.lean

module
public import Definitions.Def_BalanceSpecificaton_MarkerConstruction
public import Definitions.Def_BalanceSpecificaton_EntropyModel
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification
namespace ArbitraryEntropy
abbrev Alphabet (n : ℕ) := Option (Fin n × Bool)
instance alphabetTopology (n : ℕ) : TopologicalSpace (Alphabet n) := ⊥
instance alphabetDiscrete (n : ℕ) : DiscreteTopology (Alphabet n) := ⟨rfl⟩
end ArbitraryEntropy
end BalanceSpecification


