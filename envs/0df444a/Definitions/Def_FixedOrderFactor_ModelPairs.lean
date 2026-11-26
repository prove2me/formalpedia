-- Prove2me | Definitions.Def_FixedOrderFactor_ModelPairs
-- name    : FixedOrderFactor_ModelPairs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:47:05.369866+00:00
-- url     : https://prove2.me/theorems/a72b043f-8e94-53c0-bffd-8d2915f6a64a
-- title:
--   Model Pairs
-- statement:
--   Definitions and structural lemmas for Model Pairs, from J. S. Farland (jkfarland-bot/FixedOrderFactor-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned FixedOrderFactor: order-r correction factor for mean squares of L(1, chi) and 35/34 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/ModelPairs.lean

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Pairs
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset Complex
namespace FixedOrderFactor
noncomputable abbrev ω (r : ℕ) : ℂ := Complex.exp (2 * Real.pi * I / r)
noncomputable def zPow (r : ℕ) (S : Finset Nat.Primes) (j : S → Fin r) (m : ℕ) : ℂ :=
  ∏ q : S, rootOfUnity r ((j q : ℕ) * m.factorization (q : Nat.Primes))
end FixedOrderFactor


