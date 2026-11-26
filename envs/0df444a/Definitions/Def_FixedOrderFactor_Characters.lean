-- Prove2me | Definitions.Def_FixedOrderFactor_Characters
-- name    : FixedOrderFactor_Characters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:46:33.811861+00:00
-- url     : https://prove2.me/theorems/c0ecce4a-427f-4bea-a0f8-64921c09bd03
-- title:
--   Characters
-- statement:
--   Definitions and structural lemmas for Characters, from J. S. Farland (jkfarland-bot/FixedOrderFactor-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned FixedOrderFactor: order-r correction factor for mean squares of L(1, chi) and 35/34 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Characters.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace FixedOrderFactor
variable (p : ℕ) [Fact p.Prime]
abbrev powers (r : ℕ) : Subgroup (ZMod p)ˣ := (powMonoidHom r : (ZMod p)ˣ →* (ZMod p)ˣ).range
noncomputable abbrev dualPowers (r : ℕ) : Subgroup (MulChar (ZMod p) ℂ) :=
  (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod p) ℂ (powers p r)).ofDual
noncomputable instance (r : ℕ) : Fintype (dualPowers p r) := Fintype.ofFinite _
end FixedOrderFactor


