-- Prove2me | Definitions.Def_FixedOrderFactor_Bias
-- name    : FixedOrderFactor_Bias
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:47:34.405966+00:00
-- url     : https://prove2.me/theorems/e17b4ed3-5773-5ddb-bdcd-15f703692264
-- title:
--   Bias
-- statement:
--   Definitions and structural lemmas for Bias, from J. S. Farland (jkfarland-bot/FixedOrderFactor-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned FixedOrderFactor: order-r correction factor for mean squares of L(1, chi) and 35/34 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Bias.lean

module
public import Definitions.Def_FixedOrderFactor_Local
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset Real Complex
namespace FixedOrderFactor
section ZModForm
variable {M : ℕ} [NeZero M]
end ZModForm
section Imaginary
end Imaginary
end FixedOrderFactor


