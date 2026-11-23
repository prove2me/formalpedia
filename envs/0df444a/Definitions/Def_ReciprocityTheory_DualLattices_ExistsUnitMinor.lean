-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_ExistsUnitMinor
-- name    : ReciprocityTheory_DualLattices_ExistsUnitMinor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:14.731885+00:00
-- url     : https://prove2.me/theorems/da6f2768-693f-481d-91cd-03e4e68efcee
-- title:
--   Exists Unit Minor
-- statement:
--   Definitions and structural lemmas for Exists Unit Minor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsUnitMinor.lean

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqBlockVandermonde
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {v : Valuation C NNReal}
def fder {n : ℕ} (a : Fin n → C) (τ : Fin n) : C := ∏ τ' ∈ Finset.univ.erase τ, (a τ - a τ')
end ReciprocityTheory.PGsh.Up


