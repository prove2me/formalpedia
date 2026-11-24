-- Prove2me | Definitions.Def_RequestProject_NineteenEighteenths
-- name    : RequestProject_NineteenEighteenths
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:10:59.747395+00:00
-- url     : https://prove2.me/theorems/1cf00cfc-f9d5-48cf-8d16-42a090a19462
-- title:
--   Nineteen Eighteenths
-- statement:
--   Definitions and structural lemmas for Nineteen Eighteenths, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/NineteenEighteenths.lean

import Mathlib
import Definitions.Def_RequestProject_ChoresExamples
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_FeigeNorkinChores
set_option autoImplicit true
open scoped BigOperators
namespace FairChores
namespace NineteenEighteenths
open FeigeNorkinChores
noncomputable def instP (lam : ℝ) : Fin 8 → ℝ := fun t => lam * (fcU t : ℝ)
noncomputable def instC (lam : ℝ) : Fin 3 → Fin 8 → ℝ :=
  ![fun t => (fcR t : ℝ), fun t => (fcC t : ℝ), instP lam]
noncomputable def lamOf (rho : ℝ) : ℝ := 2 + 720 * |rho| / (380 - 360 * rho)
end NineteenEighteenths
end FairChores


