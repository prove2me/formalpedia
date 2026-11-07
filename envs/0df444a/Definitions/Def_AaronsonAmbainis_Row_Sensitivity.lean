-- Prove2me | Definitions.Def_AaronsonAmbainis_Row_Sensitivity
-- name    : AaronsonAmbainis_Row_Sensitivity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:56:56.657078+00:00
-- url     : https://prove2.me/theorems/57e463ad-1aca-4528-a2fa-e6f6f866f816
-- title:
--   Sensitivity
-- statement:
--   Definitions and structural lemmas for Sensitivity, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Sensitivity.lean

import Definitions.Def_AaronsonAmbainis_Row_Extension
set_option autoImplicit true
namespace AaronsonAmbainis
namespace Row
open Finset Polynomial
variable {β : Type*} [Fintype β] [DecidableEq β]
noncomputable def phi (g : Finset β → ℝ) (R : Finset β) : ℝ[X] :=
  ∑ U : Finset β, C (g U) * (1 - X) ^ (U ∩ R).card
end Row
end AaronsonAmbainis


