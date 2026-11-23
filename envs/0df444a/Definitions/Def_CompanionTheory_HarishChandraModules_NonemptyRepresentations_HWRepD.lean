-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_NonemptyRepresentations_HWRepD
-- name    : CompanionTheory_HarishChandraModules_NonemptyRepresentations_HWRepD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:52.373985+00:00
-- url     : https://prove2.me/theorems/ae638fc7-5d23-4794-80e8-3b06fbf3c19a
-- title:
--   HWRep D
-- statement:
--   Definitions and structural lemmas for HWRep D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/NonemptyRepresentations/HWRepD.lean

import Definitions.Def_CompanionTheory_HarishChandraModules_NonemptyRepresentations_NonemptyOfAntitone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace CompanionTheory.D.Inhab.HWRep
variable {k : ℕ} {ν : Fin k → ℤ} (R : HWRep k ν)
def one' (k : ℕ) : Fin k → Fin k → ℂ := (1 : Matrix (Fin k) (Fin k) ℂ)
def D (Y : Matrix (Fin k) (Fin k) ℂ) : Matrix R.I R.I ℂ :=
  Matrix.of fun i j => fderiv ℂ (fun B : Fin k → Fin k → ℂ => R.ρ (Matrix.of B) i j) (one' k) (fun a b => Y a b)
end CompanionTheory.D.Inhab.HWRep


