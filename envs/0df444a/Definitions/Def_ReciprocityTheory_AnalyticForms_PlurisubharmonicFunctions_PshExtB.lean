-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtB
-- name    : ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:31:32.806729+00:00
-- url     : https://prove2.me/theorems/f7db8b46-9c78-481b-8025-1978e26111f1
-- title:
--   Psh Ext B
-- statement:
--   Definitions and structural lemmas for Psh Ext B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshExtB.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Real Filter Topology MeasureTheory
namespace ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
section
open ReciprocityTheory.AnForm.A
variable {D : ℕ}
noncomputable def ej (j : Fin D) : Fin D → ℂ := Pi.single j 1
section partA
variable {U : Set (Fin D → ℂ)} {S : Finset (Fin D)} {u : (Fin D → ℂ) → ℝ} {C : ℝ}
end partA
end
section
open ReciprocityTheory.AnForm.A
variable {D : ℕ} {U : Set (Fin D → ℂ)} {S : Finset (Fin D)} {u : (Fin D → ℂ) → ℝ} {C : ℝ}
end
section
end
end ReciprocityTheory.AnForm.A.PlurisubharmonicExtension


