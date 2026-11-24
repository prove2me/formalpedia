-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExt
-- name    : ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:19.047174+00:00
-- url     : https://prove2.me/theorems/9e60db77-5401-43ad-8f21-eddbafda29bb
-- title:
--   Psh Ext
-- statement:
--   Definitions and structural lemmas for Psh Ext, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshExt.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtB
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
variable {D : ℕ} {U : Set (Fin D → ℂ)} {S : Finset (Fin D)} {u : (Fin D → ℂ) → ℝ} {C κ : ℝ}
def trunc (u : (Fin D → ℂ) → ℝ) (κ : ℝ) : (Fin D → ℂ) → ℝ := fun z => max (u z) (-κ)
noncomputable def vext (U : Set (Fin D → ℂ)) (S : Finset (Fin D)) (u : (Fin D → ℂ) → ℝ) (κ : ℝ) :
    (Fin D → ℂ) → ℝ :=
  limsupExt U (coordDiv S) (trunc u κ)
section partB
variable (hU : IsOpen U) (hU1 : U ⊆ ball 0 1) (hc : ContinuousOn u (U \ coordDiv S))
    (hpsh : IsPsh (U \ coordDiv S) u)
    (hg : ∀ z ∈ U \ coordDiv S, u z ≤ C * log (exp 1 + ∑ i ∈ S, log ‖z i‖⁻¹))
include hU hU1 hc hpsh hg
end partB
end
end ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
namespace ReciprocityTheory.AnForm.A
end ReciprocityTheory.AnForm.A


