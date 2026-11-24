-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHFreeBadFiniteSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHFreeBadFiniteSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:18.963348+00:00
-- url     : https://prove2.me/theorems/08a75308-bc71-47f4-9b7f-5c8826c755ce
-- title:
--   KHFree Bad Finite St
-- statement:
--   Definitions and structural lemmas for KHFree Bad Finite St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/KHFreeBadFiniteSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHFreeObj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree
noncomputable section
def KHFreeBadFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (e : K → ℤ),
    {a : (Σ k, ι k) → ℤ | blockSum a = e ∧ ∀ k, negSet a k = ∅ ∨ negSet a k = Finset.univ}.Finite
end
end GroundTheory.Heights₂.Heights.Kleiman


