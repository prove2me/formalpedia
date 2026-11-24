-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHFreeIndepSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHFreeIndepSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:28.887484+00:00
-- url     : https://prove2.me/theorems/9599196d-a39f-460e-aa12-5b6e7f2fb4ea
-- title:
--   KHFree Indep St
-- statement:
--   Definitions and structural lemmas for KHFree Indep St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/KHFreeIndepSt.lean

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
def KHFreeIndep.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (n : ℕ) (A : Finset ((Σ k, ι k) → ℤ))
    (f : ∀ a : (Σ k, ι k) → ℤ, CombC S (negSet a) n),
    ∑ a ∈ A, embed S a n (f a) = 0 → ∀ a ∈ A, f a = 0
end
end GroundTheory.Heights₂.Heights.Kleiman


