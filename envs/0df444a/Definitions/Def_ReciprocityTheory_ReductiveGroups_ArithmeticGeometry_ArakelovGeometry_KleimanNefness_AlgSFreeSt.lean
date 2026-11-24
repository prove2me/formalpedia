-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgSFreeSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgSFreeSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:41:29.426066+00:00
-- url     : https://prove2.me/theorems/3a5393e9-c410-4083-80cf-098c9767d57e
-- title:
--   Alg SFree St
-- statement:
--   Definitions and structural lemmas for Alg SFree St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/KleimanNefness/AlgSFreeSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AmpleSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
def TheoremSFreeStatement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (d : K → ℤ),
    (∀ (c : K → ℤ) (n : ℕ),
      Module.Finite S (cechHc ι (fun c => quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c n)) ∧
    (∀ (c : K → ℤ) (n : ℕ), 1 ≤ n → (∀ k, 0 ≤ c k + d k) →
      Subsingleton (cechHc ι (fun c => quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c n)) ∧
    (∀ c : K → ℤ, (∀ k, 0 ≤ c k + d k) →
      ∀ z ∈ cechZc ι (fun c => quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c 0,
        ∃ m ∈ quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d), ∀ I, z I = LocalizedModule.mk m 1)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH


