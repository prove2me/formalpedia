-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHFreeDecompSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHFreeDecompSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:02:15.55371+00:00
-- url     : https://prove2.me/theorems/811ba35e-ad77-40ad-b465-9f053b9c9878
-- title:
--   KHFree Decomp St
-- statement:
--   Definitions and structural lemmas for KHFree Decomp St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/KHFreeDecompSt.lean

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
def KHFreeDecomp.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (c d : K → ℤ) (n : ℕ),
    ∀ φ ∈ KH.cechCc ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c n,
      ∃ (A : Finset ((Σ k, ι k) → ℤ)) (f : ∀ a : (Σ k, ι k) → ℤ, CombC S (negSet a) n),
        (∀ a ∈ A, blockSum a = c + d) ∧ φ = ∑ a ∈ A, embed S a n (f a)
end
end GroundTheory.Heights₂.Heights.Kleiman


