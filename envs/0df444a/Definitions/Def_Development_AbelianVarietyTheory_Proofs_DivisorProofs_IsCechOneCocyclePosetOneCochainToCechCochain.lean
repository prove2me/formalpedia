-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCechOneCocyclePosetOneCochainToCechCochain
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCechOneCocyclePosetOneCochainToCechCochain
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T15:25:43.979424+00:00
-- url     : https://prove2.me/theorems/3853e070-cb3a-4cb4-8e5e-b3b6efee60d0
-- title:
--   Is Cech One Cocycle Poset One Cochain To Cech Cochain
-- statement:
--   Definitions and structural lemmas for Is Cech One Cocycle Poset One Cochain To Cech Cochain, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsCechOneCocyclePosetOneCochainToCechCochain.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RestrictCapFBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CechCmp
variable {I : Type} [Finite I] {X : Scheme.{0}} {R : Type} [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W))
end GlobalTheory.CechCmp


