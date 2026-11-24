-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T19:28:38.510147+00:00
-- url     : https://prove2.me/theorems/590b74ab-2e77-4d56-92f7-1d1db189d307
-- title:
--   Exists Unique Zpow Mul App LE
-- statement:
--   Definitions and structural lemmas for Exists Unique Zpow Mul App LE, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueZpowMulAppLE.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.PrimeSection
section Immersion
variable {X : Scheme.{u}} {t : Γ(X, ⊤)} {η : X}
  (hη : ∀ x : X, x ∉ X.basicOpen t ↔ η ⤳ x)
  (hp : ∀ U : X.Opens, IsAffineOpen U → η ∈ U →
    Prime (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
  [IsIntegral X] [IsLocallyNoetherian X]
  {Y : Scheme.{u}} {j : Y ⟶ X} [IsOpenImmersion j] (hj : j.opensRange = X.basicOpen t)
  {ι : Type v} {U : ι → X.Opens} {g : ∀ a b, Γ(X, U a ⊓ U b)}
  {W : ι → Y.Opens} (hW : ∀ a, W a = j ⁻¹ᵁ U a)
end Immersion
end GlobalTheory.PrimeSection


