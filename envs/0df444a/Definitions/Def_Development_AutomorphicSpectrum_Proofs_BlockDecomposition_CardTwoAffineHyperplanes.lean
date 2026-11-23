-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardTwoAffineHyperplanes
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardTwoAffineHyperplanes
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:37.98851+00:00
-- url     : https://prove2.me/theorems/49e91333-093a-4468-8c18-3597ec4cb442
-- title:
--   Card Two Affine Hyperplanes
-- statement:
--   Definitions and structural lemmas for Card Two Affine Hyperplanes, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardTwoAffineHyperplanes.lean

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
namespace GlobalTheory.CompanionTheory.GapOpCount
noncomputable def pairMap {k : Type} [Field k] {n : ℕ} (a b : Fin (n + 1) → k) :
    (Fin (n + 1) → k) →ₗ[k] k × k where
  toFun x := (a ⬝ᵥ x, b ⬝ᵥ x)
  map_add' x y := by simp [dotProduct_add]
  map_smul' c x := by simp [dotProduct_smul]
end GlobalTheory.CompanionTheory.GapOpCount


