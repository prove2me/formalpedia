-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteDimensionalIsoPartOfSimple
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteDimensionalIsoPartOfSimple
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:35.210823+00:00
-- url     : https://prove2.me/theorems/a2cde8e7-8132-435c-9399-0a7b002cc3b5
-- title:
--   Finite Dimensional Iso Part Of Simple
-- statement:
--   Definitions and structural lemmas for Finite Dimensional Iso Part Of Simple, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteDimensionalIsoPartOfSimple.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
namespace GlobalTheory.CompanionTheory.AdmGL
variable {K : Type} [Group K] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def isoPart (π : K →* (H →L[ℂ] H)) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ K W) :
    Submodule ℂ H :=
  ⨆ (T : W →ₗ[ℂ] H) (_ : ∀ k w, T (ρ k w) = π k (T w)), LinearMap.range T
variable [CompleteSpace H]
end GlobalTheory.CompanionTheory.AdmGL
end


