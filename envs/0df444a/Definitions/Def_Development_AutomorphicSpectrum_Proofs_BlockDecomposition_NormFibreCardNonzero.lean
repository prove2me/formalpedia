-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardNonzero
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardNonzero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:16.513015+00:00
-- url     : https://prove2.me/theorems/e8bfe955-09bf-45d1-bcb7-d838dd5c4361
-- title:
--   Norm Fibre Card Nonzero
-- statement:
--   Definitions and structural lemmas for Norm Fibre Card Nonzero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormFibreCardNonzero.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
namespace GlobalTheory.CompanionTheory.UnrDens.NormUnit
variable {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}
def tauU (τ : E →+* E) : Eˣ →* Eˣ := Units.map (τ : E →* E)
def ratioU (τ : E →+* E) : Eˣ →* Eˣ := MonoidHom.id _ / tauU τ
def normU (τ : E →+* E) : Eˣ →* Eˣ := MonoidHom.id _ * tauU τ
end GlobalTheory.CompanionTheory.UnrDens.NormUnit


