-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChainIndependence
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChainIndependence
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:50.44402+00:00
-- url     : https://prove2.me/theorems/06a7fd13-acf4-4a2f-ac06-56d8549bd88b
-- title:
--   Chain Independence
-- statement:
--   Definitions and structural lemmas for Chain Independence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChainIndependence.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RootExchangeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
namespace GlobalTheory.CompanionTheory.TyFin
def chainUnion (m k t : ℕ) : Fin m ⊕ Fin k → Fin m ⊕ Fin k → Prop
  | .inl a, .inl a' => a < a'
  | .inr w, .inr w' => w < w'
  | .inl a, .inr _ => (a : ℕ) ≤ t
  | .inr _, .inl a => t + 1 ≤ (a : ℕ)
end GlobalTheory.CompanionTheory.TyFin


