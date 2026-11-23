-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriBlockUpperLeviLower
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriBlockUpperLeviLower
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:32.554098+00:00
-- url     : https://prove2.me/theorems/da5473c0-9762-4108-a89e-beac0817240b
-- title:
--   Iwahori Block Upper Levi Lower
-- statement:
--   Definitions and structural lemmas for Iwahori Block Upper Levi Lower, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriBlockUpperLeviLower.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUdlOfIsUnit
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsPrincipalCongruence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
namespace GlobalTheory.CompanionTheory.BlockIwahoriUML
variable {k Γ : Type*} [Field k] [LinearOrderedCommGroupWithZero Γ]
def Cong (v : Valuation k Γ) (r : Γ) {n : ℕ} (A : Matrix (Fin n) (Fin n) k) : Prop :=
  ∀ i j, v (A i j - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ r
end GlobalTheory.CompanionTheory.BlockIwahoriUML


