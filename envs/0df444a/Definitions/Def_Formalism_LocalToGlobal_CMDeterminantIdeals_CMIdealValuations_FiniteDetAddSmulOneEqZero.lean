-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_FiniteDetAddSmulOneEqZero
-- name    : Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_FiniteDetAddSmulOneEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:36:51.928878+00:00
-- url     : https://prove2.me/theorems/be123ecb-c234-4201-88bc-384c3bcbd004
-- title:
--   Finite Det Add Smul One Eq Zero
-- statement:
--   Definitions and structural lemmas for Finite Det Add Smul One Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/FiniteDetAddSmulOneEqZero.lean

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
namespace Formalism.L2.LamCM
def colE {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun k => M k i)
def matOf {B : Type} {m : B → ℕ} (x : FrVar m → ℂ) (b : B) : Matrix (Fin (m b)) (Fin (m b)) ℂ :=
  Matrix.of fun k i => x ⟨b, (i, k)⟩
end Formalism.L2.LamCM


