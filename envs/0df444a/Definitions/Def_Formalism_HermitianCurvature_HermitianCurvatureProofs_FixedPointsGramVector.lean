-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedPointsGramVector
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedPointsGramVector
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T16:53:20.386893+00:00
-- url     : https://prove2.me/theorems/4a007aea-4ae4-4903-9273-92cbadd4dc2a
-- title:
--   Fixed Points Gram Vector
-- statement:
--   Definitions and structural lemmas for Fixed Points Gram Vector, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FixedPointsGramVector.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedFrameProperty
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P
namespace FixedPointsGramVector
open C2x5 C2x6 C2x7 HermitianProjections
variable {k r : ℕ}
def phiL (k r : ℕ) : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] (Fin (r + 1) → ℂ) where
  toFun y a := if h : a.val < r then y (eI k r ⟨a.val, h⟩) - y (esI k r ⟨a.val, h⟩) else y ⟨r + k, by omega⟩
  map_add' y y' := by
    funext a; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c y := by
    funext a; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring
end FixedPointsGramVector
open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector
end Formalism.FourierDecayAlt.P


