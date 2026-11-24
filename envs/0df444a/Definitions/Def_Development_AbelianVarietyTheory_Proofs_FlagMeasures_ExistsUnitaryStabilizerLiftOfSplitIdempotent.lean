-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsUnitaryStabilizerLiftOfSplitIdempotent
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsUnitaryStabilizerLiftOfSplitIdempotent
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T12:40:09.280032+00:00
-- url     : https://prove2.me/theorems/612e79c4-472a-4cd4-bb19-0cb9faf5a039
-- title:
--   Exists Unitary Stabilizer Lift Of Split Idempotent
-- statement:
--   Definitions and structural lemmas for Exists Unitary Stabilizer Lift Of Split Idempotent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsUnitaryStabilizerLiftOfSplitIdempotent.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
namespace GlobalTheory.SplitLift
open Formalism.UG
variable {A : Type} [CommRing A] {n : ℕ}
noncomputable def adj (s : A →+* A) (J Y : Matrix (Fin n) (Fin n) A) : Matrix (Fin n) (Fin n) A :=
  J⁻¹ * cT s Y * J
noncomputable def glue (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (e : A)
    (X X' : Matrix (Fin n) (Fin n) A) : Matrix (Fin n) (Fin n) A :=
  (1 - e - s e) • (1 : Matrix (Fin n) (Fin n) A) + X + adj s J X'
end GlobalTheory.SplitLift


