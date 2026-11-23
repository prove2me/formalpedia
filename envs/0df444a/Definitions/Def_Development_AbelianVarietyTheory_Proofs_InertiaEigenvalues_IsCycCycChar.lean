-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCycCycChar
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCycCycChar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:04:06.023121+00:00
-- url     : https://prove2.me/theorems/0c0a12af-5f52-4bec-a351-2eedbffe3a1d
-- title:
--   Is Cyc Cyc Char
-- statement:
--   Definitions and structural lemmas for Is Cyc Cyc Char, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCycCycChar.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
namespace GlobalTheory.Cyc
noncomputable def cycChar (l : ℕ) [Fact l.Prime] : GQ l →* ℚ_[l]ˣ :=
  (Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom).comp
    ((cyclotomicCharacter (Om l) l).comp (MulSemiringAction.toRingAut (GQ l) (Om l)))
end GlobalTheory.Cyc


