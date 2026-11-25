-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardTorsionMulFinrank
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardTorsionMulFinrank
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T02:01:25.129362+00:00
-- url     : https://prove2.me/theorems/e28002ef-e9b5-488b-a669-aa65ef01a56a
-- title:
--   Card Torsion Mul Finrank
-- statement:
--   Definitions and structural lemmas for Card Torsion Mul Finrank, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardTorsionMulFinrank.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCosetRepresentativesOfFiniteSubgroupPadicI
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ChiOntoOfUnramified
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
namespace GlobalTheory.TorsionCard
variable {l : ℕ} [hl : Fact l.Prime]
noncomputable def red (l : ℕ) [Fact l.Prime] : ℤ_[l]ˣ →* (ZMod l)ˣ :=
  Units.map (PadicInt.toZMod (p := l) : ℤ_[l] →+* ZMod l).toMonoidHom
end GlobalTheory.TorsionCard


