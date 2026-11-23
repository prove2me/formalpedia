-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsoOnG
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsoOnG
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:33.533821+00:00
-- url     : https://prove2.me/theorems/f6829485-a8d5-475a-80ba-afcbcf09199e
-- title:
--   Exists Iso On G
-- statement:
--   Definitions and structural lemmas for Exists Iso On G, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIsoOnG.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
namespace GlobalTheory.Ex.RecPeriods
section Transport
variable {O : Type} [CommRing O] {B B' : NumB O} (I : NumB.Iso B B')
end Transport
def powRep {O : Type} [CommRing O] (N : NumD O) (m : ℕ) (p : N.QT (m ^ 2)) (hp : p.1.1 = 1) : N.QT m :=
  ⟨(1, p.1.2 ^ m), by rw [NumD.mem_QT, ← pow_mul, ← sq, N.mem_QT.1 p.2, hp]⟩
section Match
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ} (μ : Match N N' n)
end Match
end GlobalTheory.Ex.RecPeriods
end


