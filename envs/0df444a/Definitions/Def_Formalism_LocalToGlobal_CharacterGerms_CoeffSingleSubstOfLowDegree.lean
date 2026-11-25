-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
-- name    : Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:47:42.643225+00:00
-- url     : https://prove2.me/theorems/21d392b3-63db-40cc-932d-7ee4091324db
-- title:
--   Coeff Single Subst Of Low Degree
-- statement:
--   Definitions and structural lemmas for Coeff Single Subst Of Low Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffSingleSubstOfLowDegree.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AbstractGermZeroCondition
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
namespace FormalGermZero
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
section Law
variable {dd : ℕ}
def addS {σ : Type} (F : Fin dd → PS C 2 dd) (a b : Fin dd → MvPowerSeries σ C) : Fin dd → MvPowerSeries σ C :=
  fun j => MvPowerSeries.subst (fun q : Fin 2 × Fin dd => ![a, b] q.1 q.2) (F j)
def gsum {σ ι : Type} (F : Fin dd → PS C 2 dd) (Γ : ι → Fin dd → MvPowerSeries σ C) :
    List ι → Fin dd → MvPowerSeries σ C
  | [] => 0
  | c :: l => addS F (Γ c) (gsum F Γ l)
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O]
end Law
section Sys1
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I : Fin 2 → Type}
  [∀ g, Fintype (I g)]
end Sys1
end FormalGermZero
end Formalism.L2.FormalSeriesBounds


