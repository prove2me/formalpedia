-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InSupportOfIsSubquotient
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_InSupportOfIsSubquotient
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T22:00:08.554604+00:00
-- url     : https://prove2.me/theorems/af65c06c-cc90-4e0c-9c3a-ce26ac949337
-- title:
--   In Support Of Is Subquotient
-- statement:
--   Definitions and structural lemmas for In Support Of Is Subquotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/InSupportOfIsSubquotient.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviEmbMulSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)
namespace GlobalTheory.JacquetExact
section Abstract
variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable [TopologicalSpace G] [IsTopologicalGroup G]
end Abstract
section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {V W : Type} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] {s : ℕ} {d : Fin s → ℕ}
end Local
end GlobalTheory.JacquetExact


