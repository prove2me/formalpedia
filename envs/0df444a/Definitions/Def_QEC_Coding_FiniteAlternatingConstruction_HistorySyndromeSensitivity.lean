-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
-- name    : QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T10:53:56.17386+00:00
-- url     : https://prove2.me/theorems/bc832833-afc0-4d9a-8d90-42fb06fe613b
-- title:
--   History Syndrome Sensitivity
-- statement:
--   Definitions and structural lemmas for History Syndrome Sensitivity, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Preimages
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26RXCoarseInfluence BDL26RXInfluenceBounds MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (d : Nat) (i : StepIndex d)
def differentialInfluence (e : (indexedFamily S d).Cochain1 i.succ) :
    Finset (FamilyZ S d i.succ) :=
  (hammingSupport e).biUnion (fun q => hammingSupport (basisSyndrome S d i q))
variable (n : Nat)
def perturbTop (sigma : TopInput S n)
    (e : (indexedFamily S (n+2)).Cochain1 (TopIndex (n+2))) : TopInput S n :=
  ⟨sigma.val + (indexedFamily S (n+2)).coboundary1 (TopIndex (n+2)) e, by
    obtain ⟨a,ha⟩ := sigma.property
    exact ⟨a+e,by rw [map_add,ha]⟩⟩
end QEC.Coding.BDL26HistorySyndromeSensitivity


