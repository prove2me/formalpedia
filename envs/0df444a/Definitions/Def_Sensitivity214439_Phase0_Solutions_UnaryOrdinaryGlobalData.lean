-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryOrdinaryGlobalData
-- name    : Sensitivity214439_Phase0_Solutions_UnaryOrdinaryGlobalData
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:08:09.217743+00:00
-- url     : https://prove2.me/theorems/e591d6a3-66b4-4418-9505-1fb9c84528a1
-- title:
--   Literal ordinary prices for phase zero
-- statement:
--   A fixed five-component natural-number price vector is assigned to ordinary phase-zero global gains. Its components price low rows, high target rows, marked target rows, external donors, and internal guard-head donors.
--
--   The exact integers are given in the formal record. They are compared with the child $A$, $B$, and $M$ entries by the price-validity theorem and combined with finite tournament population states by the ordinary global certificates.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/UnaryOrdinaryGlobalData.lean lines 6–12; SHA256 9745f55c3f13733906a2eae91c9030cd751cef0c7a5280d028afdb692a3a5b0d; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryOrdinaryGlobalNumeric
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.Range
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic

namespace SensitivityUnaryOrdinaryGlobalNumeric
end SensitivityUnaryOrdinaryGlobalNumeric



namespace SensitivityUnaryOrdinaryGlobalNumeric

def phase0Prices : Prices := {
  low := 181242075225657368948446485601435867152384,
  high := 415151148012507677458048106823024218891878400,
  marked := 21953295136055653884930920015726208883942752256,
  external := 21953113893980428227561971569240607448075599872,
  internal := 126093833950562780592225451649200678135398400
}




end SensitivityUnaryOrdinaryGlobalNumeric


