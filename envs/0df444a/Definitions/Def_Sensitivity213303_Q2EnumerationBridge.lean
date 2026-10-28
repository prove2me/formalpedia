-- Prove2me | Definitions.Def_Sensitivity213303_Q2EnumerationBridge
-- name    : Sensitivity213303_Q2EnumerationBridge
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:20:17.832983+00:00
-- url     : https://prove2.me/theorems/cd48b5ab-6944-4485-9a79-46f9409106c4
-- title:
--   Encoding tournament orientations as a finite bit list
-- statement:
--   For each unordered pair of numbered vertices i<j, orientEdge returns (j,i) if the tournament has the reverse edge and (i,j) otherwise. orientationBits records those reverse-edge decisions in the fixed pair order. This representation connects an actual finite tournament to the executable enumeration; the accompanying proofs establish exact agreement of directed edges and degree counts.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module Q2EnumerationBridge; source SHA256 03a4fb36b007fff28d4e49eea18e6afba235c6589b867de536205b797b906503.

/-
Canonical numbering and actual tournament-degree bridge for the executable
q2 enumerator.  This connects combinatorial coverage to finite tournaments,
without replacing sensitivity charging by numerical assumptions.
-/
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_Q2CandidateTypes
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_TournamentHighRows
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith



set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundQ2
open scoped Classical BigOperators







def orientationBits {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R] : List Bool :=
  (edges n).map fun e => decide (R e.2 e.1)

def orientEdge {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (e : Fin n × Fin n) : Fin n × Fin n :=
  if R e.2 e.1 then e.swap else e





















end ThreeBoundQ2


