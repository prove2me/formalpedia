-- Prove2me | Definitions.Def_Paley11987Support_053
-- name    : Paley11987Support_053
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-23T03:30:49.613986+00:00
-- url     : https://prove2.me/theorems/804c3497-f28b-4308-bfe8-c94213366ae7
-- title:
--   Reindexing finite Boolean families
-- statement:
--   Defines reindexing of Boolean families and block witnesses along equivalences, with the structural flip compatibility needed for transport.
--
--   **Formalization Note.** This is the definition interface for the supplied proof module FiniteProfileSeedTransport.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module FiniteProfileSeedTransport, SHA256 c2bc31e2deb00a5394527957fa211de0ebc13f252f62aeae287f6225ba446e45

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Paley11987Support_000
import Definitions.Def_Paley11987Support_001
import Definitions.Def_Paley11987Support_002
import Definitions.Def_Paley11987Support_003
import Definitions.Def_Paley11987Support_004
import Definitions.Def_Paley11987Support_005
import Definitions.Def_Paley11987Support_006
import Definitions.Def_Paley11987Support_007
import Definitions.Def_Paley11987Support_008
import Definitions.Def_Paley11987Support_009
import Definitions.Def_Paley11987Support_010
import Definitions.Def_Paley11987Support_011
import Definitions.Def_Paley11987Support_012
import Definitions.Def_Paley11987Support_013
import Definitions.Def_Paley11987Support_014
import Definitions.Def_Paley11987Support_015
import Definitions.Def_Paley11987Support_016
import Definitions.Def_Paley11987Support_017
import Definitions.Def_Paley11987Support_018
import Definitions.Def_Paley11987Support_019
import Definitions.Def_Paley11987Support_020
import Definitions.Def_Paley11987Support_021
import Definitions.Def_Paley11987Support_022
import Definitions.Def_Paley11987Support_023
import Definitions.Def_Paley11987Support_024
import Definitions.Def_Paley11987Support_025
import Definitions.Def_Paley11987Support_026
import Definitions.Def_Paley11987Support_027
import Definitions.Def_Paley11987Support_028
import Definitions.Def_Paley11987Support_029
import Definitions.Def_Paley11987Support_030
import Definitions.Def_Paley11987Support_031
import Definitions.Def_Paley11987Support_032
import Definitions.Def_Paley11987Support_033
import Definitions.Def_Paley11987Support_034
import Definitions.Def_Paley11987Support_035
import Definitions.Def_Paley11987Support_036
import Definitions.Def_Paley11987Support_037
import Definitions.Def_Paley11987Support_038
import Definitions.Def_Paley11987Support_039
import Definitions.Def_Paley11987Support_040
import Definitions.Def_Paley11987Support_041
import Definitions.Def_Paley11987Support_042
import Definitions.Def_Paley11987Support_043
import Definitions.Def_Paley11987Support_044
import Definitions.Def_Paley11987Support_045
import Definitions.Def_Paley11987Support_046
import Definitions.Def_Paley11987Support_047
import Definitions.Def_Paley11987Support_048
import Definitions.Def_Paley11987Support_049
import Definitions.Def_Paley11987Support_050
import Definitions.Def_Paley11987Support_051
import Definitions.Def_Paley11987Support_052

set_option autoImplicit false
set_option Elab.async false
section z81

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical
open OAI.Paper320
namespace CompactFiniteProfileSeeds
variable {I J : Type}

def reindex (e : I ≃ J) (f : (I → Bool) → Bool) : (J → Bool) → Bool :=
  fun x => f (fun i => x (e i))

theorem flip_reindex (e : I ≃ J) (x : J → Bool) (B : Finset I) :
    (fun i => OAI.Paper320.flip x (B.map e.toEmbedding) (e i)) =
      OAI.Paper320.flip (fun i => x (e i)) B := by
  funext i
  simp [OAI.Paper320.flip]





section Finite
variable [Fintype I] [Fintype J]





end Finite

def Blocks.reindex {h : ℕ} {F : Fin h → (I → Bool) → Bool} {n : ℕ}
    (w : Blocks F n) (e : I ≃ J) : Blocks (fun q => reindex e (F q)) n where
  zero q := w.zero q
  sets i := (w.sets i).map e.toEmbedding
  nonempty i := (w.nonempty i).map (f := e.toEmbedding)
  disjoint i j hij := (Finset.disjoint_map e.toEmbedding).mpr (w.disjoint hij)
  on q i := by
    change F q (fun a => OAI.Paper320.flip (fun _ => false)
      ((w.sets i).map e.toEmbedding) (e a)) = true
    rw [flip_reindex]
    exact w.on q i

end CompactFiniteProfileSeeds
end
end z81


