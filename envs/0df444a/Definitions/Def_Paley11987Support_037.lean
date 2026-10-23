-- Prove2me | Definitions.Def_Paley11987Support_037
-- name    : Paley11987Support_037
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-23T01:51:10.086178+00:00
-- url     : https://prove2.me/theorems/dd48a18b-eeff-4368-96a5-b64e4cbb2779
-- title:
--   Valid recipes and actual stage families
-- statement:
--   Defines recipe validity, target and guard indices, tolerances, and the actual tolerant Boolean family produced by a stage.
--
--   **Formalization Note.** This is the definition interface for the supplied proof module BooleanTransferRawInputs.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module BooleanTransferRawInputs, SHA256 f883c6416f355db69b5cfa557f64f47987a3f59baafffb4403af10405c1843be

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

set_option autoImplicit false
set_option Elab.async false
section z57

set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 ZT
open CompactFiniteProfileClosures
namespace ZP
variable {I : Type} [Fintype I]









structure RecipeValid (r : Recipe) : Prop where
  target_lt : ∀ i : Fin 20, (r[i.val]?.getD default).target < 20
  guard_lt : ∀ i : Fin 20, (r[i.val]?.getD default).guard < 20
  guard_target : ∀ i : Fin 20, (r[i.val]?.getD default).guard ≤ (r[i.val]?.getD default).target
  target_mono : ∀ i j : Fin 20, i ≤ j →
    (r[i.val]?.getD default).target ≤ (r[j.val]?.getD default).target
  guard_antitone : ∀ i j : Fin 20, i ≤ j →
    (r[j.val]?.getD default).guard ≤ (r[i.val]?.getD default).guard
  tol_antitone : ∀ i j : Fin 20, i ≤ j →
    (r[j.val]?.getD default).tol ≤ (r[i.val]?.getD default).tol
  tol_le : ∀ i : Fin 20, (r[i.val]?.getD default).tol ≤ 8

def targetIndex (r : Recipe) (hr : RecipeValid r) (i : Fin 20) : Fin 20 :=
  ⟨(r[i.val]?.getD default).target,hr.target_lt i⟩
def guardIndex (r : Recipe) (hr : RecipeValid r) (i : Fin 20) : Fin 20 :=
  ⟨(r[i.val]?.getD default).guard,hr.guard_lt i⟩
def tolerance (r : Recipe) (i : Fin 20) : ℕ := (r[i.val]?.getD default).tol

def stageFamily {k : ℕ} (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin 20 → (I → Bool) → Bool) (r : Recipe) (hr : RecipeValid r) :
    Fin 20 → (((Fin k × Fin 2) × I) → Bool) → Bool :=
  fun i => tolerantFamily T label F (targetIndex r hr i) (guardIndex r hr i) (tolerance r i)



end ZP
end
end z57


