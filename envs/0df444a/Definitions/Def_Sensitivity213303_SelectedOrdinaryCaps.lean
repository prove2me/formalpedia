-- Prove2me | Definitions.Def_Sensitivity213303_SelectedOrdinaryCaps
-- name    : Sensitivity213303_SelectedOrdinaryCaps
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:28:58.171169+00:00
-- url     : https://prove2.me/theorems/627306ee-ec78-4493-836d-bac89f4c862a
-- title:
--   The selected tournament and labeling in the ordinary-parent interface
-- statement:
--   This package exposes the already selected Fin 10007 tournament as the ordinary construction’s Tournament structure and its selected binary edge labels as Fin 2 values. The structure’s looplessness and orientation laws are supplied by the proved Paley geometry. It allows the ordinary-parent transfer theorems to use exactly the same tournament and labeling as the graded construction.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module SelectedOrdinaryCaps; source SHA256 1d1b46624051ea67fc1d5721f3eaf017c56d15c2b6547308a093bf5b6a3ace15.

/- Instantiate every ordinary transfer exclusion with the proved Paley-10007 label. -/
import Definitions.Def_Sensitivity213303_ArchivedOrdinaryDefinitions
import Definitions.Def_Sensitivity213303_LabelCard
import Definitions.Def_Sensitivity213303_LabelDefinitions
import Definitions.Def_Sensitivity213303_LabelExists
import Definitions.Def_Sensitivity213303_LabelLoads
import Definitions.Def_Sensitivity213303_LabelMarked
import Definitions.Def_Sensitivity213303_LabelOrdinary
import Definitions.Def_Sensitivity213303_Paley10007
import Definitions.Def_Sensitivity213303_Selected10007
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
namespace ThreeBoundOrdinaryArchive
end ThreeBoundOrdinaryArchive


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace ThreeBoundOrdinarySelected
open scoped Classical
noncomputable section
open ThreeBoundOrdinaryArchive

abbrev Adj := Sensitivity10007Labeling.Labeling10007.Adj

def tournament : ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament 10007 where
  Adj := Adj
  loopless := Sensitivity10007Labeling.Labeling10007.irreflexive
  edge_compl := fun {i j} h => Sensitivity10007Labeling.Labeling10007.edge_compl i j h

def label (v w : Fin 10007) : Fin 2 :=
  Sensitivity10007Labeling.Labeling10007.selectedLabel (v,w)





end
end ThreeBoundOrdinarySelected


