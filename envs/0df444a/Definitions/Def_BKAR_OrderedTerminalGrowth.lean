-- Prove2me | Definitions.Def_BKAR_OrderedTerminalGrowth
-- name    : BKAR_OrderedTerminalGrowth
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:41:57.486259+00:00
-- url     : https://prove2.me/theorems/6b2cbda8-b456-44c1-b977-ce285f1c4ef7
-- title:
--   Ordered Terminal Growth
-- statement:
--   Definitions and structural lemmas for Ordered Terminal Growth, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean

import Definitions.Def_BKAR_OrderedRemainder
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
namespace BKAR
namespace Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
structure TerminalGrowth (F : Forest V) where
  order : List (Edge V)
  terminal : Forest V
  growth : OrderedGrowth F order terminal
  terminal_activeEdges_eq_empty : terminal.activeEdges = ∅
namespace TerminalGrowth
variable {F : Forest V}
def branchIntegralAux (data : TerminalGrowth F) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  data.growth.branchIntegralAux top u ρ
def branchIntegral (data : TerminalGrowth F)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  data.branchIntegralAux 1 u ρ
def ofActiveEdgesEqEmpty (F : Forest V) (hF : F.activeEdges = ∅) :
    TerminalGrowth F where
  order := []
  terminal := F
  growth := OrderedGrowth.nil F
  terminal_activeEdges_eq_empty := hF
def cons {e : Edge V} (h : ActiveExtension F e)
    (tail : TerminalGrowth h.forest) : TerminalGrowth F where
  order := e :: tail.order
  terminal := tail.terminal
  growth := h.consGrowth tail.growth
  terminal_activeEdges_eq_empty := tail.terminal_activeEdges_eq_empty
def support (data : TerminalGrowth F) : ForestIndex V :=
  data.terminal.support
end TerminalGrowth
structure ActiveTerminalBranchData (F : Forest V) where
  extension : ∀ e : {e // e ∈ F.activeEdges}, ActiveExtension F e.val
  tail :
    ∀ e : {e // e ∈ F.activeEdges},
      TerminalGrowth (extension e).forest
namespace ActiveTerminalBranchData
variable {F : Forest V}
def branchData (data : ActiveTerminalBranchData F) : ActiveBranchData F where
  extension := data.extension
  order := fun e => (data.tail e).order
  terminal := fun e => (data.tail e).terminal
  tail := fun e => (data.tail e).growth
def growth (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges}) : TerminalGrowth F :=
  TerminalGrowth.cons (data.extension e) (data.tail e)
def branchIntegralAux (data : ActiveTerminalBranchData F) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  data.branchData.branchIntegralAux top u ρ
def branchIntegral (data : ActiveTerminalBranchData F)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  data.branchIntegralAux 1 u ρ
def singleton
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (extensions e).forest.activeEdges = ∅) :
    ActiveTerminalBranchData F where
  extension := extensions
  tail := fun e => TerminalGrowth.ofActiveEdgesEqEmpty
    (extensions e).forest (hterm e)
end ActiveTerminalBranchData
end Forest
end BKAR


