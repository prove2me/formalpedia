-- Prove2me | Definitions.Def_BKAR_OrderedForest
-- name    : BKAR_OrderedForest
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:26:36.468849+00:00
-- url     : https://prove2.me/theorems/baca2c6f-2323-56e9-a4b0-ee8f108baf08
-- title:
--   Ordered Forest
-- statement:
--   Definitions and structural lemmas for Ordered Forest, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean

import Definitions.Def_BKAR_OrderedExpansion
set_option autoImplicit false
namespace BKAR
namespace Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
inductive OrderedGrowth : Forest V → List (Edge V) → Forest V → Type _
  | nil (F : Forest V) : OrderedGrowth F [] F
  | cons {F F' G : Forest V} {e : Edge V} {order : List (Edge V)}
      (step : EdgeExtension F F' e)
      (tail : OrderedGrowth F' order G) :
      OrderedGrowth F (e :: order) G
namespace OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
structure ConsData (F : Forest V) (e : Edge V) (order : List (Edge V))
    (G : Forest V) where
  forest : Forest V
  step : EdgeExtension F forest e
  tail : OrderedGrowth forest order G
def consData (h : OrderedGrowth F (e :: order) G) :
    ConsData F e order G := by
  cases h with
  | cons step tail =>
      exact ⟨_, step, tail⟩
def tailForest (h : OrderedGrowth F (e :: order) G) : Forest V :=
  h.consData.forest
theorem firstStep (h : OrderedGrowth F (e :: order) G) :
    EdgeExtension F h.tailForest e :=
  h.consData.step
def tailGrowth (h : OrderedGrowth F (e :: order) G) :
    OrderedGrowth h.tailForest order G :=
  h.consData.tail
def firstActiveExtension (h : OrderedGrowth F (e :: order) G) :
    ActiveExtension F e :=
  ⟨h.tailForest, h.firstStep⟩
def support (_h : OrderedGrowth F order G) : ForestIndex V :=
  G.support
end OrderedGrowth
end Forest
end BKAR


