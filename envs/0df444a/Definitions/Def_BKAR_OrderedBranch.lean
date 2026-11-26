-- Prove2me | Definitions.Def_BKAR_OrderedBranch
-- name    : BKAR_OrderedBranch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:31:22.862552+00:00
-- url     : https://prove2.me/theorems/eaddb3fd-cbb9-4657-b6ff-5189bd87a7b1
-- title:
--   Ordered Branch
-- statement:
--   Definitions and structural lemmas for Ordered Branch, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean

import Definitions.Def_BKAR_OrderedParams
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
namespace BKAR
namespace Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
def derivativeOrder (_h : OrderedGrowth F order G) : List (Edge V) :=
  order.reverse
def branchPoint (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) (ts : List ℝ) : Edge V → ℝ :=
  G.standardInterp (h.params u ts)
def branchIntegrand (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    List ℝ → ℝ :=
  fun ts => mixedPartialList h.derivativeOrder ρ (h.branchPoint u ts)
def branchIntegralAux (top : ℝ) (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  orderedSimplexIntegralAux top order (h.branchIntegrand u ρ)
def branchIntegral (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  h.branchIntegralAux 1 u ρ
end OrderedGrowth
end Forest
end BKAR


