-- Prove2me | Definitions.Def_BKAR_OrderedSimplex
-- name    : BKAR_OrderedSimplex
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:27:18.492118+00:00
-- url     : https://prove2.me/theorems/d6339be8-2694-47a3-add9-f147ecacf893
-- title:
--   Ordered Simplex
-- statement:
--   Definitions and structural lemmas for Ordered Simplex, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean

import Definitions.Def_BKAR_OrderedForest
set_option autoImplicit false
noncomputable section
namespace BKAR
variable {V : Type*} [DecidableEq V]
def orderedSimplexIntegralAux (top : ℝ) :
    List (Edge V) → (List ℝ → ℝ) → ℝ
  | [], f => f []
  | _ :: order, f =>
      ∫ t in 0..top,
        orderedSimplexIntegralAux t order (fun ts => f (t :: ts))
def orderedSimplexIntegral (order : List (Edge V)) (f : List ℝ → ℝ) : ℝ :=
  orderedSimplexIntegralAux 1 order f
def OrderedSimplexParams : ℝ → List ℝ → Prop
  | _, [] => True
  | top, t :: ts => 0 ≤ t ∧ t ≤ top ∧ OrderedSimplexParams t ts
namespace OrderedSimplexParams
end OrderedSimplexParams
end BKAR


