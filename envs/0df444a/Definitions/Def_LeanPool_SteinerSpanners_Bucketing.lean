-- Prove2me | Definitions.Def_LeanPool_SteinerSpanners_Bucketing
-- name    : LeanPool_SteinerSpanners_Bucketing
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:46:42.589002+00:00
-- url     : https://prove2.me/theorems/78cb0763-97f5-4a4b-955b-55980736448d
-- title:
--   Bucketing
-- statement:
--   Definitions and structural lemmas for Bucketing, from Goran Zuzic; David P. Woodruff; Vahab Mirrokni; LeanPool contributors's pinned Polynomial lower bounds for high-dimensional Steiner spanners development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Bucketing.lean

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
public import Definitions.Def_LeanPool_SteinerSpanners_Geometry
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped ENNReal
open HighDimSteinerSpanners
namespace HighDimSteinerSpanners.Proofs.Bucketing
def bucketingWalkInv {P I : Type} [MetricSpace P] (B : I → Finset P) :
    ∀ (u v : P ⊕ I), (bucketingGraph B).Walk u v → Prop
  | .inl x, .inl y, q => dist x y ≤ walkWeight (bucketingWeight B) q
  | .inr i, .inl y, q =>
      ∀ x ∈ B i, dist x y ≤ bucketDiam (B i) / 2 + walkWeight (bucketingWeight B) q
  | _, .inr _, _ => True
end HighDimSteinerSpanners.Proofs.Bucketing


