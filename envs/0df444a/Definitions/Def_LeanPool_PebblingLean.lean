-- Prove2me | Definitions.Def_LeanPool_PebblingLean
-- name    : LeanPool_PebblingLean
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T06:14:21.212673+00:00
-- url     : https://prove2.me/theorems/942798f3-8faf-4d5d-92ad-20fb578d7836
-- title:
--   Pebbling Lean
-- statement:
--   Definitions and structural lemmas for Pebbling Lean, from Lior Pachter; LeanPool contributors's pinned Optimal Pebbling Number of the Hypercube development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean.lean

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Definitions.Def_LeanPool_PebblingLean_Hypercube
public import Definitions.Def_LeanPool_PebblingLean_Weight
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Definitions.Def_LeanPool_PebblingLean_FiniteProbability
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_Delivery
public import Definitions.Def_LeanPool_PebblingLean_GraphIso
public import Definitions.Def_LeanPool_PebblingLean_HypercubePath
public import Definitions.Def_LeanPool_PebblingLean_HypercubeProduct
public import Definitions.Def_LeanPool_PebblingLean_Product
public import Definitions.Def_LeanPool_PebblingLean_UpperBound
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundRecurrence
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Definitions.Def_LeanPool_PebblingLean_Paper
public import Definitions.Def_LeanPool_PebblingLean_Examples
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
set_option autoImplicit true
@[expose] public section
@[expose] public section


