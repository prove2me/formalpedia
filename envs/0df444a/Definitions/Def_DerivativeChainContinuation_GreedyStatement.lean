-- Prove2me | Definitions.Def_DerivativeChainContinuation_GreedyStatement
-- name    : DerivativeChainContinuation_GreedyStatement
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T20:13:40.166987+00:00
-- url     : https://prove2.me/theorems/195bbea1-45e4-471c-94ff-23617f9784cb
-- title:
--   The sorted source root tuple with multiplicity
-- statement:
--   For a nonempty real tuple a∈ℝ^(n+1), define orderedSource(a)=a∘Tuple.sort(a), using the sorting permutation of its labelled slots. Its first and last values are the minimum and maximum source roots. Repeated roots retain their multiplicities.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/GreedyStatement.lean, lines 7-8, SHA-256 b0b4225b71610ef2d6a2e072dc060bf94cb556fe8b6c938713302f20f8d9fac9.

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators

noncomputable def orderedSource {n : ℕ} (a : Fin (n+1) → ℝ) : Fin (n+1) → ℝ :=
  a ∘ Tuple.sort a























end DerivativeChainContinuation


