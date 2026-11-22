-- Prove2me | Definitions.Def_LeanPool_NemytskiiLebesgue_ConverseImplication
-- name    : LeanPool_NemytskiiLebesgue_ConverseImplication
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:33:54.979763+00:00
-- url     : https://prove2.me/theorems/ecd373e5-0c78-4e9c-8e76-07c1c911bbcb
-- title:
--   Converse Implication
-- statement:
--   Definitions and structural lemmas for Converse Implication, from Petr Girg; Petr Nečesal; Martin Dvořák; Jakub Psutka; LeanPool contributors's pinned Nemytskii operators on Lebesgue spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/ConverseImplication.lean

module
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable def denseSeqEucl (m : ℕ) : ℕ → ℝ^m :=
  fun n : ℕ => if n = 0 then 0 else denseSeq ℝ^m (n - 1)
noncomputable def growthSup {m k : ℕ} (f : ℝ → ℝ^m → ℝ^k) (r C : ℝ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ↱(‖f x (denseSeqEucl m n)‖ - C * ‖denseSeqEucl m n‖ ^ r)
noncomputable def growthWindowTerm
    {m k : ℕ} (f : ℝ → ℝ^m → ℝ^k)
    (C r : ℝ) (N n : ℕ) (x : ℝ) :
    ℝ≥0∞ :=
  ↱(‖f x (denseSeqEucl m n)‖ - C * ‖denseSeqEucl m n‖ ^ r) * (if ‖f x (denseSeqEucl m n)‖ ≤ (N : ℝ)
    then 1 else 0)
noncomputable def growthWindowSupr
    {m k : ℕ} (f : ℝ → ℝ^m → ℝ^k)
    (C r : ℝ) (N : ℕ) (x : ℝ) :
    ℝ≥0∞ :=
  ⨆ n : ℕ, growthWindowTerm f C r N n x
end NemytskiiLebesgue


