-- Prove2me | Definitions.Def_Research_Basic
-- name    : Research_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T17:33:59.384238+00:00
-- url     : https://prove2.me/theorems/5b7733a8-08a3-42fe-a1ce-3e783b2651b7
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Colin Snyder / Star Fleet Math; AItoBit (AItoBit/erdos-662-proof; see pinned Apache-2.0 LICENSE and NOTICE)'s pinned Erdos 662: corrected global threshold conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/Basic.lean

module
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Prod.Lex
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Research
def sqDist (p q : ℝ × ℝ) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2
def OneSeparated {n : ℕ} (x : Fin n → ℝ × ℝ) : Prop :=
  ∀ i j, i ≠ j → 1 ≤ sqDist (x i) (x j)
noncomputable def shortPairsAtOne {n : ℕ} (x : Fin n → ℝ × ℝ) :
    Finset (Fin n × Fin n) :=
  ((Finset.univ : Finset (Fin n)).product Finset.univ).filter
    (fun ij => ij.1.val < ij.2.val ∧ sqDist (x ij.1) (x ij.2) ≤ 1)
def LiteralClaimAtOne : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ x : Fin n → ℝ × ℝ,
    OneSeparated x → (shortPairsAtOne x).card ≤ 6
end Research


