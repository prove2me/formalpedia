-- Prove2me | Definitions.Def_Sendov_FiniteRange_Recurrence
-- name    : Sendov_FiniteRange_Recurrence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T17:57:13.612535+00:00
-- url     : https://prove2.me/theorems/e9ce1240-e2e6-4649-b2d8-ea0675eabb52
-- title:
--   Recurrence
-- statement:
--   Definitions and structural lemmas for Recurrence, from Terence Tao (teorth/sendov; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sendov's conjecture and the Phelps-Rodriguez conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Recurrence.lean

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option autoImplicit false
namespace Sendov
open MeasureTheory
def pev : List ℤ → ℝ → ℝ
  | [], _ => 0
  | a :: p, x => (a : ℝ) + x * pev p x
def padd : List ℤ → List ℤ → List ℤ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: padd p q
def pmul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: p, q => padd (q.map (fun b => a * b)) (0 :: pmul p q)
def rev : List (List ℤ) → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | p :: r, α, t => pev p α + t * rev r α t
def radd : List (List ℤ) → List (List ℤ) → List (List ℤ)
  | [], s => s
  | p :: r, [] => p :: r
  | p :: r, q :: s => padd p q :: radd r s
def rscale (g : List ℤ) (r : List (List ℤ)) : List (List ℤ) := r.map (pmul g)
def qstep (g₀ g₁ g₂ : List ℤ) (r : List (List ℤ)) : List (List ℤ) :=
  radd (rscale g₀ r) (radd ([] :: rscale g₁ r) ([] :: [] :: rscale g₂ r))
def qrow (g₀ g₁ g₂ : List ℤ) : ℕ → List (List ℤ)
  | 0 => [[1]]
  | k + 1 => qstep g₀ g₁ g₂ (qrow g₀ g₁ g₂ k)
noncomputable def irow : List (List ℤ) → ℕ → ℝ → ℝ
  | [], _, _ => 0
  | p :: r, i, α => pev p α / (i + 4) + irow r (i + 1) α
def gg0 (n : ℕ) : List ℤ := [6 * ((n : ℤ) - 1), 2 * ((n : ℤ) - 1)]
def gg1 (n : ℕ) : List ℤ := [-12 * ((n : ℤ) - 1), 12 - 2 * ((n : ℤ) - 1), 4]
def gg2 (n : ℕ) : List ℤ := [6 * ((n : ℤ) - 1), 2 * ((n : ℤ) - 1) - 12, -4]
end Sendov


