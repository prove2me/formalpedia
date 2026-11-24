-- Prove2me | Definitions.Def_proofs_PhosphorylationSharpness_Recurrence
-- name    : proofs_PhosphorylationSharpness_Recurrence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T07:19:10.346706+00:00
-- url     : https://prove2.me/theorems/7cec53ff-d080-4af4-86b0-befae06acda7
-- title:
--   Recurrence
-- statement:
--   Definitions and structural lemmas for Recurrence, from mmislan (mmislan/palomar-p080-phosphorylation-attainment; see pinned Apache-2.0 LICENSE)'s pinned Sharp lower bound on positive equilibria in sequential distributive phosphorylation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mmislan/palomar-p080-phosphorylation-attainment/blob/44cb5b18313448ede0f9e0df869c538602ffc66d/proofs/PhosphorylationSharpness/Recurrence.lean

import Mathlib
set_option autoImplicit true
namespace PhosphorylationSharpness
noncomputable section
open Polynomial
def DensePositive (p : ℝ[X]) (m : ℕ) : Prop :=
  (∀ i ≤ m, 0 < p.coeff i) ∧ (∀ i, m < i → p.coeff i = 0)
def nextN (a b : ℝ) (p q : ℝ[X]) : ℝ[X] :=
  C ((a+1)*(b+1))*p + C 8*(X*p) + C (2*(a+b))*q
def nextJ (a b : ℝ) (p q : ℝ[X]) : ℝ[X] :=
  C ((a-1)*(b-1))*q + C 8*(X*q) + C (4*(a+b))*(X*p)
def ratio (x : ℝ) : ℝ := (x^2-1)/8
def pair : ℕ → ℝ[X] × ℝ[X]
  | 0 => (1, C (1/2))
  | m+1 =>
    let pq := pair m
    (nextN (2*m+3) (2*m+4) pq.1 pq.2,
     nextJ (2*m+3) (2*m+4) pq.1 pq.2)
end
end PhosphorylationSharpness


