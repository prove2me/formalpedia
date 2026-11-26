-- Prove2me | Definitions.Def_FD1D_V5_LocalPolicy
-- name    : FD1D_V5_LocalPolicy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:15:43.450192+00:00
-- url     : https://prove2.me/theorems/2b89f198-b98b-5142-b0dd-c9a8e773d0cb
-- title:
--   Local Policy
-- statement:
--   Definitions and structural lemmas for Local Policy, from Yash Kanoria (ykanoria/FD1d-Lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Tight upper bound for fully dynamic matching on the line development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalPolicy.lean

import Definitions.Def_FD1D_V5_Parameters
set_option autoImplicit true
namespace FD1D.V5.LocalPolicy
noncomputable section
def inventory (x y : ℕ) : ℝ :=
  (x : ℝ) + (y : ℝ)
def parentMass (h : ℝ) (x y : ℕ) : ℝ :=
  inventory x y * h
def feedbackCandidate (a h : ℝ) (x y : ℕ) : ℝ :=
  2 * a * parentMass h x y * ((x : ℝ) - y) / ((x : ℝ) * y)
def uniformCandidate (h : ℝ) (x y : ℕ) : ℝ :=
  parentMass h x y * ((x : ℝ) - y) / inventory x y
def floorCandidate (a p h : ℝ) (x y : ℕ) : ℝ :=
  parentMass h x y - 2 * p * y / (2 * (y : ℝ) + a)
def orderedBias (a p h : ℝ) (x y : ℕ) : ℝ :=
  if x = y then 0
  else if x + y = 0 then 0
  else if y = 0 then parentMass h x y
  else min (feedbackCandidate a h x y)
    (min (uniformCandidate h x y) (floorCandidate a p h x y))
def bias (a p h : ℝ) (x y : ℕ) : ℝ :=
  if y ≤ x then orderedBias a p h x y else -orderedBias a p h y x
def massLeft (a p h : ℝ) (x y : ℕ) : ℝ :=
  (parentMass h x y + bias a p h x y) / 2
def massRight (a p h : ℝ) (x y : ℕ) : ℝ :=
  (parentMass h x y - bias a p h x y) / 2
def rateLeft (a p h : ℝ) (x y : ℕ) : ℝ :=
  if x + y = 0 then h
  else if x = 0 then max h (p / a)
  else massLeft a p h x y / x
def rateRight (a p h : ℝ) (x y : ℕ) : ℝ :=
  if x + y = 0 then h
  else if y = 0 then max h (p / a)
  else massRight a p h x y / y
def discrepancy (a p h : ℝ) (x y : ℕ) : ℝ :=
  (p - parentMass h x y) / a
def regularizedMass (a p : ℝ) (x y : ℕ) : ℝ :=
  p / (inventory x y + a / 2)
def discrepancyLeft (a p h : ℝ) (x y : ℕ) : ℝ :=
  (p / 2 - massLeft a p h x y) / a
def discrepancyRight (a p h : ℝ) (x y : ℕ) : ℝ :=
  (p / 2 - massRight a p h x y) / a
def regularizedMassLeft (a p : ℝ) (x y : ℕ) : ℝ :=
  (p / 2) / ((x : ℝ) + a / 2)
def regularizedMassRight (a p : ℝ) (x y : ℕ) : ℝ :=
  (p / 2) / ((y : ℝ) + a / 2)
def bellman (h t Z : ℝ) : ℝ :=
  (t - h / 2) * Z - t ^ 2 / 6
end
end FD1D.V5.LocalPolicy


