-- Prove2me | Definitions.Def_GaussianPerimeter_QuadratureCertificate
-- name    : GaussianPerimeter_QuadratureCertificate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T10:08:44.852503+00:00
-- url     : https://prove2.me/theorems/f1f1237b-49f3-4fee-806a-f440c5dd421c
-- title:
--   Quadrature Certificate
-- statement:
--   Definitions and structural lemmas for Quadrature Certificate, from XinyuanXie-hub (XinyuanXie-hub/GaussianPerimeter; see pinned Apache-2.0 LICENSE)'s pinned Asymptotic lower bound for Gaussian perimeter of convex bodies development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/QuadratureCertificate.lean

module
public import Definitions.Def_GaussianPerimeter_Quadrature
public import Definitions.Def_GaussianPerimeter_Prefactor
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Finset
namespace GaussianPerimeter
local notation "A" => (6131 / 5000)
local notation "B" => (2387 / 1000)
local notation "F" => lowerBoundIntegrand A B
def gridPoint (i : ℕ) : ℚ := -(15 / 4) + ((i : ℚ) + 1) / 2048
def sample (i : ℕ) : ℤ :=
  if i < 10239 then
    let x := gridPoint i
    ⌊1000000000 * expLower (-x ^ 2 - B * expUpper (A ^ 2 * x))⌋
  else 0
def sumSamples (start : ℕ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => sumSamples start n + sample (start + n)
def sumBuckets : ℕ → ℤ
  | 0 => 0
  | n + 1 => sumBuckets n + sumSamples (320 * n) 320
def bucketLower (k : ℕ) : ℤ :=
  (#[446366, 1403850, 4117277, 11420510, 30080485, 75311966, 179250084, 405452268,
    871122108, 1776519042, 3435704486, 6293798777, 10904935774, 17837760934,
    27481863818, 39760773904, 53819945108, 67836503856, 79146597553, 84838492080,
    82764148561, 72612956187, 56443046614, 38147572977, 21894730030, 10360852799,
    3895703951, 1111409668, 227126040, 30936050, 2552680, 96424] : Array ℤ)[k]!
def sumBounds : ℕ → ℤ
  | 0 => 0
  | n + 1 => sumBounds n + bucketLower n
end GaussianPerimeter


