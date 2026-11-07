-- Prove2me | Definitions.Def_CubicProductLB_negCount
-- name    : CubicProductLB_negCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:12:42.968379+00:00
-- url     : https://prove2.me/theorems/cc68253c-5243-4c21-9684-09ca0f9dea79
-- title:
--   The number $w(x)$ of negative coordinates
-- statement:
--   For a vector $x \in \mathbb F_3^n$, the quantity
--   $$w(x) = |\{j : x_j = -1\}|$$
--   is the number of its negative coordinates. It is the weight whose residue the target predicate tests.
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Section 2, p.3

import Mathlib

namespace CubicProductLB

/-- The number `w(x) = |{j : x_j = -1}|` of negative coordinates (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Section 2, p.3). -/
def negCount {n : ℕ} (x : Fin n → ZMod 3) : ℕ :=
  (Finset.univ.filter fun i => x i = -1).card

end CubicProductLB


