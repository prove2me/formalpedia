-- Prove2me | Definitions.Def_CubicProductLB_Supplement_negCountP
-- name    : CubicProductLB_Supplement_negCountP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:35:25.528198+00:00
-- url     : https://prove2.me/theorems/a4630e92-3ea5-4c1d-b9e6-7523356d3147
-- title:
--   The number $w(x)$ of negative coordinates over $\mathbb F_p$
-- statement:
--   For $x \in \mathbb F_p^n$,
--   $$w(x) = |\{i : x_i = -1\}|$$
--   is the number of its coordinates equal to $-1$.
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Section 15.1, p.51

import Mathlib

namespace CubicProductLB.Supplement

/-- The number `w(x) = |{i : x_i = -1}|` of negative coordinates of `x ∈ F_p^n`
(Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Section 15.1, p.51). -/
def negCountP {p n : ℕ} (x : Fin n → ZMod p) : ℕ :=
  (Finset.univ.filter fun i => x i = -1).card

end CubicProductLB.Supplement


