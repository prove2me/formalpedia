-- Prove2me | Definitions.Def_CubicProductLB_DependsOnAtMost
-- name    : CubicProductLB_DependsOnAtMost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:14:44.164438+00:00
-- url     : https://prove2.me/theorems/39480591-3bf6-4d21-aa82-37fa36514655
-- title:
--   Dependence on at most $r$ affine observations
-- statement:
--   A function $f$ **depends on at most $r$ affine observations** on $X_n$ if there are $s \le r$ affine forms $A_1, \dots, A_s$ and a function $H : \mathbb F_3^s \to \mathbb F_3$ with
--   $$f(x) = H(A_1(x), \dots, A_s(x)) \quad \text{for every } x \in X_n.$$
--   The map $H$ is arbitrary, since only its values on the attained image are relevant. This measures information rather than coordinate support.
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Definition 3, Eq. (4), p.4

import Mathlib
import Definitions.Def_CubicProductLB_signCube
import Definitions.Def_CubicProductLB_AffineForm

namespace CubicProductLB

/-- `f` depends on at most `r` affine observations on `X_n`: `f(x) = H(A_1(x), …, A_s(x))` on `X_n`
for some `s ≤ r`, affine forms `A_a` and a function `H : F_3^s → F_3`
(Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Definition 3, Eq. (4), p.4).

**Formalization Note** `H` is arbitrary, since "Only the values of H on the attained image are
relevant". -/
def DependsOnAtMost {n : ℕ} (r : ℕ) (f : (Fin n → ZMod 3) → ZMod 3) : Prop :=
  ∃ s ≤ r, ∃ (A : Fin s → AffineForm n) (H : (Fin s → ZMod 3) → ZMod 3),
    ∀ x ∈ signCube n, f x = H fun a => AffineForm.eval (A a) x

end CubicProductLB


