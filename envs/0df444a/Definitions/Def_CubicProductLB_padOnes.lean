-- Prove2me | Definitions.Def_CubicProductLB_padOnes
-- name    : CubicProductLB_padOnes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:17:22.064339+00:00
-- url     : https://prove2.me/theorems/6c9ec1cc-da4f-44ca-9cff-a21b9dbc15bf
-- title:
--   Fixing the surplus coordinates to $+1$
-- statement:
--   For $N \le n$, a point $x \in \mathbb F_3^N$ is extended to $(x_1, \dots, x_N, 1, \dots, 1) \in \mathbb F_3^n$, fixing $x_{N+1} = \cdots = x_n = +1$.
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), proof of Theorem 5, Eq. (358), p.40

import Mathlib

namespace CubicProductLB

/-- Extension of a point of `F_3^N` to `F_3^n` by the surplus coordinates `x_{N+1} = ⋯ = x_n = +1`
(Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), proof of Theorem 5, Eq. (358), p.40).

**Formalization Note** The first `N` coordinates are kept; it is used only with `N ≤ n`. -/
def padOnes {N n : ℕ} (x : Fin N → ZMod 3) : Fin n → ZMod 3 :=
  fun i => if h : (i : ℕ) < N then x ⟨i, h⟩ else 1

end CubicProductLB


