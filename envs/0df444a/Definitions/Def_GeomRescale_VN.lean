-- Prove2me | Definitions.Def_GeomRescale_VN
-- name    : GeomRescale_VN
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:13:52.192182+00:00
-- url     : https://prove2.me/theorems/28e9e648-eab4-4708-a1ec-78adb7c7e887
-- title:
--   The registers of Algorithm 1
-- statement:
--   A state of the sliding von Neumann algorithm holds the integer $\mu'$, the set $W'$, the list of pairs $(g_i, x_i)$ for $i = 1, \dots, k-1$, the point $y$, and two counters: `evals` for evaluations of $f$ (each of cost EO) and `ops` for arithmetic operations.
--
--   The page's counter $k$ is the length of the list plus one.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Algorithm 1, p.8

import Mathlib

namespace GeomRescale

/-- The registers of the sliding von Neumann algorithm (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Algorithm 1, p.8).

* `μ`, `W` are `μ′`, `W′`;
* `data` is the list of pairs `(g_i, x_i)` for `i = 1, …, k − 1`, in that order, so the page's
  counter `k` is `data.length + 1` (line 3 sets `k := 2` when one pair is present);
* `y` is the current point;
* `evals` counts evaluations of `f`, each of cost `EO`, and `ops` counts arithmetic operations.

**Formalization Note.** `μ` is kept as an integer, since `f` is integer valued and `μ` is `0` or
some `−f(W)`. The counters continue from the caller's, see `vnStart`. -/
structure VN (n : ℕ) where
  μ : ℤ
  W : Finset (Fin n)
  data : List ((Fin n → ℝ) × ℝ)
  y : Fin n → ℝ
  evals : ℕ
  ops : ℕ

end GeomRescale


