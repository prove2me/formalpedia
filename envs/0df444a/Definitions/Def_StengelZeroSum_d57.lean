-- Prove2me | Definitions.Def_StengelZeroSum_d57
-- name    : StengelZeroSum_d57
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:02:52.10002+00:00
-- url     : https://prove2.me/theorems/811469ab-90ac-4211-be44-90e942d1179d
-- title:
--   The vector $d$ of (57)
-- statement:
--   For $b\in\mathbb R^m$ and $c\in\mathbb R^n$, the vector
--
--   $$
--   d=\begin{bmatrix}b\\ -c\end{bmatrix}\in\mathbb R^{m+n}.
--   $$
--
--   Together with $C$ of (57) it turns the system (58) and the game $D_M$ of (60) into the LP data of (1) and (2).
--
--   **Formalization Note** $d$ is indexed by $\mathrm{Fin}\,m\oplus\mathrm{Fin}\,n$, the $b$-block first.
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, eq. (57), p.20

import Mathlib

namespace StengelZeroSum

/-- The vector `d` of (57),
von Stengel, *Zero-Sum Games and Linear Programming Duality*, arXiv:2205.11196v6, eq. (57),
p.20: `d = [ b ; −c ]`.

**Formalization Note** `d` is indexed by `Fin m ⊕ Fin n`, the `b`-block first. -/
def d57 {m n : ℕ} (b : Fin m → ℝ) (c : Fin n → ℝ) : Fin m ⊕ Fin n → ℝ :=
  Sum.elim b (-c)

end StengelZeroSum


