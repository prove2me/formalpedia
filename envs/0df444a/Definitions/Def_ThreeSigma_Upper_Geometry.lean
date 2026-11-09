-- Prove2me | Definitions.Def_ThreeSigma_Upper_Geometry
-- name    : ThreeSigma_Upper_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:14.167022+00:00
-- url     : https://prove2.me/theorems/c02fa17c-5d63-44e1-86cb-22a2c35cdf8e
-- title:
--   Euclidean coordinates, residual energy, nearest-sign rounding, and discrepancy body
-- statement:
--   For a real $d\times n$ matrix $A$ and $z\in\mathbb R^n$, let $Az$ have coordinates $\sum_j A_{ij}z_j$ and define
--   $$R(z)=n-\|z\|_2^2,\qquad \Delta(n,d)=\sqrt{3n\operatorname{arsinh}(10d/n)},$$
--   $$\mathcal K(A)=\{z: |z_j|\le1\ \forall j,\ |(Az)_i|\le\Delta(n,d)\ \forall i\}.$$
--   Nearest-sign rounding sends $z_j\ge0$ to $+1$ and $z_j<0$ to $-1$. These definitions give the objects of Lemma 3.2 and Proposition 3.6.
--
--   **Formalization Note** Coordinates use Euclidean space over `Fin n`; the row product has the ordinary finite-function supremum norm, including norm zero for no rows. Absolute row bounds encode both the original rows and their negations, exactly as in (2). At $n=0$, total division sets $10d/n=0$ and hence $\Delta=0$; all row products are zero.
-- source:
--   Victor Reis, Zhao Song, Three Standard Deviations Suffice While One Does Not, STOC 2027 submission #393 (October 2026), §3, p. 5, Lemma 3.2 and equations (1)–(2); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/393.pdf

import Mathlib

namespace ThreeSigma.Upper

/-- The paper's Euclidean coordinate space; Fin indices start at zero. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The product Az of a d×n matrix with a Euclidean vector, as a function Fin d → ℝ
(whose Mathlib norm is the sup norm, max over rows of the absolute value). -/
noncomputable def rowProduct {d n : ℕ} (A : Fin d → Fin n → ℝ) (z : E n) : Fin d → ℝ :=
  fun i => ∑ j, A i j * z j

/-- R(z) = n - ‖z‖₂² (p. 5), with real subtraction. -/
noncomputable def R {n : ℕ} (z : E n) : ℝ := (n : ℝ) - ‖z‖ ^ 2

/-- Nearest-sign rounding, with ties at zero sent to +1. -/
noncomputable def nearestSign {n : ℕ} (z : E n) : E n :=
  WithLp.toLp 2 (fun j => if 0 ≤ z j then (1 : ℝ) else (-1 : ℝ))

/-- The exact discrepancy threshold from (1); Lean's division is total at n = 0. -/
noncomputable def delta (n d : ℕ) : ℝ :=
  Real.sqrt (3 * (n : ℝ) * Real.arsinh (10 * (d : ℝ) / (n : ℝ)))

/-- (2), using absolute values of original rows in place of the doubled rows. -/
noncomputable def K {d n : ℕ} (A : Fin d → Fin n → ℝ) : Set (E n) :=
  {z | (∀ j, |z j| ≤ 1) ∧ ∀ i, |rowProduct A z i| ≤ delta n d}

end ThreeSigma.Upper


