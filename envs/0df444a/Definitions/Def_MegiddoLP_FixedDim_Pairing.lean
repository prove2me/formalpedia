-- Prove2me | Definitions.Def_MegiddoLP_FixedDim_Pairing
-- name    : MegiddoLP_FixedDim_Pairing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T23:07:44.494887+00:00
-- url     : https://prove2.me/theorems/da15f26b-c15a-4272-8af8-64f20efc67db
-- title:
--   Slopes in the $(x_1,x_2)$ plane and the paired hyperplanes $H^{(1)}_{ik}$, $H^{(2)}_{ik}$
-- statement:
--   Let $d\ge2$ and let $H=\{x\in\mathbb{R}^d:\ \sum_j a_jx_j=b\}$. The hyperplane meets the $(x_1,x_2)$ subspace in the line $a_1x_1+a_2x_2=b$, and the **slope** of $H$ is the slope of that line:
--
--   $$\operatorname{slope}(H)=\begin{cases}+\infty,& a_2=0,\\ -a_1/a_2,& a_2\neq0.\end{cases}$$
--
--   So $H$ has **nonnegative slope** when $a_2=0$ or $-a_1/a_2\ge0$, and **nonpositive slope** when $a_2\ne0$ and $-a_1/a_2\le0$. A slope $+\infty$ is nonnegative but not nonpositive.
--
--   For two hyperplanes $H_i=\{a_i^Tx=b_i\}$ and $H_k=\{a_k^Tx=b_k\}$ the paper defines the **paired hyperplanes**
--
--   $$H^{(1)}_{ik}:\ \sum_{j=1}^d(a_{k1}a_{ij}-a_{i1}a_{kj})x_j=a_{k1}b_i-a_{i1}b_k,\qquad H^{(2)}_{ik}:\ \sum_{j=1}^d(a_{k2}a_{ij}-a_{i2}a_{kj})x_j=a_{k2}b_i-a_{i2}b_k.$$
--
--   The first is obtained by subtracting $a_{i1}$ times the equation of $H_k$ from $a_{k1}$ times the equation of $H_i$, so its $x_1$-coefficient vanishes. The second is the same construction with $x_2$, so its $x_2$-coefficient vanishes. These hyperplanes are what the search queries in one dimension lower.
--
--   **Formalization Note** The dimension is written $d+2$ (Lean `Fin (d + 2)`), and the paper's coordinates $x_1,x_2$ are the indices `0` and `1`. The slope predicates avoid division by zero by testing $a_2$ first. Normals and right-hand sides of $H^{(1)}_{ik}$, $H^{(2)}_{ik}$ are given as separate functions.
-- source:
--   Megiddo, Linear Programming in Linear Time When the Dimension Is Fixed, J. ACM 31(1) (1984) 114–127, §3.2, p. 119 (definition of slope; equations of H^(1)_ik and H^(2)_ik)

import Mathlib

/-!
Slopes and paired hyperplanes (Megiddo, J. ACM 31 (1984), §3.2, p. 119).

The hyperplane `H = {x ∈ ℝ^d | a ⬝ᵥ x = b}` meets the `(x₁, x₂)` plane in the line
`a₁x₁ + a₂x₂ = b`; its *slope* is `+∞` if `a₂ = 0` and `-a₁/a₂` otherwise. The paper's
coordinates `x₁, x₂` are the indices `0, 1` of `Fin (d + 2)` (the paper's dimension is
`d + 2 ≥ 2`). For a pair `H_i, H_k` the paper defines
`H⁽¹⁾_ik : Σⱼ (a_k1 a_ij - a_i1 a_kj) xⱼ = a_k1 bᵢ - a_i1 b_k` and
`H⁽²⁾_ik : Σⱼ (a_k2 a_ij - a_i2 a_kj) xⱼ = a_k2 bᵢ - a_i2 b_k`.
-/

namespace MegiddoLP.FixedDim

variable {d : ℕ}

/-- The hyperplane with normal `a` has nonnegative slope in the `(x₁, x₂)` plane: its slope
is `+∞` (`a₂ = 0`) or `-a₁/a₂ ≥ 0`. -/
def HasNonnegSlope (a : Fin (d + 2) → ℝ) : Prop :=
  a 1 = 0 ∨ 0 ≤ -(a 0) / a 1

/-- The hyperplane with normal `a` has nonpositive slope in the `(x₁, x₂)` plane: `a₂ ≠ 0`
and `-a₁/a₂ ≤ 0` (a slope `+∞` is not nonpositive). -/
def HasNonposSlope (a : Fin (d + 2) → ℝ) : Prop :=
  a 1 ≠ 0 ∧ -(a 0) / a 1 ≤ 0

/-- Normal vector of `H⁽¹⁾_ik`: `j ↦ a_k1 a_ij - a_i1 a_kj`. -/
def pairNormal1 (ai ak : Fin (d + 2) → ℝ) : Fin (d + 2) → ℝ :=
  fun j => ak 0 * ai j - ai 0 * ak j

/-- Right-hand side of `H⁽¹⁾_ik`: `a_k1 bᵢ - a_i1 b_k`. -/
def pairRhs1 (ai ak : Fin (d + 2) → ℝ) (bi bk : ℝ) : ℝ :=
  ak 0 * bi - ai 0 * bk

/-- Normal vector of `H⁽²⁾_ik`: `j ↦ a_k2 a_ij - a_i2 a_kj`. -/
def pairNormal2 (ai ak : Fin (d + 2) → ℝ) : Fin (d + 2) → ℝ :=
  fun j => ak 1 * ai j - ai 1 * ak j

/-- Right-hand side of `H⁽²⁾_ik`: `a_k2 bᵢ - a_i2 b_k`. -/
def pairRhs2 (ai ak : Fin (d + 2) → ℝ) (bi bk : ℝ) : ℝ :=
  ak 1 * bi - ai 1 * bk

end MegiddoLP.FixedDim


