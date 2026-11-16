-- Prove2me | Definitions.Def_EuclidKSteiner_Supplement_GridLayout
-- name    : EuclidKSteiner_Supplement_GridLayout
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:56:31.396117+00:00
-- url     : https://prove2.me/theorems/8a2c07e8-39c7-449c-b5d1-7ce55ee869c9
-- title:
--   Theorem 1.3 setting — terminals on the integer grid $\{0,\dots,L\}^2$, input layout and output of Steiner points
-- statement:
--   Let $P_0,\dots,P_{n-1}$ be points of the Euclidean plane $\mathbb R^2$ and let $L\ge 0$ be an integer.
--
--   1. The terminals lie **on the $L\times L$ integer grid** if every coordinate of every $P_i$ is an integer in $\{0,1,\dots,L\}$.
--   2. The **machine input** for budget $k$ is the list of reals $k,\ n,\ L$, followed by the two coordinates of $P_0, P_1, \dots$ in order.
--   3. The **machine output** of a list $S=(s_1,\dots,s_m)$ of points of $\mathbb R^d$ is the number $m$ followed by the $d$ coordinates of each $s_j$.
--
--   These are the input and output conventions of Theorem 1.3: continuous Euclidean $k$-Steiner tree for terminals on a grid of side $L$, solved in $2^{O(k\log k)}(n+L)^{O(1)}$ time.
--
--   **Formalization Note** The paper does not say whether its $L\times L$ grid is $\{0,\dots,L\}^2$, $\{0,\dots,L-1\}^2$ or $\{1,\dots,L\}^2$; the grid $\{0,\dots,L\}^2$ contains all three readings, and the running time $(n+L)^{O(1)}$ does not distinguish them.
-- source:
--   Bhore, Kisfaludi-Bak, Marx, Odak, Parameterized Tractability of Euclidean k-Steiner Tree, STOC 2027 submission (manuscript sha256 75361687…), §1 p.2 (PDF p.4); Theorem 1.3, p.3 (PDF p.5); §7, p.33 (PDF p.35)

import Mathlib
import Definitions.Def_EuclidKSteiner_Instance

set_option autoImplicit false

namespace EuclidKSteiner

namespace Supplement

open Classical

/-!
# Theorem 1.3: terminals on an integer grid, input layout and output of Steiner points

Bhore, Kisfaludi-Bak, Marx, Odak, *Parameterized Tractability of Euclidean k-Steiner Tree*,
STOC 2027 submission (manuscript sha256 75361687…), §1, p.2 (PDF p.4): "Continuous Euclidean
k-Steiner Tree. Input: A terminal set P ⊆ ℝ^d and an integer k ≥ 0; n = |P|. … Task: Find a set
S ⊆ ℝ^d with |S| ≤ k minimizing w(MST(P ∪ S))." Theorem 1.3, p.3 (PDF p.5): "Given n terminals on
an L × L integer grid in the plane and an integer k ≥ 1, …".

**Formalization Note**
* The plane is the published `E 2 = EuclideanSpace ℝ (Fin 2)`. Terminals are an indexed sequence
  `P : Fin n → E 2`; the terminal set is its image.
* "On an L × L integer grid" is read as: every coordinate is an integer in `{0, …, L}`. The paper
  does not say whether the grid is `{0, …, L}²`, `{0, …, L − 1}²` or `{1, …, L}²`; `{0, …, L}²`
  contains each of them, and the running time `(n + L)^{O(1)}` does not distinguish them.
* The input is the list of reals `k, n, L`, then the two coordinates of `P 0, P 1, …`. The output
  (read from the cell after the input) is the number `m` of Steiner points, then their `2m`
  coordinates.
-/

/-- Every coordinate of every terminal is an integer in `{0, …, L}`.
Source: Bhore, Kisfaludi-Bak, Marx, Odak, Theorem 1.3, p.3 (PDF p.5): "n terminals on an L × L
integer grid in the plane". -/
def OnGrid {n : ℕ} (L : ℕ) (P : Fin n → E 2) : Prop :=
  ∀ i : Fin n, ∀ j : Fin 2, ∃ z : ℕ, z ≤ L ∧ P i j = (z : ℝ)

/-- **Input of Theorem 1.3**: the reals `k, n, L`, then the coordinates of the terminals. -/
noncomputable def gridLayout {n : ℕ} (k L : ℕ) (P : Fin n → E 2) : List ℝ :=
  (k : ℝ) :: (n : ℝ) :: (L : ℝ) :: coords P

/-- **Output of Theorem 1.3**: the number of points, then the `d` coordinates of each point. -/
noncomputable def encodePoints {d : ℕ} (S : List (E d)) : List ℝ :=
  (S.length : ℝ) :: S.flatMap fun x => (List.finRange d).map fun j => x j

end Supplement

end EuclidKSteiner


