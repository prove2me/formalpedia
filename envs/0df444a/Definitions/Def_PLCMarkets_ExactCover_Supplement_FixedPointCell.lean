-- Prove2me | Definitions.Def_PLCMarkets_ExactCover_Supplement_FixedPointCell
-- name    : PLCMarkets_ExactCover_Supplement_FixedPointCell
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:16:39.847179+00:00
-- url     : https://prove2.me/theorems/ef8fc4c4-7161-4dd7-bf67-d1dfa23190be
-- title:
--   The correspondence $F$ on $S\times D$, the resolution $\delta=2^{-10m}$, and a fixed point of the interpolated map $G$ in a cell (§6)
-- statement:
--   Let $M$ be an Arrow–Debreu market with $n$ agents and $g$ goods. Let $S=\{p\ge0,\ \sum_jp_j=1\}$ be the unit price simplex and $D=[0,1.1]^{ng}$ the box of demand vectors; $x_{ij}$ is the amount of good $j$ bought by agent $i$, $x_j=\sum_ix_{ij}$ is the total demand for good $j$, and $px=\sum_{ij}p_jx_{ij}$.
--
--   Each utility $f^i_j$ is **trimmed** to go flat after $1.1$ units, i.e. replaced by $x\mapsto f^i_j(\min(x,1.1))$. The correspondence $F:S\times D\rightrightarrows S\times D$ maps $(p,x)$ to the pairs $(p',x')$ such that
--
--   1. $p'$ maximizes $p'x$ over $p'\in S$ (the component $F_1$), and
--   2. $x'\in D$ consists of optimal budget-feasible bundles in $D$ for the trimmed utilities at prices $p$: for every agent $i$, $\sum_jp_jx'_{ij}\le\sum_jp_jw_{ij}$ and no bundle in $[0,1.1]^g$ within this budget has larger trimmed utility (the component $F_2$).
--
--   For $m\in\mathbb N$ the resolution is
--   $$\delta=\frac{1}{2^{10m}}.$$
--   Any two vertices of a cell of a regular simplicization of $S\times D$ of resolution $\delta$ are equal or differ by exactly $\delta$ in each coordinate. A **fixed point of $G$ in a cell $C$** consists of the vertices $(p_v,x_v)\in S\times D$ of $C$ (pairwise equal or $\delta$ apart in each coordinate), a choice $G(p_v,x_v)=(p'_v,x'_v)\in F(p_v,x_v)$ at each vertex, and weights $\lambda_v\ge0$ with $\sum_v\lambda_v=1$ such that
--   $$(p^*,x^*)=\sum_v\lambda_v(p_v,x_v)=\sum_v\lambda_v(p'_v,x'_v).$$
--   The second equality says that $(p^*,x^*)$ is a fixed point of the linear interpolation $G$ of the selected values. The point may lie on a smaller-dimensional face of $C$.
--
--   These objects are the setting of Lemma 6.3 and of the proof of Theorem 6.1.
--
--   **Formalization Note** The cell is any finite family of points of $S\times D$ with the stated coordinate property, not necessarily a cell of one particular simplicization; every cell of the regular simplicization of p. 10:12 is such a family. The index $m$ is a free natural number, not the paper's specific LP bit bound. Agents and goods are `Fin n` and `Fin g`; $1.1$ is the rational $11/10$.
-- source:
--   Vazirani and Yannakakis, Market Equilibrium under Separable, Piecewise-Linear, Concave Utilities, J. ACM 58(3), Article 10, 2011, p. 10:11 (§6: trimming at 1.1, S, D = [0,1.1]^ng, correspondence F and its components F1, F2); p. 10:12 (m, δ = 1/2^(10m), regular simplicization, the map G, fixed point (p*, x*), the cell C)

import Mathlib
import Definitions.Def_PLCMarkets_ExactCover_ADMarket

namespace PLCMarkets.ExactCover.Supplement

open PLCMarkets.ExactCover

variable {n g : ℕ}

/-- `x ∈ D = [0, 1.1]^{ng}`: the box of demand vectors of §6, p. 10:11 (`x i j` is the amount of
good `j` bought by agent `i`). -/
def InBoxD (x : Fin n → Fin g → ℝ) : Prop :=
  ∀ i j, 0 ≤ x i j ∧ x i j ≤ 11 / 10

/-- The total demand `x_j = Σ_i x_ij` for good `j` in the demand vector `x`. -/
def totalDemand (x : Fin n → Fin g → ℝ) (j : Fin g) : ℝ :=
  ∑ i, x i j

/-- The cost `p x = Σ_{ij} p_j x_ij` of the demand vector `x` at prices `p`. -/
def allocationCost (p : Fin g → ℝ) (x : Fin n → Fin g → ℝ) : ℝ :=
  ∑ i, ∑ j, p j * x i j

/-- The price component `F₁` of the correspondence `F` (p. 10:11): `p'` maximizes `p' x` over the
unit simplex `S`. -/
def IsPriceResponse (x : Fin n → Fin g → ℝ) (p' : Fin g → ℝ) : Prop :=
  ADMarket.InSimplex p' ∧
    ∀ p'' : Fin g → ℝ, ADMarket.InSimplex p'' → allocationCost p'' x ≤ allocationCost p' x

/-- Agent `i`'s utility for the bundle `y` after every `f^i_j` is trimmed to go flat after `1.1`
units of good `j` (p. 10:11): `Σ_j f^i_j(min(y_j, 1.1))`. -/
noncomputable def trimmedUtility (M : ADMarket (Fin n) (Fin g)) (i : Fin n) (y : Fin g → ℝ) : ℝ :=
  ∑ j, (M.util i j).eval (min (y j) (11 / 10))

/-- `y` is an optimal budget-feasible bundle in `D` for agent `i` under prices `p`, for the trimmed
utilities: `0 ≤ y_j ≤ 1.1`, `Σ_j p_j y_j ≤ Σ_j p_j w_ij`, and no such bundle `z` has larger trimmed
utility. -/
def IsTrimmedOptimalBundle (M : ADMarket (Fin n) (Fin g)) (p : Fin g → ℝ) (i : Fin n)
    (y : Fin g → ℝ) : Prop :=
  (∀ j, 0 ≤ y j ∧ y j ≤ 11 / 10) ∧ ∑ j, p j * y j ≤ M.income p i ∧
    ∀ z : Fin g → ℝ, (∀ j, 0 ≤ z j ∧ z j ≤ 11 / 10) → ∑ j, p j * z j ≤ M.income p i →
      trimmedUtility M i z ≤ trimmedUtility M i y

/-- The demand component `F₂` of the correspondence `F` (p. 10:11): `x'` consists of optimal
budget-feasible bundles in `D` for all agents under prices `p`. -/
def IsDemandResponse (M : ADMarket (Fin n) (Fin g)) (p : Fin g → ℝ)
    (x' : Fin n → Fin g → ℝ) : Prop :=
  ∀ i, IsTrimmedOptimalBundle M p i (x' i)

/-- `(p', x') ∈ F(p, x)`: the correspondence `F : S × D ⇉ S × D` of p. 10:11. -/
def InCorrespondenceF (M : ADMarket (Fin n) (Fin g))
    (v w : (Fin g → ℝ) × (Fin n → Fin g → ℝ)) : Prop :=
  IsPriceResponse v.2 w.1 ∧ IsDemandResponse M v.1 w.2

/-- The resolution `δ = 1/2^{10m}` of the simplicization (p. 10:12). -/
noncomputable def mesh (m : ℕ) : ℝ := ((2 : ℝ) ^ (10 * m))⁻¹

/-- Two points of `S × D` are equal or differ by `δ` in each coordinate, as any two vertices of a
cell of the regular simplicization of resolution `δ` do (p. 10:12). -/
def MeshAdjacent (δ : ℝ) (v w : (Fin g → ℝ) × (Fin n → Fin g → ℝ)) : Prop :=
  (∀ j, v.1 j = w.1 j ∨ |v.1 j - w.1 j| = δ) ∧
    ∀ i j, v.2 i j = w.2 i j ∨ |v.2 i j - w.2 i j| = δ

/-- The data around a fixed point of the interpolated map `G` of p. 10:12 on a cell `C` of a
simplicization of `S × D` of resolution `δ`:
1. the vertices `vertex a = (p_a, x_a)` of `C` lie in `S × D` and any two of them are equal or
   differ by `δ` in each coordinate;
2. `G` picks at every vertex an element `image a = (p'_a, x'_a) ∈ F(p_a, x_a)`;
3. `(p*, x*)` is a convex combination `Σ_a λ_a (p_a, x_a)` of the vertices of `C`, and, being a
   fixed point of the linear interpolation `G`, also the same convex combination
   `Σ_a λ_a (p'_a, x'_a)` of their `G`-values.
The point may lie on a smaller-dimensional face of `C` (some `λ_a = 0`). -/
structure FixedPointCell (M : ADMarket (Fin n) (Fin g)) (δ : ℝ) where
  /-- The number of vertices of the cell. -/
  k : ℕ
  /-- The vertices `(p_a, x_a)` of the cell. -/
  vertex : Fin k → (Fin g → ℝ) × (Fin n → Fin g → ℝ)
  /-- The selected values `G(p_a, x_a) = (p'_a, x'_a)`. -/
  image : Fin k → (Fin g → ℝ) × (Fin n → Fin g → ℝ)
  /-- The barycentric weights `λ_a` of the fixed point. -/
  weight : Fin k → ℝ
  /-- The price part `p*` of the fixed point. -/
  pStar : Fin g → ℝ
  /-- The demand part `x*` of the fixed point. -/
  xStar : Fin n → Fin g → ℝ
  vertex_mem : ∀ a, ADMarket.InSimplex (vertex a).1 ∧ InBoxD (vertex a).2
  vertex_adjacent : ∀ a b, MeshAdjacent δ (vertex a) (vertex b)
  image_mem : ∀ a, InCorrespondenceF M (vertex a) (image a)
  weight_nonneg : ∀ a, 0 ≤ weight a
  weight_sum : ∑ a, weight a = 1
  pStar_vertex : ∀ j, pStar j = ∑ a, weight a * (vertex a).1 j
  xStar_vertex : ∀ i j, xStar i j = ∑ a, weight a * (vertex a).2 i j
  pStar_image : ∀ j, pStar j = ∑ a, weight a * (image a).1 j
  xStar_image : ∀ i j, xStar i j = ∑ a, weight a * (image a).2 i j

end PLCMarkets.ExactCover.Supplement


