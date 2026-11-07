-- Prove2me | Definitions.Def_PairwiseRealize_Model
-- name    : PairwiseRealize_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:54:54.333712+00:00
-- url     : https://prove2.me/theorems/1616a986-d3fa-46b9-9806-7beea48dd436
-- title:
--   §2.1, p.3 — rows, the statistics $w_x$, the Walsh features $v_x$, the matrix $T$, the zonotope $P_U$, the centered target $y_U$, the depth, and exact realizations
-- statement:
--   Let $V=\{0,1\}^n$, $N=2^n$ and $m=1+n+\binom n2$. The coordinates of the statistics are indexed by the total $\emptyset$, the singletons $i$, and the pairs $\{i,j\}$ with $i<j$. For a row $x\in V$ with signs $\sigma_i=2x_i-1$ put
--
--   $$w_x=\bigl(1,(x_i)_i,(x_ix_j)_{i<j}\bigr),\qquad v_x=\bigl(1,(\sigma_i)_i,(\sigma_i\sigma_j)_{i<j}\bigr).$$
--
--   The fixed integer matrix $T$ with $v_x=Tw_x$ is $(Tb)_\emptyset=b_\emptyset$, $(Tb)_i=2b_i-b_\emptyset$, $(Tb)_{ij}=4b_{ij}-2b_i-2b_j+b_\emptyset$. For $U\subseteq V$ the **zonotope** is $P_U=\sum_{x\in U}[-v_x,v_x]$, the image of $[-1,1]^U$ under $a\mapsto\sum_{x\in U}a_xv_x$. An integer target $b\in\mathbb Z^m$ has **centered vector** $y_U=2Tb-\sum_{x\in U}v_x$, and for $y\in P_U$ the **depth** is
--
--   $$\operatorname{depth}_U(y)=\sup\{\delta\ge0: y+\delta B_m\subseteq P_U\},$$
--
--   where $B_m$ is the Euclidean unit ball of the full centered Walsh space, total coordinate included. A set $S\subseteq U$ of distinct rows is an **exact realization** of $b$ when $\sum_{x\in S}w_x=b$.
--
--   These objects carry every statement of the mission.
--
--   **Formalization Note** Rows are `Fin n → Bool`. The ball is the closed ball of `EuclideanSpace ℝ (Feat n)`, so it is Euclidean. `depth` is a real `sSup`; statements using it keep $y\in P_U$ as a hypothesis, as the paper does, so the set is nonempty and bounded. `featList` fixes the listing of the coordinates used to encode a target.
-- source:
--   Shi, Sun, Robust Exact Realization of Pairwise Boolean Statistics, STOC 2027 submission (sha256 62090516…), §2.1, pp.3 (PDF p.4), (2.1)–(2.4)

import Mathlib

namespace PairwiseRealize

/-!
# Pairwise Boolean statistics: rows, features, the zonotope and depth

K. Shi, H. Sun, *Robust Exact Realization of Pairwise Boolean Statistics*, STOC 2027 submission
(manuscript sha256 62090516…), §2.1 "Statistics and feasible geometry", printed p.3 (PDF p.4),
equations (2.1)–(2.4).

**Formalization Note** A row `x ∈ V = {0,1}ⁿ` is `x : Fin n → Bool`, with `xᵢ = 1` iff `x i = true`.
The `m = 1 + n + (n choose 2)` coordinates are indexed by `Feat n = Unit ⊕ Fin n ⊕ {(i,j) // i < j}`:
the total coordinate `∅`, the singletons `i`, and the unordered pairs `{i,j}` written with `i < j`.
Every ball and every depth lives in `EuclideanSpace ℝ (Feat n)`, so balls are Euclidean, as the paper
requires ("All balls and depths are measured in the full centered Walsh space, including the total
coordinate"). The integer target `b` and the statistics `w_x` are integer vectors; they are cast to the
reals once, in `centered`.
-/

/-- A row of the cube `V = {0,1}ⁿ`: `x i = true` means `xᵢ = 1`. -/
abbrev Row (n : ℕ) := Fin n → Bool

/-- The coordinate index of the statistics: `∅` (the total), the `n` singletons, and the
`n choose 2` pairs `{i, j}` with `i < j`. -/
abbrev Feat (n : ℕ) := Unit ⊕ Fin n ⊕ {p : Fin n × Fin n // p.1 < p.2}

/-- The total coordinate `∅`. -/
abbrev Feat.total {n : ℕ} : Feat n := Sum.inl ()

/-- The singleton coordinate `i`. -/
abbrev Feat.single {n : ℕ} (i : Fin n) : Feat n := Sum.inr (Sum.inl i)

/-- The pair coordinate `{i, j}` for `i < j`. -/
abbrev Feat.pair {n : ℕ} (i j : Fin n) (h : i < j) : Feat n := Sum.inr (Sum.inr ⟨(i, j), h⟩)

/-- The value `0` or `1` of a bit, as an integer. -/
def bv (b : Bool) : ℤ := if b then 1 else 0

/-- The monomial statistics `w_x = (1, (xᵢ)ᵢ, (xᵢxⱼ)_{i<j})` of a row, (2.1). -/
def wvec (n : ℕ) (x : Row n) : Feat n → ℤ
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl i) => bv (x i)
  | Sum.inr (Sum.inr p) => bv (x p.1.1) * bv (x p.1.2)

/-- The sign `σᵢ = 2xᵢ − 1 ∈ {−1, 1}`. -/
def sgn (b : Bool) : ℤ := 2 * bv b - 1

/-- The centered Walsh features `v_x = (1, (σᵢ)ᵢ, (σᵢσⱼ)_{i<j})`, `σᵢ = 2xᵢ − 1`, (2.1). -/
def vvec (n : ℕ) (x : Row n) : Feat n → ℤ
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl i) => sgn (x i)
  | Sum.inr (Sum.inr p) => sgn (x p.1.1) * sgn (x p.1.2)

/-- `v_x` as a real vector (a plain function). -/
def vR (n : ℕ) (x : Row n) : Feat n → ℝ := fun f => (vvec n x f : ℝ)

/-- `w_x` as a real vector (a plain function). -/
def wR (n : ℕ) (x : Row n) : Feat n → ℝ := fun f => (wvec n x f : ℝ)

/-- `v_x` as a vector of the Euclidean space `ℝ^m` (the "full centered Walsh space"). -/
def vE (n : ℕ) (x : Row n) : EuclideanSpace ℝ (Feat n) := WithLp.toLp 2 (vR n x)

/-- The fixed integer matrix `T` with `v_x = T w_x`, "induced by `σᵢ = 2xᵢ − 1` and
`σᵢσⱼ = 4xᵢxⱼ − 2xᵢ − 2xⱼ + 1`" (p.3): `(Tb)_∅ = b_∅`, `(Tb)ᵢ = 2bᵢ − b_∅`,
`(Tb)_{ij} = 4b_{ij} − 2bᵢ − 2bⱼ + b_∅`. Written over any commutative ring, so that the same
matrix acts on integer and on real vectors. -/
def Tmap {R : Type*} [CommRing R] (n : ℕ) (b : Feat n → R) : Feat n → R
  | Sum.inl _ => b Feat.total
  | Sum.inr (Sum.inl i) => 2 * b (Feat.single i) - b Feat.total
  | Sum.inr (Sum.inr p) =>
      4 * b (Sum.inr (Sum.inr p)) - 2 * b (Feat.single p.1.1) - 2 * b (Feat.single p.1.2)
        + b Feat.total

/-- The zonotope `P_U = Σ_{x∈U} [−v_x, v_x]`, (2.2), as the image of the fractional cube
`[−1,1]^U` under `a ↦ Σ_{x∈U} a_x v_x` (p.3). -/
def zonotope (n : ℕ) (U : Finset (Row n)) : Set (EuclideanSpace ℝ (Feat n)) :=
  {y | ∃ a : Row n → ℝ, (∀ x ∈ U, a x ∈ Set.Icc (-1 : ℝ) 1) ∧ y = ∑ x ∈ U, a x • vE n x}

/-- The centered target `y_U = 2Tb − Σ_{x∈U} v_x` of an integer target `b ∈ ℤ^m`, (2.3). -/
def centered (n : ℕ) (U : Finset (Row n)) (b : Feat n → ℤ) : EuclideanSpace ℝ (Feat n) :=
  WithLp.toLp 2 (fun f => 2 * Tmap n (fun g => (b g : ℝ)) f) - ∑ x ∈ U, vE n x

/-- The depth `depth_U(y) = sup{δ ≥ 0 : y + δB_m ⊆ P_U}`, (2.4), with `B_m` the closed Euclidean
unit ball of `ℝ^m`.

**Formalization Note** The paper defines the depth for `y ∈ P_U`; every statement using it keeps
that membership as a hypothesis, so the set is nonempty (`δ = 0`) and bounded (`P_U` is bounded),
and the real `sSup` is the true supremum. The closed and the open ball give the same supremum. -/
noncomputable def depth (n : ℕ) (U : Finset (Row n)) (y : EuclideanSpace ℝ (Feat n)) : ℝ :=
  sSup {δ : ℝ | 0 ≤ δ ∧ Metric.closedBall y δ ⊆ zonotope n U}

/-- `S` is an exact realization of the target `b` in `U`: `S` is a set of distinct rows of `U`
with `Σ_{x∈S} w_x = b` (p.3). -/
def IsRealization (n : ℕ) (U : Finset (Row n)) (b : Feat n → ℤ) (S : Finset (Row n)) : Prop :=
  S ⊆ U ∧ ∑ x ∈ S, wvec n x = b

/-- The listing of `Feat n` used to encode a target: `∅`, then the singletons `i` in increasing
order, then the pairs `{i,j}` (`i < j`) in lexicographic order. -/
def featList (n : ℕ) : List (Feat n) :=
  [Feat.total] ++ (List.finRange n).map (fun i => Feat.single i) ++
    (List.finRange n).flatMap (fun i => (List.finRange n).filterMap
      (fun j => if h : i < j then some (Feat.pair i j h) else none))

end PairwiseRealize


