-- Prove2me | Definitions.Def_ModernConvex_Ellipsoids_Ellipsoid
-- name    : ModernConvex_Ellipsoids_Ellipsoid
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:34:12.852655+00:00
-- url     : https://prove2.me/theorems/0d3eb49d-96fb-47f9-bb03-22155ea36a94
-- title:
--   Ellipsoids (Ell), full-dimensional ellipsoids, normalized volume, solids, W[Z], W(Y, y) and the arithmetic sum W₁ + ⋯ + W_m
-- statement:
--   This file fixes the geometric objects of §4.9 of Ben-Tal–Nemirovski (pp. 257–266). Points of $\mathbb R^n$ are vectors $x=(x_1,\dots,x_n)$ and $u^Tu=\sum_j u_j^2$.
--
--   1. The **unit Euclidean ball** of $\mathbb R^q$ is $\{u\in\mathbb R^q \mid u^Tu\le 1\}$.
--   2. An **ellipsoid** (Ell) is the image of a unit Euclidean ball under an affine map: for $A\in\mathbb R^{n\times q}$ and $c\in\mathbb R^n$,
--   $$E(A,c)=\{x=Au+c \mid u^Tu\le 1\}.$$
--   It may be flat. It is **full-dimensional** if it can be written this way with $q=n$ and $\operatorname{Det}A\neq 0$.
--   3. The **normalized volume** of a set $G\subseteq\mathbb R^n$ is $\operatorname{Vol}(G)=\kappa_n^{-1}\operatorname{mes}_n(G)$, where $\operatorname{mes}_n$ is Lebesgue measure and $\kappa_n$ is the Lebesgue measure of the unit Euclidean ball. So the unit ball has volume $1$, and $\operatorname{Vol}(E(A,c))=|\operatorname{Det}A|$ for square $A$.
--   4. A **solid** is a closed, bounded, convex set with nonempty interior. A set $S$ is **central-symmetric** if there is a point $c$ with $2c-x\in S$ for every $x\in S$.
--   5. $E$ is a **largest-volume full-dimensional ellipsoid contained in $S$** if it is a full-dimensional ellipsoid, $E\subseteq S$, and $\operatorname{Vol}(E')\le\operatorname{Vol}(E)$ for every full-dimensional ellipsoid $E'\subseteq S$. Likewise $E$ is a **smallest-volume full-dimensional ellipsoid containing $S$** if it is full-dimensional, $S\subseteq E$, and $\operatorname{Vol}(E)\le\operatorname{Vol}(E')$ for every full-dimensional ellipsoid $E'\supseteq S$.
--   6. For an $n\times n$ matrix $Z$, $W[Z]=\{x \mid x^TZx\le 1\}$. For $Z\succ 0$ this is a full-dimensional ellipsoid centred at the origin.
--   7. For $Y\in\mathbb R^{n\times n}$ and $y\in\mathbb R^n$, $W(Y,y)=\{x \mid (x-y)^TY^TY(x-y)\le 1\}$. It is a full-dimensional ellipsoid when $\operatorname{Det}Y\neq0$.
--   8. The **arithmetic (Minkowski) sum** of sets $W_1,\dots,W_m\subseteq\mathbb R^n$ is $W_1+\dots+W_m=\{w_1+\dots+w_m \mid w_i\in W_i\}$.
--
--   **Formalization Note** Vectors are `Fin n → ℝ`, and $u^Tu$ is the dot product `u ⬝ᵥ u`. The ball is written with the dot product on purpose: on `Fin n → ℝ`, Mathlib's metric ball is the cube of the sup norm. Lebesgue measure is Mathlib's `volume` on `Fin n → ℝ`, valued in $[0,\infty]$. Normalized volume is that measure divided by the measure of the unit Euclidean ball, which is positive and finite. The book's index $i=1,\dots,m$ is `Fin m`; for $m=0$ the sum is $\{0\}$.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 257 (Ell), p. 258 (full-dimensional ellipsoids), p. 259 (normalized volume, solid), p. 262 (W(Y, y)), pp. 265–266 (arithmetic sum, W[Z])

import Mathlib

open Matrix MeasureTheory

open scoped ENNReal

namespace ModernConvex.Ellipsoids

/-- The Euclidean unit ball `{u ∈ ℝ^q | uᵀu ≤ 1}`. Written with the dot product on purpose: on
`Fin q → ℝ`, Mathlib's `Metric.closedBall 0 1` is the unit cube of the sup norm. -/
def unitBall (q : ℕ) : Set (Fin q → ℝ) :=
  {u | u ⬝ᵥ u ≤ 1}

/-- An ellipsoid in `ℝⁿ` (Ben-Tal–Nemirovski, p. 257, (Ell)): the image of the unit Euclidean ball
of some `ℝ^q` under an affine mapping, `E = {x = Au + c | uᵀu ≤ 1}`, `A ∈ M^{n,q}`. It may be flat
(a segment in `ℝ¹⁰⁰` is an ellipsoid). -/
def ellipsoid {n q : ℕ} (A : Matrix (Fin n) (Fin q) ℝ) (c : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | ∃ u : Fin q → ℝ, u ⬝ᵥ u ≤ 1 ∧ x = A *ᵥ u + c}

/-- A full-dimensional ellipsoid (p. 258): a set of the form (Ell) with `A` square and
nonsingular. -/
def IsFullDimEllipsoid {n : ℕ} (E : Set (Fin n → ℝ)) : Prop :=
  ∃ (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ), A.det ≠ 0 ∧ E = ellipsoid A c

/-- The normalized volume (p. 259) `Vol(G) = κₙ⁻¹ mesₙ(G)`: Lebesgue measure divided by the
Lebesgue measure `κₙ` of the unit Euclidean ball, so that the unit ball has volume `1`. -/
noncomputable def Vol {n : ℕ} (G : Set (Fin n → ℝ)) : ℝ≥0∞ :=
  volume G / volume (unitBall n)

/-- A solid (p. 259): a closed and bounded convex set with a nonempty interior. -/
def IsSolid {n : ℕ} (S : Set (Fin n → ℝ)) : Prop :=
  IsClosed S ∧ Bornology.IsBounded S ∧ Convex ℝ S ∧ (interior S).Nonempty

/-- `S` is central-symmetric: symmetric with respect to some point `c`, i.e. `x ∈ S ⇒ 2c − x ∈ S`. -/
def IsCentralSymmetric {n : ℕ} (S : Set (Fin n → ℝ)) : Prop :=
  ∃ c : Fin n → ℝ, ∀ x ∈ S, (2 : ℝ) • c - x ∈ S

/-- `E` is a largest-volume full-dimensional ellipsoid contained in `S`. -/
def IsMaxVolInscribed {n : ℕ} (S E : Set (Fin n → ℝ)) : Prop :=
  IsFullDimEllipsoid E ∧ E ⊆ S ∧
    ∀ E' : Set (Fin n → ℝ), IsFullDimEllipsoid E' → E' ⊆ S → Vol E' ≤ Vol E

/-- `E` is a smallest-volume full-dimensional ellipsoid containing `S`. -/
def IsMinVolCircumscribed {n : ℕ} (S E : Set (Fin n → ℝ)) : Prop :=
  IsFullDimEllipsoid E ∧ S ⊆ E ∧
    ∀ E' : Set (Fin n → ℝ), IsFullDimEllipsoid E' → S ⊆ E' → Vol E ≤ Vol E'

/-- `W[Z] = {x | xᵀZx ≤ 1}` (p. 266); a full-dimensional ellipsoid centred at the origin when
`Z ≻ 0`. The ellipsoids `Wᵢ = {x | xᵀBᵢx ≤ 1}` of Problem (O) are `quadSet Bᵢ`. -/
def quadSet {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ) : Set (Fin n → ℝ) :=
  {x | x ⬝ᵥ (Z *ᵥ x) ≤ 1}

/-- `W(Y, y) = {x | (x − y)ᵀYᵀY(x − y) ≤ 1}` of Proposition 4.9.3 (p. 262); a full-dimensional
ellipsoid when `Det Y ≠ 0`. -/
def quadEllipsoid {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | (x - y) ⬝ᵥ ((Yᵀ * Y) *ᵥ (x - y)) ≤ 1}

/-- The arithmetic (Minkowski) sum `W₁ + ⋯ + W_m = {w₁ + ⋯ + w_m | wᵢ ∈ Wᵢ}` (p. 265). -/
def minkowskiSum {m n : ℕ} (W : Fin m → Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {x | ∃ w : Fin m → Fin n → ℝ, (∀ i, w i ∈ W i) ∧ x = ∑ i, w i}

end ModernConvex.Ellipsoids


