-- Prove2me | Definitions.Def_HarmonicCalib_Principal_Geometry
-- name    : HarmonicCalib_Principal_Geometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T01:05:12.365423+00:00
-- url     : https://prove2.me/theorems/4ce69527-f068-4e18-bda3-2462fc0ca885
-- title:
--   Norm unit balls, polar, center of mass, and the sets $B_1^d, B_2^d, B_\infty^d, [0,1]^d, \Delta_d$
-- statement:
--   All sets live in $\mathbb R^d$, represented as `EuclideanSpace ℝ (Fin d)` with the standard inner product $\langle x, y\rangle = \sum_i x_i y_i$.
--
--   * A **norm unit ball** is a set $L \subseteq \mathbb R^d$ that is compact, convex, centrally symmetric ($x \in L \Rightarrow -x \in L$, i.e. $L = -L$) and has $0$ in its interior. Its norm is the gauge $\|x\|_L = \inf\{\lambda > 0 : x \in \lambda L\}$ (Mathlib's `gauge L`).
--   * The **polar** of $L$ is $L^\circ = \{ r \in \mathbb R^d : \langle \ell, r\rangle \le 1 \text{ for every } \ell \in L\}$.
--   * The **center of mass** $c_Y$ of a set $Y$ is the barycenter of the uniform measure on $Y$ relative to its affine hull: with $k$ the dimension of the affine span of $Y$ and $\mathcal H^k$ the $k$-dimensional Hausdorff measure, $c_Y = \mathcal H^k(Y)^{-1} \int_Y x \, d\mathcal H^k(x)$. For a full-dimensional body this is the Lebesgue barycenter; for the simplex $\Delta_d$ (dimension $d-1$) it is $(1/d,\dots,1/d)$; for a single point it is that point. (The source writes "the center of mass of $Y$" without specifying the measure; Lebesgue measure on $\mathbb R^d$ would give $0/0$ for $\Delta_d$.)
--   * The **centered forecast set** is $\tilde Y = Y - c_Y = \{ y - c_Y : y \in Y\}$.
--   * $B_1^d = \{x : \sum_i |x_i| \le 1\}$, $B_2^d = \{x : \sum_i x_i^2 \le 1\}$, $B_\infty^d = \{x : |x_i| \le 1 \ \forall i\}$, the cube $[0,1]^d = \{x : 0 \le x_i \le 1\ \forall i\}$ and the probability simplex $\Delta_d = \{x : x_i \ge 0\ \forall i,\ \sum_i x_i = 1\}$.
-- source:
--   Fishelson and Mohri (2026), High-Dimensional Online Calibration from Harmonic Weights, arXiv:2610.07740 (version dated October 29, 2026; PDF SHA256 62ac31a3…), pp. 3–5 (protocol, polar, center of mass), Theorem 1.1 p. 3, Lemma 3.3 p. 14

import Mathlib

open scoped MeasureTheory InnerProductSpace

namespace HarmonicCalib.Principal

/-! # Geometry of forecast sets and error norms (Fishelson–Mohri 2026, pp. 3–5)

Everything lives in `ℝ^d`, modelled as `EuclideanSpace ℝ (Fin d)` (coordinates `x i`, the standard
inner product `⟪x, y⟫_ℝ = ∑ i, x i * y i`). -/

/-- A *norm unit ball* `L ⊆ ℝ^d` (p. 4): compact, convex, centrally symmetric (`-x ∈ L` whenever
`x ∈ L`, i.e. `L = -L`), with `0` in its interior. Its norm `‖·‖_L` is the gauge (Minkowski
functional) `gauge L`. -/
def IsNormBall {d : ℕ} (L : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  IsCompact L ∧ Convex ℝ L ∧ (∀ x, x ∈ L → -x ∈ L) ∧ (0 : EuclideanSpace ℝ (Fin d)) ∈ interior L

/-- The polar `L° = {r ∈ ℝ^d : ⟨ℓ, r⟩ ≤ 1 for every ℓ ∈ L}` (p. 4). -/
def polar {d : ℕ} (L : Set (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d)) :=
  {r | ∀ l ∈ L, ⟪l, r⟫_ℝ ≤ 1}

/-- The center of mass `c_Y` of a set `Y ⊆ ℝ^d` (p. 4): the barycenter of the uniform measure on
`Y` relative to its affine hull. With `k` the dimension of the affine span of `Y`, the uniform
measure is the `k`-dimensional Hausdorff measure `μH[k]` restricted to `Y` (on a `k`-dimensional
affine subspace this is `k`-dimensional Lebesgue measure), so
`c_Y = (μH[k] Y)⁻¹ ∫_Y x dμH[k](x)`. For a full-dimensional body this is the usual Lebesgue
barycenter; for the simplex `Δ_d` (dimension `d - 1`) it is `(1/d, …, 1/d)`; for a point it is
the point. -/
noncomputable def centerOfMass {d : ℕ} (Y : Set (EuclideanSpace ℝ (Fin d))) :
    EuclideanSpace ℝ (Fin d) :=
  (μH[(Module.finrank ℝ (affineSpan ℝ Y).direction : ℝ)] Y).toReal⁻¹ •
    ∫ x in Y, x ∂μH[(Module.finrank ℝ (affineSpan ℝ Y).direction : ℝ)]

/-- The centered forecast set `Ỹ = Y - c_Y` (p. 4). -/
noncomputable def centered {d : ℕ} (Y : Set (EuclideanSpace ℝ (Fin d))) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  (fun y => y - centerOfMass Y) '' Y

/-- `B_1^d = {x ∈ ℝ^d : ∑ᵢ |xᵢ| ≤ 1}`, the `ℓ₁` unit ball. -/
def ballOne (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∑ i, |x i| ≤ 1}

/-- `B_2^d = {x ∈ ℝ^d : ∑ᵢ xᵢ² ≤ 1}`, the Euclidean unit ball. -/
def ballTwo (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∑ i, (x i) ^ 2 ≤ 1}

/-- `B_∞^d = {x ∈ ℝ^d : |xᵢ| ≤ 1 for all i}`, the `ℓ_∞` unit ball. -/
def ballInf (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, |x i| ≤ 1}

/-- The cube `[0,1]^d` (multi-event forecasting). -/
def unitCube (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}

/-- The probability simplex `Δ_d = {x ∈ ℝ^d : xᵢ ≥ 0, ∑ᵢ xᵢ = 1}` (multi-class forecasting). -/
def simplex (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

end HarmonicCalib.Principal


