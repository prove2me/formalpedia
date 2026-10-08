-- Prove2me | Definitions.Def_RobustPower_StochGap_SymmetricSets
-- name    : RobustPower_StochGap_SymmetricSets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T16:53:08.957505+00:00
-- url     : https://prove2.me/theorems/8954d118-1cfa-48b1-a739-e1f9a8476477
-- title:
--   Definitions 1.1–1.3 and (2.5)–(2.7) — hypercubes, symmetric and positive sets, the bounding box
-- statement:
--   This file fixes the geometric vocabulary of Bertsimas and Goyal for subsets of $\mathbb R^n$.
--
--   1. **Hypercube** (Definition 1.1). A set $H\subseteq\mathbb R^n$ is a hypercube if there are vectors $l\le u$ with
--   $$H=\{x\in\mathbb R^n : l_i\le x_i\le u_i,\ i=1,\dots,n\}.$$
--   2. **Symmetric set** (Definition 1.2). A set $P$ in an additive group is symmetric about $u^0$ if $u^0\in P$ and, for every $z$,
--   $$u^0+z\in P\iff u^0-z\in P .$$
--   $P$ is symmetric if it is symmetric about some point $u^0$, its point of symmetry.
--   3. **Positive set** (Definition 1.3). A convex set $P\subseteq\mathbb R^n_+$ is positive if there is a convex symmetric set $S\subseteq\mathbb R^n_+$ with $P\subseteq S$ whose point of symmetry belongs to $P$.
--   4. **Bounding box** ((2.5)–(2.7)). For $S\subseteq\mathbb R^n$ and each coordinate $j$, $x^h_j=\sup_{x\in S}x_j$ and $x^l_j=\inf_{x\in S}x_j$, and $H=\{x : x^l_j\le x_j\le x^h_j,\ j=1,\dots,n\}$.
--
--   Symmetric sets are the uncertainty sets of the paper's main theorem; the bounding box is the device by which the point of symmetry is located (Lemmas 2.2 and 2.3).
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ` with the componentwise order. The paper writes $\max$ and $\min$ in (2.5)–(2.6); the file uses `sSup` and `sInf`, which agree with them when attained and are only meaningful for nonempty bounded $S$ (every statement that uses them assumes this). Positivity bundles the convexity of $P$ and $P\subseteq\mathbb R^n_+$, which Definition 1.3 presupposes.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, pp. 5–6 Definitions 1.1–1.3, p. 12 displays (2.5)–(2.7)

import Mathlib

namespace RobustPower.StochGap

/-- Definition 1.1 (p. 5): `H ⊆ ℝⁿ` is a hypercube if `H = {x | lᵢ ≤ xᵢ ≤ uᵢ ∀ i}` for some
`l ≤ u`. -/
def IsHypercube {n : ℕ} (H : Set (Fin n → ℝ)) : Prop :=
  ∃ l u : Fin n → ℝ, l ≤ u ∧ H = Set.Icc l u

/-- Definition 1.2 (p. 5), with a named point of symmetry: `u` belongs to `P` and, for every
`z`, `u + z ∈ P ↔ u - z ∈ P` (display (1.7)). -/
def IsSymmetricAbout {E : Type*} [AddCommGroup E] (P : Set E) (u : E) : Prop :=
  u ∈ P ∧ ∀ z : E, u + z ∈ P ↔ u - z ∈ P

/-- Definition 1.2 (p. 5): `P` is symmetric if it is symmetric about some point `u⁰ ∈ P`. -/
def IsSymmetric {E : Type*} [AddCommGroup E] (P : Set E) : Prop :=
  ∃ u : E, IsSymmetricAbout P u

/-- Definition 1.3 (p. 6): a convex set `P ⊆ ℝⁿ₊` is positive if there is a convex symmetric
set `S ⊆ ℝⁿ₊` with `P ⊆ S` whose point of symmetry lies in `P`. -/
def IsPositive {n : ℕ} (P : Set (Fin n → ℝ)) : Prop :=
  Convex ℝ P ∧ (∀ x ∈ P, 0 ≤ x) ∧
    ∃ S : Set (Fin n → ℝ), Convex ℝ S ∧ (∀ x ∈ S, 0 ≤ x) ∧ P ⊆ S ∧
      ∃ u : Fin n → ℝ, IsSymmetricAbout S u ∧ u ∈ P

/-- Display (2.5) (p. 12): `xʰⱼ`, the largest `j`-th coordinate of a point of `S`
(a supremum; it is a maximum when attained). Meaningful for nonempty bounded `S`. -/
noncomputable def xh {n : ℕ} (S : Set (Fin n → ℝ)) : Fin n → ℝ :=
  fun j => sSup ((fun x : Fin n → ℝ => x j) '' S)

/-- Display (2.6) (p. 12): `xˡⱼ`, the smallest `j`-th coordinate of a point of `S`
(an infimum; it is a minimum when attained). Meaningful for nonempty bounded `S`. -/
noncomputable def xl {n : ℕ} (S : Set (Fin n → ℝ)) : Fin n → ℝ :=
  fun j => sInf ((fun x : Fin n → ℝ => x j) '' S)

/-- Display (2.7) (p. 12): the hypercube `H = {x | xˡⱼ ≤ xⱼ ≤ xʰⱼ ∀ j}`. -/
noncomputable def boundingBox {n : ℕ} (S : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  Set.Icc (xl S) (xh S)

end RobustPower.StochGap


