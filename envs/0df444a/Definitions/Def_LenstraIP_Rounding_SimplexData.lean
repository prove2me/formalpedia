-- Prove2me | Definitions.Def_LenstraIP_Rounding_SimplexData
-- name    : LenstraIP_Rounding_SimplexData
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:52:49.792223+00:00
-- url     : https://prove2.me/theorems/f0860aca-b45b-4cac-8825-36722f6415ae
-- title:
--   §2 objects: simplex volume |det M|/n!, regular simplex, centroid, the sets T_c, and the model of T_c in ℝⁿ⁺¹
-- statement:
--   Work in $\mathbb R^n$ with the Euclidean length $|\cdot|$. This file introduces the objects of the second stage of §2 of Lenstra's paper, together with the coordinates in $\mathbb R^{n+1}$ used in the proof of its LEMMA.
--
--   1. **Volume of a simplex.** For points $w_0, w_1, \dots, w_n \in \mathbb R^n$,
--   $$\mathrm{vol}(w_0, w_1, \dots, w_n) = \frac{|\det M|}{n!},$$
--   where $M$ is the $n\times n$ matrix with column vectors $w_1 - w_0, \dots, w_n - w_0$. This is the $n$-dimensional volume of the simplex they span (zero when the points are affinely dependent).
--   2. **Regular simplex.** The points $z_0, \dots, z_n$ span a *regular* $n$-simplex when all pairwise distances $|z_i - z_j|$, $i \neq j$, are equal to one positive number.
--   3. **Centroid.** $p = (n+1)^{-1} \sum_{j=0}^n z_j$.
--   4. **The sets $T_c$.** For $c \in \mathbb R$ and points $z_0, \dots, z_n$,
--   $$T_c = \{ x \in \mathbb R^n : \mathrm{vol}(z_0, \dots, z_{i-1}, x, z_{i+1}, \dots, z_n) \le c \cdot \mathrm{vol}(z_0, \dots, z_n) \text{ for all } i \in \{0, 1, \dots, n\} \}.$$
--   5. **The model in $\mathbb R^{n+1}$.** Let $e_0, \dots, e_n$ be the standard basis of $\mathbb R^{n+1}$ (the paper calls them $z_0, \dots, z_n$ after identifying $\mathbb R^n$ with the hyperplane $\sum_j r_j = 1$). The model objects are: the centroid $p = \big(\tfrac{1}{n+1}, \dots, \tfrac{1}{n+1}\big)$; the set
--   $$T_c^{\mathrm{model}} = \Big\{ (r_j)_{j=0}^n \in \mathbb R^{n+1} : |r_j| \le c \text{ for } 0 \le j \le n, \text{ and } \sum_{j=0}^n r_j = 1 \Big\};$$
--   with $m = \lfloor n/2 \rfloor$, the point
--   $$e_0 - c\sum_{j=1}^m e_j + c\sum_{j=m+1}^n e_j \ (n = 2m), \qquad (1-c)e_0 - c\sum_{j=1}^m e_j + c\sum_{j=m+1}^n e_j \ (n = 2m+1);$$
--   the operation of permuting the coordinates of a point of $\mathbb R^{n+1}$ by a permutation $\sigma$ of $\{0, \dots, n\}$, $(x_j)_j \mapsto (x_{\sigma(j)})_j$; the standard simplex $S = \mathrm{conv}\{e_0, \dots, e_n\}$; and the point $(0, 1/n, 1/n, \dots, 1/n)$.
--
--   The goal theorem and every milestone of the mission are stated in these objects.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` and $\mathbb R^{n+1}$ is `EuclideanSpace ℝ (Fin (n+1))`, so distances are Euclidean and balls are round. Vertices are indexed by `Fin (n+1)`, matching $0, \dots, n$. The volume keeps the paper's normalisation $1/n!$ (p. 542); $T_c$ only uses ratios of volumes, so the normalisation does not affect it. `Tset c z` is defined for every real $c$ and every family $z$; the theorems add $c \ge 1$ and regularity where the paper has them. In the model point, coordinate $0$ is $1$ (n even) or $1-c$ (n odd), coordinates $1, \dots, m$ are $-c$, and coordinates $m+1, \dots, n$ are $c$, with $m$ = `n / 2` (natural-number division) in both cases.
-- source:
--   Lenstra, Integer Programming with a Fixed Number of Variables, Math. Oper. Res. 8 (1983), §2: p. 542 the volume |det M|/n!; p. 543 the regular n-simplex, p = (n + 1)⁻¹ Σ τ(vⱼ), the set T_c, and (proof of the LEMMA) the model p, T_c in ℝⁿ⁺¹; p. 544 the point z₀ − c Σ zⱼ + c Σ zⱼ / (1 − c)z₀ − …, and the point (0, 1/n, …, 1/n)

import Mathlib

namespace LenstraIP.Rounding

/-- The volume of the `n`-simplex spanned by `w 0, w 1, …, w n` in `ℝⁿ` (Lenstra 1983, §2,
p. 542): `|det M| / n!`, where `M` is the matrix with column vectors `w 1 − w 0, …, w n − w 0`.
Column `j` of `M` is `w (j+1) − w 0`, so its `(i, j)` entry is the `i`-th coordinate of that
vector. -/
noncomputable def simplexVol {n : ℕ} (w : Fin (n + 1) → EuclideanSpace ℝ (Fin n)) : ℝ :=
  |Matrix.det (Matrix.of fun i j : Fin n => (w j.succ - w 0) i)| / (n.factorial : ℝ)

/-- The points `z 0, …, z n` span a **regular** simplex (§2, p. 543): all pairwise Euclidean
distances between distinct vertices are equal to one positive number `s`. -/
def IsRegular {n : ℕ} (z : Fin (n + 1) → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ s : ℝ, 0 < s ∧ ∀ i j, i ≠ j → dist (z i) (z j) = s

/-- The centroid `p = (n + 1)⁻¹ Σ_{j=0}^n z j` of the points `z 0, …, z n` (§2, p. 543). -/
noncomputable def centroid {n : ℕ} (z : Fin (n + 1) → EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  ((n : ℝ) + 1)⁻¹ • ∑ j, z j

/-- The set `T_c` of §2, p. 543: the points `x ∈ ℝⁿ` such that, for every `i ∈ {0, …, n}`,
replacing the vertex `z i` by `x` gives a simplex of volume at most `c · vol(z 0, …, z n)`. -/
def Tset {n : ℕ} (c : ℝ) (z : Fin (n + 1) → EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i, simplexVol (Function.update z i x) ≤ c * simplexVol z}

/-- The centroid `p = (1/(n+1), …, 1/(n+1))` of the standard basis of `ℝⁿ⁺¹`, the model of the
centroid in the proof of the LEMMA (§2, p. 543). -/
noncomputable def pM (n : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun _ => ((n : ℝ) + 1)⁻¹)

/-- The model of `T_c` in the hyperplane `Σ rⱼ = 1` of `ℝⁿ⁺¹` (§2, p. 543):
`{(rⱼ)_{j=0}^n : |rⱼ| ≤ c for 0 ≤ j ≤ n, and Σ rⱼ = 1}`. -/
def modelT (n : ℕ) (c : ℝ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  {r | ∑ j, r j = 1 ∧ ∀ j, |r j| ≤ c}

/-- The point of §2, p. 544, whose coordinate permutations span `T_c` in the model: with
`m = ⌊n/2⌋`, it is `z₀ − c Σ_{j=1}^m zⱼ + c Σ_{j=m+1}^n zⱼ` if `n = 2m` and
`(1 − c)z₀ − c Σ_{j=1}^m zⱼ + c Σ_{j=m+1}^n zⱼ` if `n = 2m + 1`, where `z₀, …, zₙ` is the standard
basis of `ℝⁿ⁺¹`. -/
noncomputable def modelPt (n : ℕ) (c : ℝ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun j : Fin (n + 1) =>
    if (j : ℕ) = 0 then (if Even n then 1 else 1 - c)
    else if (j : ℕ) ≤ n / 2 then -c else c)

/-- The point obtained from `x ∈ ℝⁿ⁺¹` by permuting its coordinates with `σ`. -/
def permuteCoords {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun j => x (σ j))

/-- The standard simplex `S` of the model: the convex hull of the standard basis vectors
`z₀, …, zₙ` of `ℝⁿ⁺¹`. -/
def modelS (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  convexHull ℝ (Set.range fun j : Fin (n + 1) => EuclideanSpace.single j (1 : ℝ))

/-- The point `(0, 1/n, 1/n, …, 1/n)` of `ℝⁿ⁺¹` (§2, p. 544): the centroid of the facet of the
standard simplex opposite to `z₀`. -/
noncomputable def facetPt (n : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun j : Fin (n + 1) => if (j : ℕ) = 0 then 0 else (n : ℝ)⁻¹)

end LenstraIP.Rounding


