-- Prove2me | Definitions.Def_ReplParity_Supplement_IAT
-- name    : ReplParity_Supplement_IAT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:56:01.929143+00:00
-- url     : https://prove2.me/theorems/26886085-f0cc-42bc-9b78-4693893a132c
-- title:
--   Definition 2.3 — $(\gamma,A)$-isoperimetric approximate tiling of $\mathbb R^N$
-- statement:
--   Let $N\ge1$, $0<\gamma<1$ and $A>0$. A **$(\gamma,A)$-isoperimetric approximate tiling (IAT)** of Euclidean $\mathbb R^N$ is a countable family $\{S_a\}_{a\in L}$ of sets labeled by distinct points $a\in L\subseteq\mathbb R^N$ such that each $S_a$ has positive volume, the interiors are pairwise disjoint, each boundary $\partial S_a$ is piecewise smooth, and every integer unit cube $C_w=w+[0,1]^N$, $w\in\mathbb Z^N$, satisfies
--
--   1. (coverage) $\mathrm{vol}_N\big(C_w\setminus\bigcup_a S_a\big)\le\gamma$;
--   2. (surface) $\mathcal H^{N-1}\big(C_w\cap\bigcup_a\partial S_a\big)\le A$;
--   3. (radius) $\|x-a\|_2\le 1/10$ for every $a$ and every $x\in S_a$.
--
--   Here $\mathrm{vol}_N$ is Lebesgue measure and $\mathcal H^{N-1}$ is surface area. $\gamma$ is the uncovered fraction and $A$ the surface bound.
--
--   **Formalization Note** The implicit convention $N\ge1$ excludes the undefined codimension-one measure at $N=0$. $\mathcal H^{N-1}$ is the normalized $(N-1)$-dimensional Hausdorff measure $\frac{\pi^{(N-1)/2}}{\Gamma((N-1)/2+1)\,2^{N-1}}\mu_H^{N-1}$ on $\mathbb R^N$ with the Euclidean metric, the normalization that agrees with surface area (Mathlib's $\mu_H$ is unnormalized). The paper does not define "piecewise smooth boundary"; it is read as: $\partial S_a$ lies in a finite union of images $f_j(K_j)$ of compact sets $K_j\subseteq\mathbb R^{N-1}$ under $C^1$ maps $f_j:\mathbb R^{N-1}\to\mathbb R^N$. Coverage bounds the uncovered volume by $\gamma$, as printed on p.12. Volumes are outer measures in $[0,\infty]$.
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), Definition 2.3, pp.11-12 (PDF pp.13-14), after [HIK+24, Definition 4.6]

import Mathlib

set_option autoImplicit false

namespace ReplParity

namespace Supplement

open MeasureTheory

/-- **Surface area in Euclidean `ℝ^N`: the normalized `(N−1)`-dimensional Hausdorff measure.**
`H^{N−1} = (α_{N−1} / 2^{N−1}) · μH[N−1]`, where `α_s = π^{s/2} / Γ(s/2 + 1)` is the volume of the
unit ball of `ℝ^s` and `μH[s]` is Mathlib's (unnormalized, `diam^s`) Hausdorff measure on
`EuclideanSpace ℝ (Fin N)` with its `ℓ²` metric. With this normalization `H^s` agrees with
`s`-dimensional surface area on `C¹` surfaces. -/
noncomputable def surfaceArea (N : ℕ) : Measure (EuclideanSpace ℝ (Fin N)) :=
  ENNReal.ofReal (Real.sqrt Real.pi ^ (N - 1) / Real.Gamma (((N - 1 : ℕ) : ℝ) / 2 + 1) /
      2 ^ (N - 1)) • μH[((N - 1 : ℕ) : ℝ)]

/-- The closed integer unit cube `C_w = w + [0, 1]^N`, `w ∈ ℤ^N`. -/
def unitCube (N : ℕ) (w : Fin N → ℤ) : Set (EuclideanSpace ℝ (Fin N)) :=
  {x | ∀ i, (w i : ℝ) ≤ x i ∧ x i ≤ (w i : ℝ) + 1}

/-- A piecewise smooth boundary: the topological boundary of `T` lies in a finite union of images
`f_j(K_j)` of compact sets `K_j ⊆ ℝ^{N−1}` under `C¹` maps `f_j : ℝ^{N−1} → ℝ^N`. -/
def HasPiecewiseSmoothBoundary (N : ℕ) (T : Set (EuclideanSpace ℝ (Fin N))) : Prop :=
  ∃ k : ℕ, ∃ f : Fin k → EuclideanSpace ℝ (Fin (N - 1)) → EuclideanSpace ℝ (Fin N),
    ∃ K : Fin k → Set (EuclideanSpace ℝ (Fin (N - 1))),
      (∀ j, ContDiff ℝ 1 (f j)) ∧ (∀ j, IsCompact (K j)) ∧ frontier T ⊆ ⋃ j, f j '' K j

/-- **Definition 2.3 (Isoperimetric approximate tiling [HIK+24]).** Shen, Zhong, *Replicable Parity
Learning: Cubic Sample Complexity and a Geometric Characterization*, STOC 2027 submission (manuscript
sha256 40424491…), Definition 2.3, pp.11–12 (PDF pp.13–14): "Let 0 < γ < 1 and A > 0. A
(γ, A)-isoperimetric approximate tiling (IAT) of ℝ^N is a countable family {S_a} of sets labeled by
points a ∈ ℝ^N. The sets have positive volume, pairwise disjoint interiors, and piecewise smooth
boundaries, and every integer unit cube C_w = w + [0, 1]^N with w ∈ ℤ^N satisfies the following
conditions. (i) (coverage) vol_N(C_w \ ⋃_a S_a) ≤ γ, (ii) (surface) H^{N−1}(C_w ∩ ⋃_a ∂S_a) ≤ A,
and (iii) (radius) ‖x − a‖₂ ≤ 1/10 for every a and every x ∈ S_a. Here vol_N denotes volume and
H^{N−1} denotes surface area."

The family is given by its set of labels `L ⊆ ℝ^N` and the tile map `a ↦ T a`; the tiles are the
sets `T a` with `a ∈ L` (distinct labels, so each tile has its own label).

**Formalization Note.**
* `ℝ^N` is `EuclideanSpace ℝ (Fin N)`; `vol_N` is its Lebesgue measure `volume`, and `H^{N−1}` is
  `surfaceArea N`, the normalized Hausdorff measure (Mathlib's `μH[N−1]` alone is off by an
  `N`-dependent factor). `∂S_a` is the topological boundary `frontier`.
* "Piecewise smooth boundary" (undefined in the paper) is `HasPiecewiseSmoothBoundary`: the
  boundary lies in finitely many `C¹` images of compact subsets of `ℝ^{N−1}`. The field `dim_pos`
  records the implicit positive-dimension convention, avoiding truncated `N - 1` at `N = 0`.
* Coverage (i) bounds the uncovered volume by `γ`, as printed on p.12 (the paper notes that
  [HIK+24]'s Definition 4.6(4) is misprinted).
* Volumes and surface areas are outer measures; they are `ℝ≥0∞`-valued and compared with
  `ENNReal.ofReal γ`, `ENNReal.ofReal A`. -/
structure IsIAT (N : ℕ) (γ A : ℝ) (L : Set (EuclideanSpace ℝ (Fin N)))
    (T : EuclideanSpace ℝ (Fin N) → Set (EuclideanSpace ℝ (Fin N))) : Prop where
  dim_pos : 1 ≤ N
  params : 0 < γ ∧ γ < 1 ∧ 0 < A
  countable : L.Countable
  pos_volume : ∀ a ∈ L, 0 < volume (T a)
  disjoint_interiors : L.Pairwise (fun a b => Disjoint (interior (T a)) (interior (T b)))
  smooth_boundary : ∀ a ∈ L, HasPiecewiseSmoothBoundary N (T a)
  coverage : ∀ w : Fin N → ℤ, volume (unitCube N w \ ⋃ a ∈ L, T a) ≤ ENNReal.ofReal γ
  surface : ∀ w : Fin N → ℤ,
    surfaceArea N (unitCube N w ∩ ⋃ a ∈ L, frontier (T a)) ≤ ENNReal.ofReal A
  radius : ∀ a ∈ L, ∀ x ∈ T a, dist x a ≤ 1 / 10

end Supplement

end ReplParity


