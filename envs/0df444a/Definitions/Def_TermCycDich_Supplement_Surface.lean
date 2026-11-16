-- Prove2me | Definitions.Def_TermCycDich_Supplement_Surface
-- name    : TermCycDich_Supplement_Surface
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:45:07.109259+00:00
-- url     : https://prove2.me/theorems/bb1e7fd6-58f2-4ff3-a26a-14719177a13c
-- title:
--   Surfaces with or without boundary and Euler genus less than $g$
-- statement:
--   A **surface** is a compact Hausdorff space $\Sigma$ in which every point has an open neighbourhood homeomorphic to a relatively open subset of the closed half-plane $\{x\in\mathbb R^2 : x_1\ge 0\}$: a compact $2$-dimensional manifold with or without boundary. Connectedness is not required.
--
--   A surface $\Sigma$ has **Euler genus less than $g$** if, for some $h,c\in\mathbb N$ with $2h+c<g$, it is homeomorphic to the sphere with $h$ handles and $c$ crosscaps, $\Sigma(h,c)$, with the interiors of finitely many pairwise disjoint closed discs removed. Equivalently, capping every boundary circle of $\Sigma$ by a disc yields a closed surface of Euler genus $2h+c<g$.
--
--   These are the surfaces of the paper's $\Sigma$-renditions: villages live on a surface of Euler genus less than $9(6(b+1)^2+1)^2$, and the annulus combing lemma holds on every surface.
--
--   **Formalization Note** Charts are those of the public `GMSTFramework` surfaces, without its path-connectedness condition. $\Sigma(h,c)$ is the public fundamental-polygon construction `SigmaHC h c`; no uniqueness of $(h,c)$ is assumed (Mathlib has no classification of surfaces).
-- source:
--   Bentert–Cavallaro–Wiederrecht, A Dichotomy for Terminal Cyclability, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), §2.1 "Surfaces", p.16 (PDF 18)

import Mathlib
import Definitions.Def_GMSTFramework_LocalStructure_Surfaces

open Topology

noncomputable section

namespace TermCycDich

namespace Supplement

open GMSTFramework.LocalStructure

/-!
# Surfaces (with or without boundary) and their Euler genus

Bentert–Cavallaro–Wiederrecht, *A Dichotomy for Terminal Cyclability*, arXiv:2611.06234 (held
version, sha256 34a10f1a…4d4ea1), §2.1 "Surfaces", p.16 (PDF 18): "By a surface we mean a compact
2-dimensional manifold Σ with or without boundary."

* `IsSurface X`: `X` is Hausdorff and compact, and every point has an open neighbourhood
  homeomorphic to a relatively open subset of the closed half-plane (charts of the public
  `GMSTFramework.LocalStructure.halfPlane`). Unlike the public `GMSTFramework` surface, no
  connectedness is required: the paper does not require it (p.20: "where Σ is connected" is
  stated separately), and Theorem 5.2 quantifies over every surface.
* `HasEulerGenusLT X g`: `X` is homeomorphic to `Σ(h,c)` (the public `SigmaHC h c`, the sphere with
  `h` handles and `c` crosscaps, whose Euler genus is `2h + c`) with the interiors of finitely
  many pairwise disjoint closed discs removed, for some `h, c` with `2h + c < g`.

**Formalization Note** The Euler genus of a surface with boundary is that of the closed surface
obtained by capping every boundary circle with a disc; removing the interiors of `k` disjoint
closed discs from `Σ(h,c)` is exactly the inverse operation, so "Euler genus `< g`" is this
relation. The relation presupposes a connected surface, as Euler genus does. No uniqueness of
`(h, c)` is assumed (Mathlib has no classification of surfaces).
-/

/-- A surface: a compact Hausdorff 2-manifold, possibly with boundary and possibly disconnected. -/
def IsSurface (X : Type) [TopologicalSpace X] : Prop :=
  T2Space X ∧ CompactSpace X ∧
    ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ W : Set (EuclideanSpace ℝ (Fin 2)), W ⊆ halfPlane ∧
        (∃ O : Set (EuclideanSpace ℝ (Fin 2)), IsOpen O ∧ W = O ∩ halfPlane) ∧
        Nonempty (U ≃ₜ W)

/-- `X` has Euler genus less than `g`: `X ≅ Σ(h,c) ∖ (int D₁ ∪ ⋯ ∪ int D_k)` for pairwise
disjoint closed discs `Dᵢ` (with boundary circles `Tᵢ`) of `Σ(h,c)`, where `2h + c < g`. -/
def HasEulerGenusLT (X : Type) [TopologicalSpace X] (g : ℕ) : Prop :=
  ∃ h c : ℕ, 2 * h + c < g ∧ ∃ (k : ℕ) (D T : Fin k → Set (SigmaHC h c)),
    (∀ i, IsDiskWithBoundary (D i) (T i)) ∧ Pairwise (fun i j => Disjoint (D i) (D j)) ∧
    Nonempty (X ≃ₜ ((Set.univ \ ⋃ i, (D i \ T i) : Set (SigmaHC h c))))

end Supplement

end TermCycDich


