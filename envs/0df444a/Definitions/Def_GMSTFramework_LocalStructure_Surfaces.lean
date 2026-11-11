-- Prove2me | Definitions.Def_GMSTFramework_LocalStructure_Surfaces
-- name    : GMSTFramework_LocalStructure_Surfaces
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:00:15.125564+00:00
-- url     : https://prove2.me/theorems/e476510a-c201-4fa6-8ec1-b9f82410e784
-- title:
--   Surfaces, closed disks, arcs and curves, the surfaces $\Sigma(h,c)$, Euler-genus, orientability, embeddings of graphs (§2.1)
-- statement:
--   A **surface** is an arc-connected compact (Hausdorff) 2-manifold, possibly with boundary; its boundary $\mathrm{bd}(\Sigma)$ consists of finitely many circles (cuffs). A **closed disk** in a space is the image of an injective continuous map of the closed unit disk, its **boundary** the image of the unit circle; an **arc** from $a$ to $b$ is the image of an injective path; a (simple) **closed curve** is the image of an injective loop $S^1\to X$, **contractible** if the loop is homotopic to a constant map.
--
--   $\Sigma(h,c)$ is the surface obtained from the sphere by adding $h$ handles and $c$ crosscaps. A surface $\Sigma$ has **Euler-genus** $g$ if $\Sigma\cong\Sigma(h,c)$ with $c\le 2$ and $2h+c=g$ (Dyck's theorem); it is **non-orientable** if $\Sigma\cong\Sigma(h,c)$ with $c\in\{1,2\}$. A graph $H$ **embeds** in $\Sigma$ if it has a drawing: distinct points for the vertices, for every edge an arc between the points of its ends whose interior avoids all vertex points, arcs of distinct edges meeting only in common ends.
--
--   **Formalization Note.** `SigmaHC h c` is built concretely as the fundamental polygon with boundary word $a_1b_1a_1^{-1}b_1^{-1}\cdots c_1c_1\cdots c_cc_c$ (the word $aa^{-1}$ for the sphere): the closed unit disk of $\mathbb C$ with its boundary cut into equal arcs glued in pairs, with the quotient topology; it is defined for every $c\in\mathbb N$. Mathlib has no classification of surfaces, so `HasEulerGenus` and `IsNonOrientable` are relations (via homeomorphism to some $\Sigma(h,c)$) and uniqueness is never assumed. Interior points of a subspace are those with a relatively open neighbourhood homeomorphic to $\mathbb R^2$; `manifoldBd` is the rest. `ArrangedAlong e pts` says that the points occur at increasing angles along the loop $e$ (one of the two cyclic orders).
-- source:
--   Gorsky, Protopapas, Wiederrecht, A unifying framework for Graph Minor Structure Theorems with polynomial bounds, STOC 2027 submission (manuscript sha256 b2ee466d…), p. 11–12 (PDF 14–15), "Surfaces"; p. 85 (PDF 88)

import Mathlib

open Topology

noncomputable section

namespace GMSTFramework.LocalStructure

/-!
# Surfaces, disks, curves, the surfaces `Σ(h,c)`, Euler-genus, orientability, graph embeddings

Gorsky, Protopapas, Wiederrecht, *A unifying framework for Graph Minor Structure Theorems with
polynomial bounds*, STOC 2027 submission (manuscript sha256 b2ee466d…), §2.1 "Surfaces",
p. 11–12 (PDF 14–15); "`K_t` does not embed in `Σ`", p. 85 (PDF 88).

* `IsInteriorPoint S x`: `x ∈ S` has a neighbourhood in `S` (open in `S`) homeomorphic to `ℝ²`.
  `manifoldBd S` is the set of points of `S` that are not interior points of `S`; for a surface this
  is `bd(Σ)`, for a closed disk its boundary circle.
* `IsSurface X`: an arc-connected (path-connected; the space is Hausdorff), compact, Hausdorff
  2-manifold possibly with boundary: every point has an open neighbourhood homeomorphic to an open
  subset of the closed half-plane. Its boundary is a compact 1-manifold, i.e. finitely many circles
  (the cuffs). `IsClosedSurface X`: a surface without boundary.
* `TheDisk` is the closed unit disk of `ℂ`, `TheSphere` the unit sphere of `ℝ³`.
* `IsDiskWithBoundary D T`: `D ⊆ X` is the image of an embedding of the closed unit disk and `T` is
  the image of its boundary circle; `IsClosedDisk D`.
* `IsArc L a b`: `L` is the image of an injective path from `a` to `b`. `IsSimpleClosedCurve T`:
  `T` is the image of an injective loop `S¹ → X`; `IsContractibleCurve T`: moreover the loop is
  homotopic to a constant map.
* `SigmaHC h c` is **the surface obtained from the sphere by adding `h` handles and `c` crosscaps**,
  built concretely as the fundamental polygon with word
  `a₁b₁a₁⁻¹b₁⁻¹ ⋯ a_hb_ha_h⁻¹b_h⁻¹ c₁c₁ ⋯ c_cc_c` (the word `aa⁻¹`, i.e. the sphere, when
  `h = c = 0`): the closed unit disk, its boundary split into `N` equal arcs, paired arcs glued
  according to the word, with the quotient topology. It is defined for every `c ∈ ℕ`
  (Proposition 8.4 uses every `c`).
* Mathlib has no classification of surfaces, so the Euler-genus and orientability are relations:
  `HasEulerGenus X g` iff `X ≅ Σ(h,c)` for some `(h,c) ∈ ℕ × [0,2]` with `2h + c = g` (Dyck's
  theorem makes the pairs `c ≤ 2` cover all closed surfaces); `IsNonOrientable X` iff
  `X ≅ Σ(h,c)` with `c ∈ {1,2}`. Uniqueness is never assumed.
* `EmbedsIn H X`: `H` has a drawing in `X`: distinct points for the vertices, and for every edge an
  arc between its ends whose interior avoids the vertex points; arcs of distinct edges meet only in
  common ends.
-/

section Topology

variable {X : Type} [TopologicalSpace X]

/-- `x ∈ S` is an interior point of the subspace `S`: some neighbourhood of `x`, open in `S`, is
homeomorphic to the plane `ℝ²`. -/
def IsInteriorPoint (S : Set X) (x : X) : Prop :=
  x ∈ S ∧ ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    Nonempty ((U ∩ S : Set X) ≃ₜ EuclideanSpace ℝ (Fin 2))

/-- The manifold boundary of a subspace `S`: its points that are not interior points of `S`. -/
def manifoldBd (S : Set X) : Set X := {x | x ∈ S ∧ ¬ IsInteriorPoint S x}

/-- The closed half-plane `{x ∈ ℝ² : x₁ ≥ 0}`. -/
def halfPlane : Set (EuclideanSpace ℝ (Fin 2)) := {x | 0 ≤ x 1}

/-- A surface: a nonempty, path-connected, compact, Hausdorff 2-manifold possibly with boundary
(every point has an open neighbourhood homeomorphic to a relatively open subset of the closed
half-plane). -/
def IsSurface (X : Type) [TopologicalSpace X] : Prop :=
  T2Space X ∧ CompactSpace X ∧ PathConnectedSpace X ∧
    ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ W : Set (EuclideanSpace ℝ (Fin 2)), W ⊆ halfPlane ∧
        (∃ O : Set (EuclideanSpace ℝ (Fin 2)), IsOpen O ∧ W = O ∩ halfPlane) ∧
        Nonempty (U ≃ₜ W)

/-- The boundary `bd(Σ)` of a space (as a subspace of itself). -/
def surfaceBd (X : Type) [TopologicalSpace X] : Set X := manifoldBd (Set.univ : Set X)

/-- A surface without boundary. -/
def IsClosedSurface (X : Type) [TopologicalSpace X] : Prop :=
  IsSurface X ∧ surfaceBd X = ∅

/-- The closed unit disk in `ℂ`. -/
abbrev TheDisk : Set ℂ := Metric.closedBall (0 : ℂ) 1

/-- The unit sphere of `ℝ³` ("the sphere"). -/
abbrev TheSphere : Set (EuclideanSpace ℝ (Fin 3)) := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- `D` is a closed disk in `X` with boundary circle `T`: the image of an injective continuous map of
the closed unit disk, `T` being the image of the unit circle. -/
def IsDiskWithBoundary (D T : Set X) : Prop :=
  ∃ e : C(TheDisk, X), Function.Injective e ∧ Set.range e = D ∧
    e '' {z : TheDisk | ‖(z : ℂ)‖ = 1} = T

/-- `D` is a closed disk in `X`. -/
def IsClosedDisk (D : Set X) : Prop := ∃ T : Set X, IsDiskWithBoundary D T

/-- `L` is an arc from `a` to `b`: the image of an injective path from `a` to `b`. -/
def IsArc (L : Set X) (a b : X) : Prop :=
  ∃ γ : C(unitInterval, X), Function.Injective γ ∧ Set.range γ = L ∧
    γ 0 = a ∧ γ 1 = b

/-- `T` is a (simple) closed curve: the image of an injective loop. -/
def IsSimpleClosedCurve (T : Set X) : Prop :=
  ∃ γ : C(Circle, X), Function.Injective γ ∧ Set.range γ = T

/-- `T` is a contractible closed curve: the image of an injective loop that is homotopic to a
constant map. -/
def IsContractibleCurve (T : Set X) : Prop :=
  ∃ γ : C(Circle, X), Function.Injective γ ∧ Set.range γ = T ∧
    ∃ x : X, γ.Homotopic (ContinuousMap.const Circle x)

/-- Three points of the unit circle occur in positive (anticlockwise) cyclic order. -/
def CyclicPositive (z₁ z₂ z₃ : Circle) : Prop :=
  ∃ θ₁ θ₂ θ₃ : ℝ, θ₁ < θ₂ ∧ θ₂ < θ₃ ∧ θ₃ < θ₁ + 2 * Real.pi ∧
    Circle.exp θ₁ = z₁ ∧ Circle.exp θ₂ = z₂ ∧ Circle.exp θ₃ = z₃

/-- The points `x₀, …, x_{n-1}` occur in this cyclic order along the closed curve parametrised by
the injective loop `e` (anticlockwise with respect to `e`). -/
def ArrangedAlong (e : Circle → X) (pts : List X) : Prop :=
  ∃ θ : Fin pts.length → ℝ, StrictMono θ ∧ (∀ i, 0 ≤ θ i ∧ θ i < 2 * Real.pi) ∧
    ∀ i, e (Circle.exp (θ i)) = pts.get i

end Topology

/-! ### The surfaces `Σ(h,c)` -/

/-- The boundary word of the fundamental polygon of the sphere with `h` handles and `c` crosscaps:
letters are natural numbers, `true` = the letter, `false` = its inverse. -/
def polygonWord (h c : ℕ) : List (ℕ × Bool) :=
  if h = 0 ∧ c = 0 then [(0, true), (0, false)]
  else
    ((List.range h).flatMap fun i =>
        [(2 * i, true), (2 * i + 1, true), (2 * i, false), (2 * i + 1, false)]) ++
      ((List.range c).flatMap fun j => [(2 * h + j, true), (2 * h + j, true)])

/-- The point at local (anticlockwise) parameter `u ∈ [0,1]` of the `j`-th of `N` equal boundary
arcs of the unit disk. -/
def polygonEdgePoint (N j : ℕ) (u : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (((j : ℝ) + u) / (N : ℝ) : ℝ))

/-- The gluing relation of the fundamental polygon of `w`: the point at parameter `u` of arc `j` is
glued to the point at parameter `u'` of a different arc `j'` carrying the same letter, when their
positions along the letter agree (the position is `u` for a letter and `1 - u` for an inverse). -/
def polygonRel (w : List (ℕ × Bool)) (x y : TheDisk) : Prop :=
  ∃ (j j' : Fin w.length) (u u' : ℝ),
    j ≠ j' ∧ (w.get j).1 = (w.get j').1 ∧ 0 ≤ u ∧ u ≤ 1 ∧ 0 ≤ u' ∧ u' ≤ 1 ∧
    (x : ℂ) = polygonEdgePoint w.length j u ∧ (y : ℂ) = polygonEdgePoint w.length j' u' ∧
    (if (w.get j).2 then u else 1 - u) = (if (w.get j').2 then u' else 1 - u')

/-- `Σ(h,c)`: the surface obtained from the sphere by adding `h` handles and `c` crosscaps, as the
quotient of the closed disk by the gluing of its fundamental polygon. -/
def SigmaHC (h c : ℕ) : Type := Quot (polygonRel (polygonWord h c))

instance (h c : ℕ) : TopologicalSpace (SigmaHC h c) :=
  inferInstanceAs (TopologicalSpace (Quot (polygonRel (polygonWord h c))))

/-- `X` has Euler-genus `g`: `X` is homeomorphic to `Σ(h,c)` for some `h` and `c ≤ 2` with
`2h + c = g`. -/
def HasEulerGenus (X : Type) [TopologicalSpace X] (g : ℕ) : Prop :=
  ∃ h c : ℕ, c ≤ 2 ∧ 2 * h + c = g ∧ Nonempty (X ≃ₜ SigmaHC h c)

/-- `X` is non-orientable: homeomorphic to `Σ(h,c)` for some `h` and `c ∈ {1, 2}`. -/
def IsNonOrientable (X : Type) [TopologicalSpace X] : Prop :=
  ∃ h c : ℕ, 1 ≤ c ∧ c ≤ 2 ∧ Nonempty (X ≃ₜ SigmaHC h c)

/-- `H` embeds in `X`: injective vertex points; for every edge `uv` an arc from the point of `u`
to the point of `v` whose interior avoids all vertex points; arcs of distinct edges meet only in
the points of common ends. -/
def EmbedsIn {W : Type} (H : SimpleGraph W) (X : Type) [TopologicalSpace X] : Prop :=
  ∃ (f : W → X) (γ : W → W → C(unitInterval, X)), Function.Injective f ∧
    ∀ u v, H.Adj u v →
      Function.Injective (γ u v) ∧ γ u v 0 = f u ∧ γ u v 1 = f v ∧
      (∀ s : unitInterval, s ≠ 0 → s ≠ 1 → γ u v s ∉ Set.range f) ∧
      ∀ u' v', H.Adj u' v' → s(u, v) ≠ s(u', v') →
        ∀ s s' : unitInterval, γ u v s = γ u' v' s' →
          ∃ x, (x = u ∨ x = v) ∧ (x = u' ∨ x = v') ∧ γ u v s = f x

end GMSTFramework.LocalStructure


