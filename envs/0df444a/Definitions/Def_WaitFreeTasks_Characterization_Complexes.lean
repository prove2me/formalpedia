-- Prove2me | Definitions.Def_WaitFreeTasks_Characterization_Complexes
-- name    : WaitFreeTasks_Characterization_Complexes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:27:22.432228+00:00
-- url     : https://prove2.me/theorems/5013b125-e669-4993-b0ee-3a0809399a38
-- title:
--   Finite complexes, real realizations, local PL maps and subdivisions
-- statement:
--   A finite simplicial complex is a finite collection of nonempty finite vertex sets closed under nonempty subsets. A face is realized by all real nonnegative barycentric coordinates summing to one, and the realization is their union:
--
--   $$|K|=\bigcup_{\sigma\in K}\{x:x_v\ge0,\ x_v=0\ (v\notin\sigma),\ \sum_{v\in\sigma}x_v=1\}.$$
--
--   A carrier is the minimal face containing a point or a contained geometric simplex. Geometric complexes additionally require affine independence and the geometric intersection law. A subdivision refines individual faces and covers each original face exactly. PL is the source's continuous, locally conical affine-on-rays condition; cones have compact polyhedral bases and unique positive radial representations. Finite-to-one requires finiteness of each entire real point fiber. These definitions do not assume a triangulation of the map or a solvability theorem. An invalid carrier has the explicitly guarded value empty; valid uses have containing faces.
-- source:
--   Hagit Attiya, Ami Paz, STOC 2027 submission #828 (October 2026), pp. 6–7 (PDF pp. 8–9), §2.2

import Mathlib

set_option autoImplicit false

open Classical

namespace WaitFreeTasks.Characterization

/-! # Simplicial complexes, realizations, PL maps and subdivisions

Attiya–Paz, *Wait-Free Solvability of General Tasks and a New Proof of the Renaming Dichotomy*,
STOC 2027 submission #828 (October 2026), §2.2, printed pp. 6–7 (PDF pp. 8–9).

Conventions.
* An (abstract) complex on a vertex type `V` is a finite family of nonempty finite sets, closed
  under nonempty subsets (§2.2, line 243).
* The realization `|K|` lives in `V → ℝ` (product topology): the vertex `v` is the point
  `Pi.single v 1`, and the face `σ` is the set of barycentric combinations of its vertices,
  i.e. nonnegative functions supported on `σ` summing to `1`. Every real combination is
  included.
* A subdivision is a *geometric* complex: a finite family of affinely independent finite point
  sets of the ambient space, closed under nonempty subsets, any two of whose simplices meet in
  the simplex spanned by their common vertices. Its vertices are points of the ambient space.
-/

/-- An abstract finite simplicial complex (§2.2, printed p. 6): a finite collection of nonempty
finite sets, closed under nonempty subsets. -/
structure Cx (V : Type) where
  faces : Finset (Finset V)
  nonempty : ∀ σ ∈ faces, σ.Nonempty
  down_closed : ∀ σ ∈ faces, ∀ τ : Finset V, τ.Nonempty → τ ⊆ σ → τ ∈ faces

/-- The vertex set `V(F)` of a family of faces. -/
noncomputable def verts {V : Type} (F : Finset (Finset V)) : Finset V := F.biUnion id

/-- The realization `|v|` of a vertex `v`: the standard basis point `e_v ∈ ℝ^V`. -/
noncomputable def vpt {V : Type} (v : V) : V → ℝ := Pi.single v 1

/-- The realization `|σ|` of a finite vertex set `σ`: all barycentric combinations of the
points `|v|`, `v ∈ σ` (nonnegative coordinates, supported on `σ`, summing to `1`).
`|∅| = ∅`. -/
def face {V : Type} (σ : Finset V) : Set (V → ℝ) :=
  {x | (∀ v, 0 ≤ x v) ∧ (∀ v, v ∉ σ → x v = 0) ∧ ∑ v ∈ σ, x v = 1}

/-- The realization `|F| = ⋃_{σ ∈ F} |σ|` of a family of faces (e.g. a complex or a
subcomplex `Δ(σ)`). -/
def realOf {V : Type} (F : Finset (Finset V)) : Set (V → ℝ) :=
  ⋃ σ ∈ F, face σ

/-- The geometric realization `|K|` of a complex. -/
def Cx.real {V : Type} (K : Cx V) : Set (V → ℝ) := realOf K.faces

/-- `IsCarrierOf F S τ`: `τ ∈ F` is the minimal face of `F` whose realization contains the
set `S` (§2.2, printed p. 7, lines 281–285: `carr_K(x)` for a point, `carr_K(σ')` for a simplex
of a subdivision). -/
def IsCarrierOf {V : Type} (F : Finset (Finset V)) (S : Set (V → ℝ)) (τ : Finset V) : Prop :=
  τ ∈ F ∧ S ⊆ face τ ∧ ∀ τ' ∈ F, S ⊆ face τ' → τ ⊆ τ'

/-- The carrier `carr_F(S)` (§2.2, printed p. 7): the minimal face of `F` whose realization
contains `S`. It is unique when it exists. Guard: when no face of `F` contains `S` (which the
source excludes, line 285) the value is `∅`; every use in this mission is at a point of `|O|` or
at a simplex of a subdivision, where the carrier exists. -/
noncomputable def carrOf {V : Type} (F : Finset (Finset V)) (S : Set (V → ℝ)) : Finset V :=
  if h : ∃ τ, IsCarrierOf F S τ then h.choose else ∅

/-! ## Piecewise-linear maps (§2.2, printed p. 7, lines 302–304; [RS82, 1.1, 1.4]) -/

/-- The join `xL = {x} ∪ {(1-μ)x + μy : y ∈ L, 0 ≤ μ ≤ 1}`. -/
def join {E : Type} [AddCommGroup E] [Module ℝ E] (x : E) (L : Set E) : Set E :=
  insert x {z | ∃ y ∈ L, ∃ μ : ℝ, 0 ≤ μ ∧ μ ≤ 1 ∧ z = (1 - μ) • x + μ • y}

/-- `xL` is a cone with apex `x` and base `L` [RS82, p. 2]: every point of `xL` other than the
apex has a unique expression `(1-μ)x + μy`, `y ∈ L`, `0 < μ ≤ 1`. -/
def IsCone {E : Type} [AddCommGroup E] [Module ℝ E] (x : E) (L : Set E) : Prop :=
  ∀ y₁ ∈ L, ∀ y₂ ∈ L, ∀ μ₁ μ₂ : ℝ, 0 < μ₁ → μ₁ ≤ 1 → 0 < μ₂ → μ₂ ≤ 1 →
    (1 - μ₁) • x + μ₁ • y₁ = (1 - μ₂) • x + μ₂ • y₂ → μ₁ = μ₂ ∧ y₁ = y₂

/-- A compact polyhedron: a finite union of convex hulls of finite point sets (finite unions of
simplices). -/
def IsCompactPolyhedron {E : Type} [AddCommGroup E] [Module ℝ E] (L : Set E) : Prop :=
  ∃ S : Finset (Finset E), L = ⋃ s ∈ S, convexHull ℝ (s : Set E)

/-- A conical neighbourhood (star) `xL` of `x` in `A` [RS82, 1.1]: `xL` is a cone with compact
polyhedral base `L`, contained in `A`, and a neighbourhood of `x` in `A`. -/
def IsConicalNbhd {E : Type} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (A : Set E) (x : E) (L : Set E) : Prop :=
  IsCompactPolyhedron L ∧ IsCone x L ∧ join x L ⊆ A ∧ join x L ∈ nhdsWithin x A

/-- A map `f : A → B` (given as a function on the ambient space, constrained only on `A`) is
**piecewise linear** (§2.2, printed p. 7, [RS82, def. 1.4]): it is a (continuous) map, and every
`x ∈ A` has a conical neighbourhood `xL ⊆ A` with `f(λx + μy) = λf(x) + μf(y)` for all `y ∈ L`,
`λ, μ ≥ 0`, `λ + μ = 1`. -/
def IsPL {E F : Type} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    (A : Set E) (f : E → F) : Prop :=
  ContinuousOn f A ∧
    ∀ x ∈ A, ∃ L : Set E, IsConicalNbhd A x L ∧
      ∀ y ∈ L, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → f (a • x + b • y) = a • f x + b • f y

/-- `f : A → B` is **finite-to-one**: the fibre `{x ∈ A : f x = y}` is finite for every
`y ∈ B` (§1.1, printed p. 2, lines 92–93). -/
def FiniteToOne {E F : Type} (A : Set E) (B : Set F) (f : E → F) : Prop :=
  ∀ y ∈ B, {x | x ∈ A ∧ f x = y}.Finite

/-! ## Geometric complexes and subdivisions (§2.2, printed p. 6, lines 257–258) -/

/-- The geometric simplex `|σ|` spanned by a finite point set `σ`. -/
def gs {E : Type} [AddCommGroup E] [Module ℝ E] (σ : Finset E) : Set E :=
  convexHull ℝ (σ : Set E)

/-- The relative interior of the simplex spanned by `σ`: the combinations
`∑_{v ∈ σ} a_v v` with all `a_v > 0` and `∑ a_v = 1` (for affinely independent `σ` this is
`|σ| ∖ ⋃_{σ' ⊊ σ} |σ'|`, §2.2 line 255 and Definition 1). -/
def openSimplex {E : Type} [AddCommGroup E] [Module ℝ E] (σ : Finset E) : Set E :=
  {x | ∃ a : E → ℝ, (∀ v ∈ σ, 0 < a v) ∧ ∑ v ∈ σ, a v = 1 ∧ x = ∑ v ∈ σ, a v • v}

/-- A finite geometric simplicial complex in `E`: a finite family of nonempty affinely
independent finite point sets, closed under nonempty subsets, such that any two simplices meet
exactly in the simplex spanned by their common vertices. Its vertices are points of `E`. -/
structure GCx (E : Type) [AddCommGroup E] [Module ℝ E] where
  faces : Finset (Finset E)
  nonempty : ∀ σ ∈ faces, σ.Nonempty
  down_closed : ∀ σ ∈ faces, ∀ τ : Finset E, τ.Nonempty → τ ⊆ σ → τ ∈ faces
  indep : ∀ σ ∈ faces, AffineIndependent ℝ (fun v : (σ : Set E) => (v : E))
  inter : ∀ σ ∈ faces, ∀ τ ∈ faces, gs σ ∩ gs τ = convexHull ℝ ((σ : Set E) ∩ (τ : Set E))

/-- The realization `|K| = ⋃_{σ ∈ K} |σ|` of a geometric complex. -/
def GCx.real {E : Type} [AddCommGroup E] [Module ℝ E] (K : GCx E) : Set E :=
  ⋃ σ ∈ K.faces, gs σ

/-- `D` is a **subdivision** of the abstract complex `K` (§2.2, printed p. 6, lines 257–258,
in the standard form of [HKR13, Def. 3.3.1]): `D` is a geometric complex in the ambient space
`ℝ^V` of `|K|`, every simplex of `D` lies in the realization of a simplex of `K`, and the
realization of every simplex of `K` is the union of the (finitely many) simplices of `D` lying in
it. In particular `|D| = |K|`. -/
def IsSubdivOf {V : Type} (D : GCx (V → ℝ)) (K : Cx V) : Prop :=
  (∀ σ ∈ D.faces, ∃ τ ∈ K.faces, gs σ ⊆ face τ) ∧
    ∀ τ ∈ K.faces, face τ = ⋃ σ ∈ D.faces, ⋃ (_ : gs σ ⊆ face τ), gs σ

/-- `K` is a **subdivision** (refinement) of the geometric complex `D` in the same ambient space:
every simplex of `K` lies in a simplex of `D`, and every simplex of `D` is the union of the
simplices of `K` lying in it. -/
def Refines {E : Type} [AddCommGroup E] [Module ℝ E] (K D : GCx E) : Prop :=
  (∀ σ ∈ K.faces, ∃ τ ∈ D.faces, gs σ ⊆ gs τ) ∧
    ∀ τ ∈ D.faces, gs τ = ⋃ σ ∈ K.faces, ⋃ (_ : gs σ ⊆ gs τ), gs σ

/-- `f` is **linear on the simplex** `|σ|` (in the source's sense: affine with respect to the
barycentric coordinates of `σ`): `f(∑ a_v v) = ∑ a_v f(v)` for all convex weights `a` on `σ`. -/
def AffineOnSimplex {E F : Type} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (f : E → F) (σ : Finset E) : Prop :=
  ∀ a : E → ℝ, (∀ v ∈ σ, 0 ≤ a v) → ∑ v ∈ σ, a v = 1 →
    f (∑ v ∈ σ, a v • v) = ∑ v ∈ σ, a v • f v

end WaitFreeTasks.Characterization


