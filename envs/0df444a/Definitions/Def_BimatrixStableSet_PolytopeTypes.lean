-- Prove2me | Definitions.Def_BimatrixStableSet_PolytopeTypes
-- name    : BimatrixStableSet_PolytopeTypes
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:19:08.063719+00:00
-- url     : https://prove2.me/theorems/065d2db2-379c-4079-b214-9b30c2d79d03
-- title:
--   Vertex counts, the cube, the semi-cube, the type lists $\mathcal P^d_k$ and the tables (8), (9)
-- statement:
--   This module fixes the objects used to state the computer-assisted facts of §6.
--
--   1. **Counts.** $V$ is the number of vertices of a polytope and $b$ the stable-set bound of its graph.
--   2. **The $d$-cube** (p.19). The polytope $\{z\in\mathbb R^d\mid 0\le z_i\le 1\}$, as a system of $2d$ inequalities. A polytope is a $d$-cube when its face lattice is that of this system.
--   3. **Realizations.** A polytope presented as a face of a finite system in some $\mathbb R^N$. The polytope belongs to $\mathcal P^d_k$ (p.5) if it is simple, of dimension $d$, with $k$ facets.
--   4. **The semi-cube** (p.16). The polytope in $\mathcal P^4_8$ with $17$ vertices and only $3$ obstruction vertices, that is, with $(V,b)=(17,14)$.
--   5. **Vertex counts.** The sets of numbers of vertices of $d$-polytopes with $k$ facets, and of simple ones.
--   6. **Type lists.** A list of polytopes in $\mathcal P^d_k$ of pairwise different types, containing every type, with a prescribed table of pairs $(V,b)$.
--   7. **Tables.** The 37 pairs of display (8) in the order of the page, and the 5 pairs of display (9).
--
--   **Formalization Note** Row indices live in `Type`, which covers every finite system up to renaming the rows. In `table8`, the entry numbered $n$ on the page has index $n-1$. So the semi-cube has index $22$ and the 4-cube has index $23$.
-- source:
--   Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3, §6, pp.16–17, display (8), display (9); p.19; p.5

import Mathlib
import Definitions.Def_BimatrixStableSet_Polyhedra
import Definitions.Def_BimatrixStableSet_StableSets

open Matrix

namespace BimatrixStableSet

/-- The number `V` of vertices of `F`. The vertex set of a face of a finite system is finite (see
the verification file), so `ncard` is the true count. -/
noncomputable def System.vertexCount {ι : Type} {N : ℕ} (Z : System ι N)
    (F : Set (Fin N → ℝ)) : ℕ :=
  (Z.vertices F).ncard

/-- The stable-set bound `b` of the graph of `F`. -/
noncomputable def System.stableBound {ι : Type} {N : ℕ} (Z : System ι N)
    (F : Set (Fin N → ℝ)) : ℕ :=
  stableSetBound (Z.graph F)

/-- The unit `d`-cube `{z ∈ ℝᵈ | 0 ≤ zᵢ ≤ 1}` of p.19 as a system of `2d` inequalities. -/
def cubeSystem (d : ℕ) : System (Fin d ⊕ Fin d) d :=
  ⟨Matrix.fromRows (-1) 1, Sum.elim 0 1⟩

/-- `F` has the combinatorial type of the `d`-cube. -/
def System.IsCubeType {ι : Type} {N : ℕ} (Z : System ι N) (F : Set (Fin N → ℝ)) (d : ℕ) : Prop :=
  Z.SameType F (cubeSystem d) (cubeSystem d).carrier

/-- A polytope presented as a face of a finite system in some `ℝᴺ`. Every polytope arises in this
way (take its whole polyhedron), and so do the facets of `P` and `Q`.

**Formalization Note.** The index type lives in `Type`; `Fin m ⊕ Fin n` and every finite system up
to relabeling of rows are covered. -/
structure Realization where
  /-- The ambient dimension. -/
  N : ℕ
  /-- The index type of the rows. -/
  ι : Type
  /-- There are finitely many rows. -/
  [fin : Fintype ι]
  /-- The system. -/
  Z : System ι N
  /-- The polytope, a face of the system. -/
  F : Set (Fin N → ℝ)

attribute [instance] Realization.fin

/-- The face `F` of the finite system `Z`, as a `Realization`. -/
def System.realize {ι : Type} [Fintype ι] {N : ℕ} (Z : System ι N) (F : Set (Fin N → ℝ)) :
    Realization :=
  ⟨N, ι, Z, F⟩

namespace Realization

/-- The polytope is a `d`-polytope with `k` facets. -/
def IsPolytopeWith (R : Realization) (d k : ℕ) : Prop :=
  R.Z.IsPolytopeOfDim R.F d ∧ (R.Z.facets R.F).ncard = k

/-- The polytope is a simple `d`-polytope with `k` facets, that is, its type belongs to `𝒫ᵈₖ`,
p.5. -/
def IsSimplePolytope (R : Realization) (d k : ℕ) : Prop :=
  R.IsPolytopeWith d k ∧ R.Z.IsSimple R.F

/-- The number of vertices. -/
noncomputable def V (R : Realization) : ℕ := R.Z.vertexCount R.F

/-- The stable-set bound. -/
noncomputable def b (R : Realization) : ℕ := R.Z.stableBound R.F

/-- Two polytopes have the same combinatorial type. -/
def SameType (R R' : Realization) : Prop := R.Z.SameType R.F R'.Z R'.F

/-- The polytope has the combinatorial type of the `d`-cube. -/
def IsCube (R : Realization) (d : ℕ) : Prop := R.Z.IsCubeType R.F d

end Realization

/-- The semi-cube, p.16: the type in `𝒫⁴₈` with "17 vertices that has only 3 obstruction vertices".

**Formalization Note.** The number of obstruction vertices of a 4-polytope is `V - b` (p.16), so
this says `(V, b) = (17, 14)`, which is row 23 of display (8) and no other row. `display_8` proves
that this condition determines a single combinatorial type. -/
def IsSemiCube (R : Realization) : Prop :=
  R.IsSimplePolytope 4 8 ∧ R.V = 17 ∧ R.b = 14

/-- The numbers of vertices of `d`-polytopes with `k` facets. -/
def polytopeVertexCounts (d k : ℕ) : Set ℕ :=
  {v | ∃ R : Realization, R.IsPolytopeWith d k ∧ R.V = v}

/-- The numbers of vertices of simple `d`-polytopes with `k` facets (the polytopes in `𝒫ᵈₖ`). -/
def simpleVertexCounts (d k : ℕ) : Set ℕ :=
  {v | ∃ R : Realization, R.IsSimplePolytope d k ∧ R.V = v}

/-- `rep` lists the combinatorial types of `𝒫ᵈₖ` without repetition, in the order of the table `t`
of the pairs `(V, b)`: the listed polytopes belong to `𝒫ᵈₖ`, have pairwise different types, and every
polytope of `𝒫ᵈₖ` has the type of a listed polytope, with the pair `(V, b)` of that entry of `t`. -/
def IsTypeList (d k : ℕ) {r : ℕ} (t : Fin r → ℕ × ℕ) (rep : Fin r → Realization) : Prop :=
  (∀ i, (rep i).IsSimplePolytope d k) ∧
  (∀ i j, (rep i).SameType (rep j) → i = j) ∧
  (∀ i, ((rep i).V, (rep i).b) = t i) ∧
  (∀ R : Realization, R.IsSimplePolytope d k → ∃ i, R.SameType (rep i) ∧ (R.V, R.b) = t i)

/-- The 37 pairs `(V, b)` of display (8), p.17. The entry numbered `n` on the page is `table8 (n-1)`:
the semi-cube, number 23, is index 22 and the 4-cube, number 24, is index 23. -/
def table8 : Fin 37 → ℕ × ℕ :=
  ![(17, 12), (18, 12), (18, 14), (18, 12), (19, 14),
    (17, 12), (19, 14), (16, 10), (16, 10), (16, 12),
    (17, 12), (19, 14), (18, 12), (16, 10), (15, 10),
    (20, 14), (18, 14), (19, 14), (17, 12), (20, 16),
    (20, 16), (18, 12), (17, 14), (16, 16), (17, 12),
    (17, 12), (17, 12), (15, 10), (16, 10), (16, 12),
    (15, 10), (15, 10), (15, 8), (16, 12), (14, 8),
    (14, 8), (14, 8)]

/-- The 5 pairs `(V, b)` of display (9), p.17. -/
def table9 : Fin 5 → ℕ × ℕ := ![(14, 10), (13, 8), (12, 8), (12, 8), (11, 6)]

end BimatrixStableSet


