-- Prove2me | Definitions.Def_UnitSquarePack_NPHard_MonotonePlanar3SAT
-- name    : UnitSquarePack_NPHard_MonotonePlanar3SAT
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:19:18.256033+00:00
-- url     : https://prove2.me/theorems/d9e41bf5-5806-4082-9acc-c398d4a4df6d
-- title:
--   The language Monotone-Planar-3SAT
-- statement:
--   An instance $\Phi = (F, G)$ of **Monotone-Planar-3SAT** consists of a monotone 3SAT formula $F$ with variables $x_0, \dots, x_{n-1}$ and clauses $c_0, \dots, c_{m-1}$ and the plane graph $G$ with vertex set $\{x_0, \dots, x_{n-1}, c_0, \dots, c_{m-1}\}$ whose edges are the incidences $x_i c_j$ ($x_i$ or $\neg x_i$ in $c_j$) and the cycle
--   $$C = \{x_0x_1, \dots, x_{n-2}x_{n-1}, x_{n-1}x_0\},$$
--   drawn so that $C$ separates all positive clauses from all negative clauses.
--
--   A **crossing-free drawing** of $G$ places the vertices at distinct points $p(v)$ and draws each edge $uv$ as a simple arc from $p(u)$ to $p(v)$ through no other vertex point, arcs of different edges meeting only at common endpoints (the clauses of the published `WilliamsonShmoys.HasPlanarDrawingOn`, restated as `IsPlaneDrawing` so that the drawing can be named; the two agree by definition). The cycle $C$ **separates** the clauses in the drawing if no positive clause point lies in the connected component of $\mathbb R^2 \setminus C$ containing a negative clause point, where $C$ also denotes the union of the arcs of its edges.
--
--   The language **Monotone-Planar-3SAT** is the set of binary codes of $(n, F)$ (the variable order fixes $C$) such that every clause of $F$ is well formed and positive or negative, $G$ has a crossing-free drawing in which $C$ separates the positive from the negative clauses, and $F$ is satisfiable.
--
--   The variable cycle is a genuine simple cycle: the language requires at least three variables. This excludes the degenerate loop or single-edge graphs obtained with fewer variables.
-- source:
--   Abrahamsen and Stade, Hardness of Packing, Covering and Partitioning Simple Polygons with Unit Squares, arXiv:2404.09835v2, p. 4, §2.1, definition of Monotone-Planar-3SAT

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_OptimalQueuingComplexity_Restless_encNat
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_UnitSquarePack_NPHard_Formula

set_option autoImplicit false

namespace UnitSquarePack.NPHard

open Set OptimalQueuingComplexity.Restless

/-- `(p, arc)` is a crossing-free drawing of `G`: the vertex points `p` are distinct; each edge
`uv` (`u < v`) is drawn as a simple arc `arc u v` from `p u` to `p v` passing through no vertex
point in its interior; arcs of different edges meet only at common endpoints. These are exactly
the clauses of the published `WilliamsonShmoys.HasPlanarDrawingOn`, which only asserts that such
`(p, arc)` exist; the drawing is named here because Monotone-Planar-3SAT constrains it. -/
def IsPlaneDrawing {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ) : Prop :=
  Function.Injective p ∧
    (∀ u v, u < v → G.Adj u v →
      ContinuousOn (arc u v) (Set.Icc 0 1) ∧
      Set.InjOn (arc u v) (Set.Icc 0 1) ∧
      arc u v 0 = p u ∧
      arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w) ∧
    (∀ u v x y, u < v → x < y → G.Adj u v → G.Adj x y →
      (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ s ∈ Set.Icc (0 : ℝ) 1, arc u v t = arc x y s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))

/-- The named drawing is the published notion: `HasPlanarDrawingOn G` holds iff some
`IsPlaneDrawing G p arc` holds (by definition). -/
theorem hasPlanarDrawingOn_iff_exists_isPlaneDrawing {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) :
    WilliamsonShmoys.HasPlanarDrawingOn G ↔ ∃ p arc, IsPlaneDrawing G p arc := Iff.rfl

/-- The edge relation of the graph `G` of an instance `(n, F)` of Monotone-Planar-3SAT.
Vertices are `Fin (n + m)` (`m` = number of clauses): `i < n` is the variable `x_i`, and `n + j`
is the clause `c_j`. Edges: `x_i c_j` whenever `x_i` or `¬x_i` is in `c_j`, and the cycle
`C = x_0 x_1, …, x_{n-2} x_{n-1}, x_{n-1} x_0`. -/
def mpRel (n : ℕ) (F : CookPvsNP.CNF) (u v : Fin (n + F.length)) : Prop :=
  (u.val < n ∧ n ≤ v.val ∧ Occurs u.val (F.getD (v.val - n) [])) ∨
  (u.val < n ∧ v.val < n ∧ (v.val = u.val + 1 ∨ (u.val + 1 = n ∧ v.val = 0)))

/-- The graph `G` (symmetric, loopless closure of `mpRel`). -/
def mpGraph (n : ℕ) (F : CookPvsNP.CNF) : SimpleGraph (Fin (n + F.length)) :=
  SimpleGraph.fromRel (mpRel n F)

/-- `uv` is an edge of the variable cycle `C`. -/
def IsCycleEdge (n : ℕ) {N : ℕ} (u v : Fin N) : Prop :=
  u.val < n ∧ v.val < n ∧
    (v.val = u.val + 1 ∨ u.val = v.val + 1 ∨ (u.val + 1 = n ∧ v.val = 0) ∨
      (v.val + 1 = n ∧ u.val = 0))

/-- The image of the cycle `C` in the drawing: the union of the arcs of its edges. -/
def cycleImage (n : ℕ) (F : CookPvsNP.CNF) (arc : Fin (n + F.length) → Fin (n + F.length) → ℝ → ℝ × ℝ) :
    Set (ℝ × ℝ) :=
  ⋃ (u : Fin (n + F.length)) (v : Fin (n + F.length)) (_ : u < v ∧ IsCycleEdge n u v),
    arc u v '' Icc 0 1

/-- In the drawing, the cycle `C` separates all positive clauses from all negative clauses: no
positive clause point lies in the same connected component of `ℝ² ∖ C` as a negative clause
point. -/
def CycleSeparates (n : ℕ) (F : CookPvsNP.CNF) (p : Fin (n + F.length) → ℝ × ℝ)
    (arc : Fin (n + F.length) → Fin (n + F.length) → ℝ → ℝ × ℝ) : Prop :=
  ∀ (i j : ℕ) (hi : i < F.length) (hj : j < F.length),
    IsPositiveClause (F.getD i []) → IsNegativeClause (F.getD j []) →
      p ⟨n + i, by omega⟩ ∉ connectedComponentIn (cycleImage n F arc)ᶜ (p ⟨n + j, by omega⟩)

/-- Binary code of an instance: the number `n` of variables, then the clauses (in this order;
the variable order fixes the cycle `C`). -/
def mpCode (n : ℕ) (F : CookPvsNP.CNF) : List Bool := encNat n ++ encClauses F

/-- The language Monotone-Planar-3SAT (de Berg and Khosravi): codes of `(n, F)` where every
clause has one to three literals on the variables `x_0, …, x_{n-1}` and is positive or negative,
there are at least three variables (so `C` is a cycle),
the graph `G` has a crossing-free drawing in which the cycle `C` separates the positive from the
negative clauses, and `F` is satisfiable. -/
def monotonePlanar3SAT : CookPvsNP.Lang Bool :=
  {w | ∃ (n : ℕ) (F : CookPvsNP.CNF), w = mpCode n F ∧ 3 ≤ n ∧
      (∀ C ∈ F, ClauseOK n C ∧ (IsPositiveClause C ∨ IsNegativeClause C)) ∧
      (∃ p arc, IsPlaneDrawing (mpGraph n F) p arc ∧ CycleSeparates n F p arc) ∧
      CookPvsNP.CNF.Satisfiable F}

end UnitSquarePack.NPHard


