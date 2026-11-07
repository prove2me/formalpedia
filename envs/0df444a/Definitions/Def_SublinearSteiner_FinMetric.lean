-- Prove2me | Definitions.Def_SublinearSteiner_FinMetric
-- name    : SublinearSteiner_FinMetric
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:39:20.241949+00:00
-- url     : https://prove2.me/theorems/bf58abbb-e521-4778-b774-fdf2d0adc22b
-- title:
--   Metric instances, feasible Steiner trees, $\mathrm{OPT}$ and the terminal MST weight $L$
-- statement:
--   An instance of the metric Steiner tree problem is a finite point set $V=\{0,\dots,n-1\}$, a metric $w$ on $V$ (positive off the diagonal, zero on it, symmetric, with the triangle inequality) and a set $T\subseteq V$ of terminals.
--
--   A *tree on $U$* is a vertex set $U$ with a set $E$ of non-loop pairs inside $U$ such that the graph induced on $U$ is connected and acyclic. Its weight is $\sum_{e\in E}w(e)$. A feasible solution is a tree whose vertex set contains $T$, and
--   $$\mathrm{OPT}=\min\{\,w(E): (U,E)\text{ a tree},\ T\subseteq U\,\}.$$
--   $L$ is the least weight of a tree on $T$, the weight of a minimum spanning tree of the metric restricted to $T$.
--
--   These objects are the base of every statement in the mission.
--
--   **Formalization Note.** $\mathrm{OPT}$ and $L$ are given by the least-element relations `IsSteinerOpt` and `IsTerminalMST`, not by an infimum, so no default value can occur. For $n=0$ there is no tree and no $\mathrm{OPT}$. For $T=\emptyset$ the relation sets $L=0$.
-- source:
--   Mahabadi, Roghani, Tarnawski, Vakilian, Tight Bounds for Sublinear Metric Steiner Tree, STOC 2027 submission (manuscript sha256 ae133037…), Section 1, p.1; Section 2, p.12

import Mathlib

open scoped Classical

namespace SublinearSteiner

/-!
# Instances, feasible trees, OPT and the terminal MST

Mahabadi, Roghani, Tarnawski, Vakilian, *Tight Bounds for Sublinear Metric Steiner Tree*, STOC 2027
submission (manuscript sha256 ae133037…), Section 1, p.1, and Section 2, p.12.

An instance is a finite point set `V = Fin n`, a metric on it and a terminal set `T ⊆ V`. A feasible solution is
a tree in the complete graph on `V` whose vertex set contains `T`; `OPT` is its least weight. `L` is the weight
of a minimum spanning tree of the metric restricted to `T`.

**Formalization Note.**
* A tree is a vertex set `U` with a set of non-loop edges inside `U` such that the graph induced on `U` is a tree
  in Mathlib's sense (connected, hence nonempty, and acyclic). A one-vertex tree has no edges.
* `OPT` and `L` are given by `IsLeast` relations, never by `sInf`. For `n = 0` there is no tree and no `OPT`.
* The page's `L` is not meant for `T = ∅`; it is set to `0` there, as the empty sum.
-/

/-- A metric on `Fin n`: zero exactly on the diagonal, symmetric, with the triangle inequality. -/
structure FinMetric (n : ℕ) where
  /-- The distance. -/
  d : Fin n → Fin n → ℝ
  d_self : ∀ x, d x x = 0
  d_pos : ∀ x y, x ≠ y → 0 < d x y
  d_symm : ∀ x y, d x y = d y x
  d_triangle : ∀ x y z, d x z ≤ d x y + d y z

variable {n : ℕ}

/-- The length of an unordered pair. -/
def FinMetric.edgeLen (w : FinMetric n) : Sym2 (Fin n) → ℝ :=
  Sym2.lift ⟨w.d, w.d_symm⟩

/-- The weight of an edge set. -/
noncomputable def FinMetric.weight (w : FinMetric n) (E : Finset (Sym2 (Fin n))) : ℝ :=
  ∑ e ∈ E, w.edgeLen e

/-- The graph on `Fin n` with edge set `E`. -/
def edgeGraph (E : Finset (Sym2 (Fin n))) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n)))

/-- `(U, E)` is a tree in the complete graph on `Fin n`: the edges are non-loops inside `U`, and the graph induced
on `U` is connected and acyclic. In particular `U` is nonempty. -/
def IsTreeOn (U : Finset (Fin n)) (E : Finset (Sym2 (Fin n))) : Prop :=
  (∀ e ∈ E, ¬ e.IsDiag ∧ ∀ x ∈ e, x ∈ U) ∧
    ((edgeGraph E).induce (U : Set (Fin n))).IsTree

/-- The weights of the feasible solutions: trees whose vertex set contains `T` (p.1). -/
def steinerCosts (T : Finset (Fin n)) (w : FinMetric n) : Set ℝ :=
  {c | ∃ U E, T ⊆ U ∧ IsTreeOn U E ∧ c = w.weight E}

/-- `OPT` is the least weight of a feasible solution (p.1). -/
def IsSteinerOpt (T : Finset (Fin n)) (w : FinMetric n) (OPT : ℝ) : Prop :=
  IsLeast (steinerCosts T w) OPT

/-- `L` is the weight of a minimum spanning tree of the metric restricted to `T` (p.1), and `0` for empty `T`. -/
def IsTerminalMST (T : Finset (Fin n)) (w : FinMetric n) (L : ℝ) : Prop :=
  (T = ∅ ∧ L = 0) ∨ IsLeast {c | ∃ E, IsTreeOn T E ∧ c = w.weight E} L

end SublinearSteiner


