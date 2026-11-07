-- Prove2me | Definitions.Def_SublinearSteiner_PortGraph
-- name    : SublinearSteiner_PortGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:46:39.488629+00:00
-- url     : https://prove2.me/theorems/75cb8be6-8efa-4880-8044-d7ac90c59cdf
-- title:
--   The capped lists $L(C)$ and the port multigraph on $U$
-- statement:
--   For a component $C$, $L(C)$ is the list of the first $b$ centers, in a fixed public order, within distance $5a/8$ of $C$ (all of them if there are fewer). The multigraph on a set $U$ of components has a **port edge** $(v,\min\{x,x'\},\max\{x,x'\})$ between $C$ and $C'$ whenever $v\in L(C)\cap L(C')$, the row of $v$ is eligible, and $x\in C$, $x'\in C'$ are retained points within $5a/8$ of $v$.
--
--   **Formalization Note.** The public order is a permutation of the points. A copy records $(C,C',v,x,x')$ with $x<x'$; since components are disjoint, $(v,x,x')$ alone determines $C$ and $C'$. The graph is loopless: $C\ne C'$.
-- source:
--   Mahabadi, Roghani, Tarnawski, Vakilian, Tight Bounds for Sublinear Metric Steiner Tree, STOC 2027 submission (manuscript sha256 ae133037…), Section 4.6, p.27

import Mathlib
import Definitions.Def_SublinearSteiner_Statistics
import Definitions.Def_SublinearSteiner_Multigraph

open scoped Classical

namespace SublinearSteiner

/-!
# The capped incidence lists and the port multigraph

Mahabadi, Roghani, Tarnawski, Vakilian, *Tight Bounds for Sublinear Metric Steiner Tree*, STOC 2027
submission (manuscript sha256 ae133037…), Section 4.6, p.27.

"For `C ∈ U` let `L(C)` be the first `b` centers, in a fixed public order, within distance `5a/8` of `C` (all of them if
there are fewer). The multigraph on `U` has a port edge `(v, min{x, x′}, max{x, x′})` between `C` and `C′` whenever `v`
belongs to `L(C) ∩ L(C′)`, the row of `v` is eligible, and `x ∈ C`, `x′ ∈ C′` are retained points within `5a/8` of `v`."

**Formalization Note.**
* The public order is a permutation `ord` of the points, listing `ord.symm 0, ord.symm 1, …`. Centers are all points of
  `V` (rows are defined for all of `V`).
* `(v, x, x')` with `x < x'` and `x ∈ C`, `x' ∈ C'` is the label `(v, min, max)`. Components are disjoint, so the label
  determines `C` and `C'`, and each label is one copy. `C ≠ C'`: the graph is loopless and p.27 rejects `C' = C`.
-/

variable {n : ℕ}

/-- `L(C)`: the first `b` centers, in the order `ord`, within distance `5a/8` of `C` (p.27). -/
noncomputable def cappedList (w : FinMetric n) (ord : Equiv.Perm (Fin n)) (b : ℕ) (a : ℝ)
    (C : Finset (Fin n)) : Finset (Fin n) :=
  (((List.finRange n).map ord.symm).filter fun v => ∃ x ∈ C, w.d v x ≤ 5 * a / 8).take b |>.toFinset

/-- `(C, C', v, x, x')` is a port edge on the vertex set `U` (p.27). -/
def IsPortEdge (w : FinMetric n) (N : Finset (Fin n)) (a : ℝ) (ord : Equiv.Perm (Fin n)) (b : ℕ)
    (U : Finset (Finset (Fin n))) (t : ↥U × ↥U × Fin n × Fin n × Fin n) : Prop :=
  let C := t.1.1
  let C' := t.2.1.1
  let v := t.2.2.1
  let x := t.2.2.2.1
  let x' := t.2.2.2.2
  C ≠ C' ∧ x ∈ C ∧ x' ∈ C' ∧ x < x' ∧ v ∈ cappedList w ord b a C ∧ v ∈ cappedList w ord b a C' ∧
    v ∈ eligibleCenters w (comp w N a) (5 * a / 8) ∧ w.d v x ≤ 5 * a / 8 ∧ w.d v x' ≤ 5 * a / 8

/-- The copies of the port multigraph. -/
abbrev PortCopy (w : FinMetric n) (N : Finset (Fin n)) (a : ℝ) (ord : Equiv.Perm (Fin n)) (b : ℕ)
    (U : Finset (Finset (Fin n))) :=
  {t : ↥U × ↥U × Fin n × Fin n × Fin n // IsPortEdge w N a ord b U t}

/-- The port multigraph on `U` (p.27). -/
def portGraph (w : FinMetric n) (N : Finset (Fin n)) (a : ℝ) (ord : Equiv.Perm (Fin n)) (b : ℕ)
    (U : Finset (Finset (Fin n))) : Multigraph ↥U (PortCopy w N a ord b U) where
  src e := e.1.1
  tgt e := e.1.2.1
  ne e h := e.2.1 (congrArg Subtype.val h)

end SublinearSteiner


