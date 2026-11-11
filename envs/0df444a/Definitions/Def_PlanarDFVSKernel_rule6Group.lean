-- Prove2me | Definitions.Def_PlanarDFVSKernel_rule6Group
-- name    : PlanarDFVSKernel_rule6Group
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:35:39.00425+00:00
-- url     : https://prove2.me/theorems/de7e6e2d-93a0-4b7a-8e48-c4b20973edcc
-- title:
--   Reduction Rule 6: one reverse arc per directed boundary path of $F_u$
-- statement:
--   Around a vertex $u$ of a plane digraph the arc ends form maximal runs of incoming and of outgoing arcs. The dual arcs of a run form a directed path $s\rightsquigarrow t$ on the boundary of the dual face $F_u$. **Reduction Rule 6** replaces the reversals of the arcs of each such path in $R_u$ by one arc $t\to s$, keeping one copy of repeated arcs.
--
--   The **group of $u$ after Rule 6** is the set of these arcs $t\to s$, one for each run at $u$. An ordinary vertex ($\sigma(u)=2$) has two runs whose paths share their ends, so its group has one arc; a special vertex has at most $\sigma(u)$.
--
--   **Formalization Note** A run is described by its two delimiting alternating darts $p,d$ ($d$ is the first alternating dart after $p$ counterclockwise); the run consists of the darts strictly after $p$ up to $d$.
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), Reduction Rule 6, p.15–16 (PDF 16–17)

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Graphs
import Definitions.Def_PlanarDFVSKernel_dualArc

set_option autoImplicit false

namespace PlanarDFVSKernel

open PlanarDFVS.SingleExp

/-- **A maximal run of arc ends of one direction at `u`.** `IsRunAt E u p d` holds when `p` and
`d` are alternating darts at `u` and `d` is the first alternating dart strictly after `p` in the
counterclockwise order around `u`. The darts `E.rot^i p` for `1 ≤ i ≤ j` (where `E.rot^j p = d`)
then form a maximal run of arc ends that are all incoming or all outgoing at `u`, of the direction
of `d` (Sheng, Xiao, *A Polynomial Kernel for Planar Directed Feedback Vertex Set*,
arXiv:2609.23669 (held version, sha256 75cfca8f…), §3.4, p.12–13 (PDF 13–14): "In their cyclic
order, the maximal runs of outgoing arcs alternate with the maximal runs of incoming arcs"). -/
def IsRunAt {n m : ℕ} {G : Graph n m} (E : Drawing G) (u : Fin n) (p d : Dart m) : Prop :=
  origin G p = u ∧ alternating E p ∧ alternating E d ∧
    ∃ j : ℕ, 1 ≤ j ∧ (E.rot ^ j) p = d ∧ ∀ i, 1 ≤ i → i < j → ¬ alternating E ((E.rot ^ i) p)

/-- The dart `x` belongs to the run from `p` to `d`: `x = E.rot^i p` with `1 ≤ i ≤ j`, where `j`
is the first index with `E.rot^j p` alternating, and `E.rot^j p = d`. -/
def InRun {n m : ℕ} {G : Graph n m} (E : Drawing G) (p d x : Dart m) : Prop :=
  ∃ j i : ℕ, 1 ≤ i ∧ i ≤ j ∧ (E.rot ^ j) p = d ∧
    (∀ i', 1 ≤ i' → i' < j → ¬ alternating E ((E.rot ^ i') p)) ∧ (E.rot ^ i) p = x

/-- **The reverse arc `t → s` replacing a run** (Sheng, Xiao, arXiv:2609.23669 (held version,
sha256 75cfca8f…), Reduction Rule 6, p.15–16 (PDF 16–17)): "(i) Split the boundary of the
corresponding face F_u at every change of direction into directed paths. (ii) For each path from s
to t, replace all its reverse arcs in R_u by one arc t → s."

The dual arcs of the run from `p` to `d` form the directed boundary path of `F_u` through the faces
`faceOf E p, …, faceOf E d` (the angles between consecutive darts of the run and its two
neighbours). For an outgoing run (`d.2 = false`) the path goes from `s = faceOf E p` to
`t = faceOf E d`, for an incoming run (`d.2 = true`) from `s = faceOf E d` to `t = faceOf E p`.
`runArc` is the reverse arc `t → s`.

**Formalization Note** The direction is derived from `dualArc` (right-hand face to left-hand
face): an outgoing arc end `(e, false)` at `u` has dual arc from the angle before it to the angle
after it, an incoming end the opposite way. -/
noncomputable def runArc {n m : ℕ} {G : Graph n m} (E : Drawing G) (p d : Dart m) :
    Face E × Face E :=
  if d.2 then (faceOf E p, faceOf E d) else (faceOf E d, faceOf E p)

/-- The arcs of the directed boundary path of a run: the dual arcs of the arcs whose ends lie in
the run. -/
def runPathArc {n m : ℕ} {G : Graph n m} (E : Drawing G) (p d : Dart m) (a b : Face E) : Prop :=
  ∃ x, InRun E p d x ∧ dualArc E x.1 = (a, b)

/-- **The group of `u` after Reduction Rule 6** (Sheng, Xiao, arXiv:2609.23669 (held version,
sha256 75cfca8f…), Reduction Rule 6, p.15–16 (PDF 16–17)): one reverse arc `t → s` for each maximal
directed path `s ⇝ t` of the boundary of the dual face `F_u`; "If repeated arcs are produced, keep
only one copy."

`rule6Group E u` is the set of `runArc E p d` over all runs `(p, d)` at `u`.

**Formalization Note** As a set, repeated arcs are automatically kept once. A vertex with no
alternating dart (all arcs incoming or all outgoing) has an empty group; this does not occur under
the paper's standing assumptions (every vertex lies on a directed cycle). -/
noncomputable def rule6Group {n m : ℕ} {G : Graph n m} (E : Drawing G) (u : Fin n) :
    Finset (Face E × Face E) := by
  classical exact ((Finset.univ.filter fun pd : Dart m × Dart m => IsRunAt E u pd.1 pd.2).image
    (fun pd => runArc E pd.1 pd.2))

end PlanarDFVSKernel


