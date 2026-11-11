-- Prove2me | Definitions.Def_PlanarDFVSKernel_sigma
-- name    : PlanarDFVSKernel_sigma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:34:36.181257+00:00
-- url     : https://prove2.me/theorems/7cddd271-8994-4e23-8fe7-05bf8bc0517c
-- title:
--   The alternation count $\sigma(v)$ and the special vertices
-- statement:
--   Fix a plane embedding of a digraph. For a vertex $v$, the **alternation count** $\sigma(v)$ is the number of changes between incoming and outgoing arcs as one traverses the cyclic order of arcs around $v$. A vertex is **ordinary** if $\sigma(v)=2$ and **special** if $\sigma(v)>2$.
--
--   **Formalization Note** The arc ends at $v$ are the darts with origin $v$, in the counterclockwise rotation of the drawing; $\sigma(v)$ counts the darts $d$ at $v$ whose successor has the other direction (published `alternating`). It equals twice the published `b`.
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), §3, p.8 (PDF 9)

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Graphs

set_option autoImplicit false

namespace PlanarDFVSKernel

open PlanarDFVS.SingleExp

/-- **The alternation count `σ(v)`** (Sheng, Xiao, *A Polynomial Kernel for Planar Directed
Feedback Vertex Set*, arXiv:2609.23669 (held version, sha256 75cfca8f…), §3, p.8 (PDF 9)): "For a
vertex v, the alternation count σ(v) is the number of changes between incoming and outgoing arcs as
we traverse the cyclic order of arcs around v."

The arc ends at `v` are the darts with origin `v`; the cyclic order is the drawing's
counterclockwise rotation `E.rot`. A dart `d` at `v` is followed by `E.rot d`, and the pair is a
change exactly when one is an incoming and the other an outgoing arc end (`alternating E d`, the
published notion: `d.2 ≠ (E.rot d).2`). `σ(v)` is the number of such darts.

**Formalization Note** This is the count, not the published `b E v = σ(v) / 2`. A vertex with a
single arc end has `σ(v) = 0`. -/
noncomputable def sigma {n m : ℕ} {G : Graph n m} (E : Drawing G) (v : Fin n) : ℕ := by
  classical exact (Finset.univ.filter fun d : Dart m => origin G d = v ∧ alternating E d).card

/-- **The special vertices** (ibid., p.8 (PDF 9)): "We call v ordinary if σ(v) = 2, in which case
its incoming arcs occur consecutively, as do its outgoing arcs. We call v special if σ(v) > 2." -/
noncomputable def specialSet {n m : ℕ} {G : Graph n m} (E : Drawing G) : Finset (Fin n) := by
  classical exact Finset.univ.filter fun v => 2 < sigma E v

end PlanarDFVSKernel


