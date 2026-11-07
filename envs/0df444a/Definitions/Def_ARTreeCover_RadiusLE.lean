-- Prove2me | Definitions.Def_ARTreeCover_RadiusLE
-- name    : ARTreeCover_RadiusLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:53:09.175588+00:00
-- url     : https://prove2.me/theorems/4e30b754-47a8-4b47-a95f-0cb47fde3771
-- title:
--   Strong and weak radius of a cluster
-- statement:
--   A cluster $C\subseteq V$ has **strong radius** at most $R$ if there is a center $c\in C$ with $d_{G[C]}(c,v)\le R$ for all $v\in C$. It has **weak radius** at most $R$ if there is a center $c\in V$, possibly outside $C$, with $d_G(c,v)\le R$ for all $v\in C$.
--
--   **Formalization Note** A Boolean flag selects strong (`true`) or weak (`false`), so that statements of the form "strong (respectively, weak)" are one statement.
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Definition 2 and Remark 1, p.9 (PDF p.12)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph

open scoped ENNReal

namespace ARTreeCover

/-- `RadiusLE G strong C R`: the strong (if `strong = true`) or weak (if `strong = false`) radius
of the cluster `C` is at most `R`.

Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…), Definition 2, p.9 (PDF p.12): "We say that the
strong (respectively, weak) radius of C is at most R if there is a designated center u ∈ C (resp.,
u ∈ V) with d_{G[C]}(u, v) ≤ R (resp., d_G(u, v) ≤ R) for every v ∈ C." Remark 1: a weak center
may lie outside `C`.

**Formalization Note.** Clusters are `Finset V`; `d_{G[C]}` is `WGraph.distIn` (walks inside `C`). -/
def RadiusLE {V : Type} (G : WGraph V) (strong : Bool) (C : Finset V) (R : ℝ) : Prop :=
  match strong with
  | true => ∃ c ∈ C, ∀ v ∈ C, G.distIn (↑C : Set V) c v ≤ ENNReal.ofReal R
  | false => ∃ c : V, ∀ v ∈ C, G.dist c v ≤ ENNReal.ofReal R

end ARTreeCover


