-- Prove2me | Definitions.Def_SecSampling_ConflictGraph
-- name    : SecSampling_ConflictGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:31:06.195016+00:00
-- url     : https://prove2.me/theorems/33f53b86-eb8a-40d1-89fb-54d08e71c9b3
-- title:
--   The conflict graph: conflicts, edges, monotone paths, descendants and degree
-- statement:
--   For a bit string $I$ write $I[a,b]$ for its restriction to positions $a,\dots,b$. Two instances $I_1,I_2$ of sizes $n_1<n_2$, both containing a $0$, are **in conflict** if they have the same norm and $I_1[1,r]=I_2[1,r]$, where $r$ is the position of the last $0$ of $I_1$ (p.15).
--
--   The **conflict graph** (Definition 2, p.15) has all finite bit strings as nodes, with an edge between $s_1$ and $s_2$ iff they are in conflict and $s_2$ is one bit longer than $s_1$. A **monotone path** is a path whose nodes have consecutive increasing sizes. A **descendant** of $I$ is a node of larger size connected to $I$ by a monotone path (p.17). The **degree** of a node is the number of its neighbours of size one larger, its **children** (p.16).
--
--   These notions turn last-zero strategies into selections of nodes in a graph, which is how the paper proves its impossibility result.
--
--   **Formalization Note.** Only finite paths are used; a path is a list of strings with an edge between consecutive entries (a single node is a path). Edges are oriented from the shorter node to the longer one.
-- source:
--   J. Correa, A. Cristi, L. Feuilloley, T. Oosterwijk & A. Tsigonias-Dimitriadis, The Secretary Problem with Independent Sampling, arXiv:2011.07869v1, https://arxiv.org/abs/2011.07869v1, §5.2.1, p.15 (PDF p.16), conflict and Definition 2; p.16 (degree, children); p.17 (descendants)

import Mathlib
import Definitions.Def_SecSampling_LastZero

open Classical

namespace SecSampling

/-- Two instances of the last zero problem are **in conflict** (arXiv:2011.07869v1, §5.2.1,
p.15): `I₁` is strictly shorter than `I₂`, both contain at least one `0`, they have the same norm,
and with `r` the position of the last `0` of `I₁`, `I₁[1, r] = I₂[1, r]`. -/
def Conflict (I₁ I₂ : List Bool) : Prop :=
  I₁.length < I₂.length ∧ false ∈ I₁ ∧ false ∈ I₂ ∧ bitNorm I₁ = bitNorm I₂ ∧
    I₁.take (lastZero I₁) = I₂.take (lastZero I₁)

/-- An **edge of the conflict graph** (Definition 2, p.15): the nodes are all finite bit strings,
and `s₁ — s₂` is an edge iff `s₁` and `s₂` are in conflict and `s₂` is one bit longer than `s₁`.
`Edge I J` orients the edge from the shorter node `I` (the parent) to `J` (a child). -/
def Edge (I J : List Bool) : Prop :=
  Conflict I J ∧ J.length = I.length + 1

/-- A (finite) **monotone path** in the conflict graph (p.15): consecutive nodes are joined by an
edge, so their sizes increase by one at each step. A single node is a monotone path. -/
def IsMonotonePath (P : List (List Bool)) : Prop :=
  P.IsChain Edge

/-- `J` is a **descendant** of `I` (p.17: "The set of nodes in the conflict graph that are
connected to I through a monotone path and that have a larger size than I"): some monotone path
starts at `I` and ends at `J` and has at least two nodes. -/
def IsDescendant (I J : List Bool) : Prop :=
  ∃ P : List (List Bool), IsMonotonePath (I :: (P ++ [J]))

/-- The **degree** of a node (p.16): the number of its neighbours on its right (its children),
i.e. the number of strings `J` of size `|I| + 1` with an edge `I — J`. -/
noncomputable def degree (I : List Bool) : ℕ :=
  ((strings (I.length + 1)).filter (fun J => Edge I J)).card

end SecSampling


