-- Prove2me | Definitions.Def_FulkersonPERT_Bounds_Examples
-- name    : FulkersonPERT_Bounds_Examples
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T07:22:22.538545+00:00
-- url     : https://prove2.me/theorems/b3a7d49b-8124-496d-a757-20ab80311a10
-- title:
--   Figs. 4.1, 4.2 and (4.17), pp. 8, 12, 13 — the example networks and distributions
-- statement:
--   This file fixes the concrete networks and distributions of Fulkerson's examples (Fulkerson's node $k$ is event $k-1$; $t_{ij}$ is the length of arc $(i,j)$).
--
--   1. **The network of Fig. 4.2** (p. 12): events $0,1,2$ with arcs $(1)=(0,1)$, $(2)=(1,2)$, $(3)=(0,2)$.
--   2. **The joint distribution of Fig. 4.2**: the two assignments $(t_{(1)},t_{(2)},t_{(3)})=(0,1,1)$ and $(1,0,1)$, each with probability $\tfrac12$.
--   3. **The bundle-independent distribution of (4.17)** (p. 13) on the same network: the origin's empty bundle is one point of weight $1$; the bundle of event $1$ takes $t_{(1)}\in\{0,2\}$, each with probability $\tfrac12$; the bundle of event $2$ takes $(t_{(2)},t_{(3)})\in\{(0,0),(0,1)\}$, each with probability $\tfrac12$. The page's table of four rows of weight $\tfrac14$ is the product of these.
--   4. **The network of Fig. 4.1** (p. 8): events $0,1,2,3$ with arcs $(0,1),(0,2),(1,2),(1,3),(2,3)$.
--   5. **The distribution of the Fig. 4.1 example**: every arc independently takes the length $0$ or $1$ with probability $\tfrac12$, written per bundle: event $1$ has two equally likely vectors, events $2$ and $3$ each have the four $0/1$ combinations on their two arcs with weight $\tfrac14$.
--
--   These instances are used to state the page's numerical claims.
--
--   **Formalization Note** Matrix entries and vector coordinates at non-arcs are set to $0$ and never read. The weight function of the joint distribution is the constant $\tfrac12$; only its values on the two support points matter.
-- source:
--   Fulkerson, Expected Critical Path Lengths in PERT Networks, RAND Memorandum RM-3075-PR (1962), p. 8 (Fig. 4.1), p. 12 (Fig. 4.2), p. 13 (4.17)

import Mathlib
import Definitions.Def_CriticalPath_Events_ProjectNetwork
import Definitions.Def_FulkersonPERT_Bounds_Model

namespace FulkersonPERT.Bounds

open CriticalPath.Events

/-- The network of Fig. 4.2, p. 12: Fulkerson's nodes 1, 2, 3 are events 0, 1, 2; arc (1) is
`1 → 2 = (0, 1)`, arc (2) is `2 → 3 = (1, 2)`, arc (3) is `1 → 3 = (0, 2)`. -/
def fig42Network : ProjectNetwork 2 where
  P := {(0, 1), (1, 2), (0, 2)}
  one_le := by norm_num
  label_lt := by decide
  origin_precedes := by
    intro k
    fin_cases k
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (by decide)
    · exact Relation.ReflTransGen.single (by decide)
  terminus_follows := by
    intro k
    fin_cases k
    · exact Relation.ReflTransGen.single (by decide)
    · exact Relation.ReflTransGen.single (by decide)
    · exact Relation.ReflTransGen.refl

/-- First row of the table of Fig. 4.2: `(t₁, t₂, t₃) = (0, 1, 1)`, i.e. arc `(0,1)` has length
0, arcs `(1,2)` and `(0,2)` length 1 (entry `i j` is the length of arc `(i, j)`; entries of
non-arcs are 0 and never read). -/
def fig42Row1 : Fin 3 → Fin 3 → ℝ := ![![0, 0, 1], ![0, 0, 1], ![0, 0, 0]]

/-- Second row of the table of Fig. 4.2: `(t₁, t₂, t₃) = (1, 0, 1)`. -/
def fig42Row2 : Fin 3 → Fin 3 → ℝ := ![![0, 1, 1], ![0, 0, 0], ![0, 0, 0]]

/-- The joint distribution of Fig. 4.2: the two rows of the table, each with probability 1/2
(the weight function is the constant 1/2; it is only read on the support). -/
noncomputable def fig42Joint : JointDist 2 where
  supp := {fig42Row1, fig42Row2}
  p := fun _ => 1 / 2

/-- The bundle-independent distribution of the (4.17) example, p. 13, on the network of Fig. 4.2:
the origin's (empty) bundle is a single point of weight 1; the bundle of event 1 (arc (1)) takes
`t₁ ∈ {0, 2}` with probability 1/2 each; the bundle of event 2 (arcs (3) = `(0,2)` and
(2) = `(1,2)`) takes `(t₂, t₃) ∈ {(0, 0), (0, 1)}` with probability 1/2 each. The four rows of
weight 1/4 in the page's table are the product of these bundle distributions. -/
noncomputable def ex417Dist : BundleDist 2 where
  supp := fun j =>
    if j = 0 then {![0, 0, 0]}
    else if j = 1 then {![0, 0, 0], ![2, 0, 0]}
    else {![0, 0, 0], ![1, 0, 0]}
  p := fun j _ => if j = 0 then 1 else 1 / 2

/-- The network of Fig. 4.1, p. 8: Fulkerson's nodes 1, 2, 3, 4 are events 0, 1, 2, 3, with arcs
`1→2, 1→3, 2→3, 2→4, 3→4`, i.e. `(0,1), (0,2), (1,2), (1,3), (2,3)`. -/
def fig41Network : ProjectNetwork 3 where
  P := {(0, 1), (0, 2), (1, 2), (1, 3), (2, 3)}
  one_le := by norm_num
  label_lt := by decide
  origin_precedes := by
    intro k
    fin_cases k
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (by decide)
    · exact Relation.ReflTransGen.single (by decide)
    · exact Relation.ReflTransGen.tail (b := (1 : Fin 4)) (Relation.ReflTransGen.single (by decide))
        (by decide)
  terminus_follows := by
    intro k
    fin_cases k
    · exact Relation.ReflTransGen.head (b := (1 : Fin 4)) (by decide)
        (Relation.ReflTransGen.single (by decide))
    · exact Relation.ReflTransGen.single (by decide)
    · exact Relation.ReflTransGen.single (by decide)
    · exact Relation.ReflTransGen.refl

/-- The distribution of the Fig. 4.1 example, p. 8: every arc independently takes the lengths 0
or 1 with probability 1/2. The bundle of event 1 is arc `(0,1)` (two vectors, weight 1/2); the
bundles of events 2 (arcs `(0,2), (1,2)`) and 3 (arcs `(1,3), (2,3)`) take all four 0/1 values
on their two arcs with weight 1/4 each; the origin's empty bundle is a single point of weight 1. -/
noncomputable def fig41Dist : BundleDist 3 where
  supp := fun j =>
    if j = 0 then {![0, 0, 0, 0]}
    else if j = 1 then {![0, 0, 0, 0], ![1, 0, 0, 0]}
    else if j = 2 then {![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 1, 0, 0], ![1, 1, 0, 0]}
    else {![0, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 1, 1, 0]}
  p := fun j _ => if j = 0 then 1 else if j = 1 then 1 / 2 else 1 / 4

end FulkersonPERT.Bounds


