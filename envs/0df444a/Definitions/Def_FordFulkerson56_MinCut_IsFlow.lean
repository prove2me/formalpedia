-- Prove2me | Definitions.Def_FordFulkerson56_MinCut_IsFlow
-- name    : FordFulkerson56_MinCut_IsFlow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T15:31:30.169984+00:00
-- url     : https://prove2.me/theorems/c31b657b-c829-48d6-8122-88884e75d854
-- title:
--   Flows as collections of chain flows: arc loads, value, saturation and maximal flows
-- statement:
--   Let $N$ be a network with source $a$, sink $b$ and capacities $c$ (Ford–Fulkerson, pp. 399–400). A **chain flow** is a pair $(C;k)$ of a chain $C$ joining $a$ and $b$ and a number $k\ge 0$. A flow is described by a function $f$ assigning to each set of arcs $C$ a real number $f(C)$, the amount sent along $C$.
--
--   1. The **load** of an arc $e$ is $\ell_f(e)=\sum_{C\ni e} f(C)$, the sum of the numbers of all chain flows containing $e$.
--   2. The **value** of $f$ is $\mathrm{val}(f)=\sum_{C} f(C)$.
--   3. $f$ is a **flow** if $f(C)\ge 0$ for every $C$, $f(C)\neq 0$ only when $C$ is a chain joining $a$ and $b$, and $\ell_f(e)\le c(e)$ for every arc $e$.
--   4. An arc $e$ is **saturated** by $f$ if $\ell_f(e)=c(e)$.
--   5. A **maximal flow** is a flow $f$ with $\mathrm{val}(g)\le\mathrm{val}(f)$ for every flow $g$.
--
--   These are the objects of the minimal cut theorem: its left-hand side is the largest value of a flow.
--
--   **Formalization Note** The paper defines a flow as a *collection* of chain flows, which might list the same chain twice. Merging such entries into a single number per chain changes neither the value nor any arc load, so describing a flow by a function on sets of arcs is faithful. Flows are path flows: there is no conservation law and no circulation, as the paper stresses on p. 400. "Maximal" means of maximum value among all flows, not maximal under inclusion.
-- source:
--   Ford & Fulkerson, Maximal Flow Through a Network, Canad. J. Math. 8 (1956), pp. 399–400, §1, definitions of chain flow, flow, saturated arc and value of a flow; maximal flow as used in the proof of Theorem 1, p. 400

import Mathlib
import Definitions.Def_FordFulkerson56_MinCut_Network
import Definitions.Def_FordFulkerson56_MinCut_IsChain

namespace FordFulkerson56.MinCut

variable {V E : Type*} [Fintype E] [DecidableEq E]

/-- The load of arc `e` under the chain-flow assignment `f : Finset E → ℝ`: the sum of the numbers of
all chain flows that contain `e`. -/
def load (f : Finset E → ℝ) (e : E) : ℝ :=
  ∑ C ∈ (Finset.univ : Finset (Finset E)).filter (fun C => e ∈ C), f C

/-- The value of a flow: the sum of the numbers of all its chain flows (p. 400). -/
def value (f : Finset E → ℝ) : ℝ :=
  ∑ C, f C

/-- A flow in the network `N` (Ford–Fulkerson, p. 399): a non-negative number `f C` on every set of
arcs `C`, nonzero only on chains joining the source and the sink, such that the load of every arc is
at most its capacity. -/
def IsFlow (N : Network V E) (f : Finset E → ℝ) : Prop :=
  (∀ C, 0 ≤ f C) ∧ (∀ C, f C ≠ 0 → IsChain N N.source N.sink C) ∧ ∀ e, load f e ≤ N.cap e

/-- Arc `e` is saturated by `f` when its load equals its capacity (p. 399). -/
def Saturated (N : Network V E) (f : Finset E → ℝ) (e : E) : Prop :=
  load f e = N.cap e

/-- A maximal flow: a flow whose value is at least the value of every flow. -/
def IsMaxFlow (N : Network V E) (f : Finset E → ℝ) : Prop :=
  IsFlow N f ∧ ∀ g, IsFlow N g → value g ≤ value f

end FordFulkerson56.MinCut


