-- Prove2me | Definitions.Def_HousingImprove_IsSubAllocation
-- name    : HousingImprove_IsSubAllocation
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:26:52.84298+00:00
-- url     : https://prove2.me/theorems/ce5f5b37-89a0-4732-896b-57b47ca4f2e2
-- title:
--   Sub-allocations, $Y$-augmenting arcs and stability
-- statement:
--   Let $H$ be a housing market on an agent set $M$ and $W\subseteq M$. A **sub-allocation** on $W$ is a set $Y$ of arcs $(a,b)$ of the acceptability graph with $a,b\in W$ such that every agent has at most one outgoing and at most one incoming arc; we write $Y(a)=b$ for the arc $(a,b)$. Its **source set** $U$ consists of the agents of $W$ without an incoming arc and its **sink set** $V$ of the agents of $W$ without an outgoing arc; $Y$ forms vertex-disjoint cycles and paths leading from $U$ to $V$.
--
--   An arc $(a,b)$ of the acceptability graph inside $W$ is **$Y$-augmenting** if either $a\in V$ and $b\neq a$, or $Y(a)\prec_a b$. The **envy graph** of $Y$ consists of the $Y$-augmenting arcs, and $Y$ is **stable** if its envy graph is acyclic.
--
--   These notions describe the intermediate states of algorithm HM-Improve.
--
--   **Formalization Note** The page fixes $U$ and $V$ with $|U|=|V|$ first; here they are derived from $Y$ (`subSources`, `subSinks`), and $|U|=|V|$ follows by counting arcs. The page reads "either $a\in V$ or $Y(a)\prec_a b$"; because $(a,a)$ is always an arc, this would put a loop at every sink and make every sub-allocation with a sink unstable, contradicting Lemma 1; the loop is excluded.
-- source:
--   Schlotter, Biró, Fleiner, The core of housing markets from an agent's perspective: Is it worth sprucing up your home?, arXiv:2110.06875v3, §4.1, p.11 (sub-allocations, source and sink sets, Y-augmenting arcs, envy graph, stability), with the loop at a sink excluded

import Mathlib
import Definitions.Def_HousingImprove_Market

namespace HousingImprove

universe u

variable {M : Type u}

/-- A **sub-allocation** in the submarket of `H` on the agent set `W` (Schlotter, Biró, Fleiner,
arXiv:2110.06875v3, §4.1, p.11): a set `Y` of arcs of the acceptability graph, all inside `W`, with
out-degree and in-degree at most one at every agent. `Y a = some b` is the arc `(a, b)`, and
`Y a = none` means that `a` has no outgoing arc.

**Formalization Note.** The page fixes the source set `U` and the sink set `V` first and asks
`δ⁺_Y(v) = 0` on `V`, `δ⁺_Y(a) = 1` elsewhere, and the same for `δ⁻_Y` and `U`. Here `U` and `V`
are derived from `Y` (`subSources`, `subSinks`); `|U| = |V|` follows by counting arcs in a finite
`W`. -/
def IsSubAllocation (H : Market M) (W : Set M) (Y : M → Option M) : Prop :=
  (∀ a b, Y a = some b → a ∈ W ∧ b ∈ W ∧ H.Acceptable a b) ∧
  (∀ a b c, Y a = some c → Y b = some c → a = b)

/-- The **source set** `U` of a sub-allocation `Y` on `W` (p.11): the agents of `W` with no incoming
arc. -/
def subSources (W : Set M) (Y : M → Option M) : Set M :=
  {u | u ∈ W ∧ ∀ a, Y a ≠ some u}

/-- The **sink set** `V` of a sub-allocation `Y` on `W` (p.11): the agents of `W` with no outgoing
arc. -/
def subSinks (W : Set M) (Y : M → Option M) : Set M :=
  {v | v ∈ W ∧ Y v = none}

/-- `(a, b)` is a **`Y`-augmenting arc** (p.11, corrected at sinks): an arc of the acceptability graph
inside `W` such that either `a ∈ V` (and `b ≠ a`) or `Y(a) ≺_a b`.

**Formalization Note.** The page reads "either `a ∈ V` or `Y(a) ≺_a b`". Since `(a, a)` is an arc of
`G^H` for every `a`, the literal reading puts a loop at every sink, so no sub-allocation with a sink
would be stable and Lemma 1 (p.16) would fail; its proof ("the unique arc entering `q̃`") and Step 2
use no loop. The loop at a sink is excluded. -/
def IsAugmenting (H : Market M) (W : Set M) (Y : M → Option M) (a b : M) : Prop :=
  a ∈ W ∧ b ∈ W ∧ H.Acceptable a b ∧
  ((a ∈ subSinks W Y ∧ a ≠ b) ∨ ∃ c, Y a = some c ∧ H.lt a c b)

/-- A sub-allocation `Y` on `W` is **stable** (p.11) if its envy graph, whose arcs are the
`Y`-augmenting arcs, is acyclic. -/
def IsStable (H : Market M) (W : Set M) (Y : M → Option M) : Prop :=
  ∀ a, ¬ Relation.TransGen (IsAugmenting H W Y) a a

end HousingImprove


