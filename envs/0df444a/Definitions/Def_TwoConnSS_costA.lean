-- Prove2me | Definitions.Def_TwoConnSS_costA
-- name    : TwoConnSS_costA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:47:20.914092+00:00
-- url     : https://prove2.me/theorems/5c4114d2-1d2e-4076-a51f-43d635b8213a
-- title:
--   The credit assignment A and $\mathrm{cost}_A$
-- statement:
--   Let $(S, M)$ be a weak 2-edge-cover with a pairing. With $c = 2/9$, **assignment A** gives:
--
--   1. $22/9$ credits to each unpaired singleton and $11/3$ to each pair of singletons;
--   2. $1$ credit to each 4-cycle component and $2t/9$ to each $t$-cycle component, $5 \le t \le 8$;
--   3. $2$ credits to every other 2EC component;
--   4. $34/9$ credits to an **exceptional** complex component (two vertex-disjoint 5-cycles joined by a path of seven edges whose six internal vertices lie outside the cycles);
--   5. $1 + b(C) + \sum_{T} f(|E(T)|)$ credits to every other complex component $C$, the sum over its **bridge segments** $T$ (maximal trees of bridges whose non-leaf vertices are lonely), where
--   $$f(q) = \begin{cases} 0, & q \le 6,\\ 1, & 7 \le q \le 12,\\ (q-1)/6, & q \ge 13.\end{cases}$$
--
--   Then $\mathrm{cost}_A(S) = |S| + \mathrm{cr}_A(S)$, the number of edges plus the total credit. The algorithm keeps $\mathrm{cost}_A$ from increasing; the credits pay for future edges.
--
--   **Formalization Note** Credits are exact rationals. The pairing is an explicit argument. An exceptional component is recorded as a complex component whose blocks are exactly two 5-cycles and which has six lonely vertices of degree two.
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), §8.1.2, pp.35–36 (Definitions 8.9, 8.10)

import Mathlib
import Definitions.Def_TwoConnSS_IsCanonA

namespace TwoConnSS

open Classical

variable {V : Type*} [Fintype V]

/-- The segment credit `f(q)` of §8.1.2, p.36: `f(q) = 0` for `q ≤ 6`, `1` for `7 ≤ q ≤ 12`, and
`(q − 1)/6` for `q ≥ 13`. -/
def segF (q : ℕ) : ℚ :=
  if q ≤ 6 then 0 else if q ≤ 12 then 1 else ((q : ℚ) - 1) / 6

/-- A set `T` of bridges forming a tree whose non-leaf vertices are lonely: `T` is nonempty,
consists of bridges of `(V, S)`, is connected as an edge set, and every vertex incident to at
least two edges of `T` lies in no 2EC block. (A set of bridges contains no cycle, so a connected
one is a tree.) -/
def SegOK (S T : Finset (Sym2 V)) : Prop :=
  T.Nonempty ∧ T ⊆ bridges S ∧
  (∀ e ∈ T, ∀ e' ∈ T, ∀ u ∈ e, ∀ w ∈ e', (sg T).Reachable u w) ∧
  ∀ v, 2 ≤ (T.filter fun e => v ∈ e).card → ∀ B ∈ blocks S, v ∉ B

/-- **Bridge segment** (Definition 8.9, p.35): "an inclusionwise maximal tree with at least one
edge, all of whose edges are bridges and all of whose non-leaf vertices are lonely vertices." -/
def IsSegment (S T : Finset (Sym2 V)) : Prop :=
  SegOK S T ∧ ∀ T', T ⊆ T' → SegOK S T' → T' = T

/-- The bridge segments `T(C)` of a component `C`. -/
noncomputable def segs (S : Finset (Sym2 V)) (C : Finset V) : Finset (Finset (Sym2 V)) :=
  (edgesIn S C).powerset.filter fun T => IsSegment S T

/-- **Exceptional complex component** (Definition 8.10, p.35): "two vertex-disjoint 5-cycles joined
by a path of seven edges with its six internal vertices outside the cycles." Recorded as: a complex
component whose 2EC blocks are exactly two 5-cycles, with six lonely vertices, each of degree two.
(The bridge tree then has two block nodes and six degree-two nodes, so it is a path of seven
bridges.) -/
def IsExceptional (S : Finset (Sym2 V)) (C : Finset V) : Prop :=
  IsComplexComp S C ∧
  (∃ B₁ B₂, B₁ ≠ B₂ ∧ blocksIn S C = {B₁, B₂} ∧ IsCycleBlock S B₁ 5 ∧ IsCycleBlock S B₂ 5) ∧
  (lonely S C).card = 6 ∧ ∀ v ∈ lonely S C, deg S v = 2

/-- The credit of one component under assignment A (p.35–36). -/
noncomputable def compCrA (S : Finset (Sym2 V)) (C : Finset V) : ℚ :=
  if IsCycleComp S C 4 then 1
  else if ∃ t, 5 ≤ t ∧ t ≤ 8 ∧ IsCycleComp S C t then 2 * (C.card : ℚ) / 9
  else if IsTwoECComp S C then 2
  else if IsExceptional S C then 34 / 9
  else if IsComplexComp S C then
    1 + ((blocksIn S C).card : ℚ) + ∑ T ∈ segs S C, segF T.card
  else 0

/-- **The cost under assignment A**, `cost_A(S) = |S| + cr_A(S)`.
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), §8.1.2, pp.35–36: "Set c = 2/9.
Under assignment A, an unpaired singleton receives 2 + 2c = 22/9 credits, a pair of singletons
receives 3 + 3c = 11/3, a 4-cycle receives one, and a t-cycle with 5 ≤ t ≤ 8 receives 2t/9. Every
other 2EC component receives two credits. An exceptional complex component receives 34/9. Every
remaining complex component C receives 1 + b(C) + Σ_{T∈T(C)} f(|E(T)|) … Set costA(S) = |S| +
crA(S)."

Also defined here: `segF` (`f`), bridge segments (Definition 8.9), exceptional components
(Definition 8.10) and the per-component credit `compCrA`.

**Formalization Note.** Credits are exact rationals. The pairing `M` is an argument, since a pair
of singletons is credited once (Definition 8.5). Isolated vertices receive credit only as unpaired
singletons (`22/9`) or through their pair (`11/3`). -/
noncomputable def costA (S M : Finset (Sym2 V)) : ℚ :=
  (S.card : ℚ) + ((unpaired S M).card : ℚ) * (22 / 9) + (M.card : ℚ) * (11 / 3) +
    ∑ C ∈ comps S, compCrA S C

end TwoConnSS


