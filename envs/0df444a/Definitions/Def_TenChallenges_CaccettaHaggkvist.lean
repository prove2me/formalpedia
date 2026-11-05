-- Prove2me | Definitions.Def_TenChallenges_CaccettaHaggkvist
-- name    : TenChallenges_CaccettaHaggkvist
-- status  : Definition
-- author  : @utkuokur
-- created : 2026-11-04T21:32:57.420867+00:00
-- url     : https://prove2.me/theorems/a780a78a-fb44-45df-97b9-3c0cb00895e9
-- title:
--   Out-degree, directed cycles and the Caccetta–Häggkvist statement at out-degree $r$
-- statement:
--   The definitions behind Challenge 3 of the Ten Challenges benchmark, on top of Mathlib's `Digraph V` (an arbitrary binary relation on the vertex type $V$).
--
--   1. **Out-degree.** For a digraph $G$ on $V$ and a vertex $v$, $d^+(v)$ is the number of vertices $w$ with an arc $v\to w$ (the cardinality of the set of out-neighbours, $0$ if that set is infinite).
--   2. **Directed cycles.** $G$ *has a cycle of length $\ell$* if there is an injective map $f\colon\{0,\dots,\ell-1\}\to V$ such that $f(i)\to f(i+1)$ is an arc for every $i$, with $f(\ell-1)\to f(0)$ closing the cycle.
--   3. **The statement at out-degree $r$.** $\mathrm{CaccettaHaggkvistFor}(r)$ says: if $r>0$, then for every finite nonempty vertex type $V$ (in the lowest universe) and every digraph $G$ on $V$ without loops in which every vertex has out-degree at least $r$, there is some $\ell\ge 2$ with
--   $$\ell\cdot r < |V| + r$$
--   such that $G$ has a cycle of length $\ell$. The inequality says exactly $\ell\le\lceil |V|/r\rceil$.
--
--   **Formalization Note.** Loops are excluded by hypothesis; arcs in both directions between two vertices are allowed, and a $2$-cycle counts as a cycle. The cyclic successor on $\mathrm{Fin}\,\ell$ is `finRotate ℓ`.
-- source:
--   Ten Challenges repository, file Defs_and_Lems/CaccettaHaggkvist.lean (commit ff14a56), https://github.com/TenChallenges/ten-challenges/blob/main/Defs_and_Lems/CaccettaHaggkvist.lean; conjecture as in L. Caccetta, R. Häggkvist, On minimal digraphs with given girth, 1978.

import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Set.Card
import Mathlib.Logic.Equiv.Fin.Rotate

namespace Digraph

variable {V : Type*} (G : Digraph V)

/-- The out-degree of `v`: the number of out-neighbours of `v`. -/
noncomputable def outDegree (v : V) : ℕ := {w | G.Adj v w}.ncard

/-- A directed cycle of length `ℓ`: `ℓ` distinct vertices, each joined by an arc
to the next one, cyclically. -/
def HasCycleOfLength (ℓ : ℕ) : Prop :=
  ∃ f : Fin ℓ → V, Function.Injective f ∧ ∀ i, G.Adj (f i) (f (finRotate ℓ i))

end Digraph

/-- The Caccetta–Häggkvist conjecture at minimum out-degree `r`: every loopless
digraph on `n ≥ 1` vertices in which every vertex has out-degree at least `r` has
a directed cycle of length at most `⌈n / r⌉`, i.e. of some length `ℓ` with
`ℓ * r < n + r`. -/
def CaccettaHaggkvistFor (r : ℕ) : Prop :=
  0 < r → ∀ {V : Type} [Fintype V] [Nonempty V] (G : Digraph V),
    (∀ v, ¬ G.Adj v v) → (∀ v, r ≤ G.outDegree v) →
      ∃ ℓ, 2 ≤ ℓ ∧ ℓ * r < Fintype.card V + r ∧ G.HasCycleOfLength ℓ


