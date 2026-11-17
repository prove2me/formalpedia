-- Prove2me | Definitions.Def_ForgetAlt_Supplement_MCM
-- name    : ForgetAlt_Supplement_MCM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:16:16.321012+00:00
-- url     : https://prove2.me/theorems/824ea434-f4ca-4596-8b2f-d626f1dae6ad
-- title:
--   The maximum-cardinality matching problem on the word RAM
-- statement:
--   The **maximum-cardinality matching (MCM) problem**: given a simple graph $G$ on the vertex set $\{0,\dots,n-1\}$ with $m$ edges, output a matching of $G$ of maximum size $\mu(G)$.
--
--   On the word RAM (the published `EndStatement` machine, with the conventions of the base mission's `ForgetAlt.Machine`) an instance is laid out as $n$ in cell $0$, then $m$, then the $m$ edges as pairs $u,v$. It is **valid** if no edge is a loop and no edge is listed twice (in either order); isolated vertices are allowed and no matching is given. A correct output is the number $k$ of edges followed by $k$ pairs $u,v$; the listed unordered pairs are distinct and form a maximum matching of $G$.
--
--   A program $B$ **solves the MCM problem within a bound** $g(n,x)$ with width constant $b$ if, on every valid instance $x$ and at every word width $W\ge b\,(\lfloor\log_2(n+m+2)\rfloor+1)$, it halts within $g(n,x)$ steps with a correct output.
--
--   This is the problem of the second sentence of Theorem 5.1.
--
--   **Formalization Note** Maximum matchings and $\mu(G)$ are those of the published `LoadBalMatch_Main_Matching` (`IsMaximumMatching`). The output decoding `Decodes` and the width convention are the base mission's.
-- source:
--   Izumi–Kitamura–Yamaguchi, Forgetting Alternation and Blossoms, STOC 2027 submission (manuscript sha256 b656488c…), Theorem 5.1 (second sentence), printed p.48 (PDF p.49)

import Mathlib
import Definitions.Def_ForgetAlt_Machine
import Definitions.Def_LoadBalMatch_Main_Matching

namespace ForgetAlt.Supplement

/-!
# The maximum-cardinality matching problem on the published word RAM

Izumi–Kitamura–Yamaguchi, *Forgetting Alternation and Blossoms*, STOC 2027 submission
(manuscript sha256 b656488c…), Theorem 5.1, second sentence, printed p.48 (PDF p.49):
"Consequently, an MCM of G is computed in O(m√n log n) time."

**Formalization Notes.**
* The machine is the published word RAM `EndStatement` with the conventions of the base mission's
  `ForgetAlt.Machine`: programs are `List EndStatement.Instr`, time is the number of steps, a run
  starts with `n` in cell 0 and the input after it, the output is read from the cells after the
  input, and a program must work at every width `W ≥ b·(⌊log₂ size⌋ + 1)`, `size = n + m + 2`.
* **Input.** `n` vertices `Fin n` (isolated vertices allowed), then `m` and the `m` edges as pairs
  `u, v`. `Valid`: no loops and no edge listed twice (in either order). No matching is given.
* **Output.** The number `k` of edges, then the `k` edges as pairs `u, v`; the listed unordered
  pairs are distinct and form a **maximum** matching of `G` (`IsMaximumMatching` of the published
  `LoadBalMatch_Main_Matching`: a matching of size `µ(G)`).
-/

open EndStatement LoadBalMatch.Main

/-- A graph on `Fin n`, as a list of edges. -/
structure MCMInstance (n : ℕ) where
  edges : List (Fin n × Fin n)

/-- Valid input: no loops and no edge listed twice (in either order). -/
def MCMInstance.Valid {n : ℕ} (x : MCMInstance n) : Prop :=
  (∀ e ∈ x.edges, e.1 ≠ e.2) ∧ x.edges.Pairwise (fun e e' => s(e.1, e.2) ≠ s(e'.1, e'.2))

/-- The graph `G` of the instance. -/
def MCMInstance.graph {n : ℕ} (x : MCMInstance n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun a b => ∃ e ∈ x.edges, e.1 = a ∧ e.2 = b)

/-- The input words: `m`, then `u, v` for each edge (cell 0, holding `n`, is added by
`SolvedBy`). -/
def mcmInput {n : ℕ} (x : MCMInstance n) : List ℤ :=
  (x.edges.length : ℤ) :: x.edges.flatMap (fun e => [((e.1 : ℕ) : ℤ), ((e.2 : ℕ) : ℤ)])

/-- The output words for a list of edges: their number, then `u, v` for each. -/
def encEdges {n : ℕ} (M : List (Fin n × Fin n)) : List ℤ :=
  (M.length : ℤ) :: M.flatMap (fun e => [((e.1 : ℕ) : ℤ), ((e.2 : ℕ) : ℤ)])

/-- The size `n + m + 2` of an instance, which sets the word width. -/
def mcmSize {n : ℕ} (x : MCMInstance n) : ℕ := n + x.edges.length + 2

/-- The MCM problem: output the edges of a maximum-cardinality matching of `G`, each once. -/
def MCMProblem : Problem where
  Instance n := {x : MCMInstance n // x.Valid}
  input x := mcmInput x.1
  output := fun {n} x out => ∃ M : List (Fin n × Fin n), ForgetAlt.Decodes out (encEdges M) ∧
    (M.map (fun e => s(e.1, e.2))).Nodup ∧
    IsMaximumMatching x.1.graph (M.map (fun e => s(e.1, e.2))).toFinset

/-- The program `B` solves the MCM problem at every width `W ≥ b·(⌊log₂ size⌋ + 1)`, halting
within `bound n x` steps on every valid instance `x`. -/
def MCMRunsWithin (B : List Instr) (b : ℕ) (bound : (n : ℕ) → MCMInstance n → ℕ) : Prop :=
  ∀ (n : ℕ) (x : MCMInstance n) (hx : x.Valid) (W : ℕ), b * (Nat.log2 (mcmSize x) + 1) ≤ W →
    ∃ t ≤ bound n x, MCMProblem.SolvedBy (n := n) ⟨x, hx⟩ B W t

end ForgetAlt.Supplement


