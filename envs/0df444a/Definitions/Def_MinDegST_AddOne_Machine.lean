-- Prove2me | Definitions.Def_MinDegST_AddOne_Machine
-- name    : MinDegST_AddOne_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:52:26.371708+00:00
-- url     : https://prove2.me/theorems/70f72851-cf3d-4fbc-9d51-6dbc2785fe92
-- title:
--   The deterministic word RAM, its time and word-size bounds, and the encodings of graphs, forests and node sets
-- statement:
--   The paper fixes no machine model. All algorithmic statements of the mission are about one program $P$ of the published integer RAM `CongruencyTU` (unit cost per instruction), run without coins and without oracle; $P$ is **deterministic** when it contains no coin and no query instruction. A run is **word bounded** with width $w$ and scale $N$ if every register at every step has bit length at most $w\,(1+\lfloor\log_2(2+N)\rfloor)$. $P$ **halts within** $B$ on input $I$ with an output satisfying a property if the run reaches a halting state with cost counter at most $B$ whose output block $R[1],\dots,R[R[0]]$ satisfies the property.
--
--   Encodings: a graph is given as $[n,m,u_1,v_1,\dots,u_m,v_m]$; a graph with a threshold $k$ and a forest $F$ as the graph's list followed by $[k,|E(F)|]$ and $F$'s edge list; a graph by adjacency lists as $[n,m,\deg(0),N(0),\dots,\deg(n-1),N(n-1)]$. An output lists the edges of a graph each once as endpoint pairs, a node set as its nodes each once, and a family of node sets as $[\#,\,|S_1|,S_1,\dots]$.
--
--   **Formalization Note.** Without a word-size bound unit-cost arithmetic on unbounded integers would make every running-time claim trivial; with it the machine is a standard word RAM with $O(\log(n+m))$-bit words. Coin and oracle features of `CongruencyTU` are unused.
-- source:
--   Bhattacharya, Farokhnejad, Saranurak, Wang, Faster Algorithms for Minimum Degree Spanning Tree, STOC 2027 submission (manuscript sha256 7d985d3b…), p. 1 (Theorem 1.1) and p. 35 (Part III); machine model chosen by the formalization

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_MinDegST_AddOne_Graph

open Classical

namespace MinDegST.AddOne

/-! # The machine: a deterministic word RAM, and the encodings of graphs, forests and node sets

The paper fixes no machine model. Every algorithmic statement of the mission is a statement about
one program of the published integer RAM `CongruencyTU.Program` (unit cost per instruction), run
without coins and without oracle, whose registers keep `O(log(n + m))` bits: one width constant
`width`, fixed with the program, bounds the bit length of every register at every step by
`width · (1 + log₂(2 + scale))`, where `scale` is the size of the instance (`n + m` for a graph).
Without this bound unit-cost arithmetic on unbounded integers would trivialize running times.

Time is the machine's cost counter at halting; the output is the register block
`R[1], …, R[R[0]]` at halting (`CongruencyTU.outputOf`). -/

variable {n : ℕ}

/-- A deterministic program: no coin instruction and no oracle query. -/
def Deterministic (P : CongruencyTU.Program) : Prop :=
  (∀ d, CongruencyTU.Instr.coin d ∉ P) ∧ ∀ a, CongruencyTU.Instr.query a ∉ P

/-- Logarithmic words: on input `I`, at every step every register of the run of `P` (no coins, no
oracle) has bit length at most `width · (1 + log₂(2 + scale))`. -/
def WordBounded (P : CongruencyTU.Program) (I : List ℤ) (width scale : ℕ) : Prop :=
  ∀ t j, Nat.size ((CongruencyTU.run P CongruencyTU.noOracle CongruencyTU.noCoins I t).reg j).natAbs
    ≤ width * (1 + Nat.log2 (2 + scale))

/-- On input `I` the run of `P` (no coins, no oracle) halts with accumulated cost at most `B`, and
its output at halting satisfies `Good`. (A halted state is fixed, so the output is that of the
first halting step.) -/
def HaltsWithin (P : CongruencyTU.Program) (I : List ℤ) (B : ℝ) (Good : List ℤ → Prop) : Prop :=
  ∃ t, CongruencyTU.isHalted P (CongruencyTU.run P CongruencyTU.noOracle CongruencyTU.noCoins I t)
      = true ∧
    ((CongruencyTU.run P CongruencyTU.noOracle CongruencyTU.noCoins I t).cost : ℝ) ≤ B ∧
    Good (CongruencyTU.outputOf (CongruencyTU.run P CongruencyTU.noOracle CongruencyTU.noCoins I t))

/-- A list of node pairs as integers: `[u₁, v₁, u₂, v₂, …]`. -/
def encPairs (l : List (Fin n × Fin n)) : List ℤ :=
  l.flatMap fun p => [(p.1.val : ℤ), (p.2.val : ℤ)]

/-- Input of a graph given as an edge list: `[n, m, u₁, v₁, …, u_m, v_m]`. -/
def encGraph (n : ℕ) (es : List (Fin n × Fin n)) : List ℤ :=
  [(n : ℤ), (es.length : ℤ)] ++ encPairs es

/-- Input of a graph, a degree threshold `k` and a forest: the graph's edge list, then `k`, then the
number of forest edges and the forest's edge list. -/
def encForestInput (n : ℕ) (es : List (Fin n × Fin n)) (k : ℕ) (fs : List (Fin n × Fin n)) :
    List ℤ :=
  encGraph n es ++ [(k : ℤ), (fs.length : ℤ)] ++ encPairs fs

/-- The output `out` lists the edges of `H` exactly once each, as pairs of endpoints
`[u₁, v₁, u₂, v₂, …]` (each edge in either orientation, in any order). -/
def EncodesEdges (out : List ℤ) (H : SimpleGraph (Fin n)) : Prop :=
  ∃ l : List (Fin n × Fin n), IsEdgeListOf H l ∧ out = encPairs l

/-- A graph given by adjacency lists: `adj v` lists the neighbours of `v` in `G`, each once, in any
order. -/
def IsAdjListsOf (G : SimpleGraph (Fin n)) (adj : Fin n → List (Fin n)) : Prop :=
  ∀ v, (adj v).Nodup ∧ ∀ w, w ∈ adj v ↔ G.Adj v w

/-- Input of a graph given by adjacency lists:
`[n, m, deg(0), N(0)…, deg(1), N(1)…, …, deg(n−1), N(n−1)…]`. -/
def encAdj (n : ℕ) (m : ℕ) (adj : Fin n → List (Fin n)) : List ℤ :=
  [(n : ℤ), (m : ℤ)] ++
    (List.finRange n).flatMap fun v => ((adj v).length : ℤ) :: (adj v).map fun w => (w.val : ℤ)

/-- The output `out` lists the nodes of the set `S`, each once, in any order. -/
def EncodesSet (out : List ℤ) (S : Finset (Fin n)) : Prop :=
  ∃ l : List (Fin n), l.Nodup ∧ l.toFinset = S ∧ out = l.map fun v => (v.val : ℤ)

/-- A list of node sets: `[number of sets, |S₁|, S₁…, |S₂|, S₂…, …]`. -/
def encFamily (l : List (List (Fin n))) : List ℤ :=
  (l.length : ℤ) :: l.flatMap fun S => (S.length : ℤ) :: S.map fun v => (v.val : ℤ)

/-- The output `out` lists the family `𝓡` of node sets, each set once and each set's nodes once, in
any order. -/
def EncodesFamily (out : List ℤ) (𝓡 : Finset (Finset (Fin n))) : Prop :=
  ∃ l : List (List (Fin n)), (∀ S ∈ l, S.Nodup) ∧ (l.map List.toFinset).Nodup ∧
    (l.map List.toFinset).toFinset = 𝓡 ∧ out = encFamily l

end MinDegST.AddOne


