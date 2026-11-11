-- Prove2me | Definitions.Def_TurnstileCutSparsify_Main_Streaming
-- name    : TurnstileCutSparsify_Main_Streaming
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:39:29.214145+00:00
-- url     : https://prove2.me/theorems/3f5d7f86-0b06-46c5-9d32-4ca04c5f6e82
-- title:
--   Turnstile streams and one-pass linear-sketch streaming algorithms on the word RAM: update and recovery programs, output format, linear-sketch clause, randomized runs (§1.1, §2)
-- statement:
--   **Streams.** A turnstile stream on $n$ vertices is a sequence of $M$ updates $(e,\Delta)$, $e$ a pair and $\Delta$ an integer with $|\Delta|\le U$; it starts from the zero vector and each update adds $\Delta$ to coordinate $e$. Intermediate weights may be negative; the final weights lie in $\{0,1,\dots,U\}$ and form the input graph $G=(V,E,w)$, $E=\{e:w_e>0\}$.
--
--   **Model of computation.** Running times refer to the word RAM with $w$-bit words and $S$ memory cells (the published word-RAM core: unit-cost arithmetic, bitwise and comparison instructions, indirect addressing, a fault on any access outside the $S$ cells, so $S\cdot w$ bits bound everything stored). A randomized streaming algorithm draws a seed $\rho$ uniformly from a finite set and starts from an initial memory that stores the seed and everything it knows in advance ($n,\varepsilon,\delta,M,U$). An update $(e,\Delta)$ writes $\min e$, $\max e$ and $\Delta$ into the first three cells and runs the **update program**; its step count is the update time. After the last update the **recovery program** runs on the memory; its step count is the recovery time, and the output graph is read from the final memory as a list of pairs with rational weights (one word per number). The algorithm is a **linear sketch** if for every seed $\rho$ there are an integer matrix $\Phi_\rho$ with $N$ columns and a map $F_\rho$ such that the memory after every prefix of every admissible stream equals $F_\rho(\Phi_\rho x)$, where $x$ is the prefix's net weight vector. "Worst-case" bounds hold for every seed and every admissible stream.
--
--   A **randomized word-RAM computation** (used for Theorem 2.7 and Lemma 7.2) writes its input words followed by random words into an all-zero memory and runs a program for at most $T$ steps; the probability is over the uniformly random words. A graph with integer weights is input as the list $(u,v,x_e)$ of its edges.
--
--   **Formalization Note** `Admissible n M U s`: `s.length = M`, `|Δ| ≤ U`, `netVec s ∈ {0,…,U}^N`. `StreamMachine` = word size `w`, cells `S`, seed count `K`, `init : Fin K → Mem S`; `runStream`, `recover` run the programs with `runWithin`; `decodeGraph` reads cell `0` = number of entries and entry `i` from cells `1+4i … 4+4i` as `(u, v, p, q)` with `u < v < n`, `q > 0`; `GoodOutput x lo hi bound L`: distinct pairs, positive weights on edges of `x`, at most `bound` entries, and `ApproxCuts lo hi x (outGraph L)`. `WorstCase` collects the worst-case clauses (at least one seed, every initial cell a word, `IsLinearSketch`, every update within `Tu` and recovery within `Trec` on every seed and admissible stream). `randRun P w S T input r` runs `P` on `input ++ r`.
-- source:
--   Lin, Mirrokni, Woodruff (2026), Near-Optimal Space and Time Cut Sparsification in Turnstile Streams, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), §1.1 p. 2, §2 "Stream model and notation" and "Model of computation" p. 9

import Mathlib
import Definitions.Def_TurnstileCutSparsify_Main_Graph
import Definitions.Def_TurnstileRank_TightBounds_WordRAM

open scoped BigOperators Classical

noncomputable section

namespace TurnstileCutSparsify.Main

open TurnstileRank.TightBounds.RAM

/-!
# Turnstile streams and one-pass linear-sketch algorithms on the word RAM (§1.1, §2)

Lin, Mirrokni, Woodruff, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…),
§1.1 p. 2, §2 "Stream model and notation" and "Model of computation" p. 9, §7.5 pp. 37–38.

**Streams.** An update is `(e, Δ)` with `e : Pair n` and `Δ : ℤ`. A stream is a list of updates;
it starts from the zero vector and its net vector `netVec s` adds every `Δ` to its coordinate.
`Admissible n M U s`: exactly `M` updates, `|Δ| ≤ U` for each, and final weights in
`{0, 1, …, U}`; intermediate weights may be negative.

**The machine.** The word RAM is the published core `TurnstileRank.TightBounds.RAM` (`w`-bit
words, `S` cells, unit-cost instructions, a fault on any access outside the `S` cells, so `S · w`
bits bound everything stored). A `StreamMachine` has word size `w`, `S` cells, `K` seeds (the seed
`ρ` is uniform on `Fin K`) and an initial memory `init ρ` for every seed: the seed and every
parameter the algorithm knows in advance (`n, ε, δ, M, U`) are stored in, and counted in, the
memory. The update and recovery programs `upd`, `rec` are fixed word-RAM programs.
* An update `(e, Δ)` writes `min e`, `max e` (0-based) and `Δ` (two's complement) into cells
  `0, 1, 2` and runs `upd` from instruction `0`; it must halt within `Tu` steps (its update time).
* After the last update, `rec` runs on the memory and must halt within `Trec` steps (the recovery
  time, from the end of the stream until the output is produced).
* The output is read from the final memory: cell `0` holds the number `k` of output entries, and
  entry `i < k` occupies cells `1 + 4i, …, 4 + 4i` as `(u, v, p, q)`: the pair `{u, v}` with
  `u < v < n` and weight `p / q` (`q > 0`). Every number is one word.
* `IsLinearSketch`: for every seed `ρ` there are an integer matrix `Φ_ρ` with `N` columns and a map
  `F_ρ` such that the memory after **every prefix** of every admissible stream is `F_ρ(Φ_ρ x)`,
  where `x` is the prefix's net vector (which may have negative entries).

**Randomized word-RAM computations** (for Theorem 2.7 and Lemma 7.2). `randRun P w S T input r`
writes the input words, followed by the random words `r`, into cells `0, 1, …` of an all-zero
memory of `S` cells and runs `P` for at most `T` steps; the probability is over `r` uniform.
-/

/-- A stream update `(e, Δ)`. -/
abbrev Update (n : ℕ) := Pair n × ℤ

variable {n : ℕ}

/-- The net weight vector of a stream: the sum of its updates, starting from zero. -/
def netVec (s : List (Update n)) : Pair n → ℤ :=
  fun e => (s.map fun u => if u.1 = e then u.2 else 0).sum

/-- An admissible stream: `M` updates of magnitude at most `U`, with final weights in
`{0, 1, …, U}`. -/
def Admissible (n M U : ℕ) (s : List (Update n)) : Prop :=
  s.length = M ∧ (∀ u ∈ s, |u.2| ≤ (U : ℤ)) ∧ ∀ e, 0 ≤ netVec s e ∧ netVec s e ≤ (U : ℤ)

/-- The final graph `G = (V, E, w)` of a stream, as a real weight vector. -/
def finalGraph (s : List (Update n)) : Pair n → ℝ := fun e => (netVec s e : ℝ)

/-- A streaming machine: word size, number of cells, number of seeds, and the initial memory of
each seed. -/
structure StreamMachine where
  w : ℕ
  S : ℕ
  K : ℕ
  init : Fin K → Mem S

namespace StreamMachine

variable (A : StreamMachine)

/-- The input words of an update `(e, Δ)`: `min e`, `max e`, and `Δ` in two's complement. -/
def encUpdate (u : Update n) : List ℕ := [u.1.lo.val, u.1.hi.val, encInt A.w u.2]

/-- One update, run by `upd` within `Tu` steps. -/
def update (upd : Program) (Tu : ℕ) (m : Mem A.S) (u : Update n) : Option (Mem A.S) :=
  runWithin A.w A.S upd Tu (setInputs A.w m (A.encUpdate u))

/-- The memory after a stream, from seed `ρ` (`none` if some update does not halt in time). -/
def runStream (upd : Program) (Tu : ℕ) (ρ : Fin A.K) (s : List (Update n)) : Option (Mem A.S) :=
  s.foldl (fun om u => om.bind fun m => A.update upd Tu m u) (some (A.init ρ))

/-- Recovery: run `rec` on the memory within `Trec` steps. -/
def recover (rec : Program) (Trec : ℕ) (m : Mem A.S) : Option (Mem A.S) :=
  runWithin A.w A.S rec Trec m

end StreamMachine

/-- The pair `{u, v}` from two words, if `u < v < n`. -/
def decodePair (n u v : ℕ) : Option (Pair n) :=
  if h : u < v ∧ v < n then
    some ⟨(⟨u, lt_trans h.1 h.2⟩, ⟨v, h.2⟩), by simpa [Fin.lt_def] using h.1⟩
  else none

/-- Entry `i` of an output list in memory: cells `1 + 4i, …, 4 + 4i` hold `u, v, p, q`. -/
def decodeEntry {S : ℕ} (n : ℕ) (m : Mem S) (i : ℕ) : Option (Pair n × ℚ) :=
  (rd m (1 + 4 * i)).bind fun u => (rd m (2 + 4 * i)).bind fun v =>
    (rd m (3 + 4 * i)).bind fun p => (rd m (4 + 4 * i)).bind fun q =>
      (decodePair n u v).bind fun e => if q = 0 then none else some (e, (p : ℚ) / q)

/-- The output graph read from memory: cell `0` holds the number of entries. -/
def decodeGraph {S : ℕ} (n : ℕ) (m : Mem S) : Option (List (Pair n × ℚ)) :=
  (rd m 0).bind fun k => (List.range k).mapM (decodeEntry n m)

/-- The weight vector of an output list (weights of repeated pairs add up). -/
def outGraph (L : List (Pair n × ℚ)) : Pair n → ℝ :=
  fun e => ((L.filter fun p => p.1 = e).map fun p => (p.2 : ℝ)).sum

/-- A good output for the graph `x`: distinct pairs, positive weights on edges of `x` only (a
positive reweighting of edges of `x`), at most `bound` edges, and every cut within `[lo, hi]`. -/
def GoodOutput (x : Pair n → ℝ) (lo hi bound : ℝ) (L : List (Pair n × ℚ)) : Prop :=
  (L.map Prod.fst).Nodup ∧ (∀ p ∈ L, 0 < p.2 ∧ 0 < x p.1) ∧ (L.length : ℝ) ≤ bound ∧
    ApproxCuts lo hi x (outGraph L)

/-- The linear-sketch clause: for every seed `ρ` there are an integer matrix `Φ_ρ` with `N`
columns and a map `F_ρ` such that the memory after every prefix of every admissible stream is
`F_ρ(Φ_ρ x)`, `x` the prefix's net vector. -/
def IsLinearSketch (A : StreamMachine) (upd : Program) (Tu M U : ℕ) : Prop :=
  ∀ ρ : Fin A.K, ∃ (r : ℕ) (Φ : Matrix (Fin r) (Pair n) ℤ) (F : (Fin r → ℤ) → Mem A.S),
    ∀ s : List (Update n), Admissible n M U s → ∀ k ≤ s.length,
      A.runStream upd Tu ρ (s.take k) = some (F (Φ.mulVec (netVec (s.take k))))

/-- The output of a run: process the stream from seed `ρ`, recover, and read the output graph. -/
def runOutput (A : StreamMachine) (upd rec : Program) (Tu Trec : ℕ) (ρ : Fin A.K)
    (s : List (Update n)) : Option (List (Pair n × ℚ)) :=
  (A.runStream upd Tu ρ s).bind fun m => (A.recover rec Trec m).bind (decodeGraph n)

/-- The worst-case clauses of a one-pass linear-sketch streaming algorithm `(A, upd, rec)` on
admissible streams: at least one seed, every initial cell a word, the linear-sketch clause, and on
every seed and every admissible stream every update halts within `Tu` steps and recovery halts
within `Trec` steps. -/
def WorstCase (A : StreamMachine) (upd rec : Program) (n M U Tu Trec : ℕ) : Prop :=
  0 < A.K ∧ (∀ ρ i, A.init ρ i < 2 ^ A.w) ∧ IsLinearSketch (n := n) A upd Tu M U ∧
    ∀ ρ (s : List (Update n)), Admissible n M U s →
      ∃ m, A.runStream upd Tu ρ s = some m ∧ (A.recover rec Trec m).isSome

/-- The random words of a randomized word-RAM computation follow its input. -/
def randRun (P : Program) (w S T : ℕ) (input : List ℕ) {Lr : ℕ} (r : Fin Lr → Fin (2 ^ w)) :
    Option (Mem S) :=
  runWithin w S P T (setInputs w (fun _ => 0) (input ++ List.ofFn fun i => (r i).val))

/-- `L` lists the edges of the integer graph `x`, each once, with its weight. -/
def IsEdgeListing (x : Pair n → ℕ) (L : List (Pair n × ℕ)) : Prop :=
  (L.map Prod.fst).Nodup ∧ (∀ p ∈ L, x p.1 = p.2 ∧ 0 < p.2) ∧ ∀ e, 0 < x e → ∃ p ∈ L, p.1 = e

/-- The words of an edge listing: `u, v, weight` for each entry. -/
def encEdges (L : List (Pair n × ℕ)) : List ℕ :=
  L.flatMap fun p => [p.1.lo.val, p.1.hi.val, p.2]

end TurnstileCutSparsify.Main


