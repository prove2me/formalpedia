-- Prove2me | Definitions.Def_LoadBalMatch_Main_StreamingMachine
-- name    : LoadBalMatch_Main_StreamingMachine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:32:25.903709+00:00
-- url     : https://prove2.me/theorems/12964869-6305-4498-82d1-f23fbb3cdb51
-- title:
--   Randomized multi-pass streaming machines with $s$ bits of memory (§1, Theorem 3)
-- statement:
--   In the semi-streaming model (§1, p. 1) the edges of an $n$-vertex graph arrive in an arbitrarily ordered stream; an algorithm makes one or a few passes over the stream, each in the same order, and is charged for the memory it retains. A **randomized $P$-pass streaming machine with $s$ bits of memory** on graphs with vertex set $\{0,\dots,n-1\}$ consists of:
--   - an initial distribution on the $2^s$ memory states;
--   - a transition kernel: from the current memory state and the current edge, a distribution on the next memory state;
--   - an end-of-pass kernel: from the memory state, a distribution on the next memory state;
--   - an output kernel: from the memory state, a distribution on sets of vertex pairs.
--
--   On an edge stream $\sigma$ the machine starts from the initial law, runs $P$ passes (each pass applies the transition kernel to the edges of $\sigma$ in order, then the end-of-pass kernel), and then draws its output. Its **success probability** on $G$ with accuracy $\varepsilon$ is
--   $$\Pr\big[\text{the output is a matching of } G \text{ with at least } (1-\varepsilon)\mu(G) \text{ edges}\big].$$
--
--   **Formalization Note.** `MultiPassMachine n s P` has fields `initial : PMF (Fin (2^s))`, `step`, `endPass`, `output`; every retained bit (including random bits and any pass counter) is part of the state in `Fin (2^s)`; fresh randomness and computation are free; the machine never receives the pass index, the stream position, the number of edges, or the graph. `law` iterates the pass `P` times; `successProb` sums the output law over the sets that are matchings of `G` of the required size (any other output is a failure).
-- source:
--   Assadi, Bernstein, Wrzos-Kaminska, Better Bounds for Semi-Streaming Maximum Matching via Load Balancing, STOC 2027 submission (sha256 7cd28a8b…), p. 1, §1; p. 2, Theorem 3

import Mathlib
import Definitions.Def_LoadBalMatch_Main_Matching

/-!
# Randomized multi-pass streaming machines for matching

Assadi, Bernstein, Wrzos-Kaminska, STOC 2027 submission (sha256 7cd28a8b…), §1 p. 1: "the edges of
the input n-vertex graph are presented to the algorithm in some arbitrarily ordered stream. The
algorithm is allowed to make one or a few passes over this stream and uses Õ(n) := O(n·polylog(n))
memory"; Theorem 3, p. 2.

Formalization Note. A machine with `s` bits of memory making `P` passes, on graphs with vertex set
`Fin n`:
* its whole retained state is a value in `Fin (2^s)` (every stored bit is counted, including
  retained random bits and any pass counter it keeps);
* `initial` is an input-independent initial law;
* `step` sees only the memory and the current edge and returns a law on the next memory (fresh
  randomness and unbounded computation are free);
* `endPass` updates the memory at the end of each pass (it sees only the memory: the machine is
  told that a pass has ended, not which one);
* `output` returns a law on sets of unordered pairs.
The run applies `P` passes over the same list `σ` in the same order, then the output kernel. The
pattern follows the published one-pass `AssadiSemiStreaming_Greedy_StreamingMachine`, which is not
imported. `successProb A G σ ε` is the probability that the output is a matching of `G` with at
least `(1 − ε)·µ(G)` edges; any other output is a failure.
-/

namespace LoadBalMatch.Main

/-- A randomized `P`-pass streaming machine with `s` bits of memory on `n`-vertex graphs. -/
structure MultiPassMachine (n s P : ℕ) where
  initial : PMF (Fin (2 ^ s))
  step : Fin (2 ^ s) → Sym2 (Fin n) → PMF (Fin (2 ^ s))
  endPass : Fin (2 ^ s) → PMF (Fin (2 ^ s))
  output : Fin (2 ^ s) → PMF (Finset (Sym2 (Fin n)))

/-- The law of the output of `A` on the stream `σ`: `P` passes over `σ`, then the output. -/
noncomputable def MultiPassMachine.law {n s P : ℕ} (A : MultiPassMachine n s P)
    (σ : List (Sym2 (Fin n))) : PMF (Finset (Sym2 (Fin n))) :=
  ((fun q : PMF (Fin (2 ^ s)) =>
      (σ.foldl (fun q e => q.bind (fun st => A.step st e)) q).bind A.endPass)^[P]
      A.initial).bind A.output

/-- The probability that `A` outputs a matching of `G` with at least `(1 − ε)·µ(G)` edges. -/
noncomputable def successProb {n s P : ℕ} (A : MultiPassMachine n s P) (G : SimpleGraph (Fin n))
    (σ : List (Sym2 (Fin n))) (ε : ℝ) : ENNReal := by
  classical
  exact ∑ out : Finset (Sym2 (Fin n)),
    if IsMatchingIn G out ∧ (1 - ε) * (matchingNumber G : ℝ) ≤ (out.card : ℝ)
    then A.law σ out else 0

end LoadBalMatch.Main


