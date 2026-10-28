-- Prove2me | Definitions.Def_MonoReset_IntervalBFS_Algorithm
-- name    : MonoReset_IntervalBFS_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:26.584036+00:00
-- url     : https://prove2.me/theorems/3bbdf87a-340f-4215-83b6-2508a6f32db7
-- title:
--   Proof of Theorem 1, pp. 3–4 — preimage table, O(1) evaluation of δ′, minimal intervals, layered BFS, its output and counted cost
-- statement:
--   This item defines the procedure of the proof of Theorem 1 and its cost, as the paper describes it.
--
--   1. **Preimage table** (p. 3). For each letter $\sigma$ and state $s$, an interval representing the preimage $\delta^{-1}(\sigma, s) = \{x : \delta(\sigma, x) = s\}$, or "none" if that preimage is not an interval. When the preimage is all of $S$ any of its $n$ representations may be stored.
--   2. **Fast evaluation of $\delta'$** (p. 3). For an interval $I$ and a letter $\sigma$: if $\sigma$ maps the endpoints of $I$ to different states $d_i \ne d_j$, return $[d_i, d_j]$; if both go to $s$, look up the stored preimage interval $P$ of $s$ and return $[s, s]$ when $P$ represents $S$ or $I \prec P$, and $\infty$ otherwise.
--   3. **Minimal intervals** (proof of Theorem 1, p. 4). For $X = \{s_{i_1}, s_{i_2}, \dots\}$ in cyclic order, the intervals $[s_{i_j}, s_{i_{j-1}}]$; equivalently, the intervals with both endpoints in $X$ that contain $X$.
--   4. **Breadth-first search by layers.** Layer $0$ is the set of minimal intervals. Layer $d+1$ is the set of intervals $\delta'(\sigma, I)$, for $I$ in layer $d$ and $\sigma \in \Sigma$, that are not $\infty$ and were not in an earlier layer.
--   5. **Stopping layer and output.** The search stops at the first layer $D \le n^2$ that contains a singleton interval $[s, s]$ or is empty. If layer $D$ contains a singleton interval, the output is a word of length $D$ obtained by following, back from that singleton, an interval of the previous layer and a letter leading to the current one (parent pointers); otherwise the output is "no reset sequence".
--   6. **Counted cost.** With unit charges,
--   $$\mathrm{cost} = k\,n\cdot n \;+\; \sum_{d=0}^{D} \sum_{I \in L_d} \Bigl(1 + \sum_{\sigma \in \Sigma} c(\sigma, I)\Bigr) \;+\; D,$$
--   where $k n \cdot n$ pays for building the $kn$ preimage intervals in $O(n)$ each, $L_d$ is layer $d$, each interval of a layer costs one dequeue plus one evaluation per letter, an evaluation costs $c(\sigma, I) = 3$ (two look-ups, one comparison) when the endpoint images differ and $8$ otherwise (in addition one table look-up, the test "the preimage is $S$" and three endpoint comparisons), and $D$ pays for writing the output word.
--
--   These are the objects of the goal theorem, which states that the output is correct and minimal and that the cost is $O(kn^2)$.
--
--   **Formalization Note** `preimTable` and the choice of a singleton and of parents in `backtrack` use `Classical.choose`; any choice gives a valid run of the procedure, and the goal holds for the one fixed by the definitions. ∞ is never enqueued. `bfsStop` searches `d = 0, …, n²` and defaults to $n^2$ (the default is never used: the layers are disjoint subsets of the $n^2$ intervals). The search uses `dPrimeFast`, the table-based evaluation, not the definition `dPrime1`; the preimage-test milestone states that they agree on monotonic letters.
-- source:
--   Eppstein, Reset Sequences for Monotonic Automata, author manuscript of 7 Feb 1990 (SIAM J. Comput. 19, doi:10.1137/0219033; PDF sha256 6d8caa76…), pp. 3–4 (PDF 4–5): preimage table and O(1) evaluation of δ′, p. 3; minimal intervals and breadth-first search, proof of Theorem 1, p. 4; at most n²+1 visited states, proof of Theorem 2, p. 4

import Mathlib
import Definitions.Def_MonoReset_IntervalBFS_Model

namespace MonoReset.IntervalBFS

variable {n k : ℕ}

/-- The preimage table (p. 3): for a letter `a` and a state `s`, some representation of the
    preimage δ⁻¹(σ_a, s) as an interval, or `none` if that preimage is not an interval. When the
    preimage is all of S, any one of its n representations may be returned. -/
noncomputable def preimTable (δ : Fin k → Fin n → Fin n) (a : Fin k) (s : Fin n) :
    Option (Fin n × Fin n) :=
  if h : ∃ I : Fin n × Fin n, ivSet I = Finset.univ.filter (fun x => δ a x = s)
  then some (Classical.choose h) else none

/-- δ′(σ, I) evaluated as the paper does (p. 3): look up the images of the two endpoints; if they
    differ, return the interval between them; if they coincide at `s`, look up the preimage interval
    `P` of `s` and return `[s, s]` when `P` is all of S or `I ≺ P` (endpoint comparisons), else ∞. -/
noncomputable def dPrimeFast (δ : Fin k → Fin n → Fin n) (a : Fin k) :
    Option (Fin n × Fin n) → Option (Fin n × Fin n)
  | none => none
  | some I =>
    if δ a I.1 ≠ δ a I.2 then some (δ a I.1, δ a I.2)
    else match preimTable δ a (δ a I.1) with
      | none => none
      | some P => if (P.2 - P.1).val = n - 1 ∨ Prec I P then some (δ a I.1, δ a I.1) else none

/-- The minimal intervals containing `X` (proof of Theorem 1, p. 4): the intervals with both
    endpoints in `X` whose state set contains `X`, i.e. `[s_{i_j}, s_{i_{j-1}}]` for consecutive
    members of `X` in the cyclic order. -/
def minIntervals (X : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  (X ×ˢ X).filter (fun I => X ⊆ ivSet I)

/-- Breadth-first search over the interval automaton, by layers: `layers δ X d` is the pair
    (layer `d`, intervals visited in layers `0, …, d`). Layer 0 is the set of minimal intervals;
    layer `d + 1` is the set of not yet visited intervals `dPrimeFast δ a I` for `I` in layer `d`
    and a letter `a`. ∞ is never enqueued. -/
noncomputable def layers (δ : Fin k → Fin n → Fin n) (X : Finset (Fin n)) :
    ℕ → Finset (Fin n × Fin n) × Finset (Fin n × Fin n)
  | 0 => (minIntervals X, minIntervals X)
  | d + 1 =>
    let L := (layers δ X d).1
    let V := (layers δ X d).2
    let N := L.biUnion
      (fun I => Finset.univ.biUnion (fun a : Fin k => (dPrimeFast δ a (some I)).toFinset))
    (N \ V, V ∪ (N \ V))

/-- The stopping layer of the search: the first `d ≤ n²` whose layer contains a singleton
    interval `(s, s)` or is empty (`n²` if there were none). -/
noncomputable def bfsStop (δ : Fin k → Fin n → Fin n) (X : Finset (Fin n)) : ℕ :=
  ((List.range (n ^ 2 + 1)).find? (fun d =>
      decide (∃ I ∈ (layers δ X d).1, I.1 = I.2) || decide ((layers δ X d).1 = ∅))).getD (n ^ 2)

/-- Parent-pointer back-tracking: `backtrack δ X d J` is a word of length `d` that leads under
    `dPrimeFast` from a minimal interval to `J`, read off the layers by choosing, at each step back,
    an interval of the previous layer and a letter that lead to the current interval. -/
noncomputable def backtrack (δ : Fin k → Fin n → Fin n) (X : Finset (Fin n)) :
    ℕ → Fin n × Fin n → List (Fin k)
  | 0, _ => []
  | d + 1, J =>
    if h : ∃ p : (Fin n × Fin n) × Fin k,
        p.1 ∈ (layers δ X d).1 ∧ dPrimeFast δ p.2 (some p.1) = some J
    then backtrack δ X d (Classical.choose h).1 ++ [(Classical.choose h).2]
    else []

/-- The output of the search: if the stopping layer contains a singleton interval, the
    back-tracked word leading to (a chosen) one of them; otherwise `none` ("no reset sequence"). -/
noncomputable def bfsResult (δ : Fin k → Fin n → Fin n) (X : Finset (Fin n)) :
    Option (List (Fin k)) :=
  if h : ∃ I ∈ (layers δ X (bfsStop δ X)).1, I.1 = I.2
  then some (backtrack δ X (bfsStop δ X) (Classical.choose h))
  else none

/-- Unit cost of one evaluation of `dPrimeFast δ a (some I)` (p. 3): two δ look-ups and one
    comparison; if the endpoints coincide, in addition one table look-up, the test "the preimage is
    all of S" and at most three endpoint comparisons. -/
def evalCost (δ : Fin k → Fin n → Fin n) (a : Fin k) (I : Fin n × Fin n) : ℕ :=
  if δ a I.1 ≠ δ a I.2 then 3 else 8

/-- The counted cost of the run: `k·n` preimage intervals of `n` steps each; then, for every
    interval of every layer up to the stopping layer, one dequeue step and one evaluation of each
    of the `k` letters; then one step per letter of the output word. -/
noncomputable def bfsCost (δ : Fin k → Fin n → Fin n) (X : Finset (Fin n)) : ℕ :=
  k * n * n
  + ∑ d ∈ Finset.range (bfsStop δ X + 1), ∑ I ∈ (layers δ X d).1, (1 + ∑ a : Fin k, evalCost δ a I)
  + bfsStop δ X

end MonoReset.IntervalBFS


