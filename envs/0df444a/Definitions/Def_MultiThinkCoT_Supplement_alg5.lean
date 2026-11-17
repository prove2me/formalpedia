-- Prove2me | Definitions.Def_MultiThinkCoT_Supplement_alg5
-- name    : MultiThinkCoT_Supplement_alg5
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:57:17.348132+00:00
-- url     : https://prove2.me/theorems/7b4aa1b3-dc68-4049-954d-a84e45964f14
-- title:
--   The pass@$\kappa$ learner with known provenance (proof of Theorem 5), with its cost
-- statement:
--   With known provenance the learner observes triples $(x^{(i)},j^{(i)},z^{(i)})$, $i\in[m]$. For each generator index $j\in[\kappa]$ it collects the traces with $j^{(i)}=j$, decomposes each into its prefix–next-token pairs $\big([x^{(i)},z^{(i)}[1{:}t]],\,z^{(i)}[t+1]\big)$, $t<|z^{(i)}|$, and calls the Consistent oracle $\mathcal O$ (Definition 1.1) on them, obtaining $\hat f_j$. It returns the candidate-set predictor
--
--   $$
--   \widehat{\mathcal Z}(x)=\big\{\hat f_j^{\mathrm{CoT}\text{-}T}(x):j\in[\kappa]\big\}.
--   $$
--
--   The definition also accounts for the cost of the run and of evaluating $\widehat{\mathcal Z}(x)$, so that the polynomial running time of Theorem 5 is a statement about this explicit procedure:
--
--   1. reading the sample costs $|x^{(i)}|+1+|z^{(i)}|$ per triple;
--   2. for each $j$: $m$ comparisons to select the traces of generator $j$, one unit per bit written while building each pair plus one per pair, and $\mathrm{oc}(n,N)$ for the oracle call on $N$ pairs of maximal length $n$;
--   3. evaluating $\widehat{\mathcal Z}(x)$: for each $j$, the $T$ autoregressive steps of $\hat f_j$ (charging $\mathrm{ec}(|z|)$ per next-token evaluation on the current string $z$ and $1$ per appended bit) and $T$ to copy the trace, then $\kappa^2T$ bit comparisons to remove duplicates.
--
--   **Formalization Note** The cost conventions are those of the published Algorithm 1 (`MultiThinkCoT.alg1`, whose `runC` is reused); the cost functions $\mathrm{oc}$ and $\mathrm{ec}$ are inputs that Theorem 5 bounds by polynomials. The pairs of each group are taken in increasing order of $i$; a group with no trace gives the oracle the empty list.
-- source:
--   Joshi, Magen, Srebro, Tsilivis, Vardi, Learning to Think from Multiple Thinkers: How Chain-of-Thought Heterogeneity Affects Efficient Learnability, arXiv:2604.24737 (held version, sha256 e663a640…), proof of Theorem 5, p.22 (PDF p.22); runtime model §6.1, p.17; Definition 1.1, p.3

import Mathlib
import Definitions.Def_MultiThinkCoT_alg1
import Definitions.Def_MultiThinkCoT_Supplement_passErr

namespace MultiThinkCoT.Supplement

/-!
# The pass@κ learner with known provenance (proof of Theorem 5), with cost accounting

N. Joshi, R. Magen, N. Srebro, N. Tsilivis, G. Vardi, *Learning to Think from Multiple Thinkers:
How Chain-of-Thought Heterogeneity Affects Efficient Learnability*, arXiv:2604.24737 (held
version, sha256 e663a640…), proof of Theorem 5, p.22 (PDF p.22); runtime model §6.1, p.17 and
Definition 1.1, p.3.

"The learner observes `S_CoT = {(x(i), j(i), z(i)) : i ∈ [m]}`. With known provenance, the
learner applies Consistent to the prefix–next-token pairs from each generator's traces, obtaining
`f̂_1, …, f̂_κ`, and returns `Ẑ(x) = {f̂_j^{CoT-T}(x) : j ∈ [κ]}`."

**Formalization Note.**
* A sample is a list of triples `(x(i), j(i), z(i))`, `knownObs T f s` the one produced from
  draws `s i = (x(i), j(i))` with `z(i) = f_{j(i)}^{CoT-T}(x(i))`.
* `pairsOf data j` is the list of prefix–next-token pairs (`MultiThinkCoT.prefixPairs`) of the
  traces with `j(i) = j`, by increasing `i` (empty if there is none); `alg5Fit O data j` is the
  oracle's answer `O (pairsOf data j)`. The output predictor is `candSet T (alg5Fit O data)`.
* **Cost model** (the convention of `MultiThinkCoT.alg1`, unit cost per elementary step):
  - reading the sample: `|x(i)| + 1 + |z(i)|` per triple;
  - for each `j ∈ [κ]`: `m` comparisons to select the traces with `j(i) = j`, one unit per bit
    written while building each pair plus one per pair (`Σ_pairs (|prefix| + 1)`), and `oc n N`
    for the oracle call on `N` pairs of maximal length `n` (Definition 1.1);
  - a return: `1`.
  Evaluating `Ẑ(x)` (`candSetCost`): for each `j`, the `T` autoregressive steps of `f̂_j` from `x`
  as in `MultiThinkCoT.runC` (`ec |z|` per next-token evaluation and `1` per appended bit) and `T`
  to copy out the trace; `κ · κ · T` bit comparisons to remove duplicates; `1` to return.
  The cost functions `oc` and `ec` are inputs; Theorem 5 bounds them by polynomials.
-/

/-- The known-provenance observations `(x(i), j(i), f_{j(i)}^{CoT-T}(x(i)))` of draws
`s i = (x(i), j(i))`. -/
def knownObs {X : Set (List Bool)} {κ m : ℕ} (T : ℕ) (f : Fin κ → Gen) (s : Fin m → X × Fin κ) :
    Fin m → List Bool × Fin κ × List Bool :=
  fun i => ((s i).1.1, (s i).2, cot (f (s i).2) T (s i).1.1)

/-- The prefix–next-token pairs of the traces of generator `j`, by increasing index. -/
def pairsOf {κ m : ℕ} (data : Fin m → List Bool × Fin κ × List Bool) (j : Fin κ) :
    List (List Bool × Bool) :=
  ((List.finRange m).filter fun i => decide ((data i).2.1 = j)).flatMap
    fun i => prefixPairs (data i).1 (data i).2.2

/-- The fitted generators `f̂_j = O(pairs of generator j)`. -/
def alg5Fit {κ m : ℕ} (O : List (List Bool × Bool) → Gen)
    (data : Fin m → List Bool × Fin κ × List Bool) : Fin κ → Gen :=
  fun j => O (pairsOf data j)

/-- The cost of a run of the learner on `data` (see the cost model above). -/
def alg5Cost {κ m : ℕ} (oc : ℕ → ℕ → ℕ) (data : Fin m → List Bool × Fin κ × List Bool) : ℕ :=
  (∑ i, ((data i).1.length + 1 + (data i).2.2.length))
    + (∑ j : Fin κ, (m + ((pairsOf data j).map fun p => p.1.length + 1).sum
      + oc (((pairsOf data j).map fun p => p.1.length).foldr max 0) (pairsOf data j).length))
    + 1

/-- The cost of evaluating `Ẑ(x) = {f̂_j^{CoT-T}(x) : j ∈ [κ]}`. -/
def candSetCost {κ : ℕ} (ec : ℕ → ℕ) (T : ℕ) (fhat : Fin κ → Gen) (x : List Bool) : ℕ :=
  (∑ j, ((runC ec (fhat j) T x).2 + T)) + κ * κ * T + 1

end MultiThinkCoT.Supplement


