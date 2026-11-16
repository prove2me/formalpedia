-- Prove2me | Definitions.Def_SYKEdge_Supplement_RandomHypergraph
-- name    : SYKEdge_Supplement_RandomHypergraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:21:26.139398+00:00
-- url     : https://prove2.me/theorems/5f797918-7676-4854-9ee6-8418621deca4
-- title:
--   Probability over a random $k$-uniform hypergraph with $m$ hyperedges
-- statement:
--   A **random $k$-uniform hypergraph** $\mathcal H$ with $m$ hyperedges is a tuple $\mathcal H=(S_1,\dots,S_m)$ whose entries are independent and uniformly distributed on $\binom{[n]}{k}$, the $k$-element subsets of $[n]$. Repeated hyperedges are allowed, so $\mathcal H$ is a multiset, and the positions $1,\dots,m$ are distinguished: each position carries its own disorder variable in the SYK Hamiltonian.
--
--   For an event $E$ of such tuples,
--   $$\Pr_{\mathcal H}[E]=\frac{\#\{(S_1,\dots,S_m)\in\binom{[n]}{k}^m : E(S_1,\dots,S_m)\}}{\binom nk^m}.$$
--
--   This is the probability in which the sparse SYK results (Theorems 5.5–5.7) hold "with probability $\ge 1-O(1/\log n)$ over the randomness of $\mathcal H$".
--
--   **Formalization Note** Hypergraphs are maps `Fin m → KSet n k` (published `SYKEdge.KSet`); the denominator is the cardinality of that finite type, which equals $\binom nk^m$. For $k>n$ there are no $k$-subsets and the value is $0$; every use has $k\le n$.
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, §5.2, p.37 (PDF p.37); §1, p.3 and footnote 6

import Mathlib
import Definitions.Def_SYKEdge_Majorana

namespace SYKEdge.Supplement

open SYKEdge

/-!
# Probability over a random `k`-uniform hypergraph with `m` hyperedges

A. Basu, P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, §5.2, p.37 (PDF p.37) and §1, p.3 (PDF p.3), footnote 6.

A random `k`-uniform hypergraph `H` with `m` hyperedges is `H = (S₁, …, S_m)` with the `S_i`
independent and uniform on `([n] choose k)`; `H` is a multiset in general (p.37).

**Formalization Note.**
* A hypergraph is an `m`-tuple `S : Fin m → KSet n k` of `k`-subsets of `Fin n` (repetitions
  allowed, positions distinguished, as in footnote 6).
* `hyperProb n k m E` is the uniform probability of the event `E` on the finite set of such tuples:
  the number of tuples satisfying `E` divided by the number `(n choose k)^m` of all tuples. This is
  exactly the law of `m` i.i.d. uniform samples from `([n] choose k)`.
* When `k > n` there are no `k`-subsets; then the denominator is `0` (for `m ≥ 1`) and the value is
  `0`. Every use in this mission has `k ≤ n`.
-/

open Classical in
/-- The probability `Pr_H[E(H)]` of an event `E` of a random `k`-uniform hypergraph
`H = (S₁, …, S_m)` with `S_i` i.i.d. uniform on `([n] choose k)` (p.37): the number of tuples
`S : Fin m → KSet n k` satisfying `E` divided by `(n choose k)^m`. -/
noncomputable def hyperProb (n k m : ℕ) (E : (Fin m → KSet n k) → Prop) : ℝ :=
  ((Finset.univ.filter E).card : ℝ) / (Fintype.card (Fin m → KSet n k) : ℝ)

end SYKEdge.Supplement


