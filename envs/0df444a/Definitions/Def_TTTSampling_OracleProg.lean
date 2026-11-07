-- Prove2me | Definitions.Def_TTTSampling_OracleProg
-- name    : TTTSampling_OracleProg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:36:14.932474+00:00
-- url     : https://prove2.me/theorems/3101ecf8-9dd4-4052-8a60-434b9fd8a729
-- title:
--   Randomized query algorithms for the oracle $\hat\mu$ and their runs
-- statement:
--   A **randomized query algorithm** for strings of length $n$ over $\Sigma$ is a finite decision tree with three kinds of node:
--
--   1. **return** a full string $v\in\Sigma^n$;
--   2. **sample** an index $i\in\{0,\dots,k-1\}$ from a fixed distribution and continue in branch $i$;
--   3. **query** the oracle at a string $x$, receive $\hat\mu(x)\in\mathbb R_{\ge0}$, and continue in a branch that may depend arbitrarily on the answer.
--
--   Running the tree against an oracle $\hat\mu$ produces a joint distribution of the output string and of the number of query nodes on the executed path.
--
--   This is the model in which "there is a randomized algorithm … which makes at most … queries to $\hat\mu(\cdot)$" of Theorem 3.2 is read. The algorithm may compute freely with the known class $\mathcal F$ (footnote 9: values $\mu(x)$ for $\mu\in\mathcal F$ cost no query), but it learns about $\hat\mu$ only through queries.
--
--   **Formalization Note** Coins are arbitrary real-weighted distributions on finite sets, as Algorithms 2 and 3 need (Bernoulli coins with real parameters, uniform elements of multisets). Every query node counts, including a repeated query, so the count is at least the paper's cached count. Every path of the tree is finite.
-- source:
--   Golowich, Moitra, Rohatgi, The Power of Test-Time Training for Approximate Sampling, arXiv:2606.11437 (version of November 3, 2026), Theorem 3.2, p.18 (PDF p.20); footnote 9, p.6 (PDF p.8)

import Mathlib

namespace TTTSampling

/-- **Randomized query algorithms** for the oracle `µ̂ : Σ^{≤n} → ℝ≥0`, as finite decision trees.

Golowich, Moitra, Rohatgi, arXiv:2606.11437 (version of November 3, 2026), Theorem 3.2, printed
p.18 (PDF p.20): "there is a randomized algorithm … which outputs a sample … and which makes at
most … queries to µ̂(·)"; footnote 9, p.6: for µ ∈ ℱ the algorithm "can determine the value of
µ(x_{1:i}) without paying for any queries".

A program is a tree with three kinds of node:
* `ret v` — stop and output the full string `v ∈ Σⁿ`;
* `sample k p c` — draw `i ∈ {0, …, k−1}` from the distribution `p` and continue with `c i`;
* `query x c` — ask the oracle for `µ̂(x)` and continue with `c (µ̂(x))`.

`run µ̂ A` is the joint law of the output string and of the number of `query` nodes on the
executed path.

**Formalization Note**
* Coins are arbitrary distributions on `Fin k` with real weights (Algorithms 2 and 3 flip
  Bernoulli coins with real parameters and draw uniform elements of multisets).
* Computation between queries is free: a continuation is an arbitrary function of the answers
  seen so far. The program sees `µ̂` only through `query` nodes; `run` has no other access to it,
  and has no access to `µ⋆`.
* Every `query` node on the path counts, including a repeated query of the same string, so this
  count is at least the cached count used by the paper (p.18).
* Each path of the tree is finite (the type is inductive), so a run always ends. -/
inductive OracleProg (α : Type) (n : ℕ) : Type where
  | ret : (Fin n → α) → OracleProg α n
  | sample : (k : ℕ) → PMF (Fin k) → (Fin k → OracleProg α n) → OracleProg α n
  | query : List α → (NNReal → OracleProg α n) → OracleProg α n

/-- The law of a run of an oracle program against the oracle `µ̂`: the output string together
with the number of oracle queries made on that run. -/
noncomputable def OracleProg.run {α : Type} {n : ℕ} (μh : List α → NNReal) :
    OracleProg α n → PMF ((Fin n → α) × ℕ)
  | .ret v => PMF.pure (v, 0)
  | .sample _ p c => p.bind (fun i => (c i).run μh)
  | .query x c => ((c (μh x)).run μh).map (fun r => (r.1, r.2 + 1))

end TTTSampling


