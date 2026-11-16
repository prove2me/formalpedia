-- Prove2me | Definitions.Def_SingleOrSample_Supplement_IsSafeAlg1
-- name    : SingleOrSample_Supplement_IsSafeAlg1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:32:47.324752+00:00
-- url     : https://prove2.me/theorems/1d03a801-74a1-4f99-8c98-c8e6de77e4ca
-- title:
--   Safe strategies of Algorithm 1: Definitions 5 and 6
-- statement:
--   In Algorithm 1 a strategy names, at every point of agent $i$'s round, the next bucket. Let $G$ be the goods of $R_i$ not yet put into a bucket and $A$ the goods picked so far in the round.
--
--   1. **Definition 5 (additive agents).** Order $R_i$ by weakly decreasing value $v_i(e)$ and cut it into consecutive buckets of $3n$ goods. As a rule on the next bucket: whenever $|G|>3n$, the bucket consists of $3n$ goods of $G$, each of value $v_i(\{x\})$ at least the value $v_i(\{y\})$ of every good $y$ of $G$ outside it.
--   2. **Definition 6 (submodular agents).** Whenever $|G|>3n$, the bucket consists of the $3n$ goods of $G$ with the highest marginal values $v_i(e\mid A)=v_i(A\cup\{e\})-v_i(A)$ relative to the goods picked so far in this round, ties broken arbitrarily.
--
--   In both, the goods left when $|G|\le3n$ form the last, unsampled bucket.
--
--   **Formalization Note** Both are predicates on a strategy, so every tie-breaking is allowed. For Definition 5, every static weakly decreasing order satisfies the predicate; the predicate also lets ties be broken depending on the history and on the picks so far. The predicates constrain the strategy at every history, reachable or not.
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), Definition 5, p.9; Definition 6, p.10

import Mathlib
import Definitions.Def_SingleOrSample_Hist
import Definitions.Def_SingleOrSample_Strategy
import Definitions.Def_SingleOrSample_IsSafe

namespace SingleOrSample.Supplement

open SingleOrSample

/-- Greedy bucketing in Algorithm 1 by a score (Chawla, Huang, Kulkarni, Mehta, Shahkar,
Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission,
arXiv:2609.32286, manuscript sha256 28cd3d7b…, Definitions 5–6, pp.9–10): at every history and every
list of picks so far with `|G| > 3n` (`G = pending h picks`), the named bucket is a subset of `G` with
`3n` items, and every item in it has score at least that of every item of `G` outside it. The score
may depend on the picks so far. -/
def IsSafeAlg1 {m : ℕ} (n : ℕ) (score : List (Finset (Fin m) × Fin m) → Fin m → ℝ)
    (σ : Strategy m) : Prop :=
  ∀ (h : Hist m) (picks : List (Finset (Fin m) × Fin m)), 3 * n < (pending h picks).card →
    σ.bucket h picks ⊆ pending h picks ∧ (σ.bucket h picks).card = 3 * n ∧
    ∀ x ∈ σ.bucket h picks, ∀ y ∈ pending h picks \ σ.bucket h picks,
      score picks y ≤ score picks x

/-- `σ` follows the **safe strategy of Definition 5** for the additive valuation `v` (p.9): order the
remaining goods by weakly decreasing value `v({e})` and cut them into buckets of `3n` consecutive goods;
the first `ℓ_i − 1` buckets are sampled.

**Formalization Note.** As a predicate on the next bucket: it consists of `3n` goods of `G` of the
largest singleton values. Every static weakly decreasing order satisfies it; the predicate also allows
the tie-breaking to depend on the history and on the picks so far. -/
def IsSafeDef5 {m : ℕ} (n : ℕ) (v : Finset (Fin m) → ℝ) (σ : Strategy m) : Prop :=
  IsSafeAlg1 n (fun _ e => v {e}) σ

/-- `σ` follows the **safe strategy of Definition 6** for the submodular valuation `v` (p.10): each
sampled bucket `B_ij` is the `3n` goods of `R_i \ ∪_{j'<j} B_ij'` with the highest marginal values
`v(e | ∪_{j'<j} A_ij')` relative to the items picked so far in this round, ties broken arbitrarily. The
marginal value is the published `SingleOrSample.marginal`. -/
def IsSafeDef6 {m : ℕ} (n : ℕ) (v : Finset (Fin m) → ℝ) (σ : Strategy m) : Prop :=
  IsSafeAlg1 n (fun picks e => marginal v (items picks) e) σ

end SingleOrSample.Supplement


