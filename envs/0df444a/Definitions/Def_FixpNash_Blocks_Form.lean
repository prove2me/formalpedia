-- Prove2me | Definitions.Def_FixpNash_Blocks_Form
-- name    : FixpNash_Blocks_Form
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:44:15.919274+00:00
-- url     : https://prove2.me/theorems/2ad422c5-8974-4ee0-a21d-aabfd129c659
-- title:
--   pp. 23–24 — block probabilities and block matching-pennies pairs of players i, i′
-- statement:
--   Consider a finite game in normal form: a finite set of players, for each player $p$ a finite set $S_p$ of pure strategies, and payoffs $u_p(s)\in\mathbb R$ for every pure profile $s=(s_q)_q$. Fix two players $i\neq i'$.
--
--   **Blocks.** The pure strategies of player $i$ are partitioned into blocks, and the blocks are in one-to-one correspondence with the pure strategies of player $i'$. This is recorded by a surjective map $\beta : S_i\to S_{i'}$: the block of a strategy $j\in S_i$ is the one that corresponds to the strategy $\beta(j)$ of $i'$, so the block corresponding to $k\in S_{i'}$ is $\beta^{-1}(k)$, which is nonempty. For a mixed profile $x$ (where $x_p(j)$ is the probability that player $p$ plays $j$) the **total probability of block $k$** is
--   $$
--   b_k(x)=\sum_{j\in S_i:\ \beta(j)=k} x_i(j).
--   $$
--
--   **The payoff form.** Players $i,i'$ form a *block matching-pennies pair* with first term $\mu$, constant $M$ and parameter $n\in\mathbb N$ if
--   1. $u_i(s)=\mu(s)+\mu'_i(s)$, where $\mu'_i(s)=M$ if the block of $s_i$ corresponds to $s_{i'}$ (that is, $\beta(s_i)=s_{i'}$) and $\mu'_i(s)=0$ otherwise;
--   2. $\mu(s)$ does not depend on the strategy $s_{i'}$ of player $i'$;
--   3. $u_{i'}(s)=-M$ if $s_{i'}=\beta(s_i)$, and $u_{i'}(s)=0$ otherwise;
--   4. $$M>6n\max_s|\mu(s)|;$$
--   5. player $i'$ has at most $3n$ pure strategies.
--
--   This is the form "given above" in Lemma 6 of Etessami and Yannakakis: the matching-pennies component that, in their reduction, forces every unprimed player to spread its probability evenly across its blocks.
--
--   **Formalization Note.** The paper says that $\mu_i(s)$ "depends only on the strategies of the unprimed players"; in an abstract game the only meaningful part of this is item 2, which the proof of Lemma 6 does not use and which is included for faithfulness. The bound "$i'$ has at most $3n$ strategies" (item 5) is taken from the proof of Lemma 6 (p. 24), where $n$ is the number of gates of the circuit and the primed players have $n$ or $3n$ strategies (p. 23); in the abstract lemma $n$ is a parameter tied to the data only by items 4 and 5. The maximum $\max_s|\mu(s)|$ is written as the supremum `⨆ s, |μ s|` over the finite type of pure profiles, which is the maximum whenever every player has a strategy. Surjectivity of $\beta$ expresses that every strategy of $i'$ has a block.
-- source:
--   Etessami & Yannakakis, On the complexity of Nash equilibria and other fixed points, author manuscript (SIAM J. Comput. 39 (2010)), Section 3, Step 2, pp. 23–24 (the payoff form before Lemma 6) and proof of Lemma 6, p. 24

import Mathlib
import Definitions.Def_agt_games

namespace FixpNash.Blocks

open Finset

/-- The **total probability of block `k`** of player `i` under the mixed profile `x`
(Etessami–Yannakakis, p. 24, Lemma 6 part 1). The block structure of player `i`'s
strategies is given by `β : S i → S i'`: the block of a strategy `j` of `i` is the one
that corresponds to the strategy `β j` of player `i'`, so block `k` is the fibre
`β ⁻¹' {k}`, and its total probability is `∑_{j : β j = k} x i j`. -/
def blockProb {ι : Type*} {S : ι → Type*} {i i' : ι} [Fintype (S i)] [DecidableEq (S i')]
    (β : S i → S i') (x : ∀ k, S k → ℝ) (k : S i') : ℝ :=
  ∑ j ∈ univ.filter (fun j => β j = k), x i j

/-- The players `i, i'` of the finite game `u` form a **block matching-pennies pair**
of the form given on pp. 23–24 of Etessami–Yannakakis, with block map `β`, first payoff
term `μ`, constant `M` and parameter `n`:

* `i ≠ i'`;
* the strategies of `i` are partitioned into blocks in 1-1 correspondence with the
  strategies of `i'`: the block of a strategy `j` of `i` is the one corresponding to the
  strategy `β j` of `i'`, and every strategy of `i'` has a (nonempty) block, i.e. `β` is
  surjective;
* `μ` does not depend on the strategy of `i'` (the page: "depends only on the strategies
  of the unprimed players");
* `u_i(s) = μ(s) + μ'_i(s)` with `μ'_i(s) = M` if the block of `s_i` corresponds to
  `s_{i'}` and `0` otherwise;
* `u_{i'}(s) = -M` if `s_{i'}` corresponds to the block of `s_i`, and `0` otherwise;
* `M > 6 n max_s |μ(s)|`;
* `i'` has at most `3n` strategies (p. 24, proof of Lemma 6: "since i′ has at most 3n
  strategies"; on p. 23 the primed players have `n` or `3n` strategies). -/
structure IsBlockPair {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ k, Fintype (S k)] [∀ k, DecidableEq (S k)]
    (u : ι → (∀ k, S k) → ℝ) (i i' : ι) (β : S i → S i')
    (μ : (∀ k, S k) → ℝ) (M : ℝ) (n : ℕ) : Prop where
  ne : i ≠ i'
  surjective : Function.Surjective β
  mu_indep : ∀ (s : ∀ k, S k) (a : S i'), μ (Function.update s i' a) = μ s
  payoff_i : ∀ s : ∀ k, S k, u i s = μ s + (if β (s i) = s i' then M else 0)
  payoff_i' : ∀ s : ∀ k, S k, u i' s = (if s i' = β (s i) then -M else 0)
  M_gt : 6 * (n : ℝ) * (⨆ s : (∀ k, S k), |μ s|) < M
  card_le : Fintype.card (S i') ≤ 3 * n

end FixpNash.Blocks


