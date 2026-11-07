-- Prove2me | Definitions.Def_SingleOrSample_Hist
-- name    : SingleOrSample_Hist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:46:38.048753+00:00
-- url     : https://prove2.me/theorems/5e1bfebb-78a8-4fce-875a-a338009e0212
-- title:
--   Rounds, histories, the remaining set $R_i$, the counter $t$ and the set $G$ of Algorithm 2
-- statement:
--   These are the bookkeeping objects of the Single-or-Sample algorithm (Algorithm 2). A **round** is either a special round selecting one good $e$, or a non-special round recorded as the list of pairs $(B_{ij},e_{ij})$ of buckets and picked goods, oldest first. A **history** is the list of rounds served so far, oldest first.
--
--   From a history one reads:
--
--   1. the goods allocated in a round: $\{e\}$ in a special round, and the picked goods $A_i=\bigcup_j\{e_{ij}\}$ otherwise;
--   2. the remaining set $R_{i+1}=[m]\setminus(A_1\cup\dots\cup A_i)$. Goods of a bucket that were not picked stay in it;
--   3. the counter $t$ of special rounds;
--   4. inside a non-special round, the set $G$: the remaining set minus all buckets formed so far in this round;
--   5. the bundle of an agent: the goods of that agent's round, and $\emptyset$ if the round has not happened.
--
--   **Formalization Note** The history keeps every bucket and pick, which is what "arbitrary functions of the history so far" (proof of Lemma 4.4) requires. Agent indices start at $0$: Lean's agent $i$ is the page's agent $i+1$.
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), Algorithm 2, p.12

import Mathlib

namespace SingleOrSample

/-- What happened in one served round of Algorithm 2 (Chawla, Huang, Kulkarni, Mehta, Shahkar,
Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission,
arXiv:2609.32286, manuscript sha256 28cd3d7b…, p.12): a special round selecting `e` (lines 6–8), or a
non-special round with its list of buckets and picked items `(B_ij, e_ij)`, oldest first (lines 10–16). -/
inductive Round (m : ℕ) where
  | special (e : Fin m) : Round m
  | sampled (picks : List (Finset (Fin m) × Fin m)) : Round m

/-- The **history**: the rounds served so far, oldest first. Its length is the number of agents already
served.

**Formalization Note.** It records every bucket and every pick, which is what "arbitrary functions of
the history so far" (proof of Lemma 4.4, p.16) needs. -/
abbrev Hist (m : ℕ) := List (Round m)

/-- The items picked in a list of (bucket, pick) pairs: `∪_j {e_ij}` (Algorithm 2, line 15, p.12). -/
def items {m : ℕ} (picks : List (Finset (Fin m) × Fin m)) : Finset (Fin m) :=
  (picks.map Prod.snd).toFinset

/-- The goods allocated in one round: `{e}` in a special round (line 7), and `A_i = ∪_j {e_ij}`
otherwise (line 15). Items of a bucket that were not picked are not allocated. -/
def Round.goods {m : ℕ} : Round m → Finset (Fin m)
  | .special e => {e}
  | .sampled picks => items picks

/-- The remaining set `R_{i+1}` after a history: all goods minus every allocated good (lines 1, 8, 16,
p.12). Unpicked items of a bucket stay in it. -/
def remaining {m : ℕ} (h : Hist m) : Finset (Fin m) :=
  h.foldl (fun R r => R \ r.goods) Finset.univ

/-- The counter `t`: the number of special rounds in the history (Algorithm 2, line 8, p.12). -/
def specialCount {m : ℕ} (h : Hist m) : ℕ :=
  h.countP (fun r => match r with | .special _ => true | .sampled _ => false)

/-- The set `G` of Algorithm 2 (lines 10, 14, p.12) inside a non-special round: the remaining set minus
every bucket formed so far in this round. -/
def pending {m : ℕ} (h : Hist m) (picks : List (Finset (Fin m) × Fin m)) : Finset (Fin m) :=
  picks.foldl (fun G p => G \ p.1) (remaining h)

/-- The bundle of the agent with index `i` in a history: the goods of round `i`, and `∅` if that round
is absent. Lean's index `i` (from `0`) is the page's agent `i + 1`. -/
def allocOf {m n : ℕ} (h : Hist m) (i : Fin n) : Finset (Fin m) :=
  match h[(i : ℕ)]? with
  | some r => r.goods
  | none => ∅

end SingleOrSample


