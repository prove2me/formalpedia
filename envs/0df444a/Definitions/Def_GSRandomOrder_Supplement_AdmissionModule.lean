-- Prove2me | Definitions.Def_GSRandomOrder_Supplement_AdmissionModule
-- name    : GSRandomOrder_Supplement_AdmissionModule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:08:45.88922+00:00
-- url     : https://prove2.me/theorems/0000a077-ac9c-476b-8c5c-e661951568c9
-- title:
--   Admission module for a proposal map $P$ with cutoff $s$
-- statement:
--   Fix a proposal map $P$, which assigns to every $S\subseteq N$ a set $P(S)\subseteq S$, and a cutoff $s$. An **admission module** for $P$ is an online algorithm that observes every arrival and accepts or rejects each arrival irrevocably, using its own coins, and that rejects $g_k$ whenever $k\le s$ or $g_k\notin P(S_k)$. Its final accepted set is $A$.
--
--   The module is described by its acceptance probabilities: when $g_1,\dots,g_k$ have arrived and its decisions on $g_1,\dots,g_{k-1}$ are $d_1,\dots,d_{k-1}$, it accepts $g_k$ with probability $p(g_1,\dots,g_k;\,d_1,\dots,d_{k-1})\in[0,1]$. Given the order $\sigma$, the decisions $d$ then have probability
--   $$
--   \prod_{j}\bigl(d_j\ ?\ p_j : 1-p_j\bigr),
--   $$
--   and $A=\{g_k: d_k=\text{accept}\}$.
--
--   **Formalization Note** Every randomized online module with perfect recall has acceptance probabilities of this form with the same joint law of order and decisions (Kuhn's theorem), and the conditions of Definition 4.4 depend only on that law. The probabilities may depend on $v$ and $P$ in any way, so this class contains every module of the paper. The rejection rules are imposed on every input. Decisions are indexed by the arrival position $j=k-1$.
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), §4.3, p.15, "Admission modules"

import Mathlib
import Definitions.Def_GSRandomOrder_Supplement_prefixSet

set_option autoImplicit false

namespace GSRandomOrder.Supplement

/-- **Admission module** for a proposal map `P` with cutoff `s` (R. Paes Leme, M. Pál, N. Patel,
*Gross Substitutes Welfare in Random Order*, STOC 2027 submission, manuscript sha256 69787f50…,
§4.3, p.15, "Admission modules"): an online algorithm that observes every arrival and accepts or
rejects each arrival irrevocably, rejecting `g_k` whenever `k ≤ s` or `g_k ∉ P(S_k)`.

The module is given by its behavioural rule: `prob gs ds ∈ [0, 1]` is the probability of
accepting the `k`-th arrival when `gs = [g_1, …, g_k]` are the arrivals so far and
`ds = [d_1, …, d_{k−1}]` its own earlier decisions (`true` = accepted).

**Formalization Note.** Every randomized online module (arrivals and own coins, perfect recall)
induces a joint law of (arrival order, decisions) that is realized by such a rule (Kuhn's
theorem), and the conditions of Definition 4.4 depend only on that joint law; the rule may depend
on `v` and `P` in any way, so the class contains every module of the paper (it is larger, which
makes a statement "for every module" stronger). The rejection conditions are imposed for every
input; on inputs that cannot occur they do not constrain anything. `gs.toFinset` is `S_k` and
`gs.getLast?` is `g_k`. -/
structure AdmissionModule (n : ℕ) (P : Finset (Fin n) → Finset (Fin n)) (s : ℕ) where
  /-- Acceptance probability of the current arrival, given the arrivals and earlier decisions. -/
  prob : List (Fin n) → List Bool → ℝ
  prob_nonneg : ∀ gs ds, 0 ≤ prob gs ds
  prob_le_one : ∀ gs ds, prob gs ds ≤ 1
  /-- Rejects `g_k` for `k ≤ s`. -/
  reject_cutoff : ∀ gs ds, gs.length ≤ s → prob gs ds = 0
  /-- Rejects `g_k` when `g_k ∉ P(S_k)`. -/
  reject_unproposed : ∀ gs ds g, gs.getLast? = some g → g ∉ P gs.toFinset → prob gs ds = 0

/-- The probability that the module's decisions are `d` (`d j` = decision on the arrival at
position `j`, i.e. on `g_{j+1}`) given the arrival order `σ`:
`Π_j (d_j ? p_j : 1 − p_j)` with `p_j` the rule's acceptance probability at step `j + 1`. -/
def AdmissionModule.weight {n : ℕ} {P : Finset (Fin n) → Finset (Fin n)} {s : ℕ}
    (M : AdmissionModule n P s) (σ : Fin n ≃ Fin n) (d : Fin n → Bool) : ℝ :=
  ∏ j : Fin n,
    if d j then M.prob (prefixList σ (j.val + 1)) (decisionList d j.val)
    else 1 - M.prob (prefixList σ (j.val + 1)) (decisionList d j.val)

/-- The accepted set `A = {g_{j+1} : d_j = true}` of a decision sequence under the order `σ`. -/
def acceptedSet {n : ℕ} (σ : Fin n ≃ Fin n) (d : Fin n → Bool) : Finset (Fin n) :=
  (Finset.univ.filter fun j => d j = true).image σ

end GSRandomOrder.Supplement


