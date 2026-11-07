-- Prove2me | Definitions.Def_RankingCertGap_RankingRun
-- name    : RankingCertGap_RankingRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:48:59.372311+00:00
-- url     : https://prove2.me/theorems/7f3cfbc9-0eff-4831-a97f-4cd589da1a27
-- title:
--   The RANKING run on a real rank vector
-- statement:
--   Fix a rank vector $Y=(Y_i)_{i\in I}$ of real numbers. **RANKING** processes the online arrivals in order, and matches each arrival $j$ to its unmatched neighbour of minimum rank, if it has one. For a prefix of length $t$, the run records the partner of each arrival among the first $t$; the arrivals that have not been processed have no partner.
--
--   An offline vertex $i$ is **safe** after a prefix when it is still unmatched; this is the event $\mathcal E_i$. After all arrivals, $X_i$ and $X_j$ are the indicators that the offline vertex $i$ and the online vertex $j$ are matched. The **partner rank** $Y_j$ is the rank of the partner of $j$, or $1$ when $j$ is unmatched. $\mathrm{RANKING}(G)$ is the number of matched arrivals.
--
--   This is the common execution model of every statement in the mission. The gain-sharing function never influences it.
--
--   **Formalization Note** The source uses strict rank comparisons and notes that ranks are distinct with probability one. Lean needs a total rule, so a tie goes to the least index among the minimum-rank neighbours; this concerns a null set of rank vectors. The predicate $\texttt{DistinctRanks}$ says that the entries of $Y$ are distinct and lie in $[0,1]$.
-- source:
--   Xu, Certifying Capacity and Gaps of the Rank-Dependent Gain-Sharing Framework for Ranking, arXiv:2610.17545 (held file sha256 75896dd9…), §1, p.1; §1.1, pp.2–3; §5.1, p.17

import Mathlib
import Definitions.Def_RankingCertGap_Inst

namespace RankingCertGap

variable {m n : ℕ}

/-- The offline vertex `i` is matched by the partial assignment `M` of online vertices. -/
def taken (M : Fin n → Option (Fin m)) (i : Fin m) : Prop := ∃ j, M j = some i

open Classical in
/-- The vertex of `s` of minimum rank under the rank vector `Y`, and `none` when `s` is empty.

**Formalization Note.** Xu, arXiv:2610.17545 (held file sha256 75896dd9…), p.17: "We use strict rank
comparisons throughout; the offline ranks are distinct with probability one." Lean needs a total
rule, so a tie goes to the least index among the minimum-rank vertices. This affects only a
null set of rank vectors. -/
noncomputable def pick (Y : Fin m → ℝ) (s : Finset (Fin m)) : Option (Fin m) :=
  if h : (s.filter fun i => ∀ k ∈ s, Y i ≤ Y k).Nonempty then
    some ((s.filter fun i => ∀ k ∈ s, Y i ≤ Y k).min' h)
  else none

namespace Inst

open Classical in
/-- One RANKING step: the arrival `j` is matched to its unmatched neighbour of minimum rank, if any.
Xu, arXiv:2610.17545 (held file sha256 75896dd9…), §1, p.1. -/
noncomputable def step (G : Inst m n) (Y : Fin m → ℝ) (M : Fin n → Option (Fin m)) (j : Fin n) :
    Fin n → Option (Fin m) :=
  Function.update M j (pick Y ((G.N j).filter fun i => ¬ taken M i))

/-- The partial matching of RANKING on the rank vector `Y` after the arrival prefix of length `t`:
arrivals `0, …, t - 1` have been processed. `run G Y t j` is the partner of `j`, if any. -/
noncomputable def run (G : Inst m n) (Y : Fin m → ℝ) : ℕ → Fin n → Option (Fin m)
  | 0 => fun _ => none
  | t + 1 => if h : t < n then G.step Y (G.run Y t) ⟨t, h⟩ else G.run Y t

/-- The offline vertex `i` is *safe* (still unmatched) after the arrival prefix of length `t`:
the event `E_i`, p.17. -/
def safeAfter (G : Inst m n) (Y : Fin m → ℝ) (t : ℕ) (i : Fin m) : Prop := ¬ taken (G.run Y t) i

open Classical in
/-- `X_i`, the indicator that the offline vertex `i` is matched in the final matching (p.3). -/
noncomputable def Xoff (G : Inst m n) (Y : Fin m → ℝ) (i : Fin m) : ℝ :=
  if taken (G.run Y n) i then 1 else 0

/-- `X_j`, the indicator that the online vertex `j` is matched in the final matching (p.3). -/
noncomputable def Xon (G : Inst m n) (Y : Fin m → ℝ) (j : Fin n) : ℝ :=
  if (G.run Y n j).isSome then 1 else 0

/-- `Y_j`: "If `j` is matched, let `Y_j` denote the rank of its offline partner; otherwise set
`Y_j := 1`" (p.3). -/
noncomputable def partnerRank (G : Inst m n) (Y : Fin m → ℝ) (j : Fin n) : ℝ :=
  match G.run Y n j with
  | some i => Y i
  | none => 1

/-- `RANKING(G)` on the rank vector `Y`: the cardinality of the final matching. -/
noncomputable def rankingCard (G : Inst m n) (Y : Fin m → ℝ) : ℕ :=
  (Finset.univ.filter fun j => (G.run Y n j).isSome).card

end Inst

/-- A rank vector with distinct entries in `[0, 1]`: the event of distinct offline ranks (p.17). -/
def DistinctRanks (Y : Fin m → ℝ) : Prop :=
  Function.Injective Y ∧ ∀ i, Y i ∈ Set.Icc (0 : ℝ) 1

end RankingCertGap


