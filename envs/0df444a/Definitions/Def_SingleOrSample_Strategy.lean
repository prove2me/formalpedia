-- Prove2me | Definitions.Def_SingleOrSample_Strategy
-- name    : SingleOrSample_Strategy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:47:22.575235+00:00
-- url     : https://prove2.me/theorems/fb9f38dc-7af3-485b-93c2-e26070fbc321
-- title:
--   Strategies in Algorithm 2 and their legality
-- statement:
--   A **strategy** in Algorithm 2 prescribes, for every history, whether to take a special round and which good to select, and, for every history and every list of picks so far in the current round, which bucket to name next. A strategy is thus a deterministic function of everything that has happened, and of no future coin.
--
--   A strategy is **legal** for $n$ agents and parameter $k$ if, at every history with $t<n$, a selected good lies in the remaining set, and whenever $|G|\ge k(n-t)$ the named bucket is a subset of $G$ of size exactly $k(n-t)$.
--
--   This class contains the behaviour of the other agents in Theorem 4.1: they may see the whole past, including the coins already tossed.
--
--   **Formalization Note** A randomized strategy is a mixture of deterministic ones. The bound of Theorem 4.1 does not depend on the profile, so it passes through mixtures. The page's $B_{ij}\subset G$ is read as $\subseteq$, because line 11 allows $|G|=k(n-t)$. Legality is required at all histories with $t<n$, reachable or not; the values of a strategy at unreachable histories do not affect its law.
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), Algorithm 2, p.12; proof of Lemma 4.4, p.16

import Mathlib
import Definitions.Def_SingleOrSample_Hist

namespace SingleOrSample

/-- A deterministic strategy in Algorithm 2 (Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample:
Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286, manuscript
sha256 28cd3d7b…, lines 4–6 and 12, p.12): `choose h = some e` asks for a special round selecting `e`
and `choose h = none` samples; `bucket h picks` names the next bucket, given the history and the current
round's picks so far.

**Formalization Note.** A strategy sees every earlier round with its buckets and picks and the current
round's picks, as in "arbitrary functions of the history so far" (proof of Lemma 4.4, p.16), and never a
future coin. Valuations enter only through `IsSafe`, so a strategy may depend on every valuation. A
randomized strategy is a mixture of deterministic ones; since the failure probabilities of Theorem 4.1
do not depend on the profile, the bound passes through mixtures. -/
structure Strategy (m : ℕ) where
  choose : Hist m → Option (Fin m)
  bucket : Hist m → List (Finset (Fin m) × Fin m) → Finset (Fin m)

/-- A strategy obeys the rules of Algorithm 2 with `n` agents and parameter `k` (p.12): a selected item
lies in the remaining set (line 6), and whenever `|G| ≥ k(n − t)` the named bucket is a subset of `G` of
size exactly `k(n − t)` (lines 11–12), with `t` the number of special rounds at arrival.

**Formalization Note.** Line 12's `B_ij ⊂ G` is read as `⊆`, as line 11 allows `|G| = k(n − t)`. The
condition covers every history with `t < n`, reachable or not; on a run `t ≤ j < n` always holds, and
the off-run values of a strategy do not affect its law. -/
def Legal {m : ℕ} (n k : ℕ) (σ : Strategy m) : Prop :=
  ∀ h : Hist m, specialCount h < n →
    (∀ e, σ.choose h = some e → e ∈ remaining h) ∧
    ∀ picks : List (Finset (Fin m) × Fin m),
      k * (n - specialCount h) ≤ (pending h picks).card →
        σ.bucket h picks ⊆ pending h picks ∧
        (σ.bucket h picks).card = k * (n - specialCount h)

end SingleOrSample


