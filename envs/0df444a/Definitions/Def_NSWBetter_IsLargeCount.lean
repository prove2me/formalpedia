-- Prove2me | Definitions.Def_NSWBetter_IsLargeCount
-- name    : NSWBetter_IsLargeCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:51:21.339313+00:00
-- url     : https://prove2.me/theorems/94dde4f9-0bbe-4040-8b2f-b26fcdfc6734
-- title:
--   The large goods are the $\ell$ most valuable goods
-- statement:
--   In an instance with $\Delta$ identical agents and goods $v(g_1)\ge\dots\ge v(g_m)$, the set of **large goods** $L$ with $|L|=\ell$ is a set of at most $\Delta-1$ goods such that
--   1. $v(g)>\dfrac{v(G\setminus L)}{\Delta-\ell}$ for every $g\in L$, and
--   2. $v(g)\le\dfrac{v(G\setminus L)}{\Delta-\ell}$ for every $g\in G\setminus L$.
--
--   Because these are threshold conditions, $L$ must be $\{g_1,\dots,g_\ell\}$; `IsLargeCount Δ s ℓ` states the two conditions for this set together with $\ell\le\Delta-1$.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Definition 3.2, p.11 (Large and Small Goods)

import Mathlib
import Definitions.Def_NSWBetter_sortDesc
import Definitions.Def_NSWBetter_tailSum

namespace NSWBetter

/-- **Large goods (Definition 3.2), as a count.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Definition 3.2, p.11: "we define the set of large goods L (with |L| = ℓ) as the set of at most ∆−1 goods that satisfies (i) for each g ∈ L, v(g) > v(G\L)/(∆−ℓ), and (ii) for each g ∈ G \ L, v(g) ≤ v(G\L)/(∆−ℓ)."

`IsLargeCount Δ s ℓ`: `ℓ ≤ Δ − 1`, and the `ℓ` most valuable goods (sorted positions `< ℓ`) satisfy (i), the others (ii), with `v(G \ L) = tailSum s ℓ`.

**Formalization Note.** Conditions (i)–(ii) are threshold conditions, so a set `L` satisfies them exactly when it consists of the `ℓ` most valuable goods and no value is tied across the threshold; the set is therefore determined by `ℓ`. An instance with identical valuations is given by its number of agents `Δ` and the multiset `s` of the values of its goods; every notion of Section 3 depends only on these (round-robin bundle values do not depend on how ties are broken, p.23). -/
def IsLargeCount (Δ : ℕ) (s : Multiset ℝ) (ℓ : ℕ) : Prop :=
  ℓ + 1 ≤ Δ ∧ ℓ ≤ (sortDesc s).length ∧
  (∀ k, k < ℓ → tailSum s ℓ / ((Δ : ℝ) - ℓ) < (sortDesc s).getD k 0) ∧
  (∀ k, ℓ ≤ k → k < (sortDesc s).length →
    (sortDesc s).getD k 0 ≤ tailSum s ℓ / ((Δ : ℝ) - ℓ))

end NSWBetter


