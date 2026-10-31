-- Prove2me | Definitions.Def_FastCore_IsZeroFreeWinnerSet
-- name    : FastCore_IsZeroFreeWinnerSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:29:57.440708+00:00
-- url     : https://prove2.me/theorems/31fed0fb-ce06-4725-8780-754fbbba7bf6
-- title:
--   Winner set of an allocation giving no zero-value set
-- statement:
--   A subset $W\subseteq N$ is a **zero-free winner set** for the bids $\{b_i\}$ if $W=\{i\in N:x^*_i\ne\emptyset\}$ for a maximum welfare allocation $x^*$ with $b_i(x^*_i)>0$ whenever $x^*_i\ne\emptyset$.
--
--   This combines Definition 1 with the paper's convention that "the auction's allocation rule does not allocate sets of zero value". Truncated bids are bids, so the convention applies to them too. The proof of Lemma 2 uses this form: winners satisfy $b_i(x'_i)>\pi_i$, since otherwise "allocation $x'$ gives items for free".
--
--   **Formalization Note** Without this convention Algorithm 1 need not halt. For one bidder, one item, value $1$ and $\epsilon=1/2$, an oracle that always answers $\{1\}$ under bare Definition 1 keeps $S=\{1\}$ forever.
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Definition 1, p.11, and §2, p.10

import Mathlib
import Definitions.Def_FastCore_Bids
import Definitions.Def_FastCore_IsWelfareMaximizing
import Definitions.Def_FastCore_winners

namespace FastCore

/-- `W` is a winner set whose allocation gives no bidder a set of zero value: Definition 1 together
with the convention "the auction's allocation rule does not allocate sets of zero value"
(Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Definition 1, p.11, and §2, p.10).

**Formalization Note.** The convention is applied to the bids at hand, truncated bids included. That
is the form the proof of Lemma 2 uses ("otherwise, allocation x′ gives items for free", p.17), and
without it Algorithm 1 need not halt. -/
def IsZeroFreeWinnerSet {n m : ℕ} (b : Bids n m) (W : Finset (Fin n)) : Prop :=
  ∃ x, IsWelfareMaximizing b x ∧ (∀ i, x i ≠ ∅ → 0 < b i (x i)) ∧ W = winners x

end FastCore


