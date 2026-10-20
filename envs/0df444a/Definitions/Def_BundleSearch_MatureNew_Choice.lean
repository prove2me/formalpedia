-- Prove2me | Definitions.Def_BundleSearch_MatureNew_Choice
-- name    : BundleSearch_MatureNew_Choice
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:24:42.251161+00:00
-- url     : https://prove2.me/theorems/a14401bd-df4e-4676-be9b-13cfb6e30726
-- title:
--   Footnote 10 — non-obligatory search choice and no-search tie rule
-- statement:
--   A customer chooses among buying immediately without search, searching, and leaving. Let $n$ be the expected payoff from an immediate purchase and $s$ the expected payoff from searching, including its cost. The paper's tie rule selects an immediate purchase whenever it is nonnegative and at least as good as search:
--
--   $$\operatorname{BuyNow}(n,s)\iff s\le n\text{ and }0\le n.$$
--
--   Otherwise the customer searches when $s\ge0$; if neither condition holds, she leaves. This reusable rule fixes the demand at indifferent prices. It implements the equilibrium selection in footnote 10, under which indifferent customers buy without search.
-- source:
--   Wu, Jin & Chen, Managing Customer Search via Product Bundling, SSRN working paper 3692871 (version of 2022-01-17), p. 10, footnote 10

import Mathlib

namespace BundleSearch.MatureNew

/-- A customer buys without search when that option has nonnegative payoff and is at least
as good as searching. This resolves a tie in favor of buying without search. -/
def BuysWithoutSearch (ns s : ℝ) : Prop := s ≤ ns ∧ 0 ≤ ns

/-- Searching is payoff-maximizing when buying without search is not chosen and its
expected payoff is nonnegative. At a tie with leaving, the product-specific rule
also checks whether search can lead to a purchase. -/
def Searches (ns s : ℝ) : Prop := ¬ BuysWithoutSearch ns s ∧ 0 ≤ s

end BundleSearch.MatureNew


