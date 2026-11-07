-- Prove2me | Definitions.Def_NSWBetter_vals
-- name    : NSWBetter_vals
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:49:06.803116+00:00
-- url     : https://prove2.me/theorems/d4fe95c2-4d34-4009-af2f-de793d59dc36
-- title:
--   Multiset of the values of the goods
-- statement:
--   For a common valuation $v$ on goods $G=\{g_1,\dots,g_m\}$, $\mathrm{vals}(v)$ is the multiset $\{\!\{v(g):g\in G\}\!\}$ of the values of the goods.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 3, p.11

import Mathlib

namespace NSWBetter

/-- **Value multiset of an identical-valuation instance.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 3, p.11: "an instance … with ∆ agents, all with the same valuation function v over a set of goods G = {g1, . . . , gm}".

`vals v` is the multiset `{v(g) : g ∈ G}`. -/
def vals {m : ℕ} (v : Fin m → ℝ) : Multiset ℝ := Finset.univ.val.map v

end NSWBetter


