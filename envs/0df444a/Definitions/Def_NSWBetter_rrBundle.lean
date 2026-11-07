-- Prove2me | Definitions.Def_NSWBetter_rrBundle
-- name    : NSWBetter_rrBundle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:50:46.94154+00:00
-- url     : https://prove2.me/theorems/77ad953d-29a8-4129-9f3d-055e382ec582
-- title:
--   Round-robin bundle value $v(W_i)$
-- statement:
--   In the **round robin allocation** $W$ of an instance with $\Delta$ identical agents and goods $v(g_1)\ge\dots\ge v(g_m)$, agent $i$ receives $W_i=\{g_i,g_{\Delta+i},g_{2\Delta+i},\dots\}$. `rrBundle Δ s i` is $v(W_i)$ (agents 0-based).
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 3, p.11 (W_i = {g_i, g_{∆+i}, . . . })

import Mathlib
import Definitions.Def_NSWBetter_sortDesc

namespace NSWBetter

/-- **Value of a round-robin bundle.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 3, p.11: "we define W as the allocation where each agent i receives the bundle Wi = {gi, g∆+i, . . . } — this is the round robin allocation where ties are broken in favor of goods with a lower index."

`rrBundle Δ s i = Σ_(k ≡ i mod Δ) v(g_(k+1))`: agent `i` (0-based) gets the sorted positions `i, Δ + i, 2Δ + i, …`.

**Formalization Note.** An instance with identical valuations is given by its number of agents `Δ` and the multiset `s` of the values of its goods; every notion of Section 3 depends only on these (round-robin bundle values do not depend on how ties are broken, p.23). -/
noncomputable def rrBundle (Δ : ℕ) (s : Multiset ℝ) (i : ℕ) : ℝ :=
  ∑ k ∈ (Finset.range (sortDesc s).length).filter (fun k => k % Δ = i), (sortDesc s).getD k 0

end NSWBetter


