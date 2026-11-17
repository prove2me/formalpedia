-- Prove2me | Definitions.Def_SilverRateLB_Supplement_pAny
-- name    : SilverRateLB_Supplement_pAny
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:46:52.793195+00:00
-- url     : https://prove2.me/theorems/41c952d1-9966-448d-8f4c-78a322cc7bc1
-- title:
--   The anytime exponent $p_{\mathrm{any}}$ and prefixes of an infinite schedule
-- statement:
--   The **anytime silver exponent** is
--   $$
--   p_{\mathrm{any}}:=\frac{2p_{\mathrm{sil}}}{1+p_{\mathrm{sil}}}\approx1.1195,
--   $$
--   where $p_{\mathrm{sil}}=\log_2(1+\sqrt2)$ is the published silver exponent.
--
--   An anytime schedule is one infinite nonnegative sequence $H=(h_t)_{t\ge1}$ used at every horizon. Its length-$n$ prefix is $H_n=(h_1,\ldots,h_n)$.
--
--   **Formalization Note** The sequence is indexed from zero in Lean: `H t` represents $h_{t+1}$, and `schedulePrefix H n` lists exactly its first $n$ entries.
-- source:
--   Ye, Liu, Silver Rate Is (Almost) Optimal for Gradient Descent, arXiv:2609.09152 (sha256 6797dde3…), §1, p. 4

import Mathlib
import Definitions.Def_SilverRateLB_pSil

namespace SilverRateLB.Supplement

/-- **The anytime silver exponent** `p_any := 2 p_sil / (1 + p_sil) ≈ 1.1195`.

Ye, Liu, *Silver Rate Is (Almost) Optimal for Gradient Descent*, arXiv:2609.09152, §1,
p. 4: "pany := 2psil/(1 + psil) ≈ 1.1195".

**Formalization Note** The published `SilverRateLB.pSil` is reused verbatim. -/
noncomputable def pAny : ℝ := 2 * SilverRateLB.pSil / (1 + SilverRateLB.pSil)

/-- The length-`n` prefix `H_n = (h_1, …, h_n)` of one infinite schedule.

Ye, Liu, *Silver Rate Is (Almost) Optimal for Gradient Descent*, arXiv:2609.09152, §1,
p. 4: "one infinite schedule H = (ht)t≥1 is used across all horizons, with Hn = (h1, ..., hn)."

**Formalization Note** `H t` represents the paper's `h_{t+1}`; thus the `Fin n` entries are
exactly `h_1, …, h_n`, in order. -/
def schedulePrefix (H : ℕ → ℝ) (n : ℕ) : List ℝ :=
  List.ofFn (fun i : Fin n => H i)

end SilverRateLB.Supplement


