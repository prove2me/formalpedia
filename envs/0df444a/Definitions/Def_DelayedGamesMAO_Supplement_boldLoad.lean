-- Prove2me | Definitions.Def_DelayedGamesMAO_Supplement_boldLoad
-- name    : DelayedGamesMAO_Supplement_boldLoad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:51:45.450205+00:00
-- url     : https://prove2.me/theorems/96909f8c-6ff4-412a-8659-def0a9cb214a
-- title:
--   Load $n_k=|I_k|$ of instance $k$ in the refined BOLD reduction
-- statement:
--   For delays $(d_s)$, a horizon $T$ and an instance index $k$, let $I_k=\{t\in[T]: i_t=k\}$ be the rounds handled by instance $B_k$ of the refined BOLD reduction. Its **load** is
--
--   $$
--   n_k=|I_k|.
--   $$
--
--   The loads sum to $T$, and the regret bound of Theorem 4(i) is written in terms of them.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §4, p.7 and App. B.1, p.33

import Mathlib
import Definitions.Def_DelayedGamesMAO_Supplement_boldIndex

set_option autoImplicit false

namespace DelayedGamesMAO.Supplement

/-- **Load of instance `k`** `n_k = |I_k|`, `I_k = {t ∈ [T] : i_t = k}`, in the refined BOLD
reduction.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), App. B.1, p.33 ("Instance `B_k` handles the subsequence `I_k = {t ∈ [T] : i_t = k}`") and
§4, p.7 (`n_k = |I_k|`). -/
def boldLoad (d : ℕ → ℕ) (T k : ℕ) : ℕ :=
  ((Finset.Icc 1 T).filter (fun t => boldIndex d t = k)).card

end DelayedGamesMAO.Supplement


