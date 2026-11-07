-- Prove2me | Definitions.Def_NSWBetter_SmallGoodFrac
-- name    : NSWBetter_SmallGoodFrac
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:55:40.69097+00:00
-- url     : https://prove2.me/theorems/e7093725-0981-4581-9014-ce628c1f30cc
-- title:
--   Small good fraction property (Definition 4.13)
-- statement:
--   Agent $i$ has the **small good fraction property** in $x$ if
--   $$\sum_{g\in G\setminus L_i}\mathbb 1\{x_{ig}>0.5\}\,x_{ig}v_i(g)<\gamma\mu_i .$$
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Definition 4.13, p.25

import Mathlib
import Definitions.Def_NSWBetter_gamma
import Definitions.Def_NSWBetter_largeSet
import Definitions.Def_NSWBetter_muFrac

namespace NSWBetter

open Classical in
/-- **Small good fraction property (Definition 4.13).**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Definition 4.13, p.25: "an agent i satisfies the small good fraction property in x if Σ_(g∈G\Li) 1{xig > 0.5} xig vi(g) < γµi." -/
def SmallGoodFrac {n m : ℕ} (v : Fin n → Fin m → ℝ) (x : Fin n → Fin m → ℝ) (i : Fin n) : Prop :=
  ∑ g ∈ Finset.univ \ largeSet v x i, (if 1 / 2 < x i g then x i g * v i g else 0) <
    gamma * muFrac v x i

end NSWBetter


