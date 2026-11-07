-- Prove2me | Definitions.Def_NSWBetter_Gwb
-- name    : NSWBetter_Gwb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:59:38.433187+00:00
-- url     : https://prove2.me/theorems/5dbb2d92-95d6-44d0-b844-9cf846a9e0d0
-- title:
--   Well-behaved globally large goods (Definition 5.1)
-- statement:
--   A good is **globally large** if it is large for at least one agent; it is **well-behaved** if $\sum_{i\in N_{wb}}\mathbb 1\{g\in L_i\}x_{ig}\ge1-\gamma$. $G_{wb}$ is the set of well-behaved globally large goods and $G_{nwb}$ the set of all other goods.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Definition 5.1, p.28

import Mathlib
import Definitions.Def_NSWBetter_gamma
import Definitions.Def_NSWBetter_largeSet
import Definitions.Def_NSWBetter_Nwb

namespace NSWBetter

open Classical in
/-- **Well-behaved globally large goods (Definition 5.1).**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Definition 5.1, p.28: "we refer to a good g as globally large if it is large for at least one agent i … a globally large good g is well-behaved if Σ_(i∈Nwb) 1{g ∈ Li} xig ≥ 1 − γ."; "We use Gwb to denote the set of well-behaved globally large goods". -/
noncomputable def Gwb {n m : ℕ} (v : Fin n → Fin m → ℝ) (x : Fin n → Fin m → ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun g => (∃ i, g ∈ largeSet v x i) ∧
    1 - gamma ≤ ∑ i ∈ Nwb v x, if g ∈ largeSet v x i then x i g else 0

end NSWBetter


