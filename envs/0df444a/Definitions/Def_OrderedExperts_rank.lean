-- Prove2me | Definitions.Def_OrderedExperts_rank
-- name    : OrderedExperts_rank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:34:40.649971+00:00
-- url     : https://prove2.me/theorems/ec6cf83d-28f6-4583-b83c-87bf536052a3
-- title:
--   The rank $j_t(f)$ of an expert's recommendation
-- statement:
--   For an expert $f$, $j_t(f)$ is the rank of its recommendation in the active chain: the unique $j\in\{1,\dots,m_t\}$ with $x_{t,j}=a_{t,f}$. Experts recommending the same action share a rank.
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version, sha256 a6480b1e…fe429), Sec. 2.1, p.4

import Definitions.Def_OrderedExperts_chainSize

namespace OrderedExperts

/-- **The rank `jt(f)` of an expert's recommendation.** Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission (held version), Sec. 2.1, p.4:
"We call `j` the rank of `xt,j`, write `jt(f)` for the rank of the recommendation `at,f`".

`rank rec t f` is the 1-based position of `rec t f` in the increasing enumeration of the active
chain, so that `xt,jt(f) = at,f`. -/
noncomputable def rank {A : Type*} [LinearOrder A] {n : ℕ} (rec : ℕ → Fin n → A) (t : ℕ)
    (f : Fin n) : ℕ :=
  ((((active rec t).orderIsoOfFin (rfl : (active rec t).card = chainSize rec t)).symm
      ⟨rec t f, Finset.mem_image_of_mem _ (Finset.mem_univ f)⟩ : Fin (chainSize rec t)) : ℕ) + 1

end OrderedExperts


