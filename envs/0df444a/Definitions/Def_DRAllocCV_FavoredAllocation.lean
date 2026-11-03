-- Prove2me | Definitions.Def_DRAllocCV_FavoredAllocation
-- name    : DRAllocCV_FavoredAllocation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:12.721536+00:00
-- url     : https://prove2.me/theorems/156f4194-e84e-4391-a5e6-8dd3dba761e1
-- title:
--   Case (i) of a favored-agent mechanism
-- statement:
--   In scenario $t$, the mechanism $(p,q)$ **allocates to the favored agent $i^\star$ without inspection** if
--
--   $$
--   p_{i^\star}(t)=1,\qquad q_{i^\star}(t)=0,\qquad p_i(t)=q_i(t)=0\ \ \text{for all } i\ne i^\star .
--   $$
--
--   This is case (i) of Definition 3.
-- source:
--   Bayrak, Koçyiğit, Kuhn, Pınar, Distributionally Robust Optimal Allocation with Costly Verification, arXiv:2211.15122v3, §2, p.7, Definition 3 (i)

import Mathlib

namespace DRAllocCV

/-- **Case (i) of a favored-agent mechanism** (Definition 3 (i), Bayrak, Koçyiğit, Kuhn, Pınar, *Distributionally Robust Optimal Allocation with Costly Verification*, arXiv:2211.15122v3, §2, p.7): in scenario `t`
the favored agent `i⋆` receives the good without inspection, `pᵢ⋆(t) = 1`, `qᵢ⋆(t) = 0`, and
`pᵢ(t) = qᵢ(t) = 0` for all `i ≠ i⋆`. -/
def FavoredAllocation {ι : Type*} (istar : ι) (p q : ι → (ι → ℝ) → ℝ) (t : ι → ℝ) : Prop :=
  p istar t = 1 ∧ q istar t = 0 ∧ ∀ i, i ≠ istar → p i t = 0 ∧ q i t = 0

end DRAllocCV


