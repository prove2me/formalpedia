-- Prove2me | Definitions.Def_FracTruthSched_IsClassSymmetric
-- name    : FracTruthSched_IsClassSymmetric
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:32:22.311586+00:00
-- url     : https://prove2.me/theorems/c4896050-7bc2-4271-9c28-ee0ec0de3834
-- title:
--   Symmetry under relabelling within classes (property (iv))
-- statement:
--   A mechanism on $MC_\ell$ is **symmetric** if relabelling tasks within any class relabels the allocation in the same way and leaves every machine's disutility unchanged: for every within-class relabelling $\gamma$, every graph input $t$, machine $i$ and task $e$,
--   $$x_{ie}(\gamma t)=x_{i,\gamma(e)}(t),\qquad V_i(\gamma t)=V_i(t),$$
--   where $(\gamma t)_{ie}=t_{i,\gamma(e)}$. This is property (iv) of the padding lemma.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, Lemma 1 (iv), p.9; App. A, Claim 3, p.24

import Mathlib
import Definitions.Def_FracTruthSched_FracMech
import Definitions.Def_FracTruthSched_IsGraphInput
import Definitions.Def_FracTruthSched_relabel
import Definitions.Def_FracTruthSched_disutility
import Definitions.Def_FracTruthSched_IsClassPerm

set_option autoImplicit false

namespace FracTruthSched

/-- **Symmetry** of a mechanism on `MC_ℓ` (Anastasiadis et al., arXiv:2611.06642v1, Lemma 1 (iv), p.9:
"Relabelling tasks within any class Q{i,j} relabels the allocation in the same way. Each machine's
disutility is unchanged by the corresponding relabelling of the input."): for every within-class
relabelling `γ` and graph input `t`, `x_ie(γt) = x_{i,γ(e)}(t)` and `V_i(γt) = V_i(t)`, where
`(γt)_ie = t_{i,γ(e)}` (`relabel`, the convention of App. A, p.23). -/
def IsClassSymmetric {n ℓ : ℕ} (M : FracMech n (CoreTask n ℓ)) : Prop :=
  ∀ γ : Equiv.Perm (CoreTask n ℓ), IsClassPerm γ → ∀ t, IsGraphInput t →
    (∀ i e, M.x (relabel γ t) i e = M.x t i (γ e)) ∧
      ∀ i, disutility M (relabel γ t) i = disutility M t i

end FracTruthSched


