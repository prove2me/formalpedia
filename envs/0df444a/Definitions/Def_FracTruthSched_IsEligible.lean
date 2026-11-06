-- Prove2me | Definitions.Def_FracTruthSched_IsEligible
-- name    : FracTruthSched_IsEligible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:31:51.458523+00:00
-- url     : https://prove2.me/theorems/39da2f5f-aed8-41a9-83c0-731301c2887a
-- title:
--   Eligibility of an allocation function on $MC_\ell$ (property (i))
-- statement:
--   An allocation function on $MC_\ell$ is **eligible** if at every graph input every edge is allocated only to its endpoints and every self-loop only to its owner:
--   $$x_{ie}(t)=0\quad\text{whenever } i \text{ is not incident to } e.$$
--   This is property (i) of the padding lemma.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, Definition 2, p.8; Lemma 1 (i), p.9

import Mathlib
import Definitions.Def_FracTruthSched_FracMech
import Definitions.Def_FracTruthSched_IsGraphInput

set_option autoImplicit false

namespace FracTruthSched

/-- **Eligibility** of an allocation function on `MC_ℓ` (Anastasiadis et al., arXiv:2611.06642v1,
Definition 2, p.8, and Lemma 1 (i), p.9: "Edges are allocated only to their endpoints, and
self-loops only to their owners"): at every graph input, a machine not incident to a core task
receives no fraction of it. -/
def IsEligible {n ℓ : ℕ} (M : FracMech n (CoreTask n ℓ)) : Prop :=
  ∀ t, IsGraphInput t → ∀ i e, ¬ incident i e → M.x t i e = 0

end FracTruthSched


