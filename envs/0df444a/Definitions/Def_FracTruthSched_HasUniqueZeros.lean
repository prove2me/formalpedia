-- Prove2me | Definitions.Def_FracTruthSched_HasUniqueZeros
-- name    : FracTruthSched_HasUniqueZeros
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:32:02.933794+00:00
-- url     : https://prove2.me/theorems/7c7cc1ce-0900-4daa-bc91-2fbe8c3676ef
-- title:
--   Unique zeros (property (ii))
-- statement:
--   An allocation function on $MC_\ell$ has **unique zeros** if every edge with a unique zero-cost endpoint is allocated wholly to that endpoint: for every graph input $t$ and every edge $e$ with endpoints $i\ne j$,
--   $$t_{ie}=0<t_{je}\ \Longrightarrow\ x_{ie}(t)=1.$$
--   This is property (ii) of the padding lemma.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, Lemma 1 (ii), p.9

import Mathlib
import Definitions.Def_FracTruthSched_FracMech
import Definitions.Def_FracTruthSched_IsGraphInput

set_option autoImplicit false

namespace FracTruthSched

/-- **Unique zeros** (Anastasiadis et al., arXiv:2611.06642v1, Lemma 1 (ii), p.9: "Every edge with a
unique zero-cost endpoint is allocated wholly to that endpoint"): at every graph input, if an edge
`e` has endpoints `i ≠ j` with `t_ie = 0 < t_je`, then `x_ie(t) = 1`.

**Formalization Note.** `e.isLeft` says that `e` is an edge (not a self-loop); its two endpoints are
the two distinct machines incident to it. -/
def HasUniqueZeros {n ℓ : ℕ} (M : FracMech n (CoreTask n ℓ)) : Prop :=
  ∀ t, IsGraphInput t → ∀ (e : CoreTask n ℓ) (i j : Fin n), e.isLeft → incident i e →
    incident j e → i ≠ j → t i e = 0 → 0 < t j e → M.x t i e = 1

end FracTruthSched


