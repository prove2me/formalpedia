-- Prove2me | Definitions.Def_AlmostMMS_mmsProfileIn
-- name    : AlmostMMS_mmsProfileIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:48:25.852866+00:00
-- url     : https://prove2.me/theorems/9a573d55-1683-4e9d-b203-fbc93925e0dc
-- title:
--   Definitions 3.4, 4.1, pp.22, 28 — the MMS head profiles $\pi_{i,j}$, $\pi^E_{i,j}$, $\pi^S_{i,j}$
-- statement:
--   For a set $X$ of items the **MMS sub-profile** of agent $i$ and bundle $j$ is the multiset
--   $$
--   \pi^X_{i,j}=\Big\{\frac{\lfloor q^2 v_i(e)\rfloor}{q^2} : e\in B_{i,j}\cap X,\ v_i(e)\ge 1/q\Big\}.
--   $$
--   The **MMS head profile** $\pi_{i,j}$ is the case $X=M$. Two items of equal rounded value contribute two demands, and $\pi_{i,j}=\pi^E_{i,j}\uplus\pi^S_{i,j}$ for a partition $M=E+S$.
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Definition 3.4, p.22; Definition 4.1, p.28

import Mathlib
import Definitions.Def_AlmostMMS_OrderedInstance

namespace AlmostMMS

open Finset

open Classical in
/-- **MMS sub-profile** `π^X_{i,j}` (Definition 4.1, p.28): the multiset of rounded values
`⌊q² v_i(e)⌋/q²` over the items `e ∈ B_{i,j} ∩ X` with `v_i(e) ≥ 1/q`.
Feige, Grinberg, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…).

**Formalization Note.** Two items of equal rounded value contribute two demands: the map is taken on
the multiset of items. For a partition `M = E + S` the paper's `π^E_{i,j}` and `π^S_{i,j}` are
`mmsProfileIn J q i j E` and `mmsProfileIn J q i j S`. -/
noncomputable def mmsProfileIn {n m d : ℕ} (J : OrderedInstance n m d) (q : ℕ) (i : Fin n) (j : Fin d)
    (X : Finset (Fin m)) : Multiset ℝ :=
  (univ.filter fun e => J.B i e = j ∧ 1 / (q : ℝ) ≤ J.v i e ∧ e ∈ X).val.map
    fun e => (⌊(q : ℝ) ^ 2 * J.v i e⌋ : ℝ) / (q : ℝ) ^ 2

/-- **MMS head profile** `π_{i,j}` (Definition 3.4, p.22): `π^M_{i,j}` for the whole item set. -/
noncomputable def mmsProfile {n m d : ℕ} (J : OrderedInstance n m d) (q : ℕ) (i : Fin n) (j : Fin d) :
    Multiset ℝ :=
  mmsProfileIn J q i j univ

end AlmostMMS


