-- Prove2me | Definitions.Def_DecDynMatch_selectArm
-- name    : DecDynMatch_selectArm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:56:55.436846+00:00
-- url     : https://prove2.me/theorems/fcc88f96-3dfe-400d-b567-41589176e860
-- title:
--   SelectArm: the arm an SC-DA player proposes to
-- statement:
--   Given its round-start state, player $i$ proposes to
--   $$
--   x=\begin{cases}
--   \text{BUS}=0 & m=\textsf{Seek},\\
--   \sigma_s & m=\textsf{Sweep},\\
--   y & m=\textsf{Replay},\\
--   \text{PARK}=1 & m=\textsf{Work},\ 0\le h<2K \ (\text{Park}),\\
--   p_i(1) & m=\textsf{Work},\ 2K\le h\le 4K \ (\text{Top}),\\
--   p_i(k) & m=\textsf{Work},\ 4K<h<J \ (\text{DA}).
--   \end{cases}
--   $$
--   **Formalization Note** With the 0-based ranking, $p_i(1)$ is `pref I i 0` and $p_i(k)$ is `pref I i (k - 1)`.
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), Algorithm 1, SelectArm, p.6

import Mathlib
import Definitions.Def_DecDynMatch_pref
import Definitions.Def_DecDynMatch_LState

namespace DecDynMatch

variable {K : ℕ} {ι : Type*} [Fintype ι]

/-- **SelectArm.** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable Matching*,
arXiv:2610.41912 (held version, sha256 6a27277e…), Algorithm 1, SelectArm, p.6: BUS if m = Seek;
σ_s if m = Sweep; y if m = Replay; if m = Work: PARK if 0 ≤ h < 2K, pᵢ(1) if 2K ≤ h ≤ 4K, pᵢ(k)
if 4K < h < J.

**Formalization Note.** `pref I i r` is 0-based, so `pᵢ(1) = pref I i 0` and
`pᵢ(k) = pref I i (k − 1)`. -/
noncomputable def selectArm (I : Instance K ι) (i : ι) (st : LState K) : Fin K :=
  match st.m with
  | .seek => bus I
  | .sweep => sigma I st.s
  | .replay => st.y
  | .work =>
      if st.h < 2 * K then park I
      else if st.h ≤ 4 * K then pref I i 0
      else pref I i (st.k - 1)

end DecDynMatch


