-- Prove2me | Definitions.Def_DecDynMatch_NF
-- name    : DecDynMatch_NF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:56:17.728195+00:00
-- url     : https://prove2.me/theorems/fa3dbef5-eb3d-4bb7-a256-f23b2bfbaa73
-- title:
--   Iteration count $N_F(T)$
-- statement:
--   For a replay rule $F$ and a horizon $T$, the **iteration count** is
--   $$
--   N_F(T)=\#\{\,m\ge 0 : F^{\circ m}(H)<T\,\}.
--   $$
--   After calibration, consecutive common replay lengths satisfy $L_{j+1}\ge F(L_j)$ with $L_0\ge H$, so $N_F(T)$ bounds the number of maintenance windows that meet the first $T$ rounds.
--
--   **Formalization Note** The count is taken over $m<T$; for a rule with (12), $F^{\circ m}(H)\ge H+m>m$, so nothing is lost.
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), App. A.4, p.20

import Mathlib
import Definitions.Def_DecDynMatch_J

namespace DecDynMatch

/-- **Iteration count.** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable Matching*,
arXiv:2610.41912 (held version, sha256 6a27277e…), App. A.4, p.20: "N_F(T) = #{m ≥ 0 : F^{∘m}(H) < T}".

**Formalization Note.** The count is taken over `m < T`. For a rule with `F x ≥ H + 2x` (eq. (12)),
`F^{∘m}(H) ≥ H + m > m`, so every `m` with `F^{∘m}(H) < T` satisfies `m < T` and the truncation
changes nothing. -/
def NF (K : ℕ) (F : ℕ → ℕ) (T : ℕ) : ℕ :=
  ((Finset.range T).filter (fun m => F^[m] (H K) < T)).card

end DecDynMatch


