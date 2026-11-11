-- Prove2me | Definitions.Def_DecDynMatch_Psi
-- name    : DecDynMatch_Psi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:56:19.556881+00:00
-- url     : https://prove2.me/theorems/5cd971e7-13a0-4f72-a164-60acf77dce0f
-- title:
--   Recovery map $\Psi_F(x)=x+F(x+H)+3H$
-- statement:
--   For a replay rule $F$, the **recovery map** is
--   $$
--   \Psi_F(x)=x+F(x+H)+3H .
--   $$
--   Its threefold iterate $\Psi_F^{\circ 3}(t^*+1)$ bounds the round by which SC-DA has recovered and calibrated after the last population event $t^*$. For $F(x)=H+2x$, $\Psi_F(x)=3x+6H$ and $\Psi_F^{\circ3}(x)=27x+78H$.
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), eq. (19), p.17

import Mathlib
import Definitions.Def_DecDynMatch_J

namespace DecDynMatch

/-- **Recovery map.** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable Matching*,
arXiv:2610.41912 (held version, sha256 6a27277e…), eq. (19), p.17: "Ψ_F(x) = x + F(x + H) + 3H".
`(Psi K F)^[3]` is the paper's `Ψ_F^{∘3}`. -/
def Psi (K : ℕ) (F : ℕ → ℕ) (x : ℕ) : ℕ := x + F (x + H K) + 3 * H K

end DecDynMatch


