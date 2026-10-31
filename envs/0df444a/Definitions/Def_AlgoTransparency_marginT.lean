-- Prove2me | Definitions.Def_AlgoTransparency_marginT
-- name    : AlgoTransparency_marginT
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:50:34.837529+00:00
-- url     : https://prove2.me/theorems/967f8213-6798-4f28-bd5e-a316dd4ce91d
-- title:
--   Firm's margin from hiring a transparent state
-- statement:
--   In the transparent game the firm's margin from hiring state $S\in\{E,F\}$ is
--
--   $$
--   m_S=n^H_S(W^H_S-R)+n^L_S(W^L_S-R),
--   $$
--
--   with productivities from eq. (3): $W^H_S=\alpha+\beta\,\mathbf 1(S=F)$ and $W^L_S=\beta\,\mathbf 1(S=F)$.
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, eqs. (3) and (4), pp.13–14 (PDF 14–15)

import Mathlib
import Definitions.Def_AlgoTransparency_massHT
import Definitions.Def_AlgoTransparency_massLT

namespace AlgoTransparency

/-- **The firm's margin from hiring transparent state `S`**, Wang, Huang, Jasin & Singh,
arXiv:2008.09283v1, eqs. (3) and (4), pp.13–14 (PDF 14–15):

`m_S = n^H_S (W^H_S − R) + n^L_S (W^L_S − R)`,

where by eq. (3) `W^H_S = α + β·1(S = F)` and `W^L_S = β·1(S = F)`.

**Formalization Note.** Mass form, without the ratio `γ^E_S`, as for `marginO`. -/
def marginT (p : Params) (qH qL : ℝ) (S : TState) : ℝ :=
  let edu : ℝ := match S with
    | .E => 0
    | .F => p.β
  massHT p qH S * (p.α + edu - p.R) + massLT p qL S * (edu - p.R)

end AlgoTransparency


