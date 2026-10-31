-- Prove2me | Definitions.Def_AlgoTransparency_marginO
-- name    : AlgoTransparency_marginO
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:50:58.06712+00:00
-- url     : https://prove2.me/theorems/79d9d479-c2d7-44ce-af5b-36041e0691f2
-- title:
--   Firm's margin $m_S$ from hiring an opaque state
-- statement:
--   For agents' strategies $q_H,q_L$, the firm's margin from hiring everybody in opaque state $S$ is
--
--   $$
--   m_S=n^H_S\,(W^H_S-R)+n^L_S\,(W^L_S-R),
--   $$
--
--   where, by eq. (2), $W^H_S=\alpha+\beta\,\mathbf 1(S\in\{B,D\})$ and $W^L_S=\beta\,\mathbf 1(S\in\{B,D\})$. The firm's payoff (4) is $\sum_S P_S m_S$.
--
--   **Formalization Note** The paper also writes $m_S=n_S\big(\gamma^E_S(W^H_S-R)+(1-\gamma^E_S)(W^L_S-R)\big)$ with $\gamma^E_S=n^H_S/n_S$. The mass form is used because it has no division: at an unoccupied state $\gamma^E_S$ would be $0/0$.
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, eqs. (2) and (4), pp.13–14 (PDF 14–15)

import Mathlib
import Definitions.Def_AlgoTransparency_massHO
import Definitions.Def_AlgoTransparency_massLO

namespace AlgoTransparency

/-- **The firm's margin from hiring opaque state `S`**, Wang, Huang, Jasin & Singh,
arXiv:2008.09283v1, eqs. (2) and (4), pp.13–14 (PDF 14–15):

`m_S = n^H_S (W^H_S − R) + n^L_S (W^L_S − R)`,

where by eq. (2) the productivity is `W^H_S = α + β·1(S ∈ {B, D})` and
`W^L_S = β·1(S ∈ {B, D})`. The firm's payoff (4) is `Σ_S P_S m_S`.

**Formalization Note.** The paper also writes `m_S = n_S(γ^E_S(W^H_S − R) + (1 − γ^E_S)(W^L_S − R))`
with `γ^E_S = n^H_S / n_S`; the mass form is used because it has no division (at an unoccupied
state `γ^E_S` would be `0/0`). -/
def marginO (p : Params) (qH qL : ℝ) (S : OState) : ℝ :=
  let edu : ℝ := match S with
    | .A => 0
    | .B => p.β
    | .C => 0
    | .D => p.β
  massHO p qH S * (p.α + edu - p.R) + massLO p qL S * (edu - p.R)

end AlgoTransparency


