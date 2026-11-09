-- Prove2me | Definitions.Def_AutobidSPPE_endpointSpend
-- name    : AutobidSPPE_endpointSpend
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:57:31.028116+00:00
-- url     : https://prove2.me/theorems/9c60ccba-89dd-4c7a-8be0-d2e765d65cc7
-- title:
--   Endpoint spending $\mathsf s_i(a,y_{-i})=\mathbb E[Z_i(1-Z_i/a)_+]$
-- statement:
--   Write the values as $v_j=\bar v_j U_j$ with $U_j\sim\mathrm{Unif}[0,1]$ i.i.d., and use **endpoint coordinates** $y_j=\bar v_j\alpha_j$, so bidder $j$ bids $y_jU_j$. Let $Z_i=\max_{j\ne i}y_jU_j$ be the highest rival bid. The **endpoint spending** of bidder $i$ at own endpoint $a=y_i$ is
--   $$
--   \mathsf s_i(a,y_{-i}) = \mathbb E\big[Z_i\,(1-Z_i/a)_+\big]\quad(a>0),\qquad \mathsf s_i(0,y_{-i})=0 .
--   $$
--
--   **Formalization Note** The function takes a full endpoint profile $y$ and reads its own endpoint from $y_i$; $\mathsf s_i(a,y_{-i})$ is the value at $y$ with $y_i$ replaced by $a$. The value for $y_i<0$ (outside the model) is $0$.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (6), p.10; (22), p.14

import Mathlib
import Definitions.Def_AutobidSPPE_valueLaw
import Definitions.Def_AutobidSPPE_highestOther
open MeasureTheory

namespace AutobidSPPE

/-- Endpoint spending (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (6), p.10; (22), p.14): for an endpoint profile `y` (bidder `j`'s
bid is `yⱼUⱼ`, `Uⱼ ∼ Unif[0,1]` i.i.d.), with `Zᵢ = max_{j≠i} yⱼUⱼ`,
`𝗌ᵢ(a, y₋ᵢ) = E[Zᵢ(1 − Zᵢ/a)₊]` for `a = yᵢ > 0`, and `𝗌ᵢ(0, y₋ᵢ) = 0`.

**Formalization Note** The own endpoint is the coordinate `yᵢ`; `𝗌ᵢ(a, y₋ᵢ)` is
`endpointSpend (Function.update y i a) i`. The unit uniforms are `valueLaw (fun _ => 1)`.
The value at `yᵢ < 0` (outside the model) is `0`. -/
noncomputable def endpointSpend {n : ℕ} (y : Fin n → ℝ) (i : Fin n) : ℝ :=
  if 0 < y i then
    ∫ u, highestOther y u i * max (1 - highestOther y u i / y i) 0
      ∂(valueLaw (fun _ : Fin n => (1 : ℝ)))
  else 0

end AutobidSPPE


