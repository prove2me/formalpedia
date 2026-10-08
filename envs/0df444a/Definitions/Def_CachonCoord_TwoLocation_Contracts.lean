-- Prove2me | Definitions.Def_CachonCoord_TwoLocation_Contracts
-- name    : CachonCoord_TwoLocation_Contracts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:54:19.589394+00:00
-- url     : https://prove2.me/theorems/664fa760-2a32-4f81-9193-45cbfa21fba9
-- title:
--   §6.8.4, pp. 82–84 — linear transfers t_I I_r + t_B^r B_r + t_B^s B_s and the Cachon–Zipkin contracts (39)–(41)
-- statement:
--   In the two-location base-stock model, the supplier offers a linear transfer payment based on the retailer's inventory and backorders and on the supplier's own backorders:
--   $$T(s_r,s_s) = t_I\, I_r(s_r,s_s) + t_B^r\, B_r(s_r,s_s) + t_B^s\, B_s(s_s),$$
--   where $t_I$, $t_B^r$, $t_B^s$ are constants. A positive value is a payment from the supplier to the retailer. Under the transfer the retailer's cost is $\pi_r(s_r,s_s) - T(s_r,s_s)$ and the supplier's is $\pi_s(s_r,s_s) + T(s_r,s_s)$.
--
--   The Cachon–Zipkin contracts, parameterized by $\lambda$, are
--   $$t_I = (1-\lambda)h_r, \qquad t_B^r = \beta_r - \lambda\beta, \qquad t_B^s = \lambda h_s\,\frac{F_s(s_s^o)}{1 - F_s(s_s^o)},$$
--   where $s_s^o$ is the supplier's base stock in a supply-chain optimal policy $\{s_r^o, s_s^o\}$. The page uses $\lambda \in (0,1]$.
--
--   These are the contracts whose coordination properties are the subject of §6.8.4.
--
--   **Formalization Note** The contracted costs are defined from the base costs $\pi_r$, $\pi_s$ and the transfer, never by the closed forms (42)–(43), which are theorems. The value $s_s^o$ is a parameter of $t_B^s$. Its denominator $1 - F_s(s_s^o)$ is positive in the model, because $F_s$ is strictly increasing on $[0,\infty)$ and so never reaches $1$.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.8.4, p. 82 (transfer payment display, sign convention), p. 84, Eqs. (39)–(41)

import Mathlib
import Definitions.Def_CachonCoord_TwoLocation_Model

namespace CachonCoord.TwoLocation
namespace Model

variable (M : Model)

/-- The linear transfer of §6.8.4 (p. 82),
`t_I I_r(s_r, s_s) + t_B^r B_r(s_r, s_s) + t_B^s B_s(s_s)`, for constants `t_I`, `t_B^r`,
`t_B^s`. A positive value is a payment from the supplier to the retailer (p. 82). -/
noncomputable def transfer (tI tBr tBs sr ss : ℝ) : ℝ :=
  tI * M.IR2 sr ss + tBr * M.BR2 sr ss + tBs * M.BS ss

/-- The retailer's cost under the transfer: `π_r(s_r, s_s)` minus the payment received. -/
noncomputable def contractedPiR (tI tBr tBs sr ss : ℝ) : ℝ :=
  M.piR sr ss - M.transfer tI tBr tBs sr ss

/-- The supplier's cost under the transfer: `π_s(s_r, s_s)` plus the payment made. -/
noncomputable def contractedPiS (tI tBr tBs sr ss : ℝ) : ℝ :=
  M.piS sr ss + M.transfer tI tBr tBs sr ss

/-- `t_I = (1 − λ) h_r`, (39), p. 84. -/
def tI (lam : ℝ) : ℝ := (1 - lam) * M.hr

/-- `t_B^r = β_r − λβ`, (40), p. 84. -/
def tBr (lam : ℝ) : ℝ := M.br - lam * M.beta

/-- `t_B^s = λ h_s F_s(s_s°)/(1 − F_s(s_s°))`, (41), p. 84, where `ssOpt` is the supplier's
optimal base stock `s_s°`. (`F_s(s_s°) < 1` always holds in the model since `F_s` is strictly
increasing on `[0, ∞)`, so the denominator is positive.) -/
noncomputable def tBs (lam ssOpt : ℝ) : ℝ := lam * M.hs * (M.FS ssOpt / (1 - M.FS ssOpt))

/-- The retailer's cost under the contracts (39)–(41) with parameter `λ`. -/
noncomputable def czPiR (lam ssOpt sr ss : ℝ) : ℝ :=
  M.contractedPiR (M.tI lam) (M.tBr lam) (M.tBs lam ssOpt) sr ss

/-- The supplier's cost under the contracts (39)–(41) with parameter `λ`. -/
noncomputable def czPiS (lam ssOpt sr ss : ℝ) : ℝ :=
  M.contractedPiS (M.tI lam) (M.tBr lam) (M.tBs lam ssOpt) sr ss

end Model
end CachonCoord.TwoLocation


