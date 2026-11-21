-- Prove2me | Definitions.Def_FractionalCalc_scottBlair
-- name    : FractionalCalc_scottBlair
-- status  : Definition
-- author  : @LG
-- created : 2026-11-20T16:39:20.66664+00:00
-- url     : https://prove2.me/theorems/fc219be7-71de-4a8c-9395-18728cfbda87
-- title:
--   Scott-Blair model: Heaviside step, relaxation modulus and creep compliance
-- statement:
--   The **Scott-Blair** fractional viscoelastic element obeys the constitutive law $\sigma(t)=E\,\tau^\alpha D^\alpha\epsilon(t)$ with $\tau=\eta/E$ (Eq. 43), interpolating Hooke's solid ($\alpha=0$) and Newton's fluid ($\alpha=1$). Under a **Heaviside step** excitation $H(t)$ (Eq. 30), the **relaxation modulus** $G_{SB}(t)$ is the stress response to a unit step strain $\epsilon=H$, namely $E\tau^\alpha D_{0+}^\alpha H(t)$; the **creep compliance** $J_{SB}(t)$ is the strain response to a unit step stress $\sigma=H$, namely $(E\tau^\alpha)^{-1}I_{0+}^\alpha H(t)$. These are the responses computed in Eqs. (44)–(45).
--
--   **Formalization Note** $H(t)=1$ for $t>0$ and $0$ otherwise. The responses are defined via the left Riemann–Liouville operators at base $0$ applied to $H$; theorems assume $E,\tau>0$ and the order ranges stated in the paper.
-- source:
--   F. G. Rodrigues & E. C. de Oliveira, Rev. Bras. Ens. Fís. 37(3), 3305 (2015), https://doi.org/10.1590/S1806-11173731842, §5.1, Eq. (30) (Heaviside), Eq. (43) (constitutive law), Eqs. (44)–(45) (responses).

import Mathlib
import Definitions.Def_FractionalCalc_rlIntegral
import Definitions.Def_FractionalCalc_rlDeriv
open Classical
namespace FractionalCalc
/-- Heaviside step `H(t)=1` for `t>0`, else `0`. -/
noncomputable def heaviside (t : ℝ) : ℝ := if 0 < t then 1 else 0
/-- Scott-Blair relaxation modulus: stress response to unit step strain. -/
noncomputable def scottBlairRelaxation (E τ α : ℝ) (t : ℝ) : ℝ := E * τ ^ α * rlDeriv 0 α heaviside t
/-- Scott-Blair creep compliance: strain response to unit step stress. -/
noncomputable def scottBlairCreep (E τ α : ℝ) (t : ℝ) : ℝ := (E * τ ^ α)⁻¹ * rlIntegral 0 α heaviside t
end FractionalCalc


