-- Prove2me | Definitions.Def_OrderSelProphet_Kernel_Coordinates
-- name    : OrderSelProphet_Kernel_Coordinates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:57:21.085584+00:00
-- url     : https://prove2.me/theorems/dbfaf587-1834-4551-8a38-76353b6689c8
-- title:
--   $\varphi$, $q=\varphi^{-1}$, $\kappa$, the linearized area $a_\lambda$, the kernel $K_0$ (44), exponential coordinates $u_a$, $t_r$ and the inverse $r(t)$, $c_\Gamma$, $D_\Gamma$, $h(r)$, $C(r)$
-- statement:
--   - $\varphi(x)=x+(1-x)\log(1-x)$ on $[0,1]$, $\varphi(1)=1$ (24); $q(t)=\inf\{x\in[0,1]:\varphi(x)\ge t\}$, the inverse of the increasing bijection $\varphi$.
--   - $\kappa(x,u)=(x-u)_+/(1-u)$; the **linearized area** $a_\lambda(x)=\int_0^1\lambda(u)\kappa(x,u)du$ (§5.1).
--   - **Baseline kernel** (44): $K_0(t,u)=(q(t)-u)_+/(1-u)$ for $u<1$, $K_0(t,1)=t$.
--   - **Exponential coordinates** (49): $u_a=1-e^{-a}$, $t_r=1-(1+r)e^{-r}$; $r(t)=\inf\{r\ge0:t_r\ge t\}$ is the inverse of $r\mapsto t_r$ on $[0,1)$.
--   - $c_\Gamma=(1-\Gamma)/\Gamma$, $D_\Gamma(r)=c_\Gamma e^r+1+r$ (46).
--   - $h(r)=h_\lambda(u_r)$ and $C(r)=C_\lambda(u_r)$ (51); by substitution $h(r)=\int_0^r\lambda(u_s)ds$.
-- source:
--   Peng and Tang, Order-selection Prophet Inequality (Almost) Goes I.I.D., arXiv:2610.34892 (held file SHA-256 2f111b85…22dd), eq. (24) p. 14; §5.1 pp. 18–19, eq. (39); eq. (44) p. 21; eqs. (46), (49)–(51) pp. 23–24

import Mathlib
import Definitions.Def_OrderSelProphet_Kernel_Profiles

set_option autoImplicit false

open MeasureTheory Set

namespace OrderSelProphet.Kernel

/-! # The i.i.d. path, the kernel K0 and exponential coordinates

Peng and Tang (2026), arXiv:2610.34892, eq. (24) p. 14, (39) p. 19, (44) p. 21, (46) p. 23,
(49)–(51) p. 24. -/

/-- `φ(x) = x + (1-x) log(1-x)` (eq. (24), p. 14). At `x = 1` this is `1` (Lean's `log 0 = 0`),
which is the paper's convention `φ(1) = 1`. -/
noncomputable def phi (x : ℝ) : ℝ :=
  x + (1 - x) * Real.log (1 - x)

/-- `q = φ⁻¹` on `[0,1]` (eq. (24), p. 14): `q(t) = inf {x ∈ [0,1] : φ(x) ≥ t}`, which is the
inverse of the continuous strictly increasing bijection `φ` of `[0,1]` for `t ∈ [0,1]`. -/
noncomputable def qInv (t : ℝ) : ℝ :=
  sInf {x ∈ Icc (0 : ℝ) 1 | t ≤ phi x}

/-- The elementary area curve `κ(x,u) = (x-u)_+ / (1-u)` for `u < 1` (§5.1, p. 18). -/
noncomputable def kappa (x u : ℝ) : ℝ :=
  max (x - u) 0 / (1 - u)

/-- The linearized area of a profile (§5.1, pp. 18–19): `a_λ(x) = ∫_0^1 λ(u) κ(x,u) du`. -/
noncomputable def linArea (lam : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1, lam u * kappa x u

/-- The baseline kernel (eq. (44), p. 21): `K0(t,u) = (q(t) - u)_+ / (1 - u)` for `u ∈ [0,1)`,
and `K0(t,1) = t`. -/
noncomputable def K0 (t u : ℝ) : ℝ :=
  if u < 1 then kappa (qInv t) u else t

/-- The exponential rank coordinate (eq. (49), p. 24): `u_a = 1 - e^{-a}`. -/
noncomputable def uA (a : ℝ) : ℝ :=
  1 - Real.exp (-a)

/-- The exponential time coordinate (eq. (49), p. 24): `t_r = φ(u_r) = 1 - (1+r) e^{-r}`. -/
noncomputable def tR (r : ℝ) : ℝ :=
  1 - (1 + r) * Real.exp (-r)

/-- The inverse of `r ↦ t_r` on `[0,1)`: `r(t) = inf {r ≥ 0 : t_r ≥ t}`. Since `r ↦ t_r` is an
increasing continuous bijection `[0,∞) → [0,1)`, this is the unique `r ≥ 0` with `t_r = t` for
every `t ∈ [0,1)`. -/
noncomputable def rOfT (t : ℝ) : ℝ :=
  sInf {r ∈ Ici (0 : ℝ) | t ≤ tR r}

/-- `c_Γ = (1-Γ)/Γ` (eq. (46), p. 23). -/
noncomputable def cG (Γ : ℝ) : ℝ :=
  (1 - Γ) / Γ

/-- `D_Γ(r) = c_Γ e^r + 1 + r` (eq. (46), p. 23). -/
noncomputable def DG (Γ r : ℝ) : ℝ :=
  cG Γ * Real.exp r + 1 + r

/-- The cumulative hazard in exponential coordinates (eq. (51), p. 24): `h(r) = h_λ(u_r)`,
which equals `∫_0^r λ(u_s) ds` by the substitution `a = u_s`. -/
noncomputable def hExp (lam : ℝ → ℝ) (r : ℝ) : ℝ :=
  hP lam (uA r)

/-- `C(r) = C_λ(u_r)` (eq. (51), p. 24). -/
noncomputable def CExp (lam : ℝ → ℝ) (r : ℝ) : ℝ :=
  CP lam (uA r)

end OrderSelProphet.Kernel


