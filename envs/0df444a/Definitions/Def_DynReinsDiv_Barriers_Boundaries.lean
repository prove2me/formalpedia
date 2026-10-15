-- Prove2me | Definitions.Def_DynReinsDiv_Barriers_Boundaries
-- name    : DynReinsDiv_Barriers_Boundaries
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:34:30.266461+00:00
-- url     : https://prove2.me/theorems/3cc9d97c-a95d-4c7f-a0b8-385ba7ad5004
-- title:
--   The no-dividend region 𝒩𝒟, the dividend boundary d(τ), the optimal ceded loss Î (4.6) and the reinsurance boundaries K(z, τ), K_j(τ) (pp. 11–19)
-- statement:
--   These are the regions and free boundaries of Section 4 of the paper, defined from the partial derivatives $v_x, v_{xx}$ of the solution $v$ of the HJB variational inequality. Points are written $(x,\tau)$, with $x$ the surplus and $\tau=T-t\in(0,T]$ the time to maturity.
--
--   1. The **no-dividend-payout region** is $\mathcal{ND}=\{(x,\tau): x>0,\ 0<\tau\le T,\ v_x(x,\tau)>1\}$; its part with $\tau<T$ is also used.
--   2. The **dividend-payout boundary** is
--   $$d(\tau)=\inf\{x\ge 0: v_x(x,\tau)=1\}.$$
--   3. The **optimal retained loss** (4.6) for a claim of size $z$ is
--   $$\hat H(z,x,\tau)=\begin{cases}-\dfrac{v_x}{v_{xx}}(x,\tau), & -\dfrac{v_{xx}}{v_x}(x,\tau)>\dfrac1z,\\[4pt] z, & \text{otherwise,}\end{cases}$$
--   and the **optimal ceded loss** is $\hat I(z,x,\tau)=z-\hat H(z,x,\tau)$.
--   4. The **reinsurance boundary** for claim size $z$ is
--   $$K(z,\tau)=\sup\Bigl\{x>0: -\frac{v_{xx}}{v_x}(x,\tau)>\frac1z\Bigr\},$$
--   with the paper's convention $K(z,\tau)=0$ when the set is empty.
--   5. For an atom $z_j$ of a discrete claim law, the **$j$-th reinsurance boundary** is
--   $$K_j(\tau)=\inf\Bigl\{x>0: -\frac{v_{xx}}{v_x}(x,\tau)\le\frac1{z_j}\Bigr\}.$$
--
--   These objects describe the optimal strategy: dividends are paid above $d(\tau)$, and a claim of size $z$ is partly ceded to the reinsurer below $K(z,\tau)$.
--
--   **Formalization Note** The functions take the derivative witnesses `vx vxx` as arguments. Conditions are written as $-v_{xx}/v_x$ compared with $1/z$, which never divides by $v_{xx}$ (in the model $v_x\ge1$); the quotient $-v_x/v_{xx}$ appears only in the branch where $-v_{xx}/v_x>1/z>0$, so $v_{xx}<0$ there. `sInf`/`sSup` of a real set return $0$ on the empty set; the theorems either conclude nonemptiness ($d$) or use the convention as the paper does ($K(z,\tau)$). The paper writes the regions in the coordinates $(x,t)$ with $t\in[0,T)$; they are the same sets of points.
-- source:
--   Guan, Xu & Zhou, Dynamic optimal reinsurance and dividend-payout in a finite time horizon, arXiv:2008.00391v3, p. 11 (𝒟, 𝒩𝒟, d(τ)), p. 14 ((4.6), Î), p. 16 (K(z, τ)), p. 19 (K_j(τ))

import Mathlib
import Definitions.Def_DynReinsDiv_Barriers_Model

namespace DynReinsDiv.Barriers

/-! Regions and free boundaries of Section 4 of Guan, Xu & Zhou (arXiv:2008.00391v3, pp. 11–19).
All points are written `(x, τ)` with `τ = T − t ∈ (0, T]` the second argument of the solution `v` of
(3.1); the paper's sets are written in `(x, t) ∈ 𝒬^T = (0, ∞) × [0, T)`, which is the same set of
points. -/

/-- The no-dividend-payout region `𝒩𝒟 = {(x, t) ∈ 𝒬^T | v_x(x, τ) > 1}` (p. 11), in `(x, τ)`
coordinates: `x > 0`, `0 < τ ≤ T`, `v_x(x, τ) > 1`. -/
def NDset (T : ℝ) (vx : ℝ → ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ 0 < p.2 ∧ p.2 ≤ T ∧ 1 < vx p.1 p.2}

/-- The dividend-payout boundary `d(τ) = inf{x ≥ 0 | v_x(x, τ) = 1}` (p. 11). -/
noncomputable def dBoundary (vx : ℝ → ℝ → ℝ) (τ : ℝ) : ℝ :=
  sInf {x : ℝ | 0 ≤ x ∧ vx x τ = 1}

/-- The optimal retained loss (4.6): `Ĥ(z, x, τ) = −v_x/v_xx(x, τ)` if `−v_xx/v_x(x, τ) > 1/z`,
and `z` otherwise. -/
noncomputable def Hhat (vx vxx : ℝ → ℝ → ℝ) (z x τ : ℝ) : ℝ :=
  if -vxx x τ / vx x τ > 1 / z then -vx x τ / vxx x τ else z

/-- The optimal ceded loss `Î(z, x, τ) = z − Ĥ(z, x, τ)` (p. 14). -/
noncomputable def Ihat (vx vxx : ℝ → ℝ → ℝ) (z x τ : ℝ) : ℝ :=
  z - Hhat vx vxx z x τ

/-- The reinsurance boundary for claim size `z` (p. 16):
`K(z, τ) = sup{x > 0 | −v_xx/v_x(x, τ) > 1/z}` (the supremum of the empty set is `0`, as in the
paper's "K(z, τ) = 0" when the set is empty). -/
noncomputable def Kz (vx vxx : ℝ → ℝ → ℝ) (z τ : ℝ) : ℝ :=
  sSup {x : ℝ | 0 < x ∧ -vxx x τ / vx x τ > 1 / z}

/-- The reinsurance boundary of an atom `ζ` of the claim law (p. 19):
`K_j(τ) = inf{x > 0 | −v_xx/v_x(x, τ) ≤ 1/z_j}` with `ζ = z_j`. -/
noncomputable def Kinf (vx vxx : ℝ → ℝ → ℝ) (ζ τ : ℝ) : ℝ :=
  sInf {x : ℝ | 0 < x ∧ -vxx x τ / vx x τ ≤ 1 / ζ}

end DynReinsDiv.Barriers


