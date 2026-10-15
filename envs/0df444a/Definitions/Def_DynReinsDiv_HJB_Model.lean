-- Prove2me | Definitions.Def_DynReinsDiv_HJB_Model
-- name    : DynReinsDiv_HJB_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:33:57.931785+00:00
-- url     : https://prove2.me/theorems/b1faab8c-1f5c-4196-91a7-67863d64884a
-- title:
--   Claim law, loadings, the operator 𝓛 of (3.2), the functions A, B, f of (A.5), (A.6), (A.12) and the operator 𝒯 of (A.11)
-- statement:
--   This file fixes the data of the finite-horizon optimal reinsurance and dividend-payout problem of Guan, Xu and Zhou and the functions built from it.
--
--   **Model.** A model consists of
--   1. a probability measure $\mu$ on $\mathbb R$, the common law of the claims, with $\mu((-\infty,0))=0$ (claims are nonnegative, $F(0-)=0$); its distribution function is $F(z)=\mu((-\infty,z])$, which may be discontinuous;
--   2. the net reinsurance loading $\gamma>0$, the discount factor $c>0$ and the horizon $T>0$;
--   3. the tail assumption (3.3): $z^3(1-F(z))$ is bounded on $[0,\infty)$;
--   4. the assumption $\gamma<\mu_1$, where $\mu_1=\int_0^\infty z\,dF(z)$ and $\mu_2=\int_0^\infty z^2\,dF(z)$ are the first two moments (A.1).
--
--   **The functions $A$, $B$, $f$** (A.5), (A.6), (A.12):
--   $$A(y)=\begin{cases}\int_0^{1/y} z(1-F(z))\,dz,& y>0,\\ \tfrac12\mu_2,& y\le 0,\end{cases}\qquad B(y)=\begin{cases}\int_0^{1/y}(1-F(z))\,dz,& y>0,\\ \mu_1,& y\le 0,\end{cases}$$
--   $$f(y)=-yA(y)+B(y)-\gamma .$$
--   Lemma A.1's functions are $F(y,z)=A(-y/z)$ and $G(y,z)=B(-y/z)$.
--
--   **The operator $\mathcal L$** (3.2). With $\mathcal H$ the set of measurable retained-loss functions $H$ with $0\le H(z)\le z$ for $z\ge0$, and for real numbers $q$ (standing for $v_{xx}$), $p$ (for $v_x$) and $w$ (for $v$),
--   $$\mathcal L(q,p,w)=\sup_{H\in\mathcal H}\Big(\frac q2\int_0^\infty H(z)^2\,dF(z)+p\int_0^\infty H(z)\,dF(z)\Big)-\gamma p-cw .$$
--
--   **The operator $\mathcal T$** (A.11), for numbers $u_{xx}, u_x, u$:
--   $$\mathcal T(u_{xx},u_x,u)=A\Big(-\frac{u_x}{u}\Big)u_{xx}+B\Big(-\frac{u_x}{u}\Big)u_x-\gamma u_x-cu .$$
--
--   These objects are shared by every statement of the mission: the variational inequality (3.1) is written with $\mathcal L$, the penalized gradient problem (A.17) with $\mathcal T$, and $\lambda$ is the positive root of $f$.
--
--   **Formalization Note** The claim law is a `Measure ℝ` with `IsProbabilityMeasure` and `μ (Set.Iio 0) = 0`, and $F(z)$ is `(μ (Set.Iic z)).toReal`. The moments are Bochner integrals; (3.3) implies they are finite (p. 21), so this is not assumed separately. The paper's $f$ is named `fA` and Lemma A.1's $F$, $G$ are `FA`, `GB`. The paper assumes $0<\gamma<\mu_1$ only from Section 4 on; it is a standing assumption here because Theorem 3.1's (3.9) needs the root $\lambda$ of $f$, which exists only when $\mu_1>\gamma$. $\mathcal L$ is the supremum (3.2) itself, not its closed form (A.10), which is a milestone. $\mathcal T$ divides by $u$; every statement using it has $u\ne0$.
-- source:
--   Guan, Xu & Zhou, Dynamic optimal reinsurance and dividend-payout in a finite time horizon, arXiv:2008.00391v3, pp. 7–9 (γ, c, T, (3.1)–(3.3)), p. 10 (0 < γ < μ₁), pp. 21–23 ((A.1), (A.5), (A.6), (A.11), (A.12)), p. 25 (Lemma A.1's F, G)

import Mathlib

open MeasureTheory

namespace DynReinsDiv.HJB

/-- The cumulative distribution function `F(z) = μ((-∞, z])` of a claim law `μ` on `ℝ`. -/
noncomputable def claimCDF (μ : Measure ℝ) (z : ℝ) : ℝ := (μ (Set.Iic z)).toReal

/-- First moment `μ₁ = ∫ z dF(z)` of a claim law (A.1). -/
noncomputable def claimMean (μ : Measure ℝ) : ℝ := ∫ z, z ∂μ

/-- Second moment `μ₂ = ∫ z² dF(z)` of a claim law (A.1). -/
noncomputable def claimSecondMoment (μ : Measure ℝ) : ℝ := ∫ z, z ^ 2 ∂μ

/-- The data of the optimal reinsurance and dividend-payout problem (Sections 2–3):
the claim law `μ` (nonnegative claims, CDF `F`), the net reinsurance loading `γ`,
the discount factor `c` and the horizon `T`, with the tail assumption (3.3) and the
standing assumption `0 < γ < μ₁` (p. 10). -/
structure Model where
  /-- the common law of the claims `Z_i` -/
  μ : Measure ℝ
  /-- `γ = (ρ - δ) E[Z₁]` with `ρ = 1` -/
  γ : ℝ
  /-- the discount factor -/
  c : ℝ
  /-- the horizon -/
  T : ℝ
  isProb : IsProbabilityMeasure μ
  /-- the claims are nonnegative: `F(0-) = 0` -/
  claims_nonneg : μ (Set.Iio 0) = 0
  /-- (3.3): `z³ (1 - F(z))` is bounded on `[0, ∞)` -/
  tail_bound : ∃ C : ℝ, ∀ z : ℝ, 0 ≤ z → z ^ 3 * (1 - claimCDF μ z) ≤ C
  γ_pos : 0 < γ
  c_pos : 0 < c
  T_pos : 0 < T
  /-- `γ < μ₁` (p. 10) -/
  γ_lt_mean : γ < claimMean μ

namespace Model

variable (M : Model)

/-- The claim CDF `F`. -/
noncomputable def F (z : ℝ) : ℝ := claimCDF M.μ z

/-- `μ₁`. -/
noncomputable def μ₁ : ℝ := claimMean M.μ

/-- `μ₂`. -/
noncomputable def μ₂ : ℝ := claimSecondMoment M.μ

/-- (A.5): `A(y) = ∫₀^{1/y} z (1 - F z) dz` for `y > 0`, `A(y) = μ₂ / 2` for `y ≤ 0`. -/
noncomputable def A (y : ℝ) : ℝ :=
  if 0 < y then ∫ z in (0 : ℝ)..(1 / y), z * (1 - M.F z) else M.μ₂ / 2

/-- (A.6): `B(y) = ∫₀^{1/y} (1 - F z) dz` for `y > 0`, `B(y) = μ₁` for `y ≤ 0`. -/
noncomputable def B (y : ℝ) : ℝ :=
  if 0 < y then ∫ z in (0 : ℝ)..(1 / y), (1 - M.F z) else M.μ₁

/-- (A.12): the paper's `f(y) = -y A(y) + B(y) - γ` (named `fA` to avoid a clash with `f_ε`). -/
noncomputable def fA (y : ℝ) : ℝ := -y * M.A y + M.B y - M.γ

/-- The set `𝓗` of admissible retained-loss functions: measurable `H` with
`0 ≤ H z ≤ z` for `z ≥ 0` (values on `z < 0` are irrelevant, `μ`-null). -/
def Hset : Set (ℝ → ℝ) :=
  {H | Measurable H ∧ ∀ z : ℝ, 0 ≤ z → 0 ≤ H z ∧ H z ≤ z}

/-- The supremum in (3.2), as a function of the numbers `q = v_xx` and `p = v_x`:
`sup_{H ∈ 𝓗} ( q/2 ∫ H² dF + p ∫ H dF )`. -/
noncomputable def supTerm (q p : ℝ) : ℝ :=
  sSup ((fun H : ℝ → ℝ => q / 2 * ∫ z, (H z) ^ 2 ∂M.μ + p * ∫ z, H z ∂M.μ) '' Hset)

/-- The operator `𝓛` of (3.2), evaluated at `v_xx = q`, `v_x = p`, `v = w`. -/
noncomputable def Lop (q p w : ℝ) : ℝ := M.supTerm q p - M.γ * p - M.c * w

/-- The operator `𝒯` of (A.11), evaluated at `u_xx = uxx`, `u_x = ux`, `u = u`:
`A(-u_x/u) u_xx + B(-u_x/u) u_x - γ u_x - c u`. -/
noncomputable def Top (uxx ux u : ℝ) : ℝ :=
  M.A (-ux / u) * uxx + M.B (-ux / u) * ux - M.γ * ux - M.c * u

/-- `F(y, z) := A(-y/z)` of Lemma A.1 (named `FA`; the paper's `F` is also the claim CDF). -/
noncomputable def FA (y z : ℝ) : ℝ := M.A (-y / z)

/-- `G(y, z) := B(-y/z)` of Lemma A.1. -/
noncomputable def GB (y z : ℝ) : ℝ := M.B (-y / z)

end Model

end DynReinsDiv.HJB


