-- Prove2me | Definitions.Def_HaircutRate_Downside_Setting
-- name    : HaircutRate_Downside_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-23T03:56:41.430962+00:00
-- url     : https://prove2.me/theorems/18ac4b34-0290-4671-bf11-996b96b0e976
-- title:
--   §2–§3, pp. 7–22 — economy, density, bond pricing curve (23), face value (29), q, p, R, H (27)–(31), Assumptions 2–3, downside FOSD direction
-- statement:
--   The closed-form model of Hao's collateralized-bond economy, as characterized by Theorem 1.
--
--   **Economy (§2, p. 7).** There are two dates. Date-1 states are $\omega\in\Omega=[\underline\omega,\bar\omega]\subset(0,\infty)$. A mass $K>0$ of a risky asset pays $\omega$ in state $\omega$. Depositors are endowed with $e^d_0$ at date 0 and $e^d_1$ at date 1, $0\le e^d_1<e^d_0$, and have a strictly increasing, strictly concave utility $u$. The payoff has density $f$ on $\Omega$ with distribution function $F(x)=\int_{\underline\omega}^{x}f(\omega)\,d\omega$, and $\mathbb E[\varphi(\omega)]=\int_{\underline\omega}^{\bar\omega}\varphi(\omega)f(\omega)\,d\omega$.
--
--   **Prices.** Write $D=(e^d_0-e^d_1)/K$. The bond pricing curve (23) is
--   $$q^{bp}(x)=\mathbb E\Big[\frac{u'(e^d_1+K\min(\omega,x))}{u'(e^d_1+Kx)}\,\min(\omega,x)\Big],$$
--   and the equity component at face value $x$ is $\mathbb E[\max(\omega-x,0)]$. The equilibrium face value $\omega^*$ is the root in $\Omega$ of (29), $\omega^*+q^{bp}(\omega^*)=D$. Then the bond price is $q=q^{bp}(\omega^*)$ (27), the asset price $p=q+\mathbb E[\max(\omega-\omega^*,0)]$ (28), the quoted interest rate $R=\omega^*/q-1$ (30), and the haircut $H=E/p$ (31).
--
--   **Assumptions.** Assumption 2 is (20) $2\underline\omega<D$ and (21) $\bar\omega+\mathbb E\big[\tfrac{u'(e^d_1+K\omega)}{u'(e^d_1+K\bar\omega)}\omega\big]>D$. Assumption 3 is (32): $-u''(e^d_1+c)c/u'(e^d_1+c)<1$ for $c\in[K\underline\omega,K\bar\omega]$.
--
--   **Auxiliary quantities.** The right-hand side of (B.1), $q^{bp}_x(x)=\int_{\underline\omega}^{x}\frac{-u'(e^d_1+K\omega)u''(e^d_1+Kx)}{(u'(e^d_1+Kx))^2}K\omega\,dF(\omega)+1-F(x)$; the right-hand side of footnote 26, $q_\tau(x)=\int_{\underline\omega}^{x}\frac{u'(e^d_1+K\omega)}{u'(e^d_1+Kx)}\omega\psi(\omega)\,d\omega$; and the margin of (33), $m(x)=\int_{x}^{\bar\omega}\omega\,dF(\omega)-(1-F(x))D$.
--
--   **Downside shock (p. 22, footnote 23).** A direction $\psi$ is a downside FOSD improvement at $x$ if it is integrable, vanishes outside $(\underline\omega,x)$, satisfies $\int_{\underline\omega}^{x}\psi=0$, and $\int_{\underline\omega}^{x}v\psi>0$ for every $v$ strictly increasing on $[\underline\omega,x]$. The shocked density is $f+\tau\psi$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Definition 1's Arrow–Debreu equilibrium is not encoded: the quantities are those of Theorem 1's closed form. "Strictly increasing and strictly concave" is read as $u\in C^2(0,\infty)$ with $u'>0$, $u''<0$ there, and $u'$, $u''$ are `deriv u` and `deriv (deriv u)`; $e^d_1\ge0$ is a disclosed reading that keeps every argument $e^d_1+K\omega$ positive. Expectations are interval integrals over $[\underline\omega,\bar\omega]$. The face value is chosen by `Classical.choice` among roots of (29) in $\Omega$, with junk value $\underline\omega$ when there is none; every theorem evaluating it assumes Assumption 2, under which the root exists and is unique.
-- source:
--   Hao, The joint determination of haircuts and interest rates for collateralized loans in shadow banking, author's version of 19 Feb 2025 (sha256 924ec4ed…), §2 (pp. 7–19: model p. 7, Assumption 2 (20)–(21) p. 13, (23) p. 15, Theorem 1 (27)–(29) pp. 16–17, (30)–(31) and Assumption 3 (32) p. 18), §3 (footnote 23 p. 19; p. 22 and footnote 26), (B.1) p. 35, (B.7) p. 37

import Mathlib

namespace HaircutRate.Downside
open MeasureTheory Set

/-- §2, p. 7: states `Ω = [lo, hi]` (the paper's `[ω̲, ω̄]`), mass `K` of the risky asset, which pays
`ω` in state `ω`; depositors' endowments `e0 = e^d_0` (date 0) and `e1 = e^d_1` (date 1); depositors'
utility `u`. -/
structure Economy where
  lo : ℝ
  hi : ℝ
  K : ℝ
  e0 : ℝ
  e1 : ℝ
  u : ℝ → ℝ

namespace Economy

/-- Standing assumptions of §2 (p. 7): `0 < ω̲ < ω̄`, `K > 0`, `0 ≤ e^d_1 < e^d_0`, and `u` strictly
increasing and strictly concave, read as: `u` is `C²` on `(0, ∞)` with `u′ > 0` and `u″ < 0` there
(the proofs use `u″(·) < 0`). -/
structure Valid (E : Economy) : Prop where
  lo_pos : 0 < E.lo
  lo_lt_hi : E.lo < E.hi
  K_pos : 0 < E.K
  e1_nonneg : 0 ≤ E.e1
  e1_lt_e0 : E.e1 < E.e0
  u_smooth : ContDiffOn ℝ 2 E.u (Ioi 0)
  u'_pos : ∀ c, 0 < c → 0 < deriv E.u c
  u''_neg : ∀ c, 0 < c → deriv (deriv E.u) c < 0

/-- `(e^d_0 − e^d_1)/K`, the right-hand side of (29). -/
noncomputable def D (E : Economy) : ℝ := (E.e0 - E.e1) / E.K

/-- `f` is a probability density on `Ω = [ω̲, ω̄]`. -/
structure IsDensity (E : Economy) (f : ℝ → ℝ) : Prop where
  nonneg : ∀ ω ∈ Icc E.lo E.hi, 0 ≤ f ω
  integrable : IntervalIntegrable f volume E.lo E.hi
  total : ∫ ω in E.lo..E.hi, f ω = 1

/-- `E[φ(ω)] = ∫_{ω̲}^{ω̄} φ(ω) f(ω) dω`. -/
noncomputable def expect (E : Economy) (f φ : ℝ → ℝ) : ℝ := ∫ ω in E.lo..E.hi, φ ω * f ω

/-- The distribution function `F(x) = ∫_{ω̲}^{x} f(ω) dω`. -/
noncomputable def cdf (E : Economy) (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ ω in E.lo..x, f ω

/-- The bond pricing curve (23):
`q^{bp}(x) = E[u′(e^d_1 + K min(ω, x)) / u′(e^d_1 + K x) · min(ω, x)]`. -/
noncomputable def qbp (E : Economy) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  E.expect f fun ω => deriv E.u (E.e1 + E.K * min ω x) / deriv E.u (E.e1 + E.K * x) * min ω x

/-- The equity component `E[max(ω − x, 0)]` of the asset price (28), at face value `x`. -/
noncomputable def equity (E : Economy) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  E.expect f fun ω => max (ω - x) 0

/-- The right-hand side of (B.1): `∫_{ω̲}^{x} −u′(e^d_1 + Kω) u″(e^d_1 + Kx) / (u′(e^d_1 + Kx))² · Kω dF(ω)
+ 1 − F(x)`. -/
noncomputable def dqbp (E : Economy) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ ω in E.lo..x, -(deriv E.u (E.e1 + E.K * ω) * deriv (deriv E.u) (E.e1 + E.K * x)) /
      deriv E.u (E.e1 + E.K * x) ^ 2 * (E.K * ω) * f ω) + (1 - E.cdf f x)

/-- The right-hand side of footnote 26 at face value `x`:
`∫_{ω̲}^{x} u′(e^d_1 + Kω) / u′(e^d_1 + Kx) · ω ψ(ω) dω`. -/
noncomputable def dqTau (E : Economy) (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ ω in E.lo..x, deriv E.u (E.e1 + E.K * ω) / deriv E.u (E.e1 + E.K * x) * ω * ψ ω

/-- The margin of condition (33) at face value `x`, multiplied out:
`∫_{x}^{ω̄} ω dF(ω) − (1 − F(x)) (e^d_0 − e^d_1)/K`. -/
noncomputable def margin (E : Economy) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ ω in x..E.hi, ω * f ω) - (1 - E.cdf f x) * E.D

/-- Assumption 2, (20) and (21) as printed:
`2ω̲ < (e^d_0 − e^d_1)/K` and `ω̄ + E[u′(e^d_1 + Kω)/u′(e^d_1 + Kω̄) · ω] > (e^d_0 − e^d_1)/K`. -/
def Assumption2 (E : Economy) (f : ℝ → ℝ) : Prop :=
  2 * E.lo < E.D ∧
    E.D < E.hi + E.expect f (fun ω => deriv E.u (E.e1 + E.K * ω) / deriv E.u (E.e1 + E.K * E.hi) * ω)

/-- Assumption 3, (32): `−u″(e^d_1 + c) c / u′(e^d_1 + c) < 1` for `c ∈ [Kω̲, Kω̄]`. -/
def Assumption3 (E : Economy) : Prop :=
  ∀ c ∈ Icc (E.K * E.lo) (E.K * E.hi), -deriv (deriv E.u) (E.e1 + c) * c / deriv E.u (E.e1 + c) < 1

/-- (29): `x ∈ Ω` is an equilibrium face value, `x + q^{bp}(x) = (e^d_0 − e^d_1)/K`. -/
def IsFaceValue (E : Economy) (f : ℝ → ℝ) (x : ℝ) : Prop :=
  x ∈ Icc E.lo E.hi ∧ x + E.qbp f x = E.D

open Classical in
/-- The equilibrium face value `ω*`: the root of (29) in `Ω` (unique under Assumption 2, Theorem 1);
`ω̲` if there is none (a junk value no theorem of the mission evaluates). -/
noncomputable def faceValue (E : Economy) (f : ℝ → ℝ) : ℝ :=
  if h : ∃ x, E.IsFaceValue f x then h.choose else E.lo

/-- The bond price (27): `q = q^{bp}(ω*)`. -/
noncomputable def bondPrice (E : Economy) (f : ℝ → ℝ) : ℝ := E.qbp f (E.faceValue f)

/-- The risky asset price (28): `p = q + E[max(ω − ω*, 0)]`. -/
noncomputable def assetPrice (E : Economy) (f : ℝ → ℝ) : ℝ :=
  E.bondPrice f + E.equity f (E.faceValue f)

/-- The quoted interest rate (30): `R = ω*/q − 1`. -/
noncomputable def rate (E : Economy) (f : ℝ → ℝ) : ℝ := E.faceValue f / E.bondPrice f - 1

/-- The haircut (31): `H = E/p`. -/
noncomputable def haircut (E : Economy) (f : ℝ → ℝ) : ℝ :=
  E.equity f (E.faceValue f) / E.assetPrice f

/-- p. 22 and footnote 23: `ψ` is an FOSD-improving direction on the downside `(ω̲, x)`:
integrable, zero outside `(ω̲, x)`, `∫_{ω̲}^{x} ψ = 0`, and `∫_{ω̲}^{x} v ψ > 0` for every `v`
strictly increasing on `[ω̲, x]`. -/
structure IsDownsideImprovement (E : Economy) (x : ℝ) (ψ : ℝ → ℝ) : Prop where
  integrable : IntervalIntegrable ψ volume E.lo E.hi
  support : ∀ ω, ω ∉ Ioo E.lo x → ψ ω = 0
  mass : ∫ ω in E.lo..x, ψ ω = 0
  fosd : ∀ v : ℝ → ℝ, StrictMonoOn v (Icc E.lo x) → 0 < ∫ ω in E.lo..x, v ω * ψ ω

end Economy

/-- The shocked density `f + τψ` (p. 22). -/
def shock (f ψ : ℝ → ℝ) (τ : ℝ) : ℝ → ℝ := fun ω => f ω + τ * ψ ω

end HaircutRate.Downside


