-- Prove2me | Definitions.Def_BenchmarkTracking_Verification_Representation
-- name    : BenchmarkTracking_Verification_Representation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:25:03.722607+00:00
-- url     : https://prove2.me/theorems/71a41e96-6a9e-4c62-888a-df4f6d393012
-- title:
--   (3.1)–(3.7), (3.13), (3.36)–(3.37), (4.1) — the reflected processes, the probabilistic representation $v$, its dual $\hat u$ and the primal $u$
-- statement:
--   Fix model parameters, a discount rate $\rho$, and a probability space carrying three independent scalar Brownian motions $B^0,B^1,B^2$. Put $B^3=\varrho_1B^1+\sqrt{1-\varrho_1^2}\,B^0$. For $r,h,z\ge0$ and $t\ge0$:
--
--   1. **Reflected processes** ((3.2), (3.3), (3.5)):
--   $$
--   R^r_t=r+\Big(\frac{\alpha^2}2-\rho\Big)t+\alpha B^1_t+L^r_t,\qquad L^r_t=0\vee\Big\{-r+\max_{s\in[0,t]}\Big[-\alpha B^1_s-\Big(\frac{\alpha^2}2-\rho\Big)s\Big]\Big\},
--   $$
--   $$
--   H^h_t=h-\mu_Bt-\sigma_BB^3_t+K^h_t,\qquad K^h_t=0\vee\Big\{-h+\max_{s\in[0,t]}(\mu_Bs+\sigma_BB^3_s)\Big\}.
--   $$
--   2. **Geometric Brownian motion** (p. 8): $N^z_t=z\exp\big((\mu_Z-\tfrac12\sigma_Z^2)t+\sigma_Z(\varrho_2B^1_t+\sqrt{1-\varrho_2^2}\,B^2_t)\big)$.
--   3. **Independent reflection** (3.14) and p. 13: $G^h_t=h\vee\max_{l\in[0,t]}(\mu_Bl+\sigma_BB^0_l)-h$.
--   4. **The representation** (3.1):
--   $$
--   v(r,h,z)=\frac{1-p}{p}\beta^{-\frac p{1-p}}\mathbb E\Big[\int_0^\infty e^{-\rho s+\frac p{1-p}R^r_s}ds\Big]+\beta(\kappa_2-\mu_Z)\mathbb E\Big[\int_0^\infty e^{-\rho s-R^r_s}N^z_s\,ds\Big]-\beta\,\mathbb E\Big[\int_0^\infty e^{-\rho s-R^r_s}dK^h_s\Big],
--   $$
--   and $l(r,z)$, the sum of its first two terms (3.7).
--   5. **The pieces of the last term**: $\varphi(r,h)=-\beta\,\mathbb E[\int_0^\infty e^{-\rho s-R^r_s}dG^h_s]$ (3.13), $\xi(r,h)=-\kappa_1\mathbb E[\int_0^\infty e^{-\rho s}\varphi_{rh}(R^r_s,H^h_s)ds]$ (3.36) and $\psi=\varphi+\xi$ (3.37).
--   6. **Dual and primal functions**: $\hat u(y,h,z)=v(-\ln(y/\beta),h,z)$ for $y\in(0,\beta]$ (3.6), and
--   $$
--   u(x,h,z)=\inf_{y\in(0,\beta]}\{\hat u(y,h,z)+yx\},\qquad (x,h,z)\in\mathbb R^3_+.\tag{4.1}
--   $$
--
--   These are the objects of Theorem 3.1 and Theorem 4.1: $\hat u$ solves the dual Neumann problem and $u$ is the value function of the control problem.
--
--   **Formalization Note** The Brownian motions are the coordinates $0,1,2$ of a process $B:\mathbb R_{\ge0}\to\Omega\to\mathbb R^3$; the theorems assume it is a standard 3-dimensional Brownian motion, and they hold for every such space, so $u$ does not depend on the choice. Processes are indexed by real time $t\ge0$. The reflected processes are defined by the explicit Skorokhod formulas (3.5) rather than as solutions of reflected SDEs, and $N^z$, $G^h$ in closed form. Each expectation of a nonnegative integrand is a `lintegral` in $[0,\infty]$, converted to a real number; the theorems assert finiteness wherever it is needed. $\xi$ uses Bochner integrals, whose integrability is asserted by Proposition 3.5. The infimum in (4.1) is a real `sInf`; Theorem 4.1(i) asserts that it is attained. The paper prints the last term of $dN^z$ as $\sqrt{1-\varrho_2^2}\sigma_ZN^z_tB^2_t$ without the $d$ of $dB^2_t$.
-- source:
--   Bo, Huang & Yu, Stochastic control problems with state-reflections arising from relaxed benchmark tracking, arXiv:2302.08302v4, p. 8 (3.1)–(3.6), p. 9 (3.7), p. 10 (3.13)–(3.14), p. 13 (G^h), p. 16 (3.36)–(3.37), p. 18 (4.1)

import Mathlib
import Definitions.Def_BenchmarkTracking_Verification_Model
import Definitions.Def_BenchmarkTracking_Verification_Analysis
import Definitions.Def_RankBasedSDI_LoadBalancing_Reflection

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BenchmarkTracking.Verification

/-!
Bo, Huang & Yu, arXiv:2302.08302v4, §3, pp. 8–18 and (4.1), p. 18: the reflected processes
(3.2)–(3.5), (3.14), the function `v` of the probabilistic representation (3.1), its dual
`û` (3.6), the pieces `l` (3.7), `φ` (3.13), `ξ` (3.36), `ψ` (3.37), and the primal function `u`
of (4.1).

A *carrier* is a probability space `(Ω, P)` with a process `B : ℝ≥0 → Ω → ℝ³`; the theorems take
`B` to be a standard 3-dimensional Brownian motion (`EthierKurtz.IsStandardBrownian`), whose
coordinates `0, 1, 2` are the independent scalar Brownian motions `B⁰, B¹, B²` of p. 8. Processes
are indexed by real time `t` and used for `t ≥ 0`; `B` is evaluated at `t.toNNReal`.
-/

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The scalar Brownian motion `Bⁱ_t`, `i ∈ {0, 1, 2}`, at real time `t ≥ 0`. -/
noncomputable def bm (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3)) (i : Fin 3) (t : ℝ) (ω : Ω) : ℝ :=
  B t.toNNReal ω i

/-- `B³ := ϱ₁B¹ + √(1 − ϱ₁²)B⁰`, p. 8. -/
noncomputable def bm3 (M : Params d) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3)) (t : ℝ)
    (ω : Ω) : ℝ :=
  M.rho1 * bm B 1 t ω + Real.sqrt (1 - M.rho1 ^ 2) * bm B 0 t ω

/-- `L^r_t = 0 ∨ {−r + max_{s∈[0,t]}[−αB¹_s − (α²/2 − ρ)s]}`, (3.5): the Skorokhod regulator of
the free path `r + (α²/2 − ρ)s + αB¹_s`. -/
noncomputable def regR (M : Params d) (ρ : ℝ) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3))
    (r t : ℝ) (ω : Ω) : ℝ :=
  RankBasedSDI.LoadBalancing.skorokhodReg
    (fun s => r + (M.alpha ^ 2 / 2 - ρ) * s + M.alpha * bm B 1 s ω) t

/-- The reflected drifted Brownian motion `R^r_t = r + (α²/2 − ρ)t + αB¹_t + L^r_t ≥ 0`, (3.2). -/
noncomputable def procR (M : Params d) (ρ : ℝ) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3))
    (r t : ℝ) (ω : Ω) : ℝ :=
  r + (M.alpha ^ 2 / 2 - ρ) * t + M.alpha * bm B 1 t ω + regR M ρ B r t ω

/-- `K^h_t = 0 ∨ {−h + max_{s∈[0,t]}(µ_B s + σ_B B³_s)}`, (3.5). -/
noncomputable def regK (M : Params d) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3))
    (h t : ℝ) (ω : Ω) : ℝ :=
  RankBasedSDI.LoadBalancing.skorokhodReg (fun s => h - M.muB * s - M.sigmaB * bm3 M B s ω) t

/-- `H^h_t = h − µ_B t − ϱ₁σ_B B¹_t − √(1 − ϱ₁²)σ_B B⁰_t + K^h_t ≥ 0`, (3.3). -/
noncomputable def procH (M : Params d) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3))
    (h t : ℝ) (ω : Ω) : ℝ :=
  h - M.muB * t - M.sigmaB * bm3 M B t ω + regK M B h t ω

/-- The GBM `N^z` of p. 8, `dN^z = µ_Z N^z dt + ϱ₂σ_Z N^z dB¹ + √(1 − ϱ₂²)σ_Z N^z dB²`, `N^z_0 = z`,
in closed form `z exp((µ_Z − σ_Z²/2)t + σ_Z(ϱ₂B¹_t + √(1 − ϱ₂²)B²_t))`. -/
noncomputable def procN (M : Params d) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3))
    (z t : ℝ) (ω : Ω) : ℝ :=
  z * Real.exp ((M.muZ - M.sigmaZ ^ 2 / 2) * t +
    M.sigmaZ * (M.rho2 * bm B 1 t ω + Real.sqrt (1 - M.rho2 ^ 2) * bm B 2 t ω))

/-- `G^h_s = h ∨ {max_{l∈[0,s]}(µ_B l + σ_B B⁰_l)} − h` (p. 13), the regulator of the reflected
SDE (3.14) `P^h_t = h − µ_B t − σ_B B⁰_t + G^h_t ≥ 0`, driven by `B⁰` alone. -/
noncomputable def regG (M : Params d) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3))
    (h t : ℝ) (ω : Ω) : ℝ :=
  RankBasedSDI.LoadBalancing.skorokhodReg (fun s => h - M.muB * s - M.sigmaB * bm B 0 s ω) t

/-- `E[∫_0^∞ e^{−ρs + (p/(1−p))R^r_s} ds] ∈ [0, ∞]`, the first expectation in (3.1). -/
noncomputable def expect1 (M : Params d) (ρ : ℝ) (Pr : Measure Ω)
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3)) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (∫⁻ s in Ici (0 : ℝ),
    ENNReal.ofReal (Real.exp (-ρ * s + M.p / (1 - M.p) * procR M ρ B r s ω))) ∂Pr

/-- `E[∫_0^∞ e^{−ρs − R^r_s} N^z_s ds] ∈ [0, ∞]`, the second expectation in (3.1). -/
noncomputable def expect2 (M : Params d) (ρ : ℝ) (Pr : Measure Ω)
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3)) (r z : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (∫⁻ s in Ici (0 : ℝ),
    ENNReal.ofReal (Real.exp (-ρ * s - procR M ρ B r s ω) * procN M B z s ω)) ∂Pr

/-- `E[∫_0^∞ e^{−ρs − R^r_s} dK^h_s] ∈ [0, ∞]`, the third expectation in (3.1) (also (3.39)). -/
noncomputable def expect3 (M : Params d) (ρ : ℝ) (Pr : Measure Ω)
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3)) (r h : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, stieltjesLIntegral (fun s => regK M B h s ω)
    (fun s => ENNReal.ofReal (Real.exp (-ρ * s - procR M ρ B r s ω))) ∂Pr

/-- `E[∫_0^∞ e^{−ρs − R^r_s} dG^h_s] ∈ [0, ∞]`, the expectation in (3.13). -/
noncomputable def expectG (M : Params d) (ρ : ℝ) (Pr : Measure Ω)
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3)) (r h : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, stieltjesLIntegral (fun s => regG M B h s ω)
    (fun s => ENNReal.ofReal (Real.exp (-ρ * s - procR M ρ B r s ω))) ∂Pr

/-- The probabilistic representation (3.1):
`v(r,h,z) = ((1−p)/p)β^{−p/(1−p)}E[∫e^{−ρs+(p/(1−p))R^r_s}ds] + β(κ₂ − µ_Z)E[∫e^{−ρs−R^r_s}N^z_s ds]
 − βE[∫e^{−ρs−R^r_s}dK^h_s]`. Each expectation is a `lintegral`, converted with `toReal`; the
theorems about `v` also assert that the three are finite. -/
noncomputable def vRep (M : Params d) (ρ : ℝ) (Pr : Measure Ω)
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3)) (r h z : ℝ) : ℝ :=
  (1 - M.p) / M.p * M.beta ^ (-M.p / (1 - M.p)) * (expect1 M ρ Pr B r).toReal +
    M.beta * (M.kappa2 - M.muZ) * (expect2 M ρ Pr B r z).toReal -
    M.beta * (expect3 M ρ Pr B r h).toReal

/-- `l(r, z)`, the sum of the first two terms of (3.1), (3.7). -/
noncomputable def lRep (M : Params d) (ρ : ℝ) (Pr : Measure Ω)
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3)) (r z : ℝ) : ℝ :=
  (1 - M.p) / M.p * M.beta ^ (-M.p / (1 - M.p)) * (expect1 M ρ Pr B r).toReal +
    M.beta * (M.kappa2 - M.muZ) * (expect2 M ρ Pr B r z).toReal

/-- `φ(r, h) := −βE[∫_0^∞ e^{−ρs−R^r_s} dG^h_s]`, (3.13). -/
noncomputable def phiRep (M : Params d) (ρ : ℝ) (Pr : Measure Ω)
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3)) (r h : ℝ) : ℝ :=
  -M.beta * (expectG M ρ Pr B r h).toReal

/-- `φ_rh`, the mixed second partial derivative of `φ` on the closed quadrant `ℝ²₊`. -/
noncomputable def phiRH (M : Params d) (ρ : ℝ) (Pr : Measure Ω)
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3)) (r h : ℝ) : ℝ :=
  pd2₂ (pd2₁ (phiRep M ρ Pr B) (Ici 0)) (Ici 0) r h

/-- `ξ(r, h) := −κ₁E[∫_0^∞ e^{−ρs} φ_rh(R^r_s, H^h_s) ds]`, (3.36), with Bochner integrals in `s`
and in `ω` (Proposition 3.5 asserts the integrability that makes this the true value). -/
noncomputable def xiRep (M : Params d) (ρ : ℝ) (Pr : Measure Ω)
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3)) (r h : ℝ) : ℝ :=
  -M.kappa1 * ∫ ω, (∫ s in Ici (0 : ℝ),
    Real.exp (-ρ * s) * phiRH M ρ Pr B (procR M ρ B r s ω) (procH M B h s ω)) ∂Pr

/-- `ψ(r, h) := φ(r, h) + ξ(r, h)`, (3.37). -/
noncomputable def psiRep (M : Params d) (ρ : ℝ) (Pr : Measure Ω)
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3)) (r h : ℝ) : ℝ :=
  phiRep M ρ Pr B r h + xiRep M ρ Pr B r h

/-- The dual function `û(y, h, z) := v(−ln(y/β), h, z)` for `y ∈ (0, β]`, (3.6). -/
noncomputable def uHat (M : Params d) (ρ : ℝ) (Pr : Measure Ω)
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3)) (y h z : ℝ) : ℝ :=
  vRep M ρ Pr B (-Real.log (y / M.beta)) h z

/-- `u(x, h, z) = inf_{y∈(0,β]} {û(y, h, z) + yx}`, (4.1), as a real `sInf`; Theorem 4.1(i)
asserts that the infimum is attained, so this is the true infimum. -/
noncomputable def uPrimal (M : Params d) (ρ : ℝ) (Pr : Measure Ω)
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3)) (x h z : ℝ) : ℝ :=
  sInf ((fun y => uHat M ρ Pr B y h z + y * x) '' Ioc 0 M.beta)

end BenchmarkTracking.Verification


