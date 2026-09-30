-- Prove2me | Definitions.Def_SabanisEuler_Shared_Setting
-- name    : SabanisEuler_Shared_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T23:56:37.075881+00:00
-- url     : https://prove2.me/theorems/1d7d7f57-b120-4b8e-9a83-b92035004ce3
-- title:
--   The SDE (2.1) and the Euler-type scheme (2.2) on [0, T]: Itô processes, Wiener martingale, grid map κₙ
-- statement:
--   This file fixes the probabilistic setting of Sabanis (2016), §2.
--
--   Let $(\Omega,\{\mathcal F_t\}_{t\ge0},\mathcal F,P)$ be a filtered probability space, $d,d_1\in\mathbb N$, and $T>0$ a fixed horizon. States lie in $\mathbb R^d$ with the Euclidean norm $|x|$; diffusion values are $d\times d_1$ real matrices with the Hilbert–Schmidt norm $|A|=(\sum_{i,j}A_{ij}^2)^{1/2}$ (the type $\mathrm{Diffusion}(d,d_1)$).
--
--   1. **Grid map.** For $n\ge1$, $\kappa_n(t)=\lfloor nt\rfloor/n$.
--   2. **Wiener martingale.** A process $W=(W(t))_{t\ge0}$ with values in $\mathbb R^{d_1}$ is a $d_1$-dimensional Wiener martingale for $\{\mathcal F_t\}$ if it is a standard $d_1$-dimensional Brownian motion (continuous paths, independent standard real Brownian coordinates), $W(t)$ is $\mathcal F_t$-measurable for every $t$, and for every $t$ the future increments $(W(r)-W(t))_{r\ge t}$ are independent of $\mathcal F_t$.
--   3. **Itô process on $[0,T]$.** Given an initial value $\xi$, a drift integrand $B(s,\omega)\in\mathbb R^d$ and a diffusion integrand $S(s,\omega)\in\mathbb R^{d\times d_1}$, a process $X$ is an Itô process with these data if $X(t)$ is measurable and adapted to the $P$-completion of $\{\mathcal F_t\}$, its paths are continuous on $[0,T]$, the drift integrand is pathwise integrable on $[0,t]$ for $t\le T$, and almost surely, simultaneously for all $t\in[0,T]$,
--   $$X(t)=\xi+\int_0^t B(s)\,ds+\int_0^t S(s)\,dW(s),$$
--   where the stochastic integral is the Brownian Itô integral (a continuous, adapted process given coordinatewise by the platform relation of the Ethier–Kurtz series), with the integrand set to $0$ after $T$.
--   4. **Solution of (2.1).** $X$ solves $dX(t)=b(t,X(t))\,dt+\sigma(t,X(t))\,dW(t)$ on $[0,T]$ with $X(0)=\xi$ when it is an Itô process with $B(s)=b(s,X(s))$, $S(s)=\sigma(s,X(s))$.
--   5. **Solution of the scheme (2.2).** For $n\ge1$, $X_n$ solves $dX_n(t)=b_n(t,X_n(\kappa_n(t)))\,dt+\sigma_n(t,X_n(\kappa_n(t)))\,dW(t)$ on $[0,T]$ with the same initial value $X_n(0)=\xi$ when it is an Itô process with $B(s)=b_n(s,X_n(\kappa_n(s)))$ and $S(s)=\sigma_n(s,X_n(\kappa_n(s)))$.
--
--   These are the objects about which the paper's Theorems 1–4 and Lemmas 1–4 speak.
--
--   **Formalization Note** The completeness of the filtration (part of the paper's usual conditions) is handled by asking adaptedness to the filtration augmented by all $P$-null sets, which is weaker than asking the filtration itself to be complete; right-continuity is imposed as a hypothesis of the theorems. Nothing is required of the processes after $T$ beyond measurability and adaptedness, so that no existence beyond the horizon is assumed.
--
--   **Shared definition.** Serves chunks `01-lp-convergence` (§1 notation, §2 setting, eqs. (2.1)–(2.2), pp. 2–3; Theorems 1, 4, Lemmas 1–2; previously `SabanisEuler.LpConv.Setting`), `02-rate` (same pages; Theorem 2, Lemmas 2–4; previously `SabanisEuler.Rate.Setting`) and `03-uniform-rate` (same pages; Theorem 3, Lemmas 2–4; previously `SabanisEuler.UniformRate.Setting`). The three copies were identical up to their namespace: the same `Diffusion` (Hilbert–Schmidt norm), grid map `kappa` $=\lfloor nt\rfloor/n$, `IsWienerMartingale`, `IsItoProcess` (adaptedness to the $P$-completed filtration, continuity and the integral identity only on $[0,T]$), `IsSolution` and `IsSchemeSolution`.
-- source:
--   Sabanis, Euler approximations with varying coefficients, arXiv:1308.1796v4, pp. 2-3, §1 notation, §2 setting, eq. (2.1), eq. (2.2); shared by chunks 01-lp-convergence, 02-rate and 03-uniform-rate

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedSDEPast
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace SabanisEuler.Shared

open EthierKurtz

/-- Sabanis (2016), p. 2: diffusion values are `d × d₁` real matrices. As a Euclidean
space indexed by `Fin d × Fin d₁`, the norm is the Hilbert–Schmidt (Frobenius) norm
`|A| = (∑ᵢⱼ Aᵢⱼ²)^{1/2}`, which is the paper's matrix norm. -/
abbrev Diffusion (d d₁ : ℕ) := EuclideanSpace ℝ (Fin d × Fin d₁)

/-- Sabanis (2016), p. 3: the grid point `κₙ(t) = ⌊n t⌋ / n`. Only `n ≥ 1` is used. -/
noncomputable def kappa (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  (⌊(n : ℝ≥0) * t⌋₊ : ℝ≥0) / n

/-- Sabanis (2016), p. 2: `W` is a `d₁`-dimensional Wiener martingale with respect to the
filtration `ℱ`: a standard `d₁`-dimensional Brownian motion (continuous paths, independent
standard real Brownian coordinates), adapted to `ℱ`, whose future increments
`(W r - W t)_{r ≥ t}` are independent of `ℱ t` for every `t`. -/
def IsWienerMartingale {d₁ : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → SDEState d₁) : Prop :=
  IsStandardBrownian P W ∧
  (∀ t, Measurable[ℱ t] (W t)) ∧
  ∀ t, Indep (ℱ t)
    (MeasurableSpace.comap (fun ω (r : Set.Ici t) => W r.val ω - W t ω) inferInstance) P

/-- An Itô process on the horizon `[0, T]`, driven by the Wiener process `W`:
`X` is measurable, adapted to the `P`-completion of `ℱ`, has continuous paths on `[0, T]`,
and almost surely, simultaneously for all `t ∈ [0, T]`,
`X t = ξ + ∫₀ᵗ B(u) du + ∫₀ᵗ S(u) dW(u)`, coordinatewise
`X t i = ξ i + ∫₀ᵗ B(u) i du + ∑ⱼ J t (i, j)`, where `J · (i, j)` is the Brownian Itô integral
(platform relation `EthierKurtz.HasBrownianItoIntegral`) of the integrand `S · (i, j)`, cut off
to `0` after `T`, against the `j`-th coordinate of `W`. The drift integrand is required to be
pathwise interval-integrable on `[0, t]` for `t ≤ T`. Nothing is required of `X` after `T`
beyond measurability and adaptedness. -/
def IsItoProcess {d d₁ : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → SDEState d₁) (T : ℝ≥0) (ξ : Ω → SDEState d)
    (B : ℝ≥0 → Ω → SDEState d) (S : ℝ≥0 → Ω → Diffusion d d₁)
    (X : ℝ≥0 → Ω → SDEState d) : Prop :=
  (∀ t, Measurable (X t)) ∧
  (∀ t, Measurable[completedSDEPast P ℱ t] (X t)) ∧
  (∀ ω, ContinuousOn (fun t => X t ω) (Set.Icc 0 T)) ∧
  ∃ J : ℝ≥0 → Ω → Diffusion d d₁,
    (∀ ω, Continuous (fun t => J t ω)) ∧
    (∀ t, Measurable[completedSDEPast P ℱ t] (J t)) ∧
    (∀ i j, HasBrownianItoIntegral P (completedSDEPast P ℱ) (fun t ω => W t ω j)
      (fun t ω => if t ≤ T then S t ω (i, j) else 0) (fun t ω => J t ω (i, j))) ∧
    (∀ t ≤ T, ∀ ω i,
      IntervalIntegrable (fun u : ℝ => B u.toNNReal ω i) volume 0 (t : ℝ)) ∧
    ∀ᵐ ω ∂P, ∀ t ≤ T, ∀ i,
      X t ω i = ξ ω i + (∫ u in (0 : ℝ)..(t : ℝ), B u.toNNReal ω i) + ∑ j, J t ω (i, j)

/-- Sabanis (2016), eq. (2.1): `X` solves `dX(t) = b(t, X(t)) dt + σ(t, X(t)) dW(t)` on
`[0, T]` with initial value `X(0) = ξ`. -/
def IsSolution {d d₁ : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → SDEState d₁) (T : ℝ≥0) (ξ : Ω → SDEState d)
    (b : ℝ≥0 × SDEState d → SDEState d) (σ : ℝ≥0 × SDEState d → Diffusion d d₁)
    (X : ℝ≥0 → Ω → SDEState d) : Prop :=
  IsItoProcess P ℱ W T ξ (fun s ω => b (s, X s ω)) (fun s ω => σ (s, X s ω)) X

/-- Sabanis (2016), eq. (2.2): `Y` solves the `n`-th explicit Euler-type scheme
`dY(t) = bₙ(t, Y(κₙ(t))) dt + σₙ(t, Y(κₙ(t))) dW(t)` on `[0, T]` with the same initial
value `Y(0) = ξ` as (2.1). -/
def IsSchemeSolution {d d₁ : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → SDEState d₁) (T : ℝ≥0) (ξ : Ω → SDEState d)
    (bₙ : ℕ → ℝ≥0 × SDEState d → SDEState d) (σₙ : ℕ → ℝ≥0 × SDEState d → Diffusion d d₁)
    (n : ℕ) (Y : ℝ≥0 → Ω → SDEState d) : Prop :=
  IsItoProcess P ℱ W T ξ (fun s ω => bₙ n (s, Y (kappa n s) ω))
    (fun s ω => σₙ n (s, Y (kappa n s) ω)) Y

end SabanisEuler.Shared


