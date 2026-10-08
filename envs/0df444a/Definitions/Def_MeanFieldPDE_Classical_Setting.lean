-- Prove2me | Definitions.Def_MeanFieldPDE_Classical_Setting
-- name    : MeanFieldPDE_Classical_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T22:05:26.606255+00:00
-- url     : https://prove2.me/theorems/73a48dd5-0cf0-431b-b857-7562942ce3a0
-- title:
--   §2–§3, pp. 4, 8–9 — Brownian motion, rich F₀, the filtration 𝔽, P₂ and W₂, Lipschitz coefficients, solutions of (3.1)–(3.2) in S², the value function (3.6)/(5.1)
-- statement:
--   This module fixes the standing setting of §3 of Buckdahn, Li, Peng and Rainer and the objects built on it.
--
--   1. **Measures.** $\mathcal P_2(\mathbb R^d)$ is the set of Borel probability measures $\mu$ on $\mathbb R^d$ with $\int|x|^2\,\mu(dx)<\infty$, and
--   $$W_2(\mu,\nu)=\Big(\inf_{\rho}\int_{\mathbb R^d\times\mathbb R^d}|x-y|^2\,\rho(dx\,dy)\Big)^{1/2},$$
--   the infimum over all couplings $\rho$ of $\mu$ and $\nu$ (2.1).
--   2. **Stochastic basis.** $(\Omega,\mathcal F,P)$ is a complete probability space carrying a $d$-dimensional Brownian motion $B=(B^1,\dots,B^d)$, the horizon is $T>0$, and $\mathcal F_0\subset\mathcal F$ is a sub-$\sigma$-field such that (i) $B$ is independent of $\mathcal F_0$ and (ii) $\mathcal F_0$ is rich enough: every $\mu\in\mathcal P_2(\mathbb R^d)$ is the law $P_\vartheta$ of some $\vartheta\in L^2(\mathcal F_0;\mathbb R^d)$.
--   3. **Filtration.** $\mathcal F_t=\sigma\{B_r,\ r\le t\}\vee\mathcal F_0\vee\mathcal N_P$, with $\mathcal N_P$ the $P$-null sets; $L^2(\mathcal F_t;\mathbb R^d)$ is the space of square-integrable $\mathcal F_t$-measurable random vectors.
--   4. **Coefficients.** $\sigma:\mathbb R^d\times\mathcal P_2(\mathbb R^d)\to\mathbb R^{d\times d}$ and $b:\mathbb R^d\times\mathcal P_2(\mathbb R^d)\to\mathbb R^d$ are Lipschitz: $|\sigma(x,\mu)-\sigma(x',\mu')|+|b(x,\mu)-b(x',\mu')|\le L(|x-x'|+W_2(\mu,\mu'))$.
--   5. **The SDEs.** For $t\in[0,T]$ and $\xi\in L^2(\mathcal F_t;\mathbb R^d)$, $X^{t,\xi}$ solves the mean-field SDE (3.1)
--   $$X^{t,\xi}_s=\xi+\int_t^s\sigma(X^{t,\xi}_r,P_{X^{t,\xi}_r})\,dB_r+\int_t^s b(X^{t,\xi}_r,P_{X^{t,\xi}_r})\,dr,\qquad s\in[t,T],$$
--   and, for $x\in\mathbb R^d$, $X^{t,x,\xi}$ solves (3.2), the same equation started at $x$ with the law flow $P_{X^{t,\xi}_r}$ frozen. Solutions are taken in $\mathcal S^2([t,T];\mathbb R^d)$: adapted, continuous, with $E[\sup_{s\in[t,T]}|X_s|^2]<\infty$. The decoupled equation is defined for any square-integrable $\mathcal F_t$-measurable initial value $\zeta$; (3.2) is the case $\zeta\equiv x$.
--   6. **Value function** (3.6) = (5.1): for $\Phi:\mathbb R^d\times\mathcal P_2(\mathbb R^d)\to\mathbb R$ and solution families $X^{t,\xi}$, $X^{t,x,\xi}$,
--   $$V(t,x,\mu)=E\big[\Phi(X^{t,x,\xi}_T,P_{X^{t,\xi}_T})\big],$$
--   where $\xi$ is a fixed choice of an $\mathcal F_0$-measurable square-integrable vector with $P_\xi=\mu$.
--
--   These are the objects of every statement of the paper.
--
--   **Formalization Note** Time is `ℝ≥0`; $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`; measures are `Measure (E d)` and every condition is quantified over $\mathcal P_2$ only. $W_2$ is the real part of the published `wassersteinDistance 2`, finite on $\mathcal P_2$. The Brownian motion, the Brownian filtration and the Itô integral are the published `Peng1990.SMP` objects; the stochastic integral $\int_t^s\sigma\,dB$ is $J(s)-J(t)$ for an Itô integral process $J$ of the integrand $1_{(t,T]}(r)\sigma(\cdot)$; the drift is required a.s. integrable on $[t,s]$. Matrices carry the Frobenius norm. The solution families are hypotheses of the theorems (the companion well-posedness theorem states they exist); the value function picks its representative of $\mu$ by choice, and Theorem 6.2 (a) states that any other $\xi$ of law $\mu$ gives the same value.
-- source:
--   Buckdahn, Li, Peng & Rainer, Mean-field stochastic differential equations and associated PDEs, arXiv:1407.1215v1, pp. 4, 8–9, (2.1), §3 standing assumptions, (3.1), (3.2), (3.6); p. 25, (5.1)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Setting
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MeanFieldPDE.Classical

open Peng1990.SMP

/-- The Euclidean space `ℝ^d` (norm `|·|`, inner product `x · y`). -/
abbrev E (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- `μ ∈ P₂(ℝ^d)` (§2, p. 4): `μ` is a Borel probability measure on `ℝ^d` with finite second
moment `∫ |x|² μ(dx) < ∞`. -/
def IsP2 {d : ℕ} (μ : Measure (E d)) : Prop :=
  IsProbabilityMeasure μ ∧ ∫⁻ x, ‖x‖ₑ ^ 2 ∂μ < ⊤

/-- The 2-Wasserstein distance (2.1), p. 4: `W₂(μ, ν) = (inf_ρ ∫ |x − y|² ρ(dx dy))^{1/2}` over
the couplings `ρ` of `μ` and `ν`, as a real number. It is finite, hence faithful, on `P₂(ℝ^d)`;
it is only ever evaluated between elements of `P₂(ℝ^d)`. -/
noncomputable def W2 {d : ℕ} (μ ν : Measure (E d)) : ℝ :=
  (WassersteinDRO.Duality.wassersteinDistance 2 μ ν).toReal

/-- The Frobenius norm `(Σ_{i,j} M_{ij}²)^{1/2}` of a `d × d` matrix. -/
noncomputable def frob {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, M i j ^ 2)

/-- The standing setting of §3 (p. 8): `(Ω, F, P)` is a complete probability space carrying a
`d`-dimensional Brownian motion `B`, the horizon is `T > 0`, and `F₀ ⊂ F` is a sub-σ-field such
that i) `B` is independent of `F₀`, and ii) `F₀` is rich enough: every `μ ∈ P₂(ℝ^d)` is the law
`P_ϑ` of some `ϑ ∈ L²(F₀; ℝ^d)`. -/
structure IsSetting {Ω : Type*} (F₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (B : ℝ≥0 → Ω → Fin d → ℝ) (T : ℝ≥0) : Prop where
  prob : IsProbabilityMeasure P
  complete : P.IsComplete
  brownian : IsStdBrownian P B
  T_pos : 0 < T
  F₀_le : F₀ ≤ mΩ
  indep : Indep F₀ (MeasurableSpace.comap (fun ω (t : ℝ≥0) => B t ω) inferInstance) P
  rich : ∀ μ : Measure (E d), IsP2 μ →
    ∃ ϑ : Ω → E d, Measurable[F₀] ϑ ∧ MemLp ϑ 2 P ∧ P.map ϑ = μ

/-- The filtration `𝔽 = (F_t)` of §3 (p. 8), generated by `B`, completed and augmented by `F₀`:
`F_t = σ{B_r, r ≤ t} ∨ F₀ ∨ {P-null sets}`. -/
noncomputable def filt {Ω : Type*} {F₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {B : ℝ≥0 → Ω → Fin d → ℝ} {T : ℝ≥0} (hS : IsSetting F₀ P B T) : Filtration ℝ≥0 mΩ where
  seq t := brownianFiltration hS.brownian t ⊔ F₀ ⊔ ReflectedBSDE.Existence.nullSigma P
  mono' _ _ hst :=
    sup_le_sup_right (sup_le_sup_right ((brownianFiltration hS.brownian).mono hst) _) _
  le' t := sup_le (sup_le ((brownianFiltration hS.brownian).le t) hS.F₀_le)
    (MeasurableSpace.generateFrom_le fun _ hN => hN.1)

/-- `ξ ∈ L²(F_t; ℝ^d)`: `ξ` is `F_t`-measurable and square integrable. -/
def IsL2At {Ω : Type*} {F₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {B : ℝ≥0 → Ω → Fin d → ℝ} {T : ℝ≥0} (hS : IsSetting F₀ P B T)
    (t : ℝ≥0) (ξ : Ω → E d) : Prop :=
  StronglyMeasurable[filt hS t] ξ ∧ MemLp ξ 2 P

/-- `X ∈ S²([t, T]; ℝ^d)` (p. 8): `X` is `𝔽`-adapted on `[t, T]`, every path is continuous on
`[t, T]` (the page's "continuous processes"), and `E[sup_{s ∈ [t,T]} |X_s|²] < +∞`. -/
def IsS2 {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}
    (𝔽 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (t T : ℝ≥0) (X : ℝ≥0 → Ω → E d) : Prop :=
  (∀ s, t ≤ s → s ≤ T → StronglyMeasurable[𝔽 s] (X s)) ∧
    (∀ ω, ContinuousOn (fun s => X s ω) (Set.Icc t T)) ∧
    ∫⁻ ω, ⨆ s ∈ Set.Icc t T, ‖X s ω‖ₑ ^ 2 ∂P < ⊤

/-- The standing Lipschitz condition of §3 (p. 8) on the deterministic coefficients
`σ : ℝ^d × P₂(ℝ^d) → ℝ^{d×d}` and `b : ℝ^d × P₂(ℝ^d) → ℝ^d`: for some `L` and all
`x, x' ∈ ℝ^d`, `μ, μ' ∈ P₂(ℝ^d)`,
`|σ(x, μ) − σ(x', μ')| + |b(x, μ) − b(x', μ')| ≤ L (|x − x'| + W₂(μ, μ'))`
(Frobenius norm on matrices). -/
def IsLipCoeff {d : ℕ} (σ : E d → Measure (E d) → Matrix (Fin d) (Fin d) ℝ)
    (b : E d → Measure (E d) → E d) : Prop :=
  ∃ L : ℝ, ∀ (x x' : E d) (μ μ' : Measure (E d)), IsP2 μ → IsP2 μ' →
    frob (σ x μ - σ x' μ') ≤ L * (‖x - x'‖ + W2 μ μ') ∧
      ‖b x μ - b x' μ'‖ ≤ L * (‖x - x'‖ + W2 μ μ')

/-- `Y` solves, on `[t, T]`, the SDE with initial value `ζ` and frozen law flow `m`
`Y_s = ζ + ∫_t^s σ(Y_r, m_r) dB_r + ∫_t^s b(Y_r, m_r) dr`, `s ∈ [t, T]`:
`Y ∈ S²([t, T]; ℝ^d)`, there are Itô integrals `J_{iℓ}` (against `B^ℓ`, for the filtration `𝔽`) of
`r ↦ 1_{(t,T]}(r) σ_{iℓ}(Y_r, m_r)`, and for every `s ∈ [t, T]`, almost surely, `r ↦ b(Y_r, m_r)` is
integrable on `[t, s]` and `Y_s^i = ζ^i + Σ_ℓ (J_{iℓ}(s) − J_{iℓ}(t)) + (∫_t^s b(Y_r, m_r) dr)^i`. -/
def SolvesSDE {Ω : Type*} {F₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {B : ℝ≥0 → Ω → Fin d → ℝ} {T : ℝ≥0} (hS : IsSetting F₀ P B T)
    (σ : E d → Measure (E d) → Matrix (Fin d) (Fin d) ℝ) (b : E d → Measure (E d) → E d)
    (t : ℝ≥0) (ζ : Ω → E d) (m : ℝ≥0 → Measure (E d)) (Y : ℝ≥0 → Ω → E d) : Prop :=
  IsS2 (filt hS) P t T Y ∧
    ∃ J : Fin d → Fin d → ℝ≥0 → Ω → ℝ,
      (∀ i ℓ, IsItoIntegral (filt hS) P T (fun r ω => B r ω ℓ)
        (fun r ω => if t < r ∧ r ≤ T then σ (Y r ω) (m r) i ℓ else 0) (J i ℓ)) ∧
      ∀ s, t ≤ s → s ≤ T → ∀ᵐ ω ∂P,
        IntegrableOn (fun r : ℝ => b (Y r.toNNReal ω) (m r.toNNReal)) (Set.Icc (t : ℝ) s) ∧
        ∀ i, Y s ω i = ζ ω i + ∑ ℓ, (J i ℓ s ω - J i ℓ t ω)
          + (∫ r in Set.Icc (t : ℝ) s, b (Y r.toNNReal ω) (m r.toNNReal)) i

/-- `X = X^{t,ξ}` solves the mean-field (McKean–Vlasov) SDE (3.1), p. 8:
`X_s = ξ + ∫_t^s σ(X_r, P_{X_r}) dB_r + ∫_t^s b(X_r, P_{X_r}) dr`, `s ∈ [t, T]`, in `S²([t, T]; ℝ^d)`. -/
def SolvesMV {Ω : Type*} {F₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {B : ℝ≥0 → Ω → Fin d → ℝ} {T : ℝ≥0} (hS : IsSetting F₀ P B T)
    (σ : E d → Measure (E d) → Matrix (Fin d) (Fin d) ℝ) (b : E d → Measure (E d) → E d)
    (t : ℝ≥0) (ξ : Ω → E d) (X : ℝ≥0 → Ω → E d) : Prop :=
  SolvesSDE hS σ b t ξ (fun r => P.map (X r)) X

/-- `Y` solves the decoupled SDE (3.2), p. 8, with initial value `ζ` and the law flow of a solution
`Xξ = X^{t,ξ}` of (3.1): `Y_s = ζ + ∫_t^s σ(Y_r, P_{X^{t,ξ}_r}) dB_r + ∫_t^s b(Y_r, P_{X^{t,ξ}_r}) dr`.
Equation (3.2) itself, `X^{t,x,ξ}`, is the case `ζ ≡ x`. -/
def SolvesDec {Ω : Type*} {F₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {B : ℝ≥0 → Ω → Fin d → ℝ} {T : ℝ≥0} (hS : IsSetting F₀ P B T)
    (σ : E d → Measure (E d) → Matrix (Fin d) (Fin d) ℝ) (b : E d → Measure (E d) → E d)
    (t : ℝ≥0) (ζ : Ω → E d) (Xξ : ℝ≥0 → Ω → E d) (Y : ℝ≥0 → Ω → E d) : Prop :=
  SolvesSDE hS σ b t ζ (fun r => P.map (Xξ r)) Y

/-- `Xξ` is a family of solutions of (3.1): `Xξ t ξ = X^{t,ξ}` for every `t ∈ [0, T]` and every
`ξ ∈ L²(F_t; ℝ^d)`. -/
def IsMVFamily {Ω : Type*} {F₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {B : ℝ≥0 → Ω → Fin d → ℝ} {T : ℝ≥0} (hS : IsSetting F₀ P B T)
    (σ : E d → Measure (E d) → Matrix (Fin d) (Fin d) ℝ) (b : E d → Measure (E d) → E d)
    (Xξ : ℝ≥0 → (Ω → E d) → ℝ≥0 → Ω → E d) : Prop :=
  ∀ t ≤ T, ∀ ξ : Ω → E d, IsL2At hS t ξ → SolvesMV hS σ b t ξ (Xξ t ξ)

/-- `Xx` is a family of solutions of (3.2): `Xx t x ξ = X^{t,x,ξ}` for every `t ∈ [0, T]`,
`x ∈ ℝ^d` and `ξ ∈ L²(F_t; ℝ^d)`, driven by the law flow of `Xξ t ξ = X^{t,ξ}`. -/
def IsDecFamily {Ω : Type*} {F₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {B : ℝ≥0 → Ω → Fin d → ℝ} {T : ℝ≥0} (hS : IsSetting F₀ P B T)
    (σ : E d → Measure (E d) → Matrix (Fin d) (Fin d) ℝ) (b : E d → Measure (E d) → E d)
    (Xξ : ℝ≥0 → (Ω → E d) → ℝ≥0 → Ω → E d)
    (Xx : ℝ≥0 → E d → (Ω → E d) → ℝ≥0 → Ω → E d) : Prop :=
  ∀ t ≤ T, ∀ (x : E d) (ξ : Ω → E d), IsL2At hS t ξ →
    SolvesDec hS σ b t (fun _ => x) (Xξ t ξ) (Xx t x ξ)

open _root_.Classical in
/-- A chosen representative of `μ ∈ P₂(ℝ^d)`: an `F₀`-measurable square-integrable `ϑ` with
`P_ϑ = μ` (it exists by the richness of `F₀`; junk value `0` if there is none). -/
noncomputable def lawRep {Ω : Type*} (F₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (μ : Measure (E d)) :
    Ω → E d :=
  if h : ∃ ϑ : Ω → E d, Measurable[F₀] ϑ ∧ MemLp ϑ 2 P ∧ P.map ϑ = μ then Classical.choose h
  else 0

/-- The value function (3.6) = (5.1), pp. 9, 25:
`V(t, x, μ) = E[Φ(X^{t,x,P_ξ}_T, P_{X^{t,ξ}_T})]` with `ξ` the chosen representative of `μ`. -/
noncomputable def valueFn {Ω : Type*} (F₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (T : ℝ≥0)
    (Φ : E d → Measure (E d) → ℝ) (Xξ : ℝ≥0 → (Ω → E d) → ℝ≥0 → Ω → E d)
    (Xx : ℝ≥0 → E d → (Ω → E d) → ℝ≥0 → Ω → E d) (t : ℝ≥0) (x : E d) (μ : Measure (E d)) : ℝ :=
  ∫ ω, Φ (Xx t x (lawRep F₀ P μ) T ω) (P.map (Xξ t (lawRep F₀ P μ) T)) ∂P

end MeanFieldPDE.Classical


