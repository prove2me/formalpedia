-- Prove2me | Definitions.Def_SubmodMFG_Supplement_SingularCommon
-- name    : SubmodMFG_Supplement_SingularCommon
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:21:34.130188+00:00
-- url     : https://prove2.me/theorems/bffd7eb0-2933-4531-acb0-d7518e502759
-- title:
--   Costs and Brownian motion of §5: Assumption 5.1, extended expectations, Stieltjes integrals
-- statement:
--   1. $E[Y]\in[-\infty,\infty]$ is $E[Y^+]-E[Y^-]$.
--   2. For a nondecreasing right-continuous $F:\mathbb R\to\mathbb R$, $dF$ is its Lebesgue–Stieltjes measure; a control path $\xi$ on $[0,T]$ is extended by $\xi_{0-}=0$, so that $\int_{[0,t]}h\,d\xi$ includes the jump $\xi_0$.
--   3. A **standard $\mathbb F$-Brownian motion on $[0,T]$**: $W_0=0$ a.s., continuous paths a.s., adapted, and for $0\le s\le t\le T$ the increment $W_t-W_s$ is independent of $\mathcal F_s$ with law $N(0,t-s)$.
--   4. **Assumption 5.1** for measurable $f:[0,T]\times\mathbb R\times\mathcal P(\mathbb R)\to\mathbb R$, $g:\mathbb R\times\mathcal P(\mathbb R)\to\mathbb R$, $c:[0,T]\to[0,\infty)$ and an exponent $p>1$: (1) for a.e. $t$, $f(t,\cdot,\mu)$ and $g(\cdot,\mu)$ are lower semicontinuous, and for some $K,\kappa>0$ and all $(t,x,\mu)$,
--   $$\kappa(|x|^p-1)\le f(t,x,\mu)\le K(1+|x|^p),\qquad \kappa(|x|^p-1)\le g(x,\mu)\le K(1+|x|^p);$$
--   (2) for a.e. $t$, $f(t,\cdot,\cdot)$ and $g$ have decreasing differences in $(x,\mu)$: $\varphi(\bar x,\bar\mu)-\varphi(x,\bar\mu)\le\varphi(\bar x,\mu)-\varphi(x,\mu)$ for $\bar x\ge x$, $\bar\mu\ge_{st}\mu$; (3) $c$ is nonincreasing, continuously differentiable and positive.
--   5. "$f$ and $g$ are continuous in $(x,\mu)$": $f(t,x_n,\mu_n)\to f(t,x,\mu)$ and $g(x_n,\mu_n)\to g(x,\mu)$ whenever $x_n\to x$ and $\mu_n\to\mu$ weakly in $\mathcal P(\mathbb R)$.
--
--   **Formalization Note** The costs of §§5–6 can be $+\infty$, so they are extended-real expectations; under Assumption 5.1 the negative part is integrable, so $\infty-\infty$ does not occur. $f$ and $g$ take arguments in $\mathcal M_{\le1}$ and are constrained only on probability measures. Continuity is sequential for the weak topology, which is metrizable (p.9).
-- source:
--   Dianetti, Ferrari, Fischer, Nendel, A Unifying Framework for Submodular Mean Field Games, arXiv:2201.07850v1, §5, pp.15–16 (Assumption 5.1), §5.1.1 p.16, Definition 5.5 (3) p.20

import Mathlib
import Definitions.Def_SubmodMFG_Supplement_SubProb

open MeasureTheory ProbabilityTheory Filter Topology

namespace SubmodMFG.Supplement

/-- A sub-probability measure is a **probability measure**, `µ(ℝ) = 1` (`P(ℝ) ⊂ M≤1`, §3, p.8). -/
def IsProb (μ : SubProb) : Prop := μ.1 Set.univ = 1

/-- **Expectation with values in `[−∞, ∞]`**: `E[Y] = E[Y⁺] − E[Y⁻]` in `EReal`.

**Formalization Note.** Used for the costs of §§5–6, which are expectations that may be `+∞`
(Assumption 5.1 (1) only bounds the integrands from below). Under that bound `E[Y⁻] < ∞`, so the
`∞ − ∞` case (`= ⊥` in `EReal`) does not arise; no integrability hypothesis is needed. -/
noncomputable def erealExpect {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → ℝ) :
    EReal :=
  ((∫⁻ ω, ENNReal.ofReal (Y ω) ∂P : ENNReal) : EReal) -
    ((∫⁻ ω, ENNReal.ofReal (-Y ω) ∂P : ENNReal) : EReal)

/-- **Lebesgue–Stieltjes measure** `dF` of a nondecreasing right-continuous `F : ℝ → ℝ`
(Mathlib's `StieltjesFunction.measure`); `0` for any other `F` (never used: every path to which
it is applied is required to be nondecreasing and right-continuous). -/
noncomputable def stieltjesMeasure (F : ℝ → ℝ) : Measure ℝ :=
  open Classical in
  if h : Monotone F ∧ ∀ x, ContinuousWithinAt F (Set.Ici x) x then
    (StieltjesFunction.mk F h.1 h.2).measure
  else 0

/-- The path `s ↦ ξ_s` on `[0, T]` extended by `ξ_{0−} = 0` for `s < 0` and by `ξ_T` for `s > T`,
so that `∫_{[0,t]} h dξ = ∫_{[0,t]} h d(stieltjesMeasure (pathExt T ξ))` includes the jump `ξ_0`
at time `0` ("X^ξ_{0−} = x0", (5.2), p.16). -/
noncomputable def pathExt (T : ℝ) (ξ : ℝ → ℝ) (s : ℝ) : ℝ :=
  if s < 0 then 0 else ξ (min s T)

/-- **Standard `𝔽`-Brownian motion on `[0, T]`** (Definition 5.5 (3), p.20; §5.1, p.16; §6.1,
p.26): `W_0 = 0` a.s., a.s. continuous paths on `[0, T]`, `W_t` is `𝓕_t`-measurable, and for
`0 ≤ s ≤ t ≤ T` the increment `W_t − W_s` is independent of `𝓕_s` with law `N(0, t − s)`. -/
def IsFBMOn {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (F : Filtration ℝ mΩ) (T : ℝ)
    (W : ℝ → Ω → ℝ) : Prop :=
  (∀ᵐ ω ∂P, W 0 ω = 0) ∧
  (∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) (Set.Icc 0 T)) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) T, Measurable[F t] (W t)) ∧
  (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
    Indep (MeasurableSpace.comap (fun ω => W t ω - W s ω) inferInstance) (F s) P ∧
    P.map (fun ω => W t ω - W s ω) = gaussianReal 0 (t - s).toNNReal)

/-- **Assumption 5.1** (pp.15–16) for measurable `f : [0, T] × ℝ × P(ℝ) → ℝ`, `g : ℝ × P(ℝ) → ℝ`,
`c : [0, T] → [0, ∞)`, with the exponent `p > 1` made explicit: "(1) For dt-a.a. t ∈ [0, T], the
functions f(t, ·, µ) and g(·, µ) are lower semicontinuous and, for some p > 1 and all
(t, x, µ) ∈ [0, T] × ℝ × P(ℝ), κ(|x|^p − 1) ≤ f(t, x, µ) ≤ K(1 + |x|^p), κ(|x|^p − 1) ≤ g(x, µ) ≤
K(1 + |x|^p), with constants K, κ > 0; (2) For dt-a.a. t ∈ [0, T], the functions f(t, ·, ·) and g
have decreasing differences in (x, µ); that is, for φ ∈ {f(t, ·, ·), g}, φ(x̄, µ̄) − φ(x, µ̄) ≤
φ(x̄, µ) − φ(x, µ), for all x̄, x ∈ ℝ and µ̄, µ ∈ P(ℝ) with x̄ ≥ x and µ̄ ≥st µ. (3) The cost c is
nonincreasing and continuously differentiable with c > 0."

**Formalization Note.** `f`, `g` take an argument in `M≤1`; only probability measures (`IsProb`)
are constrained. "For dt-a.a. t" is `∀ᵐ t` for Lebesgue measure on `[0, T]`. In (3), `c` is
nonincreasing, `C¹` and positive on `[0, T]`. Measurability of `f`, `g`, `c` is part of the
statement (p.15: "we take measurable functions"). -/
structure Assumption51 (T p : ℝ) (f : ℝ → ℝ → SubProb → ℝ) (g : ℝ → SubProb → ℝ) (c : ℝ → ℝ) :
    Prop where
  f_meas : Measurable (fun q : ℝ × ℝ × SubProb => f q.1 q.2.1 q.2.2)
  g_meas : Measurable (fun q : ℝ × SubProb => g q.1 q.2)
  c_meas : Measurable c
  p_gt : 1 < p
  lsc : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ μ : SubProb, IsProb μ →
    LowerSemicontinuous (fun x => f t x μ) ∧ LowerSemicontinuous (fun x => g x μ)
  growth : ∃ K κ : ℝ, 0 < K ∧ 0 < κ ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ, ∀ μ : SubProb, IsProb μ →
    κ * (|x| ^ p - 1) ≤ f t x μ ∧ f t x μ ≤ K * (1 + |x| ^ p) ∧
    κ * (|x| ^ p - 1) ≤ g x μ ∧ g x μ ≤ K * (1 + |x| ^ p)
  decr_diff : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ x x' : ℝ, ∀ μ μ' : SubProb,
    IsProb μ → IsProb μ' → x ≤ x' → μ ≤ μ' →
      f t x' μ' - f t x μ' ≤ f t x' μ - f t x μ ∧ g x' μ' - g x μ' ≤ g x' μ - g x μ
  c_anti : AntitoneOn c (Set.Icc 0 T)
  c_C1 : ContDiffOn ℝ 1 c (Set.Icc 0 T)
  c_pos : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 < c t

/-- **"f and g are continuous in (x, µ)"** (Theorems 5.4, 5.9, 6.3): for every `t ∈ [0, T]`,
`(x, µ) ↦ f(t, x, µ)` and `(x, µ) ↦ g(x, µ)` are continuous on `ℝ × P(ℝ)`, written sequentially
for weak convergence (`WeakConv`; the weak topology is metrizable, p.9). -/
def ContInXMu (T : ℝ) (f : ℝ → ℝ → SubProb → ℝ) (g : ℝ → SubProb → ℝ) : Prop :=
  ∀ (x : ℕ → ℝ) (x₀ : ℝ) (μ : ℕ → SubProb) (μ₀ : SubProb), (∀ n, IsProb (μ n)) → IsProb μ₀ →
    Tendsto x atTop (𝓝 x₀) → WeakConv μ μ₀ →
      (∀ t ∈ Set.Icc (0 : ℝ) T, Tendsto (fun n => f t (x n) (μ n)) atTop (𝓝 (f t x₀ μ₀))) ∧
      Tendsto (fun n => g (x n) (μ n)) atTop (𝓝 (g x₀ μ₀))

end SubmodMFG.Supplement


