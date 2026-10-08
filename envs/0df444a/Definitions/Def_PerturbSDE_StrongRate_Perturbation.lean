-- Prove2me | Definitions.Def_PerturbSDE_StrongRate_Perturbation
-- name    : PerturbSDE_StrongRate_Perturbation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T17:08:05.993509+00:00
-- url     : https://prove2.me/theorems/d5081115-9cc0-45f7-876a-242da4bfbcd9
-- title:
--   §2 — the monotonicity ratio, exp(∫₀^τ[·]⁺ds) in [0,∞], the stochastic interval ⟦0,τ⟧, the local error of (43)
-- statement:
--   This file names the quantities appearing in the perturbation estimates of Hutzenthaler and Jentzen (arXiv:1401.0295v1, §2.4, pp. 11–15, and Lemma 3.2, p. 17), specialised to $H=\mathbb R^d$, $U=\mathbb R^m$.
--
--   1. **Monotonicity ratio.** For $\mu:\mathbb R^d\to\mathbb R^d$, $\sigma:\mathbb R^d\to\mathbb R^{d\times m}$, $p\in[2,\infty)$, $\varepsilon\in[0,\infty]$ and $x,y\in\mathbb R^d$,
--   $$R_{p,\varepsilon}(x,y)=\frac{\langle x-y,\mu(x)-\mu(y)\rangle+\frac{(p-1)(1+\varepsilon)}{2}\|\sigma(x)-\sigma(y)\|^2_{HS(\mathbb R^m,\mathbb R^d)}}{\|x-y\|^2}\in(-\infty,\infty],$$
--   evaluated with the paper's conventions $0\cdot\infty=0$ and $0/0=0$ (p. 6).
--   2. **Exponential moment integrand.** For an integrand $g$ with values in $[-\infty,\infty]$ and a random time $\tau$, $\exp\big(\int_0^{\tau}[g_s]^+\,ds\big)\in[0,\infty]$, with $\exp(\infty)=\infty$.
--   3. **Stochastic interval** $[\![0,\tau]\!]=\{(t,\omega):0\le t\le\tau(\omega)\}$, carrying the restriction of $\lambda\otimes\mathbb P$; $L^p([\![0,\tau]\!];E)$ norms are taken with respect to it.
--   4. **Local error of Theorem 2.10.** For processes $X,Y,a,b,\chi$,
--   $$p\,\|X_s-Y_s\|^{p-2}\Big[\langle X_s-Y_s,\mu(Y_s)-a_s\rangle+\tfrac{(p-1)(1+1/\varepsilon)}{2}\|b_s-\sigma(Y_s)\|^2_{HS}-\chi_s\|X_s-Y_s\|^2\Big]^+\in[0,\infty].$$
--   5. **Discount factor** $\exp\big(\int_0^s\chi_u\,du\big)$.
--
--   These are the building blocks of (33), (42), (43), (56) and (64).
--
--   **Formalization Note** The ratio is computed in `EReal`, where $\top\cdot 0=0$ and $x/0=0$; its numerator vanishes when $x=y$, which gives the paper's $0/0=0$. Positive parts are taken by mapping to $[0,\infty]$ (`EReal.toENNReal`), time integrals are Lebesgue integrals in $[0,\infty]$, and the exponential is extended by $\exp(\infty)=\infty$, so no Bochner default value can make an exponential moment look finite. Time is indexed by $\mathbb R$ in the integrals and converted to $\mathbb R_{\ge0}$ for the processes.
-- source:
--   Hutzenthaler, Jentzen, arXiv:1401.0295v1, pp. 4, 6, 11, 13, 15, 17: (33), (42), (43), (56), (64); conventions 0/0 := 0, 0·∞ := 0, p. 6

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace PerturbSDE.StrongRate

open EthierKurtz SabanisEuler.Shared

/-- The exponential on `[0, ∞]`, with `exp(∞) = ∞`. -/
noncomputable def ennExp (x : ℝ≥0∞) : ℝ≥0∞ :=
  if x = ⊤ then ⊤ else ENNReal.ofReal (Real.exp x.toReal)

/-- The monotonicity ratio of Hutzenthaler–Jentzen, (42), (56), (64):
`[⟨x − y, µ(x) − µ(y)⟩ + ((p − 1)(1 + ε)/2) ‖σ(x) − σ(y)‖²_{HS}] / ‖x − y‖²`,
for `ε ∈ [0, ∞]`, evaluated in `[−∞, ∞]` with the paper's conventions `0 · ∞ = 0` and
`0 / 0 = 0` (in `EReal`, `⊤ * 0 = 0` and `x / 0 = 0`; the numerator vanishes when `x = y`). -/
noncomputable def monoRatio {d m : ℕ} (mu : SDEState d → SDEState d)
    (sigma : SDEState d → Diffusion d m) (p : ℝ) (ε : ℝ≥0∞) (x y : SDEState d) : EReal :=
  (((inner ℝ (x - y) (mu x - mu y) : ℝ) : EReal) +
      (((p - 1) / 2 : ℝ) : EReal) * ((1 + ε : ℝ≥0∞) : EReal) *
        ((‖sigma x - sigma y‖ ^ 2 : ℝ) : EReal)) /
    ((‖x - y‖ ^ 2 : ℝ) : EReal)

/-- `exp(∫_0^{τ(ω)} [g_s(ω)]^+ ds) ∈ [0, ∞]` for an `[−∞, ∞]`-valued integrand `g`: the positive
part is taken in `[0, ∞]`, the integral is a Lebesgue integral in `[0, ∞]`, and `exp(∞) = ∞`. -/
noncomputable def expPosIntegral {Ω : Type*} (g : ℝ≥0 → Ω → EReal) (τ : Ω → ℝ≥0) (ω : Ω) :
    ℝ≥0∞ :=
  ennExp (∫⁻ s in Set.Icc (0 : ℝ) (τ ω), (g s.toNNReal ω).toENNReal)

/-- The stochastic interval `⟦0, τ⟧ = {(t, ω) : 0 ≤ t ≤ τ(ω)}` in `ℝ × Ω`. -/
def stochInterval {Ω : Type*} (τ : Ω → ℝ≥0) : Set (ℝ × Ω) :=
  {z | 0 ≤ z.1 ∧ z.1 ≤ τ z.2}

/-- The measure `λ ⊗ P` restricted to `⟦0, τ⟧`; `L^p(⟦0, τ⟧; E)` norms are `eLpNorm` for this
measure of the map `(t, ω) ↦ F_t(ω)`. -/
noncomputable def onStochInterval {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (τ : Ω → ℝ≥0) : Measure (ℝ × Ω) :=
  ((volume : Measure ℝ).prod P).restrict (stochInterval τ)

/-- The local-error integrand of Theorem 2.10, (43):
`p ‖X − Y‖^{p−2} [⟨X − Y, µ(Y) − a⟩ + ((p − 1)(1 + 1/ε)/2) ‖b − σ(Y)‖²_{HS} − χ ‖X − Y‖²]^+`
at time `s` and outcome `ω`, in `[0, ∞]` (with `1/0 = ∞`, `0 · ∞ = 0`, and `0^0 = 1`). -/
noncomputable def localError {d m : ℕ} {Ω : Type*} (mu : SDEState d → SDEState d)
    (sigma : SDEState d → Diffusion d m) (p : ℝ) (ε : ℝ≥0∞)
    (X Y a : ℝ≥0 → Ω → SDEState d) (b : ℝ≥0 → Ω → Diffusion d m) (χ : ℝ≥0 → Ω → ℝ)
    (s : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (p * ‖X s ω - Y s ω‖ ^ (p - 2)) *
    ((((inner ℝ (X s ω - Y s ω) (mu (Y s ω) - a s ω) - χ s ω * ‖X s ω - Y s ω‖ ^ 2 : ℝ) :
        EReal) +
      (((p - 1) / 2 : ℝ) : EReal) * ((1 + ε⁻¹ : ℝ≥0∞) : EReal) *
        ((‖b s ω - sigma (Y s ω)‖ ^ 2 : ℝ) : EReal)).toENNReal)

/-- The discount factor `exp(∫_0^s χ_u du)` of Propositions 2.5 and 2.9, a pathwise interval
integral. -/
noncomputable def discount {Ω : Type*} (χ : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (∫ u in (0 : ℝ)..(s : ℝ), χ u.toNNReal ω)

end PerturbSDE.StrongRate


