-- Prove2me | Definitions.Def_MLLangevin_General_Setting
-- name    : MLLangevin_General_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T04:09:27.217996+00:00
-- url     : https://prove2.me/theorems/2cde830d-4e62-4d67-9af2-33b73ab20510
-- title:
--   (7), §2.2–§2.3, (8), (39)–(40), pp. 6–8, 26 — multilevel occupation measure 𝒴, its cost 𝒞(𝒴), assumptions (H₁)–(H₄) and the parameters of Theorem 2.1
-- statement:
--   Fix $x_0\in\mathbb R^d$, a number of correcting levels $R$, a first step $\gamma_0>0$ with $\gamma_r=\gamma_0 2^{-r}$, horizons $(T_r)_{0\le r\le R}$, a warm-start time $\tau$, and Brownian paths $B^{(0)},B^{(1)},\dots$. For $\eta>0$ and $s\ge0$ write $\underline{s}_\eta=\eta\lfloor s/\eta\rfloor$ for the last grid time of step $\eta$ before $s$.
--
--   **The multilevel occupation measure** (7). For a Lipschitz function $f$,
--   $$\mathcal Y(R,(\gamma_r)_r,\tau,(T_r)_r,x_0,f)=\frac1{T_0-\tau}\int_\tau^{T_0} f\big(\bar X^{\gamma_0,x_0,B^{(0)}}_{\underline{s}_{\gamma_0}}\big)\,ds+\sum_{r=1}^R\frac1{T_r-\tau}\int_\tau^{T_r} G^{\gamma_{r-1},B^{(r)}}_s\,ds,$$
--   where, for a step $\gamma>0$ and a path $W$,
--   $$G^{\gamma,W}_s=f\big(\bar X^{\gamma/2,x_0,W}_{\underline{s}_\gamma}\big)-f\big(\bar X^{\gamma,x_0,W}_{\underline{s}_\gamma}\big).$$
--   In level $r\ge1$ the fine scheme (step $\gamma_r$) and the coarse scheme (step $\gamma_{r-1}$) are driven by the same path $B^{(r)}$ and both are read at the coarse grid times. The **complexity** is
--   $$\mathcal C(\mathcal Y)=\frac{T_0}{\gamma_0}+\sum_{r=1}^R\Big(\frac{T_r}{\gamma_r}+\frac{T_r}{\gamma_{r-1}}\Big).$$
--
--   **Assumptions** (for one driving path $W$, a function $f$, $\eta_0>0$, $\alpha>0$, $\mathfrak a\in[1,2]$, and families of measures $\pi$, $\pi^\gamma$; $\|Z\|_2=\mathbb E[|Z|^2]^{1/2}$):
--   1. $(\mathbf H_1)$: for all $x$, $\gamma\in(0,\eta_0]$ and $n\in\mathbb N$, $\big|\mathbb E[f(\bar X^{\gamma,x}_{n\gamma})]-\pi^\gamma(f)\big|\le c_1(x)[f]_1e^{-\alpha n\gamma}$.
--   2. $(\mathbf H_2)$: $c_2>0$ and for all $\gamma\in(0,\eta_0]$, $n\in\mathbb N$, $\|\bar X^{\gamma,x_0}_{n\gamma}-\bar X^{\gamma/2,x_0}_{n\gamma}\|_2\le c_2\gamma^{\mathfrak a/2}$.
--   3. $(\mathbf H_3)$: $c_3>0$, $\delta\in[1/2,1]$ if $\mathfrak a=1$ and $\delta\in((1+\mathfrak a)/4,1]$ if $\mathfrak a>1$, and $|\pi(f)-\pi^\gamma(f)|\le c_3[f]_1\gamma^\delta$ for all $\gamma\in(0,\eta_0]$.
--   4. $(\mathbf H_4)$: $c_4\ge0$ and for all $\gamma\in(0,\eta_0]$, $n\in\mathbb N$, $\|\bar X^{\gamma,x_0}_{n\gamma}-x_0\|_2+\|c_1(\bar X^{\gamma,x_0}_{n\gamma})\|_2\le c_4$.
--
--   **Parameters.** $T_r=T_02^{-\frac{1+\mathfrak a}2r}$ (Propositions 3.1–3.3); the schedule (8): $R_\varepsilon=\lceil\delta^{-1}\log_2(r_0\varepsilon^{-1})\rceil$ and $T_r=\mathfrak t\varepsilon^{-2}2^{-\frac{1+\mathfrak a}2r}$ if $\mathfrak a>1$, $T_r=\mathfrak t\varepsilon^{-2}R_\varepsilon^22^{-r}$ if $\mathfrak a=1$; the constants
--   $$\mathfrak c_{\mathfrak a}=\begin{cases}1+\tfrac32\big(2^{\frac{\mathfrak a-1}2}-1\big)^{-1}&\mathfrak a>1\\ \tfrac52&\mathfrak a=1\end{cases},\qquad \mathfrak d_{\mathfrak a}=\begin{cases}(\mathfrak a-1)^{-2}&\mathfrak a>1\\ 1&\mathfrak a=1\end{cases},$$
--   $(\mathfrak a-1)^{-2}\wedge R^2$ (equal to $R^2$ when $\mathfrak a=1$), and from (39)–(40)
--   $$\mathfrak t_0=\frac{\mathfrak d_{\mathfrak a}}\alpha\max\big(c_2^2\gamma_0^{\mathfrak a}\log(\gamma_0^{-1}),c_4^2\big),\quad \tau_1=\frac{1+\mathfrak a-2\delta}{\alpha\delta},\quad \tau_2=0\vee\frac1\alpha\log\Big(r_0^{\frac{1+\mathfrak a}{2\delta}}(\mathfrak d_{\mathfrak a}c_4)^{-1}\Big).$$
--
--   These are the objects of Theorem 2.1 and of the propositions of §3 that prove it.
--
--   **Formalization Note.** Level $r$ uses the path `B r`; `levelTerm … 0` is the level-0 average and `levelTerm … (r+1)` the correcting term of level $r+1$, and `estimator` is their sum over $r\le R$. $\|\cdot\|_2$ is `eLpNorm · 2 P` in $[0,\infty]$, so an infinite second moment is never read as $0$. The assumptions are stated at grid times $n\gamma$; for $(\mathbf H_4)$ the paper takes a supremum over all $t\ge0$ of the continuous-time scheme, so the grid-time version is a weaker assumption and the theorems that use it are stronger. The cost formula of p. 6 is given there for horizons that are multiples of the steps; it is used as the definition of $\mathcal C(\mathcal Y)$ for all horizons. At $c_4=0$ Lean's $0^{-1}=0$ makes $\tau_2=0$ (the paper's value is $+\infty$); this only enlarges the set of admissible $\tau$, and in that case $(\mathbf H_4)$ forces $c_1(x_0)=0$, so the bias term that $\tau_2$ controls vanishes.
-- source:
--   Egéa–Panloup, arXiv:2109.07753v2, (7) and the complexity, §2.2, p. 6; (H₁)–(H₄), §2.3, pp. 6–7; (8) and 𝔠_𝔞, Theorem 2.1, pp. 7–8; G^γ_s, p. 23; Remark 3.3, p. 25; (39)–(40), p. 26

import Mathlib
import Definitions.Def_MLLangevin_General_EulerChain

namespace MLLangevin.General

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-! ### The multilevel occupation measure (7) and its cost, §2.2, p. 6 -/

/-- `G^γ_s = f(X̄^{γ/2,x₀}_{s̲_γ}) − f(X̄^{γ,x₀}_{s̲_γ})` (p. 23), both schemes driven by the same
path `W` and read at the coarse grid time `s̲_γ = γ⌊s/γ⌋` (step `2⌊s/γ⌋` of the fine scheme). -/
noncomputable def Gproc {d : ℕ} {Ω : Type*} (b : Rd d → Rd d) (σ : Rd d → (Rd d →L[ℝ] Rd d))
    (f : Rd d → ℝ) (γ : ℝ) (x₀ : Rd d) (W : ℝ≥0 → Ω → Rd d) (s : ℝ) (ω : Ω) : ℝ :=
  f (eulerChain b σ (γ / 2) x₀ W (2 * ⌊s / γ⌋₊) ω) - f (eulerChain b σ γ x₀ W ⌊s / γ⌋₊ ω)

/-- The level terms of (7): level `0` is `(T₀ − τ)⁻¹ ∫_τ^{T₀} f(X̄^{γ₀,x₀,B^{(0)}}_{s̲_{γ₀}}) ds`;
level `r + 1` is `(T_{r+1} − τ)⁻¹ ∫_τ^{T_{r+1}} G^{γ_r}_s ds` driven by `B^{(r+1)}`. -/
noncomputable def levelTerm {d : ℕ} {Ω : Type*} (b : Rd d → Rd d)
    (σ : Rd d → (Rd d →L[ℝ] Rd d)) (x₀ : Rd d) (γ₀ τ : ℝ) (T : ℕ → ℝ)
    (B : ℕ → ℝ≥0 → Ω → Rd d) (f : Rd d → ℝ) : ℕ → Ω → ℝ
  | 0 => fun ω => (T 0 - τ)⁻¹ * ∫ s in τ..T 0, f (eulerChain b σ γ₀ x₀ (B 0) ⌊s / γ₀⌋₊ ω)
  | r + 1 => fun ω =>
      (T (r + 1) - τ)⁻¹ * ∫ s in τ..T (r + 1), Gproc b σ f (levelStep γ₀ r) x₀ (B (r + 1)) s ω

/-- The multilevel occupation measure `𝒴(R, (γ_r)_r, τ, (T_r)_r, x₀, f)` of (7), with steps
`γ_r = γ₀ 2^{−r}` and level `r` driven by `B r`. -/
noncomputable def estimator {d : ℕ} {Ω : Type*} (b : Rd d → Rd d)
    (σ : Rd d → (Rd d →L[ℝ] Rd d)) (x₀ : Rd d) (γ₀ : ℝ) (R : ℕ) (τ : ℝ) (T : ℕ → ℝ)
    (B : ℕ → ℝ≥0 → Ω → Rd d) (f : Rd d → ℝ) (ω : Ω) : ℝ :=
  ∑ r ∈ Finset.range (R + 1), levelTerm b σ x₀ γ₀ τ T B f r ω

/-- The complexity `𝒞(𝒴) = T₀/γ₀ + Σ_{r=1}^R (T_r/γ_r + T_r/γ_{r−1})` (p. 6). -/
noncomputable def cost (R : ℕ) (γ₀ : ℝ) (T : ℕ → ℝ) : ℝ :=
  T 0 / γ₀ + ∑ r ∈ Finset.Icc 1 R, (T r / levelStep γ₀ r + T r / levelStep γ₀ (r - 1))

/-! ### Assumptions (H₁)–(H₄), §2.3, pp. 6–7 (for one driving Brownian path `W`) -/

/-- (H₁) convergence to equilibrium, at the grid times `t̲_γ = nγ`. -/
def H1 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (b : Rd d → Rd d)
    (σ : Rd d → (Rd d →L[ℝ] Rd d)) (W : ℝ≥0 → Ω → Rd d) (f : Rd d → ℝ)
    (πγ : ℝ → Measure (Rd d)) (α η₀ : ℝ) (c₁ : Rd d → ℝ) : Prop :=
  ∀ x : Rd d, ∀ γ ∈ Set.Ioc (0 : ℝ) η₀, ∀ n : ℕ,
    |∫ ω, f (eulerChain b σ γ x W n ω) ∂P - ∫ y, f y ∂(πγ γ)|
      ≤ c₁ x * lipConst f * Real.exp (-α * ((n : ℝ) * γ))

/-- (H₂) `L²`-confluence: `‖X̄^{γ,x₀}_{nγ} − X̄^{γ/2,x₀}_{nγ}‖₂ ≤ c₂ γ^{𝔞/2}`, `c₂ > 0`. -/
def H2 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (b : Rd d → Rd d)
    (σ : Rd d → (Rd d →L[ℝ] Rd d)) (W : ℝ≥0 → Ω → Rd d) (x₀ : Rd d) (η₀ 𝔞 c₂ : ℝ) : Prop :=
  0 < c₂ ∧ ∀ γ ∈ Set.Ioc (0 : ℝ) η₀, ∀ n : ℕ,
    eLpNorm (fun ω => eulerChain b σ γ x₀ W n ω - eulerChain b σ (γ / 2) x₀ W (2 * n) ω) 2 P
      ≤ ENNReal.ofReal (c₂ * γ ^ (𝔞 / 2))

/-- The range of `δ` in (H₃): `δ ∈ [1/2, 1]` if `𝔞 = 1` and `δ ∈ ((1+𝔞)/4, 1]` if `𝔞 > 1`. -/
def DeltaRange (𝔞 δ : ℝ) : Prop :=
  (𝔞 = 1 → 1 / 2 ≤ δ ∧ δ ≤ 1) ∧ (1 < 𝔞 → (1 + 𝔞) / 4 < δ ∧ δ ≤ 1)

/-- (H₃) weak error between the invariant distributions: `|π(f) − π^γ(f)| ≤ c₃ [f]₁ γ^δ`,
`c₃ > 0`, with `δ` in the range of `DeltaRange`. -/
def H3 {d : ℕ} (f : Rd d → ℝ) (π : Measure (Rd d)) (πγ : ℝ → Measure (Rd d))
    (η₀ 𝔞 δ c₃ : ℝ) : Prop :=
  0 < c₃ ∧ DeltaRange 𝔞 δ ∧ ∀ γ ∈ Set.Ioc (0 : ℝ) η₀,
    |∫ y, f y ∂π - ∫ y, f y ∂(πγ γ)| ≤ c₃ * lipConst f * γ ^ δ

/-- (H₄) moment control at the grid times:
`‖X̄^{γ,x₀}_{nγ} − x₀‖₂ + ‖c₁(X̄^{γ,x₀}_{nγ})‖₂ ≤ c₄`, `c₄ ≥ 0`. -/
def H4 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (b : Rd d → Rd d)
    (σ : Rd d → (Rd d →L[ℝ] Rd d)) (W : ℝ≥0 → Ω → Rd d) (x₀ : Rd d) (η₀ : ℝ)
    (c₁ : Rd d → ℝ) (c₄ : ℝ) : Prop :=
  0 ≤ c₄ ∧ ∀ γ ∈ Set.Ioc (0 : ℝ) η₀, ∀ n : ℕ,
    eLpNorm (fun ω => eulerChain b σ γ x₀ W n ω - x₀) 2 P
        + eLpNorm (fun ω => c₁ (eulerChain b σ γ x₀ W n ω)) 2 P
      ≤ ENNReal.ofReal c₄

/-! ### Parameters and constants: (8), Theorem 2.1, Proposition 3.1, (39)–(40) -/

/-- `T_r = T₀ 2^{−((1+𝔞)/2) r}` (Propositions 3.1–3.3). -/
noncomputable def geomHorizon (T₀ 𝔞 : ℝ) (r : ℕ) : ℝ := T₀ * (2 : ℝ) ^ (-((1 + 𝔞) / 2) * (r : ℝ))

/-- `R_ε = ⌈δ⁻¹ log₂(r₀ ε⁻¹)⌉` of (8). -/
noncomputable def Reps (r₀ δ ε : ℝ) : ℕ := ⌈Real.logb 2 (r₀ / ε) / δ⌉₊

/-- `T_r` of (8): `𝔱 ε⁻² 2^{−((1+𝔞)/2) r}` if `𝔞 > 1`, `𝔱 ε⁻² R² 2^{−r}` if `𝔞 = 1`. -/
noncomputable def Tsched (𝔞 𝔱 ε : ℝ) (R : ℕ) (r : ℕ) : ℝ :=
  if 1 < 𝔞 then 𝔱 * ε⁻¹ ^ 2 * (2 : ℝ) ^ (-((1 + 𝔞) / 2) * (r : ℝ))
  else 𝔱 * ε⁻¹ ^ 2 * (R : ℝ) ^ 2 * (2 : ℝ) ^ (-(r : ℝ))

/-- `𝔠_𝔞 = 1 + (3/2)(2^{(𝔞−1)/2} − 1)⁻¹` if `𝔞 > 1`, `5/2` if `𝔞 = 1` (Theorem 2.1). -/
noncomputable def ca (𝔞 : ℝ) : ℝ :=
  if 1 < 𝔞 then 1 + 3 / 2 * ((2 : ℝ) ^ ((𝔞 - 1) / 2) - 1)⁻¹ else 5 / 2

/-- `𝔡_𝔞 = (𝔞 − 1)^{−2}` if `𝔞 > 1`, `1` if `𝔞 = 1` (39). -/
noncomputable def da (𝔞 : ℝ) : ℝ := if 1 < 𝔞 then ((𝔞 - 1) ^ 2)⁻¹ else 1

/-- `(𝔞 − 1)^{−2} ∧ R²`, equal to `R²` when `𝔞 = 1` (Remark 3.3). -/
noncomputable def minTerm (𝔞 : ℝ) (R : ℕ) : ℝ :=
  if 𝔞 = 1 then (R : ℝ) ^ 2 else min (((𝔞 - 1) ^ 2)⁻¹) ((R : ℝ) ^ 2)

/-- `𝔱₀ = (𝔡_𝔞/α) max(c₂² γ₀^𝔞 log(γ₀⁻¹), c₄²)` (39). -/
noncomputable def t0 (𝔞 α c₂ c₄ γ₀ : ℝ) : ℝ :=
  da 𝔞 / α * max (c₂ ^ 2 * γ₀ ^ 𝔞 * Real.log γ₀⁻¹) (c₄ ^ 2)

/-- `τ₁ = (1 + 𝔞 − 2δ)/(αδ)` (40). -/
noncomputable def tau1 (𝔞 α δ : ℝ) : ℝ := (1 + 𝔞 - 2 * δ) / (α * δ)

/-- `τ₂ = 0 ∨ α⁻¹ log(r₀^{(1+𝔞)/(2δ)} (𝔡_𝔞 c₄)⁻¹)` (40). -/
noncomputable def tau2 (𝔞 α δ r₀ c₄ : ℝ) : ℝ :=
  max 0 (α⁻¹ * Real.log (r₀ ^ ((1 + 𝔞) / (2 * δ)) * (da 𝔞 * c₄)⁻¹))

end MLLangevin.General


