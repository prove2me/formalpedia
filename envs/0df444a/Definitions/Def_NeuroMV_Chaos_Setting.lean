-- Prove2me | Definitions.Def_NeuroMV_Chaos_Setting
-- name    : NeuroMV_Chaos_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T14:41:12.992529+00:00
-- url     : https://prove2.me/theorems/866ba29c-233f-4e7e-8c74-9adbaf9a5c29
-- title:
--   §1, pp. 2–5 — coefficients, Hypothesis 1.1 (H1)–(H5), path segments, noise, strong solutions of (6) and the L∞–L² class
-- statement:
--   This module sets up the McKean–Vlasov delay equation with jumps of Mehri, Scheutzow, Stannat and Zangeneh.
--
--   **Data.** Fix dimensions $d$ (state), $m$, $n$ (noise), $k$ (space) and $P$ subpopulations, indexed $\alpha = 0,\dots,P-1$. The *geometry* consists of a delay $\tau$, measurable, pairwise disjoint regions $\Gamma_\alpha \subset \mathbb R^k$ with bounded union $\Gamma = \bigcup_\alpha \Gamma_\alpha$, and a finite Borel measure $\mathcal R$ carried by $\Gamma$ with $\mathcal R(\Gamma_\alpha) = 1$; it is *valid* when moreover $\tau > 0$. The *coefficients* are maps
--   $$f, g, h : [0,\infty)\times\mathbb R^k\times\mathbb R^d\times\Omega'(\times U) \to \mathbb R^d, \mathbb R^{d\times m}, \mathbb R^d, \qquad \theta, \beta, \eta : [0,\infty)\times\mathbb R^k\times\mathbb R^k\times\mathbb R^d\times(\mathbb R\to\mathbb R^d)\times\Omega'(\times U)\to \mathbb R^d, \mathbb R^{d\times n}, \mathbb R^d,$$
--   where $\omega' \in \Omega'$ is the disorder, $\xi\in U$ a mark, and the path argument $y$ is read on $[-\tau,0]$. They are *regular* when jointly measurable and continuous in $x \in \mathbb R^d$. For a matrix, $|A|^2 = \sum_{ij} A_{ij}^2$ (Hilbert–Schmidt).
--
--   **Hypothesis 1.1, (H1)–(H5).** There are a probability measure $\lambda$ on $[-\tau,0]$ and nonnegative, jointly measurable rates $K, L, \bar K, \bar L$, $\tilde K(R)$, locally integrable in time for every $\omega'$, such that for all positions $r, r' \in \Gamma$: (H1) $2\langle x-\tilde x, f(t,r,x)-f(t,r,\tilde x)\rangle + |g(t,r,x)-g(t,r,\tilde x)|^2 + \int_U |h(t,r,x,\xi)-h(t,r,\tilde x,\xi)|^2\nu(d\xi) \le L_t|x-\tilde x|^2$; (H2) $2\langle x, f(t,r,x)\rangle + |g(t,r,x)|^2 + \int_U |h(t,r,x,\xi)|^2\nu(d\xi) \le K_t(1+|x|^2)$; (H3) $\sup_{|x|\le R}[|f|+|g|^2+\int_U|h|^2 d\nu] \le \tilde K_t(R)$; and for càglàd paths $y, \tilde y$ on $[-\tau,0]$,
--   $$\textstyle\sum_{\Theta\in\{\theta,\beta\}}|\Theta(t,r,r',x,y)-\Theta(t,r,r',\tilde x,\tilde y)|^2+\int_U|\eta(\dots,\xi)-\eta(\dots,\xi)|^2\nu(d\xi)\le \bar L_t\Big[|x-\tilde x|^2+\int_{-\tau}^0\big(|y_s-\tilde y_s|^2+1_{s<0}|y_{s+}-\tilde y_{s+}|^2\big)\lambda(ds)\Big]$$
--   (H4), and the growth bound (H5) with $\bar K_t[1+|x|^2+\int_{-\tau}^0(|y_s|^2+1_{s<0}|y_{s+}|^2)\lambda(ds)]$ (all for every $t$ and $\omega'$).
--
--   **Noise and solutions.** On a filtered probability space, the noise of (6) is an $m$-dimensional and $P$ $n$-dimensional standard Brownian motions $W, B^\alpha$ whose coordinates form one jointly independent $(\mathcal F_t)$-Brownian family, and independent $(\mathcal F_t)$-Poisson random measures $N, N^\alpha$ with intensity $dt\otimes\nu$, packed as one Poisson measure on a product mark space. Initial conditions $\hat z^\alpha$ are càdlàg, $\mathcal F_0$-measurable, with $\mathbb E\sup_{u\in[-\tau,0]}|\hat z^\alpha_u|^2<\infty$. A process $X = (X^r)_{r\in\Gamma}$ is a *strong solution of (6)* on $[-\tau,T]$ at the disorder $\omega'$ if $(r,\omega)\mapsto X^r_t(\omega)$ is measurable and for $r\in\Gamma_\zeta$, $X^r = \hat z^\zeta$ on $[-\tau,0]$, $X^r$ is càdlàg and adapted, and
--   $$dX^r_t = f(t,r,X^r_{t-})dt + g\,dW_t + \int_U h\,\tilde N(dt,d\xi) + \sum_\alpha\int_{\Gamma_\alpha}\tilde{\mathbb E}\big[\theta(t,r,r',X^r_{t-},\tilde X^{r'}_{(t-\tau)^-:t^-})\big]\mathcal R(dr')dt + (\beta\text{-term})\,dB^\alpha_t + (\eta\text{-term})\,\tilde N^\alpha(dt,d\xi).$$
--   The class $L^\infty([-\tau,T];L^2(\Omega\times\Gamma,\mathbb P\otimes\mathcal R))$ asks $\sup_{t\in[-\tau,T]}\int_\Gamma\mathbb E|X^r_t|^2\mathcal R(dr)<\infty$.
--
--   These objects are the shared substrate of the propagation-of-chaos statements of §1.2 and §3.
--
--   **Formalization Note.** Stochastic integrals are the published predicates `EthierKurtz.HasBrownianItoIntegral` (per scalar coordinate) and `JacodTodorov10.LLN.HasCompInt` (per coordinate, against the atoms of one mark), with every integrand cut off after $T$; the drift integral is a pathwise interval integral with an integrability clause. The copy $\tilde X$ enters only through its law, so the mean-field terms are expectations over the solution's own probability space. The path argument carries the product σ-algebra (a mild strengthening of the paper's sup-norm Borel measurability). On $(-\infty,0]$ a solution equals $\hat z^\zeta_{\max(t,-\tau)}$ (the initial segment extended constantly below $-\tau$, which only fixes the left limit at $-\tau$). The class is a bound for every $t$ rather than for a.e. $t$. Subpopulations are 0-based (`Fin P`).
-- source:
--   Mehri, Scheutzow, Stannat, Zangeneh, Propagation of Chaos for Stochastic Spatially Structured Neuronal Networks with Delay driven by Jump Diffusions, arXiv:1805.01654v3, §1, pp. 2–5, (6), Hypothesis 1.1 (H1)–(H5); Theorem 1.5, p. 7 (the class); Appendix A, p. 21 (filtration)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_JacodTodorov10_LLN_Noise
import Definitions.Def_NeuroMV_WellPosed_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace NeuroMV.Chaos

/-! ### Spaces, paths and norms (§1, p. 2) -/

/-- The mark set `{N} ∪ {N^α : α}` of the Poisson measures of one neuron is discrete. -/
instance instMeasurableSpaceOptionFin (P : ℕ) : MeasurableSpace (Option (Fin P)) := ⊤

/-- The squared Hilbert–Schmidt (Frobenius) norm `|A|² = Σᵢⱼ Aᵢⱼ²` of a `d × m` matrix
(the paper's `|g|²`, `|β|²`). -/
def frob2 {d m : ℕ} (A : Matrix (Fin d) (Fin m) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j ^ 2

/-- `y` is càdlàg on `[a, b]`: right-continuous at every `t ∈ [a, b)` (within `[t, b]`) with a
left limit at every `t ∈ (a, b]`. -/
def IsCadlagOn {E : Type*} [TopologicalSpace E] (a b : ℝ) (y : ℝ → E) : Prop :=
  (∀ t ∈ Set.Ico a b, ContinuousWithinAt y (Set.Icc t b) t) ∧
    ∀ t ∈ Set.Ioc a b, ∃ l : E, Tendsto y (𝓝[<] t) (𝓝 l)

/-- `y` is càglàd on `[-τ, 0]` (an element of `Càglàd([-τ, 0]; ℝᵈ)`, read on `[-τ, 0]`):
left-continuous at every `s ∈ (-τ, 0]` (within `[-τ, s]`) with a right limit at every
`s ∈ [-τ, 0)`. -/
def IsCagladOn {E : Type*} [TopologicalSpace E] (τ : ℝ) (y : ℝ → E) : Prop :=
  (∀ s ∈ Set.Ioc (-τ) 0, ContinuousWithinAt y (Set.Icc (-τ) s) s) ∧
    ∀ s ∈ Set.Ico (-τ) 0, ∃ l : E, Tendsto y (𝓝[>] s) (𝓝 l)

/-- The left limit `Y_{t−}(ω)` of a process `Y` (Mathlib's `Function.leftLim`). -/
noncomputable def lft {Ω E : Type*} [TopologicalSpace E] (Y : ℝ → Ω → E) (t : ℝ) (ω : Ω) : E :=
  Function.leftLim (fun v => Y v ω) t

/-- The path segment `Y_{(t−τ)⁻:t⁻}(ω)`: the càglàd path `u ↦ Y_{(t+u)−}(ω)`, read on
`u ∈ [-τ, 0]` (p. 2). -/
noncomputable def seg {Ω E : Type*} [TopologicalSpace E] (Y : ℝ → Ω → E) (t : ℝ) (ω : Ω) :
    ℝ → E :=
  fun u => lft Y (t + u) ω

/-- `∫_{-τ}^0 (|y_s − ỹ_s|² + 1_{s<0} |y_{s+} − ỹ_{s+}|²) λ(ds)` in `[0, ∞]` (Hypothesis 1.1,
(H4)–(H5)); `y_{s+}` is the right limit. With `ỹ = 0` it is
`∫_{-τ}^0 (|y_s|² + 1_{s<0} |y_{s+}|²) λ(ds)`. -/
noncomputable def lamDist2 {d : ℕ} (lam : Measure ℝ) (y y' : ℝ → EthierKurtz.SDEState d) :
    ℝ≥0∞ :=
  ∫⁻ s, (‖y s - y' s‖ₑ ^ 2 +
    (Set.Iio (0 : ℝ)).indicator
      (fun s => ‖Function.rightLim y s - Function.rightLim y' s‖ₑ ^ 2) s) ∂lam

/-! ### The data of the model (§1, pp. 2–5) -/

/-- The spatial data: the delay `τ`, the subpopulation regions `Γ_α ⊂ ℝᵏ` (`α : Fin P`,
0-based) and the finite Borel measure `𝓡` of (5)–(6). -/
structure Geometry (k P : ℕ) where
  τ : ℝ
  Γα : Fin P → Set (NeuroMV.WellPosed.Pos k)
  𝓡 : Measure (NeuroMV.WellPosed.Pos k)

/-- `Γ = ⋃_α Γ_α`. -/
def Geometry.Γ {k P : ℕ} (G : Geometry k P) : Set (NeuroMV.WellPosed.Pos k) :=
  ⋃ α, G.Γα α

/-- The standing assumptions on the spatial data (pp. 2, 5): `τ > 0`; the `Γ_α` are measurable
and pairwise disjoint and `Γ` is bounded; `𝓡` is a finite measure on `Γ` with `𝓡(Γ_α) = 1`. -/
def Geometry.Valid {k P : ℕ} (G : Geometry k P) : Prop :=
  0 < G.τ ∧ (∀ α, MeasurableSet (G.Γα α)) ∧ Pairwise (Function.onFun Disjoint G.Γα) ∧
    Bornology.IsBounded G.Γ ∧ IsFiniteMeasure G.𝓡 ∧ G.𝓡 G.Γᶜ = 0 ∧ ∀ α, G.𝓡 (G.Γα α) = 1

/-- The coefficients of (1), (5), (6) (p. 2), with time in `[0, ∞)`, positions in `ℝᵏ`, the
disorder `ω' ∈ Ω'` and marks `ξ ∈ U`. The path argument of `θ, β, η` is a function `ℝ → ℝᵈ`
read on `[-τ, 0]`. -/
structure Coeffs (d m n k P : ℕ) (U Ω' : Type*) where
  f : ℝ≥0 → NeuroMV.WellPosed.Pos k → EthierKurtz.SDEState d → Ω' → EthierKurtz.SDEState d
  g : ℝ≥0 → NeuroMV.WellPosed.Pos k → EthierKurtz.SDEState d → Ω' → Matrix (Fin d) (Fin m) ℝ
  h : ℝ≥0 → NeuroMV.WellPosed.Pos k → EthierKurtz.SDEState d → Ω' → U → EthierKurtz.SDEState d
  θ : ℝ≥0 → NeuroMV.WellPosed.Pos k → NeuroMV.WellPosed.Pos k → EthierKurtz.SDEState d → (ℝ → EthierKurtz.SDEState d) → Ω' →
    EthierKurtz.SDEState d
  β : ℝ≥0 → NeuroMV.WellPosed.Pos k → NeuroMV.WellPosed.Pos k → EthierKurtz.SDEState d → (ℝ → EthierKurtz.SDEState d) → Ω' →
    Matrix (Fin d) (Fin n) ℝ
  η : ℝ≥0 → NeuroMV.WellPosed.Pos k → NeuroMV.WellPosed.Pos k → EthierKurtz.SDEState d → (ℝ → EthierKurtz.SDEState d) → Ω' → U →
    EthierKurtz.SDEState d

/-- The coefficients are jointly measurable in all variables (matrices entrywise; paths with
the product σ-algebra) and continuous in `x ∈ ℝᵈ` (p. 2). -/
def Coeffs.Regular {d m n k P : ℕ} {U Ω' : Type*} [MeasurableSpace U] [MeasurableSpace Ω']
    (C : Coeffs d m n k P U Ω') : Prop :=
  Measurable (fun p : ℝ≥0 × NeuroMV.WellPosed.Pos k × EthierKurtz.SDEState d × Ω' =>
      C.f p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
    (∀ i j, Measurable (fun p : ℝ≥0 × NeuroMV.WellPosed.Pos k × EthierKurtz.SDEState d × Ω' =>
      C.g p.1 p.2.1 p.2.2.1 p.2.2.2 i j)) ∧
    Measurable (fun p : ℝ≥0 × NeuroMV.WellPosed.Pos k × EthierKurtz.SDEState d × Ω' × U =>
      C.h p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) ∧
    Measurable (fun p : ℝ≥0 × NeuroMV.WellPosed.Pos k × NeuroMV.WellPosed.Pos k × EthierKurtz.SDEState d ×
        (ℝ → EthierKurtz.SDEState d) × Ω' =>
      C.θ p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) ∧
    (∀ i j, Measurable (fun p : ℝ≥0 × NeuroMV.WellPosed.Pos k × NeuroMV.WellPosed.Pos k × EthierKurtz.SDEState d ×
        (ℝ → EthierKurtz.SDEState d) × Ω' =>
      C.β p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 i j)) ∧
    Measurable (fun p : ℝ≥0 × NeuroMV.WellPosed.Pos k × NeuroMV.WellPosed.Pos k × EthierKurtz.SDEState d ×
        (ℝ → EthierKurtz.SDEState d) × Ω' × U =>
      C.η p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) ∧
    (∀ t r ω', Continuous (fun x => C.f t r x ω')) ∧
    (∀ t r ω', Continuous (fun x => C.g t r x ω')) ∧
    (∀ t r ω' ξ, Continuous (fun x => C.h t r x ω' ξ)) ∧
    (∀ t r r' y ω', Continuous (fun x => C.θ t r r' x y ω')) ∧
    (∀ t r r' y ω', Continuous (fun x => C.β t r r' x y ω')) ∧
    (∀ t r r' y ω' ξ, Continuous (fun x => C.η t r r' x y ω' ξ))

/-- The data of Hypothesis 1.1: the probability measure `λ` on `[-τ, 0]` and the rates
`K_t(ω')`, `L_t(ω')`, `K̄_t(ω')`, `L̄_t(ω')`, `K̃_t(R, ω')` (`Kt t R ω'`). -/
structure Rates (Ω' : Type*) where
  lam : Measure ℝ
  K : ℝ≥0 → Ω' → ℝ
  L : ℝ≥0 → Ω' → ℝ
  Kb : ℝ≥0 → Ω' → ℝ
  Lb : ℝ≥0 → Ω' → ℝ
  Kt : ℝ≥0 → ℝ → Ω' → ℝ

/-- **Hypothesis 1.1, (H1)–(H5)** (pp. 3–4), for positions `r, r' ∈ Γ`, with the preamble's
conditions on `λ` and the rates. The `ν`-integrals are in `[0, ∞]`; in (H1)–(H2), which contain
the possibly negative term `2⟨·,·⟩`, the `ν`-integral is required finite and then read as a real
number. In (H4)–(H5) the paths `y, ỹ` range over càglàd paths on `[-τ, 0]`. -/
def Hyp {d m n k P : ℕ} {U Ω' : Type*} [MeasurableSpace U] [MeasurableSpace Ω']
    (G : Geometry k P) (ν : Measure U) (C : Coeffs d m n k P U Ω') (R : Rates Ω') : Prop :=
  C.Regular ∧ IsProbabilityMeasure R.lam ∧ R.lam (Set.Icc (-G.τ) 0)ᶜ = 0 ∧
    NeuroMV.WellPosed.IsRate R.K ∧ NeuroMV.WellPosed.IsRate R.L ∧ NeuroMV.WellPosed.IsRate R.Kb ∧ NeuroMV.WellPosed.IsRate R.Lb ∧
    (∀ Rr : ℝ, 0 < Rr → NeuroMV.WellPosed.IsRate (fun t ω' => R.Kt t Rr ω')) ∧
    -- (H1)
    (∀ t, ∀ r ∈ G.Γ, ∀ x x' ω',
      (∫⁻ ξ, ‖C.h t r x ω' ξ - C.h t r x' ω' ξ‖ₑ ^ 2 ∂ν) < ⊤ ∧
      2 * inner ℝ (x - x') (C.f t r x ω' - C.f t r x' ω') + frob2 (C.g t r x ω' - C.g t r x' ω') +
          (∫⁻ ξ, ‖C.h t r x ω' ξ - C.h t r x' ω' ξ‖ₑ ^ 2 ∂ν).toReal ≤
        R.L t ω' * ‖x - x'‖ ^ 2) ∧
    -- (H2)
    (∀ t, ∀ r ∈ G.Γ, ∀ x ω',
      (∫⁻ ξ, ‖C.h t r x ω' ξ‖ₑ ^ 2 ∂ν) < ⊤ ∧
      2 * inner ℝ x (C.f t r x ω') + frob2 (C.g t r x ω') +
          (∫⁻ ξ, ‖C.h t r x ω' ξ‖ₑ ^ 2 ∂ν).toReal ≤
        R.K t ω' * (1 + ‖x‖ ^ 2)) ∧
    -- (H3)
    (∀ t, ∀ r ∈ G.Γ, ∀ ω', ∀ Rr : ℝ, 0 < Rr → ∀ x, ‖x‖ ≤ Rr →
      ENNReal.ofReal (‖C.f t r x ω'‖ + frob2 (C.g t r x ω')) +
          ∫⁻ ξ, ‖C.h t r x ω' ξ‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (R.Kt t Rr ω')) ∧
    -- (H4)
    (∀ t, ∀ r ∈ G.Γ, ∀ r' ∈ G.Γ, ∀ x x' y y' ω', IsCagladOn G.τ y → IsCagladOn G.τ y' →
      ENNReal.ofReal (‖C.θ t r r' x y ω' - C.θ t r r' x' y' ω'‖ ^ 2 +
          frob2 (C.β t r r' x y ω' - C.β t r r' x' y' ω')) +
          ∫⁻ ξ, ‖C.η t r r' x y ω' ξ - C.η t r r' x' y' ω' ξ‖ₑ ^ 2 ∂ν ≤
        ENNReal.ofReal (R.Lb t ω') * (ENNReal.ofReal (‖x - x'‖ ^ 2) + lamDist2 R.lam y y')) ∧
    -- (H5)
    (∀ t, ∀ r ∈ G.Γ, ∀ r' ∈ G.Γ, ∀ x y ω', IsCagladOn G.τ y →
      ENNReal.ofReal (‖C.θ t r r' x y ω'‖ ^ 2 + frob2 (C.β t r r' x y ω')) +
          ∫⁻ ξ, ‖C.η t r r' x y ω' ξ‖ₑ ^ 2 ∂ν ≤
        ENNReal.ofReal (R.Kb t ω') * (1 + ENNReal.ofReal (‖x‖ ^ 2) + lamDist2 R.lam y 0))

/-! ### Driving noise (p. 2, p. 5, p. 22) -/

/-- A countable family `(W^c)_c` of real Brownian motions is an `(𝓕_t)`-Brownian family:
each `W^c` is adapted, the paths of the family are mutually independent, and for `s ≤ t` the
family of increments `(W^c_t − W^c_s)_c` is independent of `𝓕_s`. -/
def IsFBrownianFamily {ι Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω)
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (Wc : ι → ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ c t, Measurable[𝓕 t] (Wc c t)) ∧ iIndepFun (fun c ω t => Wc c t ω) Pr ∧
    ∀ s t : ℝ≥0, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω c => Wc c t ω - Wc c s ω) inferInstance) (𝓕 s) Pr

/-- The atoms of mark `c` of a random measure on `[0, ∞) × (κ × U)` given by its atoms:
`{(t, ξ) : (t, (c, ξ)) ∈ N(ω)}`. -/
def markSlice {Ω κ U : Type*} (Nall : Ω → Set (ℝ≥0 × (κ × U))) (c : κ) (ω : Ω) :
    Set (ℝ≥0 × U) :=
  {p | (p.1, (c, p.2)) ∈ Nall ω}

/-- The scalar coordinates of the Brownian motions `W` (in `ℝᵐ`) and `B^α` (in `ℝⁿ`) of (6). -/
def coords6 {Ω : Type*} {m n P : ℕ} (W : ℝ≥0 → Ω → EthierKurtz.SDEState m)
    (B : Fin P → ℝ≥0 → Ω → EthierKurtz.SDEState n) : Fin m ⊕ (Fin P × Fin n) → ℝ≥0 → Ω → ℝ
  | Sum.inl j => fun t ω => W t ω j
  | Sum.inr (α, j) => fun t ω => B α t ω j

/-- The noise of (6) on a filtered probability space `(Ω, 𝓕, (𝓕_t), ℙ)` (p. 5, p. 22):
an `m`-dimensional and `P` `n`-dimensional standard Brownian motions `W, B¹, …, B^P` forming
an `(𝓕_t)`-Brownian family, and one `(𝓕_t)`-Poisson random measure on
`[0, ∞) × (Option (Fin P) × U)` with intensity `dt ⊗ (count ⊗ ν)`: its mark `none` is `N`, its
mark `some α` is `N^α`, so `N, N¹, …, N^P` are independent Poisson measures with intensity
`dt ⊗ ν`. -/
def IsNoise6 {Ω U : Type*} [MeasurableSpace Ω] [MeasurableSpace U] {m n P : ℕ} (Pr : Measure Ω)
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (ν : Measure U)
    (W : ℝ≥0 → Ω → EthierKurtz.SDEState m) (B : Fin P → ℝ≥0 → Ω → EthierKurtz.SDEState n)
    (Nall : Ω → Set (ℝ≥0 × (Option (Fin P) × U))) : Prop :=
  IsProbabilityMeasure Pr ∧ EthierKurtz.IsStandardBrownian Pr W ∧
    (∀ α, EthierKurtz.IsStandardBrownian Pr (B α)) ∧ IsFBrownianFamily Pr 𝓕 (coords6 W B) ∧
    JacodTodorov10.LLN.IsFPoisson 𝓕 Pr (Measure.count.prod ν) Nall

/-- The initial conditions `ẑ^α ∈ L²(Ω, ℙ; Càdlàg([-τ, 0]; ℝᵈ))`, `α : Fin P` (p. 2): càdlàg
paths on `[-τ, 0]`, `𝓕₀`-measurable at each time of `[-τ, 0]` (hence independent of the noise), with
`𝔼 sup_{u ∈ [-τ, 0]} |ẑ^α_u|² < ∞`. -/
def IsInit {Ω ι : Type*} [MeasurableSpace Ω] {d : ℕ} (Pr : Measure Ω)
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (τ : ℝ) (z : ι → ℝ → Ω → EthierKurtz.SDEState d) :
    Prop :=
  (∀ c ω, IsCadlagOn (-τ) 0 (fun u => z c u ω)) ∧
    (∀ c, ∀ u ∈ Set.Icc (-τ) 0, Measurable[𝓕 0] (z c u)) ∧
    ∀ c, (∫⁻ ω, ⨆ u ∈ Set.Icc (-τ) 0, ‖z c u ω‖ₑ ^ 2 ∂Pr) < ⊤

/-! ### Strong solutions of an Itô equation with jumps on `[-τ, T]` -/

/-- The integrand `v` cut off after time `T`. -/
noncomputable def cut (T : ℝ) (s : ℝ≥0) (v : ℝ) : ℝ :=
  if (s : ℝ) ≤ T then v else 0

/-- `Y` is a strong solution on `[-τ, T]` of
`dY_t = a_t dt + G_t dW_t + ∫_U H_t(ξ) Ñ(dt, dξ) + Σ_α (Gα_t dB^α_t + ∫_U Hα_t(ξ) Ñ^α(dt, dξ))`,
`Y_t = z_t` on `[-τ, 0]`, where the integrands are given processes:
1. `Y_t = z_{max(t, -τ)}` for `t ≤ 0` (the initial segment, extended constantly below `-τ`);
2. every path is càdlàg on `[-τ, T]`;
3. `Y_t` is `𝓕_t`-measurable for `t ∈ [0, T]`;
4. there are processes `Jg, Jh, Jb, Jη` that are the stochastic integrals of the coordinates of
   the integrands (cut off after `T`) — Itô integrals against the Brownian coordinates
   (`EthierKurtz.HasBrownianItoIntegral`) and compensated Poisson integrals against the atoms
   `N0`, `Nα α` (`JacodTodorov10.LLN.HasCompInt`) — the drift is pathwise integrable on
   `[0, T]`, and for every `t ∈ [0, T]`, almost surely, every coordinate satisfies the integral
   identity. -/
def IsJumpItoSol {Ω U : Type*} [MeasurableSpace Ω] [MeasurableSpace U] {d m n P : ℕ}
    (Pr : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (ν : Measure U) (τ T : ℝ)
    (W : ℝ≥0 → Ω → EthierKurtz.SDEState m) (B : Fin P → ℝ≥0 → Ω → EthierKurtz.SDEState n)
    (N0 : Ω → Set (ℝ≥0 × U)) (Nα : Fin P → Ω → Set (ℝ≥0 × U))
    (z : ℝ → Ω → EthierKurtz.SDEState d)
    (a : ℝ≥0 → Ω → EthierKurtz.SDEState d) (G : ℝ≥0 → Ω → Matrix (Fin d) (Fin m) ℝ)
    (H : ℝ≥0 → Ω → U → EthierKurtz.SDEState d)
    (Gα : Fin P → ℝ≥0 → Ω → Matrix (Fin d) (Fin n) ℝ)
    (Hα : Fin P → ℝ≥0 → Ω → U → EthierKurtz.SDEState d)
    (Y : ℝ → Ω → EthierKurtz.SDEState d) : Prop :=
  (∀ t ≤ (0 : ℝ), ∀ ω, Y t ω = z (max t (-τ)) ω) ∧
    (∀ ω, IsCadlagOn (-τ) T (fun t => Y t ω)) ∧
    (∀ t : ℝ≥0, (t : ℝ) ≤ T → Measurable[𝓕 t] (Y t)) ∧
    ∃ (Jg : Fin d → Fin m → ℝ≥0 → Ω → ℝ) (Jh : Fin d → ℝ≥0 → Ω → ℝ)
      (Jb : Fin P → Fin d → Fin n → ℝ≥0 → Ω → ℝ) (Jη : Fin P → Fin d → ℝ≥0 → Ω → ℝ),
      (∀ i j, EthierKurtz.HasBrownianItoIntegral Pr (fun t => 𝓕 t) (fun t ω => W t ω j)
        (fun s ω => cut T s (G s ω i j)) (Jg i j)) ∧
      (∀ i, JacodTodorov10.LLN.HasCompInt Pr ν N0 (fun ω s ξ => cut T s (H s ω ξ i)) (Jh i)) ∧
      (∀ α i j, EthierKurtz.HasBrownianItoIntegral Pr (fun t => 𝓕 t) (fun t ω => B α t ω j)
        (fun s ω => cut T s (Gα α s ω i j)) (Jb α i j)) ∧
      (∀ α i, JacodTodorov10.LLN.HasCompInt Pr ν (Nα α)
        (fun ω s ξ => cut T s (Hα α s ω ξ i)) (Jη α i)) ∧
      (∀ ω i, IntervalIntegrable (fun s : ℝ => a s.toNNReal ω i) volume 0 T) ∧
      ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ᵐ ω ∂Pr, ∀ i,
        Y t ω i = z 0 ω i + (∫ s in (0 : ℝ)..(t : ℝ), a s.toNNReal ω i) +
          (∑ j, Jg i j t ω) + Jh i t ω + ∑ α, ((∑ j, Jb α i j t ω) + Jη α i t ω)

/-! ### The McKean–Vlasov equation (6), p. 5 -/

/-- The mean-field drift `∫_{Γ_α} 𝔼̃[θ(s, r, r', x, X̃^{r'}_{(s−τ)⁻:s⁻}, ω')] 𝓡(dr')`, the
expectation taken over the law of the solution `X` itself (on its own probability space `PrX`,
the paper's `ℙ̃`). -/
noncomputable def meanθ {d m n k P : ℕ} {U Ω' ΩX : Type*} [MeasurableSpace ΩX]
    (G : Geometry k P) (C : Coeffs d m n k P U Ω') (PrX : Measure ΩX)
    (X : NeuroMV.WellPosed.Pos k → ℝ → ΩX → EthierKurtz.SDEState d) (α : Fin P) (s : ℝ≥0) (r : NeuroMV.WellPosed.Pos k)
    (x : EthierKurtz.SDEState d) (ω' : Ω') : EthierKurtz.SDEState d :=
  ∫ r' in G.Γα α, ∫ ω, C.θ s r r' x (seg (X r') s ω) ω' ∂PrX ∂G.𝓡

/-- The mean-field diffusion `∫_{Γ_α} 𝔼̃[β(s, r, r', x, X̃^{r'}_{(s−τ)⁻:s⁻}, ω')] 𝓡(dr')`. -/
noncomputable def meanβ {d m n k P : ℕ} {U Ω' ΩX : Type*} [MeasurableSpace ΩX]
    (G : Geometry k P) (C : Coeffs d m n k P U Ω') (PrX : Measure ΩX)
    (X : NeuroMV.WellPosed.Pos k → ℝ → ΩX → EthierKurtz.SDEState d) (α : Fin P) (s : ℝ≥0) (r : NeuroMV.WellPosed.Pos k)
    (x : EthierKurtz.SDEState d) (ω' : Ω') : Matrix (Fin d) (Fin n) ℝ :=
  fun i j => ∫ r' in G.Γα α, ∫ ω, C.β s r r' x (seg (X r') s ω) ω' i j ∂PrX ∂G.𝓡

/-- The mean-field jump integrand `∫_{Γ_α} 𝔼̃[η(s, r, r', x, X̃^{r'}_{(s−τ)⁻:s⁻}, ω', ξ)] 𝓡(dr')`. -/
noncomputable def meanη {d m n k P : ℕ} {U Ω' ΩX : Type*} [MeasurableSpace ΩX]
    (G : Geometry k P) (C : Coeffs d m n k P U Ω') (PrX : Measure ΩX)
    (X : NeuroMV.WellPosed.Pos k → ℝ → ΩX → EthierKurtz.SDEState d) (α : Fin P) (s : ℝ≥0) (r : NeuroMV.WellPosed.Pos k)
    (x : EthierKurtz.SDEState d) (ω' : Ω') (ξ : U) : EthierKurtz.SDEState d :=
  ∫ r' in G.Γα α, ∫ ω, C.η s r r' x (seg (X r') s ω) ω' ξ ∂PrX ∂G.𝓡

/-- `X = (X^r)_{r ∈ Γ}` is a strong solution of the McKean–Vlasov equation (6) on `[-τ, T]` at
the disorder `ω'`: `(r, ω) ↦ X^r_t(ω)` is jointly measurable for each `t` (p. 6), and for every
`ζ` and every `r ∈ Γ_ζ`, `X^r` solves (6) with initial condition `ẑ^ζ`, driven by `W`, `N`
(mark `none`), `B^α` and `N^α` (mark `some α`), every coefficient evaluated at `X^r_{s−}`, and
mean-field terms computed from the law of `X` itself. -/
def IsStrongSol6 {d m n k P : ℕ} {U Ω' Ω : Type*} [MeasurableSpace U] [MeasurableSpace Ω]
    (G : Geometry k P) (ν : Measure U) (C : Coeffs d m n k P U Ω') (Pr : Measure Ω)
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (W : ℝ≥0 → Ω → EthierKurtz.SDEState m)
    (B : Fin P → ℝ≥0 → Ω → EthierKurtz.SDEState n) (Nall : Ω → Set (ℝ≥0 × (Option (Fin P) × U)))
    (zh : Fin P → ℝ → Ω → EthierKurtz.SDEState d) (ω' : Ω') (T : ℝ)
    (X : NeuroMV.WellPosed.Pos k → ℝ → Ω → EthierKurtz.SDEState d) : Prop :=
  (∀ t : ℝ, Measurable (fun p : NeuroMV.WellPosed.Pos k × Ω => X p.1 t p.2)) ∧
    ∀ ζ, ∀ r ∈ G.Γα ζ,
      IsJumpItoSol Pr 𝓕 ν G.τ T W B (markSlice Nall none) (fun α => markSlice Nall (some α))
        (zh ζ)
        (fun s ω => C.f s r (lft (X r) s ω) ω' + ∑ α, meanθ G C Pr X α s r (lft (X r) s ω) ω')
        (fun s ω => C.g s r (lft (X r) s ω) ω')
        (fun s ω ξ => C.h s r (lft (X r) s ω) ω' ξ)
        (fun α s ω => meanβ G C Pr X α s r (lft (X r) s ω) ω')
        (fun α s ω ξ => meanη G C Pr X α s r (lft (X r) s ω) ω' ξ)
        (X r)

/-- The class `L^∞([-τ, T], dt; L²(Ω × Γ, ℙ ⊗ 𝓡; ℝᵈ))` of Theorem 1.5, as a bound for every
`t ∈ [-τ, T]`: `sup_t ∫_Γ 𝔼|X^r_t|² 𝓡(dr) < ∞`. -/
def InClass {d k P : ℕ} {Ω : Type*} [MeasurableSpace Ω] (G : Geometry k P) (Pr : Measure Ω)
    (T : ℝ) (X : NeuroMV.WellPosed.Pos k → ℝ → Ω → EthierKurtz.SDEState d) : Prop :=
  ∃ c : ℝ≥0∞, c < ⊤ ∧ ∀ t ∈ Set.Icc (-G.τ) T, ∫⁻ r, ∫⁻ ω, ‖X r t ω‖ₑ ^ 2 ∂Pr ∂G.𝓡 ≤ c

end NeuroMV.Chaos


