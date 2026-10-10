-- Prove2me | Definitions.Def_NeuroMV_WellPosed_Setting
-- name    : NeuroMV_WellPosed_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T13:45:24.021292+00:00
-- url     : https://prove2.me/theorems/c0e659a0-1816-479c-9857-c48d08baac2d
-- title:
--   §1, pp. 2–6 — spatial structure, coefficients, Hypothesis 1.1 (H1)–(H5), noise, strong solutions of (6), the class L^∞–L², C₁ of (7)
-- statement:
--   This module fixes the model of the spatially structured McKean–Vlasov delay equation (6) with jumps.
--
--   **Space.** There are $P \ge 1$ subpopulations placed at pairwise disjoint measurable regions $\Gamma_\alpha \subset \mathbb R^k$ (indexed $\alpha = 0,\dots,P-1$ in Lean for the paper's $1,\dots,P$), whose union $\Gamma$ is bounded, and a finite Borel measure $\mathcal R$ carried by $\Gamma$ with $\mathcal R(\Gamma_\alpha) = 1$ for every $\alpha$.
--
--   **Coefficients.** The local dynamics are $f(t,r,x,\omega') \in \mathbb R^d$, $g(t,r,x,\omega') \in \mathbb R^{d\times m}$ and $h(t,r,x,\omega',\xi) \in \mathbb R^d$; the synaptic transmissions are $\theta, \beta, \eta$, which depend in addition on a second position $r'$ and on a path segment $y_{-\tau:0}$. All coefficients are jointly measurable in all variables and continuous in $x$.
--
--   **Hypothesis 1.1 (H1)–(H5).** There are a probability measure $\lambda$ on $[-\tau,0]$ and nonnegative measurable rates $K_t(\omega'), L_t(\omega'), \bar K_t(\omega'), \bar L_t(\omega')$ and $\tilde K_t(R,\omega')$ ($R>0$), locally integrable in $t$, such that for all $t \ge 0$, $r, r' \in \Gamma$, $x, \tilde x \in \mathbb R^d$, càglàd segments $y, \tilde y$ on $[-\tau,0]$ and $\omega'$:
--
--   $$2\langle x-\tilde x, f(x)-f(\tilde x)\rangle + |g(x)-g(\tilde x)|^2 + \int_U |h(x,\xi)-h(\tilde x,\xi)|^2\,\nu(d\xi) \le L_t(\omega')|x-\tilde x|^2,$$
--
--   $$2\langle x, f(x)\rangle + |g(x)|^2 + \int_U |h(x,\xi)|^2\,\nu(d\xi) \le K_t(\omega')(1+|x|^2),\qquad \sup_{|x|\le R}\Big[|f| + |g|^2 + \int_U|h|^2 d\nu\Big] \le \tilde K_t(R,\omega'),$$
--
--   $$\sum_{\Theta\in\{\theta,\beta\}} |\Theta(x,y)-\Theta(\tilde x,\tilde y)|^2 + \int_U |\eta(x,y,\xi)-\eta(\tilde x,\tilde y,\xi)|^2 d\nu \le \bar L_t(\omega')\Big[|x-\tilde x|^2 + \int_{-\tau}^0 \big(|y_s-\tilde y_s|^2 + 1_{s<0}|y_{s+}-\tilde y_{s+}|^2\big)\lambda(ds)\Big],$$
--
--   and (H5), the same with $\bar K_t(\omega')\big[1 + |x|^2 + \int_{-\tau}^0(|y_s|^2 + 1_{s<0}|y_{s+}|^2)\lambda(ds)\big]$ bounding $\sum_\Theta|\Theta(x,y)|^2 + \int_U|\eta(x,y,\xi)|^2 d\nu$. Matrix norms are Hilbert–Schmidt norms.
--
--   **Noise.** On a filtered probability space $(\Omega,\mathcal F,(\mathcal F_t),\mathbb P)$ there are an $m$-dimensional $(\mathcal F_t)$-Brownian motion $W$ and $n$-dimensional $(\mathcal F_t)$-Brownian motions $B^1,\dots,B^P$ with jointly independent coordinates, independent $(\mathcal F_t)$-Poisson random measures $N, N^1,\dots,N^P$ on $[0,\infty)\times U$ with intensity $dt\otimes\nu$ (compensated $\tilde N = N - dt\otimes\nu$), and $\mathcal F_0$-measurable initial conditions $\hat z^\alpha \in L^2(\Omega;\text{Càdlàg}([-\tau,0];\mathbb R^d))$.
--
--   **Strong solution of (6) on $[-\tau,T]$.** A family $X^r_t(\omega)$, $r\in\Gamma$, with càdlàg paths, adapted, jointly measurable in $(r,\omega)$, equal to $\hat z^\zeta_t$ on $[-\tau,0]$ for $r \in \Gamma_\zeta$, and satisfying for every $t \in [0,T]$ almost surely
--
--   $$X^r_t = \hat z^\zeta_0 + \int_0^t f\,ds + \int_0^t g\,dW + \int_0^t\!\!\int_U h\,\tilde N(ds,d\xi) + \sum_{\alpha=1}^P\Big(\int_0^t\!\!\int_{\Gamma_\alpha}\tilde{\mathbb E}[\theta]\,\mathcal R(dr')\,ds + \int_0^t\!\!\int_{\Gamma_\alpha}\tilde{\mathbb E}[\beta]\,\mathcal R(dr')\,dB^\alpha + \int_0^t\!\!\int_U\!\int_{\Gamma_\alpha}\tilde{\mathbb E}[\eta]\,\mathcal R(dr')\,\tilde N^\alpha(ds,d\xi)\Big),$$
--
--   with every local coefficient evaluated at $(s, r, X^r_{s-}, \omega')$ and every synaptic one at $(s, r, r', X^r_{s-}, \tilde X^{r'}_{(s-\tau)^-:s^-}, \omega')$, $\tilde X$ a copy of $X$. The class $L^\infty([-\tau,T],dt;L^2(\Omega\times\Gamma,\mathbb P\otimes\mathcal R;\mathbb R^d))$ and the constant
--
--   $$C_1(t,\omega') = \Big(\sup_{u\in[-\tau,0],\,1\le\zeta\le P}\mathbb E|\hat z^\zeta(u)|^2 + 1\Big)\exp\Big(\int_0^t (K_s(\omega') + 3P\bar K_s(\omega') + P)\,ds\Big)$$
--
--   of (7) are defined here as well. Every theorem of the mission is stated in this model.
--
--   **Formalization Note.** Matrix-valued coefficients are measured, made continuous and integrated entrywise. The path argument of $\theta,\beta,\eta$ is a function $\mathbb R \to \mathbb R^d$ read on $[-\tau,0]$, with the product (cylinder) σ-algebra; the paper uses the Borel σ-algebra of the supremum norm, so joint measurability for the cylinder σ-algebra is a mild added requirement. (H4)–(H5) are quantified over paths that are càglàd on $[-\tau,0]$ (they force the synaptic coefficients to depend on the path only through $[-\tau,0]$) and stated in $[0,\infty]$; in (H1)–(H3) the $\nu$-integrals are asserted finite and compared as real numbers. (H6) is not included: it involves the network data of (1) only. All Poisson random measures are packed into one $(\mathcal F_t)$-Poisson random measure (the published `JacodTodorov10.LLN.IsFPoisson`) on $[0,\infty)\times((\{\ast\}\sqcup\{1..P\})\times U)$ with intensity $dt\otimes(\text{counting}\otimes\nu)$, which is the same as independent Poisson measures $N, N^\alpha$; that predicate excludes simultaneous atoms for every $\omega$. Independence of $\hat z$ from the drivers is encoded by $\mathcal F_0$-measurability. Stochastic integrals are the published `EthierKurtz.HasBrownianItoIntegral` and `JacodTodorov10.LLN.HasCompInt`, applied coordinatewise, with integrands cut off after $T$. The copy $\tilde X$ enters only through its law, so $\tilde{\mathbb E}$ is computed as an expectation over $X$ itself, and the mean-field integrands are required to be integrable on $\Gamma_\alpha \times \Omega$ (the paper's measurability requirement in $r'$, p. 6). Paths are càdlàg for every $\omega$; the integral identity holds almost surely for each $t$. The class is encoded as a bound for every $t\in[-\tau,T]$ rather than for a.e. $t$. A generic `SolvesOn` takes the segment map and the set of positions where the identity is required, so that the Euler scheme (13) and claim (v) reuse it.
-- source:
--   Mehri, Scheutzow, Stannat, Zangeneh, Propagation of Chaos for Stochastic Spatially Structured Neuronal Networks with Delay driven by Jump Diffusions, arXiv:1805.01654v3, §1, p. 2 (coefficients, noise), Hypothesis 1.1 (H1)–(H5), pp. 3–4, (6), p. 5, p. 6 (measurability in r′), Lemma 1.4 (7), p. 6; filtration conventions of Appendix A, p. 22

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_JacodTodorov10_LLN_Noise

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NeuroMV.WellPosed

open EthierKurtz

/-- Positions of neurons: points of `ℝ^k` (Mehri–Scheutzow–Stannat–Zangeneh, arXiv:1805.01654v3,
§1, p. 2). -/
abbrev Pos (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- A path `x : ℝ → E` is **càdlàg on `[a, b]`**: right-continuous at every `s ∈ [a, b)` and with a
left limit at every `s ∈ (a, b]`. Values outside `[a, b]` play no role. -/
def IsCadlagOn {E : Type*} [TopologicalSpace E] (x : ℝ → E) (a b : ℝ) : Prop :=
  (∀ s ∈ Set.Ico a b, ContinuousWithinAt x (Set.Ici s) s) ∧
    ∀ s ∈ Set.Ioc a b, ∃ l : E, Tendsto x (𝓝[<] s) (𝓝 l)

/-- A path `y : ℝ → E` is **càglàd on `[a, b]`**: left-continuous at every `s ∈ (a, b]` and with a
right limit at every `s ∈ [a, b)`. This is the domain `Càglàd([−τ, 0]; ℝ^d)` of the synaptic
coefficients (p. 2) when `a = −τ`, `b = 0`. -/
def IsCagladOn {E : Type*} [TopologicalSpace E] (y : ℝ → E) (a b : ℝ) : Prop :=
  (∀ s ∈ Set.Ioc a b, ContinuousWithinAt y (Set.Iic s) s) ∧
    ∀ s ∈ Set.Ico a b, ∃ l : E, Tendsto y (𝓝[>] s) (𝓝 l)

/-- The **path segment** `x_{(t−τ)⁻:t⁻}` of a path `x` at time `t` (p. 2 and (6), p. 5): the path
`u ↦ x_{(t+u)⁻}`, read on `u ∈ [−τ, 0]`. The left limit is Mathlib's `Function.leftLim`. -/
noncomputable def seg {E : Type*} [TopologicalSpace E] (x : ℝ → E) (t : ℝ) : ℝ → E :=
  fun u => Function.leftLim x (t + u)

/-- The squared Hilbert–Schmidt (Frobenius) norm `|A|² = ∑ᵢ ∑ⱼ Aᵢⱼ²` of a real matrix; this is
the norm `|g|²`, `|β|²` of Hypothesis 1.1. -/
def frobSq {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j ^ 2

/-- The **spatial structure** (pp. 2, 5): `P ≥ 1` subpopulations placed at pairwise disjoint
measurable regions `Γ_α ⊂ ℝ^k` (indexed by `Fin P`, i.e. `α = 0, …, P − 1` for the paper's
`α = 1, …, P`), whose union `Γ` is bounded, and a finite Borel measure `𝓡` on `Γ` with
`𝓡(Γ_α) = 1` for every `α`. -/
structure Space (k P : ℕ) where
  Γ : Set (Pos k)
  Γα : Fin P → Set (Pos k)
  R : Measure (Pos k)
  pos : 0 < P
  meas : ∀ α, MeasurableSet (Γα α)
  disj : Pairwise fun α β => Disjoint (Γα α) (Γα β)
  cover : Γ = ⋃ α, Γα α
  bounded : Bornology.IsBounded Γ
  finite : IsFiniteMeasure R
  null_compl : R Γᶜ = 0
  mass : ∀ α, R (Γα α) = 1

/-- The **coefficients** of (6) (p. 2): local dynamics `f, g, h` and synaptic transmissions
`θ, β, η`, depending on time `t ≥ 0`, positions `r, r'`, state `x ∈ ℝ^d`, a path segment `y`
(read on `[−τ, 0]`), the disorder `ω' ∈ Ω'` and (for `h`, `η`) a mark `ξ ∈ U`. -/
structure Coeffs (d m n k : ℕ) (U Ω' : Type*) where
  f : ℝ≥0 → Pos k → SDEState d → Ω' → SDEState d
  g : ℝ≥0 → Pos k → SDEState d → Ω' → Matrix (Fin d) (Fin m) ℝ
  h : ℝ≥0 → Pos k → SDEState d → Ω' → U → SDEState d
  θ : ℝ≥0 → Pos k → Pos k → SDEState d → (ℝ → SDEState d) → Ω' → SDEState d
  β : ℝ≥0 → Pos k → Pos k → SDEState d → (ℝ → SDEState d) → Ω' → Matrix (Fin d) (Fin n) ℝ
  η : ℝ≥0 → Pos k → Pos k → SDEState d → (ℝ → SDEState d) → Ω' → U → SDEState d

variable {d m n k P : ℕ} {U Ω Ω' : Type*}

/-- The coefficients are **jointly measurable in all variables and continuous in `x`** (p. 2).
Matrix-valued coefficients are measured and made continuous entrywise; the path argument carries
the product (cylinder) σ-algebra of `ℝ → ℝ^d`. -/
def Coeffs.Regular [MeasurableSpace U] [MeasurableSpace Ω'] (C : Coeffs d m n k U Ω') : Prop :=
  Measurable (fun p : ℝ≥0 × Pos k × SDEState d × Ω' => C.f p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  (∀ i j, Measurable
    (fun p : ℝ≥0 × Pos k × SDEState d × Ω' => C.g p.1 p.2.1 p.2.2.1 p.2.2.2 i j)) ∧
  Measurable
    (fun p : ℝ≥0 × Pos k × SDEState d × Ω' × U => C.h p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) ∧
  Measurable (fun p : ℝ≥0 × Pos k × Pos k × SDEState d × (ℝ → SDEState d) × Ω' =>
    C.θ p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) ∧
  (∀ i j, Measurable (fun p : ℝ≥0 × Pos k × Pos k × SDEState d × (ℝ → SDEState d) × Ω' =>
    C.β p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 i j)) ∧
  Measurable (fun p : ℝ≥0 × Pos k × Pos k × SDEState d × (ℝ → SDEState d) × Ω' × U =>
    C.η p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) ∧
  (∀ t r ω', Continuous fun x => C.f t r x ω') ∧
  (∀ t r ω' i j, Continuous fun x => C.g t r x ω' i j) ∧
  (∀ t r ω' ξ, Continuous fun x => C.h t r x ω' ξ) ∧
  (∀ t r r' y ω', Continuous fun x => C.θ t r r' x y ω') ∧
  (∀ t r r' y ω' i j, Continuous fun x => C.β t r r' x y ω' i j) ∧
  (∀ t r r' y ω' ξ, Continuous fun x => C.η t r r' x y ω' ξ)

/-- A **rate** of Hypothesis 1.1: a nonnegative function `F_t(ω')`, jointly measurable in
`(t, ω')`, and in `L¹_loc([0, ∞), dt)` for every `ω'`. -/
def IsRate [MeasurableSpace Ω'] (F : ℝ≥0 → Ω' → ℝ) : Prop :=
  (∀ t ω', 0 ≤ F t ω') ∧ Measurable (Function.uncurry F) ∧
    ∀ (ω' : Ω') (t : ℝ≥0), IntervalIntegrable (fun s : ℝ => F s.toNNReal ω') volume 0 (t : ℝ)

/-- The **delay integral** `∫_{−τ}^0 (|y_s − ỹ_s|² + 1_{s<0} |y_{s+} − ỹ_{s+}|²) λ(ds)` of (H4), in
`ℝ≥0∞`; with `ỹ = 0` it is the integral of (H5). `y_{s+}` is the right limit
(`Function.rightLim`). -/
noncomputable def delayInt {d : ℕ} (lam : Measure ℝ) (y y' : ℝ → SDEState d) : ℝ≥0∞ :=
  ∫⁻ s, (‖y s - y' s‖ₑ ^ 2 +
    Set.indicator (Set.Iio 0)
      (fun s => ‖Function.rightLim y s - Function.rightLim y' s‖ₑ ^ 2) s) ∂lam

/-- **Hypothesis 1.1, (H1)–(H5)** (pp. 3–4), for given data: `λ` is a probability measure on
`[−τ, 0]`; `K, L, K̄, L̄` (`K`, `L`, `Kb`, `Lb`) and, for every `R > 0`, `K̃(R)` (`Kt R`) are rates
(nonnegative, measurable, `L¹_loc`); and (H1)–(H5) hold for all `t ≥ 0`, `r, r' ∈ Γ`,
`x, x̃ ∈ ℝ^d`, càglàd segments `y, ỹ` on `[−τ, 0]` and `ω' ∈ Ω'`. In (H1)–(H3) the `ν`-integrals are
finite (the inequalities assert it) and are then compared as real numbers; (H4)–(H5) are stated in
`ℝ≥0∞`. (H6) is not part of this predicate: it concerns the network (1) only. -/
def Hyp1_1 [MeasurableSpace U] [MeasurableSpace Ω'] (S : Space k P) (C : Coeffs d m n k U Ω')
    (ν : Measure U) (τ : ℝ) (lam : Measure ℝ) (K L Kb Lb : ℝ≥0 → Ω' → ℝ)
    (Kt : ℝ → ℝ≥0 → Ω' → ℝ) : Prop :=
  IsProbabilityMeasure lam ∧ lam (Set.Icc (-τ) 0)ᶜ = 0 ∧
  IsRate K ∧ IsRate L ∧ IsRate Kb ∧ IsRate Lb ∧ (∀ R : ℝ, 0 < R → IsRate (Kt R)) ∧
  -- (H1)
  (∀ (t : ℝ≥0), ∀ r ∈ S.Γ, ∀ (x x' : SDEState d) (ω' : Ω'),
    ∫⁻ ξ, ‖C.h t r x ω' ξ - C.h t r x' ω' ξ‖ₑ ^ 2 ∂ν < ⊤ ∧
    2 * inner ℝ (x - x') (C.f t r x ω' - C.f t r x' ω') + frobSq (C.g t r x ω' - C.g t r x' ω') +
        (∫⁻ ξ, ‖C.h t r x ω' ξ - C.h t r x' ω' ξ‖ₑ ^ 2 ∂ν).toReal
      ≤ L t ω' * ‖x - x'‖ ^ 2) ∧
  -- (H2)
  (∀ (t : ℝ≥0), ∀ r ∈ S.Γ, ∀ (x : SDEState d) (ω' : Ω'),
    ∫⁻ ξ, ‖C.h t r x ω' ξ‖ₑ ^ 2 ∂ν < ⊤ ∧
    2 * inner ℝ x (C.f t r x ω') + frobSq (C.g t r x ω') + (∫⁻ ξ, ‖C.h t r x ω' ξ‖ₑ ^ 2 ∂ν).toReal
      ≤ K t ω' * (1 + ‖x‖ ^ 2)) ∧
  -- (H3)
  (∀ R : ℝ, 0 < R → ∀ (t : ℝ≥0), ∀ r ∈ S.Γ, ∀ (x : SDEState d) (ω' : Ω'), ‖x‖ ≤ R →
    ∫⁻ ξ, ‖C.h t r x ω' ξ‖ₑ ^ 2 ∂ν < ⊤ ∧
    ‖C.f t r x ω'‖ + frobSq (C.g t r x ω') + (∫⁻ ξ, ‖C.h t r x ω' ξ‖ₑ ^ 2 ∂ν).toReal
      ≤ Kt R t ω') ∧
  -- (H4)
  (∀ (t : ℝ≥0), ∀ r ∈ S.Γ, ∀ r' ∈ S.Γ, ∀ (x x' : SDEState d) (y y' : ℝ → SDEState d) (ω' : Ω'),
    IsCagladOn y (-τ) 0 → IsCagladOn y' (-τ) 0 →
    ‖C.θ t r r' x y ω' - C.θ t r r' x' y' ω'‖ₑ ^ 2 +
        ENNReal.ofReal (frobSq (C.β t r r' x y ω' - C.β t r r' x' y' ω')) +
        ∫⁻ ξ, ‖C.η t r r' x y ω' ξ - C.η t r r' x' y' ω' ξ‖ₑ ^ 2 ∂ν
      ≤ ENNReal.ofReal (Lb t ω') * (‖x - x'‖ₑ ^ 2 + delayInt lam y y')) ∧
  -- (H5)
  (∀ (t : ℝ≥0), ∀ r ∈ S.Γ, ∀ r' ∈ S.Γ, ∀ (x : SDEState d) (y : ℝ → SDEState d) (ω' : Ω'),
    IsCagladOn y (-τ) 0 →
    ‖C.θ t r r' x y ω'‖ₑ ^ 2 + ENNReal.ofReal (frobSq (C.β t r r' x y ω')) +
        ∫⁻ ξ, ‖C.η t r r' x y ω' ξ‖ₑ ^ 2 ∂ν
      ≤ ENNReal.ofReal (Kb t ω') * (1 + ‖x‖ₑ ^ 2 + delayInt lam y 0))

/-- The **driving noise and initial data** of (6) on one filtered probability space
`(Ω, 𝓕, (𝓕_t), ℙ)`: the `m`-dimensional Brownian motion `W`, the `n`-dimensional Brownian motions
`B^α`, all Poisson random measures packed into one random set of atoms `N` on
`[0, ∞) × ((Unit ⊕ Fin P) × U)` (mark `inl ()` is `N`, mark `inr α` is `N^α`), and the initial
paths `ẑ^α`. -/
structure Noise (d m n P : ℕ) (U Ω : Type*) [MeasurableSpace Ω] where
  𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›
  prob : Measure Ω
  W : ℝ≥0 → Ω → SDEState m
  B : Fin P → ℝ≥0 → Ω → SDEState n
  N : Ω → Set (ℝ≥0 × ((Unit ⊕ Fin P) × U))
  z : Fin P → ℝ → Ω → SDEState d

/-- The atoms of the Poisson random measure of mark `o`: `N` for `o = inl ()`, `N^α` for
`o = inr α`. -/
def atoms {Ω : Type*} (N : Ω → Set (ℝ≥0 × ((Unit ⊕ Fin P) × U))) (o : Unit ⊕ Fin P) :
    Ω → Set (ℝ≥0 × U) :=
  fun ω => {p | (p.1, (o, p.2)) ∈ N ω}

/-- `W` is an **`(𝓕_t)`-Brownian motion** in `ℝ^a`: a standard Brownian motion, adapted, with the
whole future increment process after `t` independent of `𝓕_t` (the clauses of the published
`EthierKurtz.IsWeakSDESolution`). -/
def IsFBrownianVec [MeasurableSpace Ω] {a : ℕ} (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (prob : Measure Ω) (W : ℝ≥0 → Ω → SDEState a) : Prop :=
  IsStandardBrownian prob W ∧ (∀ t, Measurable[𝓕 t] (W t)) ∧
    ∀ t, Indep (𝓕 t)
      (MeasurableSpace.comap (fun ω (r : Set.Ici t) => W r.val ω - W t ω) inferInstance) prob

/-- **Standing assumptions on the noise** (p. 2, p. 5, p. 22): `ℙ` is a probability measure; `W`
and every `B^α` are `(𝓕_t)`-Brownian motions whose coordinates are jointly independent; `N` is
one `(𝓕_t)`-Poisson random measure on `[0, ∞) × ((Unit ⊕ Fin P) × U)` with intensity
`dt ⊗ (counting ⊗ ν)`, i.e. `N, N^1, …, N^P` are independent Poisson random measures with
intensity `dt ⊗ ν`; every `ẑ^α` has càdlàg paths on `[−τ, 0]`, is `𝓕_0`-measurable at each time,
and lies in `L²(Ω; Càdlàg([−τ, 0]; ℝ^d))` with the supremum norm. -/
def IsNoise [MeasurableSpace U] [MeasurableSpace Ω] (τ : ℝ) (ν : Measure U)
    (Nz : Noise d m n P U Ω) : Prop :=
  IsProbabilityMeasure Nz.prob ∧
  IsFBrownianVec Nz.𝓕 Nz.prob Nz.W ∧ (∀ α, IsFBrownianVec Nz.𝓕 Nz.prob (Nz.B α)) ∧
  iIndepFun (Sum.elim (fun (j : Fin m) ω (t : ℝ≥0) => Nz.W t ω j)
    (fun (q : Fin P × Fin n) ω (t : ℝ≥0) => Nz.B q.1 t ω q.2)) Nz.prob ∧
  JacodTodorov10.LLN.IsFPoisson Nz.𝓕 Nz.prob (Measure.count.prod ν) Nz.N ∧
  (∀ α ω, IsCadlagOn (fun u => Nz.z α u ω) (-τ) 0) ∧
  (∀ α, ∀ u ∈ Set.Icc (-τ) 0, Measurable[Nz.𝓕 0] (Nz.z α u)) ∧
  ∀ α, ∫⁻ ω, ⨆ u ∈ Set.Icc (-τ) 0, ‖Nz.z α u ω‖ₑ ^ 2 ∂Nz.prob < ⊤

/-- The **left-limit process** `X^r_{s−}` (with the convention of `Function.leftLim`). -/
noncomputable def leftProc (X : Pos k → ℝ → Ω → SDEState d) (r : Pos k) (s : ℝ) (ω : Ω) :
    SDEState d :=
  Function.leftLim (fun v => X r v ω) s

/-- The **mean-field drift** `∫_{Γ_α} 𝔼̃[θ(s, r, r', x, X̃^{r'}_{seg}, ω')] 𝓡(dr')` of (6), where the
segment of the copy at time `s` is `sg (path of X^{r'}) s`. The copy `X̃` enters only through its
law, so the expectation is taken over the law of `X` itself. -/
noncomputable def meanθ [MeasurableSpace Ω] (S : Space k P) (C : Coeffs d m n k U Ω')
    (prob : Measure Ω) (sg : (ℝ → SDEState d) → ℝ≥0 → ℝ → SDEState d)
    (X : Pos k → ℝ → Ω → SDEState d) (α : Fin P) (s : ℝ≥0) (r : Pos k) (x : SDEState d)
    (ω' : Ω') : SDEState d :=
  ∫ r' in S.Γα α, ∫ ω, C.θ s r r' x (sg (fun v => X r' v ω) s) ω' ∂prob ∂S.R

/-- The **mean-field diffusion** matrix `∫_{Γ_α} 𝔼̃[β(s, r, r', x, X̃^{r'}_{seg}, ω')] 𝓡(dr')`,
integrated entrywise. -/
noncomputable def meanβ [MeasurableSpace Ω] (S : Space k P) (C : Coeffs d m n k U Ω')
    (prob : Measure Ω) (sg : (ℝ → SDEState d) → ℝ≥0 → ℝ → SDEState d)
    (X : Pos k → ℝ → Ω → SDEState d) (α : Fin P) (s : ℝ≥0) (r : Pos k) (x : SDEState d)
    (ω' : Ω') : Matrix (Fin d) (Fin n) ℝ :=
  Matrix.of fun i j =>
    ∫ r' in S.Γα α, ∫ ω, C.β s r r' x (sg (fun v => X r' v ω) s) ω' i j ∂prob ∂S.R

/-- The **mean-field jump coefficient** `∫_{Γ_α} 𝔼̃[η(s, r, r', x, X̃^{r'}_{seg}, ω', ξ)] 𝓡(dr')`. -/
noncomputable def meanη [MeasurableSpace Ω] (S : Space k P) (C : Coeffs d m n k U Ω')
    (prob : Measure Ω) (sg : (ℝ → SDEState d) → ℝ≥0 → ℝ → SDEState d)
    (X : Pos k → ℝ → Ω → SDEState d) (α : Fin P) (s : ℝ≥0) (r : Pos k) (x : SDEState d)
    (ω' : Ω') (ξ : U) : SDEState d :=
  ∫ r' in S.Γα α, ∫ ω, C.η s r r' x (sg (fun v => X r' v ω) s) ω' ξ ∂prob ∂S.R

/-- The **mean-field integrands are integrable** on `Γ_α × Ω` w.r.t. `𝓡|_{Γ_α} ⊗ ℙ` at every time
`s ≤ T`, position `r ∈ Γ` and state `x` (for `η`, for `ν`-a.e. mark `ξ`), so that the expectations in
(6) are genuine (p. 6: "a solution to (6) requires in particular the measurability of `X̃` w.r.t.
`r'`, since otherwise the integrals … are not well-defined"). -/
def MFIntegrable [MeasurableSpace U] [MeasurableSpace Ω] (S : Space k P)
    (C : Coeffs d m n k U Ω') (ν : Measure U) (prob : Measure Ω)
    (sg : (ℝ → SDEState d) → ℝ≥0 → ℝ → SDEState d) (ω' : Ω') (T : ℝ)
    (X : Pos k → ℝ → Ω → SDEState d) : Prop :=
  ∀ (α : Fin P) (s : ℝ≥0), (s : ℝ) ≤ T → ∀ r ∈ S.Γ, ∀ x : SDEState d,
    Integrable (fun p : Pos k × Ω => C.θ s r p.1 x (sg (fun v => X p.1 v p.2) s) ω')
        ((S.R.restrict (S.Γα α)).prod prob) ∧
    (∀ i j, Integrable (fun p : Pos k × Ω => C.β s r p.1 x (sg (fun v => X p.1 v p.2) s) ω' i j)
        ((S.R.restrict (S.Γα α)).prod prob)) ∧
    ∀ᵐ ξ ∂ν, Integrable (fun p : Pos k × Ω => C.η s r p.1 x (sg (fun v => X p.1 v p.2) s) ω' ξ)
        ((S.R.restrict (S.Γα α)).prod prob)

/-- The cut-off `1_{s ≤ T}` applied to every stochastic integrand: the solution on `[−τ, T]` says
nothing after `T`, and the published integral relations quantify over all times. -/
noncomputable def cutT (T : ℝ) (s : ℝ≥0) : ℝ := if (s : ℝ) ≤ T then 1 else 0

/-- The **integral form of (6)** (equivalently of the scheme (13)) at one position `r ∈ Γ_ζ`, for a
segment map `sg`: there are processes `Ig, Ih, Iβ, Iη` that are the stochastic integrals
`∫ g dW` (coordinate `i` is `∑ⱼ ∫ gᵢⱼ dWʲ`, each by the published `HasBrownianItoIntegral`),
`∫∫ h dÑ` (coordinatewise by the published `HasCompInt` on the atoms of mark `inl ()`),
`∫ (mean β) dB^α` and `∫∫ (mean η) dÑ^α`, all integrands evaluated at `X^r_{s−}` and cut off after
`T`; the drift integrands are integrable on `[0, T]`; and for every `t ∈ [0, T]`, almost surely,
`X^r_t = ẑ^ζ_0 + ∫_0^t f ds + ∫_0^t g dW + ∫_0^t∫_U h dÑ + ∑_α (∫_0^t (mean θ) ds + ∫_0^t (mean β) dB^α
+ ∫_0^t∫_U (mean η) dÑ^α)`, coordinatewise. -/
def IntegralForm [MeasurableSpace U] [MeasurableSpace Ω] (S : Space k P)
    (C : Coeffs d m n k U Ω') (ν : Measure U) (Nz : Noise d m n P U Ω)
    (sg : (ℝ → SDEState d) → ℝ≥0 → ℝ → SDEState d) (ω' : Ω') (T : ℝ)
    (X : Pos k → ℝ → Ω → SDEState d) (ζ : Fin P) (r : Pos k) : Prop :=
  ∃ (Ig : Fin d → Fin m → ℝ≥0 → Ω → ℝ) (Ih : Fin d → ℝ≥0 → Ω → ℝ)
    (Iβ : Fin P → Fin d → Fin n → ℝ≥0 → Ω → ℝ) (Iη : Fin P → Fin d → ℝ≥0 → Ω → ℝ),
    (∀ i j, HasBrownianItoIntegral Nz.prob (fun t => Nz.𝓕 t) (fun t ω => Nz.W t ω j)
      (fun t ω => cutT T t * C.g t r (leftProc X r t ω) ω' i j) (Ig i j)) ∧
    (∀ i, JacodTodorov10.LLN.HasCompInt Nz.prob ν (atoms Nz.N (Sum.inl ()))
      (fun ω t ξ => cutT T t * C.h t r (leftProc X r t ω) ω' ξ i) (Ih i)) ∧
    (∀ α i j, HasBrownianItoIntegral Nz.prob (fun t => Nz.𝓕 t) (fun t ω => Nz.B α t ω j)
      (fun t ω => cutT T t * meanβ S C Nz.prob sg X α t r (leftProc X r t ω) ω' i j)
      (Iβ α i j)) ∧
    (∀ α i, JacodTodorov10.LLN.HasCompInt Nz.prob ν (atoms Nz.N (Sum.inr α))
      (fun ω t ξ => cutT T t * meanη S C Nz.prob sg X α t r (leftProc X r t ω) ω' ξ i)
      (Iη α i)) ∧
    (∀ ω, IntervalIntegrable
      (fun s : ℝ => C.f s.toNNReal r (leftProc X r s ω) ω') volume 0 T) ∧
    (∀ α ω, IntervalIntegrable
      (fun s : ℝ => meanθ S C Nz.prob sg X α s.toNNReal r (leftProc X r s ω) ω') volume 0 T) ∧
    ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ᵐ ω ∂Nz.prob, ∀ i,
      X r t ω i = Nz.z ζ 0 ω i
        + (∫ s in (0 : ℝ)..(t : ℝ), C.f s.toNNReal r (leftProc X r s ω) ω') i
        + ∑ j, Ig i j t ω + Ih i t ω
        + ∑ α, ((∫ s in (0 : ℝ)..(t : ℝ),
              meanθ S C Nz.prob sg X α s.toNNReal r (leftProc X r s ω) ω') i
            + ∑ j, Iβ α i j t ω + Iη α i t ω)

/-- `X : Γ × [−τ, T] × Ω → ℝ^d` **solves (6)-type dynamics on `[−τ, T]`** at disorder `ω'`, with the
mean-field segments given by `sg`, the integral identity being required at the positions of `G`:
1. `X^r_t = ẑ^ζ_t` for `r ∈ Γ_ζ`, `t ∈ [−τ, 0]`;
2. every path `t ↦ X^r_t(ω)`, `r ∈ Γ`, is càdlàg on `[−τ, T]`;
3. `X^r_t` is `𝓕_t`-measurable for `t ∈ [0, T]`;
4. `(r, ω) ↦ X^r_t(ω)` is jointly measurable for each `t ∈ [−τ, T]`;
5. the mean-field integrands are integrable (`MFIntegrable`);
6. the integral form holds at every `r ∈ Γ_ζ ∩ G`. -/
def SolvesOn [MeasurableSpace U] [MeasurableSpace Ω] (S : Space k P) (C : Coeffs d m n k U Ω')
    (ν : Measure U) (Nz : Noise d m n P U Ω) (τ : ℝ)
    (sg : (ℝ → SDEState d) → ℝ≥0 → ℝ → SDEState d) (ω' : Ω') (T : ℝ) (G : Set (Pos k))
    (X : Pos k → ℝ → Ω → SDEState d) : Prop :=
  (∀ ζ, ∀ r ∈ S.Γα ζ, ∀ t ∈ Set.Icc (-τ) 0, ∀ ω, X r t ω = Nz.z ζ t ω) ∧
  (∀ r ∈ S.Γ, ∀ ω, IsCadlagOn (fun t => X r t ω) (-τ) T) ∧
  (∀ r ∈ S.Γ, ∀ t : ℝ≥0, (t : ℝ) ≤ T → Measurable[Nz.𝓕 t] (X r t)) ∧
  (∀ t ∈ Set.Icc (-τ) T, Measurable (fun p : Pos k × Ω => X p.1 t p.2)) ∧
  MFIntegrable S C ν Nz.prob sg ω' T X ∧
  ∀ ζ, ∀ r ∈ S.Γα ζ ∩ G, IntegralForm S C ν Nz sg ω' T X ζ r

/-- The segment map of (6): at time `s` the copy enters through `X̃^{r'}_{(s−τ)⁻:s⁻}`. -/
noncomputable def segMap (x : ℝ → SDEState d) (s : ℝ≥0) : ℝ → SDEState d :=
  seg x (s : ℝ)

/-- A **strong solution of (6) on `[−τ, T]`** at disorder `ω'` (p. 5): `SolvesOn` with the true
path segments `X̃^{r'}_{(s−τ)⁻:s⁻}` in the mean-field terms and the integral identity at every
`r ∈ Γ`. -/
def IsStrongSol6 [MeasurableSpace U] [MeasurableSpace Ω] (S : Space k P)
    (C : Coeffs d m n k U Ω') (ν : Measure U) (Nz : Noise d m n P U Ω) (τ : ℝ) (ω' : Ω')
    (T : ℝ) (X : Pos k → ℝ → Ω → SDEState d) : Prop :=
  SolvesOn S C ν Nz τ segMap ω' T Set.univ X

/-- The class `L^∞([−τ, T], dt; L²(Ω × Γ, ℙ ⊗ 𝓡; ℝ^d))` of Theorem 1.5 and Lemma 1.4, as a bound
`∫_Γ 𝔼|X^r_t|² 𝓡(dr) ≤ c < ∞` for every `t ∈ [−τ, T]`. -/
def InClass [MeasurableSpace Ω] (S : Space k P) (prob : Measure Ω) (τ T : ℝ)
    (X : Pos k → ℝ → Ω → SDEState d) : Prop :=
  ∃ c : ℝ≥0∞, c < ⊤ ∧ ∀ t ∈ Set.Icc (-τ) T, ∫⁻ r, ∫⁻ ω, ‖X r t ω‖ₑ ^ 2 ∂prob ∂S.R ≤ c

/-- The constant `C₁(t, ω')` of (7), p. 6:
`C₁(t, ω') = (sup_{u ∈ [−τ, 0], 1 ≤ ζ ≤ P} 𝔼|ẑ^ζ(u)|² + 1) · exp(∫_0^t (K_s(ω') + 3P K̄_s(ω') + P) ds)`,
in `ℝ≥0∞`. -/
noncomputable def C1 [MeasurableSpace Ω] (Nz : Noise d m n P U Ω) (τ : ℝ)
    (K Kb : ℝ≥0 → Ω' → ℝ) (t : ℝ) (ω' : Ω') : ℝ≥0∞ :=
  ((⨆ u ∈ Set.Icc (-τ) 0, ⨆ ζ : Fin P, ∫⁻ ω, ‖Nz.z ζ u ω‖ₑ ^ 2 ∂Nz.prob) + 1) *
    ENNReal.ofReal (Real.exp (∫ s in (0 : ℝ)..t,
      (K s.toNNReal ω' + 3 * (P : ℝ) * Kb s.toNNReal ω' + (P : ℝ))))

end NeuroMV.WellPosed


