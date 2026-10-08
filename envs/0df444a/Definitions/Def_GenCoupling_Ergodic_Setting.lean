-- Prove2me | Definitions.Def_GenCoupling_Ergodic_Setting
-- name    : GenCoupling_Ergodic_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:04.287034+00:00
-- url     : https://prove2.me/theorems/f4a4e6f7-a56e-40fc-a5fc-f25dcb2cff7c
-- title:
--   §2.1–2.2, pp. 4–7 — Markov semigroup, Feller, distance-like, premetric, couplings, W_d, d_N (2.6), Definitions 2.1–2.2, Lyapunov condition (2.2), H_φ (2.1), Assumptions A, B1, B2
-- statement:
--   These are the objects of §2 of Butkovsky, Kulik and Scheutzow. Throughout, $(E,\rho)$ is a Polish space with its Borel $\sigma$-field $\mathcal E$, and time is $t\in\mathbb R_+$.
--
--   1. **Markov semigroup.** A family $\{P_t\}_{t\ge 0}$ of Markov kernels on $E$ is a *Markov transition function* if $P_0(x,\cdot)=\delta_x$, the Chapman–Kolmogorov identity $P_{s+t}(x,A)=\int_E P_t(y,A)\,P_s(x,dy)$ holds, and $s\mapsto P_s(x,A)$ is measurable for every $x\in E$ and $A\in\mathcal E$. For $f\ge 0$ write $P_tf(x)=\int_E f(y)\,P_t(x,dy)\in[0,\infty]$.
--   2. **Feller.** The semigroup is Feller if $x\mapsto P_tf(x)$ is continuous for every bounded continuous $f:E\to\mathbb R$ and every $t\ge 0$.
--   3. **Distance-like function.** $d:E\times E\to\mathbb R_+$ is distance-like if it is symmetric, lower semicontinuous, and $d(x,y)=0\iff x=y$.
--   4. **Premetric.** $\theta:E\times E\to\mathbb R_+$ is a premetric if it is lower semicontinuous and $\theta(x,y)=0\iff x=y$; it need not be symmetric.
--   5. **Couplings and coupling distance.** $\mathcal C(\mu,\nu)$ is the set of measures on $E\times E$ with marginals $\mu$ and $\nu$, and
--   $$W_d(\mu,\nu)=\inf_{\lambda\in\mathcal C(\mu,\nu)}\int_{E\times E} d(x,y)\,\lambda(dx,dy)\in[0,\infty].$$
--   6. **The distance $d_N$** (2.6): for $N>0$, $d_N(x,y)=N\theta(x,y)\wedge N\theta(y,x)\wedge 1$.
--   7. **Contracting** (Definition 2.1): a distance-like $d\le 1$ is contracting for $P_t$ if there is $\alpha<1$ with $W_d(P_t(x,\cdot),P_t(y,\cdot))\le\alpha\, d(x,y)$ whenever $d(x,y)<1$.
--   8. **$d$-small** (Definition 2.2): $B\subset E$ is $d$-small for $P_t$ if $\sup_{x,y\in B}W_d(P_t(x,\cdot),P_t(y,\cdot))\le 1-\varepsilon$ for some $\varepsilon>0$.
--   9. **Lyapunov condition** (condition 1 of Proposition 2.1): $\varphi:\mathbb R_+\to\mathbb R_+$ is concave, differentiable, non-decreasing with $\varphi(u)\to\infty$, $\varphi(0)=0$, $K>0$, and for all $t\ge 0$, $x\in E$,
--   $$P_tV(x)\le V(x)-\int_0^t P_s(\varphi\circ V)(x)\,ds+Kt.\qquad(2.2)$$
--   10. **$H_\varphi$** (2.1): $H_\varphi(x)=\int_1^x \frac{du}{\varphi(u)}$ for $x\ge 1$.
--   11. **Assumption A.** $r:\mathbb R_+\to\mathbb R_+$ is non-increasing with $r(t)\to 0$, $L:\mathbb R_+\to\mathbb R_+$ is locally bounded, and for all $x,y\in E$ there are processes $X^{x,y},Y^{x,y}$ with $\mathrm{Law}(X^{x,y}_t)=P_t(x,\cdot)$, $d_{TV}(\mathrm{Law}(Y^{x,y}_t),P_t(y,\cdot))\le L(t)\theta(x,y)$ and $\mathsf E\,\theta(X^{x,y}_t,Y^{x,y}_t)\le r(t)\theta(x,y)$ for all $t\ge 0$.
--   12. **Assumption B1** (for $B$ and $t_0$): $t_0>0$ and for every $\varepsilon>0$ there is $D\in\mathcal E$ with $\inf_{x\in B}P_{t_0}(x,D)>0$ and $\sup_{x,y\in D}\theta(x,y)\le\varepsilon$.
--   13. **Assumption B2** (for $B$, $R$, $\varepsilon$): $R:\mathbb R_+\to\mathbb R_+$ is non-increasing with $R(t)\to0$, $\varepsilon>0$, and for all $x,y\in B$ there are processes with $\mathrm{Law}(X^{x,y}_t)=P_t(x,\cdot)$, $d_{TV}(\mathrm{Law}(Y^{x,y}_t),P_t(y,\cdot))\le 1-\varepsilon$ (2.5) and $\mathsf E\,\theta(X^{x,y}_t,Y^{x,y}_t)\le R(t)$ for all $t\ge0$.
--
--   The pair $(X^{x,y},Y^{x,y})$ of Assumptions A and B2 is a *generalized coupling*: its first component has the true law, while the second is only close in law to the process started at $y$. These are the hypotheses of every theorem of the mission.
--
--   **Formalization Note** Time is `ℝ≥0` and $P$ is a map `ℝ≥0 → Kernel E E`. Measurability of $s\mapsto P_s(x,A)$ is an addition: the $ds$-integral of (2.2) presupposes it. (2.2) is stated without subtraction, $P_tV(x)+\int_0^tP_s(\varphi\circ V)(x)\,ds\le V(x)+Kt$ in $[0,\infty]$, which is equivalent because the right side is finite. All expectations and $W_d$ are lower Lebesgue integrals of nonnegative functions in $[0,\infty]$, never Bochner integrals. A pair of processes is represented by its joint law $\Gamma$ on the path space $(\mathbb R_+\to E)\times(\mathbb R_+\to E)$ with the product $\sigma$-algebra; $\mathrm{Law}(X^{x,y})=\mathsf P_x$ is read through its one-dimensional marginals $\mathrm{Law}(X^{x,y}_t)=P_t(x,\cdot)$, which is weaker than the page (and is all the paper's proofs use). $\varphi$ is a function `ℝ → ℝ` whose properties are required on $[0,\infty)$ only. $d_{TV}$ is the published definition `MarkovChainCLT.tvDist`, $\sup_A|\mu(A)-\nu(A)|$ with no factor 2. In Definition 2.1 the requirements "distance-like" and "bounded by 1" are part of the predicate `IsContracting`.
-- source:
--   Butkovsky, Kulik and Scheutzow, Generalized couplings and ergodic rates for SPDEs and other Markov models, arXiv:1806.00395v3, pp. 4–7, §2.1 (Markov transition function, distance-like, C(µ,ν), W_d, d_TV, (2.1), (2.2), Definitions 2.1–2.2) and §2.2 (premetric, Assumptions A, B1, B2, (2.6))

import Mathlib
import Definitions.Def_TotalVariationDist

namespace GenCoupling.Ergodic

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal NNReal

variable {E : Type*} [MeasurableSpace E]

/-- §2.1, p. 4: a **Markov transition function** `{P_t}_{t ∈ ℝ₊}`: every `P_t` is a Markov
kernel, `P_0(x, ·) = δ_x`, the Chapman–Kolmogorov identity `P_{s+t} = P_s P_t` holds, and
(disclosed addition) `s ↦ P_s(x, A)` is measurable for every `x` and measurable `A`, which the
`ds`-integral in (2.2) presupposes. -/
def IsMarkovSemigroup (P : ℝ≥0 → Kernel E E) : Prop :=
  (∀ t, IsMarkovKernel (P t)) ∧
  P 0 = Kernel.id ∧
  (∀ s t, P (s + t) = P t ∘ₖ P s) ∧
  (∀ x A, MeasurableSet A → Measurable (fun s : ℝ≥0 => P s x A))

/-- The (weak) **Feller** property: `x ↦ P_t f(x) = ∫ f(y) P_t(x, dy)` is continuous for every
bounded continuous `f` and every `t`. -/
def IsFeller [TopologicalSpace E] (P : ℝ≥0 → Kernel E E) : Prop :=
  ∀ (t : ℝ≥0) (f : E →ᵇ ℝ), Continuous (fun x => ∫ y, f y ∂(P t x))

/-- §2.1, p. 4: `d : E × E → ℝ₊` is **distance-like**: symmetric, lower semicontinuous, and
`d(x, y) = 0 ⇔ x = y`. -/
def IsDistanceLike [TopologicalSpace E] (d : E → E → ℝ) : Prop :=
  (∀ x y, 0 ≤ d x y) ∧ (∀ x y, d x y = d y x) ∧
  LowerSemicontinuous (fun p : E × E => d p.1 p.2) ∧ (∀ x y, d x y = 0 ↔ x = y)

/-- §2.2, p. 6: `θ : E × E → ℝ₊` is a **premetric**: lower semicontinuous and
`θ(x, y) = 0 ⇔ x = y` (not necessarily symmetric). -/
def IsPremetric [TopologicalSpace E] (θ : E → E → ℝ) : Prop :=
  (∀ x y, 0 ≤ θ x y) ∧ LowerSemicontinuous (fun p : E × E => θ p.1 p.2) ∧
  (∀ x y, θ x y = 0 ↔ x = y)

/-- §2.1, p. 4: `C(μ, ν)`, the **couplings** of `μ` and `ν`: measures on `E × E` with marginals
`μ` and `ν` (probability measures whenever `μ` is). -/
def couplings (μ ν : Measure E) : Set (Measure (E × E)) :=
  {γ | γ.map Prod.fst = μ ∧ γ.map Prod.snd = ν}

/-- §2.1, p. 4: the **coupling distance** `W_d(μ, ν) = inf_{λ ∈ C(μ,ν)} ∫ d dλ`, valued in
`[0, ∞]`. -/
noncomputable def W (d : E → E → ℝ) (μ ν : Measure E) : ℝ≥0∞ :=
  ⨅ γ ∈ couplings μ ν, ∫⁻ p, ENNReal.ofReal (d p.1 p.2) ∂γ

/-- (2.6), p. 7: `d_N(x, y) = Nθ(x, y) ∧ Nθ(y, x) ∧ 1`. -/
noncomputable def dN (θ : E → E → ℝ) (N : ℝ) (x y : E) : ℝ :=
  min (min (N * θ x y) (N * θ y x)) 1

/-- Definition 2.1, p. 6: a distance-like function `d` bounded by `1` is **contracting** for
`P_t` if there is `α < 1` with `W_d(P_t(x, ·), P_t(y, ·)) ≤ α d(x, y)` whenever `d(x, y) < 1`. -/
def IsContracting [TopologicalSpace E] (P : ℝ≥0 → Kernel E E) (t : ℝ≥0) (d : E → E → ℝ) :
    Prop :=
  IsDistanceLike d ∧ (∀ x y, d x y ≤ 1) ∧
  ∃ α : ℝ, α < 1 ∧ ∀ x y, d x y < 1 → W d (P t x) (P t y) ≤ ENNReal.ofReal (α * d x y)

/-- Definition 2.2, p. 6: `B ⊆ E` is **`d`-small** for `P_t` if for some `ε > 0`,
`sup_{x, y ∈ B} W_d(P_t(x, ·), P_t(y, ·)) ≤ 1 - ε`. -/
def IsSmall (P : ℝ≥0 → Kernel E E) (t : ℝ≥0) (d : E → E → ℝ) (B : Set E) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ B, ∀ y ∈ B, W d (P t x) (P t y) ≤ ENNReal.ofReal (1 - ε)

/-- `P_t f(x) = ∫ f(y) P_t(x, dy)` for a function `f ≥ 0`, as an extended nonnegative real. -/
noncomputable def PV (P : ℝ≥0 → Kernel E E) (t : ℝ≥0) (f : E → ℝ) (x : E) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (f y) ∂(P t x)

/-- Condition 1 of Proposition 2.1, p. 5: `φ : ℝ₊ → ℝ₊` concave, differentiable, increasing to
infinity, `φ(0) = 0`, `K > 0`, and the **Lyapunov inequality** (2.2)
`P_tV(x) ≤ V(x) - ∫_0^t P_s(φ ∘ V)(x) ds + Kt` for all `t ≥ 0`, `x`, written without
subtraction: `P_tV(x) + ∫_0^t P_s(φ ∘ V)(x) ds ≤ V(x) + Kt` in `[0, ∞]`. -/
def LyapunovCondition (P : ℝ≥0 → Kernel E E) (V : E → ℝ) (φ : ℝ → ℝ) (K : ℝ) : Prop :=
  φ 0 = 0 ∧ (∀ u, 0 ≤ u → 0 ≤ φ u) ∧ ConcaveOn ℝ (Set.Ici 0) φ ∧
  DifferentiableOn ℝ φ (Set.Ici 0) ∧ MonotoneOn φ (Set.Ici 0) ∧ Tendsto φ atTop atTop ∧
  0 < K ∧
  ∀ (t : ℝ≥0) (x : E),
    PV P t V x + ∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ), PV P s.toNNReal (fun y => φ (V y)) x
      ≤ ENNReal.ofReal (V x) + ENNReal.ofReal (K * (t : ℝ))

/-- (2.1), p. 5: `H_φ(x) = ∫_1^x du / φ(u)`, used for `x ≥ 1`. -/
noncomputable def H (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ u in (1 : ℝ)..x, 1 / φ u

/-- Assumption A, pp. 6–7. `r : ℝ₊ → ℝ₊` non-increasing with `r(t) → 0`, `L : ℝ₊ → ℝ₊` locally
bounded, and for all `x, y` a pair of processes `(X^{x,y}, Y^{x,y})`, given by its joint law `Γ`
on path space, with `Law(X^{x,y}_t) = P_t(x, ·)`,
`d_TV(Law(Y^{x,y}_t), P_t(y, ·)) ≤ L(t)θ(x, y)` and `E θ(X^{x,y}_t, Y^{x,y}_t) ≤ r(t)θ(x, y)` for
all `t ≥ 0`. -/
def AssumptionA (θ : E → E → ℝ) (P : ℝ≥0 → Kernel E E) (r L : ℝ≥0 → ℝ) : Prop :=
  (∀ t, 0 ≤ r t) ∧ Antitone r ∧ Tendsto r atTop (𝓝 0) ∧
  (∀ t, 0 ≤ L t) ∧ (∀ T : ℝ≥0, BddAbove (L '' Set.Icc 0 T)) ∧
  ∀ x y : E, ∃ Γ : Measure ((ℝ≥0 → E) × (ℝ≥0 → E)), IsProbabilityMeasure Γ ∧
    (∀ t, Γ.map (fun ω => ω.1 t) = P t x) ∧
    (∀ t, MarkovChainCLT.tvDist (Γ.map (fun ω => ω.2 t)) (P t y) ≤ L t * θ x y) ∧
    (∀ t, ∫⁻ ω, ENNReal.ofReal (θ (ω.1 t) (ω.2 t)) ∂Γ ≤ ENNReal.ofReal (r t * θ x y))

/-- Assumption B1, p. 7: `t₀ > 0` and for every `ε > 0` a measurable `D` with
`inf_{x ∈ B} P_{t₀}(x, D) > 0` and `sup_{x, y ∈ D} θ(x, y) ≤ ε`. -/
def AssumptionB1 (θ : E → E → ℝ) (P : ℝ≥0 → Kernel E E) (B : Set E) (t₀ : ℝ≥0) : Prop :=
  0 < t₀ ∧ ∀ ε : ℝ, 0 < ε → ∃ D : Set E, MeasurableSet D ∧
    0 < (⨅ x ∈ B, P t₀ x D) ∧ ∀ x ∈ D, ∀ y ∈ D, θ x y ≤ ε

/-- Assumption B2, p. 7. `R : ℝ₊ → ℝ₊` non-increasing with `R(t) → 0`, `ε > 0`, and for all
`x, y ∈ B` a pair of processes (joint law `Γ` on path space) with `Law(X^{x,y}_t) = P_t(x, ·)`,
(2.5) `d_TV(Law(Y^{x,y}_t), P_t(y, ·)) ≤ 1 - ε` and `E θ(X^{x,y}_t, Y^{x,y}_t) ≤ R(t)` for all
`t ≥ 0`. -/
def AssumptionB2 (θ : E → E → ℝ) (P : ℝ≥0 → Kernel E E) (B : Set E) (R : ℝ≥0 → ℝ) (ε : ℝ) :
    Prop :=
  (∀ t, 0 ≤ R t) ∧ Antitone R ∧ Tendsto R atTop (𝓝 0) ∧ 0 < ε ∧
  ∀ x ∈ B, ∀ y ∈ B, ∃ Γ : Measure ((ℝ≥0 → E) × (ℝ≥0 → E)), IsProbabilityMeasure Γ ∧
    (∀ t, Γ.map (fun ω => ω.1 t) = P t x) ∧
    (∀ t, MarkovChainCLT.tvDist (Γ.map (fun ω => ω.2 t)) (P t y) ≤ 1 - ε) ∧
    (∀ t, ∫⁻ ω, ENNReal.ofReal (θ (ω.1 t) (ω.2 t)) ∂Γ ≤ ENNReal.ofReal (R t))

end GenCoupling.Ergodic


