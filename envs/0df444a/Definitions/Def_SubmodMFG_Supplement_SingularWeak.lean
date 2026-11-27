-- Prove2me | Definitions.Def_SubmodMFG_Supplement_SingularWeak
-- name    : SubmodMFG_Supplement_SingularWeak
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:22:07.200859+00:00
-- url     : https://prove2.me/theorems/c79a6300-f930-43d4-a11c-9ee220c46782
-- title:
--   The weak-formulation singular-control MFG of §5.2
-- statement:
--   Fix $T>0$, $\sigma\ge0$, a Lipschitz $b:[0,T]\times\mathbb R\to\mathbb R$, $\nu_0\in\mathcal P(\mathbb R)$ with $\int|y|^p\,d\nu_0<\infty$, and $f,g,c$ satisfying Assumption 5.1 with exponent $p$; $\pi=dt+\delta_T$ on $[0,T]$.
--
--   1. An **admissible singular control** (Definition 5.5) is $\rho=(\Omega,\mathcal F,\mathbb F,P,x_0,W,\xi)$: a filtered probability space with the usual conditions, an $\mathcal F_0$-measurable $x_0$ with law $\nu_0$, a standard $\mathbb F$-Brownian motion $W$ and an adapted nondecreasing càdlàg $\xi\ge0$; its state $X^\rho$ solves $X_t=x_0+\int_0^tb(s,X_s)\,ds+\sigma W_t+\xi_t$ (5.16).
--   2. For a measurable flow of probabilities $\mu$, $J(\rho,\mu)=E^P\big[\int_0^Tf(t,X^\rho_t,\mu_t)\,dt+g(X^\rho_T,\mu_T)+\int_{[0,T]}c_t\,d\xi_t\big]$; $\rho$ is optimal for $\mu$ if $J(\rho,\mu)=\inf J(\cdot,\mu)$.
--   3. $\mu$ is an **MFG equilibrium** (Definition 5.6) if some $\rho$ is optimal for $\mu$ and $\mu_t=P\circ(X^\rho_t)^{-1}$ for every $t$.
--   4. For $\mu^{Min},\mu^{Max}\in\mathcal P(\mathbb R)$ with (5.19), $\mu^{Min}\le_{st}P\circ(X^\rho_t)^{-1}\le_{st}\mu^{Max}$ for all $t$ and all optimal $\rho$, the lattice $L$ consists of the measurable flows with $\mu_t\in[\mu^{Min},\mu^{Max}]$ for $\pi$-a.e. $t$, ordered $\pi$-a.e. by $\le_{st}$; $R(\mu)=\{P\circ(X^\rho)^{-1}:\rho\text{ optimal for }\mu\}$.
--   5. **Control rules** $\nu^\rho=P\circ(x_0,W,X^\rho,\xi)^{-1}$ on the canonical space; $E$ is their set, $E^M$ the rules of controls with $E^P[|X^\rho_t|^p+\xi_T^p]\le M$ (5.18), $J(\nu^\rho,\mu):=J(\rho,\mu)$ and $p(\nu^\rho)=P\circ(X^\rho)^{-1}$.
--
--   **Formalization Note** Sample spaces range over `Type`. The state is carried as part of the control (it is the unique solution of (5.16)). Paths on the canonical space are functions on $[0,T]$ with the product σ-algebra (the Borel σ-algebras of $C$ and $D$ are the cylinder ones). Elements of $L$ are representatives; $R(\mu)$ and the equilibrium set consist of the elements agreeing $\pi$-a.e. with the marginal-law flows.
-- source:
--   Dianetti, Ferrari, Fischer, Nendel, A Unifying Framework for Submodular Mean Field Games, arXiv:2201.07850v1, §5.2.1–5.2.2, pp.20–21 (Definitions 5.5, 5.6, (5.16)–(5.19))

import Mathlib
import Definitions.Def_SubmodMFG_Supplement_SubProb
import Definitions.Def_RepairSched_UsualConditions
import Definitions.Def_SubmodMFG_Supplement_Processes
import Definitions.Def_SubmodMFG_Supplement_SingularCommon

open MeasureTheory ProbabilityTheory

namespace SubmodMFG.Supplement

/-- **Data of the nonconvex singular-control MFG without common noise of §5.2.**
Dianetti, Ferrari, Fischer, Nendel, *A Unifying Framework for Submodular Mean Field Games*,
arXiv:2201.07850v1, §5.2.1, p.20: a horizon `T`, a constant `σ ≥ 0`, a Lipschitz drift
`b : [0, T] × ℝ → ℝ`, an initial law `ν₀ ∈ P(ℝ)` with `∫|y|^p dν₀ < ∞`, and the costs `f, g, c` of
§5 (p.15) satisfying Assumption 5.1 with exponent `p`. The hypotheses are `Standing`. -/
structure SingWeakModel where
  /-- Horizon `T`. -/
  T : ℝ
  /-- Volatility `σ`. -/
  σ : ℝ
  /-- Drift `b(t, x)`. -/
  b : ℝ → ℝ → ℝ
  /-- Initial law `ν₀`. -/
  ν₀ : SubProb
  /-- The exponent `p` of Assumption 5.1. -/
  p : ℝ
  /-- Running cost `f(t, x, µ)`. -/
  f : ℝ → ℝ → SubProb → ℝ
  /-- Terminal cost `g(x, µ)`. -/
  g : ℝ → SubProb → ℝ
  /-- Cost of control `c(t)`. -/
  c : ℝ → ℝ

namespace SingWeakModel

variable (D : SingWeakModel)

/-- `π = dt + δ_T` on `[0, T]` (p.21, as in (5.1)). -/
noncomputable def π : Measure ℝ := volume.restrict (Set.Icc 0 D.T) + Measure.dirac D.T

/-- **Standing assumptions of §5.2** (pp.15–16, 20): `T > 0` (§5 fixes `T ∈ (0, ∞)`), `σ ≥ 0`,
`b` Lipschitz on `[0, T] × ℝ`, `ν₀ ∈ P(ℝ)` with finite `p`-th moment, and Assumption 5.1. -/
structure Standing : Prop where
  T_pos : 0 < D.T
  σ_nonneg : 0 ≤ D.σ
  b_lip : ∃ K, LipschitzOnWith K (fun q : ℝ × ℝ => D.b q.1 q.2) (Set.Icc 0 D.T ×ˢ Set.univ)
  ν₀_prob : IsProb D.ν₀
  ν₀_moment : ∫⁻ y, ENNReal.ofReal (|y| ^ D.p) ∂D.ν₀.1 < ⊤
  a51 : Assumption51 D.T D.p D.f D.g D.c

/-- **Admissible singular control, Definition 5.5** (p.20): "A tuple ρ = (Ω, 𝓕, 𝔽, P, x₀, W, ξ)
is said to be an admissible singular control if (1) (Ω, 𝓕, 𝔽, P) is a filtered probability space
satisfying the usual conditions; (2) x₀ is an 𝓕₀-measurable ℝ-valued random variable with
P ∘ x₀⁻¹ = ν₀; (3) W is a standard (Ω, 𝓕, 𝔽, P)-Brownian motion; (4) ξ : Ω × [0, T] → [0, ∞) is an
𝔽-adapted nondecreasing càdlàg process." together with its state `X^ρ`, "the unique process
solving (5.16) X^ρ_t = x₀ + ∫_0^t b(t, X^ρ_t)dt + σW_t + ξ_t, t ∈ [0, T]".

**Formalization Note.** The sample space ranges over `Type` (universe `0`). The state `X` is
carried as a field with the equation (5.16) P-a.s. on `[0, T]` and adaptedness; since the solution
is unique (p.20), this changes nothing. Paths are given on `ℝ`; only `[0, T]` enters. -/
structure Ctrl where
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  P : Measure Ω
  F : Filtration ℝ mΩ
  x₀ : Ω → ℝ
  W : ℝ → Ω → ℝ
  ξ : ℝ → Ω → ℝ
  X : ℝ → Ω → ℝ
  prob : IsProbabilityMeasure P
  usual : RepairSched.UsualConditions F P
  x₀_meas : Measurable[F 0] x₀
  x₀_law : P.map x₀ = D.ν₀.1
  bm : IsFBMOn P F D.T W
  ξ_adapted : ∀ t ∈ Set.Icc (0 : ℝ) D.T, Measurable[F t] (ξ t)
  ξ_nonneg : ∀ ω, ∀ t ∈ Set.Icc (0 : ℝ) D.T, 0 ≤ ξ t ω
  ξ_mono : ∀ ω, MonotoneOn (fun t => ξ t ω) (Set.Icc 0 D.T)
  ξ_rc : ∀ ω, ∀ t ∈ Set.Icc (0 : ℝ) D.T,
    ContinuousWithinAt (fun s => ξ s ω) (Set.Icc t D.T) t
  ξ_leftLim : ∀ ω, ∀ t ∈ Set.Ioc (0 : ℝ) D.T,
    ∃ l : ℝ, Filter.Tendsto (fun s => ξ s ω) (nhdsWithin t (Set.Iio t)) (nhds l)
  X_adapted : ∀ t ∈ Set.Icc (0 : ℝ) D.T, Measurable[F t] (X t)
  X_eq : ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) D.T,
    X t ω = x₀ ω + (∫ s in (0 : ℝ)..t, D.b s (X s ω)) + D.σ * W t ω + ξ t ω

attribute [instance] Ctrl.mΩ

/-- **The cost functional** (p.20): `J(ρ, µ) = E^P[∫_0^T f(t, X^ρ_t, µ_t)dt + g(X^ρ_T, µ_T) +
∫_{[0,T]} c_t dξ_t]` for a measurable flow of probabilities `µ`.

**Formalization Note.** Value in `[−∞, ∞]` (`erealExpect`; it is `> −∞` under Assumption 5.1).
The time integral is pathwise (the path of `X` is càdlàg, so the integrand is bounded on
`[0, T]`); `∫_{[0,T]} c dξ` is the Lebesgue–Stieltjes integral over `[0, T]` including the jump
`ξ_0` at `0` (`ξ_{0−} = 0`). -/
noncomputable def J (ρ : D.Ctrl) (μ : ℝ → SubProb) : EReal :=
  erealExpect ρ.P (fun ω => (∫ t in (0 : ℝ)..D.T, D.f t (ρ.X t ω) (μ t)) +
    D.g (ρ.X D.T ω) (μ D.T) +
    ∫ t in Set.Icc 0 D.T, D.c t ∂(stieltjesMeasure (pathExt D.T (fun s => ρ.ξ s ω))))

/-- **Optimal control** (p.20): "ρ ∈ E_w is an optimal control for the flow of measures µ if …
J(ρ, µ) = inf_{E_w} J(·, µ)". -/
def IsOptimal (ρ : D.Ctrl) (μ : ℝ → SubProb) : Prop := ∀ ρ' : D.Ctrl, D.J ρ μ ≤ D.J ρ' μ

/-- A measurable flow of probability measures `µ : [0, T] → P(ℝ)`. -/
def IsProbFlow (μ : ℝ → SubProb) : Prop := Measurable μ ∧ ∀ t ∈ Set.Icc (0 : ℝ) D.T, IsProb (μ t)

/-- **MFG equilibrium, Definition 5.6** (p.20): "A measurable flow of probabilities µ is a MFG
equilibrium if (1) there exists an optimal control ρ ∈ E_w for µ, (2) µ_t = P ∘ (X^ρ_t)⁻¹ for any
t ∈ [0, T]." -/
def IsEquilibrium (μ : ℝ → SubProb) : Prop :=
  D.IsProbFlow μ ∧ ∃ ρ : D.Ctrl, D.IsOptimal ρ μ ∧
    ∀ t ∈ Set.Icc (0 : ℝ) D.T, (μ t).1 = ρ.P.map (ρ.X t)

/-- Measurable flows of probabilities, ordered `π`-a.e. by `≤st` (p.21). -/
def Flow : Type := {μ : ℝ → SubProb // D.IsProbFlow μ}

instance : Preorder D.Flow where
  le μ ν := ∀ᵐ t ∂D.π, μ.1 t ≤ ν.1 t
  le_refl μ := Filter.Eventually.of_forall fun t => le_refl _
  le_trans μ ν ρ h₁ h₂ := by filter_upwards [h₁, h₂] with t a b using a.trans b

/-- **The bounds (5.19)** (p.21): `µ^Min, µ^Max ∈ P(ℝ)` with "µ^Min ≤st P ∘ (X^ρ_t)⁻¹ ≤st µ^Max,
for any t ∈ [0, T] and ρ ∈ arg min_{E_w} J(·, µ)", for any flow of measures `µ`. -/
def Bounds519 (μMin μMax : SubProb) : Prop :=
  IsProb μMin ∧ IsProb μMax ∧ ∀ μ : D.Flow, ∀ ρ : D.Ctrl, D.IsOptimal ρ μ.1 →
    ∀ t ∈ Set.Icc (0 : ℝ) D.T, ∀ s : ℝ,
      μMin.1 (Set.Ioi s) ≤ ρ.P.map (ρ.X t) (Set.Ioi s) ∧
      ρ.P.map (ρ.X t) (Set.Ioi s) ≤ μMax.1 (Set.Ioi s)

/-- **The feasible flows `L`** (p.21): flows with `µ_t ∈ [µ^Min, µ^Max]` for `π`-a.a.
`t ∈ [0, T]` (as a type: representatives, ordered `π`-a.e.). -/
def Lset (μMin μMax : SubProb) : Set D.Flow := {μ | ∀ᵐ t ∂D.π, μMin ≤ μ.1 t ∧ μ.1 t ≤ μMax}

/-- **The best-response correspondence** (p.21): `R(µ) = {pν | ν ∈ arg min_E J(·, µ)}` with
`p(ν^ρ) = P ∘ (X^ρ)⁻¹`: the elements of `L` that agree `π`-a.e. with the marginal laws of the
state of an optimal control for `µ`. -/
def R (μMin μMax : SubProb) (μ : D.Lset μMin μMax) : Set (D.Lset μMin μMax) :=
  {m | ∃ ρ : D.Ctrl, D.IsOptimal ρ μ.1.1 ∧ ∀ᵐ t ∂D.π, (m.1.1 t).1 = ρ.P.map (ρ.X t)}

/-- **The set `M ⊂ L` of MFG equilibria** (Theorem 5.9, p.24): the elements of `L` that agree
`π`-a.e. with an equilibrium of Definition 5.6 (each lies in `L` by (5.19)). -/
def equilibria (μMin μMax : SubProb) : Set (D.Lset μMin μMax) :=
  {m | ∃ μ : ℝ → SubProb, D.IsEquilibrium μ ∧ ∀ᵐ t ∂D.π, m.1.1 t = μ t}

/-- The canonical space (5.17), p.20, `ℝ × C × D × D↑`, as `ℝ × ℝ^{[0,T]} × ℝ^{[0,T]} ×
ℝ^{[0,T]}` with the product σ-algebra (on `C` and `D` the Borel σ-algebra is the cylinder one). -/
abbrev Can : Type :=
  ℝ × (Set.Icc (0 : ℝ) D.T → ℝ) × (Set.Icc (0 : ℝ) D.T → ℝ) × (Set.Icc (0 : ℝ) D.T → ℝ)

/-- **The control rule** `ν^ρ = P ∘ (x₀, W, X^ρ, ξ)⁻¹` (p.20). -/
noncomputable def rule (ρ : D.Ctrl) : Measure D.Can :=
  ρ.P.map (fun ω => (ρ.x₀ ω, fun t => ρ.W t.1 ω, fun t => ρ.X t.1 ω, fun t => ρ.ξ t.1 ω))

/-- The set of control rules `E = {ν^ρ | ρ ∈ E_w}` (p.20). -/
def E : Set (Measure D.Can) := Set.range D.rule

/-- `E^M = {ν^ρ | ρ ∈ E_{M,w}}` (p.21), `E_{M,w}` the controls satisfying (5.18):
`E^P[|X^ρ_t|^p + (ξ_T)^p] ≤ M` for every `t ∈ [0, T]` (the constant written `K` here). -/
def EM (K : ℝ) : Set (Measure D.Can) :=
  {ν | ∃ ρ : D.Ctrl, D.rule ρ = ν ∧ ∀ t ∈ Set.Icc (0 : ℝ) D.T,
    ∫⁻ ω, ENNReal.ofReal (|ρ.X t ω| ^ D.p + ρ.ξ D.T ω ^ D.p) ∂ρ.P ≤ ENNReal.ofReal K}

/-- `J(ν^ρ, µ) := J(ρ, µ)` (p.20, "with a slight abuse of notation"); `⊤` off `E`.

**Formalization Note.** The value does not depend on the control realizing the rule (`J` is a
functional of the law of `(x₀, W, X^ρ, ξ)`); a realizing control is chosen. -/
noncomputable def JE (ν : Measure D.Can) (μ : ℝ → SubProb) : EReal :=
  open Classical in
  if h : ∃ ρ : D.Ctrl, D.rule ρ = ν then D.J h.choose μ else ⊤

/-- Evaluation of a path of `ℝ^{[0,T]}` at `t` (`0` off `[0, T]`). -/
noncomputable def pathAt (x : Set.Icc (0 : ℝ) D.T → ℝ) (t : ℝ) : ℝ :=
  open Classical in
  if h : t ∈ Set.Icc (0 : ℝ) D.T then x ⟨t, h⟩ else 0

/-- **The projection** `p(ν^ρ) = P ∘ (X^ρ)⁻¹` (p.21): the marginal law at `t` of the state
coordinate of a control rule. -/
noncomputable def pE (ν : Measure D.Can) (t : ℝ) : Measure ℝ :=
  ν.map (fun q => D.pathAt q.2.2.1 t)

end SingWeakModel

end SubmodMFG.Supplement


