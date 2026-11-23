-- Prove2me | Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_Occupation
-- name    : ArapostathisAC_VanishingDiscount_Supplement_Occupation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T18:02:57.879934+00:00
-- url     : https://prove2.me/theorems/424e3233-916f-4dbe-9adf-69582dda863c
-- title:
--   Convex analytic setting of §5.3: $\Pi_{SR}$, stability, $\hat\eta(f)$, $I_R$, $I_D$, $\rho^*$, Assumptions 5.18–5.20, sample path optimality, empirical measures
-- statement:
--   On the countable-state model of §5:
--
--   1. **Common actions** (p. 309): $U(i)=A$ for all $i$. A stationary randomized policy $f\in\Pi_{SR}$ is a family $f(i)\in\mathcal P(A)$; $f\in\Pi_{SD}$ is the case $f(i)=\delta_{f(i)}$.
--   2. $f$ is **irreducible** if every state is reached from every state with positive probability, and **stable** if the chain is positive recurrent ($E^f_i[\tau_i]<\infty$ for all $i$, $\tau_i$ the return time). The standing assumptions of §5.3 are common actions and irreducibility under every $f\in\Pi_{SR}$.
--   3. $\eta$ is an **invariant probability vector** of $f$ if $\eta\ge0$, $\sum_i\eta(i)=1$ and $\eta P(f)=\eta$; the **ergodic occupation measure** is $\hat\eta(f)(i,da)=\eta(f)(i)f(i)(da)$, and
--   $$I_R=\{\hat\eta(f):f\in\Pi_{SSR}\},\qquad I_D=\{\hat\eta(f):f\in\Pi_{SSD}\}.$$
--   4. $\rho^*=\inf_{f\in\Pi_{SSR}}\int c\,d\hat\eta(f)$; **Assumption 5.18**: $\liminf_{i\to\infty}\min_{a\in A}c(i,a)>\rho^*$; **Assumption 5.19**: every $f\in\Pi_{SR}$ is stable and $I_R$ is compact in $\mathcal P(S\times A)$; **Assumption 5.20**: $\sup_{\pi\in\Pi}E^\pi_0[\tau^2]<\infty$, $\tau=\min\{t\ge1:X_t=0\}$.
--   5. For an initial law $\mu$ on $S$, $\mathcal P^\pi_\mu=\sum_i\mu(\{i\})\mathcal P^\pi_i$. The sample path average cost is $J_s=\limsup_{N}N^{-1}\sum_{t<N}c(X_t,A_t)$, and $\pi^*$ is **sample path optimal against a class $C$** if, for a constant $\rho^*\in[0,\infty]$ ($J_s$ is extended real-valued, p. 287), $J_s=\rho^*$ $\mathcal P^{\pi^*}_\mu$-a.s. for every $\mu$ and $J_s\ge\rho^*$ $\mathcal P^\pi_\mu$-a.s. for every $\pi\in C$ and every $\mu$ (p. 288; $C=\Pi$ is sample path optimality).
--   6. The **empirical measures** (5.17) $\nu_t=t^{-1}\sum_{s<t}\delta_{(X_s,A_s)}$, $t\ge1$, as elements of $\mathcal P(\bar S\times A)$, $\bar S=S\cup\{\infty\}$, and the embedding $S\times A\to\bar S\times A$.
--   7. $\hat\eta(f)$ is **Pareto optimal** for costs $c_1,\dots,c_m$ if no $\hat\eta(\bar f)\in I_R$ has $\int c_i\,d\hat\eta(\bar f)\le\int c_i\,d\hat\eta(f)$ for all $i$ with strict inequality for some $i$.
--
--   **Formalization Note** $\bar S$ is $\mathbb N_\infty=\mathbb N\cup\{\top\}$ with its order topology, which is the one-point compactification of the discrete $\mathbb N$; its σ-algebra is discrete. $\nu_{t+1}$ is indexed by $t\ge0$. $\hat\eta(f)$ is built from an invariant probability vector, which is unique under the standing irreducibility. Costs $c\ge0$ are integrated in $[0,\infty]$.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), pp. 309–313, §5.3, (5.17)–(5.18), Assumptions 5.18–5.20; p. 288, sample path AC optimality; p. 335, Pareto optimality

import Mathlib
import Definitions.Def_ArapostathisAC_VanishingDiscount_CMP
import Definitions.Def_ArapostathisAC_VanishingDiscount_StationaryChain

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace ArapostathisAC.VanishingDiscount.Supplement

open ArapostathisAC.VanishingDiscount

/-- `ℕ∞` (the one-point compactification `S̄ = S ∪ {∞}` of `S = ℕ`, with `∞ = ⊤`) carries the
discrete σ-algebra, which contains every open set. -/
instance : OpensMeasurableSpace ℕ∞ := ⟨fun _ _ => MeasurableSet.of_discrete⟩

variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

/-- §5.3 (p. 309): all action sets are replicas of one compact metric space `A`, `U(i) = A`. -/
def CommonActions (M : CMP A) : Prop :=
  ∀ i, M.U i = Set.univ

/-- A stationary randomized policy `f ∈ Π_SR` on `S = ℕ` (p. 286): a randomized decision rule
`f(i) ∈ 𝒫(A)` with `f(i)(U(i)) = 1`. -/
structure RandRule (M : CMP A) where
  /-- the law `f(i)` of the action at state `i` -/
  rule : ℕ → Measure A
  isProb : ∀ i, IsProbabilityMeasure (rule i)
  adm : ∀ i, rule i (M.U i)ᶜ = 0

/-- The randomized decision rule as a stochastic kernel from `S = ℕ` to `A`. -/
noncomputable def RandRule.kernel {M : CMP A} (φ : RandRule M) : Kernel ℕ A :=
  Kernel.ofFunOfCountable φ.rule

instance {M : CMP A} (φ : RandRule M) : IsMarkovKernel φ.kernel :=
  ⟨fun i => φ.isProb i⟩

/-- `f ∈ Π_SR` as an admissible policy: the action at epoch `t` is drawn from `f(x_t)`. -/
noncomputable def RandRule.toPolicy {M : CMP A} (φ : RandRule M) : Policy M where
  rule _ := φ.kernel.comap Prod.snd measurable_snd
  adm _ hist := by
    rw [Kernel.comap_apply]
    exact φ.adm hist.2

/-- `f ∈ Π_SD` as a stationary randomized policy: `f(i) = δ_{f(i)}`. -/
noncomputable def RandRule.ofDet {M : CMP A} (g : StationaryPolicy M) : RandRule M where
  rule i := Measure.dirac (g.1 i)
  isProb _ := inferInstance
  adm i := by
    rw [Measure.dirac_apply' _ (M.U_compact i).isClosed.measurableSet.compl]
    simp [g.2 i]

/-- Under `f ∈ Π_SR` the state process is irreducible (`S` is its single communicating class):
from every `i`, every `j` is reached with positive probability at some time. -/
def IsIrreducibleR (M : CMP A) (φ : RandRule M) : Prop :=
  ∀ i j, ∃ n : ℕ, 0 < pathMeasure M φ.toPolicy i {ω | (ω n).1 = j}

/-- `f ∈ Π_SR` is stable (p. 309): the state process is positive recurrent, i.e. the mean return
time to every state is finite. -/
def IsStableR (M : CMP A) (φ : RandRule M) : Prop :=
  ∀ i, ∫⁻ ω, ((returnTime i ω : ℕ∞) : ℝ≥0∞) ∂(pathMeasure M φ.toPolicy i) ≠ ⊤

/-- `η` is an invariant probability vector of the chain of `f ∈ Π_SR` (p. 309):
`η(f) P(f) = η(f)`, `P(f)(i, j) = ∫ P(j | i, a) f(i)(da)`. -/
def IsInvariantProb (M : CMP A) (φ : RandRule M) (η : ℕ → ℝ) : Prop :=
  (∀ j, 0 ≤ η j) ∧ HasSum η 1 ∧ ∀ j,
    HasSum (fun i => η i * (pathMeasure M φ.toPolicy i {ω | (ω 1).1 = j}).toReal) (η j)

/-- The ergodic occupation measure `η̂(f) ∈ 𝒫(S × A)` (p. 309),
`η̂(f)(i, da) = η(f)(i) f(i)(da)`, built from the invariant probability vector `η = η(f)`. -/
noncomputable def occ {M : CMP A} (φ : RandRule M) (η : ℕ → ℝ) : Measure (ℕ × A) :=
  Measure.sum fun i => ENNReal.ofReal (η i) • (Measure.dirac i).prod (φ.rule i)

/-- `I_R = {η̂(f) : f ∈ Π_SSR}` (p. 309), the occupation measures of stable stationary randomized
policies. -/
def occR (M : CMP A) : Set (Measure (ℕ × A)) :=
  {μ | ∃ φ : RandRule M, IsStableR M φ ∧ ∃ η, IsInvariantProb M φ η ∧ μ = occ φ η}

/-- `I_D = {η̂(f) : f ∈ Π_SSD}` (p. 309), the occupation measures of stable stationary
deterministic policies. -/
def occD (M : CMP A) : Set (Measure (ℕ × A)) :=
  {μ | ∃ g : StationaryPolicy M, IsStableR M (RandRule.ofDet g) ∧
    ∃ η, IsInvariantProb M (RandRule.ofDet g) η ∧ μ = occ (RandRule.ofDet g) η}

/-- The standing assumptions of §5.3 (p. 309): common action space `U(i) = A`, and under every
`f ∈ Π_SR` the state process has `S` as its single communicating class. -/
def StandingConvex (M : CMP A) : Prop :=
  CommonActions M ∧ ∀ φ : RandRule M, IsIrreducibleR M φ

/-- `ρ* = inf_{f ∈ Π_SSR} ρ(f)`, `ρ(f) = ∫ c dη̂(f)` (p. 312), in `[0, ∞]`. -/
noncomputable def rhoStar (M : CMP A) : ℝ≥0∞ :=
  ⨅ μ ∈ occR M, ∫⁻ p, ENNReal.ofReal (M.c p.1 p.2) ∂μ

/-- Assumption 5.18 (near monotonicity, p. 312): `liminf_{i→∞} min_{a ∈ A} c(i, a) > ρ*`. -/
def Assumption518 (M : CMP A) : Prop :=
  rhoStar M < liminf (fun i : ℕ => ⨅ a : A, ENNReal.ofReal (M.c i a)) atTop

/-- Assumption 5.19 (stability, p. 312): `Π_SR = Π_SSR` and `I_R` is compact in `𝒫(S × A)`. -/
def Assumption519 [SecondCountableTopology A] (M : CMP A) : Prop :=
  (∀ φ : RandRule M, IsStableR M φ) ∧
    IsCompact {μ : ProbabilityMeasure (ℕ × A) | (μ : Measure (ℕ × A)) ∈ occR M}

/-- Assumption 5.20 (p. 313): with `τ = min {t ≥ 1 : X_t = 0}`, `sup_{π ∈ Π} E^π_0[τ²] < ∞`. -/
def Assumption520 (M : CMP A) : Prop :=
  (⨆ π : Policy M, ∫⁻ ω, ((returnTime 0 ω : ℕ∞) : ℝ≥0∞) ^ 2 ∂(pathMeasure M π 0)) < ⊤

/-- The path measure `𝒫^π_μ` for an initial law `μ` on `S = ℕ`: `∑_i μ({i}) 𝒫^π_i`. -/
noncomputable def pathLawC (M : CMP A) (π : Policy M) (μ : Measure ℕ) : Measure (ℕ → ℕ × A) :=
  Measure.sum fun i => μ {i} • pathMeasure M π i

/-- The sample path average cost `J_s = limsup_{N→∞} N⁻¹ ∑_{t<N} c(X_t, A_t)` (p. 286), in
`[0, ∞]`. -/
noncomputable def sampleCost (M : CMP A) (ω : ℕ → ℕ × A) : ℝ≥0∞ :=
  limsup (fun N : ℕ => (N : ℝ≥0∞)⁻¹ *
    ∑ t ∈ Finset.range N, ENNReal.ofReal (M.c (ω t).1 (ω t).2)) atTop

/-- Sample path average cost optimality (p. 288) against the competitor class `C`: there is a
constant `ρ* ∈ [0, ∞]` with `J_s = ρ*` `𝒫^{π*}_μ`-a.s. for every initial law `μ`, while
`J_s ≥ ρ*` `𝒫^π_μ`-a.s. for every `π ∈ C` and every initial law `μ`. `J_s` is an extended-real
random variable (p. 287), so the constant may be `+∞` (e.g. when every stable policy has infinite
average cost). -/
def IsSamplePathOptimalIn (M : CMP A) (C : Set (Policy M)) (πs : Policy M) : Prop :=
  ∃ ρs : ℝ≥0∞,
    (∀ μ : Measure ℕ, IsProbabilityMeasure μ →
      ∀ᵐ ω ∂(pathLawC M πs μ), sampleCost M ω = ρs) ∧
    ∀ π ∈ C, ∀ μ : Measure ℕ, IsProbabilityMeasure μ →
      ∀ᵐ ω ∂(pathLawC M π μ), ρs ≤ sampleCost M ω

/-- The empirical measure `ν_{t+1} = (t+1)⁻¹ ∑_{s ≤ t} δ_{(X_s, A_s)}` of (5.17) (p. 309), viewed
in `𝒫(S̄ × A)` with `S̄ = ℕ∞`. -/
noncomputable def empirical (ω : ℕ → ℕ × A) (t : ℕ) : Measure (ℕ∞ × A) :=
  ((t : ℝ≥0∞) + 1)⁻¹ • ∑ s ∈ Finset.range (t + 1), Measure.dirac (((ω s).1 : ℕ∞), (ω s).2)

instance (ω : ℕ → ℕ × A) (t : ℕ) : IsProbabilityMeasure (empirical ω t) := by
  constructor
  simp only [empirical, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    measure_univ, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, smul_eq_mul]
  push_cast
  exact ENNReal.inv_mul_cancel (by simp) (by simp)

/-- `ν_{t+1}` as an element of `𝒫(S̄ × A)` (weak topology). -/
noncomputable def empiricalP (ω : ℕ → ℕ × A) (t : ℕ) : ProbabilityMeasure (ℕ∞ × A) :=
  ⟨empirical ω t, inferInstance⟩

/-- The embedding `S × A → S̄ × A`. -/
def embedS (p : ℕ × A) : ℕ∞ × A := ((p.1 : ℕ∞), p.2)

/-- `η̂(f)` is Pareto optimal in `I_R` for the vector cost `(∫ c_1 dη̂, …, ∫ c_m dη̂)` (p. 335): no
`η̂(f̄) ∈ I_R` has `∫ c_i dη̂(f̄) ≤ ∫ c_i dη̂(f)` for every `i` with strict inequality for some `i`. -/
def IsParetoOccupation (M : CMP A) {m : ℕ} (cs : Fin m → ℕ × A → ℝ) (μ : Measure (ℕ × A)) : Prop :=
  ∀ μ' ∈ occR M, (∀ i, ∫ p, cs i p ∂μ' ≤ ∫ p, cs i p ∂μ) → ∀ i, ∫ p, cs i p ∂μ' = ∫ p, cs i p ∂μ

end ArapostathisAC.VanishingDiscount.Supplement


