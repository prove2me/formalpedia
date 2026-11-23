-- Prove2me | Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_BorelCriteria
-- name    : ArapostathisAC_VanishingDiscount_Supplement_BorelCriteria
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T17:59:45.238773+00:00
-- url     : https://prove2.me/theorems/b606e7d2-0f35-49bd-9c11-13b4a0b1e33d
-- title:
--   Borel-model criteria in $[0,\infty]$: path law, discounted and average costs and values, $\varepsilon$-optimality, $T_\beta$, Assumptions 2.2–2.3, $\Pi_M$ and $\Pi_{SR}$
-- statement:
--   This file extends the published Borel controlled Markov process $(S,A,U,P,c)$ (state and action spaces Borel, $U$ strict, compact-valued with measurable graph $K$, $c\ge0$ on $K$, admissible history-dependent randomized policies $\Pi$) by the cost criteria of §2.2–§2.3 for possibly unbounded costs.
--
--   1. For an initial law $\mu$ and $\pi\in\Pi$, $\mathcal P^\pi_\mu$ is the law of the trajectory $((X_0,A_0),(X_1,A_1),\dots)$ given by (2.1)–(2.3).
--   2. The $N$-stage cost $J_N(\mu,\pi)=E^\pi_\mu\sum_{t<N}c(X_t,A_t)$, the discounted cost $J_\beta(x,\pi)=E^\pi_x\sum_{t\ge0}\beta^tc(X_t,A_t)$ and the average cost $J(x,\pi)=\limsup_{N\to\infty}N^{-1}J_N(x,\pi)$ (also $J(\mu,\pi)$), all in $[0,\infty]$.
--   3. The values $J^*_\beta(x)=\inf_{\pi\in\Pi}J_\beta(x,\pi)$, $J^*(x)=\inf_{\pi\in\Pi}J(x,\pi)$ and $J^*(\mu)=\inf_{\pi\in\Pi}J(\mu,\pi)$; $f\in\Pi_{SD}$ is $\beta$-discount optimal if $J_\beta(x,f)=J^*_\beta(x)$ for all $x$, average optimal if $J(x,f)=J^*(x)$ for all $x$; $\pi$ is $\varepsilon$-optimal if $J(\mu,\pi)\le J^*(\mu)+\varepsilon$ for every initial distribution $\mu$, and optimal if it is $\varepsilon$-optimal for every $\varepsilon>0$ (p. 287).
--   4. The discounted dynamic programming map (2.5)–(2.6): for $v:S\to[-\infty,\infty]$,
--   $$T_\beta(v)(x)=\inf_{a\in U(x)}\Big\{c(x,a)+\beta\int_S v(y)\,P(dy\mid x,a)\Big\}.$$
--   5. Assumption 2.2 (weak continuity): $(x,a)\mapsto\int v\,dP(\cdot\mid x,a)$ is continuous on $K$ for every $v\in C_b(S)$. Assumption 2.3: $U$ is upper semicontinuous (for every $x$ and open $G\supseteq U(x)$, $U(x')\subseteq G$ for $x'$ near $x$) and $c\in\mathcal L(K)$ (lower semicontinuous and bounded below on $K$).
--   6. Markov randomized policies $\Pi_M$ (decision rules $f_t:S\to\mathcal P(A)$ with $f_t(x)(U(x))=1$) and stationary randomized policies $\Pi_{SR}$, as admissible policies.
--
--   **Formalization Note** Costs are lintegrals in $[0,\infty]$, so $J^*_\beta$ may be $+\infty$, as the paper allows for unbounded costs. The integral of an extended-real function is $\int v^+-\int v^-$ in $\mathrm{EReal}$; for $v$ bounded below it is the usual value in $(-\infty,\infty]$. Topological assumptions refer to topologies on $S$ supplied by the theorems that use them.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), pp. 285–289, §2.2–§2.4, (2.1)–(2.6), Assumptions 2.2–2.3; p. 336, Appendix (upper semicontinuity)

import Mathlib
import Definitions.Def_ArapostathisAC_CanonicalTriplet_CMP

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace ArapostathisAC.VanishingDiscount.Supplement

open ArapostathisAC.CanonicalTriplet

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S]
  [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]

/-- The kernel giving the law of `(x₀, a₀)` from `x₀`: `x₀` is kept and `a₀ ∼ π₀(· | x₀)`. -/
noncomputable def initKernel {M : BorelCMP S A} (π : Policy M) : Kernel S (S × A) :=
  Kernel.deterministic id measurable_id ×ₖ
    (π.rule 0).comap (fun x : S => ((fun j : Fin 0 => j.elim0 : Fin 0 → S × A), x))
      (measurable_const.prodMk measurable_id)

/-- The probability measure `𝒫^π_μ` (p. 285, (2.1)–(2.3)) on trajectories
`ω = ((x₀, a₀), (x₁, a₁), …)` for an initial law `μ` of `X₀`. -/
noncomputable def pathLaw (M : BorelCMP S A) (π : Policy M) (μ : Measure S) :
    Measure (ℕ → S × A) :=
  Kernel.trajMeasure (X := fun _ => S × A) (initKernel π ∘ₘ μ) (stepKernel M π)

/-- The `N`-stage cost `J_N(μ, π) = E^π_μ ∑_{t<N} c(X_t, A_t)` (p. 286), in `[0, ∞]`. -/
noncomputable def costNμ (M : BorelCMP S A) (π : Policy M) (N : ℕ) (μ : Measure S) : ℝ≥0∞ :=
  ∫⁻ ω, ∑ t ∈ Finset.range N, ENNReal.ofReal (M.c (ω t)) ∂(pathLaw M π μ)

/-- The `N`-stage cost from the state `x`, `J_N(x, π)`, in `[0, ∞]`. -/
noncomputable def costN (M : BorelCMP S A) (π : Policy M) (N : ℕ) (x : S) : ℝ≥0∞ :=
  ∫⁻ ω, ∑ t ∈ Finset.range N, ENNReal.ofReal (M.c (ω t)) ∂(pathMeasure M π x)

/-- The discounted cost `J_β(x, π) = E^π_x ∑_{t ≥ 0} β^t c(X_t, A_t)` (p. 286), in `[0, ∞]`. -/
noncomputable def discCost (M : BorelCMP S A) (π : Policy M) (β : ℝ) (x : S) : ℝ≥0∞ :=
  ∫⁻ ω, ∑' t, ENNReal.ofReal (β ^ t * M.c (ω t)) ∂(pathMeasure M π x)

/-- The discounted value function `J*_β(x) = inf_{π ∈ Π} J_β(x, π)` (p. 287), in `[0, ∞]`. -/
noncomputable def discValue (M : BorelCMP S A) (β : ℝ) (x : S) : ℝ≥0∞ :=
  ⨅ π : Policy M, discCost M π β x

/-- `f ∈ Π_SD` is `β`-discount optimal: `J_β(x, f) = J*_β(x)` for every `x ∈ S`. -/
def IsDiscOptimal (M : BorelCMP S A) (β : ℝ) (f : StationaryPolicy M) : Prop :=
  ∀ x, discCost M f.toPolicy β x = discValue M β x

/-- The average cost `J(x, π) = limsup_{N→∞} (1/N) J_N(x, π)` (p. 286), in `[0, ∞]`. -/
noncomputable def avgCost (M : BorelCMP S A) (π : Policy M) (x : S) : ℝ≥0∞ :=
  limsup (fun N : ℕ => (N : ℝ≥0∞)⁻¹ * costN M π N x) atTop

/-- The average cost from an initial law, `J(μ, π) = limsup_{N→∞} (1/N) J_N(μ, π)`. -/
noncomputable def avgCostμ (M : BorelCMP S A) (π : Policy M) (μ : Measure S) : ℝ≥0∞ :=
  limsup (fun N : ℕ => (N : ℝ≥0∞)⁻¹ * costNμ M π N μ) atTop

/-- The optimal average cost `J*(x) = inf_{π ∈ Π} J(x, π)` (p. 287). -/
noncomputable def optAvg (M : BorelCMP S A) (x : S) : ℝ≥0∞ :=
  ⨅ π : Policy M, avgCost M π x

/-- The optimal average cost from an initial law, `J*(μ) = inf_{π ∈ Π} J(μ, π)` (p. 287). -/
noncomputable def optAvgμ (M : BorelCMP S A) (μ : Measure S) : ℝ≥0∞ :=
  ⨅ π : Policy M, avgCostμ M π μ

/-- `f ∈ Π_SD` is average optimal: `J(x, f) = J*(x)` for every `x ∈ S`. -/
def IsAvgOptimal (M : BorelCMP S A) (f : StationaryPolicy M) : Prop :=
  ∀ x, avgCost M f.toPolicy x = optAvg M x

/-- `π` is (AC) `ε`-optimal (p. 287): `J(μ, π) ≤ J*(μ) + ε` for every initial distribution
`μ ∈ 𝒫(S)`. -/
def IsAvgEpsOptimal (M : BorelCMP S A) (ε : ℝ) (π : Policy M) : Prop :=
  ∀ μ : Measure S, IsProbabilityMeasure μ → avgCostμ M π μ ≤ optAvgμ M μ + ENNReal.ofReal ε

/-- `π` is (AC) optimal (p. 287): it is `ε`-optimal for every `ε > 0`. -/
def IsAvgOptimalμ (M : BorelCMP S A) (π : Policy M) : Prop :=
  ∀ ε : ℝ, 0 < ε → IsAvgEpsOptimal M ε π

/-- The integral of an extended-real function: `∫ v dμ = ∫ v⁺ dμ − ∫ v⁻ dμ` in `EReal`. It is
the usual integral whenever one of the two parts is finite; in particular, for `v` bounded below
and `μ` finite it is a well-defined element of `(-∞, +∞]`. -/
noncomputable def extIntegral {X : Type*} [MeasurableSpace X] (μ : Measure X) (v : X → EReal) :
    EReal :=
  ((∫⁻ x, (v x).toENNReal ∂μ : ℝ≥0∞) : EReal) - ((∫⁻ x, (-v x).toENNReal ∂μ : ℝ≥0∞) : EReal)

/-- The discounted dynamic programming map (2.5)–(2.6) (p. 289), `T_β(v) = T(βv)`:
`T_β(v)(x) = inf_{a ∈ U(x)} {c(x, a) + β ∫ v(y) P(dy | x, a)}`, for `v : S → [-∞, +∞]`, computed
in `EReal`. -/
noncomputable def discBellman (M : BorelCMP S A) (β : ℝ) (v : S → EReal) (x : S) : EReal :=
  ⨅ a ∈ M.U x, ((M.c (x, a) : EReal) + (β : EReal) * extIntegral (M.P (x, a)) v)

/-- The multifunction `U` is upper semicontinuous (Appendix, p. 336): for every `x` and every
open `G ⊇ U(x)` there is a neighbourhood `N` of `x` with `U(x') ⊆ G` for all `x' ∈ N`. -/
def UpperSemicontinuousMulti {V W : Type*} [TopologicalSpace V] [TopologicalSpace W]
    (U : V → Set W) : Prop :=
  ∀ x, ∀ G : Set W, IsOpen G → U x ⊆ G → ∀ᶠ x' in 𝓝 x, U x' ⊆ G

/-- The graph `K = {(x, a) : a ∈ U(x)}` of the admissible action sets. -/
def graphK (M : BorelCMP S A) : Set (S × A) := {p | p.2 ∈ M.U p.1}

/-- Assumption 2.2 (p. 288): `P(· | x, a)` is weakly continuous in `(x, a)`: for every
`v ∈ C_b(S)`, `(x, a) ↦ ∫ v(y) P(dy | x, a)` is continuous on `K`. -/
def Assumption22 [TopologicalSpace S] (M : BorelCMP S A) : Prop :=
  ∀ v : S → ℝ, Continuous v → (∃ C, ∀ y, |v y| ≤ C) →
    ContinuousOn (fun p : S × A => ∫ y, v y ∂(M.P p)) (graphK M)

/-- Assumption 2.3 (p. 288): (i) the multifunction `U` is upper semicontinuous; (ii)
`c ∈ 𝓛(K)`, i.e. `c` is lower semicontinuous on `K` and bounded below on `K`. -/
def Assumption23 [TopologicalSpace S] (M : BorelCMP S A) : Prop :=
  UpperSemicontinuousMulti M.U ∧ LowerSemicontinuousOn M.c (graphK M) ∧
    BddBelow (M.c '' graphK M)

/-- A Markov randomized policy `π = {f_t} ∈ Π_M` (p. 285): randomized decision rules
`f_t : S → 𝒫(A)` (stochastic kernels) with `f_t(x)(U(x)) = 1`. -/
structure MarkovPolicy (M : BorelCMP S A) where
  /-- the decision rule `f_t` at epoch `t` -/
  rule : ℕ → Kernel S A
  [isMarkov : ∀ t, IsMarkovKernel (rule t)]
  /-- admissibility: `f_t(x)(U(x)ᶜ) = 0` -/
  adm : ∀ t x, rule t x (M.U x)ᶜ = 0

attribute [instance] MarkovPolicy.isMarkov

/-- A Markov randomized policy as an admissible policy: the action at epoch `t` is drawn from
`f_t(x_t)`, whatever the past. -/
noncomputable def MarkovPolicy.toPolicy {M : BorelCMP S A} (π : MarkovPolicy M) : Policy M where
  rule t := (π.rule t).comap Prod.snd measurable_snd
  adm t hist := π.adm t hist.2

/-- A stationary randomized policy `f ∈ Π_SR` (p. 286): one randomized decision rule
`f : S → 𝒫(A)` with `f(x)(U(x)) = 1`, used at every epoch. -/
structure RandStationaryPolicy (M : BorelCMP S A) where
  /-- the randomized decision rule -/
  rule : Kernel S A
  [isMarkov : IsMarkovKernel rule]
  /-- admissibility: `f(x)(U(x)ᶜ) = 0` -/
  adm : ∀ x, rule x (M.U x)ᶜ = 0

attribute [instance] RandStationaryPolicy.isMarkov

/-- A stationary randomized policy as an admissible policy. -/
noncomputable def RandStationaryPolicy.toPolicy {M : BorelCMP S A}
    (f : RandStationaryPolicy M) : Policy M where
  rule _ := f.rule.comap Prod.snd measurable_snd
  adm _ hist := f.adm hist.2

end ArapostathisAC.VanishingDiscount.Supplement


