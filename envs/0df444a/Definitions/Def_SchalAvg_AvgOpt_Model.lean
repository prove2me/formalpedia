-- Prove2me | Definitions.Def_SchalAvg_AvgOpt_Model
-- name    : SchalAvg_AvgOpt_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:48:55.182721+00:00
-- url     : https://prove2.me/theorems/79108450-74da-4af3-b3a8-2c98e9c1814c
-- title:
--   Schäl's Borel decision model (S, A, A(·), q, c): admissible policies, Φ, g, v_β, m_β, g̲, ḡ, w_β, w̲, Conditions (W), (S), (B)
-- statement:
--   This file fixes the discrete-time Markov decision model of Schäl (1993), §1–§3, and every object the main results are stated with.
--
--   **The model** (§1 (i)–(v), p. 163). A model $(S, A, A(\cdot), q, c)$ consists of
--
--   1. a **state space** $S$ and an **action space** $A$, both standard Borel spaces;
--   2. for every state $x$ a nonempty set $A(x) \subseteq A$ of **available actions**, such that $\operatorname{graph} A = \{(x, a) : a \in A(x)\}$ is a measurable subset of $S \times A$;
--   3. a **law of motion** $q$, a transition probability from $\operatorname{graph} A$ to $S$;
--   4. a measurable **one-step cost** $c : \operatorname{graph} A \to [0, \infty]$.
--
--   **Policies.** A randomized policy $\delta = (\delta_n) \in \Delta$ is a sequence of transition probabilities from the histories $(x_0, a_0, \dots, x_n)$ to $A$ such that $\delta_n(x_0, a_0, \dots, x_n)$ gives probability one to $A(x_n)$ (*admissibility*). The stationary policies form the class $\mathbb F$ of measurable $f : S \to A$ with $f(x) \in A(x)$. For each policy $\delta$ and initial state $x$ there are a canonical probability measure $P_{x\delta}$ and a state–decision process $(X_n, D_n)$.
--
--   **Costs.** For $\delta \in \Delta$ and $x \in S$,
--   $$J^n(\delta, x) = E_{x\delta}\Big[\sum_{m=0}^{n-1} c(X_m, D_m)\Big], \qquad \Phi(\delta, x) = \limsup_{n \to \infty} \frac1n J^n(\delta, x), \qquad J_\beta(\delta, x) = E_{x\delta}\Big[\sum_{m=0}^{\infty} \beta^m c(X_m, D_m)\Big]$$
--   for $0 < \beta < 1$. The minimal average cost, the discounted value function and its infimum are
--   $$g = \inf_{x \in S} \inf_{\delta \in \Delta} \Phi(\delta, x), \qquad v_\beta(x) = \inf_{\delta \in \Delta} J_\beta(\delta, x), \qquad m_\beta = \inf_{x \in S} v_\beta(x),$$
--   and $\bar g = \limsup_{\beta \to 1} (1 - \beta) m_\beta$, $\underline g = \liminf_{\beta \to 1} (1 - \beta) m_\beta$ (limits as $\beta \uparrow 1$). The **relative discounted value function** is $w_\beta(x) = v_\beta(x) - m_\beta$. A stationary $f$ is **$\beta$-discount optimal** if $J_\beta(f, x) = v_\beta(x)$ for all $x$.
--
--   **Assumptions.** The *General Assumption* is $g < \infty$ (p. 164). *Condition (B)* is $\sup_{0<\beta<1} w_\beta(x) < \infty$ for every $x \in S$ (p. 165). *Condition (W)* (p. 165): (0) $S$ is a locally compact space with countable base; (1) every $A(x)$ is a nonempty compact set and $x \mapsto A(x)$ is upper semicontinuous; (2) $q$ is continuous on $\operatorname{graph} A$ for weak convergence of probability measures; (3) $c$ is lower semicontinuous on $\operatorname{graph} A$. *Condition (S)* (p. 165): (1) every $A(x)$ is nonempty and compact; (2) for each $x$, $a \mapsto q(x, a)$ is continuous on $A(x)$ for setwise convergence; (3) for each $x$, $a \mapsto c(x, a)$ is lower semicontinuous on $A(x)$.
--
--   **Lower limits** (§3, p. 166). For a sequence $\beta(k)$ of discount factors write $w(k, x) = w_{\beta(k)}(x)$,
--   $$\underline w(x) = \liminf_{k \to \infty,\ y \to x} w(k, y), \qquad \underline w_n(k, x) = \inf_{\rho(x, y) \le 1/n} w(k, y),$$
--   where $\rho$ is a metric defining the topology of $S$. Under Condition (S) the paper uses the discrete metric, for which the lower limit is $\liminf_{k \to \infty} w(k, x)$.
--
--   These objects are shared by every statement of the mission: Lemma 1.2, Propositions 1.3, 2.1, 3.5, display (2.2), (3.2), Lemmas 3.3, 3.4 and Theorem 3.8.
--
--   **Formalization Note.** The model is built on the published `FeinbergLiang.ACOE.MDP` with `lower = 0`, so its cost `cost : S → A → [0, ∞]` is $c$; $q$ and $c$ are given on all of $S \times A$ (any measurable extension off $\operatorname{graph} A$; only values on $\operatorname{graph} A$ enter, because admissible policies act in $A(x)$ almost surely). Policies are Feinberg–Liang's history-dependent randomized kernels; `Admissible` is the probability-one constraint, and every infimum ($g$, $v_\beta$) runs over admissible policies only. All costs and values are in $[0, \infty]$; $(1 - \beta)$ enters as `ENNReal.ofReal (1 - β)`, and $\beta \to 1$ is the left neighbourhood filter `𝓝[<] 1`. $w_\beta$ uses truncated subtraction in $[0, \infty]$, which is the real difference whenever $m_\beta < \infty$; every statement that uses $w_\beta$ assumes the General Assumption, from which $m_\beta < \infty$ follows. Upper semicontinuity of $A(\cdot)$ is Berge's (every open $G \supseteq A(x)$ contains $A(y)$ for $y$ near $x$). Condition (W)(0) is carried inside `CondW` as the conjunction "Borel σ-algebra, locally compact, second countable, Hausdorff" for the topology on $S$; Condition (W)(1) in the paper prints "$A(x) \in \mathcal C(x)$", read as $\mathcal C(A)$. $\underline w$ is a lower limit along the product filter `atTop ×ˢ 𝓝 x` (which includes $y = x$), and $\underline w_n$ uses the closed ball of radius $1/n$, meaningful for $n \ge 1$.
-- source:
--   Schäl, Average Optimality in Dynamic Programming with General State Space, Math. Oper. Res. 18(1) (1993), pp. 163–166, §1 (i)–(v), (1.1), General Assumption, w_β, Condition (B), §2 Conditions (W), (S), §3 w(k, x), w̲, w̲_n(k, x); p. 168 (discrete metric under (S))

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP

open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter FeinbergLiang.ACOE

namespace SchalAvg.AvgOpt

/-- Schäl's basic model `(S, A, A(·), q, c)` (§1 (i)–(v), p. 163), built on the published `MDP`:
the one-step cost is `[0, ∞]`-valued (`lower = 0`, so `c(x, a) = cost x a`), every action set
`A(x)` is nonempty, and `graph A = {(x, a) | a ∈ A(x)}` is measurable. The law of motion `q` and
the cost `c` are given on all of `S × A`; only their values on `graph A` ever enter. -/
structure Model (S A : Type*) [MeasurableSpace S] [MeasurableSpace A] where
  /-- the underlying Markov decision process (cost `cost`, transition kernel `q`) -/
  toMDP : MDP S A
  /-- the cost takes values in `[0, ∞]` -/
  lower_eq : toMDP.lower = 0
  /-- the set `A(x)` of available actions -/
  Aset : S → Set A
  Aset_nonempty : ∀ x, (Aset x).Nonempty
  graph_meas : MeasurableSet {p : S × A | p.2 ∈ Aset p.1}
  cost_meas : Measurable (fun p : S × A => toMDP.cost p.1 p.2)

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- `graph A = {(x, a); a ∈ A(x)}`. -/
def graphA (M : Model S A) : Set (S × A) := {p | p.2 ∈ M.Aset p.1}

/-- `δ ∈ Δ`: a randomized history-dependent policy whose decision rule at every stage `t`
assigns probability one to `A(x_t)`, the action set of the current state, for every history. -/
def Admissible (M : Model S A) (π : Policy S A) : Prop :=
  ∀ (t : ℕ) (h : (Fin t → S × A) × S), π.rule t h (M.Aset h.2)ᶜ = 0

/-- `f ∈ 𝔽`: a stationary policy, i.e. a measurable `f : S → A` with `f(x) ∈ A(x)`. -/
def IsStationary (M : Model S A) (f : S → A) : Prop :=
  Measurable f ∧ ∀ x, f x ∈ M.Aset x

/-- The stationary policy of `f ∈ 𝔽`, as a (history-dependent, deterministic) policy. -/
noncomputable def statPolicy {M : Model S A} {f : S → A} (hf : IsStationary M f) : Policy S A :=
  Policy.ofStationary f hf.1

/-- The expected total `n`-stage cost `J^n(δ, x) = E_{xδ}[Σ_{m<n} c(X_m, D_m)]`. -/
noncomputable def Jn (M : Model S A) (π : Policy S A) (n : ℕ) (x : S) : ℝ≥0∞ :=
  vN M.toMDP π n 1 x

/-- The average expected cost per unit time (1.1): `Φ(δ, x) = limsup_n (1/n) J^n(δ, x)`. -/
noncomputable def Phi (M : Model S A) (π : Policy S A) (x : S) : ℝ≥0∞ :=
  avgCost M.toMDP π x

/-- The expected total discounted cost `J_β(δ, x) = E_{xδ}[Σ_m β^m c(X_m, D_m)]`. -/
noncomputable def Jbeta (M : Model S A) (π : Policy S A) (β : ℝ) (x : S) : ℝ≥0∞ :=
  vDisc M.toMDP π β x

/-- The minimal average cost `g := inf_{x ∈ S} inf_{δ ∈ Δ} Φ(δ, x)` (p. 164); the infimum is over
admissible policies only. -/
noncomputable def gStar (M : Model S A) : ℝ≥0∞ :=
  ⨅ x, ⨅ π : {π : Policy S A // Admissible M π}, Phi M π.1 x

/-- The value function `v_β(x) := inf_{δ ∈ Δ} J_β(δ, x)` (infimum over admissible policies). -/
noncomputable def vβ (M : Model S A) (β : ℝ) (x : S) : ℝ≥0∞ :=
  ⨅ π : {π : Policy S A // Admissible M π}, Jbeta M π.1 β x

/-- `m_β := inf_{x ∈ S} v_β(x)`. -/
noncomputable def mβ (M : Model S A) (β : ℝ) : ℝ≥0∞ :=
  ⨅ x, vβ M β x

/-- `ḡ := limsup_{β → 1} (1 − β) m_β` (`β ↑ 1`). -/
noncomputable def gUpper (M : Model S A) : ℝ≥0∞ :=
  limsup (fun β : ℝ => ENNReal.ofReal (1 - β) * mβ M β) (𝓝[<] 1)

/-- `g̲ := liminf_{β → 1} (1 − β) m_β` (`β ↑ 1`). -/
noncomputable def gLower (M : Model S A) : ℝ≥0∞ :=
  liminf (fun β : ℝ => ENNReal.ofReal (1 - β) * mβ M β) (𝓝[<] 1)

/-- The relative discounted value function `w_β(x) := v_β(x) − m_β` (p. 165). Truncated
subtraction in `[0, ∞]`; it is the real difference whenever `m_β < ∞`. -/
noncomputable def wβ (M : Model S A) (β : ℝ) (x : S) : ℝ≥0∞ :=
  vβ M β x - mβ M β

/-- The General Assumption (p. 164): `g < ∞`. -/
def GeneralAssumption (M : Model S A) : Prop := gStar M < ⊤

/-- Condition (B) (p. 165): `sup_{0 < β < 1} w_β(x) < ∞` for every `x ∈ S`. -/
def CondB (M : Model S A) : Prop :=
  ∀ x, (⨆ β ∈ Set.Ioo (0 : ℝ) 1, wβ M β x) < ⊤

/-- `f ∈ 𝔽` is `β`-discount optimal: `J_β(f, x) = v_β(x)` for every `x ∈ S`. -/
def IsDiscOptimal (M : Model S A) (β : ℝ) (f : S → A) : Prop :=
  ∃ hf : IsStationary M f, ∀ x, Jbeta M (statPolicy hf) β x = vβ M β x

/-- Upper semicontinuity of a set-valued map in the sense of Berge: for every `x` and every open
`G ⊇ F(x)`, `F(y) ⊆ G` for all `y` near `x`. -/
def UpperSemicontinuousMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (F : X → Set Y) : Prop :=
  ∀ x, ∀ G : Set Y, IsOpen G → F x ⊆ G → ∀ᶠ y in 𝓝 x, F y ⊆ G

/-- Condition (W) (p. 165). (0) `S` is a locally compact (Hausdorff) space with countable base
whose Borel σ-algebra is the given one; (1) every `A(x)` is compact (nonempty by `Model`) and
`x ↦ A(x)` is upper semicontinuous; (2) `q` is weakly continuous on `graph A`; (3) `c` is lower
semicontinuous on `graph A`. -/
def CondW [TopologicalSpace S] [TopologicalSpace A] (M : Model S A) : Prop :=
  (BorelSpace S ∧ LocallyCompactSpace S ∧ SecondCountableTopology S ∧ T2Space S) ∧
  (∀ x, IsCompact (M.Aset x)) ∧ UpperSemicontinuousMap M.Aset ∧
  (∀ f : S →ᵇ ℝ, ContinuousOn (fun p : S × A => ∫ y, f y ∂(M.toMDP.q p)) (graphA M)) ∧
  LowerSemicontinuousOn (fun p : S × A => M.toMDP.cost p.1 p.2) (graphA M)

/-- Condition (S) (p. 165). (1) every `A(x)` is compact (nonempty by `Model`); (2) for each `x`,
`a ↦ q(x, a)` is continuous on `A(x)` for setwise convergence; (3) for each `x`, `a ↦ c(x, a)` is
lower semicontinuous on `A(x)`. -/
def CondS [TopologicalSpace A] (M : Model S A) : Prop :=
  (∀ x, IsCompact (M.Aset x)) ∧
  (∀ x (B : Set S), MeasurableSet B → ContinuousOn (fun a => M.toMDP.q (x, a) B) (M.Aset x)) ∧
  ∀ x, LowerSemicontinuousOn (M.toMDP.cost x) (M.Aset x)

/-- `w̲(x) := liminf_{k → ∞, y → x} w(k, y)` with `w(k, y) = w_{β(k)}(y)` (§3, p. 166). -/
noncomputable def wLow [TopologicalSpace S] (M : Model S A) (β : ℕ → ℝ) (x : S) : ℝ≥0∞ :=
  liminf (fun p : ℕ × S => wβ M (β p.1) p.2) (atTop ×ˢ 𝓝 x)

/-- The lower limit `w̲` for the discrete metric used under Condition (S) (p. 168):
`liminf_{k → ∞} w_{β(k)}(x)`. -/
noncomputable def wLowDisc (M : Model S A) (β : ℕ → ℝ) (x : S) : ℝ≥0∞ :=
  liminf (fun k => wβ M (β k) x) atTop

/-- `w̲_n(k, x) := inf_{ρ(x, y) ≤ 1/n} w(k, y)` (§3, p. 166); meaningful for `n ≥ 1`. -/
noncomputable def wBall [PseudoMetricSpace S] (M : Model S A) (β : ℕ → ℝ) (n k : ℕ) (x : S) :
    ℝ≥0∞ :=
  ⨅ y ∈ Metric.closedBall x (1 / (n : ℝ)), wβ M (β k) y

end SchalAvg.AvgOpt


