-- Prove2me | Definitions.Def_FeinbergLiang_ACOE_MDP
-- name    : FeinbergLiang_ACOE_MDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T21:00:54.207978+00:00
-- url     : https://prove2.me/theorems/19c7019d-0258-41da-b7ba-3d48a6e2ab7b
-- title:
--   Markov decision processes on Borel spaces: policies, strategic measures, discounted and average costs, relative value functions, Assumptions W*, B and EC
-- statement:
--   This file sets up the discrete-time Markov decision process (MDP) framework of Feinberg and Liang (2022, §2–§3).
--
--   **Model.** An MDP consists of a state space $\mathbb X$, an action space $\mathbb A$, a one-step cost $c:\mathbb X\times\mathbb A\to\mathbb R\cup\{+\infty\}$ that is bounded below, and a transition probability $q(\cdot\mid x,a)$ on $\mathbb X$. The cost is stored as $c(x,a)=\ell+c'(x,a)$, where $\ell\in\mathbb R$ is a lower bound and $c'$ takes values in $[0,+\infty]$.
--
--   **Policies.** Let $H_t=(\mathbb X\times\mathbb A)^t\times\mathbb X$ be the set of histories $h_t=(x_0,a_0,\dots,x_{t-1},a_{t-1},x_t)$. A policy $\pi=(\pi_0,\pi_1,\dots)$ is a sequence of regular transition probabilities $\pi_t(\cdot\mid h_t)$ from $H_t$ to $\mathbb A$. A stationary policy is given by a measurable map $\phi:\mathbb X\to\mathbb A$, used at every epoch. By the Ionescu Tulcea theorem, an initial state $x$ and a policy $\pi$ determine a probability measure $P^\pi_x$ on trajectories $(x_0,a_0,x_1,a_1,\dots)$ with $x_0=x$, $a_t\sim\pi_t(\cdot\mid h_t)$, and $x_{t+1}\sim q(\cdot\mid x_t,a_t)$.
--
--   **Costs.** For a discount factor $\alpha\in[0,1)$ and horizon $N$,
--   $$v^\pi_{N,\alpha}(x)=\mathbb E^\pi_x\sum_{t=0}^{N-1}\alpha^t c(x_t,a_t),\qquad v^\pi_\alpha(x)=\mathbb E^\pi_x\sum_{t=0}^{\infty}\alpha^t c(x_t,a_t),\qquad v_\alpha(x)=\inf_{\pi} v^\pi_\alpha(x).$$
--   The infimum ranges over all policies. The average cost per unit time is $w^\pi(x)=\limsup_{N\to\infty}\frac1N v^\pi_{N,1}(x)$, and $w(x)=\inf_\pi w^\pi(x)$. A policy is optimal for the discount factor $\alpha$ if $v^\pi_\alpha=v_\alpha$, and average-cost optimal if $w^\pi=w$. Further, $m_\alpha=\inf_x v_\alpha(x)$, $u_\alpha(x)=v_\alpha(x)-m_\alpha$ (the discounted relative value function), $\underline w=\liminf_{\alpha\uparrow1}(1-\alpha)m_\alpha$, and $\mathbb X_\alpha=\{x: v_\alpha(x)=m_\alpha\}$. For a sequence $\alpha_n$,
--   $$\tilde u(x)=\liminf_{n\to\infty,\ y\to x}u_{\alpha_n}(y).$$
--
--   **Assumptions.** A function $f$ on $\mathbb X\times\mathbb A$ is $\mathbb K$-inf-compact if for every nonempty compact $K\subseteq\mathbb X$ and every $\lambda$ the set $\{(x,a):x\in K,\ f(x,a)\le\lambda\}$ is compact.
--   1. *W\**: $c$ is $\mathbb K$-inf-compact and bounded below, and $q$ is weakly continuous: $(x,a)\mapsto\int f(y)\,q(dy\mid x,a)$ is continuous for every bounded continuous $f$.
--   2. *B*: $w^*=\inf_x w(x)<\infty$, and $\sup_{\alpha\in[0,1)}u_\alpha(x)<\infty$ for every $x$.
--   3. *EC* (for a given sequence $\alpha_n$): the family $\{u_{\alpha_n}\}$ is equicontinuous, and there is a nonnegative measurable $U\ge u_{\alpha_n}$ for all $n$ with $\int U(y)\,q(dy\mid x,a)<\infty$ for all $x,a$.
--
--   A sequence $\{\alpha_n\uparrow1\}$ of nonnegative discount factors is a nondecreasing sequence in $[0,1)$ converging to $1$.
--
--   These objects are the vocabulary of the average-cost optimality equation (ACOE) for MDPs with Borel state and action spaces, weakly continuous transitions and possibly unbounded costs.
--
--   **Formalization Note.** Lean stores only the $[0,\infty]$-valued part of every cost: `vN`, `vDisc`, `vOpt`, `avgCost`, `wOpt`, `mDisc`, `wLower` are the paper's $v^\pi_{N,\alpha}$, $v^\pi_\alpha$, $v_\alpha$, $w^\pi$, $w$, $m_\alpha$, $\underline w$ minus $\ell\sum_{t<N}\alpha^t$, $\ell/(1-\alpha)$ or $\ell$ respectively. The shift cancels in $u_\alpha$ and $\tilde u$ and does not change which policies are optimal. `uRel` is computed in $[0,\infty]$ and equals $u_\alpha$ whenever $m_\alpha<\infty$, which Assumption B(i) guarantees. $P^\pi_x$ is Mathlib's `Kernel.trajMeasure` (Ionescu Tulcea). $\alpha\uparrow1$ is the filter of left neighbourhoods of $1$. Assumption EC(i) also requires $u_{\alpha_n}<\infty$, so that the real-valued equicontinuity of Definition 3.1 applies; under Assumption B this holds automatically. In $\mathbb K$-inf-compactness the levels $\lambda$ range over $[0,\infty)$ for $c'$, which is the same as all real levels for $c=\ell+c'$.
-- source:
--   Feinberg and Liang, On the optimality equation for average cost Markov decision processes and its validity for inventory control, Annals of Operations Research 317, 2022, pp. 571-573, Section 2 (Definition 2.1, Assumptions W* and B, Eqs. (2.1)-(2.3), (2.5)) and Section 3 (Definition 3.1, Assumption EC)

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace FeinbergLiang.ACOE

/-- A Markov decision process on measurable state space `X` and action space `A`
(Feinberg–Liang 2022, §2, p. 571). The paper's one-step cost `c : X × A → ℝ ∪ {+∞}` is bounded
below; it is encoded as `c(x, a) = lower + cost x a` with a real constant `lower` and
`cost : X → A → ℝ≥0∞` (every bounded-below `ℝ ∪ {+∞}`-valued function has this form).
`q` is the transition probability `q(· | x, a)`. -/
structure MDP (X A : Type*) [MeasurableSpace X] [MeasurableSpace A] where
  /-- a real lower bound of the one-step cost -/
  lower : ℝ
  /-- the one-step cost minus `lower`; the paper's cost is `c(x, a) = lower + cost x a` -/
  cost : X → A → ℝ≥0∞
  /-- the transition probability `q(dy | x, a)` -/
  q : Kernel (X × A) X
  [isMarkov : IsMarkovKernel q]

attribute [instance] MDP.isMarkov

/-- A (randomized, history-dependent) policy `π = (π₀, π₁, …)` (p. 572): `π t` is a regular
transition probability from the histories `H_t = (X × A)^t × X` to `A`. -/
structure Policy (X A : Type*) [MeasurableSpace X] [MeasurableSpace A] where
  /-- the decision rule at epoch `t` -/
  rule : (t : ℕ) → Kernel ((Fin t → X × A) × X) A
  [isMarkov : ∀ t, IsMarkovKernel (rule t)]

attribute [instance] Policy.isMarkov

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

/-- The stationary policy defined by a measurable map `φ : X → A`: at every epoch the action
`φ(x_t)` is chosen with probability one (p. 572). -/
noncomputable def Policy.ofStationary (φ : X → A) (hφ : Measurable φ) : Policy X A where
  rule _ := Kernel.deterministic (fun h => φ h.2) (hφ.comp measurable_snd)

/-- The history `(x₀, a₀, …, x_t, a_t)`, indexed by `Finset.Iic t`, as a `Fin (t+1)`-tuple. -/
def histFin (t : ℕ) (h : Π _ : Finset.Iic t, X × A) : Fin (t + 1) → X × A :=
  fun j => h ⟨j.val, Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp j.isLt)⟩

lemma measurable_histFin (t : ℕ) : Measurable (histFin (X := X) (A := A) t) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

/-- The last state–action pair `(x_t, a_t)` of a history indexed by `Finset.Iic t`. -/
def lastPair (t : ℕ) (h : Π _ : Finset.Iic t, X × A) : X × A :=
  h ⟨t, Finset.mem_Iic.mpr le_rfl⟩

/-- One step of the controlled process: given the history up to `(x_t, a_t)`, the next state is
drawn from `q(· | x_t, a_t)` and then the next action from `π_{t+1}(· | h_{t+1})`. -/
noncomputable def stepKernel (M : MDP X A) (π : Policy X A) (t : ℕ) :
    Kernel (Π _ : Finset.Iic t, X × A) (X × A) :=
  (M.q.comap (lastPair t) (measurable_pi_apply _)) ⊗ₖ
    ((π.rule (t + 1)).comap (fun p => (histFin t p.1, p.2))
      (((measurable_histFin t).comp measurable_fst).prodMk measurable_snd))

instance (M : MDP X A) (π : Policy X A) (t : ℕ) : IsMarkovKernel (stepKernel M π t) := by
  have h1 : IsMarkovKernel (M.q.comap (lastPair (X := X) (A := A) t) (measurable_pi_apply _)) :=
    Kernel.IsMarkovKernel.comap _ _
  have h2 : IsMarkovKernel ((π.rule (t + 1)).comap (fun p : (Π _ : Finset.Iic t, X × A) × X =>
      (histFin t p.1, p.2)) (((measurable_histFin t).comp measurable_fst).prodMk measurable_snd)) :=
    Kernel.IsMarkovKernel.comap _ _
  exact Kernel.IsMarkovKernel.compProd _ _

/-- The law of `(x₀, a₀)`: `x₀ = x` and `a₀ ∼ π₀(· | x)`. -/
noncomputable def initMeasure (π : Policy X A) (x : X) : Measure (X × A) :=
  ((π.rule 0) (fun j => j.elim0, x)).map (fun a => (x, a))

/-- The strategic measure `P^π_x` on trajectories `ω = ((x₀, a₀), (x₁, a₁), …)`, given by the
Ionescu Tulcea theorem (p. 572). -/
noncomputable def pathMeasure (M : MDP X A) (π : Policy X A) (x : X) : Measure (ℕ → X × A) :=
  Kernel.trajMeasure (X := fun _ => X × A) (initMeasure π x) (stepKernel M π)

/-- The nonnegative part of the `N`-horizon discounted cost (2.1):
`v^π_{N,α}(x) = lower · Σ_{t<N} α^t + vN M π N α x`. -/
noncomputable def vN (M : MDP X A) (π : Policy X A) (N : ℕ) (α : ℝ) (x : X) : ℝ≥0∞ :=
  ∫⁻ ω, ∑ t ∈ Finset.range N, ENNReal.ofReal (α ^ t) * M.cost (ω t).1 (ω t).2
    ∂(pathMeasure M π x)

/-- The nonnegative part of the infinite-horizon discounted cost `v^π_α(x)` (N = ∞ in (2.1)):
`v^π_α(x) = lower / (1 - α) + vDisc M π α x` for `α ∈ [0, 1)`. -/
noncomputable def vDisc (M : MDP X A) (π : Policy X A) (α : ℝ) (x : X) : ℝ≥0∞ :=
  ∫⁻ ω, ∑' t, ENNReal.ofReal (α ^ t) * M.cost (ω t).1 (ω t).2 ∂(pathMeasure M π x)

/-- The (nonnegative part of the) optimal discounted cost `v_α(x) = inf_{π ∈ Π} v^π_α(x)`,
the infimum over all policies. -/
noncomputable def vOpt (M : MDP X A) (α : ℝ) (x : X) : ℝ≥0∞ :=
  ⨅ π : Policy X A, vDisc M π α x

/-- `π` is optimal for the discount factor `α`: `v^π_α(x) = v_α(x)` for all `x`. -/
def IsDiscOptimal (M : MDP X A) (π : Policy X A) (α : ℝ) : Prop :=
  ∀ x, vDisc M π α x = vOpt M α x

/-- The nonnegative part of the average cost per unit time (2.2):
`w^π(x) = lower + limsup_{N → ∞} (1/N) · vN M π N 1 x`. -/
noncomputable def avgCost (M : MDP X A) (π : Policy X A) (x : X) : ℝ≥0∞ :=
  limsup (fun N : ℕ => (N : ℝ≥0∞)⁻¹ * vN M π N 1 x) atTop

/-- The nonnegative part of the optimal average cost `w(x) = inf_{π ∈ Π} w^π(x)`. -/
noncomputable def wOpt (M : MDP X A) (x : X) : ℝ≥0∞ :=
  ⨅ π : Policy X A, avgCost M π x

/-- `π` is average-cost optimal: `w^π(x) = w(x)` for all `x`. -/
def IsAvgOptimal (M : MDP X A) (π : Policy X A) : Prop :=
  ∀ x, avgCost M π x = wOpt M x

/-- The nonnegative part of `m_α = inf_x v_α(x)` (2.3): `m_α = lower / (1 - α) + mDisc M α`. -/
noncomputable def mDisc (M : MDP X A) (α : ℝ) : ℝ≥0∞ :=
  ⨅ x, vOpt M α x

/-- The discounted relative value function `u_α(x) = v_α(x) - m_α` (2.3). The constant
`lower / (1 - α)` cancels, so `u_α = vOpt - mDisc` exactly whenever `m_α < ∞`
(which Assumption B(i) guarantees). -/
noncomputable def uRel (M : MDP X A) (α : ℝ) (x : X) : ℝ≥0∞ :=
  vOpt M α x - mDisc M α

/-- The nonnegative part of `w̲ = liminf_{α ↑ 1} (1 - α) m_α` (2.3):
`w̲ = lower + wLower M`. -/
noncomputable def wLower (M : MDP X A) : ℝ≥0∞ :=
  liminf (fun α : ℝ => ENNReal.ofReal (1 - α) * mDisc M α) (𝓝[<] 1)

/-- The set `X_α = {x : v_α(x) = m_α}` of minimizers of `v_α` (p. 577). -/
def optSet (M : MDP X A) (α : ℝ) : Set X :=
  {x | vOpt M α x = mDisc M α}

/-- The average-cost relative value function (2.5) for a sequence `α_n`:
`ũ(x) = liminf_{n → ∞, y → x} u_{α_n}(y)`. -/
noncomputable def uTilde [TopologicalSpace X] (M : MDP X A) (α : ℕ → ℝ) (x : X) : ℝ≥0∞ :=
  liminf (fun p : ℕ × X => uRel M (α p.1) p.2) (atTop ×ˢ 𝓝 x)

/-- `{α_n ↑ 1}` is a sequence of nonnegative discount factors: `α_n ∈ [0, 1)`, nondecreasing,
converging to `1`. -/
def IsDiscountSeq (α : ℕ → ℝ) : Prop :=
  (∀ n, α n ∈ Set.Ico (0 : ℝ) 1) ∧ Monotone α ∧ Tendsto α atTop (𝓝 1)

/-- `𝕂`-inf-compactness (Definition 2.1) of the cost `c = lower + f`: for every nonempty compact
`K ⊆ X` and every level `λ`, the set `{(x, a) : x ∈ K, f(x, a) ≤ λ}` is compact. (Levels
`λ < lower` of `c` give the empty set, so levels `λ ∈ ℝ≥0` of `f` suffice.) -/
def KInfCompact [TopologicalSpace X] [TopologicalSpace A] (f : X → A → ℝ≥0∞) : Prop :=
  ∀ K : Set X, K.Nonempty → IsCompact K →
    ∀ l : ℝ≥0, IsCompact {p : X × A | p.1 ∈ K ∧ f p.1 p.2 ≤ (l : ℝ≥0∞)}

/-- Assumption W* (p. 571): (i) the cost is `𝕂`-inf-compact and bounded below (the latter is
built into `MDP`); (ii) `q` is weakly continuous: `(x, a) ↦ ∫ f(y) q(dy | x, a)` is continuous
for every bounded continuous `f : X → ℝ`. -/
def AssumptionWStar [TopologicalSpace X] [TopologicalSpace A] (M : MDP X A) : Prop :=
  KInfCompact M.cost ∧ ∀ f : X →ᵇ ℝ, Continuous (fun p : X × A => ∫ y, f y ∂(M.q p))

/-- Assumption B (p. 572): (i) `w* = inf_x w(x) < ∞`; (ii) `sup_{α ∈ [0,1)} u_α(x) < ∞`
for every `x`. -/
def AssumptionB (M : MDP X A) : Prop :=
  (⨅ x, wOpt M x) ≠ ⊤ ∧ ∀ x, (⨆ α ∈ Set.Ico (0 : ℝ) 1, uRel M α x) ≠ ⊤

/-- Assumption EC (p. 573) for a given sequence `α_n`: (i) the family `{u_{α_n}}` is real-valued
and equicontinuous; (ii) there is a nonnegative measurable real function `U ≥ u_{α_n}` with
`∫ U(y) q(dy | x, a) < ∞` for all `x, a`. -/
def AssumptionEC [TopologicalSpace X] (M : MDP X A) (α : ℕ → ℝ) : Prop :=
  ((∀ n x, uRel M (α n) x ≠ ⊤) ∧ Equicontinuous (fun n x => (uRel M (α n) x).toReal)) ∧
  ∃ U : X → ℝ≥0∞, Measurable U ∧ (∀ x, U x ≠ ⊤) ∧ (∀ n x, uRel M (α n) x ≤ U x) ∧
    ∀ x a, ∫⁻ y, U y ∂(M.q (x, a)) ≠ ⊤

end FeinbergLiang.ACOE


