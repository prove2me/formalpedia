-- Prove2me | Definitions.Def_MFCLearn_Process
-- name    : MFCLearn_Process
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:44:29.093839+00:00
-- url     : https://prove2.me/theorems/c3b5c500-ded6-45c0-863a-f6b16303960b
-- title:
--   Realizations of the McKean–Vlasov dynamics (2.7), the canonical path law, $v^\pi$, $v$, $Q^\pi$, $Q$ and Outstanding Assumption (A)
-- statement:
--   Fix an MFC model $(P,R,\gamma)$, a control $\pi\in\Pi$ and an initial law $\mu\in\mathcal P(\mathcal S)$.
--
--   1. **Realization of (2.7).** Processes $(s_t,a_t,r_t)_{t\ge0}$ on a probability space $(\Omega,\mathbb P)$ realize the dynamics
--   $$s_{t+1}\sim P(s_t,\mu_t,a_t,\nu_t),\qquad a_t\sim\pi_t(s_t,\mu_t),\qquad r_t\sim R(s_t,\mu_t,a_t,\nu_t),\qquad s_0\sim\mu,$$
--   where $\mu_t$ and $\nu_t$ are the laws of $s_t$ and $a_t$ themselves, when: $s_t,a_t,r_t$ are measurable; $\mathrm{law}(s_0)=\mu$; $\mathrm{law}(s_t,a_t)=\mu_t\otimes\pi_t(\cdot,\mu_t)$; $\mathrm{law}((s_t,a_t),s_{t+1})=\mathrm{law}(s_t,a_t)\otimes P(\cdot,\mu_t,\cdot,\nu_t)$; and $\mathrm{law}((s_t,a_t),r_t)=\mathrm{law}(s_t,a_t)\otimes R(\cdot,\mu_t,\cdot,\nu_t)$.
--   2. **Canonical path law.** The law on $(\mathcal S\times\mathcal A\times\mathbb R)^{\mathbb N}$ obtained by the Ionescu-Tulcea construction: $s_0\sim\mu$, then at each time $t$, $a_t\sim\pi_t(s_t,\mu_t)$, $r_t\sim R(s_t,\mu_t,a_t,\nu_t)$, $s_{t+1}\sim P(s_t,\mu_t,a_t,\nu_t)$, with $(\mu_t,\nu_t)$ the flow (2.10) used as the population input.
--   3. **Values.** $v^\pi(\mu)=\mathbb E^\pi\big[\sum_{t=0}^\infty\gamma^t r_t\big]$ under the canonical path law (2.6), and $v(\mu)=\sup_{\pi\in\Pi}v^\pi(\mu)$ (2.8), (3.2).
--   4. **IQ function** (Definition 3.1, (3.4)). For $h\in\mathcal H$ and $\pi\in\Pi_1$, $Q^\pi(\mu,h)$ is the expected discounted reward when $s_0\sim\mu$, $a_0\sim h(s_0)$ and $a_t\sim\pi_t(s_t,\mu_t)$ for $t\ge1$, and
--   $$Q(\mu,h)=\sup_{\pi\in\Pi_1}Q^\pi(\mu,h).$$
--   5. **Outstanding Assumption (A).** For every $\mu$,
--   $$\sup_{\pi\in\Pi}\mathbb E^\pi\Big[\sum_{t=0}^\infty\gamma^t\,|r(s_t,\mu_t,a_t,\nu_t)|\Big]<\infty .$$
--
--   These are the objects of the dynamic programming principle: $v^\pi$ and $Q^\pi$ are expectations under a genuine law of the McKean–Vlasov dynamics, not sums of the integrated reward.
--
--   **Formalization Note** The realization predicate contains no $\Phi$: the population laws are the process's own marginals, and the predicate constrains only one-step joint laws, which every process with the history-conditional laws of (2.7) satisfies. The canonical path law is Mathlib's `Kernel.trajMeasure`; given $(s_t,a_t)$ it draws $r_t$ and $s_{t+1}$ independently, which (2.7) leaves open. That it realizes (2.7) is a theorem of the mission (Lemma 2.1). $v^\pi$ is the Bochner integral of $\sum'_t\gamma^t r_t$; under (A) the series converges absolutely almost surely and is integrable. $Q^\pi(\mu,h)$ is $v^{\mathrm{cons}(h,\pi)}(\mu)$. The suprema are real suprema over all controls; (A) makes them bounded (the mission's (3.7)). (A) is a `lintegral` with $|r_t|$ inside the sum, as printed, and its bound may depend on $\mu$. Definition 3.1 also calls $Q$ measurable; that is not part of the definition.
-- source:
--   Gu, Guo, Wei, Xu, Dynamic Programming Principles for Mean-Field Controls with Learning, arXiv:1911.07314v6, §2.2, (2.6)–(2.8), p.5; Outstanding Assumption (A), p.6; (3.2) p.9; Definition 3.1, (3.4), p.9

import Mathlib
import Definitions.Def_MFCLearn_Model
import Definitions.Def_MFCLearn_Lifted

open MeasureTheory ProbabilityTheory

namespace MFCLearn

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- The law of a measurable random variable `f` under a probability measure `Pr`, as a point of
`P(X)`. -/
noncomputable def lawOf {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] (Pr : Measure Ω)
    [IsProbabilityMeasure Pr] (f : Ω → X) (hf : Measurable f) : ProbabilityMeasure X :=
  ⟨Pr.map f, Measure.isProbabilityMeasure_map hf.aemeasurable⟩

/-- **A realization of the McKean–Vlasov dynamics (2.7)** under the control `π` from the initial law
`μ`. Gu, Guo, Wei, Xu, *Dynamic Programming Principles for Mean-Field Controls with Learning*,
arXiv:1911.07314v6, §2.2, p.5: "Given the population state distribution, i.e., the probability
distribution μt ∈ P(S) of state st, the representative agent takes an action at ∈ A according to some
control πt. She will receive an instantaneous stochastic reward rt = r(st, μt, at, νt) ∼
R(st, μt, at, νt)(·) and her state will move to the next state st+1 according to a probability
transition function of mean-field type P(st, μt, at, νt)(·). Here νt ∈ P(A) denotes the action
distribution at time t", with (2.7): "st+1 ∼ P(st, μt, at, νt)(·), at ∼ πt(st, μt)(·),
r(st, μt, at, νt) ∼ R(st, μt, at, νt)(·)", and `s₀ = ξ ∼ μ` ((2.6) and (A), pp.5–6).

On a probability space `(Ω, Pr)`, the processes `s`, `a`, `r` realize (2.7) when, writing
`μ_t := law(s_t)` and `ν_t := law(a_t)` (the process's **own** marginals):
1. `law(s₀) = μ`;
2. `law(s_t, a_t) = μ_t ⊗ π_t(·, μ_t)`;
3. `law((s_t, a_t), s_{t+1}) = law(s_t, a_t) ⊗ P(·, μ_t, ·, ν_t)`;
4. `law((s_t, a_t), r_t) = law(s_t, a_t) ⊗ R(·, μ_t, ·, ν_t)`.

**Formalization Note** The predicate contains no `Φ` and no flow: the population laws entering `P`,
`R` and `π` are the realization's own marginals (the McKean–Vlasov feature). Every process whose
history-conditional one-step laws are those of (2.7) satisfies the four clauses, which constrain only
one-step joint laws. -/
structure MFCModel.IsRealization (m : MFCModel S A) (π : Control S A) (μ : ProbabilityMeasure S)
    {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (s : ℕ → Ω → S) (a : ℕ → Ω → A) (r : ℕ → Ω → ℝ) : Prop where
  measurable_s : ∀ t, Measurable (s t)
  measurable_a : ∀ t, Measurable (a t)
  measurable_r : ∀ t, Measurable (r t)
  init : Pr.map (s 0) = (μ : Measure S)
  action : ∀ t, Pr.map (fun ω => (s t ω, a t ω)) =
    Pr.map (s t) ⊗ₘ (π.toLocal t (lawOf Pr (s t) (measurable_s t))).kernel
  transition : ∀ t, Pr.map (fun ω => ((s t ω, a t ω), s (t + 1) ω)) =
    Pr.map (fun ω => (s t ω, a t ω)) ⊗ₘ
      m.Pfrozen (lawOf Pr (s t) (measurable_s t)) (lawOf Pr (a t) (measurable_a t))
  reward : ∀ t, Pr.map (fun ω => ((s t ω, a t ω), r t ω)) =
    Pr.map (fun ω => (s t ω, a t ω)) ⊗ₘ
      m.Rfrozen (lawOf Pr (s t) (measurable_s t)) (lawOf Pr (a t) (measurable_a t))

/-- The one-period kernel at time `t` of the canonical process: from the state `s_t = s`, draw
`a_t ∼ π_t(s, μ_t)` and `r_t ∼ R(s, μ_t, a_t, ν_t)`, and output `(s_t, a_t, r_t)`, with `(μ_t, ν_t)`
the flow (2.10) used as the frozen population input. -/
noncomputable def MFCModel.stepKernel (m : MFCModel S A) (π : Control S A)
    (μ : ProbabilityMeasure S) (t : ℕ) : Kernel S (S × A × ℝ) :=
  Kernel.id ×ₖ ((π.toLocal t (m.flow π μ t)).kernel ⊗ₖ
    m.Rfrozen (m.flow π μ t) (m.flowAction π μ t))

instance (m : MFCModel S A) (π : Control S A) (μ : ProbabilityMeasure S) (t : ℕ) :
    IsMarkovKernel (m.stepKernel π μ t) := by
  unfold MFCModel.stepKernel; infer_instance

/-- The transition kernels of the canonical process: from the history up to time `n`, read the last
coordinate `(s_n, a_n, r_n)`, draw `s_{n+1} ∼ P(s_n, μ_n, a_n, ν_n)` and then apply `stepKernel` at
time `n + 1`. -/
noncomputable def MFCModel.pathKernel (m : MFCModel S A) (π : Control S A)
    (μ : ProbabilityMeasure S) (n : ℕ) :
    Kernel (Π _ : Finset.Iic n, S × A × ℝ) (S × A × ℝ) :=
  (m.stepKernel π μ (n + 1) ∘ₖ m.Pfrozen (m.flow π μ n) (m.flowAction π μ n)).comap
    (fun x => ((x ⟨n, Finset.mem_Iic.2 le_rfl⟩).1, (x ⟨n, Finset.mem_Iic.2 le_rfl⟩).2.1))
    (by fun_prop)

instance (m : MFCModel S A) (π : Control S A) (μ : ProbabilityMeasure S) (n : ℕ) :
    IsMarkovKernel (m.pathKernel π μ n) := by
  unfold MFCModel.pathKernel; infer_instance

/-- **The canonical path law of (2.7)** on `(S × A × ℝ)^ℕ`, the coordinates being
`(s_t, a_t, r_t)`: the Ionescu-Tulcea measure (`Kernel.trajMeasure`) with initial law
`(s₀, a₀, r₀) ∼ μ ⊗ π₀(·, μ) ⊗ R(·, μ, ·, ν₀)` and the kernels `pathKernel`. arXiv:1911.07314v6, §2.2,
p.5, (2.6)–(2.7).

**Formalization Note** The flow (2.10) is used here only as the frozen population input of the
kernels. That it is the actual law of the states, i.e. that this measure realizes (2.7), is clause 1
of Lemma 2.1 (a theorem of the mission). Given `(s_t, a_t)`, `r_t` and `s_{t+1}` are drawn
independently; (2.7) leaves their joint conditional law open, and by Lemma 2.2 the objective does not
depend on it. -/
noncomputable def MFCModel.pathLaw (m : MFCModel S A) (π : Control S A) (μ : ProbabilityMeasure S) :
    Measure (ℕ → S × A × ℝ) :=
  Kernel.trajMeasure (X := fun _ : ℕ => S × A × ℝ) (m.stepKernel π μ 0 ∘ₘ (μ : Measure S))
    (m.pathKernel π μ)

instance (m : MFCModel S A) (π : Control S A) (μ : ProbabilityMeasure S) :
    IsProbabilityMeasure (m.pathLaw π μ) := by
  unfold MFCModel.pathLaw; infer_instance

/-- **The value of a control**, `V^π(ξ) = E^π[Σ_{t=0}^∞ γ^t r(st, μt, at, νt) | s0 = ξ]` (2.6),
arXiv:1911.07314v6, p.5, for `ξ ∼ μ`, written `v^π(μ)` on p.7.

**Formalization Note** The expectation of the discounted reward under the canonical path law: the
Bochner integral of `ω ↦ Σ' γ^t r_t(ω)`. Under Outstanding Assumption (A) the series converges
absolutely almost surely and the integrand is integrable (Lemma 2.2), so this is the genuine
expectation. It is **not** defined as `Σ γ^t r̂(μ_t, π_t(μ_t))`: that identity is Lemma 2.2. -/
noncomputable def MFCModel.vpi (m : MFCModel S A) (π : Control S A) (μ : ProbabilityMeasure S) : ℝ :=
  ∫ ω, ∑' t, m.γ ^ t * (ω t).2.2 ∂(m.pathLaw π μ)

/-- **The value function** `v(μ) := sup_{π∈Π} v^π(μ)`, (2.8) and (3.2), arXiv:1911.07314v6, pp.5, 9.

**Formalization Note** A real `⨆` over all admissible controls; under (A) the range is bounded above
(the mission's (3.7) states this). -/
noncomputable def MFCModel.v (m : MFCModel S A) (μ : ProbabilityMeasure S) : ℝ :=
  ⨆ π : Control S A, m.vpi π μ

/-- **`Q^π(μ, h)`**, arXiv:1911.07314v6, Definition 3.1, (3.4), p.9:
"Q^π(μ, h) = E^π[Σ_{t=0}^∞ γ^t r(st, μt, at, νt) | s0 ∼ μ, a0 ∼ h(s0), at ∼ πt(st, μt), t ∈ ℕ]", for
`π ∈ Π₁`.

**Formalization Note** `π ∈ Π₁` is an `ℕ`-indexed control re-indexed by one (`π t` plays at time
`t + 1`), and `Q^π(μ, h)` is the value of the control `Control.cons h π` that plays `h` at time 0. -/
noncomputable def MFCModel.Qpi (m : MFCModel S A) (π : Control S A) (μ : ProbabilityMeasure S)
    (h : LocalPolicy S A) : ℝ :=
  m.vpi (Control.cons h π) μ

/-- **The IQ function** `Q(μ, h) = sup_{π∈Π₁} Q^π(μ, h)`, arXiv:1911.07314v6, Definition 3.1, (3.4),
p.9.

**Formalization Note** A real `⨆`; Definition 3.1 also calls `Q` "measurable", which is not part of
this definition (it is false for every σ-algebra on `H` when `S` is uncountable; see the mission
description). -/
noncomputable def MFCModel.Q (m : MFCModel S A) (μ : ProbabilityMeasure S) (h : LocalPolicy S A) :
    ℝ :=
  ⨆ π : Control S A, m.Qpi π μ h

/-- **Outstanding Assumption (A)**, arXiv:1911.07314v6, p.6: "For any initial state s0 = ξ ∼ μ,
sup_{π∈Π} E^π[Σ_{t=0}^∞ γ^t |r(st, μt, at, νt)|] < ∞."

**Formalization Note** The expectation is a `lintegral` of the nonnegative series
`Σ γ^t |r_t|` (absolute value inside the sum, as printed) under the canonical path law, so it is
meaningful without any integrability assumption. The bound may depend on `μ`; it is not uniform. By
Lemmas 2.1–2.2 the expectation is the same for every realization of (2.7). -/
def MFCModel.OutstandingA (m : MFCModel S A) : Prop :=
  ∀ μ : ProbabilityMeasure S,
    ⨆ π : Control S A, ∫⁻ ω, ∑' t, ENNReal.ofReal (m.γ ^ t) * ‖(ω t).2.2‖ₑ ∂(m.pathLaw π μ) < ⊤

end MFCLearn


