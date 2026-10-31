-- Prove2me | Definitions.Def_MFCLearn_Lifted
-- name    : MFCLearn_Lifted
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:43:54.274993+00:00
-- url     : https://prove2.me/theorems/f18fd2fd-3c1f-4e6c-9d90-b4c488b8daf3
-- title:
--   The action law $\nu(\mu,h)$, the lifted transition $\Phi$ (2.11), the integrated reward $\widehat r$ (2.13) and the flow (2.10)
-- statement:
--   Fix an MFC model $(P,R,\gamma)$. For $\mu\in\mathcal P(\mathcal S)$ and a local policy $h\in\mathcal H$:
--
--   1. the **action distribution** is $\nu(\mu,h)(\cdot)=\int_{\mathcal S}h(s)(\cdot)\,\mu(ds)\in\mathcal P(\mathcal A)$;
--   2. the **lifted transition** is
--   $$\Phi(\mu,h)(ds')=\int_{\mathcal S}\mu(ds)\int_{\mathcal A}h(s)(da)\,P\big(s,\mu,a,\nu(\mu,h)\big)(ds');$$
--   3. the **integrated averaged reward** is
--   $$\widehat r(\mu,h)=\int_{\mathcal S}\mu(ds)\int_{\mathcal A}h(s)(da)\int_{\mathbb R}r\,R\big(s,\mu,a,\nu(\mu,h)\big)(dr);$$
--   4. for a control $\pi\in\Pi$ the **flow** of state distributions is $\mu_0=\mu$, $\mu_{t+1}=\Phi(\mu_t,\pi_t(\mu_t))$, with action laws $\nu_t=\nu(\mu_t,\pi_t(\mu_t))$.
--
--   $\Phi$ and $\widehat r$ are the transition and reward of the lifted control problem on $\mathcal P(\mathcal S)$ with actions in $\mathcal H$. The flow is a deterministic recursion; that the state laws of the McKean–Vlasov dynamics follow it is Lemma 2.1, not a definition.
--
--   **Formalization Note** $\nu(\mu,h)$ is the composition $h\circ\mu$; the printed "$\mu(s)$" in $\nu$'s definition is read as $\mu(ds)$, as in the proof of Lemma 2.1 and on p.5. $\Phi(\mu,h)$ is the kernel $(s,a)\mapsto P(s,\mu,a,\nu(\mu,h))$ composed with the joint law $\mu\otimes h$, whose value on a measurable set is the iterated integral above. $\widehat r$ is an iterated Bochner integral, in the printed order; a Bochner integral of a non-integrable function is $0$, but under Outstanding Assumption (A) every integrand here is integrable. The paper also calls $\Phi$ and $\widehat r$ measurable on $\mathcal P(\mathcal S)\times\mathcal H$; that is a claim, stated (in corrected form) in the mission's Lemmas 2.1 and 2.2, not part of the definition.
-- source:
--   Gu, Guo, Wei, Xu, Dynamic Programming Principles for Mean-Field Controls with Learning, arXiv:1911.07314v6, Lemma 2.1, (2.10)–(2.11), p.6; Lemma 2.2, (2.13), p.7; §2.2 p.5 (ν_t); (3.3) p.9

import Mathlib
import Definitions.Def_MFCLearn_Model

open MeasureTheory ProbabilityTheory

namespace MFCLearn

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- **The action distribution `ν(μ, h)`.** Gu, Guo, Wei, Xu, *Dynamic Programming Principles for
Mean-Field Controls with Learning*, arXiv:1911.07314v6, Lemma 2.1, p.6:
"ν(μ, h)(·) := ∫_{s∈S} h(s)(·)μ(s) ∈ P(A)"; also p.5: "under a feedback relaxed control πt, we have
νt(·) = ∫_{s∈S} πt(s, μt)(·)μt(ds) ∈ P(A)".

**Formalization Note** The printed `μ(s)` is read as `μ(ds)` (a typo; the proof of Lemma 2.1 and
p.5 use `μ(ds)`). `ν(μ, h)` is the composition `h ∘ₘ μ`, i.e. `ν(μ, h)(C) = ∫ h(s)(C) μ(ds)`. -/
noncomputable def nu (μ : ProbabilityMeasure S) (h : LocalPolicy S A) : ProbabilityMeasure A :=
  ⟨h.kernel ∘ₘ (μ : Measure S), inferInstance⟩

/-- **The lifted transition `Φ`** (2.11), arXiv:1911.07314v6, Lemma 2.1, p.6:
"Φ(μ, h)(ds′) := ∫_{s∈S} μ(ds) ∫_{a∈A} h(s)(da) P(s, μ, a, ν(μ, h))(ds′)".

**Formalization Note** Written as the composition of the kernel `(s, a) ↦ P(s, μ, a, ν(μ, h))` with
the joint law `μ ⊗ h` of `(s, a)`; for a measurable `C`, `Φ(μ, h)(C)` is the iterated integral of
(2.11) (checked in the verification file). The same `ν(μ, h)`, computed from `(μ, h)`, is used at every
`(s, a)`. -/
noncomputable def MFCModel.Phi (m : MFCModel S A) (μ : ProbabilityMeasure S) (h : LocalPolicy S A) :
    ProbabilityMeasure S :=
  ⟨m.Pfrozen μ (nu μ h) ∘ₘ ((μ : Measure S) ⊗ₘ h.kernel), inferInstance⟩

/-- **The integrated averaged reward `r̂`** (2.13), arXiv:1911.07314v6, Lemma 2.2, p.7:
"r̂(μ, h) := ∫_{s∈S} μ(ds) ∫_{a∈A} h(s)(da) ∫_{r∈ℝ} r R(s, μ, a, ν(μ, h))(dr)".

**Formalization Note** The three integrals are iterated Bochner integrals, in the printed order. A
Bochner integral of a non-integrable function is `0`; under Outstanding Assumption (A) the reward of
the constant control `h` is integrable, so the iterated integral is the genuine expectation. -/
noncomputable def MFCModel.rhat (m : MFCModel S A) (μ : ProbabilityMeasure S) (h : LocalPolicy S A) :
    ℝ :=
  ∫ s, ∫ a, ∫ r, r ∂(m.R (s, μ, a, nu μ h)) ∂(h.kernel s) ∂(μ : Measure S)

/-- **The lifted flow of state distributions** (2.10)/(3.3), arXiv:1911.07314v6, p.6 and p.9:
"μt+1 = Φ(μt, πt(μt)), μ0 = μ, t ∈ ℕ ∪ {0}".

**Formalization Note** This is the deterministic recursion on `P(S)`. That the state laws of the
McKean–Vlasov dynamics (2.7) follow it is Lemma 2.1, a theorem of the mission, not part of any
definition of the value. -/
noncomputable def MFCModel.flow (m : MFCModel S A) (π : Control S A) (μ : ProbabilityMeasure S) :
    ℕ → ProbabilityMeasure S
  | 0 => μ
  | t + 1 => m.Phi (m.flow π μ t) (π.toLocal t (m.flow π μ t))

/-- **The action distribution along the flow**, `ν_t = ν(μ_t, π_t(μ_t))` (arXiv:1911.07314v6, p.5). -/
noncomputable def MFCModel.flowAction (m : MFCModel S A) (π : Control S A)
    (μ : ProbabilityMeasure S) (t : ℕ) : ProbabilityMeasure A :=
  nu (m.flow π μ t) (π.toLocal t (m.flow π μ t))

end MFCLearn


