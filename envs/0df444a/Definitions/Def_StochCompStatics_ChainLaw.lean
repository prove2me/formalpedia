-- Prove2me | Definitions.Def_StochCompStatics_ChainLaw
-- name    : StochCompStatics_ChainLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:30:52.637365+00:00
-- url     : https://prove2.me/theorems/802c8293-c156-4922-9d81-d718f70a5c17
-- title:
--   State laws $\mu^t$, expected decisions $E^t$, the order $\succeq_D$ and $D$-preserving transitions
-- statement:
--   Let $S$ be a measurable space and $P$ a transition probability on $S$. The **laws of the chain** started at $s(1)$ are
--   $$
--   \mu^1=\delta_{s(1)},\qquad \mu^{t+1}(B)=\int_S P(s,B)\,\mu^t(ds)\quad(t\ge1).
--   $$
--   For a policy $g$ of the dynamic program, the transition is $P(s,B)=p(s,g(s),B)$; then $\mu^t(B)$ is the probability that the state of period $t$ lies in $B$, and the **expected decision** in period $t$ is
--   $$
--   \mathbb E^t(g)=\int_S g(s)\,\mu^t(ds).
--   $$
--   For a class $D$ of functions $S\to\mathbb R$, $\mu_2\succeq_D\mu_1$ means $\int_S f\,d\mu_2\ge\int_S f\,d\mu_1$ for all measurable $f\in D$ whose integrals exist, and a transition $P$ is **$D$-preserving** if $f\in D$ implies $s\mapsto\int_S f(s')\,P(s,ds')\in D$.
--
--   These are the objects of the stochastic comparative statics results: Theorem 1 compares the laws $\mu^t$ of two chains, and Corollary 1 and Theorem 3 compare the expected decisions $E^t$.
--
--   **Formalization Note** The Lean index $t$ starts at $0$: `chainLaw P s₁ 0` is $\mu^1$, and $\mu^{t+1}$ is the bind of $\mu^t$ with $P$. "The integrals exist" is read as integrability against both measures. $D$-preservation is imposed on the measurable $f\in D$. The state laws of a policy $g$ are the laws of the controlled chain when $g$ is measurable, which every statement of the mission assumes.
-- source:
--   Light, Stochastic Comparative Statics in Markov Decision Processes, arXiv:1904.05481v2, §2.1, pp.6–8 (µᵗ, Eᵗ, ⪰_D, Definition 1(iii))

import Mathlib

namespace StochCompStatics

open MeasureTheory ProbabilityTheory

variable {S : Type*} [MeasurableSpace S]

/-- The laws of the states of a Markov chain started at `s(1)` with transition `P`
(arXiv:1904.05481v2, §2.1, p.6): `µ¹ = δ_{s(1)}` and `µ^{t+1}(B) = ∫_S P(s, B) µ^t(ds)`.

**Formalization Note** The Lean index `t : ℕ` is the paper's period `t + 1`: `chainLaw P s₁ 0` is
`µ¹`, the point mass at the initial state. `µ^{t+1}` is the bind `µ^t.bind P`. -/
noncomputable def chainLaw (P : S → Measure S) (s₁ : S) : ℕ → Measure S
  | 0 => Measure.dirac s₁
  | t + 1 => (chainLaw P s₁ t).bind P

/-- The state laws `µ^t` under the policy `g` (arXiv:1904.05481v2, §2.1, p.6): `µ¹(B) = 1` if
`s(1) ∈ B` and `0` otherwise, `µ²(B) = p(s(1), g(s(1)), B)`, and
`µ^t(B) = ∫_S p(s, g(s), B) µ^{t-1}(ds)` for `t ≥ 3`; `µ^t(B)` is the probability that the state
of period `t` lies in `B` when the decision maker follows `g`.

**Formalization Note** The Lean index `t : ℕ` is the paper's period `t + 1`. The transition is
`P(s, ·) = p(s, g(s), ·)` (Definition 1(iii), p.8). For a measurable `g` this is a Markov kernel
and `stateLaw` is the law of the chain; every statement that uses it assumes `g` measurable. -/
noncomputable def stateLaw (p : Kernel (S × ℝ) S) (g : S → ℝ) (s₁ : S) : ℕ → Measure S :=
  chainLaw (fun s => p (s, g s)) s₁

/-- The expected decision in period `t`, `E^t(g) = ∫_S g(s) µ^t(ds)` (arXiv:1904.05481v2,
§2.1, p.7).

**Formalization Note** The Lean index `t : ℕ` is the paper's period `t + 1`. The integral is the
Bochner integral, `0` for a non-integrable `g`; statements that use it assume integrability. -/
noncomputable def expectedDecision (p : Kernel (S × ℝ) S) (g : S → ℝ) (s₁ : S) (t : ℕ) : ℝ :=
  ∫ s, g s ∂(stateLaw p g s₁ t)

/-- The integral order `⪰_D` (arXiv:1904.05481v2, §2.1, p.7): for `D ⊆ ℝ^S`,
`DDominates D μ₂ μ₁` means `µ₂ ⪰_D µ₁`, i.e. `∫ f dµ₂ ≥ ∫ f dµ₁` for all Borel measurable
`f ∈ D` such that the integrals exist.

**Formalization Note** "The integrals exist" is read as integrability of `f` against both
measures. -/
def DDominates (D : Set (S → ℝ)) (μ₂ μ₁ : Measure S) : Prop :=
  ∀ f ∈ D, Measurable f → Integrable f μ₂ → Integrable f μ₁ → ∫ s, f s ∂μ₁ ≤ ∫ s, f s ∂μ₂

/-- Definition 1(iii) (arXiv:1904.05481v2, p.8): the transition `P` is **`D`-preserving** if
`f ∈ D` implies `s ↦ ∫_S f(s') P(s, ds') ∈ D`.

**Formalization Note** The condition is imposed for the measurable `f ∈ D`, the functions whose
integrals the paper considers (footnote 9, p.8). -/
def IsDPreserving (D : Set (S → ℝ)) (P : Kernel S S) : Prop :=
  ∀ f ∈ D, Measurable f → (fun s => ∫ s', f s' ∂(P s)) ∈ D

end StochCompStatics


