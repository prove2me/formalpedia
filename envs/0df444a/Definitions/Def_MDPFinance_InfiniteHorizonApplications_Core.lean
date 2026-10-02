-- Prove2me | Definitions.Def_MDPFinance_InfiniteHorizonApplications_Core
-- name    : MDPFinance_InfiniteHorizonApplications_Core
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:59:07.270342+00:00
-- url     : https://prove2.me/theorems/5902260c-209c-4b13-8ba7-0d0f9042b8ad
-- title:
--   Infinite-horizon Markov Decision Model apparatus (restated from chunks 07a/07b)
-- statement:
--   Restates the shared infinite-horizon vocabulary (model data, the operators $L$/$T_f$/$T$, value
--   functions $J_n$/$J_\infty$/$J$, bounding functions, the Structure Assumption) from chunks
--   `07a`/`07b` in this chunk's own namespace, per this series' file-ownership convention. This
--   chapter's applications — the cash balance problem, casino games, and the bandit problem — are all
--   instances of the general theory those chunks develop.
--
--   **Moderation note.** As in chunks `07a`/`07b`: $D$ measurable containing the graph of a measurable map, $Q$ a stochastic kernel, suprema over policies in $F^\infty$, $\int b\,dQ$ as a Lebesgue integral, (SA) with $IM\subset\mathbb M(E)$.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 194-207, Ch. 7 §7.1-7.3 (restated for this chunk)

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

namespace MDPFinance.InfiniteHorizonApplications

/-- The stationary infinite-horizon Markov Decision Model data and operators (Bäuerle–Rieder,
Definition 7.1.1/Definitions 7.1.2/7.3.1, restated — own namespace copy per this series'
file-ownership boundary, matching chunks `07a`/`07b`'s identical restatements). -/
structure MarkovDecisionModel (E A : Type*) [MeasurableSpace E] [MeasurableSpace A] where
  D : Set (E × A)
  hD_meas : MeasurableSet D
  hD_graph : ∃ f : E → A, Measurable f ∧ ∀ x, (x, f x) ∈ D
  Q : Kernel (E × A) E
  isMarkovQ : IsMarkovKernel Q
  r : E × A → ℝ
  hr_meas : Measurable r
  β : ℝ
  hβ0 : 0 < β
  hβ1 : β ≤ 1

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

def MarkovDecisionModel.Dx (M : MarkovDecisionModel E A) (x : E) : Set A :=
  {a | (x, a) ∈ M.D}

def IM (E : Type*) [MeasurableSpace E] : Set (E → EReal) :=
  {v | Measurable v ∧ ∀ x, v x ≠ ⊤}

noncomputable def erealIntegral (μ : Measure E) (v : E → EReal) : EReal :=
  (↑(∫⁻ x, (v x ⊔ 0).toENNReal ∂μ) : EReal) + (-(↑(∫⁻ x, ((-v x) ⊔ 0).toENNReal ∂μ) : EReal))

def IsDecisionRuleOf (M : MarkovDecisionModel E A) (f : E → A) : Prop :=
  Measurable f ∧ ∀ x, (x, f x) ∈ M.D

noncomputable def L (M : MarkovDecisionModel E A) (v : E → EReal) (xa : E × A) : EReal :=
  (M.r xa : EReal) + (M.β : EReal) * erealIntegral (M.Q xa) v

noncomputable def Tf (M : MarkovDecisionModel E A) (f : E → A) (v : E → EReal) (x : E) : EReal :=
  L M v (x, f x)

noncomputable def T (M : MarkovDecisionModel E A) (v : E → EReal) (x : E) : EReal :=
  ⨆ a ∈ M.Dx x, L M v (x, a)

def IsMaximizerOf (M : MarkovDecisionModel E A) (v : E → EReal) (f : E → A) : Prop :=
  IsDecisionRuleOf M f ∧ (fun x => L M v (x, f x)) = T M v

/-- `J_n^{rew,π}(x)`, the `n`-stage reward-to-go under a Markov policy `π : ℕ → E → A`, restated
from chunks `07a`/`07b`. -/
noncomputable def Jnpi (M : MarkovDecisionModel E A) (rew : E × A → ℝ) (π : ℕ → E → A) :
    (n : ℕ) → E → EReal
  | 0, _ => 0
  | (n + 1), x =>
      (rew (x, π 0 x) : EReal) + (M.β : EReal) *
        erealIntegral (M.Q (x, π 0 x)) (Jnpi M rew (fun k => π (k + 1)) n)

/-- `π ∈ F^∞`: a sequence of decision rules. -/
def IsPolicyOf (M : MarkovDecisionModel E A) (π : ℕ → E → A) : Prop :=
  ∀ k, IsDecisionRuleOf M (π k)

noncomputable def Jn (M : MarkovDecisionModel E A) (rew : E × A → ℝ) (n : ℕ) (x : E) : EReal :=
  ⨆ π ∈ {π : ℕ → E → A | IsPolicyOf M π}, Jnpi M rew π n x

noncomputable def Jinfpi (M : MarkovDecisionModel E A) (rew : E × A → ℝ) (π : ℕ → E → A)
    (x : E) : EReal :=
  atTop.limsup fun n => Jnpi M rew π n x

noncomputable def Jinf (M : MarkovDecisionModel E A) (x : E) : EReal :=
  ⨆ π ∈ {π : ℕ → E → A | IsPolicyOf M π}, Jinfpi M M.r π x

noncomputable def Jlim (M : MarkovDecisionModel E A) (x : E) : EReal :=
  atTop.limsup fun n => Jn M M.r n x

/-- A bounding function (Bäuerle–Rieder, Definition 7.3.1, restated). -/
structure IsBoundingFunction (M : MarkovDecisionModel E A) (b : E → ℝ) (cr αb : ℝ) : Prop where
  hb_meas : Measurable b
  hb_nonneg : ∀ x, 0 ≤ b x
  hcr : 0 ≤ cr
  hαb : 0 ≤ αb
  hr : ∀ xa ∈ M.D, |M.r xa| ≤ cr * b xa.1
  hQ : ∀ xa ∈ M.D, ∫⁻ x', ENNReal.ofReal (b x') ∂(M.Q xa) ≤ ENNReal.ofReal (αb * b xa.1)

def IBb (b : E → ℝ) : Set (E → ℝ) :=
  {v | Measurable v ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ x, |v x| ≤ c * b x}

noncomputable def normb (b : E → ℝ) (v : E → ℝ) : ℝ :=
  ⨆ x, |v x| / b x

noncomputable def Tf' (M : MarkovDecisionModel E A) (f : E → A) (v : E → ℝ) (x : E) : ℝ :=
  M.r (x, f x) + M.β * ∫ x', v x' ∂(M.Q (x, f x))

noncomputable def T' (M : MarkovDecisionModel E A) (v : E → ℝ) (x : E) : ℝ :=
  ⨆ a ∈ M.Dx x, M.r (x, a) + M.β * ∫ x', v x' ∂(M.Q (x, a))

/-- The Structure Assumption (SA), restated. -/
def StructureAssumptionSA (M : MarkovDecisionModel E A) (IM' : Set (E → EReal)) (Δ : Set (E → A))
    (Jlim : E → EReal) : Prop :=
  IM' ⊆ IM E ∧
  (0 : E → EReal) ∈ IM' ∧
  (∀ v ∈ IM', T M v ∈ IM') ∧
  (∀ v ∈ IM', ∃ f ∈ Δ, IsMaximizerOf M v f) ∧
  Jlim ∈ IM' ∧ Jlim = T M Jlim

end MDPFinance.InfiniteHorizonApplications


