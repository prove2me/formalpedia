-- Prove2me | Definitions.Def_LearnStability_Characterization_RuleProperties
-- name    : LearnStability_Characterization_RuleProperties
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T18:07:27.205488+00:00
-- url     : https://prove2.me/theorems/235cc942-2f1d-4196-8c57-988fd5027261
-- title:
--   Consistency, learnability (Definition 1), AERM, generalization and on-average generalization
-- statement:
--   Let $f$ be a learning problem, $A$ a learning rule, $\mathcal D$ a distribution on $\mathcal Z$ and $\varepsilon(m)$ a sequence. All conditions below are required for every sample size $m\ge1$, with $S\sim\mathcal D^m$.
--
--   1. $A$ is **consistent with rate $\varepsilon$ under $\mathcal D$** (Eq. (2)) if $\mathbb E_S[F(A(S))-F^*]\le\varepsilon(m)$. It is **universally consistent** if this holds under every distribution $\mathcal D$ with the same $\varepsilon$.
--   2. The problem is **learnable** (Definition 1) if there exist a learning rule $A$ and a rate $\varepsilon_{\rm cons}$ (non-increasing and tending to $0$) such that
--   $$\forall\mathcal D,\qquad \mathbb E_{S\sim\mathcal D^m}[F(A(S))-F^*]\le\varepsilon_{\rm cons}(m).$$
--   3. $A$ is an **AERM** (asymptotic empirical risk minimiser) **with rate $\varepsilon$ under $\mathcal D$** if $\mathbb E_S[F_S(A(S))-F_S(\hat h_S)]\le\varepsilon(m)$, and **universally an AERM** if this holds under every $\mathcal D$ with the same $\varepsilon$.
--   4. $A$ **generalizes with rate $\varepsilon$ under $\mathcal D$** if $\mathbb E_S[|F(A(S))-F_S(A(S))|]\le\varepsilon(m)$, and **universally generalizes** if this holds under every $\mathcal D$.
--   5. $A$ **on-average generalizes with rate $\varepsilon$ under $\mathcal D$** (Eq. (11)) if $|\mathbb E_S[F(A(S))-F_S(A(S))]|\le\varepsilon(m)$.
--
--   In learnability the rule and the rate are chosen before the distribution: the rate is distribution-free. These are the properties related to each other by Theorem 7 and its lemmas.
--
--   **Formalization Note.** "Every distribution" means every probability measure on the measurable space $\mathcal Z$. In `Learnable` the rule is required to be measurable in the sense of the `Setting` file (a convention of this formalization, not of the paper). The predicates for a fixed $\mathcal D$ do not require $\varepsilon$ to be a rate; where the paper's statement needs monotonicity, the theorem assumes it explicitly.
-- source:
--   Shalev-Shwartz, Shamir, Srebro and Sridharan, Learnability, Stability and Uniform Convergence, JMLR 11 (2010), p. 2638, Eq. (2) and Definition 1; p. 2639 (AERM, universally AERM, generalization); p. 2650, Eq. (11)

import Mathlib
import Definitions.Def_LearnStability_Characterization_Setting

open MeasureTheory

namespace LearnStability.Characterization

variable {H Z : Type*} [MeasurableSpace Z]

/-- `A` is consistent with rate `ε` under `D`, Eq. (2), p. 2638:
`E_{S∼D^m}[F(A(S)) − F*] ≤ ε(m)` for all `m ≥ 1`. -/
def Consistent (f : H → Z → ℝ) (A : Rule H Z) (D : Measure Z) (ε : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    ∫ S, (risk f D (A m S) - optRisk f D) ∂(sampleLaw D m) ≤ ε m

/-- `A` is universally consistent with rate `ε`: consistent with the same rate `ε` under every
probability distribution `D` on `Z` (Definition 1, p. 2638). -/
def UniversallyConsistent (f : H → Z → ℝ) (A : Rule H Z) (ε : ℕ → ℝ) : Prop :=
  ∀ D : Measure Z, IsProbabilityMeasure D → Consistent f A D ε

/-- Definition 1 (p. 2638): the problem is learnable if there exist a (measurable) learning rule
`A` and a rate `ε` — chosen before the distribution — such that `A` is consistent with rate `ε`
under every distribution. -/
def Learnable (f : H → Z → ℝ) : Prop :=
  ∃ A : Rule H Z, MeasurableRule f A ∧ ∃ ε : ℕ → ℝ, IsRate ε ∧ UniversallyConsistent f A ε

/-- `A` is an AERM with rate `ε` under `D` (p. 2639):
`E_{S∼D^m}[F_S(A(S)) − F_S(ĥ_S)] ≤ ε(m)` for all `m ≥ 1`. -/
def IsAERM (f : H → Z → ℝ) (A : Rule H Z) (D : Measure Z) (ε : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    ∫ S, (empRisk f S (A m S) - ermValue f S) ∂(sampleLaw D m) ≤ ε m

/-- `A` is universally an AERM with rate `ε`: an AERM with rate `ε` under every distribution
(p. 2639). -/
def UniversalAERM (f : H → Z → ℝ) (A : Rule H Z) (ε : ℕ → ℝ) : Prop :=
  ∀ D : Measure Z, IsProbabilityMeasure D → IsAERM f A D ε

/-- `A` generalizes with rate `ε` under `D` (p. 2639):
`E_{S∼D^m}[|F(A(S)) − F_S(A(S))|] ≤ ε(m)` for all `m ≥ 1`. -/
def Generalizes (f : H → Z → ℝ) (A : Rule H Z) (D : Measure Z) (ε : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    ∫ S, |risk f D (A m S) - empRisk f S (A m S)| ∂(sampleLaw D m) ≤ ε m

/-- `A` universally generalizes with rate `ε` (p. 2639). -/
def UniversallyGeneralizes (f : H → Z → ℝ) (A : Rule H Z) (ε : ℕ → ℝ) : Prop :=
  ∀ D : Measure Z, IsProbabilityMeasure D → Generalizes f A D ε

/-- `A` on-average generalizes with rate `ε` under `D`, Eq. (11), p. 2650:
`|E_{S∼D^m}[F(A(S)) − F_S(A(S))]| ≤ ε(m)` for all `m ≥ 1`. -/
def OnAverageGeneralizes (f : H → Z → ℝ) (A : Rule H Z) (D : Measure Z) (ε : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    |∫ S, (risk f D (A m S) - empRisk f S (A m S)) ∂(sampleLaw D m)| ≤ ε m

end LearnStability.Characterization


