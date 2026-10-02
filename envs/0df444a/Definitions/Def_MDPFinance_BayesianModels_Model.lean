-- Prove2me | Definitions.Def_MDPFinance_BayesianModels_Model
-- name    : MDPFinance_BayesianModels_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:18:22.91682+00:00
-- url     : https://prove2.me/theorems/03214e2f-3072-4860-ab58-39f422f575ef
-- title:
--   A Bayesian Model (Example 5.2.4)
-- statement:
--   This definition fixes the **Bayesian Model**, the special case of a Partially Observable
--   Markov Decision Model (Bäuerle and Rieder's Example 5.2.4) that underlies the whole of Section
--   5.4: the unobservable component $Y_n \equiv \theta$ never changes — it is a fixed, unknown
--   parameter drawn once from a prior distribution $Q_0$, and the decision maker's job is to learn
--   about $\theta$ from the observable process while acting.
--
--   Concretely, a Bayesian Model consists of an observable state space $E_X$, an unknown-parameter
--   space $\Theta$, an action space $A$, a disturbance space $Z$, and:
--
--   - a feasible set $D \subseteq E_X \times A$;
--   - a deterministic transition function $T^X : E_X \times A \times Z \to E_X$ giving the next
--     observable state from the current state, the action taken, and the realized disturbance;
--   - a $\sigma$-finite reference measure $\nu$ on $Z$ and a density $q_Z(x,\theta,a,z)$, so that the
--     disturbance $Z_{n+1}$'s law given $(X_n,\theta,A_n) = (x,\theta,a)$ is
--     $Q^Z(\mathrm dz\mid x,\theta,a) = q_Z(x,\theta,a,z)\,\nu(\mathrm dz)$;
--   - the prior distribution $Q_0$ of $\theta$;
--   - a one-stage reward $r(x,\theta,a)$, a terminal reward $g(x,\theta)$, and a discount factor
--     $\beta \in (0,1]$.
--
--   The joint transition kernel of the underlying Partially Observable Markov Decision Model is then
--   $Q(B \times C \mid x,\theta,a) = Q^X_\theta(B\mid x,a)\,\delta_\theta(C)$: the observable part
--   moves according to $T^X$ driven by $Z_{n+1}$, while $\theta$ is copied forward unchanged
--   (`BayesModel.Q`).
--
--   **Formalization Note.** `hD_sel` records the standing selector assumption on $D$ used throughout
--   the book (existence of a measurable decision rule). The joint kernel is realized directly as a
--   pushforward measure rather than as a bundled `Kernel`, since it is a *derived* quantity of this
--   definition, not one of its primitive fields.
--
--   **Moderation note.** `hqZ_prob` records that $Q^Z(\cdot\mid x,\theta,a)$ is a stochastic kernel (the density integrates to one), which the book's kernel is by definition.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 155, Example 5.2.4

import Mathlib

open MeasureTheory ProbabilityTheory

namespace MDPFinance.BayesianModels

/-- A **Bayesian Model** (Bäuerle–Rieder, Example 5.2.4, p. 155, PDF 168, together with the
explicit disturbance machinery §5.2 fixes for the underlying Partially Observable Markov
Decision Model, p. 151, PDF 164): the unobservable component `Y_n ≡ θ` is a *constant*,
unknown parameter with prior `Q_0`; the observable state moves via a deterministic transition
function `T^X : E_X × A × Z → E_X` driven by a disturbance `Z_{n+1}` whose law
`Q^Z(·|x,θ,a)` has density `q_Z(x,θ,a,·)` with respect to a σ-finite reference measure `ν` on
`Z`; rewards `r(x,θ,a)`, terminal reward `g(x,θ)`, discount `β ∈ (0,1]`. -/
structure BayesModel (EX Θ A Z : Type*) [MeasurableSpace EX] [MeasurableSpace Θ]
    [MeasurableSpace A] [MeasurableSpace Z] where
  /-- `D ⊆ E_X × A`, the feasible state-action pairs. -/
  D : Set (EX × A)
  hD_meas : MeasurableSet D
  hD_sel : ∃ f : EX → A, Measurable f ∧ ∀ x, (x, f x) ∈ D
  /-- The (deterministic) observable-state transition function `T^X`. -/
  TX : EX → A → Z → EX
  hTX_meas : Measurable fun p : EX × A × Z => TX p.1 p.2.1 p.2.2
  /-- The σ-finite reference measure on `Z` against which `Q^Z` has a density. -/
  nu : Measure Z
  hnu_sigmaFinite : SigmaFinite nu
  /-- The density `q_Z(x,θ,a,z)` of the disturbance kernel `Q^Z(·|x,θ,a)` w.r.t. `ν`. -/
  qZ : EX → Θ → A → Z → ℝ
  hqZ_meas : Measurable fun p : EX × Θ × A × Z => qZ p.1 p.2.1 p.2.2.1 p.2.2.2
  hqZ_nonneg : ∀ x θ a z, 0 ≤ qZ x θ a z
  /-- `Q^Z(·|x,θ,a)` is a stochastic kernel: the density integrates to one. -/
  hqZ_prob : ∀ x θ a, ∫⁻ z, ENNReal.ofReal (qZ x θ a z) ∂nu = 1
  /-- The prior distribution `Q_0` of `θ`. -/
  Q0 : Measure Θ
  isProbQ0 : IsProbabilityMeasure Q0
  /-- The one-stage reward `r(x,θ,a)`. -/
  r : EX × Θ × A → ℝ
  hr_meas : Measurable r
  /-- The terminal reward `g(x,θ)`. -/
  g : EX × Θ → ℝ
  hg_meas : Measurable g
  β : ℝ
  hβ0 : 0 < β
  hβ1 : β ≤ 1

variable {EX Θ A Z : Type*} [MeasurableSpace EX] [MeasurableSpace Θ] [MeasurableSpace A]
  [MeasurableSpace Z]

/-- `D(x) := {a ∈ A | (x,a) ∈ D}`, the feasible actions in state `x`. -/
def BayesModel.Dx (M : BayesModel EX Θ A Z) (x : EX) : Set A :=
  {a | (x, a) ∈ M.D}

/-- The joint transition kernel `Q(B×C|x,θ,a) := Q^X_θ(B|x,a) δ_θ(C)` of the underlying
Partially Observable Markov Decision Model (Bäuerle–Rieder, Example 5.2.4, Eq. before (5.7),
p. 155, PDF 168), realized here as the pushforward of the disturbance's law under
`z ↦ (T^X(x,a,z), θ)` (since `θ` never changes). -/
noncomputable def BayesModel.Q (M : BayesModel EX Θ A Z) (x : EX) (θ : Θ) (a : A) :
    Measure (EX × Θ) :=
  (M.nu.withDensity (fun z => ENNReal.ofReal (M.qZ x θ a z))).map (fun z => (M.TX x a z, θ))

end MDPFinance.BayesianModels


