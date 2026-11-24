-- Prove2me | Definitions.Def_EquilibriumExperiment_Gradient_Supplement_Learning
-- name    : EquilibriumExperiment_Gradient_Supplement_Learning
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T06:17:49.553808+00:00
-- url     : https://prove2.me/theorems/d05936f4-e30a-4210-8133-ef37ba82c70a
-- title:
--   §4.2 — finite context family, sequential experiment and the constrained weighted quadratic update (4.5)
-- statement:
--   Let $\mathcal A$ be a finite set of contexts and let $M_a$ be the published one-state market for context $a$. The choice functions, matching primitives and revenue function are shared; demand and the private-feature distribution may depend on $a$. Fix an interval $I=[c^-,c^+]$, step size $\eta>0$ and initial payment $p_1\in I$. In round $t$, the published estimator $\hat\Gamma_t$ is evaluated at the current payment $p_t$. Set
--   $$W_t=\sum_{s=1}^t s,\qquad V_t=\sum_{s=1}^t s p_s,\qquad \theta_t=\sum_{s=1}^t s\hat\Gamma_s,\qquad p_{t+1}=\max\{c^-,\min\{c^+,(V_t+\eta\theta_t)/W_t\}\}.$$
--   This is the minimizer in (4.5): differentiating its quadratic objective gives $W_t p-V_t-\eta\theta_t=0$. The accumulated weight is positive for every source round $t\ge1$.
--
--   The experiment draws fresh demand, private features, payment shocks and activation uniforms in each round. For a fixed state path, the raw shocks are independent and centered at zero. Before computing activations and $\hat\Gamma_t$, the current payment is added to each raw payment shock. Thus actual payments depend on the past, and their conditional law is the published experiment at $p_t$. The weighted regret is $T^{-1}\sum_{t=1}^T t(u_{A_t}(p)-u_{A_t}(p_t))$.
--
--   **Formalization Note** Round $t$ uses index $t-1$ in `Fin T`; state zero contains $p_1$. The source's introductory $p_{t-1}$ is read as $p_t$ according to step 1 and (4.5). A product law is used only for independent raw draws, followed by the explicit causal payment recursion. It is not a product law for actual payments. `StrongConcavityOn` uses the differentiable first-order inequality (A.13) with coefficient $\sigma/2$.
-- source:
--   Wager & Xu, Experimenting in Equilibrium, arXiv:1903.02124v5, p. 22, §4.2, steps 1–2 and (4.5); p. 39, (A.13); pp. 12–16, §3

import Mathlib
import Definitions.Def_EquilibriumExperiment_Gradient_Model

namespace EquilibriumExperiment.Gradient.Supplement

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Classical

/-- A finite state family uses the published one-state Market. Only demand and the
private-feature law vary with the state (§3, pp.12–16). Finiteness is imposed by callers. -/
structure ContextFamily (A B : Type) [MeasurableSpace B] where
  market : A → Market B
  common : ∀ a a',
    (market a).f = (market a').f ∧ (market a).f' = (market a').f' ∧
    (market a).f'' = (market a').f'' ∧ (market a).ω = (market a').ω ∧
    (market a).Ω = (market a').Ω ∧ (market a).l = (market a').l ∧
    (market a).r = (market a').r

/-- The scalar minimizer of the weighted quadratic in (4.5), for positive weight
and step size and a nonempty closed interval. It is the projection of
(weightedPayments + η * theta) / weight onto [lo,hi]. -/
noncomputable def quadraticUpdate (lo hi η weightedPayments theta weight : ℝ) : ℝ :=
  max lo (min hi ((weightedPayments + η * theta) / weight))

/-- Sufficient statistics of (4.5); the payment is for the next experiment. -/
structure LearningState where
  payment : ℝ
  weight : ℝ
  weightedPayments : ℝ
  theta : ℝ

/-- Add period t (source indexing t≥1) with gradient estimate g. -/
noncomputable def learningStep (lo hi η : ℝ) (t : ℕ) (g : ℝ)
    (s : LearningState) : LearningState :=
  let w := s.weight + t
  let v := s.weightedPayments + (t : ℝ) * s.payment
  let θ := s.theta + (t : ℝ) * g
  ⟨quadraticUpdate lo hi η v θ w, w, v, θ⟩

/-- Translate raw payment shocks into actual payments, leaving all other data unchanged. -/
def shiftOutcome {B : Type} {n : ℕ} (p : ℝ) (x : Outcome B n) : Outcome B n :=
  (x.1, fun i => ((x.2 i).1, p + (x.2 i).2.1, (x.2 i).2.2))

/-- Independent raw draws: payments here are centered shocks ±ζ, NOT the actual
history-dependent payments. At round t, shiftOutcome adds the current payment before
any activation or gradient is evaluated. This coupling realizes the sequential experiment. -/
noncomputable def seedLaw {A B : Type} [MeasurableSpace B] (E : ContextFamily A B)
    {T : ℕ} (states : Fin T → A) (n : ℕ) (ζ : ℝ) :
    Measure (Fin T → Outcome B n) :=
  Measure.pi fun t => (E.market (states t)).sample n (perturbLaw 0 ζ)

/-- After k rounds, using fresh raw draws at each round and the published GammaHat
at the current payment p_t. For k≥T the extra estimates are set to zero; no statement
uses those estimates. State k=0 contains p₁; state k contains p_{k+1}. -/
noncomputable def runState {A B : Type} [MeasurableSpace B] (E : ContextFamily A B)
    {T : ℕ} (states : Fin T → A) (n : ℕ) (ζ lo hi η p₁ : ℝ)
    (x : Fin T → Outcome B n) : ℕ → LearningState
  | 0 => ⟨p₁, 0, 0, 0⟩
  | k + 1 =>
      let s := runState E states n ζ lo hi η p₁ x k
      let g := if h : k < T then
        (E.market (states ⟨k, h⟩)).GammaHat n s.payment ζ
          (shiftOutcome s.payment (x ⟨k, h⟩)) else 0
      learningStep lo hi η (k + 1) g s

/-- The (4.6) weighted regret, divided by T, not by the sum of the weights. -/
noncomputable def weightedRegret {A B : Type} [MeasurableSpace B] (E : ContextFamily A B)
    {T : ℕ} (states : Fin T → A) (n : ℕ) (ζ lo hi η p₁ comparator : ℝ)
    (x : Fin T → Outcome B n) : ℝ :=
  (∑ t : Fin T, ((t.val + 1 : ℕ) : ℝ) *
    ((E.market (states t)).u comparator -
      (E.market (states t)).u (runState E states n ζ lo hi η p₁ x t.val).payment)) / T

/-- The convention in (A.13): the quadratic term is σ/2. -/
def StrongConcavityOn (v : ℝ → ℝ) (σ lo hi : ℝ) : Prop :=
  ∀ x ∈ Set.Icc lo hi, ∀ y ∈ Set.Icc lo hi,
    v y ≤ v x + (y - x) * deriv v x - σ / 2 * (y - x) ^ 2

end EquilibriumExperiment.Gradient.Supplement


