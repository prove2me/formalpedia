-- Prove2me | Definitions.Def_BlindNRMLS_Policy
-- name    : BlindNRMLS_Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:47:34.010649+00:00
-- url     : https://prove2.me/theorems/ba123356-8224-47d4-8c5a-2640d11ebb19
-- title:
--   §4, p.13 — non-anticipating policies and the law of a history
-- statement:
--   A history of $t$ periods is a sequence of actions and realized demand vectors. An **action** is a price vector $k\in[K]$ or the stop action. A **non-anticipating policy** $\phi=(\phi^t)$ gives, for each period, a probability kernel from the history of the earlier periods to the action.
--
--   Given demand distributions $Q$, the law $\mathbb P^\phi_Q$ of the history is built period by period: the action is drawn from $\phi^t$, and then the demand vector is drawn from the product law of $Q_{\cdot,k}$ under action $k$, independently of the past given the action. Under the stop action, demand is $0$.
--
--   This law is the probability space on which revenue, switches and regret are defined.
--
--   **Formalization Note** Rounds are $0$-based: `select t` chooses the action of period $t+1$ of the source. Rounds $t\ge T$ are never used. The action space carries the discrete $\sigma$-algebra.
-- source:
--   Simchi-Levi, Xu & Zhao, Blind Network Revenue Management and Bandits with Knapsacks Under Limited Switches, arXiv:1911.01067v5, §4, p.13; §2, p.8; Algorithm 2, p.15

import Mathlib
import Definitions.Def_BlindNRMLS_Problem

open MeasureTheory ProbabilityTheory

namespace BlindNRMLS

variable {d n K : ℕ}

/-- The action of one period: `some k` posts price vector `p_k`; `none` stops selling for good.
Simchi-Levi, Xu & Zhao, arXiv:1911.01067v5, §4, p.13; Algorithm 2 ("stop the algorithm"), p.15 and
the proof of Lemma EC.7, p.ec52 ("the algorithm has not stopped").

**Formalization Note.** The page's action space is `[K]`, and it lets a policy stop. `none` is that
stop. A policy that never uses `none` is a policy of the page. -/
abbrev Action (K : ℕ) := Option (Fin K)

instance : MeasurableSpace (Action K) := ⊤

instance : DiscreteMeasurableSpace (Action K) := ⟨fun _ => trivial⟩

/-- The history of `t` completed periods: the actions and the realized demand vectors (p.13). -/
abbrev History (n K t : ℕ) := Fin t → Action K × (Fin n → ℝ)

/-- A non-anticipating policy `ϕ = (ϕ^t)`: for each period, a probability kernel from the history
of actions and observations of the earlier periods to the action (p.13).

**Formalization Note.** Rounds are `0`-based: `select t` chooses the action of page period `t + 1`.
The rounds `t ≥ T` are never used. -/
structure Policy (n K : ℕ) where
  /-- The law of the next action given the history of `t` periods. -/
  select : (t : ℕ) → Kernel (History n K t) (Action K)
  markov : ∀ t, IsMarkovKernel (select t)

attribute [instance] Policy.markov

/-- The demand kernel: under `some k` the period's demand vector has law `Q.joint k`; under `none`
it is `0`. -/
noncomputable def demandKernel (Q : DemandLaw n K) : Kernel (Action K) (Fin n → ℝ) :=
  Kernel.ofFunOfCountable fun a =>
    match a with
    | none => Measure.dirac 0
    | some k => Q.joint k

instance (Q : DemandLaw n K) : IsMarkovKernel (demandKernel Q) := by
  refine ⟨fun a => ?_⟩
  rcases a with _ | k
  · change IsProbabilityMeasure (Measure.dirac (0 : Fin n → ℝ))
    infer_instance
  · change IsProbabilityMeasure (Measure.pi (Q.law k))
    infer_instance

/-- One period: draw the action from the policy, then the demand vector given the action. -/
noncomputable def stepKernel (Q : DemandLaw n K) (φ : Policy n K) (t : ℕ) :
    Kernel (History n K t) (Action K × (Fin n → ℝ)) :=
  (φ.select t) ⊗ₖ ((demandKernel Q).comap Prod.snd measurable_snd)

instance (Q : DemandLaw n K) (φ : Policy n K) (t : ℕ) : IsMarkovKernel (stepKernel Q φ t) := by
  rw [stepKernel]
  infer_instance

/-- Appending one period to a history. -/
def snocHistory {t : ℕ} (p : History n K t × (Action K × (Fin n → ℝ))) : History n K (t + 1) :=
  Fin.snoc (α := fun _ => Action K × (Fin n → ℝ)) p.1 p.2

/-- The law `ℙ^ϕ_Q` of the history of `t` periods under policy `ϕ` and demand distributions `Q`:
demand vectors are drawn afresh each period, independently of the past given the action
(time-homogeneous, p.2). -/
noncomputable def historyLaw (Q : DemandLaw n K) (φ : Policy n K) :
    (t : ℕ) → Measure (History n K t)
  | 0 => Measure.dirac (fun u => u.elim0)
  | t + 1 => ((historyLaw Q φ t) ⊗ₘ (stepKernel Q φ t)).map snocHistory

end BlindNRMLS


