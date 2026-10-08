-- Prove2me | Definitions.Def_MNLBandit_UCB_EpochLaw
-- name    : MNLBandit_UCB_EpochLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T03:33:46.869099+00:00
-- url     : https://prove2.me/theorems/a04fd3c8-e902-467b-b267-1c515ba10067
-- title:
--   App. A.1, pp. 32–33 — law of one epoch with a fixed assortment and the epoch purchase count v̂ᵢ
-- statement:
--   This file models one **epoch** of the MNL-Bandit in which a fixed assortment $S$ is offered repeatedly.
--
--   Customers choose independently, each according to the MNL probabilities $p_\cdot(S)$ of (2.1). `choiceMeasure v S` is the law of one choice on the outcomes $\{0\}\cup\{1,\dots,N\}$, and `epochLaw v S` is the law of an infinite i.i.d. sequence $\omega_0,\omega_1,\dots$ of such choices. The epoch ends at the first no-purchase, and
--   $$
--   \hat v_i(\omega)=\#\{k<\kappa(\omega) : \omega_k=i\},\qquad \kappa(\omega)=\min\{k:\omega_k=0\},
--   $$
--   is the number of purchases of product $i$ during the epoch (the count (3.1) "conditioned on $S_\ell=S$"); it is set to $0$ on the null event that no no-purchase ever occurs.
--
--   These objects are used to state Lemma A.1, whose content is that the law of $\hat v_i$ depends only on $v_i$ and not on the rest of the assortment.
--
--   **Formalization Note.** The outcome space carries the discrete σ-algebra (a scoped instance). Mathlib's infinite product measure is the zero measure unless each factor is a probability measure; `choiceMeasure v S` is one whenever $v\ge 0$, which every theorem using it assumes.
-- source:
--   Agrawal, Avadhanula, Goyal, Zeevi, MNL-Bandit: A Dynamic Learning Approach to Assortment Selection, arXiv:1706.03880v2, pp. 32–33, App. A.1 (proof of Lemma A.1), (3.1)

import Mathlib
import Definitions.Def_MNLBandit_UCB_Setting

namespace MNLBandit.UCB

open MeasureTheory

/-- The outcome space `Option (Fin N)` is finite; it carries the discrete σ-algebra (every subset is
measurable). Scoped to this namespace. -/
scoped instance instMeasurableSpaceOutcome {N : ℕ} : MeasurableSpace (Option (Fin N)) := ⊤

scoped instance instDiscreteMeasurableSpaceOutcome {N : ℕ} :
    DiscreteMeasurableSpace (Option (Fin N)) :=
  ⟨fun _ => trivial⟩

/-- The law of one customer's choice when the assortment `S` is offered, as a measure on the
outcomes `Option (Fin N)`: the weighted sum of point masses with the MNL weights (2.1). For
`v ≥ 0` it is a probability measure. -/
noncomputable def choiceMeasure {N : ℕ} (v : Fin N → ℝ) (S : Finset (Fin N)) :
    Measure (Option (Fin N)) :=
  ∑ o : Option (Fin N), ENNReal.ofReal (choiceProb v S o) • Measure.dirac o

/-- The law of the choices of the customers of one epoch in which the fixed assortment `S` is
offered repeatedly: an i.i.d. sequence `ω 0, ω 1, …` with law `choiceMeasure v S` (Mathlib's
infinite product `Measure.infinitePi`, which is the zero measure unless every factor is a
probability measure). -/
noncomputable def epochLaw {N : ℕ} (v : Fin N → ℝ) (S : Finset (Fin N)) :
    Measure (ℕ → Option (Fin N)) :=
  Measure.infinitePi (fun _ : ℕ => choiceMeasure v S)

open scoped Classical in
/-- The purchase count of product `i` in an epoch (3.1): the number of customers `k` before the
first no-purchase with `ω k = some i`; `0` on the null event that no no-purchase ever occurs. -/
noncomputable def epochCount {N : ℕ} (i : Fin N) (ω : ℕ → Option (Fin N)) : ℕ :=
  if h : ∃ k, ω k = none then
    ((Finset.range (Nat.find h)).filter (fun k => ω k = some i)).card
  else 0

end MNLBandit.UCB


