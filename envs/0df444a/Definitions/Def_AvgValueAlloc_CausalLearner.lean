-- Prove2me | Definitions.Def_AvgValueAlloc_CausalLearner
-- name    : AvgValueAlloc_CausalLearner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:40:17.04279+00:00
-- url     : https://prove2.me/theorems/647626d7-7f65-4ec7-b854-d4391c2fd5fc
-- title:
--   Causal learner with unlimited computation
-- statement:
--   A **causal learner** for $n$ buyers, $S$ historical and $T$ live items has randomness $\omega$ from a probability space and decides each live item as a function of the history, the past live items, the current item and $\omega$ (measurably in $\omega$). It is **feasible** if its decisions satisfy (1) on every history, live sequence and $\omega$. Its expected welfare is $\mathbb E\,\mathrm{ALG}$ under a law or a population.
--
--   These are the learners of the lower bounds: they may use unlimited computation and may depend on the candidate family.
--
--   **Formalization Note** A learner feasible only on realized outcomes becomes everywhere feasible, with the same welfare there, by rejecting violating moves.
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), Theorem 1.2, p.3; Lemma 5.1, p.11

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_FinLaw
import Definitions.Def_AvgValueAlloc_prefixFeasible
import Definitions.Def_AvgValueAlloc_expIID

namespace AvgValueAlloc

open scoped ENNReal

/-- **A causal learner with unlimited computation.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), Theorem 1.2, p.3: "every causal learner … Learners
may use unlimited computation and know the candidate family"; Lemma 5.1, p.11: "Every
prefix-feasible learner, with all S historical and T live observations available".

A learner for `n` buyers, `S` historical and `T` live items: randomness `ω` from a probability
space `(Ω, μ)`, and a decision `act hist past cur ω` from the history, the list of past live items
and the current item. Each decision is a measurable function of `ω`. `dec` runs it on a live
sequence; `Feasible ρ` says the decisions satisfy (1) on every history, live sequence and `ω`;
`EALGiid D` and `EALGpop P` are its expected welfare.

**Formalization Note.** The learner may depend on `n`, `ρ`, `S`, `T` and anything else fixed
before the law is chosen. A learner feasible only on the realized outcomes becomes everywhere
feasible, with the same welfare on those outcomes, by rejecting violating moves. -/
structure CausalLearner (n S T : ℕ) where
  /-- the sample space of the learner's randomness -/
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  /-- the law of the randomness -/
  μ : MeasureTheory.Measure Ω
  [prob : MeasureTheory.IsProbabilityMeasure μ]
  /-- the decision from history, past live items, current item and randomness -/
  act : (Fin S → Vec n) → List (Vec n) → Vec n → Ω → Option (Fin n)
  act_meas : ∀ h past cur o, MeasurableSet {ω | act h past cur ω = o}

attribute [instance] CausalLearner.mΩ CausalLearner.prob

/-- The decisions of a learner on a live sequence. -/
def CausalLearner.dec {n S T : ℕ} (L : CausalLearner n S T) (h : Fin S → Vec n)
    (vs : Fin T → Vec n) (ω : L.Ω) : Fin T → Option (Fin n) :=
  fun t => L.act h (List.ofFn fun s : Fin t.val => vs ⟨s.val, lt_trans s.isLt t.isLt⟩) (vs t) ω

/-- The learner satisfies (1) on every outcome. -/
def CausalLearner.Feasible {n S T : ℕ} (L : CausalLearner n S T) (ρ : Fin n → ℚ) : Prop :=
  ∀ h vs ω, prefixFeasible ρ vs (L.dec h vs ω)

/-- `E ALG` under i.i.d. arrivals from `D`. -/
noncomputable def CausalLearner.EALGiid {n S T : ℕ} (L : CausalLearner n S T) (D : FinLaw n) :
    ℝ≥0∞ :=
  expIID D S T L.μ L.dec

/-- `E ALG` on a population in uniform order. -/
noncomputable def CausalLearner.EALGpop {n S T : ℕ} (L : CausalLearner n S T)
    (P : Fin (S + T) → Vec n) : ℝ≥0∞ :=
  expPop S T P L.μ L.dec

end AvgValueAlloc


