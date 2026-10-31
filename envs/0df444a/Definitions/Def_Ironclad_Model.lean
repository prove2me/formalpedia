-- Prove2me | Definitions.Def_Ironclad_Model
-- name    : Ironclad_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:24:05.892075+00:00
-- url     : https://prove2.me/theorems/e1b187fc-b454-4def-ae31-cd9bebf929a9
-- title:
--   Honest characteristic symbols $\{0,h,H\}$ and the i.i.d. honest string
-- statement:
--   Time is divided into slots. In each slot the honest parties produce at most one block, and the **honest characteristic symbol** of the slot records the outcome: $0$ (no honest block), $h$ (an honest regular block) or $H$ (an honest iron block). With $p_h\in(0,1)$ the probability that the honest parties obtain a block in a slot and $q\in(0,1)$ the probability that a newly mined block is an iron block, each symbol is drawn independently with
--
--   $$
--   w_t=\begin{cases} h & \text{with probability } (1-q)p_h,\\ H & \text{with probability } qp_h,\\ 0 & \text{with probability } 1-p_h.\end{cases}
--   $$
--
--   The module defines the symbol type, the one-slot law $(w_t=s)\mapsto$ its mass, and the predicate "$w=(w_t)_{t\ge0}$ is an honest characteristic string with parameters $(p_h,q)$ on the probability space $(\Omega,\mu)$": every $w_t$ is measurable, the family $(w_t)_t$ is mutually independent, and every $w_t$ has the law above.
--
--   This is the only randomness in the analysis of the minimal adversarial mining-power requirement $\alpha$ and of the relative performance $\mathcal R$; the adversarial string does not enter them.
--
--   **Formalization Note** The i.i.d. law is stated as three hypotheses on an arbitrary probability space rather than on a fixed product space; a satisfying instance (the coordinate process under the infinite product measure) is proved in the mission's verification files. Slots are indexed from $0$: slot $t$ here is the paper's slot $t+1$.
-- source:
--   Zhang, Gong, Li, Wu & Zhang, Improving Blockchain Consistency by Assigning Weights to Random Blocks, arXiv:2107.10467v2, §2.1, p.5 (law of the honest characteristic string)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace Ironclad

/-- The honest characteristic symbols `{0, h, H}` of Zhang, Gong, Li, Wu & Zhang, *Improving
Blockchain Consistency by Assigning Weights to Random Blocks*, arXiv:2107.10467v2, §2.1, p.5:
`zero` means no honest block in the slot, `h` an honest regular block, `H` an honest iron block.

**Formalization Note** The symbol type is the three-element inductive `{zero, h, H}`, with the
discrete σ-algebra. -/
inductive Sym
  | zero
  | h
  | H
  deriving DecidableEq, Repr

instance : Fintype Sym :=
  ⟨{.zero, .h, .H}, fun x => by cases x <;> simp⟩

instance : MeasurableSpace Sym := ⊤

instance : DiscreteMeasurableSpace Sym := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- The one-slot law of an honest symbol, arXiv:2107.10467v2, §2.1, p.5:
`h` with probability `(1 − q) p_h`, `H` with probability `q p_h`, `0` with probability `1 − p_h`. -/
def symMass (ph q : ℝ) : Sym → ℝ
  | .h => (1 - q) * ph
  | .H => q * ph
  | .zero => 1 - ph

/-- The honest characteristic string model, arXiv:2107.10467v2, §2.1, p.5: "each symbol in
honest characteristic strings is independently drawn according to" `symMass ph q`.
`w t ω` is the symbol of time slot `t` in the outcome `ω`.

**Formalization Note** The i.i.d. law is stated as three hypotheses on an arbitrary probability
space `(Ω, μ)`: each `w t` is measurable, the family `(w t)_t` is mutually independent, and every
`w t` has the law `symMass ph q`. Slots are indexed from `0`: slot `t` here is the paper's slot
`t + 1`. -/
structure IsHonestString {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (w : ℕ → Ω → Sym)
    (ph q : ℝ) : Prop where
  measurable : ∀ t, Measurable (w t)
  indep : iIndepFun w μ
  law : ∀ t s, μ.real (w t ⁻¹' {s}) = symMass ph q s

end Ironclad


