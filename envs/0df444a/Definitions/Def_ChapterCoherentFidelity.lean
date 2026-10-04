-- Prove2me | Definitions.Def_ChapterCoherentFidelity
-- name    : ChapterCoherentFidelity
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T07:56:02.78401+00:00
-- url     : https://prove2.me/theorems/f75abff3-1638-4c2e-b235-3ea208168878
-- title:
--   Chapter CoherentFidelity
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterCoherentFidelity.lean`): generated def bundle for ChapterCoherentFidelity. See BookProof/ChapterCoherentFidelity.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterCoherentFidelity.lean

import Definitions.Def_ChapterCoherentOverlapComplex
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib


/-!
# Chapter "The Coherent State of Attention" — the **quantum fidelity** of coherent
states

`Book/CoherentState.lean` §"Temperature and the Thermal Bath" phrases the
comparison of two wave-packets as a *fidelity*: the probability that a
measurement prepared in the state `|q⟩` is found in the state `|k⟩`.  For pure
states this is `F(q,k) = |⟨q|k⟩|²`, which is exactly the Born numerator
`ChapterCoherentOverlapComplex.bornNumerC` of the attention weight.

This module proves the closed form of that fidelity for **complex** coherent-state
parameters and the properties the prose uses:

* `fidelityC_eq_exp_neg_dist_sq` — the **headline**: the fidelity of two coherent
  states is `exp (-‖q - k‖²)`, a pure function of the distance between the two
  displacement parameters.  The phase of the Bargmann kernel has dropped out and
  so have the individual norms;
* `fidelityC_symm`, `fidelityC_pos`, `fidelityC_le_one`, `fidelityC_self`,
  `fidelityC_eq_one_iff` — the fidelity is a symmetric, strictly positive
  quantity bounded by `1`, attaining `1` exactly on equal parameters;
* `fidelityC_translation_invariant` — displacing *both* states by the same vector
  leaves the fidelity unchanged: the fidelity of two displaced states depends only
  on the relative displacement.  This is the formal content of "the packet is
  rigid and only its centre moves";
* `fidelityC_le_iff_dist_le`, `fidelityC_lt_iff_dist_lt` — the fidelity is
  strictly antitone in the distance;
* `bornWeightC_eq_scoreSoftmax_neg_dist_sq` — the complex Born attention weight is
  the Softmax over minus the squared distances at inverse temperature `1`; i.e.
  **attention is the normalized fidelity**, `bornWeightC_eq_fidelity_normalized`;
* `fidelityC_ofReal` — the real theory of `ChapterCoherentGeometry` is the
  restriction of this one to real parameters.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

noncomputable section

namespace BookProof.ChapterCoherentFidelity

open BookProof.ChapterCoherentOverlapComplex BookProof.ChapterSoftmaxSharpness

variable {n m : ℕ}

/-! ## The fidelity and its closed form -/

/-- The **quantum fidelity** of two (complex) coherent states: the Born
probability `|⟨q|k⟩|²`. -/
def fidelityC (q k : EuclideanSpace ℂ (Fin n)) : ℝ := ‖coherentOverlapC q k‖ ^ 2

















/-! ## The fidelity is a strictly decreasing readout of the distance -/







/-! ## Attention is the normalized fidelity -/





/-! ## The real case -/



end BookProof.ChapterCoherentFidelity

end


