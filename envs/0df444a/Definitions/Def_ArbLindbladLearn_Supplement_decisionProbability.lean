-- Prove2me | Definitions.Def_ArbLindbladLearn_Supplement_decisionProbability
-- name    : ArbLindbladLearn_Supplement_decisionProbability
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:20:42.374275+00:00
-- url     : https://prove2.me/theorems/d1670e0b-d1dd-4e0b-bbce-b86c74fdfbc2
-- title:
--   Probability that an open-ended protocol halts with a given decision
-- statement:
--   For an open-ended protocol $p$ run against a generator $\mathcal L$ and a decision $y\in\{\text{yes},\text{no}\}$, the **decision probability** is the probability that the run eventually stops and decides $y$, measuring $E_h$ (yes) or $1-E_h$ (no) at the history $h$ where it stops.
--
--   It is the limit of the probabilities $p_{y,N}$ of stopping with decision $y$ after at most $N$ queries, which increase with $N$; runs that never stop never decide.
--
--   **Formalization Note** The probabilities after at most $N$ queries are nested lower Lebesgue integrals over the instruments' outcomes of the Born densities, as in the public `runOutcome`; the decision probability is their supremum over $N$, in $[0,\infty]$.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), proof of Theorem 5.8, p.48

import Mathlib
import Definitions.Def_ArbLindbladLearn_Supplement_OpenProtocol

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn.Supplement

open MeasureTheory
open LindbladTolerant.Testing

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The probability mass, from history `h` with unnormalized state `ρ`, of halting within `q` further
queries with decision `yes` (`true`: the effect `E_h`; `false`: `1 − E_h`). Branches still running
after `q` queries contribute `0`. -/
def decideUpTo (p : OpenProtocol n Ω) (g : Super (Qubits n) (Qubits n)) (yes : Bool) :
    (q : ℕ) → (h : List Ω) → Op (Qubits n × Fin (p.memory h)) → ℝ≥0∞
  | 0, h, ρ => if p.stop h then
      ENNReal.ofReal (((if yes then p.effect h else 1 - p.effect h) * ρ).trace.re) else 0
  | q + 1, h, ρ => if p.stop h then
      ENNReal.ofReal (((if yes then p.effect h else 1 - p.effect h) * ρ).trace.re) else
      ∫⁻ o, decideUpTo p g yes q (h ++ [o])
        (applySuper ((p.instrument h).branch o)
          (tensorId (evolution g (p.duration h)) ρ)) ∂(p.instrument h).base

/-- The probability that the open-ended protocol `p`, run against the generator `g` (each query
applies `e^{tg} ⊗ id`), halts with decision `yes` (proof of Theorem 5.8, p.48, Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…): "Let `p_{d,N}`
be the probability that the original protocol returns the correct decision after at most `N`
queries … These probabilities increase to the original success probabilities").

**Formalization Note** The supremum over `q` of the truncated masses `decideUpTo … q`, which are
nondecreasing in `q`; values in `ℝ≥0∞`. Runs that never halt never decide. The Born integrals are
nested lower Lebesgue integrals against the instruments' base measures with the CP densities, as in
the public `runOutcome`. -/
def decisionProbability (p : OpenProtocol n Ω) (g : Super (Qubits n) (Qubits n)) (yes : Bool) :
    ℝ≥0∞ :=
  ⨆ q : ℕ, decideUpTo p g yes q [] p.initial

end ArbLindbladLearn.Supplement


