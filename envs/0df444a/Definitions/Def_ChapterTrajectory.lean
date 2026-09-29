-- Prove2me | Definitions.Def_ChapterTrajectory
-- name    : ChapterTrajectory
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:12:00.977093+00:00
-- url     : https://prove2.me/theorems/9cfb08a3-1609-416c-b130-60c30d16d9e3
-- title:
--   Source: `book.tex`, chapter *"Reconstructing the classical trajectory of any isolated quantum system"*, §*"Reconstructio ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.Trajectory`, source chapter `BookProof/ChapterTrajectory.lean`).
--
--   Source: `book.tex`, chapter *"Reconstructing the classical trajectory of any isolated quantum system"*, §*"Reconstruction of the trajectory"* (`book.tex` line ~3044).
--
--   The book argues that although only the *final* time of a quantum trajectory can be measured directly, *post-selection* — "using probabilities conditional on the final state and the same quantum time-evolution" — lets us "repeat the experiment in the same conditions and predict the results of a measurement at another time between the initial and final times", so that the trajectory can be reconstructed at intermediate instants.
--
--   We formalize the three-instant (initial → intermediate → final) *collapsed* Born process on a finite phase space `Fin n`. A unit initial wave-function `Ψ` is evolved by a unitary `U` to the intermediate time, where a measurement in the standard basis produces outcome `a` with the Born probability `midProb = |(U Ψ)_a|²` and collapses the state to `e_a`; the collapsed state is then evolved by a unitary `V` to the final time, where outcome `f` occurs with probability `transProb = |V_{f a}|²`.
--
--   * `jointProb U V Ψ f a = midProb · transProb` is the joint law of (intermediate `a`, final `f`). * `finalProb U V Ψ f = ∑ₐ jointProb` is the marginal final law. * `condProb U V Ψ f a = jointProb / finalProb` is the **post-selected** (conditional on the final outcome `f`) law of the intermediate outcome — the Aharonov–Bergmann–Lebowitz / two-state reconstruction formula.
--
--   Main results: * `finalProb_total` — the collapsed process is a genuine probability law: `∑_f finalProb = 1` (uses unitarity of `U`, `V` and `‖Ψ‖ = 1`). * `jointProb_sum_final_eq_midProb` — summing the post-selected joint law over all final outcomes recovers the intermediate Born distribution (consistency of the reconstruction: the intermediate statistics do not depend on which final outcome one post-selects on). * `condProb_sum` — for any realizable final outcome the post-selected intermediate law is a probability distribution (`∑ₐ condProb = 1`).
--
--   Concrete double-slit capstone (reusing `ChapterDoubleSlit`'s Hadamard `H`): * `dslit_finalProb` / `dslit_condProb` — with `U = V = H` and `Ψ = (1,0)` the collapsed final law is uniform `1/2` and post-selecting on any final outcome reconstructs the uniform `1/2` intermediate law; * `dslit_coherentFinal` — the *coherent* final law (no intermediate measurement, `|(V U Ψ)_f|²`) is instead `(1, 0)`; * `dslit_interference` — the two differ (`finalProb = 1/2 ≠ 1 = coherentFinal`): the "self-interference mystery", i.e. why the reconstructed (post-selected) picture is *not* what coherent evolution gives.
--
--   Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterTrajectory.lean

import Mathlib
import Mathlib
import Definitions.Def_ChapterDoubleSlit

import Mathlib

import Mathlib
open BookProof.ChapterDoubleSlit

/-!
# Chapter "Reconstructing the classical trajectory of any isolated quantum system"
— §"Reconstruction of the trajectory" (post-selection / conditional probability)

Source: `book.tex`, chapter *"Reconstructing the classical trajectory of any
isolated quantum system"*, §*"Reconstruction of the trajectory"*
(`book.tex` line ~3044).

The book argues that although only the *final* time of a quantum trajectory can
be measured directly, *post-selection* — "using probabilities conditional on the
final state and the same quantum time-evolution" — lets us "repeat the experiment
in the same conditions and predict the results of a measurement at another time
between the initial and final times", so that the trajectory can be
reconstructed at intermediate instants.

We formalize the three-instant (initial → intermediate → final) *collapsed* Born
process on a finite phase space `Fin n`.  A unit initial wave-function `Ψ` is
evolved by a unitary `U` to the intermediate time, where a measurement in the
standard basis produces outcome `a` with the Born probability
`midProb = |(U Ψ)_a|²` and collapses the state to `e_a`; the collapsed state is
then evolved by a unitary `V` to the final time, where outcome `f` occurs with
probability `transProb = |V_{f a}|²`.

* `jointProb U V Ψ f a = midProb · transProb` is the joint law of
  (intermediate `a`, final `f`).
* `finalProb U V Ψ f = ∑ₐ jointProb` is the marginal final law.
* `condProb U V Ψ f a = jointProb / finalProb` is the **post-selected**
  (conditional on the final outcome `f`) law of the intermediate outcome — the
  Aharonov–Bergmann–Lebowitz / two-state reconstruction formula.

Main results:
* `finalProb_total` — the collapsed process is a genuine probability law:
  `∑_f finalProb = 1` (uses unitarity of `U`, `V` and `‖Ψ‖ = 1`).
* `jointProb_sum_final_eq_midProb` — summing the post-selected joint law over all
  final outcomes recovers the intermediate Born distribution (consistency of the
  reconstruction: the intermediate statistics do not depend on which final
  outcome one post-selects on).
* `condProb_sum` — for any realizable final outcome the post-selected
  intermediate law is a probability distribution (`∑ₐ condProb = 1`).

Concrete double-slit capstone (reusing `ChapterDoubleSlit`'s Hadamard `H`):
* `dslit_finalProb` / `dslit_condProb` — with `U = V = H` and `Ψ = (1,0)` the
  collapsed final law is uniform `1/2` and post-selecting on any final outcome
  reconstructs the uniform `1/2` intermediate law;
* `dslit_coherentFinal` — the *coherent* final law (no intermediate measurement,
  `|(V U Ψ)_f|²`) is instead `(1, 0)`;
* `dslit_interference` — the two differ (`finalProb = 1/2 ≠ 1 = coherentFinal`):
  the "self-interference mystery", i.e. why the reconstructed (post-selected)
  picture is *not* what coherent evolution gives.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open scoped BigOperators Matrix

namespace BookProof.ChapterTrajectory

variable {n : ℕ}

/-- Intermediate Born probability of outcome `a`: `|(U Ψ)_a|²`. -/
noncomputable def midProb (U : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ)
    (a : Fin n) : ℝ := ‖(U *ᵥ psi) a‖ ^ 2

/-- Transition probability from intermediate outcome `a` to final outcome `f`
after the collapse: `|V_{f a}|²`. -/
noncomputable def transProb (V : Matrix (Fin n) (Fin n) ℂ) (f a : Fin n) : ℝ :=
  ‖V f a‖ ^ 2

/-- Joint probability of (intermediate `a`, final `f`) in the collapsed
three-instant process. -/
noncomputable def jointProb (U V : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ)
    (f a : Fin n) : ℝ := midProb U psi a * transProb V f a

/-- Marginal probability of the final outcome `f`. -/
noncomputable def finalProb (U V : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ)
    (f : Fin n) : ℝ := ∑ a, jointProb U V psi f a

/-- Post-selected (conditional on final outcome `f`) probability of the
intermediate outcome `a` — the ABL / two-state reconstruction formula. -/
noncomputable def condProb (U V : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ)
    (f a : Fin n) : ℝ := jointProb U V psi f a / finalProb U V psi f

/-- The *coherent* final Born probability, with **no** intermediate measurement:
`|(V U Ψ)_f|²`. -/
noncomputable def coherentFinal (U V : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ)
    (f : Fin n) : ℝ := ‖((V * U) *ᵥ psi) f‖ ^ 2

/-! ## Nonnegativity -/











/-! ## Reconstruction consistency and total mass -/











/-! ## Double-slit capstone (reusing `ChapterDoubleSlit`'s Hadamard `H`) -/














end BookProof.ChapterTrajectory


