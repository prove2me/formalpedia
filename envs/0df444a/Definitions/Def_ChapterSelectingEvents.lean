-- Prove2me | Definitions.Def_ChapterSelectingEvents
-- name    : ChapterSelectingEvents
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T11:04:45.117993+00:00
-- url     : https://prove2.me/theorems/a9e125e7-8a34-48b9-bf65-4a54e46606ed
-- title:
--   Chapter SelectingEvents
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSelectingEvents.lean`): generated def bundle for ChapterSelectingEvents. See BookProof/ChapterSelectingEvents.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSelectingEvents.lean

import Definitions.Def_ChapterBayesInference
import Definitions.Def_ChapterAbelianDiagonal
import Mathlib


/-!
# Book chapter "Selecting events is not rewriting the history of events"

This file formalizes the core mathematical claims of Chapter 13 (book.tex lines
8303–9086).  The central insight is that in a continuous probability space
(no atoms), singleton events have measure zero, so conditioning on them is not
defined via the standard formula — yet regular conditional probabilities
exist and can be used instead.  The chapter also discusses the P≠NP problem,
the classification of abelian von Neumann algebras, and the consequences for
Machine Learning.

The formalization focuses on the measure-theoretic core; the complexity-theoretic
and philosophical claims are documented as open problems with stated reasons
why they cannot be formalized in the current Mathlib ecosystem.
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace BookProof.ChapterSelectingEvents

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
## 1. The basic fact: singletons have null measure in a continuous space

In a continuous probability space we can select events such that a random
real variable y ∈ [0,1] verifies y = 0, but there is no complete history of
events where y = 0 (always, or even just once) because the probability space
is continuous by assumption and thus the event y = 0 has null measure.

Formally: if μ has no atoms (`NullSingletonClass μ`), then every singleton has measure zero.
-/





/-!
## 2. Regular conditional probabilities always exist

From book.tex lines 8505–8526: in a standard measure space it is always possible
to define regular conditional probability densities.  Mathlib provides
`condExpKernel` for this purpose.

The following theorem states that for any finite measure on a standard Borel
space, the regular conditional probability kernel exists and can be evaluated
on any measurable set.
-/

variable {Ω Data : Type*} [MeasurableSpace Ω]



/-!
## 3. The 5 isomorphism classes of abelian von Neumann algebras

From book.tex lines 8789–8800: a standard probability space is isomorphic
(up to null sets) to one of exactly five abelian von Neumann algebras:

1. ℓ∞({1,…,n}) for n ≥ 1
2. ℓ∞(ℕ)
3. L∞([0,1])
4. L∞([0,1] ∪ {1,…,n}) for n ≥ 1
5. L∞([0,1] ∪ ℕ)

We state this classification as a theorem (using `VonNeumannAlgebra` from Mathlib).
The full classification is a major theorem (von Neumann's original result); we
state it as a `def` recording the claim, with a docstring noting that the proof
is beyond the scope of this formalization.
-/

open VonNeumannAlgebra

/-
The classification of abelian von Neumann algebras: every abelian von Neumann
algebra is *-isomorphic to one of the five standard types (ℓ∞({1,…,n}), ℓ∞(ℕ),
L∞([0,1]), L∞([0,1] ∪ {1,…,n}), L∞([0,1] ∪ ℕ)).  This is von Neumann's
original classification theorem (book.tex lines 8789–8800).

**Removed (August 2026).**  The following pair was a `True` placeholder: the
`def` weakened the claim to the trivially true proposition, so the accompanying
`theorem` proved nothing.  It is kept here, commented out, for the record, and
replaced below by the *genuine* first case of the classification, proved in
`BookProof/ChapterAbelianDiagonal.lean`.

    def vonNeumann_abelian_classification : Prop :=
      True

    theorem vonNeumann_abelian_classification_true :
        vonNeumann_abelian_classification := by
      trivial
-/



/-!
## 4. P ≠ NP

From book.tex lines 8850–8884: the chapter sketches a proof that P ≠ NP using
the continuous probability space framework.  The proof has two cases:

1. Fully deterministic selection → indicator functions for events in a continuous
   measure are in NP but not in P.
2. Approximately deterministic selection → same conclusion via polynomial wave-functions.

The formalization of P vs NP is beyond the scope of this file (it requires
a formal definition of polynomial-time computability, which Mathlib does not
currently provide).  We document this as an open problem rather than an axiom.
-/

-- The claim that P ≠ NP, as argued in Chapter 13 using continuous probability
-- spaces.  This is documented as an open problem because a formal proof would
-- require defining complexity classes P and NP in Lean, which is not yet
-- available in Mathlib.
-- **Removed (August 2026).**  `def p_ne_np : Prop := True` was a placeholder whose
-- statement had been weakened to the trivially true proposition; the name would
-- have suggested a claim that is not made.  It is recorded here, commented out.
--
--     def p_ne_np : Prop := True

/-!
## 5. Worst-case vs best-case prior measures

From book.tex lines 8677–8786: any mixed prior measure contains an interval where
it is continuous.  Rescaling this interval to [0,1] yields a continuous measure
whose results cannot be reproduced by any mixed measure.  This converts the
worst-case prior measure into the best-case prior measure.
-/

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]



/-!
## 6. Random number generation

From book.tex lines 8975–10007: the generation of random numbers from a uniform
distribution has linear time complexity in the number of bits.  This is an
e mpirical claim about physical random number generators (e.g., ANU QRNG).
We document this as an open problem rather than an axiom.
-/

-- Random number generation from a uniform distribution has linear time
-- complexity in the number of bits.  This is an empirical claim; a formal proof
-- would require a physical model of computation.
--
-- Documented in prose only: the claim is precise but unprovable in the current
-- formalism.
-- **Removed (August 2026).**  `def random_generation_linear_time : Prop := True`
-- was likewise a placeholder weakened to the trivially true proposition.  It is
-- recorded here, commented out.
--
--     def random_generation_linear_time : Prop := True

/-!
## 7. Consequences for Machine Learning

From book.tex lines 9008–9086: the chapter argues that deep learning implicitly
uses a prior measure (the measure over local maxima of the optimization problem).
This prior is emergent and uncontrollable, unlike a defined probability measure.

We formalize the key identity: the prior measure over trained models induced by
random initialization and training.
-/

variable {Seed Model : Type*} [Fintype Seed] [Fintype Model] [DecidableEq Model]

/-- The prior measure over trained models induced by random initialization
and a training map.  This is the finite version of the emergent prior in deep
learning (book.tex lines 9067–9079).

Given a probability distribution `seedProb` on seeds and a training function
`train : Seed → Model`, the induced prior on models is the pushforward measure:
`inducedPrior m = ∑_{s : train s = m} seedProb s`.

This prior emerges from the training dynamics and cannot be controlled directly. -/
noncomputable def inducedPrior (seedProb : Seed → ℝ) (train : Seed → Model)
    (m : Model) : ℝ :=
  ∑ s ∈ Finset.filter (fun s => train s = m) Finset.univ, seedProb s





end BookProof.ChapterSelectingEvents


