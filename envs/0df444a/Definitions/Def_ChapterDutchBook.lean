-- Prove2me | Definitions.Def_ChapterDutchBook
-- name    : ChapterDutchBook
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:44:19.76722+00:00
-- url     : https://prove2.me/theorems/40849201-0dae-400f-ba6b-4f949a474faa
-- title:
--   Chapter DutchBook
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterDutchBook.lean`): generated def bundle for ChapterDutchBook. See BookProof/ChapterDutchBook.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterDutchBook.lean

import Mathlib


/-!
# The de Finetti Dutch-Book coherence theorem (finite sample space)

Source: `book.tex`, chapter *"Consciousness as a representation of a Bayesian
prior"*, §*"Non-informative priors vs. Fermi Paradox and Artificial General
Intelligence"* (`book.tex` line ~9142), where the book invokes the classical
**Dutch-book** argument (`\cite{dutchbook}`) underpinning the Bayesian
interpretation of probability that the whole book is built on: a system of
betting prices is *coherent* (cannot be turned into a guaranteed loss) **iff**
those prices are the expectations of a genuine probability distribution.

This module formalizes that statement (finite version, on a finite sample
space `Ω`).

## Setup

* An **event** is a `Finset Ω`; a **price function** `Pr : Finset Ω → ℝ`
  assigns each event its fair betting quotient.
* A **gamble** on an event `A` with stake `s` pays the bettor
  `s * (1_A(ω) - Pr A)` in state `ω` (they pay `s * Pr A` up front and
  receive `s` iff `A` occurs).  A finite family of gambles has total payoff
  `payoff Pr A s ω = ∑ i, s i * (1_{A i}(ω) - Pr (A i))`.
* `HasDutchBook Pr` — there is a finite family of gambles whose payoff is
  **strictly negative in every state** (a guaranteed loss).
* `Coherent Pr := ¬ HasDutchBook Pr`.
* `Represents Pr p` — `Pr A = ∑_{ω ∈ A} p ω`; `IsProb p` — `p ≥ 0` and
  `∑ p = 1`.

## Results (all `sorry`-free, axiom-clean)

* Easy direction `represents_isProb_coherent` — prices coming from a genuine
  probability distribution are coherent (the `p`-expected payoff is `0`, so it
  cannot be negative everywhere).
* From coherence, the probability axioms follow by explicit Dutch books:
  `Coherent.empty` (`Pr ∅ = 0`), `Coherent.univ` (`Pr univ = 1`),
  `Coherent.nonneg` (`0 ≤ Pr A`), `Coherent.le_one` (`Pr A ≤ 1`),
  `Coherent.additive` (finite additivity on disjoint events).
* `Coherent.represents_singleton` — `Pr A = ∑_{ω ∈ A} Pr {ω}` (additivity over
  singletons), whence the hard direction `coherent_exists_prob` — a coherent
  price function is represented by the probability distribution `ω ↦ Pr {ω}`.
* Headline `coherent_iff_exists_prob` — `Coherent Pr ↔ ∃ probability p,
  Represents Pr p`.
-/

open scoped BigOperators
open Finset

namespace BookProof.ChapterDutchBook

variable {Ω : Type*} [DecidableEq Ω]

/-- Indicator of an event as a real number: `1` if `ω ∈ A`, else `0`. -/
def betIndicator (A : Finset Ω) (ω : Ω) : ℝ := if ω ∈ A then 1 else 0



/-- Total payoff to the bettor of a finite family of gambles (events `A i`,
stakes `s i`) in state `ω`. -/
def payoff {m : ℕ} (Pr : Finset Ω → ℝ) (A : Fin m → Finset Ω) (s : Fin m → ℝ)
    (ω : Ω) : ℝ :=
  ∑ i, s i * (betIndicator (A i) ω - Pr (A i))

/-- A price function admits a **Dutch book**: a finite family of gambles whose
payoff is strictly negative in *every* state (a guaranteed loss). -/
def HasDutchBook (Pr : Finset Ω → ℝ) : Prop :=
  ∃ (m : ℕ) (A : Fin m → Finset Ω) (s : Fin m → ℝ), ∀ ω, payoff Pr A s ω < 0

/-- A price function is **coherent** if it admits no Dutch book. -/
def Coherent (Pr : Finset Ω → ℝ) : Prop := ¬ HasDutchBook Pr

/-- `p` is a probability distribution: nonnegative weights summing to `1`. -/
def IsProb [Fintype Ω] (p : Ω → ℝ) : Prop := (∀ ω, 0 ≤ p ω) ∧ ∑ ω, p ω = 1

/-- The price function `Pr` is represented by the weights `p`:
`Pr A = ∑_{ω ∈ A} p ω`. -/
def Represents (Pr : Finset Ω → ℝ) (p : Ω → ℝ) : Prop :=
  ∀ A : Finset Ω, Pr A = ∑ ω ∈ A, p ω

/-! ### Payoff of a single gamble -/





/-! ### Easy direction: probability ⇒ coherent -/



/-! ### Hard direction: coherent ⇒ probability, via explicit Dutch books -/

















end BookProof.ChapterDutchBook


