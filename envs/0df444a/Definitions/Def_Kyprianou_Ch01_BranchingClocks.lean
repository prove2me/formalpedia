-- Prove2me | Definitions.Def_Kyprianou_Ch01_BranchingClocks
-- name    : Kyprianou_Ch01_BranchingClocks
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-14T00:12:38.453756+00:00
-- url     : https://prove2.me/theorems/4a1687f4-6e7e-4ea4-88fd-e12a7a888c42
-- title:
--   Discrete Markov branching law, Laplace cumulants and Lamperti occupation time change
-- statement:
--   Source-faithful primitive definitions from Kyprianou §1.3.4, pp. 23–26: branching distribution convolution, time-homogeneous branching semigroup, one-ancestor Laplace transform, offspring jump mechanism, forward occupation clock J and its inverse, and the time-changed population path with extinction convention. Reverse clock and full compound-Poisson equivalence remain to be formalised; this definition bundle does not assert them as facts.
-- source:
--   Kyprianou (2006), Chapter 1, Definition 1.14, pp. 24–26, equations (1.17)–(1.19), Exercise 1.11, pp. 31–32.

import Mathlib

open MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

namespace Kyprianou.Ch01

/-- Laws of the population size from each initial population at each time. -/
abbrev PopulationLaws := ℕ → ℝ≥0 → PMF ℕ

/-- Definition 1.14: descendants of disjoint initial populations are
    independent, so their sum has the convolution distribution. -/
def HasBranchingProperty (law : PopulationLaws) : Prop :=
  ∀ (a b : ℕ) (t : ℝ≥0),
    law (a + b) t =
      (law a t).bind (fun n => (law b t).map (fun m => n + m))

/-- Time-homogeneous Markov transition kernel of a branching population. -/
def IsPopulationMarkovSemigroup (law : PopulationLaws) : Prop :=
  ∀ (y : ℕ) (s t : ℝ≥0),
    law y (s + t) = (law y s).bind (fun n => law n t)

/-- Laplace transform of the integer-valued branching population. -/
noncomputable def branchingLaplace
    (law : PopulationLaws) (y : ℕ) (t : ℝ≥0) (phi : ℝ) : ℝ :=
  ∑' n : ℕ, (law y t n).toReal * Real.exp (-phi * (n : ℝ))

/-- The logarithmic Laplace cumulant u_t(phi), determined by one ancestor. -/
noncomputable def branchingU
    (law : PopulationLaws) (t : ℝ≥0) (phi : ℝ) : ℝ :=
  -Real.log (branchingLaplace law 1 t phi)

/-- Offspring law p_k: the population jump is k-1. -/
noncomputable def branchingMechanism
    (lambda : ℝ) (offspring : PMF ℕ) (q : ℝ) : ℝ :=
  lambda * ∑' k : ℕ,
    (offspring k).toReal * (1 - Real.exp (-q * ((k : ℝ) - 1)))

/-- Lamperti's forward occupation clock J_t = ∫_0^t Y_s ds. -/
noncomputable def branchingOccupation
    {Ω : Type*} (Y : ℝ≥0 → Ω → ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..(t : ℝ), (Y (Real.toNNReal s) ω : ℝ)

/-- Right-continuous inverse occupation clock, infinite if no crossing occurs. -/
noncomputable def inverseBranchingOccupation
    {Ω : Type*} (Y : ℝ≥0 → Ω → ℕ) (t : ℝ≥0)
    (ω : Ω) : WithTop ℝ≥0 :=
  by
    classical
    exact if ∃ s : ℝ≥0, (t : ℝ) < branchingOccupation Y s ω then
      ((sInf ({s : ℝ≥0 | (t : ℝ) < branchingOccupation Y s ω} : Set ℝ≥0) : ℝ≥0) :
        WithTop ℝ≥0)
    else ⊤

/-- The discrete Lamperti forward time change X_t = Y_(phi_t), with 0
    beyond the extinction clock. -/
noncomputable def branchingToPoisson
    {Ω : Type*} (Y : ℝ≥0 → Ω → ℕ) (t : ℝ≥0) (ω : Ω) : ℕ :=
  match inverseBranchingOccupation Y t ω with
  | none => 0
  | some s => Y s ω

end Kyprianou.Ch01


