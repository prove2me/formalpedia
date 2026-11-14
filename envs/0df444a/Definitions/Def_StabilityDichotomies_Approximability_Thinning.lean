-- Prove2me | Definitions.Def_StabilityDichotomies_Approximability_Thinning
-- name    : StabilityDichotomies_Approximability_Thinning
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T06:33:26.299898+00:00
-- url     : https://prove2.me/theorems/341b2ce7-2eac-486f-83c1-1370efe8018c
-- title:
--   Exact thinning output law for Horn and dual-Horn CSPs
-- statement:
--   The denotational output law of Definition 4.2: every occurrence of a constraint receives an independent Bernoulli retention decision, conditional on a retention probability drawn uniformly from [1−ε,1]. The output is the coordinatewise least solution in the Horn case and greatest solution in the dual-Horn case. Repeated constraints are indexed separately, and isolated variables remain in the fixed carrier. This definition states an output-law relation and does not assert existence of a solver or any computational runtime.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, Definition 4.2, p. 16, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_Core

noncomputable section
open scoped Classical BigOperators Interval
open MeasureTheory
namespace StabilityDichotomies.Solvability

/-- Index a constraint occurrence in a chosen ordering of the input multiset. Equal constraints
remain distinct occurrences, so independent thinning is represented correctly. -/
def occurrenceAt {Γ : Language} {V : Type} (I : Instance Γ V)
    (i : Fin I.constraints.card) : Constraint Γ V :=
  I.constraints.toList.get ⟨i.1, by simpa using i.2⟩

/-- Retain exactly the indexed occurrences selected by a Boolean mask. -/
def thinnedInstance {Γ : Language} {V : Type} (I : Instance Γ V)
    (mask : Fin I.constraints.card → Bool) : Instance Γ V :=
  ⟨((List.ofFn fun i : Fin I.constraints.card => (i, occurrenceAt I i)).filter
      (fun p => mask p.1)).map Prod.snd⟩

/-- The least solution for `b=false`, the greatest for `b=true`, with an arbitrary fallback when
no such solution exists. On Horn or dual-Horn satisfiable subinstances, the extremum exists and is
unique; the fallback does not affect the paper's satisfiable inputs. -/
def extremalSolution {Γ : Language} {V : Type} (I : Instance Γ V) (b : Bool) : V → Bool :=
  if h : ∃ x : V → Bool, Solution I x ∧
      ∀ y : V → Bool, Solution I y → (if b then y ≤ x else x ≤ y) then
    Classical.choose h
  else fun _ => b

/-- The Bernoulli-p probability of an occurrence mask. -/
def retentionWeight {m : ℕ} (p : ℝ) (mask : Fin m → Bool) : ℝ :=
  ∏ i, if mask i then p else 1 - p

/-- Exact denotational output law of Definition 4.2. For a satisfiable input, draw p uniformly from
`[1-ε,1]`, retain each occurrence independently with probability p, and return the least solution
when `b=false` or the greatest solution when `b=true`. The equality is stated for every output
assignment, with the finite mask sum integrated over p. The relation does not assert an algorithmic
runtime or construct a solver; these remain separate obligations. -/
def ThinningOutputLaw (Γ : Language) (b : Bool) (ε : ℝ) (A : Solver Γ) : Prop :=
  ∀ (V : Type) [Fintype V] (I : Instance Γ V), Satisfiable I → ∀ x : V → Bool,
    (A V I x).toReal = ε⁻¹ *
      ∫ p in (1 - ε)..1, ∑ mask : Fin I.constraints.card → Bool,
        retentionWeight p mask *
          (if extremalSolution (thinnedInstance I mask) b = x then 1 else 0)

end StabilityDichotomies.Solvability


