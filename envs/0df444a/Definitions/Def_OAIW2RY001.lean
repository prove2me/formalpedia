-- Prove2me | Definitions.Def_OAIW2RY001
-- name    : OAIW2RY001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T04:25:19.687715+00:00
-- url     : https://prove2.me/theorems/c3ccff8c-960f-4a5b-b746-b333ec49d55d
-- title:
--   Definitions bundle OAIW2RY001 of the split of OpenAI, A counterexample to Ryser's covering conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.RyserCoveringCounterexample.exists_prime_eventually_counterexampleRank`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Ryser's covering conjecture*, OpenAI Math Release, September 23, 2026, result family 162, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 56 declarations of OpenAI's Lean: 43 definitions, 1 inductive type or structure and 12 theorems. The definitions and types are `OAI.RyserCoveringCounterexample.Incidence.differenceWalkLabels`, `OAI.RyserCoveringCounterexample.Incidence.neighbors`, `OAI.RyserCoveringCounterexample.Incidence.quotientWalkEval`, `OAI.RyserCoveringCounterexample.Incidence.scalarCollisionCount`, `OAI.RyserCoveringCounterexample.Incidence.scalarCoverExponent`, `OAI.RyserCoveringCounterexample.Incidence.upperDegreeCutoff`, `OAI.RyserCoveringCounterexample.Incidence.walkQuotientLabels`, `OAI.RyserCoveringCounterexample.InjectionSampling.relationCount`, `OAI.RyserCoveringCounterexample.InjectionSampling.restrict`, `OAI.RyserCoveringCounterexample.IsMatching`, `OAI.RyserCoveringCounterexample.LineCover.RigidityParameters`, `OAI.RyserCoveringCounterexample.LineCover.countTailConstant`, `OAI.RyserCoveringCounterexample.LineCover.coveredPoints`, `OAI.RyserCoveringCounterexample.LineCover.heavyPoints`, `OAI.RyserCoveringCounterexample.LineCover.highFailureEnvelope`, `OAI.RyserCoveringCounterexample.LineCover.logarithmicSampleSize`, `OAI.RyserCoveringCounterexample.LineCover.lowFailureEnvelope`, `OAI.RyserCoveringCounterexample.LineCover.multiplicity`, `OAI.RyserCoveringCounterexample.LineCover.orderedPairMass`, `OAI.RyserCoveringCounterexample.LineCover.overlapExcess`, `OAI.RyserCoveringCounterexample.LineCover.rigidityBudget`, `OAI.RyserCoveringCounterexample.LineCover.tupleTailConstant`, `OAI.RyserCoveringCounterexample.NonemptyEdges`, `OAI.RyserCoveringCounterexample.Selection.candidateChunk`, `OAI.RyserCoveringCounterexample.Selection.certificateEventBound`, `OAI.RyserCoveringCounterexample.Selection.chunkCount`, `OAI.RyserCoveringCounterexample.Selection.chunkPrefix`, `OAI.RyserCoveringCounterexample.Selection.chunkRank`, `OAI.RyserCoveringCounterexample.Selection.densityAlpha`, `OAI.RyserCoveringCounterexample.Selection.densityChunkCount`, `OAI.RyserCoveringCounterexample.Selection.densityDelta`, `OAI.RyserCoveringCounterexample.Selection.densityFailureBound`, `OAI.RyserCoveringCounterexample.Selection.densityGamma`, `OAI.RyserCoveringCounterexample.Selection.densityRate`, `OAI.RyserCoveringCounterexample.Selection.equationBound`, `OAI.RyserCoveringCounterexample.Selection.regularTailConstant`, `OAI.RyserCoveringCounterexample.Selection.selectionCutoff`, `OAI.RyserCoveringCounterexample.Selection.selectionFailureBound`, `OAI.RyserCoveringCounterexample.Selection.selectionLargeCoefficient`, `OAI.RyserCoveringCounterexample.Selection.selectionLargeFactor` and 4 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Ryser_Geometry_ProjectiveTransformXY`, `Ryser_Hypergraph_Definitions`, `Ryser_Hypergraph_Matching`, `Ryser_Incidence_PruningNumerics`, `Ryser_Incidence_ScalarCollisionCount`, `Ryser_Incidence_ScalarCoverExpressions`, `Ryser_Incidence_WalkCounts`, `Ryser_Incidence_WalkExpansion`, `Ryser_Incidence_WalkQuotients`, `Ryser_LineCover_FailureNumerics`, `Ryser_LineCover_InjectionSampling`, `Ryser_LineCover_Overlap`, `Ryser_LineCover_RigidityNumerics`, `Ryser_LineCover_RigidityParameters`, `Ryser_LineCover_TailNumerics`, `Ryser_LineCover_TupleConcentration`, `Ryser_LineCover_TwoPopulationMoments`, `Ryser_Selection_CertificateBounds`, `Ryser_Selection_ChunkPartition`, `Ryser_Selection_ChunkTail`, `Ryser_Selection_DensityConstants`, `Ryser_Selection_NumericLimits`, `Ryser_Selection_Parameters`.
--
--   **Imports.** It imports the published bundle `Def_RyserCovering`.
--
--   **Imported by** (directly, in this split): the bundle `OAIW2RY002`.
-- source:
--   OpenAI, A counterexample to Ryser's covering conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 162; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Counterexample-to-Rysers-Covering-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_RyserCovering

section
-- module Solutions.OAIW2_RyserCov.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
end OAICompat434

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Geometry_ProjectiveTransformXY
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample

variable {F : Type*} [Field F]

theorem swapXY_projection_equation (a b x y : F) (ha : a ≠ 0) :
    (x - a⁻¹ * y = -b / a) ↔ (y - a * x = b) := by
  have hrewrite : x - a⁻¹ * y = -(y - a * x) / a := by
    field_simp [ha]; ring
  rw [hrewrite, div_left_inj' ha]
  exact neg_inj

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Hypergraph_Definitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample

variable {V : Type*} [DecidableEq V]

def NonemptyEdges (H : Hypergraph V) : Prop := ∀ e ∈ H, e.Nonempty

def IsMatching (H M : Hypergraph V) : Prop :=
  M ⊆ H ∧ (M : Set (Finset V)).Pairwise Disjoint

def Uniform (r : ℕ) (H : Hypergraph V) : Prop := ∀ e ∈ H, e.card = r

end RyserCoveringCounterexample

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Hypergraph_Matching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample

variable {V : Type*} [instDecidableEqV : DecidableEq V]

@[simp] theorem mem_matchings {H M : Hypergraph V} :
    M ∈ matchings H ↔ IsMatching H M := let _ := instDecidableEqV; by
  classical
  simp only [matchings, Finset.mem_filter, Finset.mem_powerset, IsMatching]

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_PruningNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Incidence

noncomputable def upperDegreeCutoff (U q : ℝ) : ℝ := 16 * U ^ 3 * Real.sqrt q

end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_ScalarCollisionCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Incidence

open scoped BigOperators

variable {F : Type*} [Field F] [instDecidableEqF : DecidableEq F]

def scalarCollisionCount (E : Finset F) (a : F) : ℕ :=
  (((E.product E).product (E.product E)).filter
    (fun p => p.1.1 + a * p.1.2 = p.2.1 + a * p.2.2)).card

end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_ScalarCoverExpressions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Incidence

open scoped Pointwise

variable {F : Type*} [Field F] [instDecidableEqF : DecidableEq F]

def scalarCoverExponent : ℕ → ℕ
  | 0 => 4
  | m + 1 => 3 * scalarCoverExponent m + 5

@[simp] theorem scalarCoverExponent_zero :
    scalarCoverExponent 0 = 4 := rfl

@[simp] theorem scalarCoverExponent_succ (m : ℕ) :
    scalarCoverExponent (m + 1) =
      3 * scalarCoverExponent m + 5 := rfl

end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_WalkCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Incidence

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def neighbors (A : Finset α) (G : Finset (α × β)) (b : β) : Finset α :=
  A.filter fun a => (a, b) ∈ G

@[simp] theorem mem_neighbors (A : Finset α) (G : Finset (α × β)) (a : α) (b : β) :
    a ∈ neighbors A G b ↔ a ∈ A ∧ (a, b) ∈ G := by
  simp only [neighbors, Finset.mem_filter]

end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_WalkExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Incidence

open scoped Pointwise

variable {F : Type*} [Field F] [instDecidableEqF : DecidableEq F]

def differenceWalkLabels (a a' : F) (w : Σ _ : F, F × F) :
    (F × F) × (F × F) :=
  ((a - w.2.1, w.1 - w.2.1), (w.1 - w.2.2, a' - w.2.2))

end RyserCoveringCounterexample.Incidence

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_WalkQuotients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Incidence

open scoped Pointwise

variable {F : Type*} [Field F] [instDecidableEqF : DecidableEq F]

def walkQuotientLabels (a a' : F) (w : Σ _ : F, F × F) :
    (F × F) × (F × F) :=
  ((a / w.2.1, w.1 / w.2.1), (w.1 / w.2.2, a' / w.2.2))

def quotientWalkEval (q : (F × F) × (F × F)) : F :=
  q.1.1 * q.2.1 / (q.1.2 * q.2.2)

end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_TailNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.LineCover

open Filter Topology

def logarithmicSampleSize (A q : ℝ) : ℕ := ⌈A * Real.log q⌉₊

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_FailureNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.LineCover

open Filter Topology

def lowFailureEnvelope (D : ℕ) (δ A κ q : ℝ) : ℝ :=
  let h := 10 * (D + 1)
  let t := (logarithmicSampleSize A q : ℝ)
  (16 / δ) * (((D : ℝ) + 4) * q ^ (-(7 * κ / 30)) + q ^ (-(3 * κ / 4))) +
    (16 * (t ^ 2 * q ^ (-(1 / 2 - κ / 4))) +
      32 * (t ^ 3 * q ^ (-(1 / 2 - κ / 4)))) +
    ((D : ℝ) * (8 * (D : ℝ)) ^ h) *
      (t ^ (2 * h) * q ^ (-((h : ℝ) * (1 / 2 - κ / 4) - D)))

def highFailureEnvelope (D : ℕ) (δ ρ A κ q : ℝ) : ℝ :=
  let h := 10 * (D + 1)
  let t := (logarithmicSampleSize A q : ℝ)
  (4 * ((D : ℝ) + 4) / (δ * ρ)) * q ^ (-(3 * κ / 20)) +
    (t ^ 2 * q ^ (-(1 / 2 + κ / 4)) +
      t ^ 3 * q ^ (-(1 / 2 + κ / 4))) +
    ((D : ℝ) * (4 * (D : ℝ)) ^ h) *
      (t ^ (2 * h) * q ^ (-((h : ℝ) * (1 / 2 + κ / 4) - D)))

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_InjectionSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.InjectionSampling

universe u v w

def restrict {I : Type u} {J : Type v} {Ω : Type w}
    (j : I ↪ J) (sample : J ↪ Ω) : I ↪ Ω :=
  j.trans sample

@[simp] theorem restrict_apply {I : Type u} {J : Type v} {Ω : Type w}
    (j : I ↪ J) (sample : J ↪ Ω) (i : I) :
    restrict j sample i = sample (j i) := rfl

theorem sample_nonempty (I : Type u) (Ω : Type v) [Fintype I] [Fintype Ω]
    (hle : Nat.card I ≤ Nat.card Ω) : Nonempty (I ↪ Ω) :=
  Function.Embedding.nonempty_of_card_le
    (by simpa only [Nat.card_eq_fintype_card] using hle)

end RyserCoveringCounterexample.InjectionSampling

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_Overlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {P Λ : Type*} [instDecidableEqP : DecidableEq P] [instDecidableEqΛ : DecidableEq Λ]

def multiplicity (I : P → Λ → Prop) (L : Finset Λ) (x : P) : ℕ :=
  (L.filter (I x)).card

def coveredPoints (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ) : Finset P :=
  X.filter fun x => 0 < multiplicity I L x

def overlapExcess (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ) : ℕ :=
  ∑ x ∈ X, (multiplicity I L x - 1)

def orderedPairMass (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ) : ℕ :=
  ∑ x ∈ X, multiplicity I L x * (multiplicity I L x - 1)

def heavyPoints (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ) (T : ℝ) :
    Finset P := X.filter fun x => T ≤ (multiplicity I L x : ℝ)

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_RigidityNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.LineCover

open Filter Topology

def rigidityBudget (D : ℕ) (κ q : ℝ) : ℝ :=
  2 * q ^ (3 / 2 + κ / 10) + ((D : ℝ) + 2) * q

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_RigidityParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.LineCover

open Filter Topology

structure RigidityParameters (D : ℕ) (δ ρ A κ q : ℝ) : Prop where
  q_one : 1 ≤ q
  m_four : 4 ≤ q / 2
  m_h : 4 * ((10 * (D + 1) : ℕ) : ℝ) ≤ q / 2
  m_t : 2 * (logarithmicSampleSize A q : ℝ) ≤ q / 2
  h_t : 10 * (D + 1) ≤ logarithmicSampleSize A q
  r_t : (logarithmicSampleSize A q : ℝ) ≤ q ^ (1 / 2 + κ / 4)
  r_h : 2 * ((10 * (D + 1) : ℕ) : ℝ) ≤ q ^ (1 / 2 + κ / 4)
  n_t : (logarithmicSampleSize A q : ℝ) ≤ ρ * q / 2
  n_h : 2 * ((10 * (D + 1) : ℕ) : ℝ) ≤ ρ * q / 2
  T_one : 1 < q ^ (1 / 2 - κ / 3)
  gap_half : rigidityBudget D κ q / (δ * q) ≤ q / 2
  gap_rho : rigidityBudget D κ q / (δ * q) ≤ ρ * q / 2
  heavy : rigidityBudget D κ q / (q ^ (1 / 2 - κ / 3) - 1) ≤ q ^ (1 + κ)
  low : lowFailureEnvelope D δ A κ q < 1
  high : highFailureEnvelope D δ ρ A κ q < 1
  lineerror : q ^ (1 / 2 + κ / 10) ≤ δ * q / 2

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_TupleConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

def countTailConstant (D H : ℕ) (δ : ℝ) : ℝ :=
  min (δ ^ 2 / (16 * (D : ℝ) ^ 2 * ((D : ℝ) * (H : ℝ)) ^ 2))
    (δ / (16 * ((D : ℝ) * (H : ℝ))))

def tupleTailConstant (D h : ℕ) (δ : ℝ) : ℝ :=
  countTailConstant D (2 * D * h) δ

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_TwoPopulationMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RyserCoveringCounterexample.InjectionSampling

def relationCount {A B : Type*} [Fintype A] [Fintype B] {t : ℕ}
    (S : Finset (A × B)) (z : (Fin t ↪ A) × (Fin t ↪ B)) : ℕ :=
  (Finset.univ.filter fun ij : Fin t × Fin t => (z.1 ij.1, z.2 ij.2) ∈ S).card

end RyserCoveringCounterexample.InjectionSampling

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_ChunkTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n K : ℕ}

def equationBound (D : ℕ) : ℝ := 2 * (D : ℝ) ^ 3

def regularTailConstant (D : ℕ) (γ : ℝ) : ℝ :=
  (8 * equationBound D * (D : ℝ) ^ 7 + 2 * (D : ℝ) ^ 5) / γ ^ 2

end RyserCoveringCounterexample.Selection

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_DensityConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Selection

def densityChunkCount (D : ℕ) : ℕ := 16 * D ^ 4 + 1

def densityAlpha (D : ℕ) : ℝ := 1 / (4 * (D : ℝ) ^ 3)

def densityDelta (D : ℕ) : ℝ := (1 / 2 : ℝ) ^ (densityChunkCount D + 1)

def densityGamma (D : ℕ) : ℝ :=
  densityDelta D / (2 * (densityAlpha D + 4 * (D : ℝ) ^ 3))

def densityRate (D : ℕ) : ℝ := densityGamma D / 4

end RyserCoveringCounterexample.Selection

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_Parameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace RyserCoveringCounterexample.Selection

def selectionCutoff (D : ℕ) : ℝ := 1 / (4 * equationBound D)
def selectionSmallFactor (D : ℕ) : ℝ := 6 * equationBound D * Real.exp 1 * (D : ℝ)
def selectionLargeFactor (D : ℕ) : ℝ := (Real.exp 1 * (D : ℝ) / selectionCutoff D) * 3
def selectionSmallCoefficient (D K : ℕ) : ℝ := selectionSmallFactor D * (K : ℝ) ^ 2
def selectionLargeCoefficient (D K : ℕ) : ℝ := selectionLargeFactor D * (K : ℝ) ^ 2

end RyserCoveringCounterexample.Selection

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_ChunkPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Selection

variable {E : Type*} [DecidableEq E]

noncomputable def chunkRank (T : Finset E) (e : E) : ℕ :=
  if h : e ∈ T then (T.equivFin ⟨e, h⟩).val else 0

def chunkCount (T : Finset E) (L : ℕ) : ℕ := T.card / L + 1

noncomputable def candidateChunk (T : Finset E) (L j : ℕ) : Finset E :=
  T.filter (fun e => chunkRank T e / L = j)

noncomputable def chunkPrefix (T : Finset E) (L j : ℕ) : Finset E :=
  T.filter (fun e => chunkRank T e / L < j)

@[simp] theorem mem_candidateChunk (T : Finset E) (L j : ℕ) (e : E) :
    e ∈ candidateChunk T L j ↔ e ∈ T ∧ chunkRank T e / L = j :=
  Finset.mem_filter

@[simp] theorem mem_chunkPrefix (T : Finset E) (L j : ℕ) (e : E) :
    e ∈ chunkPrefix T L j ↔ e ∈ T ∧ chunkRank T e / L < j :=
  Finset.mem_filter

@[simp] theorem chunkPrefix_zero (T : Finset E) (L : ℕ) :
    chunkPrefix T L 0 = ∅ := by
  ext e
  simp only [mem_chunkPrefix, Nat.not_lt_zero, and_false, Finset.notMem_empty]

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_CertificateBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u
noncomputable section
namespace RyserCoveringCounterexample.Selection

def smallCertificateBase (D q m : ℕ) : ℝ :=
  (2 * (m : ℝ)) * ((2 * (D : ℝ) ^ 3) / (q : ℝ))

def densityFailureBound (D q : ℕ) : ℝ :=
  (densityChunkCount D : ℝ) * Real.exp (-densityRate D * (q : ℝ) * Real.log (q : ℝ))

def certificateEventBound (D K q m : ℕ) : ℝ :=
  if (m : ℝ) ≤ selectionCutoff D * (q : ℝ) then
    smallCertificateBase D q m ^ ((K - 2) * m)
  else densityFailureBound D q + Real.exp (-(((K : ℝ) * densityDelta D - 2) * (m : ℝ)))

end RyserCoveringCounterexample.Selection

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_NumericLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace RyserCoveringCounterexample.Selection

noncomputable def selectionFailureBound (D K R : ℕ) (A B C J c c1 : ℝ) (q : ℕ) : ℝ :=
  (R : ℝ) * A * (2 * C * (R : ℝ) / (q : ℝ)) ^ (K - 3) + (1 / 2 : ℝ) ^ R +
    J * ((D : ℝ) * (q : ℝ)) * B ^ (D * q) *
      Real.exp (-c * (q : ℝ) * Real.log (q : ℝ)) +
    (1 / 2 : ℝ) ^ Nat.floor (c1 * (q : ℝ))

end RyserCoveringCounterexample.Selection

end OAI
end


