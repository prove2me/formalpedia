-- Prove2me | Definitions.Def_OAIW2RY002
-- name    : OAIW2RY002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T04:27:20.569931+00:00
-- url     : https://prove2.me/theorems/474afa74-46ef-4c5f-ba16-bd392fd238c5
-- title:
--   Definitions bundle OAIW2RY002 of the split of OpenAI, A counterexample to Ryser's covering conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.RyserCoveringCounterexample.exists_prime_eventually_counterexampleRank`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Ryser's covering conjecture*, OpenAI Math Release, September 23, 2026, result family 162, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 183 declarations of OpenAI's Lean: 96 definitions, 1 instance and 86 theorems. The definitions and types are `OAI.RyserCoveringCounterexample.Incidence.pencilSlice`, `OAI.RyserCoveringCounterexample.Incidence.pruningPotential`, `OAI.RyserCoveringCounterexample.Incidence.ratioSubfield`, `OAI.RyserCoveringCounterexample.InjectionSampling.law`, `OAI.RyserCoveringCounterexample.LineCover.AdmissibleTuple`, `OAI.RyserCoveringCounterexample.LineCover.ComplementPopulation`, `OAI.RyserCoveringCounterexample.LineCover.CoverSample`, `OAI.RyserCoveringCounterexample.LineCover.CrossHit`, `OAI.RyserCoveringCounterexample.LineCover.DeletionProcess.Config`, `OAI.RyserCoveringCounterexample.LineCover.DeletionProcess.law`, `OAI.RyserCoveringCounterexample.LineCover.DeletionProcess.survivorSet`, `OAI.RyserCoveringCounterexample.LineCover.FiniteCrossings`, `OAI.RyserCoveringCounterexample.LineCover.GoodCounts`, `OAI.RyserCoveringCounterexample.LineCover.GoodTuples`, `OAI.RyserCoveringCounterexample.LineCover.HighSample`, `OAI.RyserCoveringCounterexample.LineCover.LowBad`, `OAI.RyserCoveringCounterexample.LineCover.LowDegeneracy.AnyConcurrent`, `OAI.RyserCoveringCounterexample.LineCover.LowDegeneracy.AnyParallel`, `OAI.RyserCoveringCounterexample.LineCover.LowDegeneracy.Concurrent`, `OAI.RyserCoveringCounterexample.LineCover.LowDegeneracy.SameDirection`, `OAI.RyserCoveringCounterexample.LineCover.LowDegeneracy.firstPair`, `OAI.RyserCoveringCounterexample.LineCover.LowDegeneracy.pairMeet`, `OAI.RyserCoveringCounterexample.LineCover.NoConcurrentTriple`, `OAI.RyserCoveringCounterexample.LineCover.NoParallel`, `OAI.RyserCoveringCounterexample.LineCover.PencilPopulation`, `OAI.RyserCoveringCounterexample.LineCover.cleanLines`, `OAI.RyserCoveringCounterexample.LineCover.contribution`, `OAI.RyserCoveringCounterexample.LineCover.crossHitCount`, `OAI.RyserCoveringCounterexample.LineCover.highBadLines`, `OAI.RyserCoveringCounterexample.LineCover.highCollisionLines`, `OAI.RyserCoveringCounterexample.LineCover.highCrossPairs`, `OAI.RyserCoveringCounterexample.LineCover.highFailureBound`, `OAI.RyserCoveringCounterexample.LineCover.highParallelLines`, `OAI.RyserCoveringCounterexample.LineCover.highShapePairs`, `OAI.RyserCoveringCounterexample.LineCover.highSurvivorPairCount`, `OAI.RyserCoveringCounterexample.LineCover.highTuple`, `OAI.RyserCoveringCounterexample.LineCover.highUniformLaw`, `OAI.RyserCoveringCounterexample.LineCover.liftSample`, `OAI.RyserCoveringCounterexample.LineCover.linecoverFailureBound`, `OAI.RyserCoveringCounterexample.LineCover.lowFailureBound` and 56 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Ryser_Domination_Basic`, `Ryser_Domination_TraceDefinitions`, `Ryser_Field_Extension`, `Ryser_Geometry_ProjectiveJoins`, `Ryser_Geometry_ProjectiveTransformAffine`, `Ryser_Geometry_ProjectiveTransformXY`, `Ryser_Geometry_ProjectiveTransformXZ`, `Ryser_Geometry_SliceEnergy`, `Ryser_Incidence_Pencils`, `Ryser_Incidence_PruningCore`, `Ryser_Incidence_RatioSet`, `Ryser_LineCover_CleanCover`, `Ryser_LineCover_Definitions`, `Ryser_LineCover_Deletion`, `Ryser_LineCover_GoodCounts`, `Ryser_LineCover_GoodTuples`, `Ryser_LineCover_HighDegeneracy`, `Ryser_LineCover_HighProbability`, `Ryser_LineCover_HighSamples`, `Ryser_LineCover_InjectionSampling`, `Ryser_LineCover_LowConcurrency`, `Ryser_LineCover_LowDegeneracy`, `Ryser_LineCover_LowOccupancy`, `Ryser_LineCover_Main`, `Ryser_LineCover_MaxConcurrency`, `Ryser_LineCover_PairCounting`, `Ryser_LineCover_Process`, `Ryser_LineCover_ProjectiveLift`, `Ryser_LineCover_SamplingDefinitions`, `Ryser_LineCover_TupleGeometry`, `Ryser_Selection_Chunk`, `Ryser_Selection_ChunkLoss`, `Ryser_Selection_ChunkTail`, `Ryser_Selection_Definitions`, `Ryser_Selection_FeasibleDensity`, `Ryser_Selection_Forbidden`, `Ryser_Selection_PoolCounts`, `Ryser_Selection_PoolLaw`, `Ryser_Selection_SmallCertificates`.
--
--   **Imports.** It imports the bundles `OAIW2RY000` and `OAIW2RY001` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.RyserCoveringCounterexample.LineCover.goodLineCover_of_goodCounts_goodTuples` and `OAI.RyserCoveringCounterexample.Selection.compatible_selection_uniform`; the proofs of `OAI.RyserCoveringCounterexample.Construction.exists_goodAmbientPool_uniform`, `OAI.RyserCoveringCounterexample.Construction.exists_prime_goodGadget`, `OAI.RyserCoveringCounterexample.Incidence.uniform_incidence_bound`, `OAI.RyserCoveringCounterexample.LineCover.goodLineCover_of_goodCounts_goodTuples`, `OAI.RyserCoveringCounterexample.Selection.compatible_selection_uniform` and `OAI.RyserCoveringCounterexample.exists_prime_eventually_counterexampleRank`.
-- source:
--   OpenAI, A counterexample to Ryser's covering conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 162; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Counterexample-to-Rysers-Covering-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIW2RY000
import Definitions.Def_OAIW2RY001

section
-- module Solutions.OAIW2_RyserCov.Ryser_Domination_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Selection

variable {V ι : Type*} [instDecidableEqV : DecidableEq V] [DecidableEq ι]

def DominatesOn (G : Graph V) (pool : V → ι)
    (I : Finset ι) (T : Finset V) : Prop :=
  ∀ x, pool x ∈ I → x ∉ T → ∃ y ∈ T, G.Adj x y

def DominationCertificate (G : Graph V) (pool : V → ι) : Prop :=
  ∃ I : Finset ι, ∃ T : Finset V,
    I.Nonempty ∧ (∀ x ∈ T, pool x ∈ I) ∧
    T.card ≤ 2 * (I.card - 1) ∧ DominatesOn G pool I T

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Domination_TraceDefinitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Selection

variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

namespace DominationTrace

variable {G : Graph V} {pool : V → ι} {J : Finset ι} {root : ι} {k : ℕ}

def indices (t : DominationTrace G pool J root k) : Finset ι :=
  insert root (t.verticesY.image pool)

def vertices (t : DominationTrace G pool J root k) : Finset V :=
  t.verticesX ∪ t.verticesY

def empty (v : V) {U : Finset V} (hU : IsTransversalOn G pool J U) :
    DominationTrace G pool J root 0 where
  x := fun _ => v
  y := fun _ => ∅
  nonempty := by simp
  disjoint := by simp
  realized := ⟨U, hU, by simp⟩
  minimal := by simp
  origin := by simp

end DominationTrace
end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Field_Extension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample

noncomputable instance extensionFieldFintype (p n : ℕ) [Fact p.Prime] :
    Fintype (ExtensionField p n) := Fintype.ofFinite _

noncomputable def primeEmbedding (p n : ℕ) [Fact p.Prime] :
    ZMod p →+* ExtensionField p n := algebraMap _ _

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Geometry_ProjectiveJoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample

variable {F : Type*} [Field F]

theorem existsUnique_projectivePoint_of_ne {l m : ProjectiveLine F}
    (hlm : l ≠ m) :
    ∃! p : ProjectivePoint F, ProjectiveIncidence p l ∧ ProjectiveIncidence p m := by
  classical
  cases l with
  | none =>
    cases m with
    | none => exact (hlm rfl).elim
    | some m =>
      refine ⟨Sum.inr m.1, ⟨trivial, rfl⟩, ?_⟩
      intro p hp
      cases p with
      | inl p => exact hp.1.elim
      | inr d => exact congrArg Sum.inr hp.2
  | some l =>
    cases m with
    | none =>
      refine ⟨Sum.inr l.1, ⟨rfl, trivial⟩, ?_⟩
      intro p hp
      cases p with
      | inl p => exact hp.2.elim
      | inr d => exact congrArg Sum.inr hp.1
    | some m =>
      by_cases hdir : l.1 = m.1
      · refine ⟨Sum.inr l.1, ⟨rfl, hdir⟩, ?_⟩
        intro p hp
        cases p with
        | inl p =>
          have heq : l = m := line_eq_of_direction_eq_of_incidence hdir hp.1 hp.2
          exact (hlm (congrArg some heq)).elim
        | inr d => exact congrArg Sum.inr hp.1
      · obtain ⟨p, hp, huniq⟩ := existsUnique_incident_of_ne_direction l m hdir
        refine ⟨Sum.inl p, hp, ?_⟩
        intro q hq
        cases q with
        | inl q => exact congrArg Sum.inl (huniq q hq)
        | inr d => exact (hdir (hq.1.symm.trans hq.2)).elim

theorem existsUnique_projective_incident_of_ne_lines {l m : AffineLine F}
    (hlm : l ≠ m) :
    ∃! p : ProjectivePoint F,
      ProjectiveIncidence p (some l) ∧ ProjectiveIncidence p (some m) := by
  apply existsUnique_projectivePoint_of_ne
  intro h
  exact hlm (Option.some.inj h)

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Geometry_ProjectiveTransformAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample

variable {F : Type*} [Field F]

def translatePointMap (u v : F) : ProjectivePoint F → ProjectivePoint F
  | Sum.inl p => Sum.inl (p.1 + u, p.2 + v)
  | Sum.inr d => Sum.inr d

def translateLineMap (u v : F) : ProjectiveLine F → ProjectiveLine F
  | none => none
  | some (none, b) => some (none, b + u)
  | some (some a, b) => some (some a, b + v - a * u)

theorem translatePointMap_left_inv (u v : F) :
    Function.LeftInverse (translatePointMap (-u) (-v)) (translatePointMap u v) := by
  rintro (⟨x, y⟩ | d) <;> simp [translatePointMap]

theorem translateLineMap_left_inv (u v : F) :
    Function.LeftInverse (translateLineMap (-u) (-v)) (translateLineMap u v) := by
  intro l
  cases l with
  | none => rfl
  | some l =>
    rcases l with ⟨d, b⟩
    cases d with
    | none => simp [translateLineMap]
    | some slope => simp [translateLineMap]; ring

def translate (u v : F) : ProjectiveTransform F where
  points :=
    { toFun := translatePointMap u v
      invFun := translatePointMap (-u) (-v)
      left_inv := translatePointMap_left_inv u v
      right_inv := by
        intro p
        simpa only [neg_neg] using translatePointMap_left_inv (-u) (-v) p }
  lines :=
    { toFun := translateLineMap u v
      invFun := translateLineMap (-u) (-v)
      left_inv := translateLineMap_left_inv u v
      right_inv := by
        intro l
        simpa only [neg_neg] using translateLineMap_left_inv (-u) (-v) l }
  incidence := by
    intro p l
    change ProjectiveIncidence (translatePointMap u v p) (translateLineMap u v l) ↔
      ProjectiveIncidence p l
    cases p with
    | inl p =>
      rcases p with ⟨x, y⟩
      cases l with
      | none => rfl
      | some l =>
        rcases l with ⟨d, b⟩
        cases d with
        | none => simp [translatePointMap, translateLineMap, ProjectiveIncidence,
            Incidence, projection]
        | some a =>
          change y + v - a * (x + u) = b + v - a * u ↔ y - a * x = b
          have hleft : y + v - a * (x + u) = (y - a * x) + (v - a * u) := by ring
          have hright : b + v - a * u = b + (v - a * u) := by ring
          rw [hleft, hright]
          exact add_right_cancel_iff
    | inr d =>
      cases l with
      | none => rfl
      | some l =>
        rcases l with ⟨e, b⟩
        cases e <;> rfl

@[simp] theorem translate_points_finite (u v : F) (p : Point F) :
    (translate u v).points (Sum.inl p) = Sum.inl (p.1 + u, p.2 + v) := rfl

@[simp] theorem translate_points_infinite (u v : F) (d : Direction F) :
    (translate u v).points (Sum.inr d) = Sum.inr d := rfl

@[simp] theorem translate_lines_infinity (u v : F) :
    (translate u v).lines none = none := rfl

@[simp] theorem translate_lines_vertical (u v b : F) :
    (translate u v).lines (some (none, b)) = some (none, b + u) := rfl

@[simp] theorem translate_lines_slope (u v a b : F) :
    (translate u v).lines (some (some a, b)) = some (some a, b + v - a * u) := rfl

def shearPointMap (r : F) : ProjectivePoint F → ProjectivePoint F
  | Sum.inl p => Sum.inl (p.1, p.2 + r * p.1)
  | Sum.inr none => Sum.inr none
  | Sum.inr (some a) => Sum.inr (some (a + r))

def shearLineMap (r : F) : ProjectiveLine F → ProjectiveLine F
  | none => none
  | some (none, b) => some (none, b)
  | some (some a, b) => some (some (a + r), b)

theorem shearPointMap_left_inv (r : F) :
    Function.LeftInverse (shearPointMap (-r)) (shearPointMap r) := by
  intro p
  cases p with
  | inl p => rcases p with ⟨x, y⟩; simp [shearPointMap]
  | inr d => cases d <;> simp [shearPointMap]

theorem shearLineMap_left_inv (r : F) :
    Function.LeftInverse (shearLineMap (-r)) (shearLineMap r) := by
  intro l
  cases l with
  | none => rfl
  | some l =>
    rcases l with ⟨d, b⟩
    cases d <;> simp [shearLineMap]

def shear (r : F) : ProjectiveTransform F where
  points :=
    { toFun := shearPointMap r
      invFun := shearPointMap (-r)
      left_inv := shearPointMap_left_inv r
      right_inv := by
        intro p
        simpa only [neg_neg] using shearPointMap_left_inv (-r) p }
  lines :=
    { toFun := shearLineMap r
      invFun := shearLineMap (-r)
      left_inv := shearLineMap_left_inv r
      right_inv := by
        intro l
        simpa only [neg_neg] using shearLineMap_left_inv (-r) l }
  incidence := by
    intro p l
    change ProjectiveIncidence (shearPointMap r p) (shearLineMap r l) ↔
      ProjectiveIncidence p l
    cases p with
    | inl p =>
      rcases p with ⟨x, y⟩
      cases l with
      | none => rfl
      | some l =>
        rcases l with ⟨d, b⟩
        cases d with
        | none => rfl
        | some a =>
          change y + r * x - (a + r) * x = b ↔ y - a * x = b
          have h : y + r * x - (a + r) * x = y - a * x := by ring
          rw [h]
    | inr d =>
      cases l with
      | none => cases d <;> rfl
      | some l =>
        rcases l with ⟨e, b⟩
        cases d <;> cases e <;> simp [shearPointMap, shearLineMap, ProjectiveIncidence]

@[simp] theorem shear_points_finite (r : F) (p : Point F) :
    (shear r).points (Sum.inl p) = Sum.inl (p.1, p.2 + r * p.1) := rfl

@[simp] theorem shear_points_infinite_vertical (r : F) :
    (shear r).points (Sum.inr none) = Sum.inr none := rfl

@[simp] theorem shear_points_infinite_slope (r a : F) :
    (shear r).points (Sum.inr (some a)) = Sum.inr (some (a + r)) := rfl

@[simp] theorem shear_lines_infinity (r : F) :
    (shear r).lines none = none := rfl

@[simp] theorem shear_lines_vertical (r b : F) :
    (shear r).lines (some (none, b)) = some (none, b) := rfl

@[simp] theorem shear_lines_slope (r a b : F) :
    (shear r).lines (some (some a, b)) = some (some (a + r), b) := rfl

def scaleYPointMap (c : F) : ProjectivePoint F → ProjectivePoint F
  | Sum.inl p => Sum.inl (p.1, c * p.2)
  | Sum.inr none => Sum.inr none
  | Sum.inr (some a) => Sum.inr (some (c * a))

def scaleYLineMap (c : F) : ProjectiveLine F → ProjectiveLine F
  | none => none
  | some (none, b) => some (none, b)
  | some (some a, b) => some (some (c * a), c * b)

theorem scaleYPointMap_left_inv (c : F) (hc : c ≠ 0) :
    Function.LeftInverse (scaleYPointMap c⁻¹) (scaleYPointMap c) := by
  intro p
  cases p with
  | inl p => rcases p with ⟨x, y⟩; simp [scaleYPointMap, hc]
  | inr d => cases d <;> simp [scaleYPointMap, hc]

theorem scaleYLineMap_left_inv (c : F) (hc : c ≠ 0) :
    Function.LeftInverse (scaleYLineMap c⁻¹) (scaleYLineMap c) := by
  intro l
  cases l with
  | none => rfl
  | some l =>
    rcases l with ⟨d, b⟩
    cases d <;> simp [scaleYLineMap, hc]

def scaleY (c : F) (hc : c ≠ 0) : ProjectiveTransform F where
  points :=
    { toFun := scaleYPointMap c
      invFun := scaleYPointMap c⁻¹
      left_inv := scaleYPointMap_left_inv c hc
      right_inv := by
        intro p
        simpa only [inv_inv] using scaleYPointMap_left_inv c⁻¹ (inv_ne_zero hc) p }
  lines :=
    { toFun := scaleYLineMap c
      invFun := scaleYLineMap c⁻¹
      left_inv := scaleYLineMap_left_inv c hc
      right_inv := by
        intro l
        simpa only [inv_inv] using scaleYLineMap_left_inv c⁻¹ (inv_ne_zero hc) l }
  incidence := by
    intro p l
    change ProjectiveIncidence (scaleYPointMap c p) (scaleYLineMap c l) ↔
      ProjectiveIncidence p l
    cases p with
    | inl p =>
      rcases p with ⟨x, y⟩
      cases l with
      | none => rfl
      | some l =>
        rcases l with ⟨d, b⟩
        cases d with
        | none => rfl
        | some a =>
          change c * y - (c * a) * x = c * b ↔ y - a * x = b
          have h : c * y - (c * a) * x = c * (y - a * x) := by ring
          rw [h]
          exact mul_right_inj' hc
    | inr d =>
      cases l with
      | none => cases d <;> rfl
      | some l =>
        rcases l with ⟨e, b⟩
        cases d <;> cases e <;>
          simp [scaleYPointMap, scaleYLineMap, ProjectiveIncidence, mul_right_inj' hc]

@[simp] theorem scaleY_points_finite (c : F) (hc : c ≠ 0) (p : Point F) :
    (scaleY c hc).points (Sum.inl p) = Sum.inl (p.1, c * p.2) := rfl

@[simp] theorem scaleY_points_infinite_vertical (c : F) (hc : c ≠ 0) :
    (scaleY c hc).points (Sum.inr none) = Sum.inr none := rfl

@[simp] theorem scaleY_points_infinite_slope (c : F) (hc : c ≠ 0) (a : F) :
    (scaleY c hc).points (Sum.inr (some a)) = Sum.inr (some (c * a)) := rfl

@[simp] theorem scaleY_lines_infinity (c : F) (hc : c ≠ 0) :
    (scaleY c hc).lines none = none := rfl

@[simp] theorem scaleY_lines_vertical (c : F) (hc : c ≠ 0) (b : F) :
    (scaleY c hc).lines (some (none, b)) = some (none, b) := rfl

@[simp] theorem scaleY_lines_slope (c : F) (hc : c ≠ 0) (a b : F) :
    (scaleY c hc).lines (some (some a, b)) = some (some (c * a), c * b) := rfl

end RyserCoveringCounterexample

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

noncomputable def swapXYDirection (d : Direction F) : Direction F := by
  classical
  exact match d with
    | none => some 0
    | some a => if a = 0 then none else some a⁻¹

@[simp] theorem swapXYDirection_none :
    swapXYDirection (none : Direction F) = some 0 := rfl

@[simp] theorem swapXYDirection_zero :
    swapXYDirection (some (0 : F)) = none := by simp [swapXYDirection]

@[simp] theorem swapXYDirection_nonzero (a : F) (ha : a ≠ 0) :
    swapXYDirection (some a) = some a⁻¹ := by simp [swapXYDirection, ha]

theorem swapXYDirection_involutive :
    Function.Involutive (swapXYDirection (F := F)) := by
  classical
  intro d
  cases d with
  | none => simp [swapXYDirection]
  | some a =>
    by_cases ha : a = 0
    · simp [swapXYDirection, ha]
    · simp [swapXYDirection, ha]

noncomputable def swapXYPoint : ProjectivePoint F → ProjectivePoint F
  | Sum.inl p => Sum.inl (p.2, p.1)
  | Sum.inr d => Sum.inr (swapXYDirection d)

theorem swapXYPoint_involutive :
    Function.Involutive (swapXYPoint (F := F)) := by
  intro p
  cases p with
  | inl p => rfl
  | inr d =>
    change Sum.inr (swapXYDirection (swapXYDirection d)) = Sum.inr d
    rw [swapXYDirection_involutive]

noncomputable def swapXYAffineLine (l : AffineLine F) : AffineLine F := by
  classical
  exact match l with
    | (none, b) => (some 0, b)
    | (some a, b) => if a = 0 then (none, b) else (some a⁻¹, -b / a)

@[simp] theorem swapXYAffineLine_direction (l : AffineLine F) :
    (swapXYAffineLine l).1 = swapXYDirection l.1 := by
  classical
  rcases l with ⟨d, b⟩
  cases d with
  | none => rfl
  | some a =>
    by_cases ha : a = 0 <;> simp [swapXYAffineLine, swapXYDirection, ha]

theorem swapXYAffineLine_involutive :
    Function.Involutive (swapXYAffineLine (F := F)) := by
  classical
  rintro ⟨d, b⟩
  cases d with
  | none => simp [swapXYAffineLine]
  | some a =>
    by_cases ha : a = 0
    · simp [swapXYAffineLine, ha]
    · simp [swapXYAffineLine, ha, div_eq_mul_inv]

noncomputable def swapXYLine : ProjectiveLine F → ProjectiveLine F
  | none => none
  | some l => some (swapXYAffineLine l)

theorem swapXYLine_involutive :
    Function.Involutive (swapXYLine (F := F)) := by
  intro l
  cases l with
  | none => rfl
  | some l =>
    change some (swapXYAffineLine (swapXYAffineLine l)) = some l
    rw [swapXYAffineLine_involutive]

theorem swapXY_affine_incidence (p : Point F) (l : AffineLine F) :
    Incidence (p.2, p.1) (swapXYAffineLine l) ↔ Incidence p l := by
  classical
  rcases p with ⟨x, y⟩
  rcases l with ⟨d, b⟩
  cases d with
  | none => simp [swapXYAffineLine, Incidence, projection]
  | some a =>
    by_cases ha : a = 0
    · simp [swapXYAffineLine, Incidence, projection, ha]
    · simpa only [swapXYAffineLine, ite_eq_right ha, Incidence, projection] using
        swapXY_projection_equation a b x y ha

theorem swapXY_incidence (p : ProjectivePoint F) (l : ProjectiveLine F) :
    ProjectiveIncidence (swapXYPoint p) (swapXYLine l) ↔
      ProjectiveIncidence p l := by
  cases p with
  | inl p =>
    cases l with
    | none => rfl
    | some l => exact swapXY_affine_incidence p l
  | inr d =>
    cases l with
    | none => rfl
    | some l =>
      change swapXYDirection d = (swapXYAffineLine l).1 ↔ d = l.1
      rw [swapXYAffineLine_direction]
      exact swapXYDirection_involutive.injective.eq_iff

noncomputable def swapXY (F : Type*) [Field F] : ProjectiveTransform F where
  points :=
    { toFun := swapXYPoint
      invFun := swapXYPoint
      left_inv := swapXYPoint_involutive
      right_inv := swapXYPoint_involutive }
  lines :=
    { toFun := swapXYLine
      invFun := swapXYLine
      left_inv := swapXYLine_involutive
      right_inv := swapXYLine_involutive }
  incidence := swapXY_incidence

@[simp] theorem swapXY_points_finite (p : Point F) :
    (swapXY F).points (Sum.inl p) = Sum.inl (p.2, p.1) := rfl

@[simp] theorem swapXY_points_infinite (d : Direction F) :
    (swapXY F).points (Sum.inr d) = Sum.inr (swapXYDirection d) := rfl

@[simp] theorem swapXY_lines_infinity :
    (swapXY F).lines none = none := rfl

@[simp] theorem swapXY_lines_affine (l : AffineLine F) :
    (swapXY F).lines (some l) = some (swapXYAffineLine l) := rfl

@[simp] theorem swapXY_lines_vertical (b : F) :
    (swapXY F).lines (some (none, b)) = some (some 0, b) := rfl

@[simp] theorem swapXY_lines_slope_zero (b : F) :
    (swapXY F).lines (some (some 0, b)) = some (none, b) := by
  rw [swapXY_lines_affine]
  simp [swapXYAffineLine]

@[simp] theorem swapXY_lines_slope_nonzero (a b : F) (ha : a ≠ 0) :
    (swapXY F).lines (some (some a, b)) = some (some a⁻¹, -b / a) := by
  rw [swapXY_lines_affine]
  simp [swapXYAffineLine, ha]

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Geometry_ProjectiveTransformXZ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample

variable {F : Type*} [Field F]

noncomputable def swapXZPoint : ProjectivePoint F → ProjectivePoint F := by
  classical
  exact fun p => match p with
    | Sum.inl (x, y) =>
        if x = 0 then Sum.inr (some y) else Sum.inl (1 / x, y / x)
    | Sum.inr none => Sum.inr none
    | Sum.inr (some a) => Sum.inl (0, a)

noncomputable def swapXZLine : ProjectiveLine F → ProjectiveLine F := by
  classical
  exact fun l => match l with
    | none => some (none, 0)
    | some (none, c) => if c = 0 then none else some (none, 1 / c)
    | some (some a, b) => some (some b, a)

@[simp] theorem swapXZPoint_finite_zero (y : F) :
    swapXZPoint (Sum.inl (0, y)) = Sum.inr (some y) := by
  classical
  simp [swapXZPoint]

@[simp] theorem swapXZPoint_infinite_slope (a : F) :
    swapXZPoint (Sum.inr (some a)) = Sum.inl (0, a) := rfl

@[simp] theorem swapXZPoint_infinite_vertical :
    swapXZPoint (Sum.inr (none : Direction F)) = Sum.inr none := rfl

@[simp] theorem swapXZLine_infinity :
    swapXZLine (none : ProjectiveLine F) = some (none, 0) := rfl

@[simp] theorem swapXZLine_vertical_zero :
    swapXZLine (some (none, (0 : F))) = none := by
  classical
  simp [swapXZLine]

@[simp] theorem swapXZLine_sloped (a b : F) :
    swapXZLine (some (some a, b)) = some (some b, a) := rfl

theorem swapXZPoint_involutive : Function.Involutive (swapXZPoint (F := F)) := by
  classical
  intro p
  cases p with
  | inl p =>
    rcases p with ⟨x, y⟩
    by_cases hx : x = 0
    · subst x
      simp [swapXZPoint]
    · have hy : y / x / (1 / x) = y := by
        simpa only [div_one] using div_div_div_cancel_right₀ hx y (1 : F)
      simp [swapXZPoint, hx]
  | inr d =>
    cases d <;> simp [swapXZPoint]

theorem swapXZLine_involutive : Function.Involutive (swapXZLine (F := F)) := by
  classical
  intro l
  cases l with
  | none => simp [swapXZLine]
  | some l =>
    rcases l with ⟨d, c⟩
    cases d with
    | none =>
      by_cases hc : c = 0
      · subst c
        simp [swapXZLine]
      · simp [swapXZLine, hc]
    | some a => rfl

theorem swapXZ_incidence (p : ProjectivePoint F) (l : ProjectiveLine F) :
    ProjectiveIncidence (swapXZPoint p) (swapXZLine l) ↔
      ProjectiveIncidence p l := by
  classical
  cases p with
  | inl p =>
    rcases p with ⟨x, y⟩
    cases l with
    | none =>
      by_cases hx : x = 0
      · simp [swapXZPoint, swapXZLine, ProjectiveIncidence, hx]
      · simp [swapXZPoint, swapXZLine, ProjectiveIncidence, Incidence, projection,
          hx]
    | some l =>
      rcases l with ⟨d, b⟩
      cases d with
      | none =>
        by_cases hx : x = 0
        · by_cases hb : b = 0
          · simp [swapXZPoint, swapXZLine, ProjectiveIncidence, Incidence, projection,
              hx, hb]
          · simp [swapXZPoint, swapXZLine, ProjectiveIncidence, Incidence, projection,
              hx, hb, Ne.symm hb]
        · by_cases hb : b = 0
          · simp [swapXZPoint, swapXZLine, ProjectiveIncidence, Incidence, projection,
              hx, hb]
          · simp only [swapXZPoint, ite_eq_right hx, swapXZLine, ite_eq_right hb,
              ProjectiveIncidence, Incidence, projection]
            exact ⟨eq_of_one_div_eq_one_div,
              fun h => congrArg (fun c : F => 1 / c) h⟩
      | some a =>
        by_cases hx : x = 0
        · simp [swapXZPoint, swapXZLine, ProjectiveIncidence, Incidence, projection, hx]
        · simp only [swapXZPoint, ite_eq_right hx, swapXZLine,
            ProjectiveIncidence, Incidence, projection]
          rw [mul_one_div, ← sub_div, div_eq_iff hx,
            sub_eq_iff_eq_add, sub_eq_iff_eq_add, add_comm (a * x) b]
  | inr d =>
    cases d with
    | none =>
      cases l with
      | none => simp [swapXZPoint, swapXZLine, ProjectiveIncidence]
      | some l =>
        rcases l with ⟨d, c⟩
        cases d with
        | none =>
          by_cases hc : c = 0 <;>
            simp [swapXZPoint, swapXZLine, ProjectiveIncidence, hc]
        | some a => simp [swapXZPoint, swapXZLine, ProjectiveIncidence]
    | some a =>
      cases l with
      | none => simp [swapXZPoint, swapXZLine, ProjectiveIncidence, Incidence, projection]
      | some l =>
        rcases l with ⟨d, c⟩
        cases d with
        | none =>
          by_cases hc : c = 0
          · simp [swapXZPoint, swapXZLine, ProjectiveIncidence, hc]
          · simp [swapXZPoint, swapXZLine, ProjectiveIncidence, Incidence, projection,
              hc, Ne.symm hc]
        | some b =>
          simp [swapXZPoint, swapXZLine, ProjectiveIncidence, Incidence, projection]

noncomputable def swapXZ (F : Type*) [Field F] : ProjectiveTransform F where
  points :=
    { toFun := swapXZPoint
      invFun := swapXZPoint
      left_inv := swapXZPoint_involutive
      right_inv := swapXZPoint_involutive }
  lines :=
    { toFun := swapXZLine
      invFun := swapXZLine
      left_inv := swapXZLine_involutive
      right_inv := swapXZLine_involutive }
  incidence := swapXZ_incidence

@[simp] theorem swapXZ_points (p : ProjectivePoint F) :
    (swapXZ F).points p = swapXZPoint p := rfl

@[simp] theorem swapXZ_lines (l : ProjectiveLine F) :
    (swapXZ F).lines l = swapXZLine l := rfl

@[simp] theorem swapXZ_points_finite_zero (y : F) :
    (swapXZ F).points (Sum.inl (0, y)) = Sum.inr (some y) :=
  swapXZPoint_finite_zero y

@[simp] theorem swapXZ_points_infinite_slope (a : F) :
    (swapXZ F).points (Sum.inr (some a)) = Sum.inl (0, a) := rfl

@[simp] theorem swapXZ_points_infinite_vertical :
    (swapXZ F).points (Sum.inr none) = Sum.inr none := rfl

@[simp] theorem swapXZ_lines_infinity :
    (swapXZ F).lines none = some (none, 0) := rfl

@[simp] theorem swapXZ_lines_vertical_zero :
    (swapXZ F).lines (some (none, 0)) = none :=
  swapXZLine_vertical_zero

@[simp] theorem swapXZ_lines_sloped (a b : F) :
    (swapXZ F).lines (some (some a, b)) = some (some b, a) := rfl

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Geometry_SliceEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample

open scoped BigOperators

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [DecidableEq F]

def sliceCount (U : Finset (Point F)) (d : Direction F) (t : F) : ℕ :=
  (U.filter (fun p => projection d p = t)).card

noncomputable def sliceEnergy (U : Finset (Point F)) (d : Direction F) : ℝ :=
  (∑ t : F, ((sliceCount U d t : ℝ) -
    (U.card : ℝ) / (Fintype.card F : ℝ)) ^ 2) / (Fintype.card F : ℝ)

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_Pencils
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Incidence
noncomputable section
variable {F : Type*} [Field F] [instDecidableEqF : DecidableEq F]

def pencilSlice (L : Finset (ProjectiveLine F)) (p : ProjectivePoint F) :
    Finset (ProjectiveLine F) :=
  L.filter fun l => ProjectiveIncidence p l

end
end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_PruningCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Incidence

variable {Pt Ln : Type*} [instDecidableEqPt : DecidableEq Pt] [instDecidableEqLn : DecidableEq Ln]

def pruningPotential (R : Pt → Ln → Prop) (d : ℝ) (P : Finset Pt) (L : Finset Ln) : ℝ :=
  (incidenceCount R P L : ℝ) - d * ((P.card : ℝ) + (L.card : ℝ))

end RyserCoveringCounterexample.Incidence

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_RatioSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Incidence
noncomputable section
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem mem_ratioSet_of_collision {E : Finset F} {c : F}
    {x y x' y' : F} (hx : x ∈ E) (hy : y ∈ E)
    (hx' : x' ∈ E) (hy' : y' ∈ E)
    (hne : (x, y) ≠ (x', y')) (heq : x + c * y = x' + c * y') :
    c ∈ ratioSet E := by
  have hyy' : y ≠ y' := by
    intro h
    apply hne
    apply Prod.ext
    · exact add_right_cancel (by simpa only [h] using heq)
    · exact h
  apply mem_ratioSet.mpr
  refine ⟨x', hx', x, hx, y, hy, y', hy', hyy', ?_⟩
  apply (div_eq_iff (sub_ne_zero.mpr hyy')).mpr
  calc
    x' - x = (x' + c * y') - (x + c * y') := by ring
    _ = (x + c * y) - (x + c * y') := by rw [heq]
    _ = c * (y - y') := by ring

theorem mem_ratioSet_of_dilateSum_card_lt {E : Finset F} {c : F}
    (hcard : (dilateSum E c).card < E.card ^ 2) : c ∈ ratioSet E := by
  have hcard' : (dilateSum E c).card < (E ×ˢ E).card := by
    simpa only [Finset.card_product, pow_two] using hcard
  obtain ⟨z, hz, z', hz', hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard'
      (f := fun z : F × F => z.1 + c * z.2) (by
        intro z hz
        have hzE := Finset.mem_product.mp hz
        exact mem_dilateSum.mpr ⟨z.1, hzE.1, z.2, hzE.2, rfl⟩)
  have hzE := Finset.mem_product.mp hz
  have hzE' := Finset.mem_product.mp hz'
  exact mem_ratioSet_of_collision hzE.1 hzE.2 hzE'.1 hzE'.2 hne heq

theorem one_mem_ratioSet {E : Finset F} (hE : 2 ≤ E.card) :
    (1 : F) ∈ ratioSet E := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hE
  exact mem_ratioSet.mpr ⟨x, hx, y, hy, x, hx, y, hy, hxy,
    div_self (sub_ne_zero.mpr hxy)⟩

theorem neg_mem_ratioSet {E : Finset F} {c : F} (hc : c ∈ ratioSet E) :
    -c ∈ ratioSet E := by
  obtain ⟨x, hx, x', hx', y, hy, y', hy', hyy', hquot⟩ := mem_ratioSet.mp hc
  apply mem_ratioSet.mpr
  refine ⟨x', hx', x, hx, y, hy, y', hy', hyy', ?_⟩
  rw [← neg_sub x x', neg_div, hquot]

def ratioSubfield (E : Finset F) (hE : 2 ≤ E.card)
    (hadd : ∀ r ∈ ratioSet E, ∀ r' ∈ ratioSet E,
      (dilateSum E (r + r')).card < E.card ^ 2)
    (hmul : ∀ r ∈ ratioSet E, ∀ r' ∈ ratioSet E,
      (dilateSum E (r * r')).card < E.card ^ 2) : Subfield F where
  carrier := (ratioSet E : Set F)
  zero_mem' := zero_mem_ratioSet hE
  one_mem' := one_mem_ratioSet hE
  add_mem' := fun hr hr' => mem_ratioSet_of_dilateSum_card_lt (hadd _ hr _ hr')
  mul_mem' := fun hr hr' => mem_ratioSet_of_dilateSum_card_lt (hmul _ hr _ hr')
  neg_mem' := fun hc => neg_mem_ratioSet hc
  inv_mem' := fun _ hc => inv_mem_ratioSet hE hc

@[simp] theorem mem_ratioSubfield (E : Finset F) (hE : 2 ≤ E.card)
    (hadd : ∀ r ∈ ratioSet E, ∀ r' ∈ ratioSet E,
      (dilateSum E (r + r')).card < E.card ^ 2)
    (hmul : ∀ r ∈ ratioSet E, ∀ r' ∈ ratioSet E,
      (dilateSum E (r * r')).card < E.card ^ 2) (x : F) :
    x ∈ ratioSubfield E hE hadd hmul ↔ x ∈ ratioSet E := Iff.rfl

end
end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_Definitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.LineCover

open scoped Classical

variable {F : Type*} [instFieldF : Field F] [instFintypeF : Fintype F] [instDecidableEqF : DecidableEq F]

def FiniteCrossings {t : ℕ} (a : LineTuple F t) : Prop :=
  ∀ i j, ∃ x, Incidence x (a (Sum.inl i)) ∧ Incidence x (a (Sum.inr j))

def AdmissibleTuple (shapes : Finset (Finset (Point F))) (D h : ℕ)
    {t : ℕ} (a : LineTuple F t) : Prop :=
  FiniteCrossings a ∧ (crossPoints a).card = t * t ∧
    ∀ S ∈ shapes, S ∉ tupleShapes a → (S ∩ crossPoints a).card ≤ 2 * D * h

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_Process
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {shapes : Finset (Finset (Point F))} {D n : ℕ}

namespace DeletionProcess

variable {δ : ℝ} (process : DeletionProcess F D δ)

abbrev Config := Fin process.trialsCount → Outcome process.shapes D

def law : FiniteLaw process.Config := FiniteLaw.pi process.trials

def survivorSet (ω : process.Config) : Finset (Point F) := survivors ∅ ω

end DeletionProcess
end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_CleanCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {shapes : Finset (Finset (Point F))} {D n : ℕ}

def cleanLines (ω : Fin n → Outcome shapes D) (L : Finset (AffineLine F)) :
    Finset (AffineLine F) := L.filter fun l => linePoints l ∉ selected ω

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_Deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {P : Type*} [DecidableEq P]
  {shapes : Finset (Finset P)} {D n : ℕ}

def contribution (ignore : Finset (Finset P)) (test : Finset P)
    (a : Outcome shapes D) : Finset P := deleted ignore a ∩ test

def rare (ignore : Finset (Finset P)) (test : Finset P)
    (a : Outcome shapes D) : Prop := (contribution ignore test a).Nonempty

@[simp] theorem contribution_emptyOutcome (ignore : Finset (Finset P))
    (test : Finset P) : contribution ignore test (emptyOutcome shapes D) = ∅ := by
  simp [contribution]

variable [instFintypeP : Fintype P]

def retainedCount (ignore : Finset (Finset P)) (test : Finset P)
    (ω : Fin n → Outcome shapes D) : ℝ :=
  ((survivors ignore ω ∩ test).card : ℝ)

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_GoodCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {D : ℕ} {δ : ℝ}

def GoodCounts (process : DeletionProcess F D δ) (ε : ℝ)
    (ω : process.Config) : Prop :=
  |((survivors ∅ ω).card : ℝ) - process.survival * (Fintype.card F : ℝ) ^ 2| ≤
      (Fintype.card F : ℝ) ^ ((3 : ℝ) / 2 + ε) ∧
    ∀ l : AffineLine F,
      process.survival * (Fintype.card F : ℝ) -
          (Fintype.card F : ℝ) ^ ((1 : ℝ) / 2 + ε) ≤
        retainedCount {linePoints l} (linePoints l) ω ∧
      retainedCount {linePoints l} (linePoints l) ω ≤
        process.survival * (Fintype.card F : ℝ) + (D : ℝ) +
          (Fintype.card F : ℝ) ^ ((1 : ℝ) / 2 + ε)

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_GoodTuples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {D : ℕ} {δ : ℝ}

def GoodTuples (process : DeletionProcess F D δ) (h t : ℕ)
    (ω : process.Config) : Prop :=
  ∀ a : LineTuple F t, AdmissibleTuple process.shapes D h a →
    δ * (t : ℝ) ^ 2 / 2 ≤ retainedCount (tupleShapes a) (crossPoints a) ω

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_HighSamples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [DecidableEq F]

abbrev PencilPopulation (L : Finset (AffineLine F)) (p : ProjectivePoint F) :=
  ↥(coverPencil L p)

abbrev ComplementPopulation (L : Finset (AffineLine F)) (p : ProjectivePoint F) :=
  ↥(L \ coverPencil L p)

abbrev HighSample (L : Finset (AffineLine F)) (p : ProjectivePoint F) (t : ℕ) :=
  (Fin t ↪ PencilPopulation L p) × (Fin t ↪ ComplementPopulation L p)

theorem pencilPopulation_incident (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    (k : PencilPopulation L p) : ProjectiveIncidence p (some k.val) :=
  (mem_coverPencil L p k.val).mp k.property |>.2

theorem complementPopulation_mem (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    (c : ComplementPopulation L p) : c.val ∈ L := let _ := instFintypeF;
  (Finset.mem_sdiff.mp c.property).1

theorem complementPopulation_not_incident (L : Finset (AffineLine F))
    (p : ProjectivePoint F) (c : ComplementPopulation L p) :
    ¬ ProjectiveIncidence p (some c.val) := by
  intro hc
  exact (Finset.mem_sdiff.mp c.property).2
    ((mem_coverPencil L p c.val).mpr ⟨complementPopulation_mem L p c, hc⟩)

theorem pencil_ne_complement (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    (k : PencilPopulation L p) (c : ComplementPopulation L p) : k.val ≠ c.val := by
  intro h
  apply complementPopulation_not_incident L p c
  rw [← h]
  exact pencilPopulation_incident L p k

def highTuple (L : Finset (AffineLine F)) (p : ProjectivePoint F) {t : ℕ}
    (s : HighSample L p t) : LineTuple F t where
  toFun := Sum.elim (fun i => (s.1 i).val) (fun j => (s.2 j).val)
  inj' := by
    intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl j => exact congrArg Sum.inl (s.1.injective (Subtype.ext hab))
      | inr j => exact (pencil_ne_complement L p (s.1 i) (s.2 j) hab).elim
    | inr i =>
      cases b with
      | inl j => exact (pencil_ne_complement L p (s.1 j) (s.2 i) hab.symm).elim
      | inr j => exact congrArg Sum.inr (s.2.injective (Subtype.ext hab))

@[simp] theorem highTuple_left (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    {t : ℕ} (s : HighSample L p t) (i : Fin t) :
    highTuple L p s (Sum.inl i) = (s.1 i).val := rfl

@[simp] theorem highTuple_right (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    {t : ℕ} (s : HighSample L p t) (i : Fin t) :
    highTuple L p s (Sum.inr i) = (s.2 i).val := rfl

def highCrossPairs (X : Finset (Point F)) (L : Finset (AffineLine F))
    (p : ProjectivePoint F) : Finset (PencilPopulation L p × ComplementPopulation L p) :=
  Finset.univ.filter fun kc =>
    ∃ x ∈ X, Incidence x kc.1.val ∧ Incidence x kc.2.val

@[simp] theorem mem_highCrossPairs (X : Finset (Point F)) (L : Finset (AffineLine F))
    (p : ProjectivePoint F) (kc : PencilPopulation L p × ComplementPopulation L p) :
    kc ∈ highCrossPairs X L p ↔
      ∃ x ∈ X, Incidence x kc.1.val ∧ Incidence x kc.2.val := let _ := instFintypeF; by
  simp only [highCrossPairs, Finset.mem_filter, Finset.mem_univ, true_and]

def highShapePairs (S : Finset (Point F)) (L : Finset (AffineLine F))
    (p : ProjectivePoint F) : Finset (PencilPopulation L p × ComplementPopulation L p) :=
  (highCrossPairs S L p).filter fun kc =>
    S ≠ linePoints kc.1.val ∧ S ≠ linePoints kc.2.val

@[simp] theorem mem_highShapePairs (S : Finset (Point F)) (L : Finset (AffineLine F))
    (p : ProjectivePoint F) (kc : PencilPopulation L p × ComplementPopulation L p) :
    kc ∈ highShapePairs S L p ↔
      (∃ x ∈ S, Incidence x kc.1.val ∧ Incidence x kc.2.val) ∧
      S ≠ linePoints kc.1.val ∧ S ≠ linePoints kc.2.val := by
  simp only [highShapePairs, Finset.mem_filter, mem_highCrossPairs]

def highSurvivorPairCount (X : Finset (Point F)) (L : Finset (AffineLine F))
    (p : ProjectivePoint F) {t : ℕ} (s : HighSample L p t) : ℕ :=
  (Finset.univ.filter fun ij : Fin t × Fin t =>
    (s.1 ij.1, s.2 ij.2) ∈ highCrossPairs X L p).card

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_HighDegeneracy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [DecidableEq F]

def highParallelLines (L : Finset (AffineLine F)) (p : ProjectivePoint F) {t : ℕ}
    (b : Fin t ↪ ComplementPopulation L p) : Finset (PencilPopulation L p) :=
  Finset.univ.biUnion fun j => Finset.univ.filter fun k => k.val.1 = (b j).val.1

def highCollisionLines (L : Finset (AffineLine F)) (p : ProjectivePoint F) {t : ℕ}
    (b : Fin t ↪ ComplementPopulation L p) : Finset (PencilPopulation L p) :=
  Finset.univ.biUnion fun ij : Fin t × Fin t => Finset.univ.filter fun k =>
    ij.1 ≠ ij.2 ∧ ∃ x : ProjectivePoint F,
      ProjectiveIncidence x (some k.val) ∧
      ProjectiveIncidence x (some (b ij.1).val) ∧
      ProjectiveIncidence x (some (b ij.2).val)

def highBadLines (L : Finset (AffineLine F)) (p : ProjectivePoint F) {t : ℕ}
    (b : Fin t ↪ ComplementPopulation L p) : Finset (PencilPopulation L p) :=
  highParallelLines L p b ∪ highCollisionLines L p b

@[simp] theorem mem_highParallelLines (L : Finset (AffineLine F))
    (p : ProjectivePoint F) {t : ℕ} (b : Fin t ↪ ComplementPopulation L p)
    (k : PencilPopulation L p) :
    k ∈ highParallelLines L p b ↔ ∃ j, k.val.1 = (b j).val.1 := let _ := instFintypeF; by
  simp only [highParallelLines, Finset.mem_biUnion, Finset.mem_univ,
    Finset.mem_filter, true_and]

@[simp] theorem mem_highCollisionLines (L : Finset (AffineLine F))
    (p : ProjectivePoint F) {t : ℕ} (b : Fin t ↪ ComplementPopulation L p)
    (k : PencilPopulation L p) :
    k ∈ highCollisionLines L p b ↔ ∃ i j, i ≠ j ∧
      ∃ x : ProjectivePoint F, ProjectiveIncidence x (some k.val) ∧
        ProjectiveIncidence x (some (b i).val) ∧
        ProjectiveIncidence x (some (b j).val) := by
  simp only [highCollisionLines, Finset.mem_biUnion, Finset.mem_univ,
    Finset.mem_filter, true_and, Prod.exists]

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

noncomputable def law (I : Type u) (Ω : Type v) [Fintype I] [Fintype Ω]
    (hle : Nat.card I ≤ Nat.card Ω) : FiniteLaw (I ↪ Ω) := by
  letI : Nonempty (I ↪ Ω) := sample_nonempty I Ω hle
  exact FiniteLaw.uniform (I ↪ Ω)

end RyserCoveringCounterexample.InjectionSampling

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_HighProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def highUniformLaw (L : Finset (AffineLine F)) (p : ProjectivePoint F) (t : ℕ)
    [Nonempty (Fin t ↪ PencilPopulation L p)]
    [Nonempty (Fin t ↪ ComplementPopulation L p)] : FiniteLaw (HighSample L p t) :=
  (FiniteLaw.uniform (Fin t ↪ PencilPopulation L p)).prod
    (FiniteLaw.uniform (Fin t ↪ ComplementPopulation L p))

def highFailureBound (X : Finset (Point F)) (L : Finset (AffineLine F))
    (p : ProjectivePoint F) (shapes : Finset (Finset (Point F)))
    (D h t : ℕ) (δ : ℝ) : ℝ :=
  let R := (coverPencil L p).card
  let N := (L \ coverPencil L p).card
  2 * (overlapExcess Incidence X L : ℝ) / (δ * R * N) +
    ((t : ℝ) ^ 2 + (t : ℝ) ^ 3) / R +
    (shapes.card : ℝ) * (t.descFactorial h : ℝ) ^ 2 * ((D * N : ℕ) : ℝ) ^ h /
      ((R.descFactorial h : ℝ) * (N.descFactorial h : ℝ))

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_LowDegeneracy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover.LowDegeneracy

open InjectionSampling

variable {F : Type*} [instFieldF : Field F] [instDecidableEqF : DecidableEq F]

def SameDirection {L : Finset (AffineLine F)} (u : Fin 2 ↪ ↥L) : Prop :=
  (u 0).val.1 = (u 1).val.1

def Concurrent {L : Finset (AffineLine F)} (u : Fin 3 ↪ ↥L) : Prop :=
  ∃ p : ProjectivePoint F, ∀ i, ProjectiveIncidence p (some (u i).val)

def firstPair {L : Finset (AffineLine F)} (u : Fin 3 ↪ ↥L) : Fin 2 ↪ ↥L :=
  (Fin.castLEEmb (by decide : 2 ≤ 3)).trans u

@[simp] theorem firstPair_zero {L : Finset (AffineLine F)} (u : Fin 3 ↪ ↥L) :
    firstPair u 0 = u 0 := let _ := instFieldF; let _ := instDecidableEqF; rfl

@[simp] theorem firstPair_one {L : Finset (AffineLine F)} (u : Fin 3 ↪ ↥L) :
    firstPair u 1 = u 1 := let _ := instFieldF; let _ := instDecidableEqF; rfl

theorem pair_lines_ne {L : Finset (AffineLine F)} (u : Fin 2 ↪ ↥L) :
    (u 0).val ≠ (u 1).val := let _ := instFieldF; let _ := instDecidableEqF; by
  intro h
  have h01 : (0 : Fin 2) = 1 := u.injective (Subtype.ext h)
  exact (by decide : (0 : Fin 2) ≠ 1) h01

def pairMeet {L : Finset (AffineLine F)} (u : Fin 2 ↪ ↥L) : ProjectivePoint F :=
  Classical.choose (existsUnique_projective_incident_of_ne_lines (pair_lines_ne u))

def AnyParallel {I : Type*} {L : Finset (AffineLine F)} (u : I ↪ ↥L) : Prop :=
  ∃ j : Fin 2 ↪ I, SameDirection (restrict j u)

def AnyConcurrent {I : Type*} {L : Finset (AffineLine F)} (u : I ↪ ↥L) : Prop :=
  ∃ j : Fin 3 ↪ I, Concurrent (restrict j u)

end RyserCoveringCounterexample.LineCover.LowDegeneracy

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_SamplingDefinitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [instFieldF : Field F] [instFintypeF : Fintype F] [instDecidableEqF : DecidableEq F]

abbrev CoverSample (L : Finset (AffineLine F)) (t : ℕ) :=
  (Fin t ⊕ Fin t) ↪ ↥L

def liftSample (L : Finset (AffineLine F)) {t : ℕ} (u : CoverSample L t) :
    LineTuple F t :=
  u.trans ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem liftSample_apply (L : Finset (AffineLine F)) {t : ℕ}
    (u : CoverSample L t) (i : Fin t ⊕ Fin t) :
    liftSample L u i = (u i).val := let _ := instFieldF; let _ := instFintypeF; let _ := instDecidableEqF; rfl

def CrossHit (X : Finset (Point F)) {t : ℕ} (a : LineTuple F t)
    (p : Fin t × Fin t) : Prop :=
  ∃ x ∈ X, Incidence x (a (Sum.inl p.1)) ∧ Incidence x (a (Sum.inr p.2))

def crossHitCount (X : Finset (Point F)) {t : ℕ} (a : LineTuple F t) : ℕ :=
  (Finset.univ.filter (CrossHit X a)).card

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_LowOccupancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def shapePairs (L : Finset (AffineLine F)) (S : Finset (Point F)) :
    Finset (↥L × ↥L) :=
  Finset.univ.filter fun p =>
    p.1 ≠ p.2 ∧ S ≠ linePoints p.1.val ∧ S ≠ linePoints p.2.val ∧
      ∃ x ∈ S, Incidence x p.1.val ∧ Incidence x p.2.val

@[simp] theorem mem_shapePairs (L : Finset (AffineLine F))
    (S : Finset (Point F)) (p : ↥L × ↥L) :
    p ∈ shapePairs L S ↔
      p.1 ≠ p.2 ∧ S ≠ linePoints p.1.val ∧ S ≠ linePoints p.2.val ∧
        ∃ x ∈ S, Incidence x p.1.val ∧ Incidence x p.2.val := by
  simp only [shapePairs, Finset.mem_filter, Finset.mem_univ, true_and]

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_PairCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F]

def survivorPairs (X : Finset (Point F)) (L : Finset (AffineLine F)) :
    Finset (AffineLine F × AffineLine F) :=
  X.biUnion fun x => (L.filter (Incidence x)).offDiag

def populationSurvivorPairs (X : Finset (Point F)) (L : Finset (AffineLine F)) :
    Finset (↥L × ↥L) :=
  Finset.univ.filter fun p => (p.1.val, p.2.val) ∈ survivorPairs X L

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_TupleGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [instDecidableEqF : DecidableEq F] {t : ℕ}

def NoParallel (a : LineTuple F t) : Prop :=
  ∀ i j, i ≠ j → (a i).1 ≠ (a j).1

def NoConcurrentTriple (a : LineTuple F t) : Prop :=
  ∀ p : ProjectivePoint F, ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    ProjectiveIncidence p (some (a i)) →
    ProjectiveIncidence p (some (a j)) →
    ProjectiveIncidence p (some (a k)) → False

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_LowConcurrency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [DecidableEq F]

def lowFailureBound (X : Finset (Point F)) (L : Finset (AffineLine F))
    (shapes : Finset (Finset (Point F))) (D R h t : ℕ) (δ : ℝ) : ℝ :=
  2 * (orderedPairMass Incidence X L : ℝ) /
      (δ * (L.card.descFactorial 2 : ℝ)) +
    ((2 * t).descFactorial 2 : ℝ) * R / ((L.card - 1 : ℕ) : ℝ) +
    ((2 * t).descFactorial 3 : ℝ) * R / ((L.card - 2 : ℕ) : ℝ) +
    (shapes.card : ℝ) * (t : ℝ) ^ (2 * h) * ((L.card * D * R : ℕ) : ℝ) ^ h /
      (L.card.descFactorial (2 * h) : ℝ)

def LowBad (X : Finset (Point F)) (L : Finset (AffineLine F))
    (shapes : Finset (Finset (Point F))) (D h t : ℕ) (δ : ℝ)
    (u : CoverSample L t) : Prop :=
  δ * (t : ℝ) ^ 2 / 2 ≤ ((X ∩ crossPoints (liftSample L u)).card : ℝ) ∨
    LowDegeneracy.AnyParallel u ∨ LowDegeneracy.AnyConcurrent u ∨
    ∃ S ∈ shapes, S ∉ tupleShapes (liftSample L u) ∧
      2 * D * h < (S ∩ crossPoints (liftSample L u)).card

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_ProjectiveLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [instFieldF : Field F] [instFintypeF : Fintype F] [DecidableEq F]

def projectivePointsOf (X : Finset (Point F)) : Finset (ProjectivePoint F) :=
  X.image Sum.inl

def projectiveLinesOf (L : Finset (AffineLine F)) : Finset (ProjectiveLine F) :=
  L.image some

@[simp] theorem card_projectivePointsOf (X : Finset (Point F)) :
    (projectivePointsOf X).card = X.card := let _ := instFieldF; let _ := instFintypeF;
  Finset.card_image_of_injective X Sum.inl_injective

@[simp] theorem card_projectiveLinesOf (L : Finset (AffineLine F)) :
    (projectiveLinesOf L).card = L.card := let _ := instFieldF; let _ := instFintypeF;
  Finset.card_image_of_injective L (Option.some_injective _)

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_MaxConcurrency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem exists_max_coverPencil (L : Finset (AffineLine F)) :
    ∃ p : ProjectivePoint F, ∀ r : ProjectivePoint F,
      (coverPencil L r).card ≤ (coverPencil L p).card := by
  obtain ⟨p, _, hp⟩ := Finset.exists_max_image
    (Finset.univ : Finset (ProjectivePoint F))
    (fun p => (coverPencil L p).card)
    ⟨Sum.inr none, Finset.mem_univ _⟩
  exact ⟨p, fun r => hp r (Finset.mem_univ r)⟩

def maxCenter (L : Finset (AffineLine F)) : ProjectivePoint F :=
  Classical.choose (exists_max_coverPencil L)

def maxConcurrency (L : Finset (AffineLine F)) : ℕ :=
  (coverPencil L (maxCenter L)).card

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology
open scoped Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

universe u

def linecoverFailureBound (D : ℕ) (δ A q : ℝ) : ℝ :=
  2 * (1 + q * (q + 1)) *
      Real.exp (-q ^ (2 * (Incidence.savingExponent / 10)) / (16 * (D : ℝ) ^ 5)) +
    2 * (q * (q + 1)) ^ (2 * logarithmicSampleSize A q) *
      Real.exp (-tupleTailConstant D (10 * (D + 1)) δ *
        (logarithmicSampleSize A q : ℝ) ^ 2)

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_Definitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [instDecidableEqF : DecidableEq F] {n K : ℕ}

section Finite
variable [Fintype F]

def Bounded (D : ℕ) (data : Data F n) : Prop :=
  n ≤ D * Fintype.card F ∧
    (∀ i, (data.W i).card ≤ D) ∧
    (∀ i, (data.dirs i).card ≤ D) ∧
    ∀ d, (Finset.univ.filter fun i => d ∈ data.dirs i).card ≤ D

noncomputable def feasibleMass (data : Data F n) (I : Finset (Fin n))
    (T : Finset (Position n K)) (pool : Pool F n K) : ℕ :=
  ∑ i ∈ I, (feasibleSet data T pool i).card

def exposedCount (T : Finset (Position n K)) (i : Fin n) : ℕ :=
  (T.filter fun e => e.1 = i).card

end Finite
end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_Chunk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section

namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [DecidableEq F] {n : ℕ}

def equationLoss (U : Finset (Point F)) (d : Direction F) (c : F)
    (x : Point F) : ℝ := (sliceCount U d (projection d x + c) : ℝ)

def lossByDirections (data : Data F n) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (j : Fin n)
    (dirs : Fin n → Finset (Direction F)) (x : Point F) : ℝ :=
  ∑ i ∈ I, ∑ d ∈ dirs i, ∑ u ∈ data.W i, ∑ v ∈ data.W j,
    equationLoss (U i) d (projection d (v - u)) x

def targetLoss (data : Data F n) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (j : Fin n) : Point F → ℝ :=
  lossByDirections data I U j data.dirs

def sourceLoss (data : Data F n) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (j : Fin n) : Point F → ℝ :=
  lossByDirections data I U j (fun _ => data.dirs j)

def entryLoss (data : Data F n) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (j : Fin n) (x : Point F) : ℝ :=
  targetLoss data I U j x + sourceLoss data I U j x

def frozenMass (I : Finset (Fin n)) (U : Fin n → Finset (Point F)) : ℝ :=
  ∑ i ∈ I, (U i).card

def sourceEnergy (data : Data F n) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (j : Fin n) : ℝ :=
  ∑ i ∈ I, ∑ d ∈ data.dirs j, sliceEnergy (U i) d

def targetDirectionGroup (data : Data F n) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (j : Fin n) (d : Direction F) (t : F) : ℝ :=
  ∑ i ∈ I.filter (fun i => d ∈ data.dirs i), ∑ u ∈ data.W i, ∑ v ∈ data.W j,
    (sliceCount (U i) d (t + projection d (v - u)) : ℝ)

end RyserCoveringCounterexample.Selection

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_ChunkLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Selection

section Configurations

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [DecidableEq F] {n K : ℕ}

noncomputable def conflictingPoints (data : Data F n) (U : Finset (Point F))
    (i j : Fin n) (x : Point F) : Finset (Point F) := by
  classical
  exact U.filter fun b => Conflict data i j b x

@[simp] theorem mem_conflictingPoints (data : Data F n) (U : Finset (Point F))
    (i j : Fin n) (x b : Point F) :
    b ∈ conflictingPoints data U i j x ↔ b ∈ U ∧ Conflict data i j b x := let _ := instFintypeF; by
  classical
  simp only [conflictingPoints, Finset.mem_filter]

end Configurations

end RyserCoveringCounterexample.Selection

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

def RegularEntry (data : Data F n) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (j : Fin n) : Prop :=
  sourceEnergy data I U j ≤ (I.card : ℝ) * Fintype.card F *
    Real.sqrt (Fintype.card F)

noncomputable def regularEntries (data : Data F n) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (E : Finset (Position n K)) :
    Finset (Position n K) := by
  classical
  exact E.filter (fun e => RegularEntry data I U e.1)

end RyserCoveringCounterexample.Selection

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_PoolLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Selection

variable (F : Type*) [instFieldF : Field F] [instFintypeF : Fintype F] [instDecidableEqF : DecidableEq F] (n K : ℕ)

noncomputable def poolLaw : FiniteLaw (Pool F n K) :=
  FiniteLaw.pi (fun _ : Position n K => FiniteLaw.uniform (Point F))

variable {F n K}

def frozenPool (T : Finset (Position n K)) (x : ExposedAssignment (F := F) T) :
    Pool F n K := joinAssignments T x (fun _ => 0)

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_FeasibleDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n K : ℕ}

noncomputable def feasibleDensity (data : Data F n) (T : Finset (Position n K))
    (pool : Pool F n K) (i : Fin n) : ℝ :=
  (FiniteLaw.uniform (Point F)).prob (Feasible data T pool i)

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_Forbidden
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [DecidableEq F] {n K : ℕ}

abbrev EquationIndex (data : Data F n) (i j : Fin n) :=
  ↥(data.W i) × ↥(data.W j) × ↥(data.dirs i ∪ data.dirs j)

def equationEvent (data : Data F n) (i j : Fin n) (b' : Point F)
    (e : EquationIndex data i j) (b : Point F) : Prop :=
  projection e.2.2.val b = projection e.2.2.val b' +
    projection e.2.2.val (e.2.1.val - e.1.val)

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_SmallCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n K : ℕ}

def NoFeasibleOutside (data : Data F n) (I : Finset (Fin n))
    (T : Finset (Position n K)) (pool : Pool F n K) : Prop :=
  ∀ e : Position n K, e.1 ∈ I → e ∉ T → ¬Feasible data T pool e.1 (pool e)

def freshTargets (I : Finset (Fin n)) (T : Finset (Position n K)) :
    Finset {e : Position n K // e ∉ T} :=
  Finset.univ.filter fun e => e.val.1 ∈ I

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_PoolCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
namespace RyserCoveringCounterexample.Selection

variable {n K : ℕ}

def targetPositions (I : Finset (Fin n)) (K : ℕ) : Finset (Position n K) :=
  I.product Finset.univ

@[simp] theorem mem_targetPositions {I : Finset (Fin n)} {e : Position n K} :
    e ∈ targetPositions I K ↔ e.1 ∈ I := by
  simp only [targetPositions, Finset.product_eq_sprod, Finset.mem_product,
    Finset.mem_univ, and_true]

@[simp] theorem card_targetPositions (I : Finset (Fin n)) (K : ℕ) :
    (targetPositions I K).card = I.card * K := by
  simp only [targetPositions, Finset.product_eq_sprod, Finset.card_product,
    Finset.card_univ, Fintype.card_fin]

end RyserCoveringCounterexample.Selection

end OAI
end


