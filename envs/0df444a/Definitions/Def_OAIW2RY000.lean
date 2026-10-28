-- Prove2me | Definitions.Def_OAIW2RY000
-- name    : OAIW2RY000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T04:25:51.49937+00:00
-- url     : https://prove2.me/theorems/b5b131b8-13c8-4e6c-b5fd-cb2c5aa303ea
-- title:
--   Definitions bundle OAIW2RY000 of the split of OpenAI, A counterexample to Ryser's covering conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.RyserCoveringCounterexample.exists_prime_eventually_counterexampleRank`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Ryser's covering conjecture*, OpenAI Math Release, September 23, 2026, result family 162, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 498 declarations of OpenAI's Lean: 208 definitions, 9 inductive types or structures, 3 instances and 278 theorems. The definitions and types are `OAI.RyserCoveringCounterexample.AffineLine`, `OAI.RyserCoveringCounterexample.Construction.ActiveExceptional`, `OAI.RyserCoveringCounterexample.Construction.AmbientPool`, `OAI.RyserCoveringCounterexample.Construction.AmbientPosition`, `OAI.RyserCoveringCounterexample.Construction.ConfigurationData`, `OAI.RyserCoveringCounterexample.Construction.ConfigurationGroup`, `OAI.RyserCoveringCounterexample.Construction.CosetIndex`, `OAI.RyserCoveringCounterexample.Construction.DeletionSeparated`, `OAI.RyserCoveringCounterexample.Construction.GadgetCoverProperty`, `OAI.RyserCoveringCounterexample.Construction.GadgetOutcome`, `OAI.RyserCoveringCounterexample.Construction.GoodAmbientPool`, `OAI.RyserCoveringCounterexample.Construction.GoodGadget`, `OAI.RyserCoveringCounterexample.Construction.LineCapable`, `OAI.RyserCoveringCounterexample.Construction.NonzeroSlope`, `OAI.RyserCoveringCounterexample.Construction.OffPencilThin`, `OAI.RyserCoveringCounterexample.Construction.OriginalLineDensity`, `OAI.RyserCoveringCounterexample.Construction.PlaneLinearMap`, `OAI.RyserCoveringCounterexample.Construction.PlaneLinearMap.apply`, `OAI.RyserCoveringCounterexample.Construction.PlaneLinearMap.determinant`, `OAI.RyserCoveringCounterexample.Construction.PlaneLinearMap.diagonal`, `OAI.RyserCoveringCounterexample.Construction.PlaneLinearMap.directionMap`, `OAI.RyserCoveringCounterexample.Construction.PlaneLinearMap.extra`, `OAI.RyserCoveringCounterexample.Construction.PlaneLinearMap.inverse`, `OAI.RyserCoveringCounterexample.Construction.PlaneLinearMap.projectionScale`, `OAI.RyserCoveringCounterexample.Construction.PlaneLinearMap.toEquiv`, `OAI.RyserCoveringCounterexample.Construction.PoolThin`, `OAI.RyserCoveringCounterexample.Construction.ShiftHits`, `OAI.RyserCoveringCounterexample.Construction.Vertex`, `OAI.RyserCoveringCounterexample.Construction.activeDeletionGroupEquivDeletedPencil`, `OAI.RyserCoveringCounterexample.Construction.activeDeletionGroups`, `OAI.RyserCoveringCounterexample.Construction.activeDeletionLine`, `OAI.RyserCoveringCounterexample.Construction.activeDeletionLineInPencil`, `OAI.RyserCoveringCounterexample.Construction.allDeletedLines`, `OAI.RyserCoveringCounterexample.Construction.alteredDirections`, `OAI.RyserCoveringCounterexample.Construction.alteredInverseSlope`, `OAI.RyserCoveringCounterexample.Construction.ambientDeletionConstant`, `OAI.RyserCoveringCounterexample.Construction.ambientDeletionDelta`, `OAI.RyserCoveringCounterexample.Construction.ambientDeletionProcess`, `OAI.RyserCoveringCounterexample.Construction.ambientFlatPoolEquiv`, `OAI.RyserCoveringCounterexample.Construction.ambientLineOutcome` and 177 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Ryser_Construction_AmbientDeletionGeometry`, `Ryser_Construction_AmbientDeletionNumerics`, `Ryser_Construction_AmbientDeletionPoolLaw`, `Ryser_Construction_AmbientDeletionProcess`, `Ryser_Construction_AmbientDeletionShapes`, `Ryser_Construction_AmbientDeletionSurvivors`, `Ryser_Construction_AmbientDeletionTrials`, `Ryser_Construction_AmbientPoolExistence`, `Ryser_Construction_CoordinateCompatibility`, `Ryser_Construction_CosetDirections`, `Ryser_Construction_CosetIndex`, `Ryser_Construction_CoverPencil`, `Ryser_Construction_DeletionIntersection`, `Ryser_Construction_DeletionLines`, `Ryser_Construction_DeletionUnionBasic`, `Ryser_Construction_DeletionUnionOutside`, `Ryser_Construction_DeterministicCover`, `Ryser_Construction_DirectionPlacement`, `Ryser_Construction_DirectionSets`, `Ryser_Construction_ExceptionalCover`, `Ryser_Construction_ExtraDirections`, `Ryser_Construction_FiniteOutsideAction`, `Ryser_Construction_FiniteSelectionCounting`, `Ryser_Construction_GadgetAlgebra`, `Ryser_Construction_GadgetConcentration`, `Ryser_Construction_GadgetConsequences`, `Ryser_Construction_GadgetDefinitions`, `Ryser_Construction_GadgetGood`, `Ryser_Construction_GadgetOriginalCounts`, `Ryser_Construction_GadgetProcess`, `Ryser_Construction_GadgetShapes`, `Ryser_Construction_GroupBounds`, `Ryser_Construction_GroupPlacement`, `Ryser_Construction_GroupSelection`, `Ryser_Construction_Hypergraph`, `Ryser_Construction_LinearPlacement`, `Ryser_Construction_OrdinaryCover`, `Ryser_Construction_PlacedLines`, `Ryser_Construction_PlacementIntersection`, `Ryser_Construction_PoolThinAsymptotic`, `Ryser_Construction_PoolThinGeometry`, `Ryser_Construction_PoolThinProbability`, `Ryser_Construction_SelectedHypergraph`, `Ryser_Domination_Basic`, `Ryser_Domination_TraceDefinitions`, `Ryser_Field_Extension`, `Ryser_Geometry_AffineJoins`, `Ryser_Geometry_Basic`, `Ryser_Geometry_Cardinality`, `Ryser_Geometry_ProjectionPair`, `Ryser_Geometry_ProjectiveTransformBasic`, `Ryser_Incidence_CoordinateTransferSet`, `Ryser_Incidence_FiniteSetEstimates`, `Ryser_Incidence_FourAnchorsCounting`, `Ryser_Incidence_Parameters`, `Ryser_Incidence_Pencils`, `Ryser_Incidence_PruningCore`, `Ryser_Incidence_PruningNumerics`, `Ryser_Incidence_RatioSet`, `Ryser_Incidence_ScalarCover`, `Ryser_Incidence_ScalarCoverExpressions`, `Ryser_Incidence_Uniform`, `Ryser_Incidence_WalkCounts`, `Ryser_Incidence_WalkExpansion`, `Ryser_Incidence_WalkQuotients`, `Ryser_LineCover_Definitions`, `Ryser_LineCover_DeletionDefinitions`, `Ryser_LineCover_Process`, `Ryser_LineCover_SurvivalNumerics`, `Ryser_Probability_Exposure`, `Ryser_Probability_Finite`, `Ryser_Probability_Product`, `Ryser_Probability_Variance`, `Ryser_Selection_ChunkLoss`, `Ryser_Selection_Definitions`, `Ryser_Selection_Forbidden`, `Ryser_Selection_PoolGraph`, `Ryser_Selection_PoolLaw`.
--
--   **Imports.** It imports the published bundle `Def_RyserCovering`.
--
--   **Imported by** (directly, in this split): the bundle `OAIW2RY002`; the statements `OAI.RyserCoveringCounterexample.Construction.exists_goodAmbientPool_uniform`, `OAI.RyserCoveringCounterexample.Construction.exists_prime_goodGadget` and `OAI.RyserCoveringCounterexample.Incidence.uniform_incidence_bound`.
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
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Geometry_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample

abbrev Point (F : Type*) := F × F
abbrev Direction (F : Type*) := Option F
abbrev AffineLine (F : Type*) := Direction F × F
abbrev ProjectivePoint (F : Type*) := Point F ⊕ Direction F
abbrev ProjectiveLine (F : Type*) := Option (AffineLine F)

variable {F : Type*} [Field F]

def projection : Direction F → Point F → F
  | none, p => p.1
  | some a, p => p.2 - a * p.1

def Incidence (p : Point F) (l : AffineLine F) : Prop :=
  projection l.1 p = l.2

instance instDecidableIncidenceOfDecidableEq [DecidableEq F] (p : Point F) (l : AffineLine F) :
    Decidable (Incidence p l) :=
  inferInstanceAs (Decidable (projection l.1 p = l.2))

def lineThrough (d : Direction F) (p : Point F) : AffineLine F :=
  (d, projection d p)

@[simp] theorem projection_none (p : Point F) : projection none p = p.1 := rfl
@[simp] theorem projection_some (a : F) (p : Point F) :
    projection (some a) p = p.2 - a * p.1 := rfl
@[simp] theorem projection_some_zero (p : Point F) :
    projection (some 0) p = p.2 := by simp [projection]

@[simp] theorem incidence_mk (p : Point F) (d : Direction F) (b : F) :
    Incidence p (d, b) ↔ projection d p = b := Iff.rfl

@[simp] theorem lineThrough_direction (d : Direction F) (p : Point F) :
    (lineThrough d p).1 = d := rfl
@[simp] theorem lineThrough_offset (d : Direction F) (p : Point F) :
    (lineThrough d p).2 = projection d p := rfl
@[simp] theorem incidence_lineThrough (d : Direction F) (p : Point F) :
    Incidence p (lineThrough d p) := rfl

@[simp] theorem incidence_lineThrough_iff (d : Direction F) (p q : Point F) :
    Incidence p (lineThrough d q) ↔ projection d p = projection d q := Iff.rfl

theorem eq_lineThrough_of_incidence {p : Point F} {l : AffineLine F}
    (h : Incidence p l) : l = lineThrough l.1 p := by
  apply Prod.ext
  · rfl
  · exact h.symm

theorem projection_add (d : Direction F) (p q : Point F) :
    projection d (p.1 + q.1, p.2 + q.2) = projection d p + projection d q := by
  cases d with
  | none => rfl
  | some slope => simp only [projection]; ring

theorem projection_sub (d : Direction F) (p q : Point F) :
    projection d (p.1 - q.1, p.2 - q.2) = projection d p - projection d q := by
  cases d with
  | none => rfl
  | some slope => simp only [projection]; ring

def ProjectiveIncidence : ProjectivePoint F → ProjectiveLine F → Prop
  | Sum.inl p, some l => Incidence p l
  | Sum.inr d, some l => d = l.1
  | Sum.inl _, none => False
  | Sum.inr _, none => True

instance instDecidableProjectiveIncidenceOfDecidableEq [DecidableEq F] (p : ProjectivePoint F) (l : ProjectiveLine F) :
    Decidable (ProjectiveIncidence p l) := by
  cases p <;> cases l <;> simp only [ProjectiveIncidence] <;> infer_instance

@[simp] theorem projectiveIncidence_finite_affine (p : Point F) (l : AffineLine F) :
    ProjectiveIncidence (Sum.inl p) (some l) ↔ Incidence p l := Iff.rfl
@[simp] theorem projectiveIncidence_infinite_affine (d : Direction F) (l : AffineLine F) :
    ProjectiveIncidence (Sum.inr d) (some l) ↔ d = l.1 := Iff.rfl
@[simp] theorem projectiveIncidence_finite_infinity (p : Point F) :
    ¬ ProjectiveIncidence (Sum.inl p) (none : ProjectiveLine F) := not_false
@[simp] theorem projectiveIncidence_infinite_infinity (d : Direction F) :
    ProjectiveIncidence (Sum.inr d) (none : ProjectiveLine F) := trivial

section Finite
variable [Fintype F] [DecidableEq F]

def linePoints (l : AffineLine F) : Finset (Point F) :=
  Finset.univ.filter fun p => Incidence p l

def affinePencil (p : ProjectivePoint F) : Finset (AffineLine F) :=
  Finset.univ.filter fun l => ProjectiveIncidence p (some l)

@[simp] theorem mem_linePoints (p : Point F) (l : AffineLine F) :
    p ∈ linePoints l ↔ Incidence p l := by simp only [linePoints, Finset.mem_filter,
    Finset.mem_univ, true_and]

@[simp] theorem mem_affinePencil (p : ProjectivePoint F) (l : AffineLine F) :
    l ∈ affinePencil p ↔ ProjectiveIncidence p (some l) := by
  simp only [affinePencil, Finset.mem_filter, Finset.mem_univ, true_and]

end Finite
end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_LinearPlacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F]

structure PlaneLinearMap (F : Type*) [Field F] where
  xx : F
  xy : F
  yx : F
  yy : F
  determinant_ne_zero : xx * yy - xy * yx ≠ 0

namespace PlaneLinearMap

def determinant (M : PlaneLinearMap F) : F := M.xx * M.yy - M.xy * M.yx

def apply (M : PlaneLinearMap F) (p : Point F) : Point F :=
  (M.xx * p.1 + M.xy * p.2, M.yx * p.1 + M.yy * p.2)

def inverse (M : PlaneLinearMap F) (p : Point F) : Point F :=
  ((M.yy * p.1 - M.xy * p.2) / M.determinant,
    (M.xx * p.2 - M.yx * p.1) / M.determinant)

@[simp] theorem inverse_apply (M : PlaneLinearMap F) (p : Point F) :
    M.inverse (M.apply p) = p := by
  have hd : M.determinant ≠ 0 := M.determinant_ne_zero
  apply Prod.ext <;> dsimp [inverse, apply]
  · field_simp [hd]
    simp only [determinant]
    ring
  · field_simp [hd]
    simp only [determinant]
    ring

@[simp] theorem apply_inverse (M : PlaneLinearMap F) (p : Point F) :
    M.apply (M.inverse p) = p := by
  have hd : M.determinant ≠ 0 := M.determinant_ne_zero
  apply Prod.ext <;> dsimp [inverse, apply]
  · field_simp [hd]
    simp only [determinant]
    ring
  · field_simp [hd]
    simp only [determinant]
    ring

def toEquiv (M : PlaneLinearMap F) : Point F ≃ Point F where
  toFun := M.apply
  invFun := M.inverse
  left_inv := M.inverse_apply
  right_inv := M.apply_inverse

@[simp] theorem apply_zero (M : PlaneLinearMap F) : M.apply (0, 0) = (0, 0) := by
  simp [apply]

def diagonal (a : F) (ha : a ≠ 0) : PlaneLinearMap F where
  xx := 1
  xy := 0
  yx := 0
  yy := a
  determinant_ne_zero := by simpa using ha

@[simp] theorem diagonal_apply (a : F) (ha : a ≠ 0) (p : Point F) :
    (diagonal a ha).apply p = (p.1, a * p.2) := by
  simp [diagonal, apply]

def extra (u v : F) (huv : u ≠ v) : PlaneLinearMap F where
  xx := 1
  xy := 1
  yx := u
  yy := v
  determinant_ne_zero := by
    simpa only [one_mul] using sub_ne_zero.mpr huv.symm

@[simp] theorem extra_apply (u v : F) (huv : u ≠ v) (p : Point F) :
    (extra u v huv).apply p = (p.1 + p.2, u * p.1 + v * p.2) := by
  simp [extra, apply]

end PlaneLinearMap

section Subfield

variable {k : Type*} [Field k]

def mapPoint (σ : k →+* F) (p : Point k) : Point F := (σ p.1, σ p.2)

def placedPoint (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (w : Point k) : Point F := b + M.apply (mapPoint σ w)

end Subfield

end RyserCoveringCounterexample.Construction

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Geometry_AffineJoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample

variable {F : Type*} [Field F]

theorem point_eq_of_projection_eq_of_ne_direction
    {d e : Direction F} {p q : Point F} (hde : d ≠ e)
    (hd : projection d p = projection d q)
    (he : projection e p = projection e q) : p = q := by
  rcases p with ⟨x, y⟩
  rcases q with ⟨z, w⟩
  cases d with
  | none =>
    cases e with
    | none => exact (hde rfl).elim
    | some b =>
      change x = z at hd
      change y - b * x = w - b * z at he
      apply Prod.ext hd
      calc
        y = (y - b * x) + b * x := by ring
        _ = (w - b * z) + b * z := by rw [he, hd]
        _ = w := by ring
  | some a =>
    cases e with
    | none =>
      change y - a * x = w - a * z at hd
      change x = z at he
      apply Prod.ext he
      calc
        y = (y - a * x) + a * x := by ring
        _ = (w - a * z) + a * z := by rw [hd, he]
        _ = w := by ring
    | some b =>
      have hab : a ≠ b := fun h => hde (congrArg Option.some h)
      change y - a * x = w - a * z at hd
      change y - b * x = w - b * z at he
      have hmul : (a - b) * x = (a - b) * z := by
        calc
          (a - b) * x = (y - b * x) - (y - a * x) := by ring
          _ = (w - b * z) - (w - a * z) := by rw [he, hd]
          _ = (a - b) * z := by ring
      have hx : x = z := mul_left_cancel₀ (sub_ne_zero.mpr hab) hmul
      apply Prod.ext hx
      calc
        y = (y - a * x) + a * x := by ring
        _ = (w - a * z) + a * z := by rw [hd, hx]
        _ = w := by ring

theorem line_eq_of_direction_eq_of_incidence
    {l m : AffineLine F} {p : Point F} (hdl : l.1 = m.1)
    (hpl : Incidence p l) (hpm : Incidence p m) : l = m := by
  change projection l.1 p = l.2 at hpl
  change projection m.1 p = m.2 at hpm
  apply Prod.ext hdl
  exact hpl.symm.trans ((congrArg (fun d => projection d p) hdl).trans hpm)

theorem line_eq_of_two_incident_points
    {p q : Point F} {l m : AffineLine F} (hpq : p ≠ q)
    (hpl : Incidence p l) (hql : Incidence q l)
    (hpm : Incidence p m) (hqm : Incidence q m) : l = m := by
  by_cases hdir : l.1 = m.1
  · exact line_eq_of_direction_eq_of_incidence hdir hpl hpm
  · change projection l.1 p = l.2 at hpl
    change projection l.1 q = l.2 at hql
    change projection m.1 p = m.2 at hpm
    change projection m.1 q = m.2 at hqm
    exact (hpq (point_eq_of_projection_eq_of_ne_direction hdir
      (hpl.trans hql.symm) (hpm.trans hqm.symm))).elim

theorem eq_of_common_incidence_of_ne_lines
    {l m : AffineLine F} {p q : Point F} (hlm : l ≠ m)
    (hpl : Incidence p l) (hpm : Incidence p m)
    (hql : Incidence q l) (hqm : Incidence q m) : p = q := by
  by_contra hpq
  exact hlm (line_eq_of_two_incident_points hpq hpl hql hpm hqm)

theorem existsUnique_incident_of_ne_direction (l m : AffineLine F)
    (hdir : l.1 ≠ m.1) :
    ∃! p : Point F, Incidence p l ∧ Incidence p m := by
  have hex : ∃ p : Point F, Incidence p l ∧ Incidence p m := by
    rcases l with ⟨d, b⟩
    rcases m with ⟨e, c⟩
    change d ≠ e at hdir
    cases d with
    | none =>
      cases e with
      | none => exact (hdir rfl).elim
      | some a =>
        refine ⟨(b, c + a * b), ?_⟩
        change b = b ∧ (c + a * b) - a * b = c
        exact ⟨rfl, by ring⟩
    | some a =>
      cases e with
      | none =>
        refine ⟨(c, b + a * c), ?_⟩
        change (b + a * c) - a * c = b ∧ c = c
        exact ⟨by ring, rfl⟩
      | some a' =>
        have haa : a ≠ a' := fun h => hdir (congrArg Option.some h)
        have hne : a - a' ≠ 0 := sub_ne_zero.mpr haa
        let x : F := (c - b) / (a - a')
        have hx : x * (a - a') = c - b := by
          change (c - b) / (a - a') * (a - a') = c - b
          exact div_mul_cancel₀ (c - b) hne
        refine ⟨(x, b + a * x), ?_⟩
        change (b + a * x) - a * x = b ∧ (b + a * x) - a' * x = c
        constructor
        · ring
        · calc
            (b + a * x) - a' * x = b + x * (a - a') := by ring
            _ = b + (c - b) := by rw [hx]
            _ = c := by ring
  obtain ⟨p, hp⟩ := hex
  refine ⟨p, hp, ?_⟩
  intro q hq
  change projection l.1 p = l.2 ∧ projection m.1 p = m.2 at hp
  change projection l.1 q = l.2 ∧ projection m.1 q = m.2 at hq
  exact point_eq_of_projection_eq_of_ne_direction hdir
    (hq.1.trans hp.1.symm) (hq.2.trans hp.2.symm)

section Join

variable [DecidableEq F]

def joinDirection (p q : Point F) : Direction F :=
  if p.1 = q.1 then none else some ((q.2 - p.2) / (q.1 - p.1))

def joinLine (p q : Point F) : AffineLine F :=
  lineThrough (joinDirection p q) p

@[simp] theorem incidence_joinLine_left (p q : Point F) :
    Incidence p (joinLine p q) := rfl

@[simp] theorem incidence_joinLine_right (p q : Point F) :
    Incidence q (joinLine p q) := by
  change projection (joinDirection p q) q = projection (joinDirection p q) p
  by_cases hx : p.1 = q.1
  · have hd : joinDirection p q = none := by
      unfold joinDirection
      exact ite_eq_left hx
    simpa only [hd, projection] using hx.symm
  · let a : F := (q.2 - p.2) / (q.1 - p.1)
    have hd : joinDirection p q = some a := by
      unfold joinDirection
      exact ite_eq_right hx
    have hden : q.1 - p.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    have hs : a * (q.1 - p.1) = q.2 - p.2 := by
      change (q.2 - p.2) / (q.1 - p.1) * (q.1 - p.1) = q.2 - p.2
      exact div_mul_cancel₀ (q.2 - p.2) hden
    simp only [hd, projection]
    calc
      q.2 - a * q.1 = p.2 - a * p.1 +
          ((q.2 - p.2) - a * (q.1 - p.1)) := by ring
      _ = p.2 - a * p.1 := by rw [hs]; ring

end Join

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_DirectionPlacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F] [instDecidableEqF : DecidableEq F]

def directionVector : Direction F → Point F
  | none => (0, 1)
  | some a => (1, a)

theorem directionVector_kernel_iff (d e : Direction F) :
    projection d (directionVector e) = 0 ↔ d = e := let _ := instDecidableEqF; by
  cases d <;> cases e <;> simp [directionVector, projection, sub_eq_zero, eq_comm]

namespace PlaneLinearMap

def directionMap (M : PlaneLinearMap F) : Direction F → Direction F
  | none => if M.xy = 0 then none else some (M.yy / M.xy)
  | some a => if M.xx + M.xy * a = 0 then none
      else some ((M.yx + M.yy * a) / (M.xx + M.xy * a))

def projectionScale (M : PlaneLinearMap F) : Direction F → F
  | none => if M.xy = 0 then M.xx else -M.determinant / M.xy
  | some a => if M.xx + M.xy * a = 0 then M.xy
      else M.determinant / (M.xx + M.xy * a)

theorem projectionScale_ne_zero (M : PlaneLinearMap F) (d : Direction F) :
    M.projectionScale d ≠ 0 := by
  cases d with
  | none =>
      by_cases hxy : M.xy = 0
      · simp only [projectionScale, ite_eq_left hxy]
        intro hxx
        exact M.determinant_ne_zero (by simp [hxy, hxx])
      · simp only [projectionScale, ite_eq_right hxy]
        exact div_ne_zero (neg_ne_zero.mpr M.determinant_ne_zero) hxy
  | some a =>
      by_cases hA : M.xx + M.xy * a = 0
      · simp only [projectionScale, ite_eq_left hA]
        intro hxy
        have hxx : M.xx = 0 := by simpa only [hxy, zero_mul, add_zero] using hA
        exact M.determinant_ne_zero (by simp [hxy, hxx])
      · simp only [projectionScale, ite_eq_right hA]
        exact div_ne_zero M.determinant_ne_zero hA

theorem projection_directionMap_apply (M : PlaneLinearMap F)
    (d : Direction F) (p : Point F) :
    projection (M.directionMap d) (M.apply p) =
      M.projectionScale d * projection d p := by
  cases d with
  | none =>
      by_cases hxy : M.xy = 0
      · simp [directionMap, projectionScale, hxy, projection, apply]
      · simp only [directionMap, projectionScale, ite_eq_right hxy, projection, apply]
        field_simp [hxy]
        simp only [determinant]
        ring
  | some a =>
      by_cases hA : M.xx + M.xy * a = 0
      · have hxx : M.xx = -(M.xy * a) := eq_neg_of_add_eq_zero_left hA
        simp only [directionMap, projectionScale, ite_eq_left hA, projection, apply]
        rw [hxx]
        ring
      · simp only [directionMap, projectionScale, ite_eq_right hA, projection, apply]
        apply mul_right_cancel₀ hA
        calc
          (M.yx * p.1 + M.yy * p.2 -
              (M.yx + M.yy * a) / (M.xx + M.xy * a) *
                (M.xx * p.1 + M.xy * p.2)) * (M.xx + M.xy * a) =
              (M.yx * p.1 + M.yy * p.2) * (M.xx + M.xy * a) -
                ((M.yx + M.yy * a) / (M.xx + M.xy * a) * (M.xx + M.xy * a)) *
                  (M.xx * p.1 + M.xy * p.2) := by ring
          _ = (M.yx * p.1 + M.yy * p.2) * (M.xx + M.xy * a) -
                (M.yx + M.yy * a) * (M.xx * p.1 + M.xy * p.2) := by
              rw [div_mul_cancel₀ _ hA]
          _ = M.determinant * (p.2 - a * p.1) := by
              simp only [determinant]
              ring
          _ = (M.determinant / (M.xx + M.xy * a) * (M.xx + M.xy * a)) *
                (p.2 - a * p.1) := by rw [div_mul_cancel₀ _ hA]
          _ = (M.determinant / (M.xx + M.xy * a) * (p.2 - a * p.1)) *
                (M.xx + M.xy * a) := by ring

theorem projection_directionMap_apply_eq_iff (M : PlaneLinearMap F)
    (d : Direction F) (p q : Point F) :
    projection (M.directionMap d) (M.apply p) =
      projection (M.directionMap d) (M.apply q) ↔
      projection d p = projection d q := by
  rw [M.projection_directionMap_apply, M.projection_directionMap_apply]
  exact ⟨mul_left_cancel₀ (M.projectionScale_ne_zero d),
    congrArg (fun x => M.projectionScale d * x)⟩

theorem directionMap_injective (M : PlaneLinearMap F) :
    Function.Injective M.directionMap := by
  intro d e hde
  have hd : projection d (directionVector d) = 0 :=
    (directionVector_kernel_iff d d).2 rfl
  have hz : projection (M.directionMap e) (M.apply (directionVector d)) = 0 := by
    rw [← hde, M.projection_directionMap_apply, hd, mul_zero]
  rw [M.projection_directionMap_apply] at hz
  have he : projection e (directionVector d) = 0 :=
    (mul_eq_zero.mp hz).resolve_left (M.projectionScale_ne_zero e)
  exact ((directionVector_kernel_iff e d).1 he).symm

theorem projection_directionMap_placed_eq_iff (M : PlaneLinearMap F)
    (b : Point F) (d : Direction F) (p q : Point F) :
    projection (M.directionMap d) (b + M.apply p) =
      projection (M.directionMap d) (b + M.apply q) ↔
      projection d p = projection d q := by
  change projection (M.directionMap d)
      (b.1 + (M.apply p).1, b.2 + (M.apply p).2) =
    projection (M.directionMap d)
      (b.1 + (M.apply q).1, b.2 + (M.apply q).2) ↔ _
  rw [projection_add, projection_add, add_left_cancel_iff]
  exact M.projection_directionMap_apply_eq_iff d p q

@[simp] theorem diagonal_directionMap_none (a : F) (ha : a ≠ 0) :
    (diagonal a ha).directionMap none = none := by
  simp [directionMap, diagonal]

@[simp] theorem diagonal_directionMap_some (a : F) (ha : a ≠ 0) (t : F) :
    (diagonal a ha).directionMap (some t) = some (a * t) := by
  simp [directionMap, diagonal]

@[simp] theorem extra_directionMap_none (u v : F) (huv : u ≠ v) :
    (extra u v huv).directionMap none = some v := by
  simp [directionMap, extra]

@[simp] theorem extra_directionMap_zero (u v : F) (huv : u ≠ v) :
    (extra u v huv).directionMap (some 0) = some u := by
  simp [directionMap, extra]

end PlaneLinearMap

section Subfield

variable {k : Type*} [Field k] [instDecidableEqk : DecidableEq k]

def mapDirection (σ : k →+* F) : Direction k → Direction F := Option.map σ

theorem mapDirection_injective (σ : k →+* F) : Function.Injective (mapDirection σ) := let _ := instDecidableEqF; let _ := instDecidableEqk; by
  intro d e hde
  cases d with
  | none =>
      cases e with
      | none => rfl
      | some b => cases hde
  | some a =>
      cases e with
      | none => cases hde
      | some b => exact congrArg Option.some (σ.injective (Option.some.inj hde))

theorem projection_mapDirection_mapPoint (σ : k →+* F) (d : Direction k)
    (p : Point k) :
    projection (mapDirection σ d) (mapPoint σ p) = σ (projection d p) := let _ := instDecidableEqF; let _ := instDecidableEqk; by
  cases d <;> simp [mapDirection, mapPoint, projection, map_sub, map_mul]

def placedDirection (σ : k →+* F) (M : PlaneLinearMap F) :
    Direction k → Direction F := fun d => M.directionMap (mapDirection σ d)

theorem placedDirection_injective (σ : k →+* F) (M : PlaneLinearMap F) :
    Function.Injective (placedDirection σ M) :=
  M.directionMap_injective.comp (mapDirection_injective σ)

theorem projection_placedPoint_eq_iff (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (d : Direction k) (p q : Point k) :
    projection (placedDirection σ M d) (placedPoint σ M b p) =
      projection (placedDirection σ M d) (placedPoint σ M b q) ↔
      projection d p = projection d q := by
  unfold placedDirection placedPoint
  rw [M.projection_directionMap_placed_eq_iff,
    projection_mapDirection_mapPoint, projection_mapDirection_mapPoint]
  exact σ.injective.eq_iff

end Subfield

end RyserCoveringCounterexample.Construction

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_DirectionSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [instFintypek : Fintype k]

def alteredDirections (σ : k →+* F) (M : PlaneLinearMap F) : Finset (Direction F) :=
  (Finset.univ.erase 0).image (fun t : k => placedDirection σ M (some t))

def axisDirections (σ : k →+* F) (M : PlaneLinearMap F) : Finset (Direction F) :=
  ({none, some 0} : Finset (Direction k)).image (placedDirection σ M)

theorem mem_alteredDirections_iff (σ : k →+* F) (M : PlaneLinearMap F)
    (d : Direction F) :
    d ∈ alteredDirections σ M ↔
      ∃ t : k, t ≠ 0 ∧ placedDirection σ M (some t) = d := by
  simp only [alteredDirections, Finset.mem_image, Finset.mem_erase,
    Finset.mem_univ, and_true]

theorem mem_axisDirections_iff (σ : k →+* F) (M : PlaneLinearMap F)
    (d : Direction F) :
    d ∈ axisDirections σ M ↔
      d = placedDirection σ M none ∨ d = placedDirection σ M (some 0) := let _ := instFintypek; by
  simp [axisDirections]

theorem placedDirection_mem_alteredDirections (σ : k →+* F) (M : PlaneLinearMap F)
    (t : k) (ht : t ≠ 0) :
    placedDirection σ M (some t) ∈ alteredDirections σ M :=
  (mem_alteredDirections_iff σ M _).mpr ⟨t, ht, rfl⟩

theorem disjoint_alteredDirections_axisDirections (σ : k →+* F)
    (M : PlaneLinearMap F) : Disjoint (alteredDirections σ M) (axisDirections σ M) := by
  apply Finset.disjoint_left.mpr
  intro d hd ha
  obtain ⟨t, ht, rfl⟩ := (mem_alteredDirections_iff σ M d).mp hd
  rcases (mem_axisDirections_iff σ M _).mp ha with hnone | hzero
  · have h := placedDirection_injective σ M hnone
    cases h
  · exact ht (Option.some.inj (placedDirection_injective σ M hzero))

theorem placedDirection_mem_altered_or_axis (σ : k →+* F) (M : PlaneLinearMap F)
    (d : Direction k) :
    placedDirection σ M d ∈ alteredDirections σ M ∪ axisDirections σ M := by
  cases d with
  | none =>
      exact Finset.mem_union_right _ ((mem_axisDirections_iff σ M _).mpr (Or.inl rfl))
  | some t =>
      by_cases ht : t = 0
      · subst t
        exact Finset.mem_union_right _ ((mem_axisDirections_iff σ M _).mpr (Or.inr rfl))
      · exact Finset.mem_union_left _ (placedDirection_mem_alteredDirections σ M t ht)

theorem card_alteredDirections (σ : k →+* F) (M : PlaneLinearMap F) :
    (alteredDirections σ M).card = Fintype.card k - 1 := by
  have hinj : Function.Injective (fun t : k => placedDirection σ M (some t)) := by
    intro t u h
    exact Option.some.inj (placedDirection_injective σ M h)
  unfold alteredDirections
  rw [Finset.card_image_of_injective _ hinj,
    Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]

theorem existsUnique_alteredSlope (σ : k →+* F) (M : PlaneLinearMap F)
    (d : {d : Direction F // d ∈ alteredDirections σ M}) :
    ∃! t : k, t ≠ 0 ∧ placedDirection σ M (some t) = d.val := by
  obtain ⟨t, ht, htd⟩ := (mem_alteredDirections_iff σ M d.val).mp d.property
  refine ⟨t, ⟨ht, htd⟩, ?_⟩
  intro u hu
  exact Option.some.inj (placedDirection_injective σ M (hu.2.trans htd.symm))

noncomputable def alteredInverseSlope (σ : k →+* F) (M : PlaneLinearMap F)
    (d : {d : Direction F // d ∈ alteredDirections σ M}) : k :=
  Classical.choose (existsUnique_alteredSlope σ M d).exists

end RyserCoveringCounterexample.Construction

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_GadgetAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F]

def cubeMap (p : Point F) : Point F := (p.1 ^ 3, p.2)

def cubicPoint (d z x : F) : Point F := (x ^ 3, d * x + z)

theorem cubicPoint_injective (d z : F) (hd : d ≠ 0) :
    Function.Injective (cubicPoint d z) := by
  intro x y h
  exact mul_left_cancel₀ hd (add_right_cancel (congrArg Prod.snd h))

variable [instFintypeF : Fintype F]

theorem cube_bijective (h : Nat.Coprime 3 (Fintype.card F - 1)) :
    Function.Bijective (fun x : F => x ^ 3) := by
  classical
  have hU : (Nat.card Fˣ).Coprime 3 := by
    rw [Nat.card_units, Nat.card_eq_fintype_card]
    exact h.symm
  have hpow : Function.Bijective (fun u : Fˣ => u ^ 3) :=
    Nat.Coprime.pow_left_bijective hU
  apply Function.Surjective.bijective_of_finite
  intro y
  by_cases hy : y = 0
  · subst y
    exact ⟨0, by simp⟩
  · obtain ⟨u, hu⟩ := hpow.surjective (Units.mk0 y hy)
    refine ⟨(u : F), ?_⟩
    simpa only [Units.val_pow_eq_pow_val, Units.val_mk0] using
      congrArg (fun v : Fˣ => (v : F)) hu

variable [instDecidableEqF : DecidableEq F]

def cubicShape (d z : F) : Finset (Point F) :=
  Finset.univ.image (cubicPoint d z)

@[simp] theorem mem_cubicShape {d z : F} {p : Point F} :
    p ∈ cubicShape d z ↔ ∃ x, cubicPoint d z x = p := by
  simp [cubicShape]

theorem cubicShape_card (d z : F) (hd : d ≠ 0) :
    (cubicShape d z).card = Fintype.card F := by
  rw [cubicShape, Finset.card_image_of_injective _ (cubicPoint_injective d z hd),
    Finset.card_univ]

open Polynomial

def cubicLinePolynomial (d z : F) : AffineLine F → F[X]
  | (none, b) => X ^ 3 - C b
  | (some m, b) => C d * X + C z - C m * X ^ 3 - C b

theorem eval_cubicLinePolynomial_eq_zero_iff (d z : F) (l : AffineLine F) (x : F) :
    (cubicLinePolynomial d z l).eval x = 0 ↔ Incidence (cubicPoint d z x) l := let _ := instFintypeF; let _ := instDecidableEqF; by
  obtain ⟨a, b⟩ := l
  cases a <;>
    simp [cubicLinePolynomial, cubicPoint, Incidence, projection, sub_eq_zero]

theorem cubicLinePolynomial_ne_zero (d z : F) (hd : d ≠ 0) (l : AffineLine F) :
    cubicLinePolynomial d z l ≠ 0 := let _ := instFintypeF; let _ := instDecidableEqF; by
  obtain ⟨a, b⟩ := l
  cases a with
  | none =>
      intro hp
      have hc := congrArg (fun p : F[X] => p.coeff 3) hp
      exact (one_ne_zero : (1 : F) ≠ 0)
        (by simp [cubicLinePolynomial, coeff_X_pow] at hc)
  | some m =>
      intro hp
      have hc := congrArg (fun p : F[X] => p.coeff 1) hp
      exact hd (by simpa [cubicLinePolynomial, coeff_X_pow] using hc)

theorem cubicLinePolynomial_natDegree_le (d z : F) (l : AffineLine F) :
    (cubicLinePolynomial d z l).natDegree ≤ 3 := let _ := instFintypeF; let _ := instDecidableEqF; by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have hn3 : n ≠ 3 := by omega
  obtain ⟨a, b⟩ := l
  cases a <;>
    simp [cubicLinePolynomial, coeff_X_pow, coeff_C, coeff_X,
      hn0, Ne.symm hn1, hn3]

theorem cubicShape_filter_incidence_card_le (d z : F) (hd : d ≠ 0)
    (l : AffineLine F) :
    ((cubicShape d z).filter (fun p => Incidence p l)).card ≤ 3 := by
  have hcount :
      (Finset.univ.filter (fun x => Incidence (cubicPoint d z x) l)).card ≤
        (cubicLinePolynomial d z l).natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro x hx
    exact (Polynomial.mem_roots (cubicLinePolynomial_ne_zero d z hd l)).2
      ((eval_cubicLinePolynomial_eq_zero_iff d z l x).2 (Finset.mem_filter.mp hx).2)
  rw [cubicShape, Finset.filter_image]
  exact (Finset.card_image_le.trans hcount).trans (cubicLinePolynomial_natDegree_le d z l)

theorem cubicShape_inter_linePoints_card_le (d z : F) (hd : d ≠ 0)
    (l : AffineLine F) :
    (cubicShape d z ∩ linePoints l).card ≤ 3 := by
  have heq : cubicShape d z ∩ linePoints l =
      (cubicShape d z).filter (fun p => Incidence p l) := by
    ext p
    simp
  rw [heq]
  exact cubicShape_filter_incidence_card_le d z hd l

theorem cubicShape_ne_linePoints (d z : F) (hd : d ≠ 0)
    (hcard : 3 < Fintype.card F) (l : AffineLine F) :
    cubicShape d z ≠ linePoints l := by
  intro heq
  have hall : (cubicShape d z).filter (fun p => Incidence p l) = cubicShape d z := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    exact (mem_linePoints _ _).mp (heq ▸ hp)
  have hle := cubicShape_filter_incidence_card_le d z hd l
  rw [hall, cubicShape_card d z hd] at hle
  exact (not_le_of_gt hcard) hle

theorem cubicShape_intercept_unique (h : Nat.Coprime 3 (Fintype.card F - 1))
    (d : F) (p : Point F) : ∃! z, p ∈ cubicShape d z := by
  obtain ⟨x, hx⟩ := (cube_bijective h).surjective p.1
  refine ⟨p.2 - d * x, ?_, ?_⟩
  · refine mem_cubicShape.mpr ⟨x, ?_⟩
    apply Prod.ext
    · exact hx
    · change d * x + (p.2 - d * x) = p.2
      ring
  · intro z hz
    obtain ⟨y, hy⟩ := mem_cubicShape.mp hz
    have hyx : y = x :=
      (cube_bijective h).injective ((congrArg Prod.fst hy).trans hx.symm)
    subst y
    apply eq_sub_iff_add_eq.mpr
    simpa [cubicPoint, add_comm] using congrArg Prod.snd hy

theorem cubicShape_intercept_card (h : Nat.Coprime 3 (Fintype.card F - 1))
    (d : F) (p : Point F) :
    (Finset.univ.filter (fun z => p ∈ cubicShape d z)).card = 1 := by
  obtain ⟨z, hz, hu⟩ := cubicShape_intercept_unique h d p
  apply Finset.card_eq_one.mpr
  refine ⟨z, ?_⟩
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨hu w, fun hw => hw ▸ hz⟩

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_GadgetDefinitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k]

abbrev NonzeroSlope (k : Type*) [Zero k] := {d : k // d ≠ 0}

abbrev GadgetOutcome (k : Type*) [Zero k] := NonzeroSlope k → k

def omittedLine (a : GadgetOutcome k) (d : NonzeroSlope k) : AffineLine k :=
  (some d.val, a d)

def retainedPoints (a : GadgetOutcome k) : Finset (Point k) :=
  Finset.univ \ Finset.univ.biUnion (fun d => linePoints (omittedLine a d))

def transformedRetained (a : GadgetOutcome k) : Finset (Point k) :=
  (retainedPoints a).image cubeMap

def cubicDeletionUnion (a : GadgetOutcome k) : Finset (Point k) :=
  Finset.univ.biUnion fun d : NonzeroSlope k => cubicShape d.val (a d)

@[simp] theorem mem_retainedPoints (a : GadgetOutcome k) (w : Point k) :
    w ∈ retainedPoints a ↔ ∀ d, ¬Incidence w (omittedLine a d) := by
  simp [retainedPoints]

theorem not_incidence_omittedLine (a : GadgetOutcome k) {w : Point k}
    (hw : w ∈ retainedPoints a) (d : NonzeroSlope k) :
    ¬Incidence w (omittedLine a d) := (mem_retainedPoints a w).mp hw d

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_PlacedLines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k : Type*} [Field k]

def lineAnchor (l : AffineLine k) : Point k :=
  match l.1 with
  | none => (l.2, 0)
  | some _ => (0, l.2)

@[simp] theorem projection_lineAnchor (l : AffineLine k) :
    projection l.1 (lineAnchor l) = l.2 := by
  obtain ⟨d, c⟩ := l
  cases d <;> simp [lineAnchor, projection]

@[simp] theorem incidence_lineAnchor (l : AffineLine k) :
    Incidence (lineAnchor l) l :=
  projection_lineAnchor l

variable {F : Type*} [Field F] [DecidableEq F] [instDecidableEqk : DecidableEq k]

def placedLine (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    (l : AffineLine k) : AffineLine F :=
  lineThrough (placedDirection σ M l.1) (placedPoint σ M b (lineAnchor l))

@[simp] theorem placedLine_direction (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (l : AffineLine k) :
    (placedLine σ M b l).1 = placedDirection σ M l.1 := let _ := instDecidableEqk; rfl

theorem incidence_placedLine_iff (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (p : Point k) (l : AffineLine k) :
    Incidence (placedPoint σ M b p) (placedLine σ M b l) ↔ Incidence p l := by
  change projection (placedDirection σ M l.1) (placedPoint σ M b p) =
      projection (placedDirection σ M l.1) (placedPoint σ M b (lineAnchor l)) ↔
    projection l.1 p = l.2
  rw [projection_placedPoint_eq_iff, projection_lineAnchor]

theorem placedLine_injective (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) : Function.Injective (placedLine σ M b) := by
  intro l m hlm
  have hdir : l.1 = m.1 :=
    placedDirection_injective σ M (congrArg Prod.fst hlm)
  have hinc : Incidence (lineAnchor l) m := by
    apply (incidence_placedLine_iff σ M b (lineAnchor l) m).mp
    rw [← hlm]
    exact (incidence_placedLine_iff σ M b (lineAnchor l) l).mpr
      (incidence_lineAnchor l)
  exact line_eq_of_direction_eq_of_incidence hdir (incidence_lineAnchor l) hinc

theorem eq_placedLine_of_direction_of_incidence
    (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    (p : Point k) (d : Direction k) (ell : AffineLine F)
    (hdir : ell.1 = placedDirection σ M d)
    (hinc : Incidence (placedPoint σ M b p) ell) :
    ell = placedLine σ M b (d, projection d p) := by
  apply line_eq_of_direction_eq_of_incidence
  · exact hdir
  · exact hinc
  · exact (incidence_placedLine_iff σ M b p (d, projection d p)).mpr rfl

end RyserCoveringCounterexample.Construction

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_DeletionLines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

open scoped BigOperators

variable {k F : Type*} [Field k] [Field F]
variable [Fintype k] [instFintypeF : Fintype F] [DecidableEq k] [DecidableEq F]

def OriginalLineDensity (a : GadgetOutcome k) : Prop :=
  ∀ t : NonzeroSlope k, ∀ c : k, c ≠ a t →
    5 ≤ ((retainedPoints a).filter (fun p => Incidence p (some t.val, c))).card

def deletedLines (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    (a : GadgetOutcome k) : Finset (AffineLine F) :=
  Finset.univ.filter (fun ell => ell.1 ∈ alteredDirections σ M ∧
    ∃ y ∈ retainedPoints a, Incidence (placedPoint σ M b y) ell)

@[simp] theorem mem_deletedLines (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (a : GadgetOutcome k) (ell : AffineLine F) :
    ell ∈ deletedLines σ M b a ↔ ell.1 ∈ alteredDirections σ M ∧
      ∃ y ∈ retainedPoints a, Incidence (placedPoint σ M b y) ell := by
  simp only [deletedLines, Finset.mem_filter, Finset.mem_univ, true_and]

theorem intercept_ne_omitted_of_mem_retained (a : GadgetOutcome k)
    (t : NonzeroSlope k) {p : Point k} {c : k}
    (hp : p ∈ retainedPoints a) (hpc : Incidence p (some t.val, c)) :
    c ≠ a t := by
  intro hc
  apply not_incidence_omittedLine a hp t
  simpa only [omittedLine, hc] using hpc

theorem deletedLines_direction_eq_image (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (a : GadgetOutcome k) (ha : OriginalLineDensity a)
    (t : NonzeroSlope k) :
    (deletedLines σ M b a).filter
        (fun ell => ell.1 = placedDirection σ M (some t.val)) =
      (Finset.univ.erase (a t)).image
        (fun c : k => placedLine σ M b (some t.val, c)) := by
  ext ell
  constructor
  · intro hell
    obtain ⟨hdel, hdir⟩ := Finset.mem_filter.mp hell
    obtain ⟨y, hy, hyell⟩ := ((mem_deletedLines σ M b a ell).mp hdel).2
    have hline : ell = placedLine σ M b
        (some t.val, projection (some t.val) y) :=
      eq_placedLine_of_direction_of_incidence σ M b y (some t.val) ell hdir hyell
    have hc : projection (some t.val) y ≠ a t :=
      intercept_ne_omitted_of_mem_retained a t hy rfl
    exact Finset.mem_image.mpr
      ⟨projection (some t.val) y, Finset.mem_erase.mpr ⟨hc, Finset.mem_univ _⟩,
        hline.symm⟩
  · intro hell
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hell
    have hpos : 0 < ((retainedPoints a).filter
        (fun p => Incidence p (some t.val, c))).card :=
      lt_of_lt_of_le (by decide : 0 < 5) (ha t c (Finset.mem_erase.mp hc).1)
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
    obtain ⟨hyret, hyline⟩ := Finset.mem_filter.mp hy
    apply Finset.mem_filter.mpr
    refine ⟨(mem_deletedLines σ M b a _).mpr ?_, rfl⟩
    exact ⟨placedDirection_mem_alteredDirections σ M t.val t.property,
      y, hyret, (incidence_placedLine_iff σ M b y _).mpr hyline⟩

theorem card_deletedLines_direction (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (a : GadgetOutcome k) (ha : OriginalLineDensity a)
    (t : NonzeroSlope k) :
    ((deletedLines σ M b a).filter
      (fun ell => ell.1 = placedDirection σ M (some t.val))).card =
        Fintype.card k - 1 := by
  have hinj : Function.Injective
      (fun c : k => placedLine σ M b (some t.val, c)) := by
    intro c c' h
    exact congrArg Prod.snd (placedLine_injective σ M b h)
  rw [deletedLines_direction_eq_image σ M b a ha t,
    Finset.card_image_of_injective _ hinj,
    Finset.card_erase_of_mem (Finset.mem_univ (a t)), Finset.card_univ]

theorem card_deletedLines_of_mem_alteredDirections (σ : k →+* F)
    (M : PlaneLinearMap F) (b : Point F) (a : GadgetOutcome k)
    (ha : OriginalLineDensity a) (d : Direction F)
    (hd : d ∈ alteredDirections σ M) :
    ((deletedLines σ M b a).filter (fun ell => ell.1 = d)).card =
      Fintype.card k - 1 := by
  obtain ⟨t, ht, rfl⟩ := (mem_alteredDirections_iff σ M d).mp hd
  exact card_deletedLines_direction σ M b a ha ⟨t, ht⟩

theorem card_deletedLines (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (a : GadgetOutcome k) (ha : OriginalLineDensity a) :
    (deletedLines σ M b a).card = (Fintype.card k - 1) ^ 2 := by
  calc
    (deletedLines σ M b a).card =
        ∑ d ∈ alteredDirections σ M,
          ((deletedLines σ M b a).filter (fun ell => ell.1 = d)).card :=
      Finset.card_eq_sum_card_fiberwise
        (fun ell hell => ((mem_deletedLines σ M b a ell).mp hell).1)
    _ = (alteredDirections σ M).card * (Fintype.card k - 1) :=
      Finset.sum_const_nat (fun d hd =>
        card_deletedLines_of_mem_alteredDirections σ M b a ha d hd)
    _ = (Fintype.card k - 1) ^ 2 := by rw [card_alteredDirections, pow_two]

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Geometry_Cardinality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample

variable {F : Type*} [instFieldF : Field F] [Fintype F] [instDecidableEqF : DecidableEq F]

@[simp] theorem card_point :
    Fintype.card (Point F) = Fintype.card F ^ 2 := let _ := instFieldF; let _ := instDecidableEqF; by
  simp only [Point, Fintype.card_prod, pow_two]

@[simp] theorem card_direction :
    Fintype.card (Direction F) = Fintype.card F + 1 := let _ := instFieldF; let _ := instDecidableEqF; by
  exact Fintype.card_option

@[simp] theorem card_affineLine :
    Fintype.card (AffineLine F) = Fintype.card F * (Fintype.card F + 1) := by
  simp only [AffineLine, Fintype.card_prod, card_direction, Nat.mul_comm]

@[simp] theorem card_projectivePoint :
    Fintype.card (ProjectivePoint F) =
      Fintype.card F ^ 2 + Fintype.card F + 1 := by
  simp only [ProjectivePoint, Fintype.card_sum, card_point, card_direction, Nat.add_assoc]

@[simp] theorem card_projectiveLine :
    Fintype.card (ProjectiveLine F) =
      Fintype.card F ^ 2 + Fintype.card F + 1 := by
  simp only [ProjectiveLine, Fintype.card_option, card_affineLine,
    Nat.mul_add, Nat.mul_one, pow_two]

def linePointEquiv (l : AffineLine F) : F ≃ ↥(linePoints l) := by
  rcases l with ⟨d, b⟩
  cases d with
  | none =>
      refine
        { toFun := fun t => ⟨(b, t), by simp [Incidence, projection]⟩
          invFun := fun p => p.val.2
          left_inv := fun _ => rfl
          right_inv := ?_ }
      intro p
      apply Subtype.ext
      apply Prod.ext
      · have hp := (mem_linePoints p.val (none, b)).mp p.property
        change p.val.1 = b at hp
        exact hp.symm
      · rfl
  | some a =>
      refine
        { toFun := fun t => ⟨(t, b + a * t), by simp [Incidence, projection]⟩
          invFun := fun p => p.val.1
          left_inv := fun _ => rfl
          right_inv := ?_ }
      intro p
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · have hp := (mem_linePoints p.val (some a, b)).mp p.property
        change p.val.2 - a * p.val.1 = b at hp
        simpa only [sub_add_cancel] using
          (congrArg (fun u : F => u + a * p.val.1) hp).symm

@[simp] theorem card_linePoints (l : AffineLine F) :
    (linePoints l).card = Fintype.card F := by
  simpa only [Fintype.card_coe] using (Fintype.card_congr (linePointEquiv l)).symm

def affinePencilFiniteEquiv (p : Point F) :
    Direction F ≃ ↥(affinePencil (Sum.inl p)) where
  toFun d := ⟨lineThrough d p, by simp⟩
  invFun l := l.val.1
  left_inv _ := rfl
  right_inv l := by
    apply Subtype.ext
    have hl : Incidence p l.val :=
      (mem_affinePencil (Sum.inl p) l.val).mp l.property
    exact (eq_lineThrough_of_incidence hl).symm

def affinePencilInfiniteEquiv (d : Direction F) :
    F ≃ ↥(affinePencil (Sum.inr d)) where
  toFun b := ⟨(d, b), by simp⟩
  invFun l := l.val.2
  left_inv _ := rfl
  right_inv l := by
    apply Subtype.ext
    apply Prod.ext
    · exact (mem_affinePencil (Sum.inr d) l.val).mp l.property
    · rfl

@[simp] theorem card_affinePencil_finite (p : Point F) :
    (affinePencil (Sum.inl p)).card = Fintype.card F + 1 := by
  simpa only [Fintype.card_coe, card_direction] using
    (Fintype.card_congr (affinePencilFiniteEquiv p)).symm

@[simp] theorem card_affinePencil_infinite (d : Direction F) :
    (affinePencil (Sum.inr d)).card = Fintype.card F := by
  simpa only [Fintype.card_coe] using
    (Fintype.card_congr (affinePencilInfiniteEquiv d)).symm

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Probability_Finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample

structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1

namespace FiniteLaw

def expectation {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  ∑ ω, μ.weight ω * f ω

def prob {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (P : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if P ω then μ.weight ω else 0

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

@[simp] theorem expectation_const (μ : FiniteLaw Ω) (c : ℝ) :
    μ.expectation (fun _ => c) = c := by
  rw [expectation, ← Finset.sum_mul, μ.total, one_mul]

theorem expectation_sum {ι : Type*} [Fintype ι] (μ : FiniteLaw Ω) (f : ι → Ω → ℝ) :
    μ.expectation (fun ω => ∑ i, f i ω) = ∑ i, μ.expectation (f i) := by
  simp only [expectation, Finset.mul_sum]
  exact Finset.sum_comm

theorem expectation_mono (μ : FiniteLaw Ω) {f g : Ω → ℝ} (hfg : ∀ ω, f ω ≤ g ω) :
    μ.expectation f ≤ μ.expectation g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (μ.nonneg ω)

theorem prob_eq_expectation (μ : FiniteLaw Ω) (P : Ω → Prop) :
    μ.prob P = μ.expectation (fun ω => if P ω then 1 else 0) := by
  classical
  simp [prob, expectation, mul_ite]

@[simp] theorem prob_true (μ : FiniteLaw Ω) : μ.prob (fun _ => True) = 1 := by
  simp [prob, μ.total]

@[simp] theorem prob_false (μ : FiniteLaw Ω) : μ.prob (fun _ => False) = 0 := by
  simp [prob]

theorem prob_compl (μ : FiniteLaw Ω) (P : Ω → Prop) :
    μ.prob (fun ω => ¬ P ω) = 1 - μ.prob P := by
  classical
  have h : μ.prob P + μ.prob (fun ω => ¬ P ω) = 1 := by
    rw [prob, prob, ← Finset.sum_add_distrib, ← μ.total]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hp : P ω <;> simp [hp]
  linarith

theorem prob_le_expectation (μ : FiniteLaw Ω) (P : Ω → Prop) (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) (hP : ∀ ω, P ω → 1 ≤ f ω) : μ.prob P ≤ μ.expectation f := by
  classical
  rw [prob_eq_expectation]
  apply μ.expectation_mono
  intro ω
  by_cases hp : P ω
  · simpa [hp] using hP ω hp
  · simpa [hp] using hf ω

def prod (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) : FiniteLaw (Ω × Γ) where
  weight ω := μ.weight ω.1 * ν.weight ω.2
  nonneg ω := mul_nonneg (μ.nonneg _) (ν.nonneg _)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, ν.total, mul_one, μ.total]

@[simp] theorem prod_weight (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) (ω : Ω) (γ : Γ) :
    (μ.prod ν).weight (ω, γ) = μ.weight ω * ν.weight γ := rfl

def pi {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*} [∀ i, Fintype (A i)]
    (μ : ∀ i, FiniteLaw (A i)) : FiniteLaw (∀ i, A i) := by
  classical
  exact {
    weight := fun ω => ∏ i, (μ i).weight (ω i)
    nonneg := fun ω => Finset.prod_nonneg fun i _ => (μ i).nonneg (ω i)
    total := by
      rw [← Fintype.prod_sum (fun i a => (μ i).weight a)]
      simp_rw [(μ _).total]
      simp }

@[simp] theorem pi_weight {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*} [∀ i, Fintype (A i)]
    (μ : ∀ i, FiniteLaw (A i)) (ω : ∀ i, A i) :
    (pi μ).weight ω = ∏ i, (μ i).weight (ω i) := rfl

def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteLaw Ω where
  weight _ := (Fintype.card Ω : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    have hN : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp [hN]

theorem uniform_prob (Ω : Type*) [Fintype Ω] [Nonempty Ω] (P : Ω → Prop) :
    (uniform Ω).prob P = ((Finset.univ.filter P).card : ℝ) / Fintype.card Ω := by
  simp [prob, uniform, ← Finset.sum_filter, div_eq_mul_inv]

@[ext] theorem ext_weight {mu nu : FiniteLaw Ω} (h : mu.weight = nu.weight) :
    mu = nu := by
  cases mu
  cases nu
  cases h
  rfl

theorem prob_exists_le {ι : Type*} [Fintype ι] (mu : FiniteLaw Ω)
    (P : ι → Ω → Prop) :
    mu.prob (fun x => ∃ i, P i x) ≤ ∑ i, mu.prob (P i) := by
  classical
  have hn (i : ι) (x : Ω) : 0 ≤ (if P i x then (1 : ℝ) else 0) := by
    by_cases hix : P i x <;> simp [hix]
  calc
    _ ≤ mu.expectation (fun x => ∑ i, if P i x then (1 : ℝ) else 0) := by
      apply mu.prob_le_expectation
      · exact fun x => Finset.sum_nonneg (fun i _ => hn i x)
      · rintro x ⟨i, hi⟩
        calc
          1 = (if P i x then (1 : ℝ) else 0) := by rw [ite_eq_left hi]
          _ ≤ ∑ j, if P j x then (1 : ℝ) else 0 :=
            Finset.single_le_sum (fun j _ => hn j x) (Finset.mem_univ i)
    _ = ∑ i, mu.prob (P i) := by
      rw [expectation_sum]
      simp_rw [← prob_eq_expectation]

end FiniteLaw

end RyserCoveringCounterexample

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

structure Data (F : Type*) [Field F] (n : ℕ) where
  W : Fin n → Finset (Point F)
  dirs : Fin n → Finset (Direction F)

abbrev Position (n K : ℕ) := Fin n × Fin K
abbrev Pool (F : Type*) (n K : ℕ) := Position n K → Point F

variable {F : Type*} [Field F] [instDecidableEqF : DecidableEq F] {n K : ℕ}

def Conflict (data : Data F n) (i j : Fin n) (b b' : Point F) : Prop :=
  ∃ u ∈ data.W i, ∃ v ∈ data.W j, ∃ d ∈ data.dirs i ∪ data.dirs j,
    projection d ((b + u) - (b' + v)) = 0

theorem projection_sub_eq (d : Direction F) (p q : Point F) :
    projection d (p - q) = projection d p - projection d q := let _ := instDecidableEqF; by
  exact RyserCoveringCounterexample.projection_sub d p q

theorem Conflict.symm {data : Data F n} {i j : Fin n} {b b' : Point F}
    (h : Conflict data i j b b') : Conflict data j i b' b := by
  rcases h with ⟨u, hu, v, hv, d, hd, heq⟩
  refine ⟨v, hv, u, hu, d, ?_, ?_⟩
  · simpa only [Finset.union_comm] using hd
  · rw [projection_sub_eq] at heq ⊢
    exact sub_eq_zero.mpr (sub_eq_zero.mp heq).symm

def HasCompatibleChoice (data : Data F n) (pool : Pool F n K) : Prop :=
  ∃ choice : Fin n → Fin K, ∀ i j, i ≠ j →
    ¬ Conflict data i j (pool (i, choice i)) (pool (j, choice j))

def Feasible (data : Data F n) (T : Finset (Position n K))
    (pool : Pool F n K) (i : Fin n) (b : Point F) : Prop :=
  ∀ e ∈ T, ¬ Conflict data i e.1 b (pool e)

@[simp] theorem feasible_empty (data : Data F n) (pool : Pool F n K)
    (i : Fin n) (b : Point F) : Feasible data ∅ pool i b := by
  simp [Feasible]

section Finite
variable [Fintype F]

noncomputable def feasibleSet (data : Data F n) (T : Finset (Position n K))
    (pool : Pool F n K) (i : Fin n) : Finset (Point F) := by
  classical
  exact Finset.univ.filter (Feasible data T pool i)

@[simp] theorem mem_feasibleSet (data : Data F n) (T : Finset (Position n K))
    (pool : Pool F n K) (i : Fin n) (b : Point F) :
    b ∈ feasibleSet data T pool i ↔ Feasible data T pool i b := by
  classical
  simp only [feasibleSet, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem feasibleSet_empty (data : Data F n) (pool : Pool F n K)
    (i : Fin n) : feasibleSet data ∅ pool i = Finset.univ := by
  classical
  ext b
  simp

end Finite
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

theorem uniform_prob_projection (d : Direction F) (c : F) :
    (FiniteLaw.uniform (Point F)).prob (fun b => projection d b = c) =
      1 / (Fintype.card F : ℝ) := by
  classical
  rw [FiniteLaw.uniform_prob]
  calc
    _ = ((linePoints (d, c)).card : ℝ) / (Fintype.card (Point F) : ℝ) := by
      apply congrArg (fun T : Finset (Point F) =>
        (T.card : ℝ) / (Fintype.card (Point F) : ℝ))
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_linePoints, Incidence]
    _ = _ := by
      rw [card_linePoints, card_point, Nat.cast_pow]
      have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      field_simp

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_AmbientDeletionGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F]

def shiftAffineLine (b : Point F) (l : AffineLine F) : AffineLine F :=
  (l.1, l.2 + projection l.1 b)

@[simp] theorem shiftAffineLine_direction (b : Point F) (l : AffineLine F) :
    (shiftAffineLine b l).1 = l.1 := rfl

@[simp] theorem shiftAffineLine_offset (b : Point F) (l : AffineLine F) :
    (shiftAffineLine b l).2 = l.2 + projection l.1 b := rfl

@[simp] theorem shiftAffineLine_zero (l : AffineLine F) : shiftAffineLine 0 l = l := by
  obtain ⟨d, c⟩ := l
  cases d <;> simp [shiftAffineLine, projection]

theorem incidence_shiftAffineLine_iff (b x : Point F) (l : AffineLine F) :
    Incidence x (shiftAffineLine b l) ↔ Incidence (x - b) l := by
  change projection l.1 x = l.2 + projection l.1 b ↔ projection l.1 (x - b) = l.2
  have hproj : projection l.1 (x - b) = projection l.1 x - projection l.1 b :=
    projection_sub l.1 x b
  rw [hproj, sub_eq_iff_eq_add]

section Finite

variable [Fintype F] [DecidableEq F]

def ambientLineUnion (B : Finset (AffineLine F)) : Finset (Point F) :=
  B.biUnion linePoints

@[simp] theorem mem_ambientLineUnion (B : Finset (AffineLine F)) (x : Point F) :
    x ∈ ambientLineUnion B ↔ ∃ l ∈ B, Incidence x l := by
  simp only [ambientLineUnion, Finset.mem_biUnion, mem_linePoints]

theorem mem_ambientLineUnion_shift (B : Finset (AffineLine F)) (b x : Point F) :
    x ∈ ambientLineUnion (B.image (shiftAffineLine b)) ↔ x - b ∈ ambientLineUnion B := by
  rw [mem_ambientLineUnion, mem_ambientLineUnion]
  constructor
  · rintro ⟨l, hl, hxl⟩
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hl
    exact ⟨m, hm, (incidence_shiftAffineLine_iff b x m).mp hxl⟩
  · rintro ⟨l, hl, hxl⟩
    exact ⟨shiftAffineLine b l, Finset.mem_image.mpr ⟨l, hl, rfl⟩,
      (incidence_shiftAffineLine_iff b x l).mpr hxl⟩

theorem card_ambientLineUnion_le (B : Finset (AffineLine F)) :
    (ambientLineUnion B).card ≤ B.card * Fintype.card F :=
  Finset.card_biUnion_le_card_mul B linePoints (Fintype.card F)
    (fun l _ => (card_linePoints l).le)

theorem uniform_prob_mem_ambientLineUnion_shift (B : Finset (AffineLine F)) (x : Point F) :
    (FiniteLaw.uniform (Point F)).prob
        (fun b => x ∈ ambientLineUnion (B.image (shiftAffineLine b))) =
      ((ambientLineUnion B).card : ℝ) / (Fintype.card F : ℝ) ^ 2 := by
  classical
  have hinj : Function.Injective (fun y : Point F => x - y) := by
    intro y z hyz
    have h := congrArg (fun w : Point F => x - w) hyz
    simpa only [sub_sub_cancel] using h
  rw [FiniteLaw.uniform_prob]
  calc
    _ = (((ambientLineUnion B).image (fun y => x - y)).card : ℝ) /
        (Fintype.card (Point F) : ℝ) := by
      apply congrArg (fun T : Finset (Point F) =>
        (T.card : ℝ) / (Fintype.card (Point F) : ℝ))
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_ambientLineUnion_shift]
      constructor
      · intro hb
        exact Finset.mem_image.mpr ⟨x - b, hb, sub_sub_cancel x b⟩
      · intro hb
        obtain ⟨y, hy, hyb⟩ := Finset.mem_image.mp hb
        rw [← hyb, sub_sub_cancel]
        exact hy
    _ = _ := by
      rw [Finset.card_image_of_injective _ hinj, card_point, Nat.cast_pow]

theorem uniform_prob_mem_ambientLineUnion_shift_le (B : Finset (AffineLine F))
    (x : Point F) :
    (FiniteLaw.uniform (Point F)).prob
        (fun b => x ∈ ambientLineUnion (B.image (shiftAffineLine b))) ≤
      (B.card : ℝ) / (Fintype.card F : ℝ) := by
  rw [uniform_prob_mem_ambientLineUnion_shift]
  have hcard : ((ambientLineUnion B).card : ℝ) ≤
      (B.card : ℝ) * (Fintype.card F : ℝ) := by
    exact_mod_cast card_ambientLineUnion_le B
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc
    ((ambientLineUnion B).card : ℝ) / (Fintype.card F : ℝ) ^ 2 ≤
        ((B.card : ℝ) * (Fintype.card F : ℝ)) / (Fintype.card F : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hcard (sq_nonneg _)
    _ = (B.card : ℝ) / (Fintype.card F : ℝ) := by
      field_simp [hq]

theorem uniform_prob_mem_image_shiftAffineLine_le (B : Finset (AffineLine F))
    (l : AffineLine F) :
    (FiniteLaw.uniform (Point F)).prob (fun b => l ∈ B.image (shiftAffineLine b)) ≤
      ((B.filter (fun e => e.1 = l.1)).card : ℝ) / (Fintype.card F : ℝ) := by
  classical
  let T := B.filter (fun e => e.1 = l.1)
  have hP : (fun b => l ∈ B.image (shiftAffineLine b)) =
      (fun b => ∃ e : ↥T, projection l.1 b = l.2 - e.val.2) := by
    funext b
    apply propext
    constructor
    · intro hb
      obtain ⟨e, heB, heq⟩ := Finset.mem_image.mp hb
      have hdir := congrArg Prod.fst heq
      change e.1 = l.1 at hdir
      have hoff := congrArg Prod.snd heq
      change e.2 + projection e.1 b = l.2 at hoff
      have hproj : projection l.1 b = l.2 - e.2 := by
        rw [← hdir]
        apply (eq_sub_iff_add_eq).2
        exact (add_comm _ _).trans hoff
      exact ⟨⟨e, Finset.mem_filter.mpr ⟨heB, hdir⟩⟩, hproj⟩
    · rintro ⟨e, heq⟩
      have hdir : e.val.1 = l.1 := (Finset.mem_filter.mp e.property).2
      refine Finset.mem_image.mpr ⟨e.val, (Finset.mem_filter.mp e.property).1, ?_⟩
      apply Prod.ext
      · exact hdir
      · change e.val.2 + projection e.val.1 b = l.2
        rw [hdir, heq]
        ring
  rw [hP]
  calc
    _ ≤ ∑ e : ↥T, (FiniteLaw.uniform (Point F)).prob
        (fun b => projection l.1 b = l.2 - e.val.2) := FiniteLaw.prob_exists_le _ _
    _ = ∑ _e : ↥T, 1 / (Fintype.card F : ℝ) := by
      apply Finset.sum_congr rfl
      intro e _
      exact Selection.uniform_prob_projection l.1 (l.2 - e.val.2)
    _ = ((B.filter (fun e => e.1 = l.1)).card : ℝ) / (Fintype.card F : ℝ) := by
      simp [T, div_eq_mul_inv]

end Finite

section Placed

variable {k : Type*} [Field k] [instFintypek : Fintype k] [instDecidableEqk : DecidableEq k]
variable [instFintypeF : Fintype F] [instDecidableEqF : DecidableEq F]

theorem placedPoint_sub_shift (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (y : Point k) :
    placedPoint σ M b y - b = placedPoint σ M 0 y := let _ := instFintypek; let _ := instDecidableEqk; let _ := instFintypeF; let _ := instDecidableEqF; by
  simp only [placedPoint, add_sub_cancel_left, zero_add]

theorem mem_deletedLines_shift (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (a : GadgetOutcome k) (l : AffineLine F) :
    shiftAffineLine b l ∈ deletedLines σ M b a ↔ l ∈ deletedLines σ M 0 a := by
  simp only [mem_deletedLines, shiftAffineLine_direction, incidence_shiftAffineLine_iff,
    placedPoint_sub_shift]

theorem deletedLines_eq_image_shiftAffineLine (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (a : GadgetOutcome k) :
    deletedLines σ M b a = (deletedLines σ M 0 a).image (shiftAffineLine b) := by
  ext l
  constructor
  · intro hl
    let m : AffineLine F := (l.1, l.2 - projection l.1 b)
    have hm : shiftAffineLine b m = l := by
      apply Prod.ext
      · rfl
      · exact sub_add_cancel _ _
    refine Finset.mem_image.mpr ⟨m, ?_, hm⟩
    apply (mem_deletedLines_shift σ M b a m).mp
    rw [hm]
    exact hl
  · intro hl
    obtain ⟨m, hm, hml⟩ := Finset.mem_image.mp hl
    rw [← hml]
    exact (mem_deletedLines_shift σ M b a m).mpr hm

theorem uniform_prob_mem_deletedLines_union (σ : k →+* F) (M : PlaneLinearMap F)
    (a : GadgetOutcome k) (x : Point F) :
    (FiniteLaw.uniform (Point F)).prob (fun b => x ∈ ambientLineUnion (deletedLines σ M b a)) =
      ((ambientLineUnion (deletedLines σ M 0 a)).card : ℝ) / (Fintype.card F : ℝ) ^ 2 := by
  have hP : (fun b => x ∈ ambientLineUnion (deletedLines σ M b a)) =
      (fun b => x ∈ ambientLineUnion ((deletedLines σ M 0 a).image (shiftAffineLine b))) := by
    funext b
    rw [deletedLines_eq_image_shiftAffineLine σ M b a]
  rw [hP]
  exact uniform_prob_mem_ambientLineUnion_shift (deletedLines σ M 0 a) x

theorem uniform_prob_mem_deletedLines_union_le (σ : k →+* F) (M : PlaneLinearMap F)
    (a : GadgetOutcome k) (x : Point F) :
    (FiniteLaw.uniform (Point F)).prob (fun b => x ∈ ambientLineUnion (deletedLines σ M b a)) ≤
      ((deletedLines σ M 0 a).card : ℝ) / (Fintype.card F : ℝ) := by
  have hP : (fun b => x ∈ ambientLineUnion (deletedLines σ M b a)) =
      (fun b => x ∈ ambientLineUnion ((deletedLines σ M 0 a).image (shiftAffineLine b))) := by
    funext b
    rw [deletedLines_eq_image_shiftAffineLine σ M b a]
  rw [hP]
  exact uniform_prob_mem_ambientLineUnion_shift_le (deletedLines σ M 0 a) x

theorem uniform_prob_mem_deletedLines_le (σ : k →+* F) (M : PlaneLinearMap F)
    (a : GadgetOutcome k) (l : AffineLine F) :
    (FiniteLaw.uniform (Point F)).prob (fun b => l ∈ deletedLines σ M b a) ≤
      (((deletedLines σ M 0 a).filter (fun e => e.1 = l.1)).card : ℝ) /
        (Fintype.card F : ℝ) := by
  have hP : (fun b => l ∈ deletedLines σ M b a) =
      (fun b => l ∈ (deletedLines σ M 0 a).image (shiftAffineLine b)) := by
    funext b
    rw [deletedLines_eq_image_shiftAffineLine σ M b a]
  rw [hP]
  exact uniform_prob_mem_image_shiftAffineLine_le (deletedLines σ M 0 a) l

end Placed

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_AmbientDeletionNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Construction

noncomputable def ambientDeletionDelta (s K : ℕ) : ℝ :=
  Real.exp (-4 * (K : ℝ) * ((s - 1 : ℕ) : ℝ))

theorem neg_two_mul_le_log_one_sub {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    -2 * t ≤ Real.log (1 - t) := by
  have hb : 0 < 1 - t := by linarith
  have hratio : t / (1 - t) ≤ 2 * t := by
    apply (div_le_iff₀ hb).2
    have hmul := mul_nonneg ht0 (show 0 ≤ 1 - 2 * t by linarith)
    nlinarith only [hmul]
  have hid : 1 - (1 - t)⁻¹ = -(t / (1 - t)) := by
    field_simp [hb.ne']
    ring
  calc
    -2 * t ≤ -(t / (1 - t)) := by linarith only [hratio]
    _ = 1 - (1 - t)⁻¹ := hid.symm
    _ ≤ Real.log (1 - t) := Real.one_sub_inv_le_log_of_pos hb

theorem exp_neg_two_mul_le_one_sub_pow (N : ℕ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    Real.exp (-2 * (N : ℝ) * t) ≤ (1 - t) ^ N := by
  have hb : 0 < 1 - t := by linarith
  apply (Real.le_log_iff_exp_le (pow_pos hb N)).mp
  rw [Real.log_pow]
  have hlog := mul_le_mul_of_nonneg_left (neg_two_mul_le_log_one_sub ht0 ht)
    (Nat.cast_nonneg N : (0 : ℝ) ≤ (N : ℝ))
  nlinarith only [hlog]

theorem ambientDeletionDelta_le_pow (s K q N : ℕ) (hs : 2 ≤ s) (hq : 0 < q)
    (hsmall : 2 * (s - 1) ^ 2 ≤ q) (hcount : N * (s - 1) ≤ 2 * K * q) :
    ambientDeletionDelta s K ≤ (1 - ((s - 1 : ℕ) : ℝ) ^ 2 / (q : ℝ)) ^ N := by
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hm : (0 : ℝ) < ((s - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hs)
  have hsmall' : (2 : ℝ) * ((s - 1 : ℕ) : ℝ) ^ 2 ≤ (q : ℝ) := by
    exact_mod_cast hsmall
  have hcount' : (N : ℝ) * ((s - 1 : ℕ) : ℝ) ≤ 2 * (K : ℝ) * (q : ℝ) := by
    exact_mod_cast hcount
  let t : ℝ := ((s - 1 : ℕ) : ℝ) ^ 2 / (q : ℝ)
  have ht0 : 0 ≤ t := div_nonneg (sq_nonneg _) hq'.le
  have ht : t ≤ 1 / 2 := by
    apply (div_le_iff₀ hq').2
    nlinarith only [hsmall']
  have htotal : (N : ℝ) * t ≤ 2 * (K : ℝ) * ((s - 1 : ℕ) : ℝ) := by
    dsimp only [t]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hq').2
    have hmul := mul_le_mul_of_nonneg_right hcount' hm.le
    nlinarith only [hmul]
  have hexponent : -4 * (K : ℝ) * ((s - 1 : ℕ) : ℝ) ≤ -2 * (N : ℝ) * t := by
    nlinarith only [htotal]
  unfold ambientDeletionDelta
  exact (Real.exp_le_exp.mpr hexponent).trans
    (exp_neg_two_mul_le_one_sub_pow N ht0 ht)

theorem ambientDeletionDelta_le_finset_prod {ι : Type*} (I : Finset ι)
    (s K q : ℕ) (hs : 2 ≤ s) (hq : 0 < q) (hsmall : 2 * (s - 1) ^ 2 ≤ q)
    (hcount : I.card * (s - 1) ≤ 2 * K * q) (p : ι → ℝ)
    (hp : ∀ i ∈ I, p i ≤ ((s - 1 : ℕ) : ℝ) ^ 2 / (q : ℝ)) :
    ambientDeletionDelta s K ≤ ∏ i ∈ I, (1 - p i) := by
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hsmall' : (2 : ℝ) * ((s - 1 : ℕ) : ℝ) ^ 2 ≤ (q : ℝ) := by
    exact_mod_cast hsmall
  have hhalf : ((s - 1 : ℕ) : ℝ) ^ 2 / (q : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hq').2
    nlinarith only [hsmall']
  have hbase : 0 ≤ 1 - ((s - 1 : ℕ) : ℝ) ^ 2 / (q : ℝ) := by linarith
  apply (ambientDeletionDelta_le_pow s K q I.card hs hq hsmall hcount).trans
  calc
    (1 - ((s - 1 : ℕ) : ℝ) ^ 2 / (q : ℝ)) ^ I.card =
        ∏ _i ∈ I, (1 - ((s - 1 : ℕ) : ℝ) ^ 2 / (q : ℝ)) := by
      rw [Finset.prod_const]
    _ ≤ ∏ i ∈ I, (1 - p i) :=
      Finset.prod_le_prod (fun _ _ => hbase)
        (fun i hi => sub_le_sub_left (hp i hi) 1)

theorem ambientDeletionDelta_le_prod {ι : Type*} [Fintype ι]
    (s K q : ℕ) (hs : 2 ≤ s) (hq : 0 < q) (hsmall : 2 * (s - 1) ^ 2 ≤ q)
    (hcount : Fintype.card ι * (s - 1) ≤ 2 * K * q) (p : ι → ℝ)
    (hp : ∀ i, p i ≤ ((s - 1 : ℕ) : ℝ) ^ 2 / (q : ℝ)) :
    ambientDeletionDelta s K ≤ ∏ i, (1 - p i) := by
  classical
  apply ambientDeletionDelta_le_finset_prod Finset.univ s K q hs hq hsmall ?_ p ?_
  · simpa only [Finset.card_univ] using hcount
  · intro i _
    exact hp i

end RyserCoveringCounterexample.Construction

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_CoverPencil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Construction

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem card_linePoints_inter_le_one {l m : AffineLine F} (hlm : l ≠ m) :
    (linePoints l ∩ linePoints m).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  exact eq_of_common_incidence_of_ne_lines hlm
    ((mem_linePoints _ _).mp (Finset.mem_inter.mp hx).1)
    ((mem_linePoints _ _).mp (Finset.mem_inter.mp hx).2)
    ((mem_linePoints _ _).mp (Finset.mem_inter.mp hy).1)
    ((mem_linePoints _ _).mp (Finset.mem_inter.mp hy).2)

end RyserCoveringCounterexample.Construction

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

abbrev LineTuple (F : Type*) (t : ℕ) := (Fin t ⊕ Fin t) ↪ AffineLine F

def crossPoints {t : ℕ} (a : LineTuple F t) : Finset (Point F) :=
  Finset.univ.filter fun x =>
    ∃ i j, Incidence x (a (Sum.inl i)) ∧ Incidence x (a (Sum.inr j))

def tupleShapes {t : ℕ} (a : LineTuple F t) : Finset (Finset (Point F)) :=
  Finset.univ.image fun i => linePoints (a i)

def SparseShapes (shapes : Finset (Finset (Point F))) (D : ℕ) : Prop :=
  ∀ S ∈ shapes, ∀ l : AffineLine F, S ≠ linePoints l →
    (S ∩ linePoints l).card ≤ D

def coverPencil (L : Finset (AffineLine F)) (p : ProjectivePoint F) :
    Finset (AffineLine F) :=
  L.filter fun l => ProjectiveIncidence p (some l)

@[simp] theorem mem_crossPoints {t : ℕ} (a : LineTuple F t) (x : Point F) :
    x ∈ crossPoints a ↔
      ∃ i j, Incidence x (a (Sum.inl i)) ∧ Incidence x (a (Sum.inr j)) := by
  simp only [crossPoints, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem mem_tupleShapes {t : ℕ} (a : LineTuple F t)
    (S : Finset (Point F)) :
    S ∈ tupleShapes a ↔ ∃ i, linePoints (a i) = S := by
  simp only [tupleShapes, Finset.mem_image, Finset.mem_univ, true_and]

@[simp] theorem mem_coverPencil (L : Finset (AffineLine F))
    (p : ProjectivePoint F) (l : AffineLine F) :
    l ∈ coverPencil L p ↔ l ∈ L ∧ ProjectiveIncidence p (some l) := let _ := instFintypeF; by
  simp only [coverPencil, Finset.mem_filter]

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_DeletionDefinitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {P : Type*} [DecidableEq P]

abbrev Outcome (shapes : Finset (Finset P)) (D : ℕ) :=
  {A : Finset ↥shapes // A.card ≤ D}

def emptyOutcome (shapes : Finset (Finset P)) (D : ℕ) : Outcome shapes D :=
  ⟨∅, by simp⟩

variable {shapes : Finset (Finset P)} {D n : ℕ}

def deleted (ignore : Finset (Finset P)) (a : Outcome shapes D) : Finset P :=
  (a.val.filter (fun L => L.val ∉ ignore)).biUnion Subtype.val

@[simp] theorem mem_deleted {ignore : Finset (Finset P)}
    {a : Outcome shapes D} {x : P} :
    x ∈ deleted ignore a ↔ ∃ L ∈ a.val, L.val ∉ ignore ∧ x ∈ L.val := by
  simp [deleted, Finset.mem_biUnion, and_assoc]

@[simp] theorem deleted_emptyOutcome (ignore : Finset (Finset P)) :
    deleted ignore (emptyOutcome shapes D) = ∅ := by
  simp [deleted, emptyOutcome]

def selected (ω : Fin n → Outcome shapes D) : Finset (Finset P) :=
  Finset.univ.biUnion (fun i => (ω i).val.image Subtype.val)

@[simp] theorem mem_selected {ω : Fin n → Outcome shapes D} {L : Finset P} :
    L ∈ selected ω ↔ ∃ i, ∃ s ∈ (ω i).val, s.val = L := by
  simp [selected, Finset.mem_biUnion, Finset.mem_image]

variable [instFintypeP : Fintype P]

def survivors (ignore : Finset (Finset P))
    (ω : Fin n → Outcome shapes D) : Finset P :=
  Finset.univ \ Finset.univ.biUnion (fun i => deleted ignore (ω i))

@[simp] theorem mem_survivors {ignore : Finset (Finset P)}
    {ω : Fin n → Outcome shapes D} {x : P} :
    x ∈ survivors ignore ω ↔ ∀ i, x ∉ deleted ignore (ω i) := by
  simp [survivors, Finset.mem_biUnion]

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Probability_Product
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.FiniteLaw

section ProductCoordinates

variable {I : Type*} [Fintype I] [DecidableEq I]
  {A : I → Type*} [∀ i, Fintype (A i)]

theorem expectation_pi_product (μ : ∀ i, FiniteLaw (A i))
    (f : ∀ i, A i → ℝ) :
    (pi μ).expectation (fun ω => ∏ i, f i (ω i)) =
      ∏ i, (μ i).expectation (f i) := by
  classical
  simp only [expectation, pi_weight]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => (μ i).weight a * f i a)).symm

theorem prob_pi (μ : ∀ i, FiniteLaw (A i)) (P : ∀ i, A i → Prop) :
    (pi μ).prob (fun ω => ∀ i, P i (ω i)) = ∏ i, (μ i).prob (P i) := by
  classical
  rw [prob_eq_expectation]
  calc
    _ = (pi μ).expectation (fun ω => ∏ i, if P i (ω i) then 1 else 0) := by
      congr 1
      funext ω
      symm
      by_cases h : ∀ i, P i (ω i)
      · simpa only [ite_eq_left h] using
          (Fintype.prod_boole (p := fun i => P i (ω i)) (M₀ := ℝ))
      · simpa only [ite_eq_right h] using
          (Fintype.prod_boole (p := fun i => P i (ω i)) (M₀ := ℝ))
    _ = ∏ i, (μ i).expectation (fun a => if P i a then 1 else 0) :=
      expectation_pi_product μ (fun i a => if P i a then 1 else 0)
    _ = _ := by simp_rw [prob_eq_expectation]

end ProductCoordinates

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

def map (μ : FiniteLaw Ω) (f : Ω → Γ) : FiniteLaw Γ where
  weight γ := ∑ ω, if f ω = γ then μ.weight ω else 0
  nonneg γ := Finset.sum_nonneg fun ω _ => by
    split_ifs
    · exact μ.nonneg ω
    · exact le_rfl
  total := by
    rw [Finset.sum_comm]
    simpa using μ.total

@[simp] theorem map_weight (μ : FiniteLaw Ω) (f : Ω → Γ) (γ : Γ) :
    (map μ f).weight γ = ∑ ω, if f ω = γ then μ.weight ω else 0 := rfl

theorem expectation_map (μ : FiniteLaw Ω) (f : Ω → Γ) (g : Γ → ℝ) :
    (map μ f).expectation g = μ.expectation (fun ω => g (f ω)) := by
  unfold expectation
  simp only [map_weight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp [ite_mul]

theorem prob_map (μ : FiniteLaw Ω) (f : Ω → Γ) (P : Γ → Prop) :
    (map μ f).prob P = μ.prob (fun ω => P (f ω)) := by
  rw [prob_eq_expectation, expectation_map, prob_eq_expectation]

end RyserCoveringCounterexample.FiniteLaw

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

structure DeletionProcess (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (D : ℕ) (δ : ℝ) where
  shapes : Finset (Finset (Point F))
  shapeCount : shapes.card ≤ D * Fintype.card F ^ D
  shapeSize : ∀ S ∈ shapes, S.card ≤ D * Fintype.card F
  sparse : SparseShapes shapes D
  trialsCount : ℕ
  trials : Fin trialsCount → FiniteLaw (Outcome shapes D)
  trialsCount_le : trialsCount ≤ D * Fintype.card F
  pointCap : ∀ i x,
    (trials i).prob (fun a => x ∈ deleted ∅ a) ≤ (D : ℝ) / Fintype.card F
  survival : ℝ
  survivalLower : δ ≤ survival
  uniformSurvival : ∀ x,
    (FiniteLaw.pi trials).prob (fun ω => x ∈ survivors ∅ ω) = survival
  lineCap : ∀ l : AffineLine F,
    (∑ i, (trials i).prob (fun a => ∃ S ∈ a.val, S.val = linePoints l)) ≤
      (D : ℝ) / Fintype.card F

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {shapes : Finset (Finset (Point F))} {D n : ℕ}

def GoodLineCover (δ ρ : ℝ) (ω : Fin n → Outcome shapes D) : Prop :=
  (∀ l : AffineLine F,
    δ * Fintype.card F / 2 ≤
      ((survivors {linePoints l} ω ∩ linePoints l).card : ℝ)) ∧
  (∀ L : Finset (AffineLine F), L.card ≤ Fintype.card F →
    (survivors ∅ ω \ L.biUnion linePoints).card ≤ 2 * Fintype.card F →
    ∃ p : ProjectivePoint F,
      (1 - ρ) * Fintype.card F ≤ ((coverPencil L p).card : ℝ))

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_AmbientDeletionShapes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def ambientShapes (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    Finset (Finset (Point F)) := Finset.univ.image linePoints

theorem linePoints_mem_ambientShapes (l : AffineLine F) :
    linePoints l ∈ ambientShapes F := Finset.mem_image_of_mem _ (Finset.mem_univ l)

theorem ambient_linePoints_injective : Function.Injective (linePoints (F := F)) := by
  intro l m h
  by_contra hlm
  have hbound := card_linePoints_inter_le_one hlm
  rw [h, Finset.inter_self, card_linePoints] at hbound
  exact (Fintype.one_lt_card : 1 < Fintype.card F).not_ge hbound

theorem ambientShapes_count_le {D : ℕ} (hD : 2 ≤ D) :
    (ambientShapes F).card ≤ D * Fintype.card F ^ D := by
  have hq : 1 ≤ Fintype.card F := Nat.succ_le_of_lt Fintype.card_pos
  have hpow : Fintype.card F ^ 2 ≤ Fintype.card F ^ D :=
    pow_le_pow_right₀ hq hD
  calc
    (ambientShapes F).card ≤ Fintype.card (AffineLine F) :=
      (Finset.card_image_le).trans_eq (Finset.card_univ)
    _ = Fintype.card F * (Fintype.card F + 1) := card_affineLine
    _ ≤ 2 * Fintype.card F ^ 2 := by nlinarith
    _ ≤ D * Fintype.card F ^ D := Nat.mul_le_mul hD hpow

theorem ambientShapes_size_le {D : ℕ} (hD : 1 ≤ D)
    (S : Finset (Point F)) (hS : S ∈ ambientShapes F) :
    S.card ≤ D * Fintype.card F := by
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hS
  rw [card_linePoints]
  simpa only [one_mul] using Nat.mul_le_mul_right (Fintype.card F) hD

theorem ambientShapes_sparse {D : ℕ} (hD : 1 ≤ D) :
    LineCover.SparseShapes (ambientShapes F) D := by
  intro S hS l hne
  obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hS
  have hml : m ≠ l := fun h => hne (congrArg linePoints h)
  exact (card_linePoints_inter_le_one hml).trans hD

def ambientLineOutcome {D : ℕ} (B : Finset (AffineLine F)) (hB : B.card ≤ D) :
    LineCover.Outcome (ambientShapes F) D :=
  ⟨B.image (fun l => (⟨linePoints l, linePoints_mem_ambientShapes l⟩ :
      ↥(ambientShapes F))), Finset.card_image_le.trans hB⟩

theorem mem_deleted_ambientLineOutcome {D : ℕ} (B : Finset (AffineLine F))
    (hB : B.card ≤ D) (ignore : Finset (Finset (Point F))) (x : Point F) :
    x ∈ LineCover.deleted ignore (ambientLineOutcome B hB) ↔
      ∃ l ∈ B, linePoints l ∉ ignore ∧ Incidence x l := by
  rw [LineCover.mem_deleted]
  constructor
  · rintro ⟨S, hS, hignore, hx⟩
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hS
    exact ⟨l, hl, hignore, (mem_linePoints x l).mp hx⟩
  · rintro ⟨l, hl, hignore, hx⟩
    exact ⟨⟨linePoints l, linePoints_mem_ambientShapes l⟩,
      Finset.mem_image_of_mem _ hl, hignore, (mem_linePoints x l).mpr hx⟩

theorem ambientLineOutcome_lists_line {D : ℕ} (B : Finset (AffineLine F))
    (hB : B.card ≤ D) (l : AffineLine F) :
    (∃ S ∈ (ambientLineOutcome B hB).val, S.val = linePoints l) ↔ l ∈ B := by
  constructor
  · rintro ⟨S, hS, heq⟩
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hS
    exact ambient_linePoints_injective heq ▸ hm
  · intro hl
    exact ⟨⟨linePoints l, linePoints_mem_ambientShapes l⟩,
      Finset.mem_image_of_mem _ hl, rfl⟩

theorem deleted_empty_ambientLineOutcome {D : ℕ} (B : Finset (AffineLine F))
    (hB : B.card ≤ D) :
    LineCover.deleted ∅ (ambientLineOutcome B hB) = B.biUnion linePoints := by
  ext x
  simp only [mem_deleted_ambientLineOutcome, Finset.notMem_empty, not_false_eq_true, true_and,
    Finset.mem_biUnion, mem_linePoints]

def ambientDeletionConstant (s K : ℕ) : ℕ :=
  2 + (s - 1) ^ 2 + 2 * K + 2 * K * (s - 1)

theorem ambientDeletionConstant_two_le (s K : ℕ) :
    2 ≤ ambientDeletionConstant s K := by
  unfold ambientDeletionConstant
  omega

theorem ambientDeletionConstant_lines_le (s K : ℕ) :
    (s - 1) ^ 2 ≤ ambientDeletionConstant s K := by
  unfold ambientDeletionConstant
  omega

theorem ambientDeletionConstant_trials_le (s K : ℕ) :
    2 * K ≤ ambientDeletionConstant s K := by
  unfold ambientDeletionConstant
  omega

theorem ambientDeletionConstant_lineRate_le (s K : ℕ) :
    2 * K * (s - 1) ≤ ambientDeletionConstant s K := by
  unfold ambientDeletionConstant
  omega

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_CosetIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]

def embeddedUnits (σ : k →+* F) : kˣ →* Fˣ := Units.map σ.toMonoidHom

theorem embeddedUnits_injective (σ : k →+* F) : Function.Injective (embeddedUnits σ) :=
  Units.map_injective σ.injective

def smallUnitSubgroup (σ : k →+* F) : Subgroup Fˣ := (embeddedUnits σ).range

abbrev CosetIndex (σ : k →+* F) := Fˣ ⧸ smallUnitSubgroup σ

def unitCoset (σ : k →+* F) (a : Fˣ) : CosetIndex σ := QuotientGroup.mk a

def cosetRepresentative (σ : k →+* F) (c : CosetIndex σ) : Fˣ := by
  classical
  exact if c = 1 then 1 else c.out

@[simp] theorem cosetRepresentative_one (σ : k →+* F) :
    cosetRepresentative σ 1 = 1 := by
  classical
  simp [cosetRepresentative]

@[simp] theorem unitCoset_representative (σ : k →+* F) (c : CosetIndex σ) :
    unitCoset σ (cosetRepresentative σ c) = c := by
  classical
  by_cases hc : c = 1
  · subst c
    simp [cosetRepresentative, unitCoset]
  · simp only [cosetRepresentative, ite_eq_right hc, unitCoset]
    exact Quotient.out_eq' c

theorem unitCoset_eq_iff (σ : k →+* F) (a b : Fˣ) :
    unitCoset σ a = unitCoset σ b ↔
      ∃ u : kˣ, embeddedUnits σ u = a / b := by
  change (a : Fˣ ⧸ smallUnitSubgroup σ) = b ↔ _
  rw [QuotientGroup.eq_iff_div_mem]
  rfl

theorem exists_embeddedUnit_mul_representative (σ : k →+* F) (a : Fˣ) :
    ∃ u : kˣ, a = embeddedUnits σ u * cosetRepresentative σ (unitCoset σ a) := by
  have hc : unitCoset σ a =
      unitCoset σ (cosetRepresentative σ (unitCoset σ a)) := by simp
  obtain ⟨u, hu⟩ := (unitCoset_eq_iff σ _ _).mp hc
  refine ⟨u, ?_⟩
  rw [hu, div_mul_cancel]

abbrev ConfigurationGroup (σ : k →+* F) := Option (CosetIndex σ)

theorem natCard_smallUnitSubgroup (σ : k →+* F) :
    Nat.card (smallUnitSubgroup σ) = Nat.card k - 1 := by
  calc
    Nat.card (smallUnitSubgroup σ) = Nat.card kˣ :=
      (Nat.card_congr (MonoidHom.ofInjective (embeddedUnits_injective σ)).toEquiv).symm
    _ = Nat.card k - 1 := Nat.card_units k

theorem natCard_cosetIndex_mul (σ : k →+* F) :
    Nat.card (CosetIndex σ) * (Nat.card k - 1) = Nat.card F - 1 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (smallUnitSubgroup σ)
  rw [Nat.card_units, natCard_smallUnitSubgroup] at h
  exact h.symm

section Finite

variable [instFintypek : Fintype k] [Fintype F]

instance instFintypeCosetIndex (σ : k →+* F) : Fintype (CosetIndex σ) := Fintype.ofFinite _

theorem card_cosetIndex_mul (σ : k →+* F) :
    Fintype.card (CosetIndex σ) * (Fintype.card k - 1) = Fintype.card F - 1 := by
  simpa only [Nat.card_eq_fintype_card] using natCard_cosetIndex_mul σ

theorem card_configurationGroup (σ : k →+* F) :
    Fintype.card (ConfigurationGroup σ) = Fintype.card (CosetIndex σ) + 1 := let _ := instFintypek;
  Fintype.card_option

end Finite

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_CosetDirections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]
variable [instDecidableEqk : DecidableEq k] [instDecidableEqF : DecidableEq F] [instFintypek : Fintype k]

def cosetPlacement (σ : k →+* F) (c : CosetIndex σ) : PlaneLinearMap F :=
  PlaneLinearMap.diagonal (cosetRepresentative σ c : F)
    (cosetRepresentative σ c).ne_zero

@[simp] theorem placedDirection_coset_none (σ : k →+* F) (c : CosetIndex σ) :
    placedDirection σ (cosetPlacement σ c) none = none := let _ := instDecidableEqk; let _ := instFintypek; by
  simp [placedDirection, mapDirection, cosetPlacement]

@[simp] theorem placedDirection_coset_some (σ : k →+* F) (c : CosetIndex σ)
    (t : k) :
    placedDirection σ (cosetPlacement σ c) (some t) =
      some ((cosetRepresentative σ c : F) * σ t) := let _ := instDecidableEqk; let _ := instFintypek; by
  simp [placedDirection, mapDirection, cosetPlacement]

theorem mem_coset_altered_iff (σ : k →+* F) (c : CosetIndex σ)
    (d : Direction F) :
    d ∈ alteredDirections σ (cosetPlacement σ c) ↔
      ∃ t : k, t ≠ 0 ∧ d = some ((cosetRepresentative σ c : F) * σ t) := by
  rw [mem_alteredDirections_iff]
  simp only [placedDirection_coset_some, eq_comm]

@[simp] theorem none_notMem_coset_altered (σ : k →+* F) (c : CosetIndex σ) :
    none ∉ alteredDirections σ (cosetPlacement σ c) := by
  simp [mem_coset_altered_iff]

@[simp] theorem zero_notMem_coset_altered (σ : k →+* F) (c : CosetIndex σ) :
    some 0 ∉ alteredDirections σ (cosetPlacement σ c) := by
  rintro hd
  obtain ⟨t, ht, heq⟩ := (mem_coset_altered_iff σ c _).mp hd
  have hz := Option.some.inj heq
  exact mul_ne_zero (cosetRepresentative σ c).ne_zero
    (fun hz' => ht (σ.injective (hz'.trans (map_zero σ).symm))) hz.symm

theorem unitCoset_mul_embedded (σ : k →+* F) (a : Fˣ) (u : kˣ) :
    unitCoset σ (a * embeddedUnits σ u) = unitCoset σ a := let _ := instDecidableEqk; let _ := instDecidableEqF; let _ := instFintypek; by
  apply (unitCoset_eq_iff σ _ _).mpr
  refine ⟨u, ?_⟩
  simp only [mul_div_cancel_left]

theorem some_unit_mem_coset_altered_iff (σ : k →+* F) (c : CosetIndex σ)
    (a : Fˣ) :
    some (a : F) ∈ alteredDirections σ (cosetPlacement σ c) ↔
      unitCoset σ a = c := by
  constructor
  · intro ha
    obtain ⟨t, ht, heq⟩ := (mem_coset_altered_iff σ c _).mp ha
    have hu : a = cosetRepresentative σ c * embeddedUnits σ (Units.mk0 t ht) := by
      apply Units.ext
      simpa [embeddedUnits] using Option.some.inj heq
    rw [hu, unitCoset_mul_embedded, unitCoset_representative]
  · intro ha
    obtain ⟨u, hu⟩ := exists_embeddedUnit_mul_representative σ a
    apply (mem_coset_altered_iff σ c _).mpr
    refine ⟨(u : k), u.ne_zero, ?_⟩
    apply congrArg Option.some
    have hv := congrArg (fun z : Fˣ => (z : F)) hu
    simpa [embeddedUnits, ha, mul_comm] using hv

theorem coset_altered_index_eq (σ : k →+* F) {c e : CosetIndex σ}
    {d : Direction F}
    (hc : d ∈ alteredDirections σ (cosetPlacement σ c))
    (he : d ∈ alteredDirections σ (cosetPlacement σ e)) : c = e := by
  obtain ⟨t, ht, rfl⟩ := (mem_coset_altered_iff σ c d).mp hc
  let a : Fˣ := cosetRepresentative σ c * embeddedUnits σ (Units.mk0 t ht)
  have hc' : unitCoset σ a = c := by
    simp only [a, unitCoset_mul_embedded, unitCoset_representative]
  have he' : unitCoset σ a = e := by
    apply (some_unit_mem_coset_altered_iff σ e a).mp
    simpa [a, embeddedUnits] using he
  exact hc'.symm.trans he'

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_ExtraDirections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F] [DecidableEq k] [DecidableEq F]

namespace PlaneLinearMap

theorem directionMap_bijective [Fintype F] (M : PlaneLinearMap F) :
    Function.Bijective M.directionMap :=
  M.directionMap_injective.bijective_of_finite

end PlaneLinearMap

theorem extra_placedDirection (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (d : Direction k) :
    placedDirection σ (PlaneLinearMap.extra (σ u) (σ v) (σ.injective.ne huv)) d =
      mapDirection σ ((PlaneLinearMap.extra u v huv).directionMap d) := by
  cases d with
  | none =>
      simp [placedDirection, mapDirection]
  | some t =>
      have hzero : 1 + σ t = 0 ↔ 1 + t = 0 := by
        constructor
        · intro h
          apply σ.injective
          simpa only [map_add, map_one, map_zero] using h
        · intro h
          simpa only [map_add, map_one, map_zero] using congrArg σ h
      by_cases ht : 1 + t = 0
      · have hF := hzero.mpr ht
        simp [placedDirection, mapDirection, PlaneLinearMap.directionMap,
          PlaneLinearMap.extra, ht, hF]
      · have hF : 1 + σ t ≠ 0 := fun h => ht (hzero.mp h)
        simp [placedDirection, mapDirection, PlaneLinearMap.directionMap,
          PlaneLinearMap.extra, ht, hF, map_div₀, map_add, map_mul]

variable [instFintypek : Fintype k]

theorem extra_allDirections_image (σ : k →+* F) (u v : k) (huv : u ≠ v) :
    (Finset.univ.image
      (placedDirection σ (PlaneLinearMap.extra (σ u) (σ v) (σ.injective.ne huv)))) =
      Finset.univ.image (mapDirection σ) := by
  ext d
  constructor
  · intro hd
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hd
    exact Finset.mem_image.mpr
      ⟨(PlaneLinearMap.extra u v huv).directionMap e, Finset.mem_univ _,
        (extra_placedDirection σ u v huv e).symm⟩
  · intro hd
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨a, ha⟩ := (PlaneLinearMap.extra u v huv).directionMap_bijective.surjective e
    refine Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ?_⟩
    rw [extra_placedDirection σ u v huv a, ha]

theorem extra_axisDirections (σ : k →+* F) (u v : k) (huv : u ≠ v) :
    axisDirections σ (PlaneLinearMap.extra (σ u) (σ v) (σ.injective.ne huv)) =
      {some (σ u), some (σ v)} := let _ := instFintypek; by
  simp [axisDirections, placedDirection, mapDirection, Finset.pair_comm]

theorem alteredDirections_eq_allDirections_sdiff_axisDirections
    (σ : k →+* F) (M : PlaneLinearMap F) :
    alteredDirections σ M =
      (Finset.univ.image (placedDirection σ M)) \ axisDirections σ M := by
  ext d
  constructor
  · intro hd
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · obtain ⟨t, _, rfl⟩ := (mem_alteredDirections_iff σ M d).mp hd
      exact Finset.mem_image.mpr ⟨some t, Finset.mem_univ _, rfl⟩
    · intro ha
      exact Finset.disjoint_left.mp (disjoint_alteredDirections_axisDirections σ M) hd ha
  · intro hd
    obtain ⟨hf, hn⟩ := Finset.mem_sdiff.mp hd
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hf
    rcases Finset.mem_union.mp (placedDirection_mem_altered_or_axis σ M a) with ha | ha
    · exact ha
    · exact False.elim (hn ha)

theorem extra_alteredDirections (σ : k →+* F) (u v : k) (huv : u ≠ v) :
    alteredDirections σ (PlaneLinearMap.extra (σ u) (σ v) (σ.injective.ne huv)) =
      (Finset.univ.image (mapDirection σ)) \ {some (σ u), some (σ v)} := by
  rw [alteredDirections_eq_allDirections_sdiff_axisDirections,
    extra_allDirections_image σ u v huv, extra_axisDirections σ u v huv]

end RyserCoveringCounterexample.Construction

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_GroupPlacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [Fintype k]

def embeddedDirections (σ : k →+* F) : Finset (Direction F) :=
  Finset.univ.image (mapDirection σ)

def groupPlacement (σ : k →+* F) (u v : k) (huv : u ≠ v) :
    ConfigurationGroup σ → PlaneLinearMap F
  | none => PlaneLinearMap.extra (σ u) (σ v) (σ.injective.ne huv)
  | some c => cosetPlacement σ c

def groupAltered (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (i : ConfigurationGroup σ) : Finset (Direction F) :=
  alteredDirections σ (groupPlacement σ u v huv i)

def groupAxes (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (i : ConfigurationGroup σ) : Finset (Direction F) :=
  axisDirections σ (groupPlacement σ u v huv i)

def groupConflict (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (i : ConfigurationGroup σ) : Finset (Direction F) := by
  classical
  exact match i with
  | none => embeddedDirections σ
  | some c => if c = 1 then embeddedDirections σ else groupAltered σ u v huv (some c)

theorem coset_altered_embedded_index (σ : k →+* F) {c : CosetIndex σ}
    {d : Direction F} (hc : d ∈ alteredDirections σ (cosetPlacement σ c))
    (hd : d ∈ embeddedDirections σ) : c = 1 := by
  obtain ⟨e, _, he⟩ := Finset.mem_image.mp hd
  cases e with
  | none =>
      have he' : d = none := he.symm
      subst d
      exact (none_notMem_coset_altered σ c hc).elim
  | some t =>
      have he' : d = some (σ t) := he.symm
      subst d
      have ht : t ≠ 0 := by
        intro ht
        subst t
        exact zero_notMem_coset_altered σ c (by simp [mapDirection] at hc)
      have h1 : some (σ t) ∈ alteredDirections σ (cosetPlacement σ 1) := by
        apply (mem_coset_altered_iff σ 1 _).mpr
        exact ⟨t, ht, by simp⟩
      exact coset_altered_index_eq σ hc h1

theorem identity_altered_subset_embedded (σ : k →+* F) :
    alteredDirections σ (cosetPlacement σ 1) ⊆ embeddedDirections σ := by
  intro d hd
  obtain ⟨t, ht, rfl⟩ := (mem_coset_altered_iff σ 1 d).mp hd
  apply Finset.mem_image.mpr
  exact ⟨some t, Finset.mem_univ _, by simp [mapDirection]⟩

theorem groupAltered_subset_conflict (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (i : ConfigurationGroup σ) : groupAltered σ u v huv i ⊆ groupConflict σ u v huv i := by
  classical
  cases i with
  | none =>
      intro d hd
      change d ∈ embeddedDirections σ
      change d ∈ alteredDirections σ
        (PlaneLinearMap.extra (σ u) (σ v) (σ.injective.ne huv)) at hd
      rw [extra_alteredDirections σ u v huv] at hd
      exact (Finset.mem_sdiff.mp hd).1
  | some c =>
      by_cases hc : c = 1
      · subst c
        simpa [groupConflict, groupAltered, groupPlacement] using
          identity_altered_subset_embedded σ
      · simp only [groupConflict, ite_eq_right hc]
        exact Finset.Subset.refl _

theorem shared_groupConflict (σ : k →+* F) (u v : k) (huv : u ≠ v)
    {i j : ConfigurationGroup σ} {d : Direction F} (hij : i ≠ j)
    (hi : d ∈ groupConflict σ u v huv i)
    (hj : d ∈ groupConflict σ u v huv j) :
    (i = none ∧ j = some 1) ∨ (i = some 1 ∧ j = none) := by
  classical
  cases i with
  | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some c =>
          have hc : c = 1 := by
            by_contra hc
            have hj' : d ∈ alteredDirections σ (cosetPlacement σ c) := by
              simpa [groupConflict, hc, groupAltered, groupPlacement] using hj
            exact hc (coset_altered_embedded_index σ hj' hi)
          exact Or.inl ⟨rfl, congrArg some hc⟩
  | some c =>
      cases j with
      | none =>
          have hc : c = 1 := by
            by_contra hc
            have hi' : d ∈ alteredDirections σ (cosetPlacement σ c) := by
              simpa [groupConflict, hc, groupAltered, groupPlacement] using hi
            exact hc (coset_altered_embedded_index σ hi' hj)
          exact Or.inr ⟨congrArg some hc, rfl⟩
      | some e =>
          have hce : c ≠ e := fun h => hij (congrArg some h)
          by_cases hc : c = 1
          · subst c
            have he : e ≠ 1 := Ne.symm hce
            have hj' : d ∈ alteredDirections σ (cosetPlacement σ e) := by
              simpa [groupConflict, he, groupAltered, groupPlacement] using hj
            have hi' : d ∈ embeddedDirections σ := by simpa [groupConflict] using hi
            exact (he (coset_altered_embedded_index σ hj' hi')).elim
          · have hi' : d ∈ alteredDirections σ (cosetPlacement σ c) := by
              simpa [groupConflict, hc, groupAltered, groupPlacement] using hi
            by_cases he : e = 1
            · subst e
              have hj' : d ∈ embeddedDirections σ := by simpa [groupConflict] using hj
              exact (hc (coset_altered_embedded_index σ hi' hj')).elim
            · have hj' : d ∈ alteredDirections σ (cosetPlacement σ e) := by
                simpa [groupConflict, he, groupAltered, groupPlacement] using hj
              exact (hce (coset_altered_index_eq σ hi' hj')).elim

section FiniteAmbient

variable [Fintype F]

theorem groupConflict_multiplicity_le_two (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (d : Direction F) :
    (Finset.univ.filter (fun i => d ∈ groupConflict σ u v huv i)).card ≤ 2 := by
  classical
  let I := Finset.univ.filter (fun i => d ∈ groupConflict σ u v huv i)
  by_cases hsingle : ∀ i ∈ I, ∀ j ∈ I, i = j
  · have hcard : I.card ≤ 1 := Finset.card_le_one.mpr hsingle
    exact hcard.trans (by decide)
  · push Not at hsingle
    obtain ⟨i, hi, j, hj, hij⟩ := hsingle
    have hsub : I ⊆ ({none, some 1} : Finset (ConfigurationGroup σ)) := by
      intro a ha
      by_cases hai : a = i
      · subst a
        rcases shared_groupConflict σ u v huv hij (Finset.mem_filter.mp hi).2
          (Finset.mem_filter.mp hj).2 with h | h
        · simp [h.1]
        · simp [h.1]
      · rcases shared_groupConflict σ u v huv hai (Finset.mem_filter.mp ha).2
          (Finset.mem_filter.mp hi).2 with h | h
        · simp [h.1]
        · simp [h.1]
    exact (Finset.card_le_card hsub).trans Finset.card_le_two

theorem groupAltered_multiplicity_le_two (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (d : Direction F) :
    (Finset.univ.filter (fun i => d ∈ groupAltered σ u v huv i)).card ≤ 2 := by
  apply (Finset.card_le_card ?_).trans (groupConflict_multiplicity_le_two σ u v huv d)
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    groupAltered_subset_conflict σ u v huv i (Finset.mem_filter.mp hi).2⟩

end FiniteAmbient

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_GroupBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]
variable [instDecidableEqk : DecidableEq k] [instDecidableEqF : DecidableEq F] [Fintype k]

def groupPoints (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (i : ConfigurationGroup σ) : Finset (Point F) :=
  Finset.univ.image (fun w : Point k => (groupPlacement σ u v huv i).apply (mapPoint σ w))

section FiniteAmbient

variable [Fintype F]

theorem card_groups_mul_sub_one_le (σ : k →+* F) :
    Fintype.card (ConfigurationGroup σ) * (Fintype.card k - 1) ≤
      2 * Fintype.card F := let _ := instDecidableEqk; let _ := instDecidableEqF; by
  have hcard : Fintype.card k ≤ Fintype.card F :=
    Fintype.card_le_of_injective σ σ.injective
  rw [card_configurationGroup, Nat.add_mul, card_cosetIndex_mul, one_mul]
  omega

end FiniteAmbient

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_AmbientDeletionTrials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F] [Fintype k] [Fintype F]
  [DecidableEq k] [DecidableEq F]

def ambientTrialOutcome (σ : k →+* F) (M : PlaneLinearMap F)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) (b : Point F) :
    LineCover.Outcome (ambientShapes F) (ambientDeletionConstant (Fintype.card k) K) :=
  ambientLineOutcome (deletedLines σ M b a) (by
    rw [card_deletedLines σ M b a ha]
    exact ambientDeletionConstant_lines_le _ _)

def ambientTrialLaw (σ : k →+* F) (M : PlaneLinearMap F)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) :
    FiniteLaw (LineCover.Outcome (ambientShapes F)
      (ambientDeletionConstant (Fintype.card k) K)) :=
  (FiniteLaw.uniform (Point F)).map (ambientTrialOutcome σ M a ha K)

def ambientPointRate (σ : k →+* F) (M : PlaneLinearMap F) (a : GadgetOutcome k) : ℝ :=
  ((ambientLineUnion (deletedLines σ M 0 a)).card : ℝ) / (Fintype.card F : ℝ) ^ 2

theorem ambientTrialLaw_point_probability (σ : k →+* F) (M : PlaneLinearMap F)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) (x : Point F) :
    (ambientTrialLaw σ M a ha K).prob (fun A => x ∈ LineCover.deleted ∅ A) =
      ambientPointRate σ M a := by
  rw [ambientTrialLaw, FiniteLaw.prob_map]
  simp only [ambientTrialOutcome, deleted_empty_ambientLineOutcome]
  exact uniform_prob_mem_deletedLines_union σ M a x

theorem ambientPointRate_le (σ : k →+* F) (M : PlaneLinearMap F)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) :
    ambientPointRate σ M a ≤ ((Fintype.card k - 1 : ℕ) : ℝ) ^ 2 / Fintype.card F := by
  have h := uniform_prob_mem_deletedLines_union_le σ M a (0 : Point F)
  rw [uniform_prob_mem_deletedLines_union, card_deletedLines σ M 0 a ha,
    Nat.cast_pow] at h
  exact h

theorem ambientTrialLaw_line_probability_le (σ : k →+* F) (M : PlaneLinearMap F)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) (l : AffineLine F) :
    (ambientTrialLaw σ M a ha K).prob (fun A => ∃ S ∈ A.val, S.val = linePoints l) ≤
      if l.1 ∈ alteredDirections σ M then
        ((Fintype.card k - 1 : ℕ) : ℝ) / Fintype.card F else 0 := by
  rw [ambientTrialLaw, FiniteLaw.prob_map]
  simp only [ambientTrialOutcome, ambientLineOutcome_lists_line]
  have h := uniform_prob_mem_deletedLines_le σ M a l
  by_cases hd : l.1 ∈ alteredDirections σ M
  · rw [ite_eq_left hd]
    rw [card_deletedLines_of_mem_alteredDirections σ M 0 a ha l.1 hd] at h
    exact h
  · rw [ite_eq_right hd]
    have hempty : ((deletedLines σ M 0 a).filter (fun e => e.1 = l.1)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨he, hdir⟩ := Finset.mem_filter.mp he
      have hedir := ((mem_deletedLines σ M 0 a e).mp he).1
      exact hd (hdir ▸ hedir)
    simpa only [hempty, Finset.card_empty, Nat.cast_zero, zero_div] using h

abbrev AmbientPosition (σ : k →+* F) (K : ℕ) := ConfigurationGroup σ × Fin K

def ambientTrialCount (σ : k →+* F) (K : ℕ) : ℕ := Fintype.card (AmbientPosition σ K)

def ambientPosition (σ : k →+* F) (K : ℕ) (t : Fin (ambientTrialCount σ K)) :
    AmbientPosition σ K := (Fintype.equivFin (AmbientPosition σ K)).symm t

def ambientTrials (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ)
    (t : Fin (ambientTrialCount σ K)) :
    FiniteLaw (LineCover.Outcome (ambientShapes F)
      (ambientDeletionConstant (Fintype.card k) K)) :=
  ambientTrialLaw σ (groupPlacement σ u v huv (ambientPosition σ K t).1) a ha K

theorem ambientTrialCount_mul_sub_one_le (σ : k →+* F) (K : ℕ) :
    ambientTrialCount σ K * (Fintype.card k - 1) ≤ 2 * K * Fintype.card F := by
  unfold ambientTrialCount AmbientPosition
  rw [Fintype.card_prod, Fintype.card_fin]
  calc
    Fintype.card (ConfigurationGroup σ) * K * (Fintype.card k - 1) =
        K * (Fintype.card (ConfigurationGroup σ) * (Fintype.card k - 1)) := by ring
    _ ≤ K * (2 * Fintype.card F) :=
      Nat.mul_le_mul_left K (card_groups_mul_sub_one_le σ)
    _ = 2 * K * Fintype.card F := by ring

theorem ambientTrialCount_le (σ : k →+* F) (K : ℕ) (hs : 2 ≤ Fintype.card k) :
    ambientTrialCount σ K ≤ ambientDeletionConstant (Fintype.card k) K * Fintype.card F := by
  have hs' : 1 ≤ Fintype.card k - 1 := by omega
  calc
    ambientTrialCount σ K = ambientTrialCount σ K * 1 := by rw [Nat.mul_one]
    _ ≤ ambientTrialCount σ K * (Fintype.card k - 1) := Nat.mul_le_mul_left _ hs'
    _ ≤ 2 * K * Fintype.card F := ambientTrialCount_mul_sub_one_le σ K
    _ ≤ ambientDeletionConstant (Fintype.card k) K * Fintype.card F :=
      Nat.mul_le_mul_right _ (ambientDeletionConstant_trials_le _ _)

theorem ambientTrials_line_probability_sum_le (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) (l : AffineLine F) :
    (∑ t, (ambientTrials σ u v huv a ha K t).prob
      (fun A => ∃ S ∈ A.val, S.val = linePoints l)) ≤
      (2 : ℝ) * K * ((Fintype.card k - 1 : ℕ) : ℝ) / Fintype.card F := by
  let rate : ℝ := ((Fintype.card k - 1 : ℕ) : ℝ) / Fintype.card F
  have hrate : 0 ≤ rate := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hsum : (∑ i : ConfigurationGroup σ,
      if l.1 ∈ groupAltered σ u v huv i then rate else 0) ≤ 2 * rate := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hmult : ((Finset.univ.filter
        (fun i => l.1 ∈ groupAltered σ u v huv i)).card : ℝ) ≤ 2 := by
      exact_mod_cast groupAltered_multiplicity_le_two σ u v huv l.1
    exact mul_le_mul_of_nonneg_right hmult hrate
  calc
    _ = ∑ p : AmbientPosition σ K,
        (ambientTrialLaw σ (groupPlacement σ u v huv p.1) a ha K).prob
          (fun A => ∃ S ∈ A.val, S.val = linePoints l) :=
      Equiv.sum_comp (Fintype.equivFin (AmbientPosition σ K)).symm _
    _ ≤ ∑ i : ConfigurationGroup σ, ∑ _j : Fin K,
        if l.1 ∈ groupAltered σ u v huv i then rate else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact ambientTrialLaw_line_probability_le σ (groupPlacement σ u v huv i) a ha K l
    _ = (K : ℝ) * ∑ i : ConfigurationGroup σ,
        if l.1 ∈ groupAltered σ u v huv i then rate else 0 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Finset.mul_sum]
    _ ≤ (K : ℝ) * (2 * rate) := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ = (2 : ℝ) * K * ((Fintype.card k - 1 : ℕ) : ℝ) / Fintype.card F := by
      dsimp only [rate]
      ring

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_AmbientDeletionProcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F] [Fintype k] [Fintype F]
  [DecidableEq k] [DecidableEq F]

def ambientSurvival (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (K : ℕ) : ℝ :=
  ∏ t : Fin (ambientTrialCount σ K),
    (1 - ambientPointRate σ (groupPlacement σ u v huv (ambientPosition σ K t).1) a)

theorem ambientTrials_uniformSurvival (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) (x : Point F) :
    (FiniteLaw.pi (ambientTrials σ u v huv a ha K)).prob
      (fun ω => x ∈ LineCover.survivors ∅ ω) = ambientSurvival σ u v huv a K := by
  simp only [LineCover.mem_survivors]
  rw [FiniteLaw.prob_pi (ambientTrials σ u v huv a ha K)
    (fun _ A => x ∉ LineCover.deleted ∅ A)]
  simp_rw [FiniteLaw.prob_compl]
  simp only [ambientTrials, ambientTrialLaw_point_probability, ambientSurvival]

theorem ambientSurvival_lower (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ)
    (hs : 2 ≤ Fintype.card k)
    (hsmall : 2 * (Fintype.card k - 1) ^ 2 ≤ Fintype.card F) :
    ambientDeletionDelta (Fintype.card k) K ≤ ambientSurvival σ u v huv a K := by
  apply ambientDeletionDelta_le_prod (Fintype.card k) K (Fintype.card F) hs
    Fintype.card_pos hsmall ?_ _ ?_
  · simpa only [Fintype.card_fin] using ambientTrialCount_mul_sub_one_le σ K
  · intro t
    exact ambientPointRate_le σ (groupPlacement σ u v huv (ambientPosition σ K t).1) a ha

def ambientDeletionProcess (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ)
    (hs : 2 ≤ Fintype.card k)
    (hsmall : 2 * (Fintype.card k - 1) ^ 2 ≤ Fintype.card F) :
    LineCover.DeletionProcess F (ambientDeletionConstant (Fintype.card k) K)
      (ambientDeletionDelta (Fintype.card k) K) where
  shapes := ambientShapes F
  shapeCount := ambientShapes_count_le (ambientDeletionConstant_two_le _ _)
  shapeSize := ambientShapes_size_le (le_trans (by decide) (ambientDeletionConstant_two_le _ _))
  sparse := ambientShapes_sparse (le_trans (by decide) (ambientDeletionConstant_two_le _ _))
  trialsCount := ambientTrialCount σ K
  trials := ambientTrials σ u v huv a ha K
  trialsCount_le := ambientTrialCount_le σ K hs
  pointCap := by
    intro t x
    rw [ambientTrials, ambientTrialLaw_point_probability]
    apply (ambientPointRate_le σ
      (groupPlacement σ u v huv (ambientPosition σ K t).1) a ha).trans
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast ambientDeletionConstant_lines_le (Fintype.card k) K
  survival := ambientSurvival σ u v huv a K
  survivalLower := ambientSurvival_lower σ u v huv a ha K hs hsmall
  uniformSurvival := ambientTrials_uniformSurvival σ u v huv a ha K
  lineCap := by
    intro l
    apply (ambientTrials_line_probability_sum_le σ u v huv a ha K l).trans
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast ambientDeletionConstant_lineRate_le (Fintype.card k) K

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_PoolThinGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F] [Fintype F] [instDecidableEqF : DecidableEq F]

def ShiftHits (W : Finset (Point F)) (S : Finset (Direction F))
    (p : Point F) (ell : AffineLine F) (b : Point F) : Prop :=
  ∃ w ∈ W, ∃ d ∈ S, Incidence (b + w) ell ∧
    projection d (b + w) = projection d p

def badShifts (W : Finset (Point F)) (S : Finset (Direction F))
    (p : Point F) (ell : AffineLine F) : Finset (Point F) := by
  classical
  exact Finset.univ.filter (ShiftHits W S p ell)

@[simp] theorem mem_badShifts (W : Finset (Point F)) (S : Finset (Direction F))
    (p : Point F) (ell : AffineLine F) (b : Point F) :
    b ∈ badShifts W S p ell ↔ ShiftHits W S p ell b := let _ := instDecidableEqF; by
  classical
  simp only [badShifts, Finset.mem_filter, Finset.mem_univ, true_and]

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_PoolThinProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def poolThinLaw (G : Type*) [Fintype G] [DecidableEq G] (K : ℕ) :
    FiniteLaw (G → Fin K → Point F) :=
  FiniteLaw.pi (fun _ : G => FiniteLaw.uniform (Fin K → Point F))

def poolGroupBad {K : ℕ} (W : Finset (Point F)) (S : Finset (Direction F))
    (p : Point F) (ell : AffineLine F) (a : Fin K → Point F) : Prop :=
  ∃ j, ShiftHits W S p ell (a j)

variable {G : Type*} [Fintype G] [DecidableEq G] {K : ℕ}

def poolBadGroups (W : G → Finset (Point F)) (S : G → Finset (Direction F))
    (p : Point F) (ell : AffineLine F) (ω : G → Fin K → Point F) : Finset G :=
  Finset.univ.filter (fun i => poolGroupBad (W i) (S i) p ell (ω i))

def PoolThin (W : G → Finset (Point F)) (S : G → Finset (Direction F))
    (ω : G → Fin K → Point F) : Prop :=
  ∀ p ell, ¬ Incidence p ell → (poolBadGroups W S p ell ω).card ≤ 5

end RyserCoveringCounterexample.Construction

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

variable {F n K}

abbrev ExposedAssignment (T : Finset (Position n K)) :=
  {e : Position n K // e ∈ T} → Point F

abbrev FreshAssignment (T : Finset (Position n K)) :=
  {e : Position n K // e ∉ T} → Point F

def joinAssignments (T : Finset (Position n K))
    (x : ExposedAssignment (F := F) T) (y : FreshAssignment (F := F) T) :
    Pool F n K :=
  (Equiv.piEquivPiSubtypeProd (fun e : Position n K => e ∈ T)
    (fun _ => Point F)).symm (x, y)

@[simp] theorem joinAssignments_exposed (T : Finset (Position n K))
    (x : ExposedAssignment (F := let _ := instFieldF; let _ := instFintypeF; let _ := instDecidableEqF; F) T) (y : FreshAssignment (F := F) T)
    (e : {e : Position n K // e ∈ T}) : joinAssignments T x y e.val = x e := by
  simp [joinAssignments, Equiv.piEquivPiSubtypeProd, e.property]

@[simp] theorem joinAssignments_fresh (T : Finset (Position n K))
    (x : ExposedAssignment (F := let _ := instFieldF; let _ := instFintypeF; let _ := instDecidableEqF; F) T) (y : FreshAssignment (F := F) T)
    (e : {e : Position n K // e ∉ T}) : joinAssignments T x y e.val = y e := by
  simp [joinAssignments, Equiv.piEquivPiSubtypeProd, e.property]

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_AmbientDeletionPoolLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F] [instFintypeK : Fintype k] [Fintype F]
  [instDecidableEqK : DecidableEq k] [DecidableEq F]

abbrev AmbientPool (σ : k →+* F) (K : ℕ) := ConfigurationGroup σ → Fin K → Point F

def ambientPoolTrialEquiv (σ : k →+* F) (K : ℕ) :
    AmbientPool σ K ≃ (Fin (ambientTrialCount σ K) → Point F) where
  toFun b t := b (ambientPosition σ K t).1 (ambientPosition σ K t).2
  invFun b i j := b ((Fintype.equivFin (AmbientPosition σ K)) (i, j))
  left_inv b := by
    funext i j
    simp only [ambientPosition, Equiv.symm_apply_apply]
  right_inv b := by
    funext t
    change b ((Fintype.equivFin (AmbientPosition σ K))
      ((Fintype.equivFin (AmbientPosition σ K)).symm t)) = b t
    exact congrArg b ((Fintype.equivFin (AmbientPosition σ K)).apply_symm_apply t)

def ambientFlatPoolEquiv (σ : k →+* F) (K : ℕ) :
    AmbientPool σ K ≃ Selection.Pool F (Fintype.card (ConfigurationGroup σ)) K where
  toFun b p := b ((Fintype.equivFin (ConfigurationGroup σ)).symm p.1) p.2
  invFun b i j := b ((Fintype.equivFin (ConfigurationGroup σ)) i, j)
  left_inv b := by
    funext i j
    simp only [Equiv.symm_apply_apply]
  right_inv b := by
    funext p
    simp only [Equiv.apply_symm_apply, Prod.mk.eta]

def ambientPoolConfig (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) (b : AmbientPool σ K) :
    Fin (ambientTrialCount σ K) →
      LineCover.Outcome (ambientShapes F) (ambientDeletionConstant (Fintype.card k) K) :=
  fun t => ambientTrialOutcome σ
    (groupPlacement σ u v huv (ambientPosition σ K t).1) a ha K
    (b (ambientPosition σ K t).1 (ambientPosition σ K t).2)

@[simp] theorem ambientPoolConfig_at (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) (b : AmbientPool σ K)
    (i : ConfigurationGroup σ) (j : Fin K) :
    ambientPoolConfig σ u v huv a ha K b
        ((Fintype.equivFin (AmbientPosition σ K)) (i, j)) =
      ambientTrialOutcome σ (groupPlacement σ u v huv i) a ha K (b i j) := by
  simp only [ambientPoolConfig, ambientPosition, Equiv.symm_apply_apply]

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_PlacementIntersection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F] [DecidableEq k] [DecidableEq F]

theorem mem_range_placedPoint_of_incident_of_ne_placedLines
    (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    {p : Point F} {l m : AffineLine k}
    (hlm : placedLine σ M b l ≠ placedLine σ M b m)
    (hpl : Incidence p (placedLine σ M b l))
    (hpm : Incidence p (placedLine σ M b m)) :
    p ∈ Set.range (placedPoint σ M b) := by
  have hdir : l.1 ≠ m.1 := by
    intro hsame
    have hplaced : (placedLine σ M b l).1 = (placedLine σ M b m).1 := by
      simpa only [placedLine_direction] using congrArg (placedDirection σ M) hsame
    exact hlm (line_eq_of_direction_eq_of_incidence
      (l := placedLine σ M b l) (m := placedLine σ M b m) (p := p)
      hplaced hpl hpm)
  obtain ⟨q, hq, _⟩ := existsUnique_incident_of_ne_direction l m hdir
  have hql : Incidence (placedPoint σ M b q) (placedLine σ M b l) :=
    (incidence_placedLine_iff σ M b q l).2 hq.1
  have hqm : Incidence (placedPoint σ M b q) (placedLine σ M b m) :=
    (incidence_placedLine_iff σ M b q m).2 hq.2
  have hpq : p = placedPoint σ M b q :=
    eq_of_common_incidence_of_ne_lines hlm hpl hpm hql hqm
  exact ⟨q, hpq.symm⟩

theorem eq_placedLine_of_incident_of_notMem_range
    (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    {p : Point F} {l m : AffineLine k}
    (houtside : p ∉ Set.range (placedPoint σ M b))
    (hpl : Incidence p (placedLine σ M b l))
    (hpm : Incidence p (placedLine σ M b m)) :
    placedLine σ M b l = placedLine σ M b m := by
  by_contra hlm
  exact houtside (mem_range_placedPoint_of_incident_of_ne_placedLines σ M b hlm hpl hpm)

end RyserCoveringCounterexample.Construction

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_DeletionIntersection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]
variable [Fintype k] [instFintypeF : Fintype F] [instDecidableEqk : DecidableEq k] [DecidableEq F]

def placedSubplane (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F) :
    Finset (Point F) := Finset.univ.image (placedPoint σ M b)

@[simp] theorem mem_placedSubplane_iff (σ : k →+* F) (M : PlaneLinearMap F)
    (b p : Point F) : p ∈ placedSubplane σ M b ↔ p ∈ Set.range (placedPoint σ M b) := let _ := instFintypeF; let _ := instDecidableEqk; by
  simp only [placedSubplane, Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range]

theorem exists_placedLine_of_mem_deletedLines (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (a : GadgetOutcome k) {ell : AffineLine F}
    (hell : ell ∈ deletedLines σ M b a) :
    ∃ l : AffineLine k, placedLine σ M b l = ell := by
  have hmem : ell.1 ∈ alteredDirections σ M ∧
      ∃ y ∈ retainedPoints a, Incidence (placedPoint σ M b y) ell := by
    simpa only [deletedLines, Finset.mem_filter, Finset.mem_univ, true_and] using hell
  obtain ⟨t, _, ht⟩ := (mem_alteredDirections_iff σ M ell.1).mp hmem.1
  obtain ⟨y, _, hy⟩ := hmem.2
  refine ⟨(some t, projection (some t) y), ?_⟩
  exact (eq_placedLine_of_direction_of_incidence σ M b y (some t) ell ht.symm hy).symm

theorem eq_deletedLine_of_incident_of_notMem_placedSubplane
    (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F) (a : GadgetOutcome k)
    {p : Point F} {ell m : AffineLine F}
    (houtside : p ∉ placedSubplane σ M b)
    (hell : ell ∈ deletedLines σ M b a) (hm : m ∈ deletedLines σ M b a)
    (hpell : Incidence p ell) (hpm : Incidence p m) : ell = m := by
  have hout : p ∉ Set.range (placedPoint σ M b) := by
    simpa only [mem_placedSubplane_iff] using houtside
  obtain ⟨l, rfl⟩ := exists_placedLine_of_mem_deletedLines σ M b a hell
  obtain ⟨l', rfl⟩ := exists_placedLine_of_mem_deletedLines σ M b a hm
  exact eq_placedLine_of_incident_of_notMem_range σ M b hout hpell hpm

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_DeletionUnionBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {G k F : Type*} [Field k] [Field F]
variable [instFintypeG : Fintype G] [Fintype k] [Fintype F]
variable [instDecidableEqG : DecidableEq G] [DecidableEq k] [DecidableEq F]

def DeletionSeparated (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) : Prop :=
  ∀ i j : G, i ≠ j → ∀ p ∈ placedSubplane σ (M i) (b i),
    ∀ y ∈ (retainedPoints a).image (placedPoint σ (M j) (b j)),
      ∀ d ∈ alteredDirections σ (M j), projection d p ≠ projection d y

def allDeletedLines (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) : Finset (AffineLine F) :=
  Finset.univ.biUnion (fun i => deletedLines σ (M i) (b i) a)

def deletedPencil (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (p : Point F) : Finset (AffineLine F) :=
  (allDeletedLines σ M b a).filter (fun ell => Incidence p ell)

def activeDeletionGroups (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (p : Point F) : Finset G :=
  Finset.univ.filter (fun i => ∃ ell ∈ deletedLines σ (M i) (b i) a, Incidence p ell)

@[simp] theorem mem_allDeletedLines (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (ell : AffineLine F) :
    ell ∈ allDeletedLines σ M b a ↔ ∃ i, ell ∈ deletedLines σ (M i) (b i) a := let _ := instDecidableEqG; by
  simp only [allDeletedLines, Finset.mem_biUnion, Finset.mem_univ, true_and]

@[simp] theorem mem_deletedPencil (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (p : Point F) (ell : AffineLine F) :
    ell ∈ deletedPencil σ M b a p ↔
      ell ∈ allDeletedLines σ M b a ∧ Incidence p ell := let _ := instDecidableEqG; by
  simp only [deletedPencil, Finset.mem_filter]

@[simp] theorem mem_activeDeletionGroups (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (p : Point F) (i : G) :
    i ∈ activeDeletionGroups σ M b a p ↔
      ∃ ell ∈ deletedLines σ (M i) (b i) a, Incidence p ell := let _ := instDecidableEqG; by
  simp only [activeDeletionGroups, Finset.mem_filter, Finset.mem_univ, true_and]

theorem not_incidence_deletedLines_of_mem_other_subplane
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F) (a : GadgetOutcome k)
    (hsep : DeletionSeparated σ M b a) {i j : G} (hij : i ≠ j)
    {p : Point F} (hp : p ∈ placedSubplane σ (M i) (b i))
    {ell : AffineLine F} (hell : ell ∈ deletedLines σ (M j) (b j) a) :
    ¬Incidence p ell := let _ := instFintypeG; let _ := instDecidableEqG; by
  obtain ⟨hdir, y, hy, hyell⟩ := (mem_deletedLines σ (M j) (b j) a ell).mp hell
  have hyplaced : placedPoint σ (M j) (b j) y ∈
      (retainedPoints a).image (placedPoint σ (M j) (b j)) :=
    Finset.mem_image.mpr ⟨y, hy, rfl⟩
  intro hpell
  exact hsep i j hij p hp (placedPoint σ (M j) (b j) y) hyplaced ell.1 hdir
    (hpell.trans hyell.symm)

theorem disjoint_deletedLines_of_separated
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F) (a : GadgetOutcome k)
    (hsep : DeletionSeparated σ M b a) {i j : G} (hij : i ≠ j) :
    Disjoint (deletedLines σ (M i) (b i) a) (deletedLines σ (M j) (b j) a) := by
  apply Finset.disjoint_left.mpr
  intro ell helli hellj
  obtain ⟨y, _, hyell⟩ := ((mem_deletedLines σ (M i) (b i) a ell).mp helli).2
  have hyplane : placedPoint σ (M i) (b i) y ∈ placedSubplane σ (M i) (b i) :=
    (mem_placedSubplane_iff σ (M i) (b i) _).mpr ⟨y, rfl⟩
  exact not_incidence_deletedLines_of_mem_other_subplane
    σ M b a hsep hij hyplane hellj hyell

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_AmbientDeletionSurvivors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F] [Fintype k] [Fintype F]
  [DecidableEq k] [DecidableEq F]

def ambientSelectedLines (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (K : ℕ) (b : AmbientPool σ K)
    (choice : ConfigurationGroup σ → Fin K) : Finset (AffineLine F) :=
  allDeletedLines σ (groupPlacement σ u v huv) (fun i => b i (choice i)) a

@[simp] theorem mem_ambientSelectedLines (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (K : ℕ) (b : AmbientPool σ K)
    (choice : ConfigurationGroup σ → Fin K) (l : AffineLine F) :
    l ∈ ambientSelectedLines σ u v huv a K b choice ↔
      ∃ i, l ∈ deletedLines σ (groupPlacement σ u v huv i) (b i (choice i)) a :=
  mem_allDeletedLines σ (groupPlacement σ u v huv) (fun i => b i (choice i)) a l

def ambientSelectedSurvivors (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (K : ℕ) (b : AmbientPool σ K)
    (choice : ConfigurationGroup σ → Fin K) : Finset (Point F) :=
  Finset.univ \ (ambientSelectedLines σ u v huv a K b choice).biUnion linePoints

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_GroupSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [Fintype k] [Fintype F]

def groupSelectionData (σ : k →+* F) (u v : k) (huv : u ≠ v) :
    Selection.Data F (Fintype.card (ConfigurationGroup σ)) where
  W i := groupPoints σ u v huv ((Fintype.equivFin (ConfigurationGroup σ)).symm i)
  dirs i := groupConflict σ u v huv ((Fintype.equivFin (ConfigurationGroup σ)).symm i)

@[simp] theorem groupSelectionData_W_equivFin (σ : k →+* F)
    (u v : k) (huv : u ≠ v) (i : ConfigurationGroup σ) :
    (groupSelectionData σ u v huv).W ((Fintype.equivFin (ConfigurationGroup σ)) i) =
      groupPoints σ u v huv i := by
  simp only [groupSelectionData, Equiv.symm_apply_apply]

@[simp] theorem groupSelectionData_dirs_equivFin (σ : k →+* F)
    (u v : k) (huv : u ≠ v) (i : ConfigurationGroup σ) :
    (groupSelectionData σ u v huv).dirs ((Fintype.equivFin (ConfigurationGroup σ)) i) =
      groupConflict σ u v huv i := by
  simp only [groupSelectionData, Equiv.symm_apply_apply]

def groupSelectionConstant (s : ℕ) : ℕ := s ^ 2 + s + 2

def selectedShifts (σ : k →+* F) {K : ℕ}
    (pool : Selection.Pool F (Fintype.card (ConfigurationGroup σ)) K)
    (choice : Fin (Fintype.card (ConfigurationGroup σ)) → Fin K)
    (i : ConfigurationGroup σ) : Point F :=
  pool ((Fintype.equivFin (ConfigurationGroup σ)) i,
    choice ((Fintype.equivFin (ConfigurationGroup σ)) i))

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_PoolThinAsymptotic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology
open scoped Classical
noncomputable section

namespace RyserCoveringCounterexample.Construction

def thinFailureConstant (s K : ℕ) : ℝ := 128 * (K : ℝ) ^ 6 * (s : ℝ) ^ 12

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Probability_Exposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Exposure

open scoped BigOperators

variable {Omega : Type*} [instFintypeOmega : Fintype Omega]

def splitConfig (n : Nat) :
    (Fin (n + 1) → Omega) ≃ Omega × (Fin n → Omega) where
  toFun w := (w 0, fun i => w i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv w := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv p := by
    rcases p with ⟨x, tail⟩
    rfl

def headMean {n : Nat} (mu : Fin (n + 1) → FiniteLaw Omega)
    (f : (Fin (n + 1) → Omega) → ℝ) (x : Omega) : ℝ :=
  (FiniteLaw.pi (fun i : Fin n => mu i.succ)).expectation
    (fun tail => f (Fin.cons x tail))

def ExposureBounds (M : ℝ) : (n : Nat) →
    (Fin n → FiniteLaw Omega) → ((Fin n → Omega) → ℝ) →
    (Fin n → ℝ) → Prop
  | 0, _, _, _ => True
  | n + 1, mu, f, v =>
      (∀ x, |headMean mu f x - (mu 0).expectation (headMean mu f)| ≤ M) ∧
      (mu 0).expectation
        (fun x => (headMean mu f x - (mu 0).expectation (headMean mu f)) ^ 2)
        ≤ v 0 ∧
      ∀ x, ExposureBounds M n (fun i => mu i.succ)
        (fun tail => f (Fin.cons x tail)) (fun i => v i.succ)

end RyserCoveringCounterexample.Exposure

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Geometry_ProjectiveTransformBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample

structure ProjectiveTransform (F : Type*) [Field F] where
  points : ProjectivePoint F ≃ ProjectivePoint F
  lines : ProjectiveLine F ≃ ProjectiveLine F
  incidence : ∀ p l, ProjectiveIncidence (points p) (lines l) ↔ ProjectiveIncidence p l

namespace ProjectiveTransform

variable {F : Type*} [Field F]

def refl (F : Type*) [Field F] : ProjectiveTransform F where
  points := Equiv.refl _
  lines := Equiv.refl _
  incidence _ _ := Iff.rfl

def trans (T U : ProjectiveTransform F) : ProjectiveTransform F where
  points := T.points.trans U.points
  lines := T.lines.trans U.lines
  incidence p l := (U.incidence (T.points p) (T.lines l)).trans (T.incidence p l)

@[simp] theorem refl_points (p : ProjectivePoint F) : (refl F).points p = p := rfl

@[simp] theorem refl_lines (l : ProjectiveLine F) : (refl F).lines l = l := rfl

@[simp] theorem trans_points (T U : ProjectiveTransform F) (p : ProjectivePoint F) :
    (T.trans U).points p = U.points (T.points p) := rfl

@[simp] theorem trans_lines (T U : ProjectiveTransform F) (l : ProjectiveLine F) :
    (T.trans U).lines l = U.lines (T.lines l) := rfl

end ProjectiveTransform

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_CoordinateTransferSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Incidence

variable {F : Type*} [Field F] [instDecidableEqF : DecidableEq F]

def goodW (T : ProjectiveTransform F) (W : Finset (ProjectivePoint F)) :
    Finset (ProjectivePoint F) :=
  W.filter fun w =>
    ¬ ProjectiveIncidence w (T.lines.symm none) ∧
    ¬ ProjectiveIncidence w (T.lines.symm (some (some 0, 0))) ∧
    ¬ ProjectiveIncidence w (T.lines.symm (some (none, 0)))

def affinePart : ProjectivePoint F → Point F
  | Sum.inl z => z
  | Sum.inr _ => (0, 0)

@[simp] theorem affinePart_inl (z : Point F) :
    affinePart (Sum.inl z : ProjectivePoint F) = z := let _ := instDecidableEqF; rfl

@[simp] theorem affinePart_inr (d : Direction F) :
    affinePart (Sum.inr d : ProjectivePoint F) = (0, 0) := let _ := instDecidableEqF; rfl

def coordinateGraph (T : ProjectiveTransform F) (W : Finset (ProjectivePoint F)) :
    Finset (Point F) :=
  (goodW T W).image fun w => affinePart (T.points w)

@[simp] theorem mem_goodW (T : ProjectiveTransform F)
    (W : Finset (ProjectivePoint F)) (w : ProjectivePoint F) :
    w ∈ goodW T W ↔ w ∈ W ∧
      ¬ ProjectiveIncidence w (T.lines.symm none) ∧
      ¬ ProjectiveIncidence w (T.lines.symm (some (some 0, 0))) ∧
      ¬ ProjectiveIncidence w (T.lines.symm (some (none, 0))) := by
  exact Finset.mem_filter

end RyserCoveringCounterexample.Incidence

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

def HasJoin (L : Finset (ProjectiveLine F)) (p : ProjectivePoint F) (z : Point F) : Prop :=
  ∃ l ∈ L, ProjectiveIncidence p l ∧ ProjectiveIncidence (Sum.inl z) l

end
end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_FiniteSetEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

public section

namespace RyserCoveringCounterexample.Incidence.FiniteSetEstimates

open Finset Nat
open scoped Pointwise

variable {G : Type*} [DecidableEq G]

section Group
variable [Group G] {A B C : Finset G}

@[to_additive                                                             ]
theorem ruzsa_triangle_inequality_div_div_div (A B C : Finset G) :
    #(A / C) * #B ≤ #(A / B) * #(C / B) := by
  exact Finset.ruzsa_triangle_inequality_div_div_div A B C

@[to_additive                                                             ]
theorem ruzsa_triangle_inequality_div_mul_mul (A B C : Finset G) :
    #(A / C) * #B ≤ #(A * B) * #(C * B) := by
  exact Finset.ruzsa_triangle_inequality_div_mul_mul A B C

@[to_additive]
theorem pluennecke_petridis_inequality_mul (C : Finset G)
    (hA : ∀ A' ⊆ A, #(A * B) * #A' ≤ #(A' * B) * #A) :
    #(C * A * B) * #A ≤ #(A * B) * #(C * A) := by
  exact Finset.pluennecke_petridis_inequality_mul C hA

end Group

variable [CommGroup G] {A B C : Finset G}

@[to_additive
                                                                                        ]
theorem pluennecke_ruzsa_inequality_pow_div_pow_mul (hA : A.Nonempty) (B : Finset G) (m n : ℕ) :
    #(B ^ m / B ^ n) ≤ (#(A * B) / #A : ℚ≥0) ^ (m + n) * #A := by
  exact Finset.pluennecke_ruzsa_inequality_pow_div_pow_mul hA B m n

@[to_additive                                                                ]
theorem pluennecke_ruzsa_inequality_pow_div_pow_div (hA : A.Nonempty) (B : Finset G) (m n : ℕ) :
    #(B ^ m / B ^ n) ≤ (#(A / B) / #A : ℚ≥0) ^ (m + n) * #A := by
  exact Finset.pluennecke_ruzsa_inequality_pow_div_pow_div hA B m n

end RyserCoveringCounterexample.Incidence.FiniteSetEstimates

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

def ratioSet (E : Finset F) : Finset F :=
  ((E - E) ×ˢ ((E - E).erase 0)).image (fun z => z.1 / z.2)

def dilateSum (E : Finset F) (c : F) : Finset F :=
  E + E.image (fun x => c * x)

theorem mem_dilateSum {E : Finset F} {c z : F} :
    z ∈ dilateSum E c ↔ ∃ x ∈ E, ∃ y ∈ E, x + c * y = z := by
  constructor
  · intro hz
    obtain ⟨x, hx, w, hw, hzw⟩ := Finset.mem_add.mp hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
    exact ⟨x, hx, y, hy, hzw⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact Finset.mem_add.mpr ⟨x, hx, c * y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, rfl⟩

theorem mem_ratioSet {E : Finset F} {c : F} :
    c ∈ ratioSet E ↔ ∃ x ∈ E, ∃ x' ∈ E, ∃ y ∈ E, ∃ y' ∈ E,
      y ≠ y' ∧ (x - x') / (y - y') = c := by
  constructor
  · intro hc
    obtain ⟨⟨u, v⟩, huv, huv_eq⟩ := Finset.mem_image.mp hc
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
    obtain ⟨hv0, hv⟩ := Finset.mem_erase.mp hv
    obtain ⟨x, hx, x', hx', rfl⟩ := Finset.mem_sub.mp hu
    obtain ⟨y, hy, y', hy', rfl⟩ := Finset.mem_sub.mp hv
    exact ⟨x, hx, x', hx', y, hy, y', hy', sub_ne_zero.mp hv0, huv_eq⟩
  · rintro ⟨x, hx, x', hx', y, hy, y', hy', hyy', hquot⟩
    apply Finset.mem_image.mpr
    refine ⟨(x - x', y - y'), Finset.mem_product.mpr ⟨?_, ?_⟩, hquot⟩
    · exact Finset.mem_sub.mpr ⟨x, hx, x', hx', rfl⟩
    · exact Finset.mem_erase.mpr ⟨sub_ne_zero.mpr hyy',
        Finset.mem_sub.mpr ⟨y, hy, y', hy', rfl⟩⟩

theorem zero_mem_ratioSet {E : Finset F} (hE : 2 ≤ E.card) :
    (0 : F) ∈ ratioSet E := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hE
  exact mem_ratioSet.mpr ⟨x, hx, x, hx, x, hx, y, hy, hxy, by simp⟩

theorem inv_mem_ratioSet {E : Finset F} {c : F}
    (hE : 2 ≤ E.card) (hc : c ∈ ratioSet E) : c⁻¹ ∈ ratioSet E := by
  by_cases hc0 : c = 0
  · simpa only [hc0, inv_zero] using zero_mem_ratioSet hE
  obtain ⟨x, hx, x', hx', y, hy, y', hy', hyy', hquot⟩ := mem_ratioSet.mp hc
  have hxx' : x ≠ x' := by
    intro h
    apply hc0
    simpa only [h, sub_self, zero_div] using hquot.symm
  exact mem_ratioSet.mpr ⟨y, hy, y', hy', x, hx, x', hx', hxx',
    by simpa only [inv_div] using congrArg Inv.inv hquot⟩

end
end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_ScalarCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Incidence

open scoped Pointwise

variable {F : Type*} [Field F] [DecidableEq F]

def ScalarCovered (B : Finset F) (K : ℝ) (c : F) (a : ℕ) : Prop :=
  ∃ T : Finset F, (T.card : ℝ) ≤ K ^ a ∧ c • B ⊆ T + (B - B)

end RyserCoveringCounterexample.Incidence

end

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

inductive ScalarExpression (E : Finset F) : F → ℕ → Prop
  | seed {c : F} (hc : c ∈ E ∨ c = 0 ∨ c = 1) :
      ScalarExpression E c 0
  | neg {c : F} {m : ℕ} (h : ScalarExpression E c m) :
      ScalarExpression E (-c) (m + 1)
  | add {c d : F} {m n : ℕ}
      (hc : ScalarExpression E c m) (hd : ScalarExpression E d n) :
      ScalarExpression E (c + d) (m + n + 1)
  | sub {c d : F} {m n : ℕ}
      (hc : ScalarExpression E c m) (hd : ScalarExpression E d n) :
      ScalarExpression E (c - d) (m + n + 1)
  | mul {c d : F} {m n : ℕ}
      (hc : ScalarExpression E c m) (hd : ScalarExpression E d n) :
      ScalarExpression E (c * d) (m + n + 1)
  | inv {c : F} {m : ℕ}
      (h : ScalarExpression E c m) (hc : c ≠ 0) :
      ScalarExpression E c⁻¹ (m + 1)

end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_FourAnchorsCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace RyserCoveringCounterexample.Incidence
attribute [local instance] Classical.propDecidable

variable {Pt Ln : Type*} [DecidableEq Pt] [instDecidableEqLn : DecidableEq Ln]

def orderedTriples (P : Finset Pt) : Finset (Σ _ : Pt, Σ _ : Pt, Pt) :=
  P.sigma fun a => (P.erase a).sigma fun b => (P.erase a).erase b

@[simp] theorem mem_orderedTriples {P : Finset Pt} {t : Σ _ : Pt, Σ _ : Pt, Pt} :
    t ∈ orderedTriples P ↔ t.1 ∈ P ∧ t.2.1 ∈ P ∧ t.2.2 ∈ P ∧
      t.2.1 ≠ t.1 ∧ t.2.2 ≠ t.1 ∧ t.2.2 ≠ t.2.1 := by
  simp only [orderedTriples, Finset.mem_sigma, Finset.mem_erase]
  simp only [and_assoc, and_left_comm, and_comm]

def joinedNeighbors (R : Pt → Ln → Prop) (P : Finset Pt) (L : Finset Ln)
    (x : Pt) : Finset Pt := by
  classical
  exact P.filter fun p => x ≠ p ∧ ∃ l ∈ L, R x l ∧ R p l

def anchorConfigurations (R : Pt → Ln → Prop) (P : Finset Pt) (L : Finset Ln) :
    Finset (Σ _ : Ln, (Σ _ : Pt, Σ _ : Pt, Pt) × Pt) := by
  classical
  exact L.sigma fun l =>
    orderedTriples (P.filter fun p => R p l) ×ˢ (P.filter fun p => ¬ R p l)

def anchorWitnesses (R : Pt → Ln → Prop) (P : Finset Pt) (L : Finset Ln)
    (c : Σ _ : Ln, (Σ _ : Pt, Σ _ : Pt, Pt) × Pt) : Finset Pt := by
  classical
  exact P.filter fun x =>
    c.2.1.1 ∈ joinedNeighbors R P L x ∧
    c.2.1.2.1 ∈ joinedNeighbors R P L x ∧
    c.2.1.2.2 ∈ joinedNeighbors R P L x ∧
    c.2.2 ∈ joinedNeighbors R P L x

@[simp] theorem mem_anchorConfigurations (R : Pt → Ln → Prop)
    (P : Finset Pt) (L : Finset Ln)
    (c : Σ _ : Ln, (Σ _ : Pt, Σ _ : Pt, Pt) × Pt) :
    c ∈ anchorConfigurations R P L ↔ c.1 ∈ L ∧
      c.2.1.1 ∈ P ∧ c.2.1.2.1 ∈ P ∧ c.2.1.2.2 ∈ P ∧ c.2.2 ∈ P ∧
      R c.2.1.1 c.1 ∧ R c.2.1.2.1 c.1 ∧ R c.2.1.2.2 c.1 ∧ ¬ R c.2.2 c.1 ∧
      c.2.1.2.1 ≠ c.2.1.1 ∧ c.2.1.2.2 ≠ c.2.1.1 ∧
      c.2.1.2.2 ≠ c.2.1.2.1 := let _ := instDecidableEqLn; by
  classical
  simp only [anchorConfigurations, Finset.mem_sigma, Finset.mem_product,
    mem_orderedTriples, Finset.mem_filter]
  simp only [and_assoc, and_left_comm, and_comm]

end RyserCoveringCounterexample.Incidence

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_Parameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Incidence
noncomputable section
open Filter Topology

def savingExponent : ℝ := 1 / 10000000000
def witnessConstant : ℝ := 1 / (9 * 2 ^ 57)
def graphScaleConstant : ℝ := 9 * 2 ^ 58
def densityScale (q : ℝ) : ℝ := q ^ savingExponent
def graphScale (U : ℝ) : ℝ := graphScaleConstant * U ^ 39
def expansionScale (V : ℝ) : ℝ := 2 ^ 23 * V ^ 24

@[simp] theorem savingExponent_pos : 0 < savingExponent := by
  norm_num [savingExponent]

theorem scaled_power_identity (A U : ℝ) (a b c : ℕ) :
    A * U ^ a * (graphScale U) ^ b * (expansionScale (graphScale U)) ^ c =
      (A * graphScaleConstant ^ b * (2 ^ 23 * graphScaleConstant ^ 24) ^ c) *
        U ^ (a + 39 * b + 936 * c) := by
  simp only [graphScale, expansionScale, mul_pow, pow_add, pow_mul]
  rw [show (936 : ℕ) = 39 * 24 from rfl, pow_mul]
  ring

theorem eventually_coefficient_density_power_lt_sqrt
    (A : ℝ) (m : ℕ) (hm : savingExponent * m < 1 / 2) :
    ∀ᶠ q : ℝ in atTop, A * densityScale q ^ m < Real.sqrt q := by
  have hgap : 0 < (1 / 2 : ℝ) - savingExponent * m := sub_pos.mpr hm
  have hgrow := (tendsto_rpow_atTop hgap).eventually_gt_atTop A
  filter_upwards [eventually_gt_atTop (0 : ℝ), hgrow] with q hq hbound
  have hpow : 0 < q ^ (savingExponent * m) := Real.rpow_pos_of_pos hq _
  have hmul := mul_lt_mul_of_pos_right hbound hpow
  have hid : q ^ ((1 / 2 : ℝ) - savingExponent * m) *
      q ^ (savingExponent * m) = Real.sqrt q := by
    rw [← Real.rpow_add hq, sub_add_cancel, Real.sqrt_eq_rpow]
  rw [hid] at hmul
  simpa only [densityScale, Real.rpow_mul_natCast hq.le] using hmul

theorem eventually_scaled_powers_lt_sqrt (A : ℝ) (a b c : ℕ)
    (hExp : savingExponent * (a + 39 * b + 936 * c : ℕ) < 1 / 2) :
    ∀ᶠ q : ℝ in atTop,
      A * densityScale q ^ a * (graphScale (densityScale q)) ^ b *
        (expansionScale (graphScale (densityScale q))) ^ c < Real.sqrt q := by
  have h := eventually_coefficient_density_power_lt_sqrt
    (A * graphScaleConstant ^ b * (2 ^ 23 * graphScaleConstant ^ 24) ^ c)
    (a + 39 * b + 936 * c) hExp
  filter_upwards [h] with q hq
  simpa only [scaled_power_identity] using hq

def LargeEnough (q : ℝ) : Prop :=
  let U := densityScale q
  let V := graphScale U
  let K := expansionScale V
  0 < q ∧ 2 ≤ U ∧
    16 * U ^ 2 ≤ Real.sqrt q ∧
    4096 * U ^ 7 ≤ Real.sqrt q ∧
    (96 / witnessConstant) * U ^ 42 ≤ Real.sqrt q ∧
    32 * V ^ 2 * K ^ 127942 < 3 * Real.sqrt q ∧
    4096 * V ^ 6 * K ^ 3 < 27 * Real.sqrt q ∧
    2 * K ^ 527 * V ≤ Real.sqrt q

theorem eventually_largeEnough : ∀ᶠ q : ℝ in atTop, LargeEnough q := by
  have hU := (tendsto_rpow_atTop savingExponent_pos).eventually_ge_atTop 2
  have h2 := eventually_scaled_powers_lt_sqrt 16 2 0 0 (by norm_num [savingExponent])
  have h7 := eventually_scaled_powers_lt_sqrt 4096 7 0 0 (by norm_num [savingExponent])
  have h42 := eventually_scaled_powers_lt_sqrt (96 / witnessConstant) 42 0 0
    (by norm_num [savingExponent])
  have hfirst := eventually_scaled_powers_lt_sqrt (32 / 3) 0 2 127942
    (by norm_num [savingExponent])
  have hsecond := eventually_scaled_powers_lt_sqrt (4096 / 27) 0 6 3
    (by norm_num [savingExponent])
  have hthird := eventually_scaled_powers_lt_sqrt 2 0 1 527
    (by norm_num [savingExponent])
  filter_upwards [eventually_gt_atTop (0 : ℝ), hU, h2, h7, h42,
    hfirst, hsecond, hthird] with q hq hu h2q h7q h42q hf hs ht
  simp only [pow_zero, pow_one, mul_one] at h2q h7q h42q hf hs ht
  refine ⟨hq, hu, h2q.le, h7q.le, h42q.le, ?_, ?_, ?_⟩
  · nlinarith only [hf]
  · nlinarith only [hs]
  · have heq : 2 * expansionScale (graphScale (densityScale q)) ^ 527 *
        graphScale (densityScale q) =
      2 * graphScale (densityScale q) * expansionScale (graphScale (densityScale q)) ^ 527 := by
        ring
    rw [heq]
    exact ht.le

theorem exists_threshold_largeEnough :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → LargeEnough (q : ℝ) := by
  have h : ∀ᶠ q : ℕ in atTop, LargeEnough (q : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually eventually_largeEnough
  exact eventually_atTop.mp h

def incidenceThreshold : ℕ := Classical.choose exists_threshold_largeEnough

end
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

def commonNeighbors (B : Finset β) (G : Finset (α × β)) (a a' : α) : Finset β :=
  B.filter fun b => (a, b) ∈ G ∧ (a', b) ∈ G

def fourWalks (A : Finset α) (B : Finset β) (G : Finset (α × β)) (a a' : α) :
    Finset (Σ _ : α, β × β) :=
  A.sigma fun a₂ => commonNeighbors B G a a₂ ×ˢ commonNeighbors B G a₂ a'

@[simp] theorem mem_commonNeighbors (B : Finset β) (G : Finset (α × β))
    (a a' : α) (b : β) :
    b ∈ commonNeighbors B G a a' ↔ b ∈ B ∧ (a, b) ∈ G ∧ (a', b) ∈ G := by
  simp only [commonNeighbors, Finset.mem_filter]

@[simp] theorem mem_fourWalks (A : Finset α) (B : Finset β) (G : Finset (α × β))
    (a a' : α) (w : Σ _ : α, β × β) :
    w ∈ fourWalks A B G a a' ↔
      w.1 ∈ A ∧ w.2.1 ∈ commonNeighbors B G a w.1 ∧
        w.2.2 ∈ commonNeighbors B G w.1 a' := by
  simp only [fourWalks, Finset.mem_sigma, Finset.mem_product]

noncomputable section
attribute [local instance] Classical.propDecidable

def badPairs (A : Finset α) (B : Finset β) (G : Finset (α × β)) (t : ℝ) :
    Finset (α × α) :=
  (A ×ˢ A).filter fun p => ((commonNeighbors B G p.1 p.2).card : ℝ) < t

def badPartners (A : Finset α) (B : Finset β) (G : Finset (α × β))
    (t : ℝ) (a : α) : Finset α :=
  A.filter fun a' => ((commonNeighbors B G a a').card : ℝ) < t

def localBad (A : Finset α) (B : Finset β) (G : Finset (α × β))
    (t : ℝ) (b : β) : Finset (α × α) :=
  (badPairs A B G t).filter fun p => (p.1, b) ∈ G ∧ (p.2, b) ∈ G

@[simp] theorem mem_badPairs (A : Finset α) (B : Finset β) (G : Finset (α × β))
    (t : ℝ) (p : α × α) :
    p ∈ badPairs A B G t ↔
      (p.1 ∈ A ∧ p.2 ∈ A) ∧ ((commonNeighbors B G p.1 p.2).card : ℝ) < t := by
  simp only [badPairs, Finset.mem_filter, Finset.mem_product]

@[simp] theorem mem_badPartners (A : Finset α) (B : Finset β)
    (G : Finset (α × β)) (t : ℝ) (a a' : α) :
    a' ∈ badPartners A B G t a ↔
      a' ∈ A ∧ ((commonNeighbors B G a a').card : ℝ) < t := by
  simp only [badPartners, Finset.mem_filter]

end

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

def edgeDifferences (G : Finset (F × F)) : Finset F :=
  G.image fun e => e.1 - e.2

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

def edgeQuotients (G : Finset (F × F)) : Finset F :=
  G.image (fun e => e.1 / e.2)

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

def leftDegree (R : Pt → Ln → Prop) (L : Finset Ln) (p : Pt) : ℕ := by
  classical
  exact (L.filter (R p)).card

def rightDegree (R : Pt → Ln → Prop) (P : Finset Pt) (l : Ln) : ℕ :=
  leftDegree (fun l p => R p l) P l

def incidenceCount (R : Pt → Ln → Prop) (P : Finset Pt) (L : Finset Ln) : ℕ :=
  ∑ p ∈ P, leftDegree R L p

def MinimumDegrees (R : Pt → Ln → Prop) (d : ℝ) (P : Finset Pt) (L : Finset Ln) : Prop :=
  (∀ p ∈ P, d ≤ (leftDegree R L p : ℝ)) ∧
    (∀ l ∈ L, d ≤ (rightDegree R P l : ℝ))

end RyserCoveringCounterexample.Incidence

end

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

noncomputable def lowerDegreeCutoff (U q : ℝ) : ℝ := Real.sqrt q / (8 * U ^ 2)

end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_Uniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Incidence
noncomputable section

def SmallProperSubfields (F : Type*) [Field F] [Fintype F] : Prop :=
  ∀ M : Subfield F, M ≠ ⊤ → Nat.card M ^ 3 ≤ Fintype.card F

end
end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Geometry_ProjectionPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample

open scoped BigOperators

variable {F : Type*} [Field F]

theorem projectionPair_bijective (d e : Direction F) (hne : d ≠ e) :
    Function.Bijective (fun p : Point F => (projection d p, projection e p)) := by
  constructor
  · intro p q hpq
    exact point_eq_of_projection_eq_of_ne_direction hne
      (congrArg Prod.fst hpq) (congrArg Prod.snd hpq)
  · intro z
    obtain ⟨p, hp, _⟩ :=
      existsUnique_incident_of_ne_direction (d, z.1) (e, z.2) hne
    exact ⟨p, Prod.ext hp.1 hp.2⟩

noncomputable def projectionPairEquiv (d e : Direction F) (hne : d ≠ e) :
    Point F ≃ F × F :=
  Equiv.ofBijective (fun p : Point F => (projection d p, projection e p))
    (projectionPair_bijective d e hne)

@[simp] theorem projectionPairEquiv_apply (d e : Direction F) (hne : d ≠ e)
    (p : Point F) :
    projectionPairEquiv d e hne p = (projection d p, projection e p) := rfl

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Probability_Variance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section

namespace RyserCoveringCounterexample
namespace FiniteLaw

variable {Ω I : Type*} [Fintype Ω]

def variance (μ : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  μ.expectation (fun ω => (f ω - μ.expectation f) ^ 2)

def covariance (μ : FiniteLaw Ω) (f g : Ω → ℝ) : ℝ :=
  μ.expectation (fun ω =>
    (f ω - μ.expectation f) * (g ω - μ.expectation g))

end FiniteLaw
end RyserCoveringCounterexample

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

noncomputable def chunkFeasibleSet (data : Data F n) (U : Fin n → Finset (Point F))
    (E : Finset (Position n K)) (pool : Pool F n K) (i : Fin n) :
    Finset (Point F) := by
  classical
  exact (U i).filter (Feasible data E pool i)

@[simp] theorem mem_chunkFeasibleSet (data : Data F n)
    (U : Fin n → Finset (Point F)) (E : Finset (Position n K))
    (pool : Pool F n K) (i : Fin n) (b : Point F) :
    b ∈ chunkFeasibleSet data U E pool i ↔ b ∈ U i ∧ Feasible data E pool i b := let _ := instFintypeF; by
  classical
  simp only [chunkFeasibleSet, Finset.mem_filter]

end Configurations

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Domination_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Selection

structure Graph (V : Type*) where
  Adj : V → V → Prop
  symm : Std.Symm Adj
  loopless : Std.Irrefl Adj

variable {V ι : Type*} [instDecidableEqV : DecidableEq V] [DecidableEq ι]

def IsTransversalOn (G : Graph V) (pool : V → ι)
    (J : Finset ι) (U : Finset V) : Prop :=
  (∀ x ∈ U, ∀ y ∈ U, ¬ G.Adj x y) ∧
    Set.InjOn pool (U : Set V) ∧ U.image pool = J

noncomputable def neighborsIn (G : Graph V) (x : V) (U : Finset V) : Finset V := by
  classical
  exact U.filter (G.Adj x)

@[simp] theorem mem_neighborsIn {G : Graph V} {x y : V} {U : Finset V} :
    y ∈ neighborsIn G x U ↔ y ∈ U ∧ G.Adj x y := let _ := instDecidableEqV; by
  classical
  simp [neighborsIn]

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

structure DominationTrace (G : Graph V) (pool : V → ι)
    (J : Finset ι) (root : ι) (k : ℕ) where
  x : ℕ → V
  y : ℕ → Finset V
  nonempty : ∀ a, a < k → (y a).Nonempty
  disjoint : ∀ a, a < k → ∀ b, b < k → a ≠ b → Disjoint (y a) (y b)
  realized : ∃ U, IsTransversalOn G pool J U ∧
    ∀ a, a < k → neighborsIn G (x a) U = y a
  minimal : ∀ a, a < k → ∀ U, IsTransversalOn G pool J U →
    (∀ b, b < a → neighborsIn G (x b) U = y b) →
      (y a).card ≤ (neighborsIn G (x a) U).card
  origin : ∀ a, a < k → pool (x a) = root ∨
    ∃ b, b < a ∧ ∃ v ∈ y b, pool (x a) = pool v

namespace DominationTrace

variable {G : Graph V} {pool : V → ι} {J : Finset ι} {root : ι} {k : ℕ}

def verticesX (t : DominationTrace G pool J root k) : Finset V :=
  (Finset.range k).image t.x

def verticesY (t : DominationTrace G pool J root k) : Finset V :=
  (Finset.range k).biUnion t.y

@[simp] theorem mem_verticesY {t : DominationTrace G pool J root k} {v : V} :
    v ∈ t.verticesY ↔ ∃ a, a < k ∧ v ∈ t.y a := by
  simp [verticesY]

@[simp] theorem mem_verticesX {t : DominationTrace G pool J root k} {v : V} :
    v ∈ t.verticesX ↔ ∃ a, a < k ∧ t.x a = v := by
  simp [verticesX]

end DominationTrace
end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_PoolGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [DecidableEq F] {n K : ℕ}

def candidateGraph (data : Data F n) (pool : Pool F n K) :
    Graph (Position n K) where
  Adj e f := e.1 ≠ f.1 ∧ Conflict data e.1 f.1 (pool e) (pool f)
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[simp] theorem candidateGraph_adj (data : Data F n) (pool : Pool F n K)
    (e f : Position n K) :
    (candidateGraph data pool).Adj e f ↔
      e.1 ≠ f.1 ∧ Conflict data e.1 f.1 (pool e) (pool f) := Iff.rfl

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_AmbientPoolExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical

namespace RyserCoveringCounterexample.Construction

universe uk uf

variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]

def GoodAmbientPool {F : Type uf} [Field F] [Fintype F] [DecidableEq F]
    (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ)
    (pool : AmbientPool σ K) : Prop :=
  Selection.HasCompatibleChoice (groupSelectionData σ u v huv)
      (ambientFlatPoolEquiv σ K pool) ∧
    LineCover.GoodLineCover (ambientDeletionDelta (Fintype.card k) K)
      (ambientDeletionDelta (Fintype.card k) K / 10)
      (ambientPoolConfig σ u v huv a ha K pool) ∧
    PoolThin (groupPoints σ u v huv) (groupAltered σ u v huv) pool

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_Hypergraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

structure ConfigurationData (k F G : Type*) [DecidableEq F] where
  altered : G → Finset (Direction F)
  inverseSlope : ∀ i, {d : Direction F // d ∈ altered i} → k
  base : G → Point k → Point F
  transform : Point k → Point k
  retained : Finset (Point k)
  ordinaryPoints : Finset (Point F)

abbrev Vertex {k F G : Type*} [DecidableEq F]
    (altered : G → Finset (Direction F)) :=
  AffineLine F ⊕ (Σ i : G, {d : Direction F // d ∈ altered i} × k)

variable {k F G : Type*} [instFieldk : Field k] [instFieldF : Field F]
variable [instDecidableEqk : DecidableEq k] [DecidableEq F] [instDecidableEqG : DecidableEq G]

def ordinaryVertex (data : ConfigurationData k F G) (ell : AffineLine F) :
    Vertex (k := k) data.altered := Sum.inl ell

def specialVertex (data : ConfigurationData k F G) (i : G)
    (d : {d : Direction F // d ∈ data.altered i}) (c : k) :
    Vertex (k := k) data.altered := Sum.inr ⟨i, (d, c)⟩

def vertexPart (data : ConfigurationData k F G) :
    Vertex (k := k) data.altered → Direction F
  | Sum.inl ell => ell.1
  | Sum.inr v => v.2.1.val

@[simp] theorem vertexPart_ordinaryVertex (data : ConfigurationData k F G)
    (ell : AffineLine F) : vertexPart data (ordinaryVertex data ell) = ell.1 := let _ := instFieldk; let _ := instFieldF; let _ := instDecidableEqk; let _ := instDecidableEqG; rfl

@[simp] theorem vertexPart_specialVertex (data : ConfigurationData k F G) (i : G)
    (d : {d : Direction F // d ∈ data.altered i}) (c : k) :
    vertexPart data (specialVertex data i d c) = d.val := let _ := instFieldk; let _ := instFieldF; let _ := instDecidableEqk; let _ := instDecidableEqG; rfl

def exceptionalVertex (data : ConfigurationData k F G) (i : G) (w : Point k)
    (d : Direction F) : Vertex (k := k) data.altered :=
  if h : d ∈ data.altered i then
    specialVertex data i ⟨d, h⟩
      (projection (some (data.inverseSlope i ⟨d, h⟩)) (data.transform w))
  else ordinaryVertex data (lineThrough d (data.base i w))

variable [Fintype F]

def ordinaryEdge (data : ConfigurationData k F G) (x : Point F) :
    Finset (Vertex (k := k) data.altered) :=
  Finset.univ.image (fun d => ordinaryVertex data (lineThrough d x))

def exceptionalEdge (data : ConfigurationData k F G) (i : G) (w : Point k) :
    Finset (Vertex (k := k) data.altered) :=
  Finset.univ.image (exceptionalVertex data i w)

variable [Fintype G]

def hypergraph (data : ConfigurationData k F G) :
    Hypergraph (Vertex (k := k) data.altered) := by
  classical
  exact data.ordinaryPoints.image (ordinaryEdge data) ∪
    Finset.univ.biUnion (fun i => data.retained.image (exceptionalEdge data i))

@[simp] theorem mem_hypergraph (data : ConfigurationData k F G)
    (e : Finset (Vertex (k := k) data.altered)) :
    e ∈ hypergraph data ↔
      (∃ x ∈ data.ordinaryPoints, ordinaryEdge data x = e) ∨
      (∃ i, ∃ w ∈ data.retained, exceptionalEdge data i w = e) := by
  classical
  simp only [hypergraph, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
    Finset.mem_univ, true_and]

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_CoordinateCompatibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [Field k] [Field F]
variable [instFintypek : Fintype k] [instDecidableEqk : DecidableEq k] [DecidableEq F] [DecidableEq G]

def placedConfiguration (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (Y : Finset (Point k)) (X : Finset (Point F)) :
    ConfigurationData k F G where
  altered i := alteredDirections σ (M i)
  inverseSlope i := alteredInverseSlope σ (M i)
  base i := placedPoint σ (M i) (b i)
  transform := cubeMap
  retained := Y
  ordinaryPoints := X

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_DeletionUnionOutside
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {G k F : Type*} [Field k] [Field F]
variable [Fintype G] [Fintype k] [Fintype F]
variable [DecidableEq G] [DecidableEq k] [DecidableEq F]

def activeDeletionLine (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (p : Point F)
    (i : {i // i ∈ activeDeletionGroups σ M b a p}) : AffineLine F :=
  Classical.choose ((mem_activeDeletionGroups σ M b a p i.val).mp i.property)

theorem activeDeletionLine_spec (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (p : Point F)
    (i : {i // i ∈ activeDeletionGroups σ M b a p}) :
    activeDeletionLine σ M b a p i ∈ deletedLines σ (M i.val) (b i.val) a ∧
      Incidence p (activeDeletionLine σ M b a p i) :=
  Classical.choose_spec ((mem_activeDeletionGroups σ M b a p i.val).mp i.property)

theorem activeDeletionLine_mem (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (p : Point F)
    (i : {i // i ∈ activeDeletionGroups σ M b a p}) :
    activeDeletionLine σ M b a p i ∈ deletedLines σ (M i.val) (b i.val) a :=
  (activeDeletionLine_spec σ M b a p i).1

theorem incidence_activeDeletionLine (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (p : Point F)
    (i : {i // i ∈ activeDeletionGroups σ M b a p}) :
    Incidence p (activeDeletionLine σ M b a p i) :=
  (activeDeletionLine_spec σ M b a p i).2

theorem activeDeletionLine_injective (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (p : Point F)
    (hsep : DeletionSeparated σ M b a) :
    Function.Injective (activeDeletionLine σ M b a p) := by
  intro i j hij
  apply Subtype.ext
  by_contra hne
  have hdisj := disjoint_deletedLines_of_separated σ M b a hsep hne
  have hmemj : activeDeletionLine σ M b a p i ∈
      deletedLines σ (M j.val) (b j.val) a := by
    rw [hij]
    exact activeDeletionLine_mem σ M b a p j
  exact (Finset.disjoint_left.mp hdisj)
    (activeDeletionLine_mem σ M b a p i) hmemj

def activeDeletionLineInPencil (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (p : Point F)
    (i : {i // i ∈ activeDeletionGroups σ M b a p}) :
    {ell // ell ∈ deletedPencil σ M b a p} :=
  ⟨activeDeletionLine σ M b a p i,
    (mem_deletedPencil σ M b a p _).mpr
      ⟨(mem_allDeletedLines σ M b a _).mpr
        ⟨i.val, activeDeletionLine_mem σ M b a p i⟩,
        incidence_activeDeletionLine σ M b a p i⟩⟩

theorem activeDeletionLineInPencil_surjective
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (p : Point F)
    (hout : ∀ i, p ∉ placedSubplane σ (M i) (b i)) :
    Function.Surjective (activeDeletionLineInPencil σ M b a p) := by
  intro ell
  obtain ⟨hell, hpell⟩ := (mem_deletedPencil σ M b a p ell.val).mp ell.property
  obtain ⟨i, hi⟩ := (mem_allDeletedLines σ M b a ell.val).mp hell
  have hactive : i ∈ activeDeletionGroups σ M b a p :=
    (mem_activeDeletionGroups σ M b a p i).mpr ⟨ell.val, hi, hpell⟩
  refine ⟨⟨i, hactive⟩, ?_⟩
  apply Subtype.ext
  change activeDeletionLine σ M b a p ⟨i, hactive⟩ = ell.val
  exact eq_deletedLine_of_incident_of_notMem_placedSubplane
    σ (M i) (b i) a (hout i)
    (activeDeletionLine_mem σ M b a p ⟨i, hactive⟩) hi
    (incidence_activeDeletionLine σ M b a p ⟨i, hactive⟩) hpell

theorem activeDeletionLineInPencil_bijective
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (p : Point F) (hsep : DeletionSeparated σ M b a)
    (hout : ∀ i, p ∉ placedSubplane σ (M i) (b i)) :
    Function.Bijective (activeDeletionLineInPencil σ M b a p) := by
  constructor
  · intro i j hij
    exact activeDeletionLine_injective σ M b a p hsep (congrArg Subtype.val hij)
  · exact activeDeletionLineInPencil_surjective σ M b a p hout

def activeDeletionGroupEquivDeletedPencil
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (p : Point F) (hsep : DeletionSeparated σ M b a)
    (hout : ∀ i, p ∉ placedSubplane σ (M i) (b i)) :
    {i // i ∈ activeDeletionGroups σ M b a p} ≃
      {ell // ell ∈ deletedPencil σ M b a p} :=
  Equiv.ofBijective (activeDeletionLineInPencil σ M b a p)
    (activeDeletionLineInPencil_bijective σ M b a p hsep hout)

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_OrdinaryCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [instFieldk : Field k] [instFieldF : Field F]
variable [instDecidableEqk : DecidableEq k] [DecidableEq F] [instDecidableEqG : DecidableEq G]

def ordinaryLines (data : ConfigurationData k F G)
    (C : Finset (Vertex (k := k) data.altered)) : Finset (AffineLine F) := C.toLeft

@[simp] theorem mem_ordinaryLines (data : ConfigurationData k F G)
    (C : Finset (Vertex (k := let _ := instFieldk; let _ := instFieldF; let _ := instDecidableEqk; let _ := instDecidableEqG; k) data.altered)) (ell : AffineLine F) :
    ell ∈ ordinaryLines data C ↔ ordinaryVertex data ell ∈ C :=
  Finset.mem_toLeft

variable [Fintype F]

def forcedPencilVertices (data : ConfigurationData k F G)
    (B : Finset (AffineLine F)) (p : ProjectivePoint F) :
    Finset (Vertex (k := k) data.altered) :=
  (affinePencil p \ B).image (ordinaryVertex data)

end RyserCoveringCounterexample.Construction

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_ExceptionalCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [DecidableEq G] [Fintype F]

def ActiveExceptional (data : ConfigurationData k F G) (i : G)
    (v : Vertex (k := k) data.altered) : Prop :=
  ∃ w ∈ data.retained, v ∈ exceptionalEdge data i w

def LineCapable (data : ConfigurationData k F G)
    (axes : G → Finset (Direction F)) (i : G) :
    Vertex (k := k) data.altered → Prop
  | Sum.inl ell => ell.1 ∈ axes i
  | Sum.inr tag => tag.1 = i

def lineResources (data : ConfigurationData k F G)
    (axes : G → Finset (Direction F))
    (C : Finset (Vertex (k := k) data.altered)) (i : G) :
    Finset (Vertex (k := k) data.altered) := by
  classical
  exact C.filter fun v => LineCapable data axes i v ∧ ActiveExceptional data i v

def pointResources (data : ConfigurationData k F G)
    (axes : G → Finset (Direction F))
    (C : Finset (Vertex (k := k) data.altered)) (i : G) :
    Finset (Vertex (k := k) data.altered) := by
  classical
  exact C.filter fun v => ¬ LineCapable data axes i v ∧ ActiveExceptional data i v

@[simp] theorem mem_lineResources (data : ConfigurationData k F G)
    (axes : G → Finset (Direction F))
    (C : Finset (Vertex (k := k) data.altered)) (i : G)
    (v : Vertex (k := k) data.altered) :
    v ∈ lineResources data axes C i ↔
      v ∈ C ∧ LineCapable data axes i v ∧ ActiveExceptional data i v := by
  classical
  simp only [lineResources, Finset.mem_filter]

@[simp] theorem mem_pointResources (data : ConfigurationData k F G)
    (axes : G → Finset (Direction F))
    (C : Finset (Vertex (k := k) data.altered)) (i : G)
    (v : Vertex (k := k) data.altered) :
    v ∈ pointResources data axes C i ↔
      v ∈ C ∧ ¬ LineCapable data axes i v ∧ ActiveExceptional data i v := by
  classical
  simp only [pointResources, Finset.mem_filter]

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_GadgetConsequences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def GadgetCoverProperty (Y : Finset (Point F)) : Prop :=
  ∀ (B : Finset (Point F)) (L : Finset (AffineLine F)),
    (∀ y ∈ Y, y ∈ B ∨ ∃ ell ∈ L, Incidence y ell) →
    2 * L.card + B.card ≤ 2 * Fintype.card F →
    ∃ d : Direction F, L = affinePencil (Sum.inr d) ∧ B = ∅

end RyserCoveringCounterexample.Construction

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_FiniteSelectionCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Construction

open scoped BigOperators

variable {G P : Type*}

variable [DecidableEq G] [instDecidableEqP : DecidableEq P]

def selectedPositions (I : Finset G) (S : G → Finset P) : Finset (G × P) :=
  I.biUnion (fun i => (S i).image (fun w => (i, w)))

@[simp] theorem mem_selectedPositions
    {I : Finset G} {S : G → Finset P} {x : G × P} :
    x ∈ selectedPositions I S ↔ x.1 ∈ I ∧ x.2 ∈ S x.1 := by
  rcases x with ⟨i, w⟩
  simp [selectedPositions]

end RyserCoveringCounterexample.Construction

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_FiniteOutsideAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [instFieldk : Field k] [Field F]
variable [instDecidableEqk : DecidableEq k] [DecidableEq F] [instDecidableEqG : DecidableEq G]
variable [instFintypeF : Fintype F] [instFintypeG : Fintype G]

def offPencilGroups (data : ConfigurationData k F G) (p : Point F)
    (ell : AffineLine F) : Finset G := by
  classical
  exact Finset.univ.filter (fun i => ∃ w ∈ data.retained,
    Incidence (data.base i w) ell ∧
      joinDirection p (data.base i w) ∈ data.altered i)

@[simp] theorem mem_offPencilGroups (data : ConfigurationData k F G)
    (p : Point F) (ell : AffineLine F) (i : G) :
    i ∈ offPencilGroups data p ell ↔ ∃ w ∈ data.retained,
      Incidence (data.base i w) ell ∧
        joinDirection p (data.base i w) ∈ data.altered i := let _ := instFieldk; let _ := instDecidableEqk; let _ := instDecidableEqG; let _ := instFintypeF; by
  classical
  simp only [offPencilGroups, Finset.mem_filter, Finset.mem_univ, true_and]

def OffPencilThin (data : ConfigurationData k F G) (p : Point F) : Prop :=
  ∀ ell : AffineLine F, ¬ Incidence p ell →
    (offPencilGroups data p ell).card ≤ 5

open scoped Classical

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_GadgetShapes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable (k : Type*) [Field k] [Fintype k] [DecidableEq k]

def cubicShapes : Finset (Finset (Point k)) :=
  Finset.univ.image fun dz : NonzeroSlope k × k => cubicShape dz.1.val dz.2

theorem cubicShapes_card_le_square : (cubicShapes k).card ≤ Fintype.card k ^ 2 := by
  calc
    (cubicShapes k).card ≤
        (Finset.univ : Finset (NonzeroSlope k × k)).card :=
      Finset.card_image_le
    _ = Fintype.card (NonzeroSlope k) * Fintype.card k := by
      rw [Finset.card_univ, Fintype.card_prod]
    _ ≤ Fintype.card k * Fintype.card k :=
      Nat.mul_le_mul_right _
        (Fintype.card_subtype_le (fun d : k => d ≠ 0))
    _ = Fintype.card k ^ 2 := (pow_two _).symm

theorem cubicShapes_card_le : (cubicShapes k).card ≤ 3 * Fintype.card k ^ 3 := by
  have hq : 1 ≤ Fintype.card k := Nat.succ_le_of_lt Fintype.card_pos
  have hstep : Fintype.card k ^ 2 ≤ Fintype.card k ^ 3 := by
    rw [pow_succ (Fintype.card k) 2]
    simpa only [Nat.mul_one] using
      (Nat.mul_le_mul_left (Fintype.card k ^ 2) hq)
  exact (cubicShapes_card_le_square k).trans (hstep.trans (by omega))

variable {k}

@[simp] theorem mem_cubicShapes {S : Finset (Point k)} :
    S ∈ cubicShapes k ↔ ∃ d : NonzeroSlope k, ∃ z : k, cubicShape d.val z = S := by
  simp only [cubicShapes, Finset.mem_image, Finset.mem_univ, true_and, Prod.exists]

theorem cubicShape_mem_cubicShapes (d : NonzeroSlope k) (z : k) :
    cubicShape d.val z ∈ cubicShapes k :=
  Finset.mem_image.mpr ⟨(d, z), Finset.mem_univ _, rfl⟩

theorem cubicShapes_member_card {S : Finset (Point k)} (hS : S ∈ cubicShapes k) :
    S.card = Fintype.card k := by
  obtain ⟨d, z, rfl⟩ := mem_cubicShapes.mp hS
  exact cubicShape_card d.val z d.property

theorem cubicShapes_member_card_le {S : Finset (Point k)} (hS : S ∈ cubicShapes k) :
    S.card ≤ 3 * Fintype.card k := by
  rw [cubicShapes_member_card hS]
  omega

variable (k) in
theorem cubicShapes_sparse : LineCover.SparseShapes (cubicShapes k) 3 := by
  intro S hS ell _
  obtain ⟨d, z, rfl⟩ := mem_cubicShapes.mp hS
  exact cubicShape_inter_linePoints_card_le d.val z d.property ell

theorem cubicShapes_member_ne_linePoints (hcard : 3 < Fintype.card k)
    {S : Finset (Point k)} (hS : S ∈ cubicShapes k) (ell : AffineLine k) :
    S ≠ linePoints ell := by
  obtain ⟨d, z, rfl⟩ := mem_cubicShapes.mp hS
  exact cubicShape_ne_linePoints d.val z d.property hcard ell

def cubicTrialOutcome (d : NonzeroSlope k) (z : k) :
    LineCover.Outcome (cubicShapes k) 3 :=
  ⟨{⟨cubicShape d.val z, cubicShape_mem_cubicShapes d z⟩}, by simp⟩

@[simp] theorem cubicTrialOutcome_val (d : NonzeroSlope k) (z : k) :
    (cubicTrialOutcome d z).val =
      {⟨cubicShape d.val z, cubicShape_mem_cubicShapes d z⟩} := rfl

@[simp] theorem mem_deleted_cubicTrialOutcome (ignore : Finset (Finset (Point k)))
    (d : NonzeroSlope k) (z : k) (x : Point k) :
    x ∈ LineCover.deleted ignore (cubicTrialOutcome d z) ↔
      cubicShape d.val z ∉ ignore ∧ x ∈ cubicShape d.val z := by
  simp [LineCover.mem_deleted, cubicTrialOutcome]

@[simp] theorem deleted_empty_cubicTrialOutcome (d : NonzeroSlope k) (z : k) :
    LineCover.deleted ∅ (cubicTrialOutcome d z) = cubicShape d.val z := by
  ext x
  simp only [mem_deleted_cubicTrialOutcome, Finset.notMem_empty, not_false_eq_true, true_and]

@[simp] theorem mem_deleted_empty_cubicTrialOutcome
    (d : NonzeroSlope k) (z : k) (x : Point k) :
    x ∈ LineCover.deleted ∅ (cubicTrialOutcome d z) ↔ x ∈ cubicShape d.val z := by
  rw [deleted_empty_cubicTrialOutcome]

theorem cubicTrialOutcome_no_line (d : NonzeroSlope k) (z : k)
    (hcard : 3 < Fintype.card k) (ell : AffineLine k) :
    ¬ ∃ S ∈ (cubicTrialOutcome d z).val, S.val = linePoints ell := by
  rintro ⟨S, _, hline⟩
  exact cubicShapes_member_ne_linePoints hcard S.property ell hline

@[simp] theorem mem_selected_cubicTrials {n : ℕ}
    (d : Fin n → NonzeroSlope k) (z : Fin n → k) (S : Finset (Point k)) :
    S ∈ LineCover.selected (fun i => cubicTrialOutcome (d i) (z i)) ↔
      ∃ i, cubicShape (d i).val (z i) = S := by
  simp [LineCover.mem_selected, cubicTrialOutcome]

@[simp] theorem mem_survivors_cubicTrials {n : ℕ}
    (ignore : Finset (Finset (Point k)))
    (d : Fin n → NonzeroSlope k) (z : Fin n → k) (x : Point k) :
    x ∈ LineCover.survivors ignore (fun i => cubicTrialOutcome (d i) (z i)) ↔
      ∀ i, cubicShape (d i).val (z i) ∉ ignore → x ∉ cubicShape (d i).val (z i) := by
  simp only [LineCover.mem_survivors, mem_deleted_cubicTrialOutcome, not_and]

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_SurvivalNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.LineCover

theorem log_one_quarter_le_neg_one : Real.log (1 / 4 : ℝ) ≤ -1 := by
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
    have h := Real.le_log_one_add_of_nonneg (x := 3) (by norm_num)
    norm_num at h
    linarith
  rw [one_div, Real.log_inv]
  linarith

theorem one_quarter_le_survival_pow_pred (q : ℕ) (hq : 2 ≤ q) :
    (1 / 4 : ℝ) ≤ (1 - 1 / (q : ℝ)) ^ (q - 1) := by
  have hq1 : 1 ≤ q := le_trans (by decide : 1 ≤ 2) hq
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hqm : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hbase : 1 - 1 / (q : ℝ) = ((q : ℝ) - 1) / (q : ℝ) := by
    field_simp [hq0.ne']
  have hb : (0 : ℝ) < 1 - 1 / (q : ℝ) := by
    rw [hbase]
    exact div_pos hqm hq0
  have hunit : ((q - 1 : ℕ) : ℝ) * (1 - (1 - 1 / (q : ℝ))⁻¹) = -1 := by
    rw [Nat.cast_sub hq1, Nat.cast_one, hbase, inv_div]
    field_simp [hqm.ne']; ring
  have hlog := mul_le_mul_of_nonneg_left
    (Real.one_sub_inv_le_log_of_pos hb)
    (Nat.cast_nonneg (q - 1) : (0 : ℝ) ≤ ((q - 1 : ℕ) : ℝ))
  rw [hunit] at hlog
  apply (Real.log_le_log_iff (by norm_num : (0 : ℝ) < 1 / 4)
    (pow_pos hb (q - 1))).mp
  rw [Real.log_pow]
  exact log_one_quarter_le_neg_one.trans hlog

end RyserCoveringCounterexample.LineCover

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_GadgetProcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Construction

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k]

theorem nonzeroSlope_card (k : Type*) [Field k] [Fintype k] [DecidableEq k] :
    Fintype.card (NonzeroSlope k) = Fintype.card k - 1 := by
  change Fintype.card {d : k // ¬d = 0} = _
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]

def cubicTrialLaw (d : NonzeroSlope k) :
    FiniteLaw (LineCover.Outcome (cubicShapes k) 3) :=
  (FiniteLaw.uniform k).map (cubicTrialOutcome d)

theorem cubicTrialLaw_point_probability
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (d : NonzeroSlope k) (x : Point k) :
    (cubicTrialLaw d).prob (fun a => x ∈ LineCover.deleted ∅ a) =
      1 / (Fintype.card k : ℝ) := by
  rw [cubicTrialLaw, FiniteLaw.prob_map]
  simp only [deleted_empty_cubicTrialOutcome]
  rw [FiniteLaw.uniform_prob]
  have hfilter : @Finset.filter _ (fun z => x ∈ cubicShape d.val z)
      (fun z => Classical.propDecidable (x ∈ cubicShape d.val z)) Finset.univ =
      Finset.univ.filter (fun z => x ∈ cubicShape d.val z) :=
    Finset.filter_congr_decidable _ _ _
  rw [hfilter, cubicShape_intercept_card hcop]
  simp

theorem cubicTrialLaw_point_probability_le
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (d : NonzeroSlope k) (x : Point k) :
    (cubicTrialLaw d).prob (fun a => x ∈ LineCover.deleted ∅ a) ≤
      (3 : ℝ) / Fintype.card k := by
  rw [cubicTrialLaw_point_probability hcop]
  exact div_le_div_of_nonneg_right (by norm_num) (by positivity)

theorem cubicTrialLaw_line_probability_zero
    (hcard : 3 < Fintype.card k) (d : NonzeroSlope k) (l : AffineLine k) :
    (cubicTrialLaw d).prob (fun a => ∃ S ∈ a.val, S.val = linePoints l) = 0 := by
  rw [cubicTrialLaw, FiniteLaw.prob_map]
  have hevent : (fun z : k => ∃ S ∈ (cubicTrialOutcome d z).val,
      S.val = linePoints l) = (fun _ : k => False) := by
    funext z
    exact propext (iff_false_intro (cubicTrialOutcome_no_line d z hcard l))
  rw [hevent, FiniteLaw.prob_false]

def gadgetSlope (i : Fin (Fintype.card (NonzeroSlope k))) : NonzeroSlope k :=
  (Fintype.equivFin (NonzeroSlope k)).symm i

def gadgetTrials (i : Fin (Fintype.card (NonzeroSlope k))) :
    FiniteLaw (LineCover.Outcome (cubicShapes k) 3) :=
  cubicTrialLaw (gadgetSlope i)

def gadgetSurvival (k : Type*) [Field k] [Fintype k] : ℝ :=
  (1 - 1 / (Fintype.card k : ℝ)) ^ (Fintype.card k - 1)

theorem gadgetTrials_uniformSurvival
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (x : Point k) :
    (FiniteLaw.pi (gadgetTrials (k := k))).prob
      (fun a => x ∈ LineCover.survivors ∅ a) = gadgetSurvival k := by
  simp only [LineCover.mem_survivors]
  rw [FiniteLaw.prob_pi (gadgetTrials (k := k))
    (fun _ a => x ∉ LineCover.deleted ∅ a)]
  simp_rw [FiniteLaw.prob_compl]
  simp only [gadgetTrials, cubicTrialLaw_point_probability hcop]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    nonzeroSlope_card, gadgetSurvival]

def gadgetDeletionProcess
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (hcard : 3 < Fintype.card k) (δ : ℝ)
    (hδ : δ ≤ gadgetSurvival k) : LineCover.DeletionProcess k 3 δ where
  shapes := cubicShapes k
  shapeCount := cubicShapes_card_le k
  shapeSize := by
    intro S hS
    exact cubicShapes_member_card_le hS
  sparse := cubicShapes_sparse k
  trialsCount := Fintype.card (NonzeroSlope k)
  trials := gadgetTrials
  trialsCount_le := by rw [nonzeroSlope_card]; omega
  pointCap := fun i x => cubicTrialLaw_point_probability_le hcop (gadgetSlope i) x
  survival := gadgetSurvival k
  survivalLower := hδ
  uniformSurvival := gadgetTrials_uniformSurvival hcop
  lineCap := by
    intro l
    have hzero : ∀ i : Fin (Fintype.card (NonzeroSlope k)),
        (gadgetTrials i).prob (fun a => ∃ S ∈ a.val, S.val = linePoints l) = 0 :=
      fun i => cubicTrialLaw_line_probability_zero hcard (gadgetSlope i) l
    simp only [hzero, Finset.sum_const_zero]
    positivity

def cubicDeletionProcess
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (hcard : 3 < Fintype.card k) : LineCover.DeletionProcess k 3 (1 / 4 : ℝ) :=
  gadgetDeletionProcess hcop hcard (1 / 4)
    (LineCover.one_quarter_le_survival_pow_pred (Fintype.card k) (by omega))

def gadgetLaw (k : Type*) [Field k] [Fintype k] [DecidableEq k] :
    FiniteLaw (GadgetOutcome k) :=
  FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)

def gadgetInterceptEquiv : GadgetOutcome k ≃
    (Fin (Fintype.card (NonzeroSlope k)) → k) where
  toFun a i := a (gadgetSlope i)
  invFun b d := b ((Fintype.equivFin (NonzeroSlope k)) d)
  left_inv a := by
    funext d
    simp only [gadgetSlope, Equiv.symm_apply_apply]
  right_inv b := by
    funext i
    simp only [gadgetSlope, Equiv.apply_symm_apply]

def gadgetConfig (a : GadgetOutcome k) :
    Fin (Fintype.card (NonzeroSlope k)) → LineCover.Outcome (cubicShapes k) 3 :=
  fun i => cubicTrialOutcome (gadgetSlope i) (a (gadgetSlope i))

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_GadgetGood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k]

def GoodGadget (a : GadgetOutcome k) : Prop :=
  OriginalLineDensity a ∧
    (∀ ell : AffineLine k,
      Fintype.card k ≤ 8 * (transformedRetained a ∩ linePoints ell).card) ∧
    GadgetCoverProperty (transformedRetained a)

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_DeterministicCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [Fintype k] [Fintype F]
variable (σ : k →+* F) (u v : k) (huv : u ≠ v)
variable (a : GadgetOutcome k) (b : ConfigurationGroup σ → Point F)
variable (X : Finset (Point F))

local instance instDecidableEqConfigurationGroup : DecidableEq (ConfigurationGroup σ) := Classical.decEq _

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_GadgetConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

open scoped BigOperators

variable (I Ω : Type*) [Fintype I]

def finCoordinateEquiv : (Fin (Fintype.card I) → Ω) ≃ (I → Ω) where
  toFun w i := w (Fintype.equivFin I i)
  invFun a j := a ((Fintype.equivFin I).symm j)
  left_inv w := by
    funext j
    simp
  right_inv a := by
    funext i
    simp

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_GadgetOriginalCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k]

def originalLineSurvivors (a : GadgetOutcome k) (d : NonzeroSlope k) (z : k) :
    Finset (Point k) :=
  (linePoints (some d.val, z)).filter
    (fun p => ∀ e : NonzeroSlope k, e ≠ d → ¬ Incidence p (omittedLine a e))

def originalLineCount (a : GadgetOutcome k) (d : NonzeroSlope k) (z : k) : ℝ :=
  (originalLineSurvivors a d z).card

@[simp] theorem mem_originalLineSurvivors (a : GadgetOutcome k)
    (d : NonzeroSlope k) (z : k) (p : Point k) :
    p ∈ originalLineSurvivors a d z ↔
      Incidence p (some d.val, z) ∧
        ∀ e : NonzeroSlope k, e ≠ d → ¬ Incidence p (omittedLine a e) := by
  simp only [originalLineSurvivors, Finset.mem_filter, mem_linePoints]

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_SelectedHypergraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F] [Fintype k] [Fintype F]
  [DecidableEq k] [DecidableEq F]

def ambientSelectedConfiguration
    (σ : k →+* F) (u v : k) (huv : u ≠ v) (a : GadgetOutcome k)
    (K : ℕ) (b : AmbientPool σ K) (choice : ConfigurationGroup σ → Fin K) :
    ConfigurationData k F (ConfigurationGroup σ) :=
  placedConfiguration σ (groupPlacement σ u v huv) (fun i => b i (choice i))
    (retainedPoints a) (ambientSelectedSurvivors σ u v huv a K b choice)

end RyserCoveringCounterexample.Construction

end

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

abbrev ExtensionField (p n : ℕ) [Fact p.Prime] := GaloisField p n

end RyserCoveringCounterexample

end OAI
end


