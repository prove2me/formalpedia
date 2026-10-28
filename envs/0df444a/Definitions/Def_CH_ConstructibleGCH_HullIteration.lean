-- Prove2me | Definitions.Def_CH_ConstructibleGCH_HullIteration
-- name    : CH_ConstructibleGCH_HullIteration
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-25T22:35:35.806347+00:00
-- url     : https://prove2.me/theorems/29d4edd8-bc8e-4376-a241-14ef4925cefb
-- title:
--   Uniform witness iteration and elementary-hull interfaces
-- statement:
--   This library supplies the finite and omega-indexed textbook E witness iteration, its elementary-hull seed and the tagged binary-union injection interfaces. All internal families and representing graphs are constructible sets.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   This module includes supporting proofs required by its definitions and constructor data.
--
--   Mathematical references: Andrew Marks, [*Set Theory*, Lemma 21.3 and Corollary 21.4, printed pp. 90–91](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf); Kurt Gödel, [“The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis,” PNAS 24 (1938), 556–557](https://doi.org/10.1073/pnas.24.12.556); and Gödel’s 1940 Princeton monograph, *The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis with the Axioms of Set Theory* ([publisher note](https://assets.press.princeton.edu/about_pup/PUP100/book/1hGodel.pdf)). The upstream textbook E/Df construction cites Wang Fangting, *Axiomatic Set Theory*, §§6.3–6.8.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. Source modules: https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookEUniformWitnessIteration.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookEElementaryHull.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/InternalBinaryUnionInjection.lean#L1

import Definitions.Def_CH_ConstructibleAC_Library15
import Definitions.Def_CH_Constructible
import Mathlib.Data.List.Shortlex
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Sigma.Lex
import Mathlib.Data.Sum.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.Tactic.FinCases
import Mathlib.SetTheory.ZFC.Cardinal
import Mathlib.SetTheory.ZFC.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.SetTheory.Cardinal.Basic

import Definitions.Def_CH_ConstructibleGCH_FiniteIteration
/-
Prove2Me adaptation of the constructible-universe formalization by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
Original copyright notices are preserved below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 1000000

/- Source module: Solutions.Work_CUGCH_TextbookEUniformWitnessIteration -/
section GCHSource_Work_CUGCH_TextbookEUniformWitnessIteration
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# The internal omega iteration of the uniform textbook E witness step

The simultaneous witness operation from
`TextbookEUniformWitnessStepFormula` is defined by one fixed first-order
formula.  This file applies the general finite-iteration formula to that
operation, uses Replacement over the genuine internal omega, and takes the
internal union of the resulting family.

The final closure proof is the standard finite-tuple maximum-stage argument:
each parameter occurs at a finite stage, all parameters occur together at
their maximum stage, and the next stage supplies the requested witness.
-/

section

open Set

universe u

namespace Constructible.Model

open FiniteSequenceZF
open ContinuumFormula

noncomputable section

local notation "LMem" => lCarrierMem

/-! ## Exact finite iteration -/

/-- The four fixed parameters of the simultaneous witness-step formula. -/
def textbookEUniformWitnessStepParameters
    (U : LCarrier.{u}) : Tuple LCarrier.{u} 4 :=
  ![U, canonicalWitnessOrder U, textbookEWitnessTaskDomain, omegaLCarrier]

/-- The fixed step formula defines exactly the simultaneous witness step. -/
theorem textbookEUniformWitnessStep_definesFiniteIterationStep
    (U : LCarrier.{u}) :
    DefinesFiniteIterationStep textbookEUniformWitnessStepFormula
      (textbookEUniformWitnessStepParameters U)
      (fun current => textbookEUniformWitnessStep current U) := by
  intro current next
  have hassignment :
      snoc
          (snoc (textbookEUniformWitnessStepParameters U) current)
          next =
        ![U, canonicalWitnessOrder U, textbookEWitnessTaskDomain,
          omegaLCarrier, current, next] := by
    funext i
    fin_cases i <;> rfl
  rw [hassignment]
  exact satisfies_textbookEUniformWitnessStepFormula_iff U current next

/-- The standard finite iteration beginning with `seed`. -/
def textbookEUniformWitnessStage
    (seed U : LCarrier.{u}) : Nat -> LCarrier.{u} :=
  uniformFiniteIterate
    (fun current => textbookEUniformWitnessStep current U) seed

@[simp]
theorem textbookEUniformWitnessStage_zero
    (seed U : LCarrier.{u}) :
    textbookEUniformWitnessStage seed U 0 = seed :=
  rfl

@[simp]
theorem textbookEUniformWitnessStage_succ
    (seed U : LCarrier.{u}) (n : Nat) :
    textbookEUniformWitnessStage seed U (n + 1) =
      textbookEUniformWitnessStep
        (textbookEUniformWitnessStage seed U n) U :=
  rfl







/-! ## The internal omega family and its union -/

/--
The fixed finite-history formula, with parameters
`[U, canonicalWitnessOrder U, textbookEWitnessTaskDomain, omega, seed]`,
uniformly defines all finite stages.
-/
noncomputable def textbookEUniformWitnessOmegaFamilySpec
    (seed U : LCarrier.{u}) :
    ParametricUniformOmegaFamilySpec.{u} 5 :=
  uniformFiniteIterationOmegaFamilySpec
    textbookEUniformWitnessStepFormula
    (textbookEUniformWitnessStepParameters U)
    (fun current => textbookEUniformWitnessStep current U)
    seed
    (textbookEUniformWitnessStep_definesFiniteIterationStep U)

@[simp]
theorem textbookEUniformWitnessOmegaFamilySpec_value
    (seed U : LCarrier.{u}) (n : Nat) :
    (textbookEUniformWitnessOmegaFamilySpec seed U).value n =
      textbookEUniformWitnessStage seed U n :=
  rfl

/-- The actual internal union of the Replacement-collected finite stages. -/
noncomputable def textbookEUniformWitnessOmegaUnion
    (seed U : LCarrier.{u}) : LCarrier.{u} :=
  parametricUniformOmegaUnion
    (textbookEUniformWitnessOmegaFamilySpec seed U)

@[simp]
theorem mem_textbookEUniformWitnessOmegaUnion_iff
    (seed U z : LCarrier.{u}) :
    z.1 ∈ (textbookEUniformWitnessOmegaUnion seed U).1 ↔
      ∃ n : Nat,
        z.1 ∈ (textbookEUniformWitnessStage seed U n).1 := by
  rw [textbookEUniformWitnessOmegaUnion,
    mem_parametricUniformOmegaUnion_iff]
  rfl







/-! ## The finite-tuple maximum-stage argument -/





end

end Constructible.Model

end
end GCHSource_Work_CUGCH_TextbookEUniformWitnessIteration


/- Source module: Solutions.Work_CUGCH_TextbookEElementaryHull -/
section GCHSource_Work_CUGCH_TextbookEElementaryHull
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# The full textbook E elementary hull

For constructible parameters `kappa` and `x`, choose a condensation reflection
level containing both.  Start with the textbook seed

`kappa union {x}`,

represented exactly by `adjoinLCarrier kappa x`, and iterate the simultaneous
textbook `E` witness operation through the internal natural numbers.
Replacement collects the finite stages, and their internal union is fully
elementary in the chosen constructible level.

The construction of the elementary hull is independent of its cardinal
bound.  The final assembly into `CardinalControlledHull` therefore keeps the
remaining smallness premise visible as an actual internal injection from this
specific hull into `kappa`.
-/

section

open Set

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model
open Constructible.MostowskiCollapse

noncomputable section

local notation "LMem" => Constructible.Model.lCarrierMem

/-! ## The chosen ambient level and the textbook seed -/

/-- A condensation reflection level containing both displayed parameters. -/
noncomputable def textbookEElementaryHullTheta
    (kappa x : LCarrier.{u}) : Ordinal.{u} :=
  Classical.choose
    (exists_condensationReflectionLevel_containing_pair kappa x)



/-- The selected constructible level, packaged as an actual member of `L`. -/
noncomputable def textbookEElementaryHullAmbient
    (kappa x : LCarrier.{u}) : LCarrier.{u} :=
  stageLCarrier (textbookEElementaryHullTheta kappa x)

/--
The initial textbook hull seed is exactly `kappa union {x}`.  The existing
`adjoinLCarrier` definition writes the binary union in the opposite order,
which is extensionally the same set.
-/
def textbookEElementaryHullSeed
    (kappa x : LCarrier.{u}) : LCarrier.{u} :=
  adjoinLCarrier kappa x





/-! ## The full elementary hull -/

/-- The internal omega union of all simultaneous textbook E witness stages. -/
noncomputable def textbookEElementaryHull
    (kappa x : LCarrier.{u}) : LCarrier.{u} :=
  textbookEUniformWitnessOmegaUnion
    (textbookEElementaryHullSeed kappa x)
    (textbookEElementaryHullAmbient kappa x)











/-! ## Condensation and the explicit cardinal-smallness interface -/







end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_TextbookEElementaryHull


/- Source module: Solutions.Work_CUGCH_InternalBinaryUnionInjection -/
section GCHSource_Work_CUGCH_InternalBinaryUnionInjection
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Internally represented injections for binary unions

The standard cardinal estimate for one Skolem step uses the fact that a
finite union of sets of size at most an infinite cardinal again has size at
most that cardinal.  This file proves the binary case with an actual
Kuratowski graph in `L`.

The two summands are tagged by the internal natural numbers zero and one.
The resulting graph maps the union into `kappa x kappa`; a supplied internal
square-absorption graph then gives the desired injection into `kappa`.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-- The disjointly tagged relation used to inject a binary union.  Elements
of the left set use the left graph and tag zero.  Elements belonging only to
the right set use the right graph and tag one. -/
def TaggedUnionInjectionRel {A : Type u} (E : A -> A -> Prop)
    (left right first second zero one input output : A) : Prop :=
  (E input left /\
      exists image : A,
        GraphValue E first input image /\
          IsKuratowskiPairOf E output zero image) \/
    (Not (E input left) /\ E input right /\
      exists image : A,
        GraphValue E second input image /\
          IsKuratowskiPairOf E output one image)

/-- Layout `(left,right,first,second,zero,one,input,output)`. -/
def taggedUnionInjectionFormula : FOFormula 8 :=
  .disj
    (.conj
      (.mem (6 : Fin 8) (0 : Fin 8))
      (.ex <| .conj
        (graphValueAt
          (2 : Fin 8).castSucc (6 : Fin 8).castSucc (Fin.last 8))
        (kuratowskiPairAt
          (7 : Fin 8).castSucc (4 : Fin 8).castSucc (Fin.last 8))))
    (.conj
      (.neg (.mem (6 : Fin 8) (0 : Fin 8)))
      (.conj
        (.mem (6 : Fin 8) (1 : Fin 8))
        (.ex <| .conj
          (graphValueAt
            (3 : Fin 8).castSucc (6 : Fin 8).castSucc (Fin.last 8))
          (kuratowskiPairAt
            (7 : Fin 8).castSucc (5 : Fin 8).castSucc (Fin.last 8)))))

 theorem taggedUnionInjection_assignment
    (left right first second zero one input output image : LCarrier.{u}) :
    snoc ![left, right, first, second, zero, one, input, output] image =
      ![left, right, first, second, zero, one, input, output, image] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_taggedUnionInjectionFormula
    (left right first second zero one input output : LCarrier.{u}) :
    FOFormula.Satisfies LMem taggedUnionInjectionFormula
        ![left, right, first, second, zero, one, input, output] <->
      TaggedUnionInjectionRel LMem
        left right first second zero one input output := by
  simp only [taggedUnionInjectionFormula, FOFormula.satisfies_disj,
    FOFormula.Satisfies, satisfies_graphValueAt,
    satisfies_kuratowskiPairAt, TaggedUnionInjectionRel]
  apply or_congr
  · apply and_congr Iff.rfl
    apply exists_congr
    intro image
    rw [taggedUnionInjection_assignment]
    rfl
  · apply and_congr Iff.rfl
    apply and_congr Iff.rfl
    apply exists_congr
    intro image
    rw [taggedUnionInjection_assignment]
    rfl

 theorem taggedUnionInjection_relation_assignment
    (left right first second zero one input output : LCarrier.{u}) :
    snoc (snoc ![left, right, first, second, zero, one] input) output =
      ![left, right, first, second, zero, one, input, output] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_taggedUnionInjectionRelation
    (left right first second zero one input output : LCarrier.{u}) :
    FOFormula.Satisfies LMem taggedUnionInjectionFormula
        (snoc (snoc ![left, right, first, second, zero, one] input) output) <->
      TaggedUnionInjectionRel LMem
        left right first second zero one input output := by
  rw [taggedUnionInjection_relation_assignment,
    satisfies_taggedUnionInjectionFormula]





end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalBinaryUnionInjection


