-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13ReductionClassifier_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13ReductionClassifier_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T18:14:41.226845+00:00
-- url     : https://prove2.me/theorems/c3d03a75-8203-400b-9465-9b5b89c9f6de
-- title:
--   FLT.Assumptions.MazurProof.N13ReductionClassifier source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13ReductionClassifier

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13ReductionClassifier
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13AbelFiberTwoModel_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordFullKummerTwoSurjective_p2

set_option autoImplicit false




/-!
# A set-valued finite reduction target for N13

Reduction injectivity does not require a group law on the nineteen-element
special Abel quotient.  It is enough to define a subgroup `K` of the rational
Picard group and a set-valued classifier whose fibres are exactly the cosets
of `K`.  The quotient group `G ⧸ K` then embeds into the finite classifier
type.

This file isolates that purely structural passage.  The remaining fixed-curve
geometry must construct the classifier and prove its exactness.
-/

namespace MazurProof.N13ReductionClassifier

noncomputable section

open N18RouteC.Separated

universe u v

/-- A set-valued classifier whose fibres are precisely the cosets of a
subgroup.  No operation on `S` is assumed. -/
structure Data (G : Type u) (S : Type v) [AddCommGroup G] where
  kernel : AddSubgroup G
  classify : G → S
  exact : ∀ P Q : G,
    classify P = classify Q ↔ P - Q ∈ kernel

namespace Data

variable {G : Type u} {S : Type v} [AddCommGroup G]

/-- The genuine additive reduction target: the actual image quotient. -/
abbrev Target (D : Data G S) : Type u :=
  G ⧸ D.kernel

/-- The quotient map onto the actual image target. -/
def red (D : Data G S) : G →+ D.Target :=
  QuotientAddGroup.mk' D.kernel

theorem red_surjective (D : Data G S) :
    Function.Surjective D.red :=
  QuotientAddGroup.mk'_surjective D.kernel

@[simp] theorem red_eq_zero_iff (D : Data G S) (P : G) :
    D.red P = 0 ↔ P ∈ D.kernel := by
  simp [red]

@[simp] theorem red_ker (D : Data G S) :
    D.red.ker = D.kernel := by
  ext P
  simp

theorem classify_eq_zero_iff (D : Data G S) (P : G) :
    D.classify P = D.classify 0 ↔ P ∈ D.kernel := by
  simpa using D.exact P 0

private theorem classify_respects_leftRel
    (D : Data G S) (P Q : G)
    (hPQ : QuotientAddGroup.leftRel D.kernel P Q) :
    D.classify P = D.classify Q := by
  apply (D.exact P Q).2
  have hQP : -P + Q ∈ D.kernel :=
    QuotientAddGroup.leftRel_apply.mp hPQ
  have hPQ' := D.kernel.neg_mem hQP
  simpa [sub_eq_add_neg, add_comm] using hPQ'

/-- The set-valued classifier descends to the actual image quotient. -/
def quotientClassify (D : Data G S) : D.Target → S :=
  fun z =>
    Quotient.liftOn' z D.classify D.classify_respects_leftRel

@[simp] theorem quotientClassify_red
    (D : Data G S) (P : G) :
    D.quotientClassify (D.red P) = D.classify P :=
  QuotientAddGroup.quotient_liftOn_mk
    D.classify D.classify_respects_leftRel P

theorem quotientClassify_injective (D : Data G S) :
    Function.Injective D.quotientClassify := by
  intro x y
  revert y
  refine QuotientAddGroup.induction_on x (fun P y => ?_)
  refine QuotientAddGroup.induction_on y (fun Q hxy => ?_)
  apply QuotientAddGroup.eq.mpr
  have hclass : D.classify P = D.classify Q := by
    simpa only [quotientClassify,
      QuotientAddGroup.quotient_liftOn_mk] using hxy
  have hPQ : P - Q ∈ D.kernel :=
    (D.exact P Q).1 hclass
  have hQP := D.kernel.neg_mem hPQ
  simpa [sub_eq_add_neg, add_comm] using hQP

/-- The actual image quotient as a subset of the special classifier set. -/
def quotientEmbedding (D : Data G S) : D.Target ↪ S where
  toFun := D.quotientClassify
  inj' := D.quotientClassify_injective

noncomputable instance targetFinite
    (D : Data G S) [Finite S] :
    Finite D.Target :=
  Finite.of_injective D.quotientClassify
    D.quotientClassify_injective

/-- Finite classification and a separated kernel close the reduction
argument. -/
theorem reduction_injective
    (D : Data G S) [Finite S]
    (twoSurjective :
      N13TwoAdicEndgame.TwoSurjective G)
    (separated : NSeparated D.red.ker 2) :
    Function.Injective D.red :=
  N13TwoAdicEndgame.reduction_injective_of_finite_target
    D.red D.red_surjective twoSurjective separated

end Data

abbrev G : Type :=
  N13MumfordFullKummerTwoSurjective.G

abbrev SpecialSet : Type :=
  N13AbelFiberTwoModel.PicTwoSetModel

/-- N13 specialization of the abstract classifier endpoint. -/
theorem n13_reduction_injective
    (D : Data G SpecialSet)
    (separated : NSeparated D.red.ker 2) :
    Function.Injective D.red :=
  D.reduction_injective
    N13MumfordFullKummerTwoSurjective.twoSurjective separated

end

end MazurProof.N13ReductionClassifier


