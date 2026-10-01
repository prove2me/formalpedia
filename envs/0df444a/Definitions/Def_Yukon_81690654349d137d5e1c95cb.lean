-- Prove2me | Definitions.Def_Yukon_81690654349d137d5e1c95cb
-- name    : Yukon_81690654349d137d5e1c95cb
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:15:48.793109+00:00
-- url     : https://prove2.me/theorems/75f0025d-0ac4-4974-886b-7402bacf9966
-- title:
--   YukonModule.VCVio.OracleComp.Traversal.part0
-- statement:
--   Source module VCVio.OracleComp.Traversal.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/OracleComp/Traversal.lean
--
--   yukon-proof-operation:33f555f5f50f959e601ed2c07c985e850b979eb1b38ce310932da9bcd916e3fb
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246MzNmNTU1ZjVmNTBmOTU5ZTYwMWVkMmMwN2M5ODVlODUwYjk3OWViMWIzOGNlMzEwOTMyZGE5YmNkOTE2ZTNmYiIsImhhc2giOiJkNGU0OGEyZGNlZTkzZTQxMjAyZDAxMjIzNzgzYWZiNjQ4NzJiY2I0OTZmYjcyOWI2NWNhMzgzNWRjNDUzNGRmIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl84MTY5MDY1NDM0OWQxMzdkNWUxYzk1Y2IiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import Definitions.Def_Yukon_2b5744019605f484379c669d

public import Definitions.Def_Yukon_6aff9017218cbc4c7dc17172



public import Batteries.Tactic.Lint
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Init
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Init
public import Lean.Message
public import Batteries.Tactic.Lint.Basic
public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Vector.Defs
public import Mathlib.Data.Finset.Card
public import Batteries.Control.OptionT
public import Batteries.Control.AlternativeMonad
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.MvPolynomial.Eval
meta import Definitions.Def_Yukon_6aff9017218cbc4c7dc17172
meta import Definitions.Def_Yukon_2b5744019605f484379c669d
set_option backward.isDefEq.respectTransparency.types false
/-!
# Traversing Possible Paths of a Computation

This file defines structural predicates for checking whether all or some reachable paths of an
`OracleComp` satisfy predicates on query nodes and final outputs, relative to a chosen set of
possible oracle outputs.

The predicates are phrased in terms of `PFunctor.FreeM.Cursor`: a cursor is a typed path prefix
into the underlying free-monad tree, so quantifying over cursors whose recorded directions stay
within the possible outputs simultaneously reaches every demanded query node (via non-terminal
cursors) and every reachable final output (via terminal cursors). The generic PolyFun predicates
`PFunctor.TraceList.DirectionsWithin` and `PFunctor.FreeM.RootSatisfies` express the trace filter
and the demand made by the selected residual root.

It also connects those structural predicates to the denotational set `supportWhen`, so proofs can
move cleanly between the syntax-level traversal view and the reachable-output view.
-/

@[expose] public section

open OracleSpec

universe u v

open scoped OracleSpec.PrimitiveQuery

namespace OracleComp

open PFunctor

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {α β γ : Type v}

/-- Given that oracle outputs are bounded by `possibleOutputs`, every reachable query input in the
computation satisfies `queryPred`, and every reachable pure output satisfies `outputPred`.

Phrased as: every cursor into the computation whose recorded directions stay within
`possibleOutputs` satisfies its root demand (`PFunctor.FreeM.RootSatisfies`). Non-terminal cursors
reach every demanded query node — including nodes with no possible continuation below them —
while terminal cursors reach every possible final output. -/
def allPathsSatisfy (queryPred : spec.Domain → Prop) (outputPred : α → Prop)
    (possibleOutputs : (x : spec.Domain) → Set (spec.Range x))
    (oa : OracleComp spec α) : Prop :=
  ∀ c : PFunctor.FreeM.Cursor oa,
    TraceList.DirectionsWithin possibleOutputs c.trace →
      FreeM.RootSatisfies queryPred outputPred c.residual

/-- Given that oracle outputs are bounded by `possibleOutputs`, some reachable query input in the
computation satisfies `queryPred`, or some reachable pure output satisfies `outputPred`.

Phrased as: some cursor into the computation whose recorded directions stay within
`possibleOutputs` satisfies its root demand (`PFunctor.FreeM.RootSatisfies`). -/
def somePathSatisfies (queryPred : spec.Domain → Prop) (outputPred : α → Prop)
    (possibleOutputs : (x : spec.Domain) → Set (spec.Range x))
    (oa : OracleComp spec α) : Prop :=
  ∃ c : PFunctor.FreeM.Cursor oa,
    TraceList.DirectionsWithin possibleOutputs c.trace ∧
      FreeM.RootSatisfies queryPred outputPred c.residual

/-- Output-only view of [`OracleComp.allPathsSatisfy`]: every output reachable under
`possibleOutputs` satisfies `outputPred`. -/
def allOutputsSatisfyWhen (outputPred : α → Prop)
    (possibleOutputs : (x : spec.Domain) → Set (spec.Range x))
    (oa : OracleComp spec α) : Prop :=
  allPathsSatisfy (fun _ => True) outputPred possibleOutputs oa

/-- Output-only view of [`OracleComp.somePathSatisfies`]: some output reachable under
`possibleOutputs` satisfies `outputPred`. -/
def someOutputSatisfiesWhen (outputPred : α → Prop)
    (possibleOutputs : (x : spec.Domain) → Set (spec.Range x))
    (oa : OracleComp spec α) : Prop :=
  somePathSatisfies (fun _ => False) outputPred possibleOutputs oa

variable {queryPred : spec.Domain → Prop} {outputPred : α → Prop}
  {possibleOutputs : (x : spec.Domain) → Set (spec.Range x)}

@[simp]
lemma allPathsSatisfy_pure (x : α) :
    allPathsSatisfy queryPred outputPred possibleOutputs (pure x : OracleComp spec α) =
      outputPred x := by
  refine propext ⟨fun h => h (PFunctor.FreeM.Cursor.root _) (by simp), fun h c hw => ?_⟩
  obtain ⟨res, sp⟩ := c
  cases sp
  exact h

@[simp]
lemma somePathSatisfies_pure (x : α) :
    somePathSatisfies queryPred outputPred possibleOutputs (pure x : OracleComp spec α) =
      outputPred x := by
  refine propext ⟨fun ⟨c, _, hc⟩ => ?_, fun h => ⟨PFunctor.FreeM.Cursor.root _, by simp, h⟩⟩
  obtain ⟨res, sp⟩ := c
  cases sp
  exact hc

@[simp]
lemma allPathsSatisfy_query_bind (q : spec.Domain)
    (oa : spec.Range q → OracleComp spec α) :
    allPathsSatisfy queryPred outputPred possibleOutputs
        ((query q : OracleComp spec _) >>= oa) ↔
      queryPred q ∧
        ∀ x ∈ possibleOutputs q,
          allPathsSatisfy queryPred outputPred possibleOutputs (oa x) := by
  change allPathsSatisfy queryPred outputPred possibleOutputs
      (PFunctor.FreeM.liftBind q oa) ↔ _
  constructor
  · intro h
    refine ⟨h (PFunctor.FreeM.Cursor.root _) (by simp), fun u hu c hc => ?_⟩
    exact h (PFunctor.FreeM.Cursor.down u c)
      (by
        simp only [PFunctor.FreeM.Cursor.trace_down, TraceList.directionsWithin_cons]
        exact ⟨hu, hc⟩)
  · rintro ⟨hq, h⟩ ⟨res, sp⟩ hw
    cases sp with
    | root => exact hq
    | down answer tail =>
        simp only [show (⟨res, PFunctor.FreeM.Cursor.Spine.down answer tail⟩ :
          PFunctor.FreeM.Cursor _) = PFunctor.FreeM.Cursor.down answer ⟨res, tail⟩ from rfl,
          PFunctor.FreeM.Cursor.trace_down, TraceList.directionsWithin_cons] at hw ⊢
        exact h answer hw.1 ⟨res, tail⟩ hw.2

@[simp]
lemma somePathSatisfies_query_bind (q : spec.Domain)
    (oa : spec.Range q → OracleComp spec α) :
    somePathSatisfies queryPred outputPred possibleOutputs
        ((query q : OracleComp spec _) >>= oa) ↔
      queryPred q ∨
        ∃ x ∈ possibleOutputs q,
          somePathSatisfies queryPred outputPred possibleOutputs (oa x) := by
  change somePathSatisfies queryPred outputPred possibleOutputs
      (PFunctor.FreeM.liftBind q oa) ↔ _
  constructor
  · rintro ⟨⟨res, sp⟩, hw, hc⟩
    cases sp with
    | root => exact Or.inl hc
    | down answer tail =>
        simp only [show (⟨res, PFunctor.FreeM.Cursor.Spine.down answer tail⟩ :
          PFunctor.FreeM.Cursor _) = PFunctor.FreeM.Cursor.down answer ⟨res, tail⟩ from rfl,
          PFunctor.FreeM.Cursor.trace_down, TraceList.directionsWithin_cons] at hw hc
        exact Or.inr ⟨answer, hw.1, ⟨res, tail⟩, hw.2, hc⟩
  · rintro (hq | ⟨u, hu, c, hw, hc⟩)
    · exact ⟨PFunctor.FreeM.Cursor.root _, by simp, hq⟩
    · refine ⟨PFunctor.FreeM.Cursor.down u c, ?_, hc⟩
      simp only [PFunctor.FreeM.Cursor.trace_down, TraceList.directionsWithin_cons]
      exact ⟨hu, hw⟩

/-- Every output of `oa` reachable under `possibleOutputs` satisfies `outputPred` exactly when
`outputPred` holds throughout `oa.supportWhen possibleOutputs`. -/
lemma allOutputsSatisfyWhen_iff_supportWhen (outputPred : α → Prop)
    (possibleOutputs : (x : spec.Domain) → Set (spec.Range x)) (oa : OracleComp spec α) :
    allOutputsSatisfyWhen outputPred possibleOutputs oa ↔
      ∀ x ∈ oa.supportWhen possibleOutputs, outputPred x := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [OracleComp.allOutputsSatisfyWhen, OracleComp.supportWhen_pure]
  | query_bind q oa ih =>
      simp only [OracleComp.allOutputsSatisfyWhen, OracleComp.allPathsSatisfy_query_bind,
        true_and, OracleComp.supportWhen_query_bind, Set.mem_iUnion, exists_prop] at ih ⊢
      grind

/-- Some output of `oa` reachable under `possibleOutputs` satisfies `outputPred` exactly when
`outputPred` holds at some point of `oa.supportWhen possibleOutputs`. -/
lemma someOutputSatisfiesWhen_iff_supportWhen (outputPred : α → Prop)
    (possibleOutputs : (x : spec.Domain) → Set (spec.Range x)) (oa : OracleComp spec α) :
    someOutputSatisfiesWhen outputPred possibleOutputs oa ↔
      ∃ x ∈ oa.supportWhen possibleOutputs, outputPred x := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [OracleComp.someOutputSatisfiesWhen, OracleComp.supportWhen_pure]
  | query_bind q oa ih =>
      simp only [OracleComp.someOutputSatisfiesWhen, OracleComp.somePathSatisfies_query_bind,
        false_or, OracleComp.supportWhen_query_bind, Set.mem_iUnion, exists_prop] at ih ⊢
      grind

/-- A bind satisfies a universal path property exactly when every path of the first computation
leads to a continuation that also satisfies that path property. -/
@[simp]
lemma allPathsSatisfy_bind_iff
    (queryPred : spec.Domain → Prop) (outputPred : β → Prop)
    (possibleOutputs : (x : spec.Domain) → Set (spec.Range x))
    (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    allPathsSatisfy queryPred outputPred possibleOutputs (oa >>= ob) ↔
      allPathsSatisfy queryPred
        (fun x => allPathsSatisfy queryPred outputPred possibleOutputs (ob x))
        possibleOutputs oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [pure_bind]
  | query_bind q oa ih => simp [monad_norm, OracleComp.allPathsSatisfy_query_bind, ih]

/-- A bind satisfies an existential path property exactly when either the first computation
already satisfies it on some path, or one reachable continuation does. -/
@[simp]
lemma somePathSatisfies_bind_iff
    (queryPred : spec.Domain → Prop) (outputPred : β → Prop)
    (possibleOutputs : (x : spec.Domain) → Set (spec.Range x))
    (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    somePathSatisfies queryPred outputPred possibleOutputs (oa >>= ob) ↔
      somePathSatisfies queryPred
        (fun x => somePathSatisfies queryPred outputPred possibleOutputs (ob x))
        possibleOutputs oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [pure_bind]
  | query_bind q oa ih => simp [monad_norm, OracleComp.somePathSatisfies_query_bind, ih]

/-- Output-only specialization of [`OracleComp.allPathsSatisfy_bind_iff`]. -/
@[simp]
lemma allOutputsSatisfyWhen_bind_iff (outputPred : β → Prop)
    (possibleOutputs : (x : spec.Domain) → Set (spec.Range x))
    (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    (oa >>= ob).allOutputsSatisfyWhen outputPred possibleOutputs ↔
      oa.allOutputsSatisfyWhen
        (fun x => (ob x).allOutputsSatisfyWhen outputPred possibleOutputs)
        possibleOutputs := by
  simp only [allOutputsSatisfyWhen, allPathsSatisfy_bind_iff]

/-- Output-only specialization of [`OracleComp.somePathSatisfies_bind_iff`]. -/
@[simp]
lemma someOutputSatisfiesWhen_bind_iff (outputPred : β → Prop)
    (possibleOutputs : (x : spec.Domain) → Set (spec.Range x))
    (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    (oa >>= ob).someOutputSatisfiesWhen outputPred possibleOutputs ↔
      oa.someOutputSatisfiesWhen
        (fun x => (ob x).someOutputSatisfiesWhen outputPred possibleOutputs)
        possibleOutputs := by
  simp only [someOutputSatisfiesWhen, somePathSatisfies_bind_iff]

/-- Output-only bind rule phrased directly in terms of reachable intermediate outputs. -/
lemma allOutputsSatisfyWhen_bind_iff_supportWhen (outputPred : β → Prop)
    (possibleOutputs : (x : spec.Domain) → Set (spec.Range x))
    (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    (oa >>= ob).allOutputsSatisfyWhen outputPred possibleOutputs ↔
      ∀ x ∈ oa.supportWhen possibleOutputs,
        (ob x).allOutputsSatisfyWhen outputPred possibleOutputs := by
  rw [OracleComp.allOutputsSatisfyWhen_bind_iff]
  simp [OracleComp.allOutputsSatisfyWhen_iff_supportWhen]

/-- Existential output bind rule phrased directly in terms of reachable intermediate outputs. -/
lemma someOutputSatisfiesWhen_bind_iff_supportWhen (outputPred : β → Prop)
    (possibleOutputs : (x : spec.Domain) → Set (spec.Range x))
    (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    (oa >>= ob).someOutputSatisfiesWhen outputPred possibleOutputs ↔
      ∃ x ∈ oa.supportWhen possibleOutputs,
        (ob x).someOutputSatisfiesWhen outputPred possibleOutputs := by
  rw [OracleComp.someOutputSatisfiesWhen_bind_iff]
  simp [OracleComp.someOutputSatisfiesWhen_iff_supportWhen]

end OracleComp


