-- Prove2me | Definitions.Def_Yukon_168b3f56a3214d856e63e24f
-- name    : Yukon_168b3f56a3214d856e63e24f
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:12:09.978443+00:00
-- url     : https://prove2.me/theorems/60166a73-0b46-424c-8d18-df18f4e745a8
-- title:
--   YukonModule.VCVio.OracleComp.SimSemantics.WriterT.Basic.part0
-- statement:
--   Source module VCVio.OracleComp.SimSemantics.WriterT.Basic.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/OracleComp/SimSemantics/WriterT/Basic.lean
--
--   yukon-proof-operation:65b46598254a65a840e663aa1cc73c897f05fab02f0c3100d6fb367c53640414
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246NjViNDY1OTgyNTRhNjVhODQwZTY2M2FhMWNjNzNjODk3ZjA1ZmFiMDJmMGMzMTAwZDZmYjM2N2M1MzY0MDQxNCIsImhhc2giOiIzZDQxMzY0YmY4NWQ0ODk3Y2NhYjk1MzU2ZTE3OTIzZGE2ZmRjMjNiMzNhN2NlOGY4MTE0MTRmMzgyZjFjZGFjIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl8xNjhiM2Y1NmEzMjE0ZDg1NmU2M2UyNGYiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Definitions.Def_Yukon_2b5744019605f484379c669d

public import Definitions.Def_Yukon_4231d0ef2a5eb8af03e94595



public import Batteries.Control.AlternativeMonad
public import Mathlib.Order.Basic
public import Mathlib.Control.Monad.Writer
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Init
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Vector.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Batteries.Control.OptionT
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Init
public import Lean.Message
public import Batteries.Tactic.Lint.Basic
public import Batteries.Tactic.Lint
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.MvPolynomial.Eval
meta import Definitions.Def_Yukon_4231d0ef2a5eb8af03e94595
meta import Definitions.Def_Yukon_2b5744019605f484379c669d
set_option backward.isDefEq.respectTransparency.types false
/-!
# Simulation through `WriterT` Handlers

Combinators and output-preservation lemmas for writer-instrumented query implementations.
The combinators here mirror the StateT/ReaderT versions in
`SimSemantics/StateT/Basic.lean` and `SimSemantics/ReaderT/Basic.lean`.
-/

@[expose] public section

open OracleSpec Function Prod

universe u v w x

open scoped OracleSpec.PrimitiveQuery

namespace QueryImpl

/-- Given implementations for oracles in `spec₁` and `spec₂` in terms of writer monads for
two different log monoids `ω₁` and `ω₂`, implement the combined set `spec₁ + spec₂` in terms
of the product monoid `ω₁ × ω₂`. Each side leaves the other component at the identity. -/
def parallelWriterT {ι₁ : Type u} {ι₂ : Type v}
    {spec₁ : OracleSpec.{u, w} ι₁} {spec₂ : OracleSpec.{v, w} ι₂}
    {m : Type w → Type x} [Functor m] {ω₁ ω₂ : Type w} [Monoid ω₁] [Monoid ω₂]
    (impl₁ : QueryImpl spec₁ (WriterT ω₁ m))
    (impl₂ : QueryImpl spec₂ (WriterT ω₂ m)) :
    QueryImpl (spec₁ + spec₂) (WriterT (ω₁ × ω₂) m)
  | .inl t => WriterT.mk <| Prod.map id (·, (1 : ω₂)) <$> (impl₁ t).run
  | .inr t => WriterT.mk <| Prod.map id ((1 : ω₁), ·) <$> (impl₂ t).run

/-- Indexed version of `QueryImpl.parallelWriterT`. Each query for index `t` writes into the
`t`-th component of the pi-product `(t : τ) → ω t`, leaving every other component at the
identity. Note that `m` cannot vary with `t`. -/
def sigmaWriterT {τ : Type} [DecidableEq τ] {ι : τ → Type v}
    {spec : (t : τ) → OracleSpec.{v, w} (ι t)}
    {m : Type w → Type x} [Functor m] {ω : τ → Type w} [(t : τ) → Monoid (ω t)]
    (impl : (t : τ) → QueryImpl (spec t) (WriterT (ω t) m)) :
    QueryImpl (OracleSpec.sigma spec) (WriterT ((t : τ) → ω t) m)
  | ⟨t, q⟩ => WriterT.mk <| Prod.map id (Function.update (fun _ => 1) t) <$> (impl t q).run

/-- Reassociate a nested writer transformer into one product log.

The outer log is the first component of the product; the inner/base log is the second. This
is the writer-transformer analogue of `flattenStateT`. Requires `[Monoid ω₂]` to lift the
inner writer's run; the resulting `WriterT (ω₁ × ω₂) m` carries both logs as a product. -/
def flattenWriterT {ι : Type _} {spec : OracleSpec ι}
    {m : Type u → Type v} [Monad m] {ω₁ ω₂ : Type u} [Monoid ω₂]
    (impl : QueryImpl spec (WriterT ω₁ (WriterT ω₂ m))) :
    QueryImpl spec (WriterT (ω₁ × ω₂) m) := fun t =>
  WriterT.mk <| do
    let ((a, w₁), w₂) ← (impl t).run.run
    pure (a, (w₁, w₂))

end QueryImpl

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec ι} {α : Type u} {ω : Type u} [Monoid ω]

/-- Taking the first component of the WriterT output recovers the original computation,
when the query implementation preserves the underlying oracle behavior (hso). -/
lemma fst_map_writerT_run_simulateQ
    {so : QueryImpl spec (WriterT ω (OracleComp spec))}
    (hso : ∀ t, fst <$> (so t).run = liftM (query t))
    (oa : OracleComp spec α) : fst <$> (simulateQ so oa).run = oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [WriterT.run_pure]
  | query_bind t oa ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, WriterT.run_bind, map_bind]
    refine (bind_congr fun ⟨a, w₁⟩ => ?_).trans (by rw [← bind_map_left, hso t])
    simpa [← LawfulFunctor.comp_map] using ih a

/-- Running a writer-instrumented simulation preserves the failure probability of the
underlying computation. -/
lemma probFailure_writerT_run_simulateQ [IsUniformSpec spec]
    {so : QueryImpl spec (WriterT ω (OracleComp spec))}
    (oa : OracleComp spec α) : Pr[⊥ | (simulateQ so oa).run] = Pr[⊥ | oa] := by
  induction oa using OracleComp.inductionOn <;> simp

/-- A writer-instrumented simulation never fails iff the underlying computation never fails. -/
lemma NeverFail_writerT_run_simulateQ_iff [IsUniformSpec spec]
    {so : QueryImpl spec (WriterT ω (OracleComp spec))}
    (oa : OracleComp spec α) :
    NeverFail ((simulateQ so oa).run : OracleComp spec _) ↔
      NeverFail (oa : OracleComp spec α) := by
  rw [← probFailure_eq_zero_iff, ← probFailure_eq_zero_iff,
    probFailure_writerT_run_simulateQ oa]

end OracleComp


