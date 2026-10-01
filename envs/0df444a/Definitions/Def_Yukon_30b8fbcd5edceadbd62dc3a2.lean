-- Prove2me | Definitions.Def_Yukon_30b8fbcd5edceadbd62dc3a2
-- name    : Yukon_30b8fbcd5edceadbd62dc3a2
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:27:29.56701+00:00
-- url     : https://prove2.me/theorems/a1513b2b-e2f9-457d-815e-34c0729df926
-- title:
--   YukonModule.VCVio.OracleComp.QueryTracking.Tracing.part0
-- statement:
--   Source module VCVio.OracleComp.QueryTracking.Tracing.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/OracleComp/QueryTracking/Tracing.lean
--
--   yukon-proof-operation:8da9bd5a5ec0dea6ae313ccbce634e367c334e2ef1b74a84964c7a60254f823d
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiOTNhZjQwMWU2NTE1MmM0YTA3MGRiMGE4ZDVhMDczMzZhMjQyOTU2YzkxZjIyNTliNjVhYWQ3NzkxZDBlMzkxMiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOjhkYTliZDVhNWVjMGRlYTZhZTMxM2NjYmNlNjM0ZTM2N2MzMzRlMmVmMWI3NGE4NDk2NGM3YTYwMjU0ZjgyM2QiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8zMGI4ZmJjZDVlZGNlYWRiZDYyZGMzYTIiLCJ2IjoyfQ]

/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Definitions.Def_Yukon_3a940f7a9ed7ceff2d5cc7d0

public import Definitions.Def_Yukon_be0ea4aaa74139969f477ed4

public import Definitions.Def_Yukon_2b5744019605f484379c669d

public import Definitions.Def_Yukon_168b3f56a3214d856e63e24f

public import Definitions.Def_Yukon_31339f69d701f2d4fdaf823f

public import Definitions.Def_Yukon_4231d0ef2a5eb8af03e94595



public import Batteries.Control.AlternativeMonad
public import Mathlib.Order.Basic
public import Mathlib.Control.Monad.Writer
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Init
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Pi.Basic
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
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.FinEnum
public import Init.Data.UInt.Lemmas
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Data.List.Sym
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Real.ENatENNReal
meta import Definitions.Def_Yukon_31339f69d701f2d4fdaf823f
meta import Definitions.Def_Yukon_4231d0ef2a5eb8af03e94595
meta import Definitions.Def_Yukon_2b5744019605f484379c669d
meta import Definitions.Def_Yukon_3a940f7a9ed7ceff2d5cc7d0
meta import Definitions.Def_Yukon_be0ea4aaa74139969f477ed4
meta import Definitions.Def_Yukon_168b3f56a3214d856e63e24f
set_option backward.isDefEq.respectTransparency.types false
/-!
# Generic Trace Instrumentation for Query Implementations

Two primitive ways to attach a writer-valued trace to a `QueryImpl`. Each
comes in two flavours, mirroring Mathlib's two `Monad (WriterT ω M)` instances:

* `[Monoid ω]` flavour (`withTrace` / `withTraceBefore`): the trace lives in
  an arbitrary monoid `ω` and accumulates via `1` and `*`. This is what
  `QueryImpl.withCost` (`CountingOracle.lean`) uses, with `ω = QueryCount ι`
  (pointwise additive monoid).

* `[EmptyCollection ω] [Append ω]` flavour (`withTraceAppend` /
  `withTraceAppendBefore`): the trace accumulates via `∅` and `++`, matching
  the Append-based `Monad (WriterT ω m)` instance. This is what
  `QueryImpl.withLogging` (`LoggingOracle.lean`) uses, with
  `ω = QueryLog spec` (a list of query/response pairs).

The two flavours are mathematically the same (a free monoid view vs. an
append-list view), but they correspond to *different* `Monad (WriterT ω m)`
instances and Lean's resolver picks whichever one is unambiguously available.
We expose both so neither of `QueryCount`/`QueryLog` has to switch its
underlying writer interpretation.

For each flavour, "Before" emits `traceFn t` *before* running the handler
(so a handler failure still records the trace), while the bare version emits
`traceFn t u` *after* the handler returns response `u` (so a failure skips
the trace).

Concretely:

* `withCost = withTraceBefore` (the cost ignores the response).
* `withLogging so = withTraceAppend so (fun t u => [⟨t, u⟩])` (the log records
  the response, hence "after" semantics).

The generic lemmas (output marginal, failure probability, `NeverFail`
equivalence, `evalDist` / `support` / `probOutput` bridges) flow downstream
automatically.

## Connection to `Control.Trace`

The trace function `traceFn : (t : spec.Domain) → spec.Range t → ω` is a curried
form of `Idx spec.toPFunctor → ω`, which is precisely
`Control.Trace ω (Idx spec.toPFunctor)`. The `Tracing` API is therefore the
oracle-level counterpart of the abstract `Control.Trace` / `PFunctor.Trace`
infrastructure in `ToMathlib`.
-/

@[expose] public section

open OracleSpec OracleComp

universe u v w

variable {ι : Type u} {spec : OracleSpec ι} {α β γ : Type u}

namespace QueryImpl

variable {m : Type u → Type v} [Monad m]

/-! ### `withTraceBefore`: response-independent trace, recorded before handler -/

section withTraceBefore

variable {ω : Type u} [Monoid ω]

/-- Wrap an oracle implementation so that each query records `traceFn t` in
the writer `ω` *before* running the handler. The trace value depends only on
the query, so a failure inside the handler still leaves the trace recorded. -/
def withTraceBefore (so : QueryImpl spec m) (traceFn : spec.Domain → ω) :
    QueryImpl spec (WriterT ω m) :=
  so.preInsert fun t => tell (traceFn t)

@[simp, grind =]
lemma withTraceBefore_apply (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (t : spec.Domain) :
    so.withTraceBefore traceFn t = (do tell (traceFn t); so t) := rfl

lemma fst_map_run_withTraceBefore [LawfulMonad m]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    Prod.fst <$> (simulateQ (so.withTraceBefore traceFn) mx).run = simulateQ so mx :=
  proj_simulateQ_preInsert so (fun t => tell (traceFn t))
    (proj := fun {γ} (x : WriterT ω m γ) => Prod.fst <$> x.run)
    WriterT.fst_map_run_pure WriterT.fst_map_run_bind
    (fun t => by simp) mx

/-- A "before"-style trace preserves failure probability for any base monad with
`MonadLiftT m SPMF`: instrumenting with `withTraceBefore` does not change the
probability of failure. -/
lemma probFailure_run_simulateQ_withTraceBefore [LawfulMonad m]
    [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    Pr[⊥ | (simulateQ (so.withTraceBefore traceFn) mx).run] = Pr[⊥ | simulateQ so mx] := by
  rw [← fst_map_run_withTraceBefore so traceFn mx, probFailure_map]

lemma neverFail_run_simulateQ_withTraceBefore_iff [LawfulMonad m]
    [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    NeverFail (simulateQ (so.withTraceBefore traceFn) mx).run ↔ NeverFail (simulateQ so mx) := by
  simp only [neverFail_iff, probFailure_run_simulateQ_withTraceBefore]

@[deprecated (since := "2026-06-25")]
alias NeverFail_run_simulateQ_withTraceBefore_iff := neverFail_run_simulateQ_withTraceBefore_iff

/-- When every query traces to the monoid identity `1`, `withTraceBefore` is a
no-op up to pairing with `1`. -/
@[simp]
lemma run_simulateQ_withTraceBefore_const_one [LawfulMonad m]
    (so : QueryImpl spec m) (mx : OracleComp spec α) :
    (simulateQ (so.withTraceBefore (fun _ => (1 : ω))) mx).run =
      (·, 1) <$> simulateQ so mx := by
  induction mx using OracleComp.inductionOn <;> simp [*]

/-! #### `evalDist` / `probOutput` / `support` bridges for `withTraceBefore` -/

lemma evalDist_fst_run_withTraceBefore [LawfulMonad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    𝒟[Prod.fst <$> (simulateQ (so.withTraceBefore traceFn) mx).run] =
      𝒟[simulateQ so mx] :=
  congrArg evalDist (fst_map_run_withTraceBefore so traceFn mx)

lemma probOutput_fst_run_withTraceBefore [LawfulMonad m] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) (x : α) :
    Pr[= x | Prod.fst <$> (simulateQ (so.withTraceBefore traceFn) mx).run] =
      Pr[= x | simulateQ so mx] := by
  rw [fst_map_run_withTraceBefore]

lemma support_fst_run_withTraceBefore [LawfulMonad m] [MonadLiftT m SetM]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    support (Prod.fst <$> (simulateQ (so.withTraceBefore traceFn) mx).run) =
      support (simulateQ so mx) := by
  rw [fst_map_run_withTraceBefore]

end withTraceBefore

/-! ### `withTrace`: response-dependent trace, recorded after handler -/

section withTrace

variable {ω : Type u} [Monoid ω]

/-- Wrap an oracle implementation so that each query records
`traceFn t u` in the writer `ω` *after* the handler returns response `u`.
A handler failure skips the trace (the response never materialised). -/
def withTrace (so : QueryImpl spec m)
    (traceFn : (t : spec.Domain) → spec.Range t → ω) :
    QueryImpl spec (WriterT ω m) :=
  so.postInsert fun t u => tell (traceFn t u)

@[simp, grind =]
lemma withTrace_apply (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (t : spec.Domain) :
    so.withTrace traceFn t = (do let u ← so t; tell (traceFn t u); return u) := rfl

lemma fst_map_run_withTrace [LawfulMonad m]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    Prod.fst <$> (simulateQ (so.withTrace traceFn) mx).run = simulateQ so mx :=
  proj_simulateQ_postInsert so (fun t u => tell (traceFn t u))
    (proj := fun {γ} (x : WriterT ω m γ) => Prod.fst <$> x.run)
    WriterT.fst_map_run_pure WriterT.fst_map_run_bind
    (fun t => by simp) mx

/-- An "after"-style trace preserves failure probability for any base monad with
`MonadLiftT m SPMF`: instrumenting with `withTrace` does not change the probability
of failure. When `m = OracleComp spec`, both sides are `0` (trivially true);
when `m` can genuinely fail (e.g. `OptionT (OracleComp spec)`), this is a
non-trivial faithfulness property. -/
lemma probFailure_run_simulateQ_withTrace [LawfulMonad m] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    Pr[⊥ | (simulateQ (so.withTrace traceFn) mx).run] = Pr[⊥ | simulateQ so mx] := by
  rw [← fst_map_run_withTrace so traceFn mx, probFailure_map]

lemma neverFail_run_simulateQ_withTrace_iff [LawfulMonad m] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    NeverFail (simulateQ (so.withTrace traceFn) mx).run ↔ NeverFail (simulateQ so mx) := by
  simp only [neverFail_iff, probFailure_run_simulateQ_withTrace]

@[deprecated (since := "2026-06-25")]
alias NeverFail_run_simulateQ_withTrace_iff := neverFail_run_simulateQ_withTrace_iff

/-- When every query/response pair traces to the monoid identity `1`,
`withTrace` is a no-op up to pairing with `1`. -/
@[simp]
lemma run_simulateQ_withTrace_const_one [LawfulMonad m]
    (so : QueryImpl spec m) (mx : OracleComp spec α) :
    (simulateQ (so.withTrace (fun _ _ => (1 : ω))) mx).run =
      (·, 1) <$> simulateQ so mx := by
  induction mx using OracleComp.inductionOn <;> simp [*]

/-! #### `evalDist` / `probOutput` / `support` bridges for `withTrace` -/

lemma evalDist_fst_run_withTrace [LawfulMonad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    𝒟[Prod.fst <$> (simulateQ (so.withTrace traceFn) mx).run] =
      𝒟[simulateQ so mx] :=
  congrArg evalDist (fst_map_run_withTrace so traceFn mx)

lemma probOutput_fst_run_withTrace [LawfulMonad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) (x : α) :
    Pr[= x | Prod.fst <$> (simulateQ (so.withTrace traceFn) mx).run] =
      Pr[= x | simulateQ so mx] := by
  rw [fst_map_run_withTrace]

lemma support_fst_run_withTrace [LawfulMonad m] [MonadLiftT m SetM]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    support (Prod.fst <$> (simulateQ (so.withTrace traceFn) mx).run) =
      support (simulateQ so mx) := by
  rw [fst_map_run_withTrace]

end withTrace

/-! ### `withTraceAppendBefore`: response-independent trace, recorded before
handler, accumulating via `∅` / `++` -/

section withTraceAppendBefore

variable {ω : Type u} [EmptyCollection ω] [Append ω]

/-- Append-flavoured analogue of `withTraceBefore`: each query records
`traceFn t` in the writer `ω` *before* running the handler, and `WriterT`
uses the `[EmptyCollection ω] [Append ω]` `Monad` instance (`tell` is a single
push, `bind` concatenates with `++`). The trace value depends only on the
query, so a failure inside the handler still leaves the trace recorded. -/
def withTraceAppendBefore (so : QueryImpl spec m) (traceFn : spec.Domain → ω) :
    QueryImpl spec (WriterT ω m) :=
  so.preInsert fun t => tell (traceFn t)

@[simp, grind =]
lemma withTraceAppendBefore_apply (so : QueryImpl spec m) (traceFn : spec.Domain → ω)
    (t : spec.Domain) :
    so.withTraceAppendBefore traceFn t = (do tell (traceFn t); so t) := rfl

lemma fst_map_run_withTraceAppendBefore [LawfulMonad m] [LawfulAppend ω]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    Prod.fst <$> (simulateQ (so.withTraceAppendBefore traceFn) mx).run = simulateQ so mx :=
  proj_simulateQ_preInsert so (fun t => tell (traceFn t))
    (proj := fun {γ} (x : WriterT ω m γ) => Prod.fst <$> x.run)
    WriterT.fst_map_run_pure' WriterT.fst_map_run_bind'
    (fun t => by simp) mx

lemma probFailure_run_simulateQ_withTraceAppendBefore [LawfulMonad m]
    [LawfulAppend ω] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    Pr[⊥ | (simulateQ (so.withTraceAppendBefore traceFn) mx).run] =
      Pr[⊥ | simulateQ so mx] := by
  rw [← fst_map_run_withTraceAppendBefore so traceFn mx, probFailure_map]

lemma neverFail_run_simulateQ_withTraceAppendBefore_iff [LawfulMonad m]
    [LawfulAppend ω] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    NeverFail (simulateQ (so.withTraceAppendBefore traceFn) mx).run ↔
      NeverFail (simulateQ so mx) := by
  simp only [neverFail_iff, probFailure_run_simulateQ_withTraceAppendBefore]

@[deprecated (since := "2026-06-25")]
alias NeverFail_run_simulateQ_withTraceAppendBefore_iff :=
  neverFail_run_simulateQ_withTraceAppendBefore_iff

/-! #### `evalDist` / `probOutput` / `support` bridges for `withTraceAppendBefore` -/

lemma evalDist_fst_run_withTraceAppendBefore [LawfulMonad m] [LawfulAppend ω] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    𝒟[Prod.fst <$> (simulateQ (so.withTraceAppendBefore traceFn) mx).run] =
      𝒟[simulateQ so mx] :=
  congrArg evalDist (fst_map_run_withTraceAppendBefore so traceFn mx)

lemma probOutput_fst_run_withTraceAppendBefore [LawfulMonad m] [LawfulAppend ω] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) (x : α) :
    Pr[= x | Prod.fst <$> (simulateQ (so.withTraceAppendBefore traceFn) mx).run] =
      Pr[= x | simulateQ so mx] := by
  rw [fst_map_run_withTraceAppendBefore]

lemma support_fst_run_withTraceAppendBefore [LawfulMonad m] [LawfulAppend ω] [MonadLiftT m SetM]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    support (Prod.fst <$> (simulateQ (so.withTraceAppendBefore traceFn) mx).run) =
      support (simulateQ so mx) := by
  rw [fst_map_run_withTraceAppendBefore]

end withTraceAppendBefore

/-! ### `withTraceAppend`: response-dependent trace, recorded after handler,
accumulating via `∅` / `++` -/

section withTraceAppend

variable {ω : Type u} [EmptyCollection ω] [Append ω]

/-- Append-flavoured analogue of `withTrace`: each query records
`traceFn t u` in the writer `ω` *after* the handler returns response `u`,
using the `[EmptyCollection ω] [Append ω]` `Monad (WriterT ω m)` instance.
A handler failure skips the trace (the response never materialised). -/
def withTraceAppend (so : QueryImpl spec m)
    (traceFn : (t : spec.Domain) → spec.Range t → ω) :
    QueryImpl spec (WriterT ω m) :=
  so.postInsert fun t u => tell (traceFn t u)

@[simp, grind =]
lemma withTraceAppend_apply (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (t : spec.Domain) :
    so.withTraceAppend traceFn t = (do let u ← so t; tell (traceFn t u); return u) := rfl

lemma fst_map_run_withTraceAppend [LawfulMonad m] [LawfulAppend ω]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    Prod.fst <$> (simulateQ (so.withTraceAppend traceFn) mx).run = simulateQ so mx :=
  proj_simulateQ_postInsert so (fun t u => tell (traceFn t u))
    (proj := fun {γ} (x : WriterT ω m γ) => Prod.fst <$> x.run)
    WriterT.fst_map_run_pure' WriterT.fst_map_run_bind'
    (fun t => by simp) mx

lemma probFailure_run_simulateQ_withTraceAppend [LawfulMonad m]
    [LawfulAppend ω] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    Pr[⊥ | (simulateQ (so.withTraceAppend traceFn) mx).run] = Pr[⊥ | simulateQ so mx] := by
  rw [← fst_map_run_withTraceAppend so traceFn mx, probFailure_map]

lemma neverFail_run_simulateQ_withTraceAppend_iff [LawfulMonad m]
    [LawfulAppend ω] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    NeverFail (simulateQ (so.withTraceAppend traceFn) mx).run ↔
      NeverFail (simulateQ so mx) := by
  simp only [neverFail_iff, probFailure_run_simulateQ_withTraceAppend]

@[deprecated (since := "2026-06-25")]
alias NeverFail_run_simulateQ_withTraceAppend_iff := neverFail_run_simulateQ_withTraceAppend_iff

/-! #### `evalDist` / `probOutput` / `support` bridges for `withTraceAppend` -/

lemma evalDist_fst_run_withTraceAppend [LawfulMonad m] [LawfulAppend ω] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    𝒟[Prod.fst <$> (simulateQ (so.withTraceAppend traceFn) mx).run] =
      𝒟[simulateQ so mx] :=
  congrArg evalDist (fst_map_run_withTraceAppend so traceFn mx)

lemma probOutput_fst_run_withTraceAppend [LawfulMonad m] [LawfulAppend ω] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) (x : α) :
    Pr[= x | Prod.fst <$> (simulateQ (so.withTraceAppend traceFn) mx).run] =
      Pr[= x | simulateQ so mx] := by
  rw [fst_map_run_withTraceAppend]

lemma support_fst_run_withTraceAppend [LawfulMonad m] [LawfulAppend ω] [MonadLiftT m SetM]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    support (Prod.fst <$> (simulateQ (so.withTraceAppend traceFn) mx).run) =
      support (simulateQ so mx) := by
  rw [fst_map_run_withTraceAppend]

end withTraceAppend

end QueryImpl


