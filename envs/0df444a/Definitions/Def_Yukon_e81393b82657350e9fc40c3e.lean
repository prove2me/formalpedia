-- Prove2me | Definitions.Def_Yukon_e81393b82657350e9fc40c3e
-- name    : Yukon_e81393b82657350e9fc40c3e
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:03:15.405889+00:00
-- url     : https://prove2.me/theorems/1e8cbea9-905a-44a1-a529-07cb7a11231a
-- title:
--   YukonModule.PolyFun.PFunctor.Resumption.Truncate.part0
-- statement:
--   Source module PolyFun.PFunctor.Resumption.Truncate.
-- source:
--   https://github.com/Verified-zkEVM/PolyFun/blob/dd77aa91dd425ebaec4388270f3a8e3dc7ace571/PolyFun/PFunctor/Resumption/Truncate.lean
--
--   yukon-proof-operation:7da10e30dc336ae5a00e3ee0d85a38436311998bd5fc326c5d7c615ed2a9bbd1
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246N2RhMTBlMzBkYzMzNmFlNWEwMGUzZWUwZDg1YTM4NDM2MzExOTk4YmQ1ZmMzMjZjNWQ3YzYxNWVkMmE5YmJkMSIsImhhc2giOiI2N2RlODVkYTZkZjhmMWI2OTc2ZTQwZjg0YzlhZDFkMDk0ZjYyNzIwYTlmYjM0M2UyMDYxNjUxODNkMTFmYzZkIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl9lODEzOTNiODI2NTczNTBlOWZjNDBjM2UiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Definitions.Def_Yukon_3e259ba73c40aefea227f941

public import Definitions.Def_Yukon_1ba351e678ec6ebc0aa89b54



public import Mathlib.Data.PFunctor.Univariate.M
public import Init
public import Batteries.Tactic.Lint
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Init
public import Lean.Message
public import Batteries.Tactic.Lint.Basic
public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
meta import Definitions.Def_Yukon_3e259ba73c40aefea227f941
meta import Definitions.Def_Yukon_1ba351e678ec6ebc0aa89b54
set_option backward.isDefEq.respectTransparency.types false
/-!
# Finite truncation of resumptions

`Resumption.truncate k computation` unfolds through at most `k` visible-query layers and
returns a bounded-depth free program with an optional result. Returning is free; a
query at zero fuel truncates to `none`; and every answered query consumes one
unit of fuel.

The main characterization says that truncation returns `some` throughout
exactly for well-founded programs whose resumption is the original computation and
whose every branch contains at most `k` queries.
-/

@[expose] public section

universe uA uB uβ

namespace PFunctor.Resumption

variable {p : PFunctor.{uA, uB}} {β : Type uβ}

/-- Truncate a possibly infinite resumption to at most `k` visible queries.
Returning consumes no fuel; reaching a query at zero fuel returns `none`. -/
def truncate : ℕ → Resumption p β → FreeM p (Option β)
  | 0, computation =>
      match dest computation with
      | Sum.inl result => FreeM.pure (some result)
      | Sum.inr _ => FreeM.pure none
  | k + 1, computation =>
      match dest computation with
      | Sum.inl result => FreeM.pure (some result)
      | Sum.inr ⟨position, next⟩ =>
          FreeM.liftBind position fun direction => truncate k (next direction)

theorem truncate_zero (computation : Resumption p β) :
    truncate 0 computation = match dest computation with
      | Sum.inl result => FreeM.pure (some result)
      | Sum.inr _ => FreeM.pure none := rfl

theorem truncate_succ (k : ℕ) (computation : Resumption p β) :
    truncate (k + 1) computation = match dest computation with
      | Sum.inl result => FreeM.pure (some result)
      | Sum.inr ⟨position, next⟩ =>
          FreeM.liftBind position fun direction => truncate k (next direction) := rfl

@[simp] theorem truncate_pure (k : ℕ) (result : β) :
    truncate k (pure (p := p) result) = FreeM.pure (some result) := by
  cases k <;> rfl

@[simp] theorem truncate_query_zero (position : p.A) (next : p.B position → Resumption p β) :
    truncate 0 (query position next) = FreeM.pure none := rfl

@[simp] theorem truncate_query_succ (k : ℕ) (position : p.A)
    (next : p.B position → Resumption p β) :
    truncate (k + 1) (query position next) =
      FreeM.liftBind position fun direction => truncate k (next direction) := rfl

/-- Truncation never constructs a branch deeper than its fuel. -/
theorem isTotalRollBound_truncate (k : ℕ) (computation : Resumption p β) :
    (truncate k computation).IsTotalRollBound k := by
  induction k generalizing computation with
  | zero =>
      rcases h : dest computation with result | query
      <;> simp [truncate, h]
  | succ k ih =>
      rcases h : dest computation with result | ⟨position, next⟩
      · simp [truncate, h]
      · rw [truncate_succ, h]
        change (FreeM.liftBind position fun direction =>
          truncate k (next direction)).IsTotalRollBound (k + 1)
        rw [FreeM.liftBind_eq, FreeM.isTotalRollBound_lift_bind_iff]
        refine ⟨by omega, fun direction => ?_⟩
        simpa using ih (next direction)

/-- Truncation succeeds with exactly the option-lift of `program` iff the
resumption is that well-founded program's embedding and every branch of the program
fits within the fuel budget. -/
theorem truncate_eq_map_some_iff (k : ℕ) (computation : Resumption p β) (program : FreeM p β) :
    truncate k computation = FreeM.map some program ↔
      computation = FreeM.toResumption program ∧
        program.IsTotalRollBound k := by
  induction program using FreeM.induction generalizing k computation with
  | pure value =>
      constructor
      · intro h
        cases k with
        | zero =>
            rcases hdest : dest computation with result | ⟨position, next⟩
            · have hvalue : result = value := by
                simpa [truncate, hdest] using h
              subst result
              refine ⟨Resumption.eq_of_dest_eq ?_, by simp⟩
              simpa using hdest
            · simp [truncate, hdest] at h
        | succ k =>
            rcases hdest : dest computation with result | ⟨position, next⟩
            · have hvalue : result = value := by
                simpa [truncate, hdest] using h
              subst result
              refine ⟨Resumption.eq_of_dest_eq ?_, by simp⟩
              simpa using hdest
            · rw [truncate_succ, hdest] at h
              cases h
      · rintro ⟨rfl, _⟩
        exact truncate_pure k value
  | lift_bind position next ih =>
      rw [← FreeM.liftBind_eq]
      constructor
      · intro h
        cases k with
        | zero =>
            rcases hdest : dest computation with result | ⟨position', next'⟩
            · rw [truncate_zero, hdest] at h
              change FreeM.pure (some result) = FreeM.liftBind position
                (fun direction => FreeM.map some (next direction)) at h
              cases h
            · rw [truncate_zero, hdest] at h
              change FreeM.pure none = FreeM.liftBind position
                (fun direction => FreeM.map some (next direction)) at h
              cases h
        | succ k =>
            rcases hdest : dest computation with result | ⟨position', next'⟩
            · rw [truncate_succ, hdest] at h
              cases h
            · rw [truncate_succ, hdest] at h
              change FreeM.liftBind position'
                  (fun direction => truncate k (next' direction)) =
                FreeM.liftBind position
                  (fun direction => FreeM.map some (next direction)) at h
              injection h with hposition hnext
              subst position'
              have hnext' :
                  (fun direction => truncate k (next' direction)) =
                    (fun direction => FreeM.map some (next direction)) :=
                eq_of_heq hnext
              have hbranch (direction : p.B position) :=
                (ih direction k (next' direction)).mp (congrFun hnext' direction)
              constructor
              · apply Resumption.eq_of_dest_eq
                rw [hdest, FreeM.dest_toResumption_liftBind]
                apply congrArg Sum.inr
                apply Sigma.ext
                · rfl
                · apply heq_of_eq
                  funext direction
                  exact (hbranch direction).1
              · rw [FreeM.liftBind_eq, FreeM.isTotalRollBound_lift_bind_iff]
                refine ⟨by omega, fun direction => ?_⟩
                simpa using (hbranch direction).2
      · rintro ⟨rfl, hbound⟩
        cases k with
        | zero =>
            rw [FreeM.liftBind_eq, FreeM.isTotalRollBound_lift_bind_iff] at hbound
            omega
        | succ k =>
            rw [truncate_succ, FreeM.dest_toResumption_liftBind]
            change FreeM.liftBind position
                (fun direction => truncate k (FreeM.toResumption (next direction))) =
              FreeM.liftBind position
                (fun direction => FreeM.map some (next direction))
            apply congrArg (FreeM.liftBind position)
            funext direction
            apply (ih direction k (FreeM.toResumption (next direction))).mpr
            refine ⟨rfl, ?_⟩
            rw [FreeM.liftBind_eq, FreeM.isTotalRollBound_lift_bind_iff] at hbound
            simpa using hbound.2 direction

/-- A well-founded program fitting within `k` is recovered exactly by truncating its
resumption embedding. -/
theorem truncate_toResumption_eq_map_some {program : FreeM p β} {k : ℕ}
    (hbound : program.IsTotalRollBound k) :
    truncate k (FreeM.toResumption program) = FreeM.map some program :=
  (truncate_eq_map_some_iff k (FreeM.toResumption program) program).2
    ⟨rfl, hbound⟩

/-- Once truncation has recovered a well-founded program, any larger fuel budget
recovers the same program. This is the valid monotonicity law; raw truncations
need not be equal before all cutoff leaves disappear. -/
theorem truncate_eq_map_some_of_le {j k : ℕ} {computation : Resumption p β} {program : FreeM p β}
    (htruncate : truncate j computation = FreeM.map some program) (hjk : j ≤ k) :
    truncate k computation = FreeM.map some program := by
  have hcharacterized :=
    (truncate_eq_map_some_iff j computation program).1 htruncate
  exact (truncate_eq_map_some_iff k computation program).2
    ⟨hcharacterized.1, hcharacterized.2.mono hjk⟩

end PFunctor.Resumption


