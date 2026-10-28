-- Prove2me | Definitions.Def_MarkovProcess_Time_FiniteOrderedTimes
-- name    : MarkovProcess_Time_FiniteOrderedTimes
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T11:55:50.920148+00:00
-- url     : https://prove2.me/theorems/d72bd3fc-ef64-44e8-bdcc-a0ed711703a0
-- title:
--   MarkovProcess definitions: Time.FiniteOrderedTimes
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.Time.FiniteOrderedTimes`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Time/FiniteOrderedTimes.lean#L1-L146

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic

/-!
# Finite ordered time families

This file provides increasing finite families of nonnegative times and the elementary operations
for restricting such families and their coordinate paths along order embeddings.  It is an
ordinary finite-dimensional API and makes no probability-law or stochastic-process claim.
-/

namespace MarkovProcess

/-- A strictly increasing family of `n` nonnegative times. -/
abbrev FiniteOrderedTimes (n : ℕ) := Fin n ↪o NNReal

namespace FiniteOrderedTimes

/-- The times after the first one, shifted so that the first time becomes zero. -/
def relativeTail {n : ℕ} (times : FiniteOrderedTimes (n + 1)) : FiniteOrderedTimes n :=
  OrderEmbedding.ofStrictMono (fun i ↦ times i.succ - times 0) fun _ _ hij ↦
    tsub_lt_tsub_right_of_le (times.monotone (Fin.zero_le _))
      (times.strictMono (Fin.strictMono_succ hij))



/-- Translate every time in a finite ordered family by the same nonnegative amount. -/
def translate {n : ℕ} (s : NNReal) (times : FiniteOrderedTimes n) : FiniteOrderedTimes n :=
  OrderEmbedding.ofStrictMono (fun i ↦ s + times i) fun _ _ hij ↦
    by simpa only [add_comm] using add_lt_add_left (times.strictMono hij) s











/-- Restrict a finite ordered time family along an order embedding of its indices. -/
def restrict {m n : ℕ} (times : FiniteOrderedTimes n) (e : Fin m ↪o Fin n) :
    FiniteOrderedTimes m :=
  e.trans times







/-- Restrict a coordinate path along an embedding of finite index sets. -/
def restrictPath {m n : ℕ} (e : Fin m ↪o Fin n) {α : Type*} (path : Fin n → α) :
    Fin m → α :=
  fun i ↦ path (e i)









/-- The unique path indexed by the empty finite type. -/
def emptyPath (α : Type*) : Fin 0 → α :=
  Fin.elim0





end FiniteOrderedTimes

end MarkovProcess


