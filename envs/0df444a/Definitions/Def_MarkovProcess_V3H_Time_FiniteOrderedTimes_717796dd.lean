-- Prove2me | Definitions.Def_MarkovProcess_V3H_Time_FiniteOrderedTimes_717796dd
-- name    : MarkovProcess_V3H_Time_FiniteOrderedTimes_717796dd
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:16:36.069436+00:00
-- url     : https://prove2.me/theorems/bc5868cd-a33c-4caf-ab2f-570dcf15b21e
-- title:
--   MarkovProcess: MarkovProcess_V3H_Time_FiniteOrderedTimes_717796dd
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

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

@[simp]
theorem relativeTail_apply {n : ℕ} (times : FiniteOrderedTimes (n + 1)) (i : Fin n) :
    times.relativeTail i = times i.succ - times 0 :=
  rfl

/-- Translate every time in a finite ordered family by the same nonnegative amount. -/
def translate {n : ℕ} (s : NNReal) (times : FiniteOrderedTimes n) : FiniteOrderedTimes n :=
  OrderEmbedding.ofStrictMono (fun i ↦ s + times i) fun _ _ hij ↦
    by simpa only [add_comm] using add_lt_add_left (times.strictMono hij) s

@[simp]
theorem translate_apply {n : ℕ} (s : NNReal) (times : FiniteOrderedTimes n) (i : Fin n) :
    times.translate s i = s + times i :=
  rfl

/-- The original successor time is the first time plus its relative-tail coordinate. -/
theorem add_relativeTail {n : ℕ} (times : FiniteOrderedTimes (n + 1)) (i : Fin n) :
    times 0 + times.relativeTail i = times i.succ :=
  add_tsub_cancel_of_le (times.monotone (Fin.zero_le _))

/-- Translation does not change the relative tail of a finite ordered time family. -/
@[simp]
theorem relativeTail_translate {n : ℕ} (s : NNReal)
    (times : FiniteOrderedTimes (n + 1)) :
    (times.translate s).relativeTail = times.relativeTail := by
  apply DFunLike.ext _ _
  intro i
  exact add_tsub_add_eq_tsub_left s (times i.succ) (times 0)

/-- Translation by zero does not change a finite ordered time family. -/
@[simp]
theorem p2m_embedded_bd78ec662dc40c78 {n : ℕ} (times : FiniteOrderedTimes n) : times.translate 0 = times := by
  apply DFunLike.ext _ _
  intro i
  exact zero_add (times i)

/-- Successive translations combine by addition. -/
@[simp]
theorem p2m_embedded_a75dbbb87da12336 {n : ℕ} (s r : NNReal) (times : FiniteOrderedTimes n) :
    (times.translate r).translate s = times.translate (s + r) := by
  apply DFunLike.ext _ _
  intro i
  exact (add_assoc s r (times i)).symm

/-- Restrict a finite ordered time family along an order embedding of its indices. -/
def restrict {m n : ℕ} (times : FiniteOrderedTimes n) (e : Fin m ↪o Fin n) :
    FiniteOrderedTimes m :=
  e.trans times

@[simp]
theorem restrict_apply {m n : ℕ} (times : FiniteOrderedTimes n) (e : Fin m ↪o Fin n)
    (i : Fin m) : times.restrict e i = times (e i) :=
  rfl

/-- Restriction along the identity order embedding does not change the time family. -/
@[simp]
theorem restrict_id {n : ℕ} (times : FiniteOrderedTimes n) :
    times.restrict (OrderIso.refl (Fin n)).toOrderEmbedding = times :=
  rfl

/-- Successive restrictions agree with restriction along the composite embedding. -/
@[simp]
theorem restrict_trans {k m n : ℕ} (times : FiniteOrderedTimes n)
    (e : Fin m ↪o Fin n) (d : Fin k ↪o Fin m) :
    (times.restrict e).restrict d = times.restrict (d.trans e) :=
  rfl

/-- Restrict a coordinate path along an embedding of finite index sets. -/
def restrictPath {m n : ℕ} (e : Fin m ↪o Fin n) {α : Type*} (path : Fin n → α) :
    Fin m → α :=
  fun i ↦ path (e i)

@[simp]
theorem p2m_embedded_39f0059b006c632e {m n : ℕ} (e : Fin m ↪o Fin n) {α : Type*}
    (path : Fin n → α) (i : Fin m) : restrictPath e path i = path (e i) :=
  rfl

/-- Path restriction along the identity embedding is the identity. -/
@[simp]
theorem restrictPath_id {n : ℕ} {α : Type*} (path : Fin n → α) :
    restrictPath (OrderIso.refl (Fin n)).toOrderEmbedding path = path :=
  rfl

/-- Successive path restrictions agree with restriction along the composite embedding. -/
@[simp]
theorem p2m_embedded_b7f2c745d83730ce {k m n : ℕ} (e : Fin m ↪o Fin n) (d : Fin k ↪o Fin m)
    {α : Type*} (path : Fin n → α) :
    restrictPath d (restrictPath e path) = restrictPath (d.trans e) path :=
  rfl

/-- Restriction of finite coordinate paths is measurable for product measurable spaces. -/
theorem measurable_restrictPath {m n : ℕ} (e : Fin m ↪o Fin n)
    {α : Type*} [MeasurableSpace α] :
    Measurable (restrictPath e : (Fin n → α) → Fin m → α) :=
  measurable_pi_iff.mpr fun i ↦ measurable_pi_apply (e i)

/-- The unique path indexed by the empty finite type. -/
def emptyPath (α : Type*) : Fin 0 → α :=
  Fin.elim0



/-- Restricting any path to an empty index family gives the canonical empty path. -/
@[simp]
theorem p2m_embedded_38067e24787830d3 {n : ℕ} (e : Fin 0 ↪o Fin n) {α : Type*}
    (path : Fin n → α) : restrictPath e path = emptyPath α :=
  Subsingleton.elim _ _

end FiniteOrderedTimes

end MarkovProcess


