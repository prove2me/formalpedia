-- Prove2me | Definitions.Def_Yukon_94b8f5dc056c300eb1adf1dd
-- name    : Yukon_94b8f5dc056c300eb1adf1dd
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T17:59:31.723736+00:00
-- url     : https://prove2.me/theorems/0b792fe8-3b46-4079-bd8d-798991d5f459
-- title:
--   YukonModule.ArkLib.ToVCVio.ToMathlib.Data.Vector.Basic.part0
-- statement:
--   Source module ArkLib.ToVCVio.ToMathlib.Data.Vector.Basic.
-- source:
--   https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/ToVCVio/ToMathlib/Data/Vector/Basic.lean
--
--   yukon-proof-operation:b191161854bf8c357346c786fb2a5ea710ef43b9f3c0a66ab424c23adbc9a5db
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246YjE5MTE2MTg1NGJmOGMzNTczNDZjNzg2ZmIyYTVlYTcxMGVmNDNiOWYzYzBhNjZhYjQyNGMyM2FkYmM5YTVkYiIsImhhc2giOiI3NDc1MWQ1YWM3NzA1MmJjNzY3YjdiOGJiOWFkNGEyOTAzMjlkNzAxMTAxNTZmZjk3MGQ4NjJkNWVmMDc0ODA0Iiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl85NGI4ZjVkYzA1NmMzMDBlYjFhZGYxZGQiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Vector.Basic
import Definitions.Def_Yukon_e88c9935225aedcca88ceb17



import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Finset.Card
import Init
import Mathlib.Data.Vector.Defs
import Mathlib.CategoryTheory.Monad.Types
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Batteries.Control.AlternativeMonad
set_option backward.isDefEq.respectTransparency.types false
/-!
# Additions to VCV-io's `ToMathlib.Data.Vector.Basic`

`Vector.support_mapM_index`, formerly proved in this module, now comes from
`VCVio.EvalDist.List` under the same public name.
-/

/-- `Vector.mapM` commutes with post-composition by a pure map:
    mapping `g` after each monadic action is the same as mapping `g` over the collected vector. -/
lemma Vector.mapM_map_postcomp {m : Type → Type} {α β γ : Type} {n : ℕ}
    [Monad m] [LawfulMonad m]
    (v : Vector α n) (f : α → m β) (g : β → γ) :
    (v.mapM (fun a => g <$> f a)) = (Vector.map g) <$> (v.mapM f) := by
  have hlist : ∀ l : List α, l.mapM (fun a => g <$> f a) = List.map g <$> l.mapM f := by
    intro l
    induction l with
    | nil => simp
    | cons a t ih => simp [ih]
  apply Vector.map_toArray_inj.mp
  rw [Vector.toArray_mapM]
  simp only [Functor.map_map, Vector.toArray_map]
  rw [← Functor.map_map]
  rw [Vector.toArray_mapM]
  rw [Array.mapM_eq_mapM_toList, Array.mapM_eq_mapM_toList]
  simp only [Functor.map_map]
  rw [hlist]
  simp [Functor.map_map]

/-- `Option.map` distributes through `Vector.mapM id` (sequencing of options):
    mapping before sequencing equals sequencing then mapping. -/
lemma Vector.mapM_id_option_map_comm {α β : Type} {n : ℕ}
    (v : Vector (Option α) n) (g : α → β) :
    (v.map (Option.map g)).mapM (id : Option β → Option β) =
    (v.mapM (id : Option α → Option α)).map (Vector.map g) := by
  rw [Vector.mapM_map]
  exact Vector.mapM_map_postcomp v (id : Option α → Option α) g

/-- Two `Vector.mapM` calls with pointwise-related monadic bodies produce equal
    results after compatible post-processing when the bodies differ by a pure map. -/
lemma Vector.mapM_bind_map_eq {m : Type → Type} {α β γ δ : Type} {n : ℕ}
    [Monad m] [LawfulMonad m]
    (v : Vector α n)
    (f₁ : α → m γ) (f₂ : α → m β) (g : β → γ)
    (hf : ∀ a, f₁ a = g <$> f₂ a)
    (post₁ : Vector γ n → m δ) (post₂ : Vector β n → m δ)
    (hpost : ∀ opts, post₁ (opts.map g) = post₂ opts) :
    (v.mapM f₁ >>= post₁) = (v.mapM f₂ >>= post₂) := by
  have hf' : f₁ = fun a => g <$> f₂ a := by
    funext a
    exact hf a
  rw [hf']
  rw [Vector.mapM_map_postcomp]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp, pure_bind]
  apply bind_congr
  intro opts
  exact hpost opts

/-- For a `Vector` of `Option` values, if `mapM id` yields `some w`, then each entry is
    `some` of the corresponding entry in `w`. -/
lemma Vector.mapM_id_some_index
    {α : Type} {L : ℕ} {v : Vector (Option α) L} {w : Vector α L}
    (h : v.mapM id = some w) (i : Fin L) : v[i] = some w[i] := by
  induction L with
  | zero => exact Fin.elim0 i
  | succ L ih =>
      obtain ⟨v0, a, hv⟩ := Vector.exists_push (xs := v)
      obtain ⟨w0, b, hw⟩ := Vector.exists_push (xs := w)
      subst hv
      subst hw
      have hdecomp : v0.mapM id = some w0 ∧ a = some b := by
        have hpush : (v0.push a).mapM id =
            (v0.mapM id >>= (fun x => a.map (fun last => x.push last))) := by
          have hsingle : (#v[a]).mapM id = a.map (fun last => #v[last]) := by
            apply Vector.map_toArray_inj.mp
            cases a <;> simp
          rw [← Vector.append_singleton, Vector.mapM_append, hsingle]
          cases a <;> simp [Vector.append_singleton]
        rw [hpush] at h
        cases hv0 : v0.mapM id with
        | none => simp [hv0] at h
        | some w0' =>
            cases ha : a with
            | none => simp [hv0, ha] at h
            | some aval =>
                simp only [hv0, ha, Option.map_some, Option.bind_eq_bind, Option.bind_some,
                  Option.some.injEq] at h
                have hp := Vector.push_eq_push.mp h
                exact ⟨congrArg some hp.2, congrArg some hp.1⟩
      by_cases hi : (i : ℕ) < L
      · change (v0.push a)[(i : ℕ)] = some ((w0.push b)[(i : ℕ)])
        rw [Vector.getElem_push_lt hi, Vector.getElem_push_lt hi]
        exact ih hdecomp.1 ⟨i, hi⟩
      · have hilast : (i : ℕ) = L := by omega
        have hi_eq : i = ⟨L, Nat.lt_succ_self L⟩ := Fin.ext hilast
        subst i
        simp [hdecomp.2]


