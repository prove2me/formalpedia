-- Prove2me | Definitions.Def_MarkovProcess_Time_CountableDenseTime
-- name    : MarkovProcess_Time_CountableDenseTime
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T11:55:36.622853+00:00
-- url     : https://prove2.me/theorems/72ffba9f-ccb9-4fe8-ad70-a186795683c2
-- title:
--   MarkovProcess definitions: Time.CountableDenseTime
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.Time.CountableDenseTime`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Time/CountableDenseTime.lean#L1-L146

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Countable dense time indices

This file gives finite prefixes and measurable path reindexings for an arbitrary enumeration of
a countably infinite type. The fixed enumeration of nonnegative rational times below is arbitrary,
not increasing. No probability law, projective limit, stochastic process, continuity, or path
regularity is constructed here.
-/

namespace MarkovProcess

noncomputable section

namespace CountableEnumeration

variable {D : Type*}

/-- The first `n` values of an enumeration. -/
def «prefix» (e : ℕ ≃ D) (n : ℕ) : Finset D :=
  Finset.map e.toEmbedding (Finset.range n)

@[simp]
theorem mem_prefix_iff (e : ℕ ≃ D) (n : ℕ) (d : D) :
    d ∈ «prefix» e n ↔ e.symm d < n := by
  simp only [«prefix», Finset.mem_map, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, hkd⟩
    rw [← hkd]
    change e.symm (e k) < n
    rw [e.symm_apply_apply]
    exact hk
  · intro hd
    exact ⟨e.symm d, hd, e.apply_symm_apply d⟩

















/-- Measurable reindexing between paths on `ℕ` and paths on the enumerated type. -/
def measurableEquivPath (e : ℕ ≃ D) (α : Type*) [MeasurableSpace α] :
    (ℕ → α) ≃ᵐ (D → α) :=
  MeasurableEquiv.piCongrLeft (fun _ : D ↦ α) e

end CountableEnumeration

/-- The countable dense carrier of nonnegative rational times. -/
abbrev DenseTime := NNRat

namespace DenseTime

/-- The order embedding of nonnegative rational times into nonnegative real times. -/
noncomputable def castOrderEmbedding : DenseTime ↪o NNReal :=
  NNRat.castOrderEmbedding

/-- Between two distinct nonnegative real times lies a nonnegative rational time. -/
theorem exists_cast_btwn {a b : NNReal} (hab : a < b) :
    ∃ q : DenseTime, a < castOrderEmbedding q ∧ castOrderEmbedding q < b := by
  obtain ⟨q, hq, haq, hqb⟩ := (NNReal.lt_iff_exists_rat_btwn a b).mp hab
  have hcast : NNRat.cast (K := NNReal) ⟨q, hq⟩ = Real.toNNReal q := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (Rat.cast_nonneg.mpr hq)]
    norm_cast
  have hcoe : castOrderEmbedding ⟨q, hq⟩ = NNRat.cast (K := NNReal) ⟨q, hq⟩ := rfl
  refine ⟨⟨q, hq⟩, ?_, ?_⟩
  · rw [hcoe, hcast]
    exact haq
  · rw [hcoe, hcast]
    exact hqb

private instance : Infinite DenseTime :=
  Infinite.of_injective (fun n : ℕ ↦ (n : DenseTime)) Nat.cast_injective

private instance : Countable DenseTime where
  exists_injective_nat' :=
    ⟨fun q ↦ Encodable.encode (q : ℚ), fun _ _ h ↦
      NNRat.ext (Encodable.encode_injective h)⟩

/-- A fixed arbitrary enumeration of nonnegative rational times. It is not order-preserving. -/
noncomputable def enumeration : ℕ ≃ DenseTime :=
  nonempty_equiv_of_countable.some

end DenseTime
end
end MarkovProcess


