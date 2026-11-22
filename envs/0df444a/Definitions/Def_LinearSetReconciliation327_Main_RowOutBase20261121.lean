-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_RowOutBase20261121
-- name    : LinearSetReconciliation327_Main_RowOutBase20261121
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-21T13:44:43.770205+00:00
-- url     : https://prove2.me/theorems/498a9eae-8767-47e7-8a7e-6b09b7fe89a6
-- title:
--   The RowOut base convention: a composite header that extends detStd
-- statement:
--   The row-bitmap base of Theorem 6.5's row loop read out of the preprocessing table `det`.
--   Proposition 2.1's table `detStd` cannot carry the composite header (its slot 3 is $2t$ and slots
--   $13\dots63$ are zero), so this bundle separates the two questions: which slots of `det` may differ
--   from `detStd` (exactly the slots Proposition 2.1's decoder never reads: $3$, $7$, $11$ and
--   $13\dots63$), and where the row base lives (in such a free slot).  It proves the base constraint
--   `RowOutFits` for the extended table, exhibits an explicit header that inhabits it, and records the
--   agreement fact that the weakened decoder contract consumes.
-- source:
--   arXiv:2611.11409 (Liu, Xu, Yang, Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), §2.1 (word-RAM model) and Theorem 6.5 (row stage); verified development of the project.

import Definitions.Def_LinearSetReconciliation327_Main_RowDecode20261121

/-!
# The `RowOut` base convention: a composite header that extends `detStd`

`RDec.rowBase E = E.det 3`, i.e. the row-bitmap base is read out of `det` slot `3`.  In
`detEnv (8*w) (detStd t N b ι)` that convention is *provably* unusable: `detStd`'s slot `3` is `2t`
(`hdrTab`), so `not_rowOutFits_detStd` shows `¬ RowOutFits … t` — the scratch clear would erase the
row bitmaps — and `detStd_high_zero` shows slots `13 … 63` are all `0`, so a composite header cannot
be smuggled into `detStd` either.

This module resolves both by separating the two questions:

* **Which slots of `det` may differ from `detStd`?**  Proposition 2.1's decoder reads `det` only at
  the ten header slots `0, 1, 2, 4, 5, 6, 8, 9, 10, 12` (`paramBody`: `0,1,4,5,6,12`;
  `saveHeaderCode`: `0,4`; `saveDestinationCode`: `0`; `decoderMetadataAssignments`: `1,2`; the
  field-table codes: `6,8,9,10`) and at table addresses `≥ detMulBase w = 64`.  So `3`, `7`, `11`
  and the block `13 … 63` are **free** (`hdrFree`), and `detExt` is the table that agrees with
  `detStd` off the free slots and carries an arbitrary composite header on them.
* **Where does the row-bitmap base live?**  In a free slot.  `rowBaseAt E ρ` reads slot `ρ`; for
  `ρ = 3` this is *definitionally* `RDec.rowBase`, so no program change is needed, and for any
  `ρ ≥ 13` (e.g. `17`) it is the convention the previous round asked for.

The main results are `rowOutFitsAt_detExt` (the base constraint holds as soon as the header value is
above `decoderAllocEnd t`) and `exists_rowOutFits` (the new convention is **inhabited**), together
with `detExt_agrees`, which is exactly the `det` hypothesis the weakened contract
`pinsketch_decoding_at_det` consumes.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Finset

open LinearSetReconciliation327.Main.R66

noncomputable section

namespace LinearSetReconciliation327.Main
namespace RDec

variable {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {N t w : ℕ}
variable {b : Module.Basis (Fin w) (ZMod 2) F} {ι : ℕ → F}

/-! ## 1. The free slots and the composite table -/

/-- The `det` header slots 2.1's decoder reads (see the module docstring for the code sites). -/
def hdrRead (a : ℕ) : Prop :=
  a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 12

instance hdrReadDecidable (a : ℕ) : Decidable (hdrRead a) := by
  unfold hdrRead; infer_instance

/-- A slot is **free** for the composite header when 2.1's decoder never reads it as a header slot:
everything below the first table except the ten header slots — explicitly `3`, `7`, `11` and the
block `13 … 63`. -/
def hdrFree (w a : ℕ) : Prop := ¬ hdrRead a ∧ a < detMulBase w

instance hdrFreeDecidable (w a : ℕ) : Decidable (hdrFree w a) := by
  unfold hdrFree; infer_instance

/-- **The composite table**: `detStd`, with the free slots replaced by the composite's header. -/
noncomputable def detExt (hdr : ℕ → ℕ) (t N : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (ι : ℕ → F) : ℕ → ℕ :=
  fun a => if hdrFree w a then hdr a else detStd t N b ι a

theorem detExt_free {hdr : ℕ → ℕ} {a : ℕ} (h : hdrFree w a) :
    detExt hdr t N b ι a = hdr a := by
  unfold detExt; rw [if_pos h]

theorem detExt_read {hdr : ℕ → ℕ} {a : ℕ} (h : ¬ hdrFree w a) :
    detExt hdr t N b ι a = detStd t N b ι a := by
  unfold detExt; rw [if_neg h]

/-- **`detExt` satisfies the weakened `det` contract**, for any composite header: it agrees with
`detStd` on the ten header slots and on the whole table region.  This is exactly the hypothesis of
`pinsketch_decoding_at_det`. -/
theorem detExt_agrees {hdr : ℕ → ℕ} {t N : ℕ} (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) :
    (∀ a, hdrRead a → detExt hdr t N b ι a = detStd t N b ι a) ∧
      (∀ a, detMulBase w ≤ a → detExt hdr t N b ι a = detStd t N b ι a) := by
  constructor
  · intro a ha
    exact detExt_read (fun hf => hf.1 ha)
  · intro a ha
    exact detExt_read (fun hf => absurd hf.2 (by omega))

/-- Slot `3` — where `RDec.rowBase` reads the row base — is free. -/
theorem hdrFree_three : hdrFree w 3 := by
  refine ⟨by decide, ?_⟩
  unfold detMulBase; norm_num

/-- Slot `17` — the `≥ 13` convention — is free. -/
theorem hdrFree_seventeen : hdrFree w 17 := by
  refine ⟨by decide, ?_⟩
  unfold detMulBase; norm_num

/-- Every slot `≥ 13` below the first table is free. -/
theorem hdrFree_of_ge {a : ℕ} (h13 : 13 ≤ a) (h64 : a < detMulBase w) : hdrFree w a := by
  refine ⟨?_, h64⟩
  intro h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-! ## 2. The row base out of a free slot -/

/-- The row-bitmap base read out of `det` slot `ρ`.  `rowBaseAt E 3` is definitionally `rowBase E`. -/
def rowBaseAt (E : RAMEnv) (ρ : ℕ) : ℕ := E.det ρ % 2 ^ E.W

theorem rowBaseAt_three (E : RAMEnv) : rowBaseAt E 3 = rowBase E := rfl

theorem rowBaseAt_lt (E : RAMEnv) (ρ : ℕ) : rowBaseAt E ρ < 2 ^ E.W :=
  Nat.mod_lt _ (Nat.two_pow_pos E.W)

/-- Under `detExt`, slot `ρ` holds the composite header's value. -/
theorem rowBaseAt_detExt {hdr : ℕ → ℕ} {ρ : ℕ} (hρ : hdrFree w ρ) :
    rowBaseAt (detEnv (8 * w) (detExt (w := w) hdr t N b ι)) ρ = hdr ρ % 2 ^ (8 * w) := by
  show detExt (w := w) hdr t N b ι ρ % 2 ^ (8 * w) = hdr ρ % 2 ^ (8 * w)
  rw [detExt_free hρ]

/-- The base constraint at slot `ρ`: the row bitmaps start at or above 2.1's scratch. -/
def RowOutFitsAt (E : RAMEnv) (ρ t : ℕ) : Prop := decoderAllocEnd t ≤ rowBaseAt E ρ

/-- **The new `RowOut` base convention, proved.**  If the composite header puts, in a free slot `ρ`,
a value at least `decoderAllocEnd t` (and below the word size), then the base constraint holds for
the composite table.  No hypothesis on `detStd` is left: the free slot is exactly a slot the decoder
never reads. -/
theorem rowOutFitsAt_detExt {hdr : ℕ → ℕ} {ρ : ℕ} (hρ : hdrFree w ρ)
    (hfit : decoderAllocEnd t ≤ hdr ρ) (hlt : hdr ρ < 2 ^ (8 * w)) :
    RowOutFitsAt (detEnv (8 * w) (detExt (w := w) hdr t N b ι)) ρ t := by
  unfold RowOutFitsAt
  rw [rowBaseAt_detExt hρ, Nat.mod_eq_of_lt hlt]
  exact hfit

/-- The same, phrased with the **existing** `RowOutFits` (which reads slot `3`): the old convention
is not wrong, only `detStd` is — put the row base in slot `3` of a table that extends `detStd` and
the constraint holds. -/
theorem rowOutFits_detExt {hdr : ℕ → ℕ}
    (hfit : decoderAllocEnd t ≤ hdr 3) (hlt : hdr 3 < 2 ^ (8 * w)) :
    RowOutFits (detEnv (8 * w) (detExt (w := w) hdr t N b ι)) t := by
  unfold RowOutFits
  have h : RowOutFitsAt (detEnv (8 * w) (detExt (w := w) hdr t N b ι)) 3 t :=
    rowOutFitsAt_detExt (hdr := hdr) (ρ := 3) (t := t) hdrFree_three hfit hlt
  simpa only [RowOutFitsAt, rowBaseAt_three] using h

/-- The `≥ 13` convention: the row base in slot `17`. -/
theorem rowOutFitsAt_detExt_seventeen {hdr : ℕ → ℕ}
    (hfit : decoderAllocEnd t ≤ hdr 17) (hlt : hdr 17 < 2 ^ (8 * w)) :
    RowOutFitsAt (detEnv (8 * w) (detExt (w := w) hdr t N b ι)) 17 t :=
  rowOutFitsAt_detExt (hdr := hdr) (ρ := 17) (t := t) hdrFree_seventeen hfit hlt

/-! ## 3. Non-vacuity: an explicit composite header that satisfies the constraint

The header `rowHeader t` sends the two free slots `3` and `17` to `decoderAllocEnd t` and everything
else to `0`.  It inhabits the new convention, and the resulting memory layout is the one the row loop
of Theorem 6.5 needs (rows above 2.1's scratch, and 2.1's own table untouched). -/

/-- An explicit composite header: row base at slots `3` and `17`, `0` elsewhere. -/
def rowHeader (t : ℕ) : ℕ → ℕ := fun a => if a = 3 ∨ a = 17 then decoderAllocEnd t else 0

theorem rowHeader_three (t : ℕ) : rowHeader t 3 = decoderAllocEnd t := by
  simp [rowHeader]

theorem rowHeader_seventeen (t : ℕ) : rowHeader t 17 = decoderAllocEnd t := by
  simp [rowHeader]

/-- `decoderAllocEnd t` fits in a word as soon as `t < 2^w`. -/
theorem decoderAllocEnd_lt_pow {t w : ℕ} (hw : 1 ≤ w) (ht : t < 2 ^ w) :
    decoderAllocEnd t < 2 ^ (8 * w) :=
  decoderAllocEnd_fits t w hw ht

/-- **The new convention is inhabited**: there is a table `dt` that agrees with `detStd` on every
slot 2.1's decoder reads and for which `RowOutFits` holds — while `not_rowOutFits_detStd` says the
same is false for `detStd` itself. -/
theorem exists_rowOutFits (hw : 1 ≤ w) (ht : t < 2 ^ w) : ∃ dt : ℕ → ℕ,
    (∀ a, hdrRead a → dt a = detStd t N b ι a) ∧
      (∀ a, detMulBase w ≤ a → dt a = detStd t N b ι a) ∧
        RowOutFits (detEnv (8 * w) dt) t := by
  obtain ⟨h1, h2⟩ := detExt_agrees (hdr := rowHeader t) (t := t) (N := N) b ι
  refine ⟨detExt (rowHeader t) t N b ι, h1, h2, ?_⟩
  refine rowOutFits_detExt (hfit := le_rfl) (hlt := ?_)
  rw [rowHeader_three]
  exact decoderAllocEnd_fits t w hw ht

/-! ## 4. The `≥ 13` layout, end to end: `RowOut` at an arbitrary free slot -/

/-- Address of the first word of row `j`'s bitmap when the base is read out of slot `ρ`. -/
def rowSlotAt (E : RAMEnv) (ρ R j : ℕ) : ℕ := rowBaseAt E ρ + j * rowWords E R

/-- The `RowOut` layout at slot `ρ`.  `RowOutAt E 3 = RowOut E` definitionally. -/
def RowOutAt (E : RAMEnv) (ρ R j : ℕ) (x : Fin R → ZMod 2) (m : ℕ → ℕ) : Prop :=
  ∀ i, i < rowWords E R → m (rowSlotAt E ρ R j + i) = packMem E.W x i

theorem rowSlotAt_three (E : RAMEnv) (R j : ℕ) : rowSlotAt E 3 R j = rowSlot E R j := rfl

theorem rowSlotAt_zero (E : RAMEnv) (ρ R : ℕ) : rowSlotAt E ρ R 0 = rowBaseAt E ρ := by
  simp [rowSlotAt]

theorem rowSlotAt_succ (E : RAMEnv) (ρ R j : ℕ) :
    rowSlotAt E ρ R (j + 1) = rowSlotAt E ρ R j + rowWords E R := by
  simp only [rowSlotAt, Nat.succ_mul]; omega

theorem rowSlotAt_lt_next (E : RAMEnv) (ρ R j i : ℕ) (hi : i < rowWords E R) :
    rowSlotAt E ρ R j + i < rowSlotAt E ρ R (j + 1) := by
  rw [rowSlotAt_succ]; omega

/-- Rows occupy pairwise disjoint word blocks at any base. -/
theorem rowSlotAt_disjoint (E : RAMEnv) (ρ R j j' i i' : ℕ) (hjj : j < j')
    (hi : i < rowWords E R) :
    rowSlotAt E ρ R j + i ≠ rowSlotAt E ρ R j' + i' := by
  intro h
  have h1 : rowSlotAt E ρ R j + i < rowSlotAt E ρ R (j + 1) := rowSlotAt_lt_next E ρ R j i hi
  have h2 : rowSlotAt E ρ R (j + 1) ≤ rowSlotAt E ρ R j' := by
    simp only [rowSlotAt]
    have hm : (j + 1) * rowWords E R ≤ j' * rowWords E R :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  omega

/-- Under the base constraint the clearing pass leaves the bitmap of row `j` alone, at any slot. -/
theorem rowOutAt_preserved (E : RAMEnv) (ρ R j t : ℕ) (x : Fin R → ZMod 2) (m m' : ℕ → ℕ)
    (hfit : RowOutFitsAt E ρ t) (hframe : ∀ a, decoderAllocEnd t ≤ a → m' a = m a)
    (h : RowOutAt E ρ R j x m) : RowOutAt E ρ R j x m' := by
  intro i hi
  have hle : decoderAllocEnd t ≤ rowSlotAt E ρ R j := by
    simp only [rowSlotAt, RowOutFitsAt] at *
    omega
  rw [hframe _ (by omega), h i hi]

end RDec
end LinearSetReconciliation327.Main


