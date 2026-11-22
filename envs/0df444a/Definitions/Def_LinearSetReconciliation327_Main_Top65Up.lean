-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_Top65Up
-- name    : LinearSetReconciliation327_Main_Top65Up
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-21T15:28:37.292397+00:00
-- url     : https://prove2.me/theorems/1c00cf63-4263-473f-b2ec-13a1039fe6d4
-- title:
--   Theorem 6.5, conjunct 6: composite `det` layout, per-block run contract, prologue and the ℓ-block stitching
-- statement:
--   The infrastructure of Theorem 6.5's **toggle conjunct** (conjunct 6), for the composite programme `progUpOfProB Sup Scr` over $\ell$ child blocks and a final $\mathrm{CR}$ block.
--
--   1. **The composite deterministic table.**  The child blocks occupy $[s\cdot 2^{W_d},(s+1)\cdot 2^{W_d})$ and the CR block $[\ell\cdot 2^{W_d},(\ell+1)\cdot 2^{W_d})$, which leaves no room for the two numbers a *fixed* programme cannot know ($\ell$ and $2^{W_d}$), nor for the table of payload bases the dispatcher reads.  `compUpDet` therefore prefixes the blocks by one $2^{W_d}$-wide metadata block: address $0$ holds $\ell+1$ (the loop bound), $1$ holds $2^{W_d}$, $2$ holds `compPayBase` $-1$; the payload bases $\beta_s = \mathrm{blkOff}\ W\ f\ s$ live in the tail of the CR block above the CR table's own words.
--   2. **The per-block contract** `UpBlkSem`: one `Stmt`, base-relative in *both* addresses, run at the block's padded width, with a two-sided memory frame and preservation of the dispatcher's five registers $r_0,\dots,r_4$.
--   3. **The prologue** `compProCode`, which reads the three metadata cells into $r_2,r_3,r_4$ and sets $r_1 = 1$, so that the already-built loop body ($r_{14} = r_1 r_3$, $r_{15} = \mathrm{det}(r_4+r_1)$, $r_1 \mathrel{+}= 1$) runs the blocks $s = 0,\dots,\ell-1$ unchanged.
--   4. **The $\ell$-block stitching**: one `Sem` per iteration from the per-block contract, glued by `Sem.block`/`Sem.seq`/`Sem.loop` around the payload invariant $\mathrm{mem}\ q = \mathrm{packMem}\ W\ (y + \mathrm{compAsm}(v_j,0))\ q$, with the word-local packing lemma doing the per-block word stitching.
--   5. **The cost** and the final `TogglesWithin` statement.
-- source:
--   arXiv:2611.11409 (Liu, Xu, Yang, Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), §6.1, Theorem 6.5, conjunct 6 (the toggle conjunct) together with Proposition 2.3's toggle block as the CR child.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_TopLevel
import Definitions.Def_LinearSetReconciliation327_Main_WordRAM
import Definitions.Def_LinearSetReconciliation327_Main_DecoderModel
import Definitions.Def_LinearSetReconciliation327_Main_DecoderLemmas
import Definitions.Def_LinearSetReconciliation327_Main_Top65
/-!
# `Top65Up`: the composite toggle programme of Theorem 6.5, conjunct 6

`Solutions/Sol_theorem_6_5.lean` builds the composite datum (`compAsm`, `compDet`) and both
dispatchers, and proves everything about them that does not need a per-block *run* contract.
This module adds the missing half of conjunct 6:

* **U1 the composite `det` layout.**  `compDet`'s child blocks are `[s*2^Wd, (s+1)*2^Wd)` and the
  `CR` block is `[l*2^Wd, (l+1)*2^Wd)`, which leaves no room for the two numbers a *fixed*
  programme cannot know (`l`, `2^Wd`) nor for the payload-base table the dispatcher reads.  The
  layout below prefixes the blocks by one `2^Wd`-wide metadata block (`det 0 = l+1`,
  `det 1 = 2^Wd`, `det 2 = base-table address - 1`) and stores the payload bases `beta_s = blkOff W f s`
  in the *tail of the `CR` block*, above the `CR` table's own words; `compDet_child`, `compDet_cr`
  then apply verbatim to `compUpDet`, and `compUpDet_pay` says a `qDet` of the base table hits `beta_s`.
* **U2 the per-block contract** `UpBlkSem` — one `Stmt`, base-relative in *both* addresses, at the
  block's padded width, with a two-sided frame and preservation of the dispatcher's five registers.
  This is the single hypothesis Theorem 5.1's export has to supply (and the same predicate is used
  for the `CR` block, whose programme is 2.3's).
* **U3 the prologue**: `compProCode` reads the three metadata cells into `r2`, `r3`, `r4` and sets
  `r1 = 1`, so the already-built `compUpStmt` loop (`r14 = r1*r3`, `r15 = det (r4+r1)`, `r1 := r1+1`)
  runs blocks `s = r1 - 1 = 0 ... l-1` without a single change to the body.
* **U4 the `l`-block stitching**: one `Sem` per iteration from the per-block contract, glued by
  `Sem.block`/`Sem.seq`/`Sem.loop`, with the payload invariant
  `mem q = packMem W (y + compAsm (v_j) 0) q`, the word-local `packMem` lemma
  `packMem_add_compAsm_blk` doing the per-block word stitching, and `compAsm_add` carrying the
  partial vector.
* **U5 the cost** and **U6 the final `TogglesWithin`**.

Nothing here is special to Theorem 5.1 other than `UpBlkSem`: the file is a `Definitions` bundle so
that the 6.5 solution file stays inside the platform's elaboration budget.
-/

set_option autoImplicit false

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

noncomputable section

/-! ## U1. The composite `det`: metadata block, child blocks, `CR` block with the base table -/

/-- The payload-base table, at offsets `Rpad, ..., Rpad + l - 1` of the `CR` block. -/
def compPayTbl {l : ℕ} (Rpad : ℕ) (b : Fin l → ℕ) : ℕ → ℕ :=
  fun q => if h : Rpad ≤ q ∧ q - Rpad < l then b ⟨q - Rpad, h.2⟩ else 0

/-- The `CR` block's table, extended by the payload bases above the `CR` table's own `Rpad` words. -/
def compCRDet {l : ℕ} (Rpad : ℕ) (dcr : ℕ → ℕ) (b : Fin l → ℕ) : ℕ → ℕ :=
  fun q => if q < Rpad then dcr q else compPayTbl Rpad b q

/-- The address in `det` of the payload-base table. -/
def compPayBase (l Wd Rpad : ℕ) : ℕ := (l + 1) * 2 ^ Wd + Rpad

/-- The composite `det` of the toggle programme: **one metadata block**, then `compDet`'s child
blocks and `CR` block shifted by it.  Address `0` holds `l+1` (the loop's bound), `1` holds the
block width `2^Wd`, `2` holds `compPayBase - 1` (so that `r4 + r1` with `r1 = s+1` is the address of
`beta_s`), and every other address of the first block reads `0`. -/
def compUpDet {l : ℕ} (Wd Rpad : ℕ) (dt : Fin l → ℕ → ℕ) (dcr : ℕ → ℕ)
    (b : Fin l → ℕ) : ℕ → ℕ :=
  fun a =>
    if a < 2 ^ Wd then
      (if a = 0 then l + 1
       else if a = 1 then 2 ^ Wd
       else if a = 2 then compPayBase l Wd Rpad - 1 else 0)
    else compDet Wd dt (compCRDet Rpad dcr b) (a - 2 ^ Wd)

/-- The low (metadata) block of `compUpDet`. -/
theorem compUpDet_meta {l Wd Rpad : ℕ} (dt : Fin l → ℕ → ℕ) (dcr : ℕ → ℕ) (b : Fin l → ℕ)
    {a : ℕ} (ha : a < 2 ^ Wd) (h0 : a ≠ 0) (h1 : a ≠ 1) (h2 : a ≠ 2) :
    compUpDet Wd Rpad dt dcr b a = 0 := by
  unfold compUpDet
  rw [if_pos ha, if_neg h0, if_neg h1, if_neg h2]

/-- Metadata cell `0`: the loop bound `l + 1`. -/
theorem compUpDet_zero {l Wd Rpad : ℕ} (dt : Fin l → ℕ → ℕ) (dcr : ℕ → ℕ) (b : Fin l → ℕ)
    (h : 0 < 2 ^ Wd) : compUpDet Wd Rpad dt dcr b 0 = l + 1 := by
  unfold compUpDet
  rw [if_pos h, if_pos rfl]

/-- Metadata cell `1`: the block width `2^Wd`. -/
theorem compUpDet_one {l Wd Rpad : ℕ} (dt : Fin l → ℕ → ℕ) (dcr : ℕ → ℕ) (b : Fin l → ℕ)
    (h : 1 < 2 ^ Wd) : compUpDet Wd Rpad dt dcr b 1 = 2 ^ Wd := by
  unfold compUpDet
  rw [if_pos h, if_neg (by norm_num), if_pos rfl]

/-- Metadata cell `2`: the address of `beta_0`, minus one. -/
theorem compUpDet_two {l Wd Rpad : ℕ} (dt : Fin l → ℕ → ℕ) (dcr : ℕ → ℕ) (b : Fin l → ℕ)
    (h : 2 < 2 ^ Wd) : compUpDet Wd Rpad dt dcr b 2 = compPayBase l Wd Rpad - 1 := by
  unfold compUpDet
  rw [if_pos h, if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]

/-- Inside child `s`'s block (address `(s+1)*2^Wd + k`) the composite `det` is child `s`'s table. -/
theorem compUpDet_child {l Wd Rpad : ℕ} (dt : Fin l → ℕ → ℕ) (dcr : ℕ → ℕ) (b : Fin l → ℕ)
    (s : Fin l) {k : ℕ} (hk : k < 2 ^ Wd) :
    compUpDet Wd Rpad dt dcr b ((s.val + 1) * 2 ^ Wd + k) = dt s k := by
  have hW : 0 < 2 ^ Wd := Nat.two_pow_pos Wd
  have hshift : (s.val + 1) * 2 ^ Wd + k - 2 ^ Wd = s.val * 2 ^ Wd + k := by
    rw [Nat.succ_mul]; omega
  have hge : ¬ ((s.val + 1) * 2 ^ Wd + k < 2 ^ Wd) := by
    rw [Nat.succ_mul]; omega
  have hdiv : (s.val * 2 ^ Wd + k) / 2 ^ Wd = s.val := nat_div_mul_add (2 ^ Wd) hW s.val k hk
  have hmod : (s.val * 2 ^ Wd + k) % 2 ^ Wd = k := nat_mod_mul_add (2 ^ Wd) s.val k hk
  unfold compUpDet
  rw [if_neg hge, hshift,
    compDet_child dt (compCRDet Rpad dcr b) (a := s.val * 2 ^ Wd + k) (by rw [hdiv]; exact s.isLt)]
  rw [hmod]
  exact congrArg (fun t : Fin l => dt t k) (Fin.ext hdiv)

/-- Inside the `CR` block (address `(l+1)*2^Wd + q`, `q < Rpad`) the composite `det` is the `CR`
table. -/
theorem compUpDet_cr {l Wd Rpad : ℕ} (dt : Fin l → ℕ → ℕ) (dcr : ℕ → ℕ) (b : Fin l → ℕ)
    {q : ℕ} (hq : q < Rpad) (hfit : Rpad ≤ 2 ^ Wd) :
    compUpDet Wd Rpad dt dcr b ((l + 1) * 2 ^ Wd + q) = dcr q := by
  have hW : 0 < 2 ^ Wd := Nat.two_pow_pos Wd
  have hlt : q < 2 ^ Wd := lt_of_lt_of_le hq hfit
  have hshift : (l + 1) * 2 ^ Wd + q - 2 ^ Wd = l * 2 ^ Wd + q := by
    rw [Nat.succ_mul]; omega
  have hge : ¬ ((l + 1) * 2 ^ Wd + q < 2 ^ Wd) := by
    rw [Nat.succ_mul]; omega
  have hdiv : (l * 2 ^ Wd + q) / 2 ^ Wd = l := nat_div_mul_add (2 ^ Wd) hW l q hlt
  have hmod : (l * 2 ^ Wd + q) % 2 ^ Wd = q := nat_mod_mul_add (2 ^ Wd) l q hlt
  unfold compUpDet
  rw [if_neg hge, hshift,
    compDet_cr dt (compCRDet Rpad dcr b) (a := l * 2 ^ Wd + q) hdiv, hmod]
  unfold compCRDet
  rw [if_pos hq]

/-- **The payload base of block `s` is a `qDet` away.**  Reading `det` at
`(compPayBase - 1) + (s+1)` --- which is what the dispatcher's `r4 + r1` computes at block `s` ---
gives `beta_s`. -/
theorem compUpDet_pay {l Wd Rpad : ℕ} (dt : Fin l → ℕ → ℕ) (dcr : ℕ → ℕ) (b : Fin l → ℕ)
    (s : Fin l) (hR : 0 < Rpad) (hfit : Rpad + s.val < 2 ^ Wd) :
    compUpDet Wd Rpad dt dcr b (compPayBase l Wd Rpad - 1 + (s.val + 1)) = b s := by
  have hW : 0 < 2 ^ Wd := Nat.two_pow_pos Wd
  have hA : compPayBase l Wd Rpad - 1 + (s.val + 1) = (l + 1) * 2 ^ Wd + (Rpad + s.val) := by
    unfold compPayBase; omega
  rw [hA]
  have hshift : (l + 1) * 2 ^ Wd + (Rpad + s.val) - 2 ^ Wd
      = l * 2 ^ Wd + (Rpad + s.val) := by
    rw [Nat.succ_mul]; omega
  have hge : ¬ ((l + 1) * 2 ^ Wd + (Rpad + s.val) < 2 ^ Wd) := by
    rw [Nat.succ_mul]; omega
  have hfit' : Rpad + s.val < 2 ^ Wd := hfit
  have hdiv : (l * 2 ^ Wd + (Rpad + s.val)) / 2 ^ Wd = l :=
    nat_div_mul_add (2 ^ Wd) hW l (Rpad + s.val) hfit'
  have hmod : (l * 2 ^ Wd + (Rpad + s.val)) % 2 ^ Wd = Rpad + s.val :=
    nat_mod_mul_add (2 ^ Wd) l (Rpad + s.val) hfit'
  unfold compUpDet
  rw [if_neg hge, hshift,
    compDet_cr dt (compCRDet Rpad dcr b) (a := l * 2 ^ Wd + (Rpad + s.val)) hdiv, hmod]
  unfold compCRDet compPayTbl
  rw [if_neg (by omega), dif_pos ⟨Nat.le_add_right _ _, by omega⟩]
  exact congrArg b (Fin.ext (by simp))

/-! ## U2. The padded block lengths, and the block embedding

`compAsm` gives block `s` the `f s` coordinates `W * blkOff f s + k`; the words of the block are
`[blkOff f s, blkOff f s + wordsOf (f s))`.  A child programme packs `wordsOf (f s)` words and its
`packMem` knows nothing about the bits of the *last* word above `f s`, so the composite must run the
child at the *padded* length `blkPad W f s = W * wordsOf W (f s)`: then the block's coordinates are
exactly its words.  `compAsm` at `blkPad` is the same vector as at `f` (both are `0` on the padding),
so nothing about the composite datum changes. -/

/-- The padded length of block `s`: its `f s` bits rounded up to whole words. -/
def blkPad {L : ℕ} (W : ℕ) (f : Fin L → ℕ) : Fin L → ℕ := fun s => W * wordsOf W (f s)

lemma wordsOf_blkPad {L W : ℕ} (hW : 0 < W) (f : Fin L → ℕ) (s : Fin L) :
    wordsOf W (blkPad W f s) = wordsOf W (f s) := by
  unfold blkPad
  exact wordsOf_mul W (wordsOf W (f s)) hW

lemma blkPad_words {L W : ℕ} (hW : 0 < W) (f : Fin L → ℕ) (s : Fin L) :
    W * wordsOf W (blkPad W f s) = blkPad W f s := by
  unfold blkPad
  rw [wordsOf_mul W (wordsOf W (f s)) hW]

lemma blkOff_blkPad {L W : ℕ} (hW : 0 < W) (f : Fin L → ℕ) (s : ℕ) :
    blkOff W (blkPad W f) s = blkOff W f s := by
  unfold blkOff
  exact Finset.sum_congr rfl fun t _ => by rw [wordsOf_blkPad hW]

lemma blkTotal_blkPad {L W : ℕ} (hW : 0 < W) (f : Fin L → ℕ) :
    blkTotal W (blkPad W f) = blkTotal W f := by
  unfold blkTotal
  exact Finset.sum_congr rfl fun t _ => wordsOf_blkPad hW f t

/-- Block `s`'s coordinate `k` as a coordinate of the whole composite. -/
def blkEmb {L : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin L → ℕ) (R : ℕ) (s : Fin L) :
    Fin (f s) → Fin (W * blkTotal W f + R) :=
  fun k => ⟨W * blkOff W f s.val + k.val, by
    have h := blkEmb_lt_total W hW f s k
    omega⟩

@[simp] lemma blkEmb_val {L W : ℕ} (hW : 0 < W) (f : Fin L → ℕ) (R : ℕ) (s : Fin L)
    (k : Fin (f s)) : (blkEmb W hW f R s k).val = W * blkOff W f s.val + k.val := rfl

lemma blkEmb_injective {L W : ℕ} (hW : 0 < W) (f : Fin L → ℕ) (R : ℕ) (s : Fin L) :
    Function.Injective (blkEmb W hW f R s) := by
  intro k k' h
  have hv : W * blkOff W f s.val + k.val = W * blkOff W f s.val + k'.val := by
    simpa using congrArg Fin.val h
  exact Fin.ext (by omega)

/-! ## U3. The word-local `packMem` lemmas: the per-block stitching -/

lemma packMem_congr_of_word {M : ℕ} (W : ℕ) {z z' : Fin M → ZMod 2} {a : ℕ}
    (h : ∀ p : Fin M, p.val / W = a → z p = z' p) : packMem W z a = packMem W z' a := by
  unfold packMem
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : p.val / W = a
  · rw [h p hp]
  · rw [if_neg (fun hc => hp hc.1), if_neg (fun hc => hp hc.1)]

lemma compAsmV_zero {L : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin L → ℕ) (R : ℕ) (p : ℕ) :
    compAsmV W hW f R (fun _ _ => 0) (fun _ => 0) p = 0 := by
  unfold compAsmV
  split_ifs <;> rfl

lemma compAsm_zero {L : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin L → ℕ) (R : ℕ) :
    compAsm W hW f R (fun _ _ => 0) (fun _ => 0) = 0 := by
  funext q
  exact compAsmV_zero W hW f R q.val

/-- **The per-block word stitching.**  Word `a` of block `s` of `y + compAsm v u` is word `a` of
`y`'s own block-`s` slice plus `v s` --- provided the block's length is word-padded, so that the
block owns exactly the coordinates of its words. -/
theorem packMem_add_compAsm_blk {L : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin L → ℕ)
    (hpad : ∀ t, W * wordsOf W (f t) = f t) (R : ℕ)
    (v : (s : Fin L) → Fin (f s) → ZMod 2) (u : Fin R → ZMod 2)
    (y : Fin (W * blkTotal W f + R) → ZMod 2) (s : Fin L) {a : ℕ}
    (ha : a < wordsOf W (f s)) :
    packMem W (fun q => y q + compAsm W hW f R v u q) (blkOff W f s.val + a)
      = packMem W (fun k : Fin (f s) => y (blkEmb W hW f R s k) + v s k) a := by
  have hoff : blkOff W f (s.val + 1) = blkOff W f s.val + wordsOf W (f s) := blkOff_succ f s
  -- all coordinates contributing to word `blkOff s + a` are the image of `blkEmb s`
  have hzero : ∀ p ∈ (Finset.univ : Finset (Fin (W * blkTotal W f + R))),
      p ∉ Finset.univ.image (blkEmb W hW f R s) →
      (if p.val / W = blkOff W f s.val + a ∧ (y p + compAsm W hW f R v u p) = 1
        then 2 ^ (p.val % W) else 0) = 0 := by
    intro p _ hp
    rw [if_neg]
    rintro ⟨hdiv, -⟩
    apply hp
    have hle : blkOff W f s.val + a < blkTotal W f := by
      have h1 : blkOff W f s.val + a < blkOff W f (s.val + 1) := by
        rw [hoff]; exact Nat.add_lt_add_left ha _
      have h2 : blkOff W f (s.val + 1) ≤ blkTotal W f := by
        have h3 : blkTotal W f = blkOff W f L := (blkOff_total f (le_refl L)).symm
        rw [h3]
        exact blkOff_mono (W := W) f (show s.val + 1 ≤ L from by have := s.isLt; omega)
      exact lt_of_lt_of_le h1 h2
    have hlt : p.val < W * blkTotal W f := by
      rcases lt_or_ge p.val (W * blkTotal W f) with h | h
      · exact h
      · exfalso
        have h1 : blkTotal W f ≤ p.val / W := by
          refine (Nat.le_div_iff_mul_le hW).mpr ?_
          rw [Nat.mul_comm]; exact h
        omega
    have hblk : compBlk W hW f p.val hlt = s := by
      refine Fin.ext (blkIdx_unique f s.isLt ?_ ?_ (div_lt_blkTotal hW f hlt))
      · omega
      · rw [hoff]; omega
    have hbit : compBit W hW f p.val hlt = a * W + p.val % W := by
      unfold compBit
      rw [hblk, hdiv, Nat.add_sub_cancel_left]
    have hkf : a * W + p.val % W < f s := by
      have h1 : p.val % W < W := Nat.mod_lt _ hW
      calc a * W + p.val % W < a * W + W := by omega
        _ = (a + 1) * W := by ring
        _ ≤ wordsOf W (f s) * W := Nat.mul_le_mul_right W (by omega)
        _ = f s := by rw [Nat.mul_comm, hpad s]
    refine Finset.mem_image.mpr ⟨⟨a * W + p.val % W, hkf⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    rw [blkEmb_val]
    have h := compBlk_bit_eq W hW f hlt
    rw [hblk, hbit] at h
    omega
  have hL : packMem W (fun p => y p + compAsm W hW f R v u p) (blkOff W f s.val + a)
      = ∑ p ∈ Finset.univ.image (blkEmb W hW f R s),
          (if p.val / W = blkOff W f s.val + a ∧ (y p + compAsm W hW f R v u p) = 1
            then 2 ^ (p.val % W) else 0) := by
    unfold packMem
    exact (Finset.sum_subset (Finset.subset_univ _) hzero).symm
  rw [hL, Finset.sum_image (fun x _ y _ h => blkEmb_injective hW f R s h)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hdiv : (blkEmb W hW f R s k).val / W = blkOff W f s.val + k.val / W := by
    rw [blkEmb_val, Nat.add_comm, Nat.add_mul_div_left _ _ hW]
    omega
  have hmod : (blkEmb W hW f R s k).val % W = k.val % W := by
    rw [blkEmb_val, Nat.add_comm, Nat.add_mul_mod_self_left]
  have hcomp : compAsm W hW f R v u (blkEmb W hW f R s k) = v s k := by
    have h := compAsmV_blk W hW f R v u s k
    simpa only [compAsm, blkEmb_val] using h
  rw [hdiv, hmod, hcomp]
  simp only [Nat.add_left_cancel_iff]

/-- `compAsm` only depends on block `s` of `v` inside block `s`'s words. -/
theorem packMem_compAsmV_congr {L : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin L → ℕ) (R : ℕ)
    {v v' : (t : Fin L) → Fin (f t) → ZMod 2} {u u' : Fin R → ZMod 2} {s : Fin L}
    (hv : ∀ t, t ≠ s → v t = v' t) (hu : ∀ p, u p = u' p)
    (z : Fin (W * blkTotal W f + R) → ZMod 2) {q : ℕ}
    (hq : ¬ (blkOff W f s.val ≤ q ∧ q < blkOff W f s.val + wordsOf W (f s))) :
    packMem W (fun p => z p + compAsm W hW f R v u p) q
      = packMem W (fun p => z p + compAsm W hW f R v' u' p) q := by
  refine packMem_congr_of_word W (z := fun p => z p + compAsm W hW f R v u p)
    (z' := fun p => z p + compAsm W hW f R v' u' p) (fun p hp => ?_)
  have hcomp : compAsm W hW f R v u p = compAsm W hW f R v' u' p := by
    show compAsmV W hW f R v u p.val = compAsmV W hW f R v' u' p.val
    unfold compAsmV
    by_cases h1 : p.val < W * blkTotal W f
    · rw [dif_pos h1, dif_pos h1]
      have hblk : compBlk W hW f p.val h1 ≠ s := by
        intro he
        have hb : blkIdx f (p.val / W) (div_lt_blkTotal hW f h1) = s.val := by
          have := congrArg Fin.val he
          simpa [compBlk] using this
        apply hq
        constructor
        · rw [← hb, ← hp]
          exact blkIdx_low f (div_lt_blkTotal hW f h1)
        · rw [← hp, ← blkOff_succ f s, ← hb]
          exact blkIdx_high f (div_lt_blkTotal hW f h1)
      by_cases hk : compBit W hW f p.val h1 < f (compBlk W hW f p.val h1)
      · rw [dif_pos hk, dif_pos hk]
        exact congrFun (hv (compBlk W hW f p.val h1) hblk) ⟨compBit W hW f p.val h1, hk⟩
      · rw [dif_neg hk, dif_neg hk]
    · rw [dif_neg h1, dif_neg h1]
      by_cases h2 : p.val - W * blkTotal W f < R
      · rw [dif_pos h2, dif_pos h2]
        exact hu _
      · rw [dif_neg h2, dif_neg h2]
  rw [hcomp]

/-! ## U4. The per-block contract (the one hypothesis)

`UpBlkSem Sup E T Hs` is the run contract of *one* block: `Sup` compiled at an arbitrary base, started
at that base with `r14` the `det` base, `r15` the payload word base and `r0` the coordinate, run in an
environment whose `det` agrees with the block's table on the block's `2^Wd` addresses.  It must

1. reach `base + Sup.len` (so the appended `halt` — or the next block — is reachable),
2. XOR `Hs (single i 1)` into the payload words `[beta, beta + wordsOf E.W Ms)`,
3. leave every other address alone (two-sided frame: blocks below `beta` are untouched too),
4. preserve `r0`, `r1`, `r2`, `r3`, `r4` (the dispatcher's loop counter, bound, stride and
   base-table pointer).

This is exactly `TogglesWithin` *plus* the four things a composite needs and `TogglesWithin` does not
provide: a payload base, a `det` base, a frame, and register preservation.  It is *weaker* than
`TogglesWithin` at base `0` in one respect (it says nothing about registers other than those five, and
nothing about the `det` outside the block's addresses), and it is uniform in the junk registers, which
is what lets the same `Stmt` be run once per block. -/
def UpBlkSem (Sup : Stmt) (E : RAMEnv) (T : ℝ) {N Ms : ℕ}
    (Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)) : Prop :=
  ∀ (G : Program) (base δ β Bw : ℕ) (dt : ℕ → ℕ) (y : Fin Ms → ZMod 2) (i : Fin N)
    (s : RAMState),
    At G base (Sup.compile base) → s.pc = base →
    δ + Bw ≤ 2 ^ E.W →
    (∀ a < Bw, E.det (δ + a) = dt a) →
    s.regs 14 = δ → s.regs 15 = β → s.regs 0 = i.val →
    (∀ q < wordsOf E.W Ms, s.mem (β + q) = packMem E.W y q) →
    ∃ (k : ℕ) (out : RAMState), (k : ℝ) ≤ T ∧ (step G E)^[k] s = out ∧
      out.pc = base + Sup.len ∧
      (∀ q < wordsOf E.W Ms, out.mem (β + q) = packMem E.W (y + Hs (Pi.single i 1)) q) ∧
      (∀ a, a < β ∨ β + wordsOf E.W Ms ≤ a → out.mem a = s.mem a) ∧
      out.regs 0 = s.regs 0 ∧ out.regs 1 = s.regs 1 ∧ out.regs 2 = s.regs 2 ∧
      out.regs 3 = s.regs 3 ∧ out.regs 4 = s.regs 4

/-- The composite's per-block hypothesis: one contract per child block. -/
def UpChildSem {ι : Type} (Sup : Stmt) (E : RAMEnv) (T : ℝ) {N : ℕ} (Ms : ι → ℕ)
    (Hs : (p : ι) → (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin (Ms p) → ZMod 2)) : Prop :=
  ∀ p : ι, UpBlkSem Sup E T (Hs p)

/-! ## U5. The prologue: read the three metadata cells, start the loop at `r1 = 1`

`compUpStmt`'s loop body computes the `det` base as `r1 * r3` and the base-table entry as `det (r4 + r1)`.
Running `r1 = 1 … l` therefore uses the `det` blocks `[(s+1)*2^Wd, (s+2)*2^Wd)` and the base-table
entries `compPayBase + s`, which is exactly what `compUpDet_child` / `compUpDet_pay` describe.  The
prologue is the three `qDet`s of cells `0, 1, 2` into `r2, r3, r4`, plus `r1 := 1`. -/

/-- The two-instruction idiom `r := det c` for the metadata cells: `r6 := c; r? := det r6`. -/
def compProCode : List Instr :=
  [iImm r6 0, iTbl r2 r6, iImm r6 1, iTbl r3 r6, iImm r6 2, iTbl r4 r6, iImm r1 1]

/-- The composite toggle programme with its prologue. -/
def compUpStmtPro (Sup Scr : Stmt) : Stmt :=
  .seq (.code compProCode) (compUpStmtFull Sup Scr)

/-- The full composite toggle programme, prologue included: `l` child blocks, then the `CR` block. -/
def progUpOfPro (Sup Scr : Stmt) : Program :=
  (compUpStmtPro Sup Scr).compile 0 ++ [Instr.halt]

/-- The tying equation for the prologue programme, by construction. -/
theorem progUpOfPro_eq (Sup Scr : Stmt) :
    ∃ Sup' : Stmt, Sup'.compile 0 ++ [Instr.halt] = progUpOfPro Sup Scr :=
  ⟨compUpStmtPro Sup Scr, rfl⟩

/-- The prologue is the prefix of the programme. -/
theorem progUpOfPro_append (Sup Scr : Stmt) :
    progUpOfPro Sup Scr
      = compProCode ++ ((compUpStmtFull Sup Scr).compile 7 ++ [Instr.halt]) := rfl

theorem at_proCode (Sup Scr : Stmt) : At (progUpOfPro Sup Scr) 0 compProCode := by
  intro r hr
  have h := List.getElem?_append_left (l₁ := compProCode)
    (l₂ := (compUpStmtFull Sup Scr).compile 7 ++ [Instr.halt]) (by simpa using hr)
  simpa [progUpOfPro_append] using h


theorem compProCode_noBranch : NoBranch compProCode := by
  simp [compProCode, NoBranch, Instr.NoBranchI]

/-- **The prologue's run**: seven steps from `initState` reach `pc = 7` with `r1 = 1`, `r2 = l+1`,
`r3 = 2^Wd`, `r4 = compPayBase - 1`, `r0` still the coordinate, and the memory untouched. -/
example (Sup Scr : Stmt) (E : RAMEnv) {N M : ℕ} {y : Fin M → ZMod 2} {i : Fin N} :
    (initState (packMem E.W y) i.val 0 0).pc = 0 := by
  simp [initState]

theorem compPro_sem (Sup Scr : Stmt) (E : RAMEnv) {l Wd Rpad N M : ℕ}
    {y : Fin M → ZMod 2} {i : Fin N}
    (hdet0 : E.det 0 = l + 1) (hdet1 : E.det 1 = 2 ^ Wd)
    (hdet2 : E.det 2 = compPayBase l Wd Rpad - 1)
    (hW1 : 1 < 2 ^ E.W) (h2 : 2 < 2 ^ E.W) (hl : l + 1 < 2 ^ E.W) (hWd : 2 ^ Wd < 2 ^ E.W)
    (hPB : compPayBase l Wd Rpad - 1 < 2 ^ E.W) :
    Sem (progUpOfPro Sup Scr) E 0 7 (initState (packMem E.W y) i.val 0 0)
      (fun k out => k = 7 ∧ out.pc = 7 ∧ out.mem = packMem E.W y ∧
        out.regs 0 = i.val ∧ out.regs 1 = 1 ∧ out.regs 2 = l + 1 ∧
        out.regs 3 = 2 ^ Wd ∧ out.regs 4 = compPayBase l Wd Rpad - 1) := by
  have hno : NoBranch compProCode := compProCode_noBranch
  have e0 : E.det 0 % 2 ^ E.W = l + 1 := by rw [hdet0]; exact Nat.mod_eq_of_lt hl
  have e1 : E.det 1 % 2 ^ E.W = 2 ^ Wd := by rw [hdet1]; exact Nat.mod_eq_of_lt hWd
  have e2 : E.det 2 % 2 ^ E.W = compPayBase l Wd Rpad - 1 := by
    rw [hdet2]; exact Nat.mod_eq_of_lt hPB
  have h1m : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hW1
  have h0m : (0 : ℕ) % 2 ^ E.W = 0 := Nat.zero_mod _
  have h2m : (2 : ℕ) % 2 ^ E.W = 2 := Nat.mod_eq_of_lt h2
  refine Sem.mono (Sem.block (progUpOfPro Sup Scr) E 0 compProCode
    (initState (packMem E.W y) i.val 0 0) (at_proCode Sup Scr) hno (by simp [initState])) ?_
  intro k s' h
  obtain ⟨rfl, rfl⟩ := h
  have hpc : (runBlock compProCode E (initState (packMem E.W y) i.val 0 0)).pc = 7 := by
    rw [runBlock_pc _ _ _ hno]
    simp [compProCode, initState]
  have hmem : (runBlock compProCode E (initState (packMem E.W y) i.val 0 0)).mem
      = packMem E.W y := by
    simp [compProCode, runBlock_cons, runBlock_nil, execInstr, initState]
  refine ⟨rfl, hpc, hmem, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [compProCode, runBlock_cons, runBlock_nil, execInstr, initState,
      e0, e1, e2, h1m, h0m, h2m]

/-! ## U6. The loop body: one dispatch, from the per-block contract

The body of `compUpStmt`'s loop is the fixed three-instruction setup `r14 := r1 * r3`,
`r7 := r4 + r1`, `r15 := det r7`, then one copy of `Sup`, then `blkInc`.  With `r1 = j+1`, `r3 = 2^Wd`
and `r4 = compPayBase - 1` the setup produces the `det` base `(j+1)*2^Wd` and the payload base
`det (compPayBase + j) = beta_j`, so the per-block contract applies verbatim; `blkInc` restores the
counter to `j+2`.  The payload invariant `mem q = packMem (y + compAsm (upPart w j) 0) q` advances by
`packMem_add_compAsm_blk` (inside block `j`'s words) and `packMem_compAsmV_congr` (outside them). -/

/-- The three-instruction setup of the loop body. -/
def blkSetup : List Instr := [iMul r14 r1 r3, iAdd r7 r4 r1, iTbl r15 r7]

/-- The loop body of the toggle dispatcher, spelled out. -/
def blkBody (Sup : Stmt) : Stmt := .seq (.code blkSetup) (.seq Sup (.code blkInc))

theorem compUpStmt_eq_loop (Sup : Stmt) : compUpStmt Sup = .loop blkCond (blkBody Sup) := rfl

theorem blkSetup_noBranch : NoBranch blkSetup := by
  simp [blkSetup, NoBranch, Instr.NoBranchI]

theorem blkInc_noBranch : NoBranch blkInc := by
  simp [blkInc, NoBranch, Instr.NoBranchI]

/-- The partial vector of the first `j` blocks. -/
def upPart {l : ℕ} {f : Fin l → ℕ} (w : (s : Fin l) → Fin (f s) → ZMod 2) (j : ℕ) :
    (s : Fin l) → Fin (f s) → ZMod 2 :=
  fun s k => if s.val < j then w s k else 0

@[simp] lemma upPart_apply {l : ℕ} {f : Fin l → ℕ} (w : (s : Fin l) → Fin (f s) → ZMod 2)
    (j : ℕ) (s : Fin l) (k : Fin (f s)) :
    upPart w j s k = if s.val < j then w s k else 0 := rfl

lemma upPart_zero {l : ℕ} {f : Fin l → ℕ} (w : (s : Fin l) → Fin (f s) → ZMod 2) :
    upPart w 0 = 0 := by
  funext s k; simp

lemma upPart_of_ne {l : ℕ} {f : Fin l → ℕ} (w : (s : Fin l) → Fin (f s) → ZMod 2) {j : ℕ}
    {s : Fin l} (h : s.val ≠ j) :
    upPart w (j + 1) s = upPart w j s := by
  funext k
  simp only [upPart_apply]
  by_cases hlt : s.val < j
  · rw [if_pos (by omega), if_pos hlt]
  · rw [if_neg (by omega), if_neg hlt]

lemma upPart_self {l : ℕ} {f : Fin l → ℕ} (w : (s : Fin l) → Fin (f s) → ZMod 2) (s : Fin l) :
    upPart w (s.val + 1) s = w s := by
  funext k
  simp only [upPart_apply]
  rw [if_pos (by omega)]

/-- The test code of the dispatcher, run. -/
theorem runBlock_test (E : RAMEnv) (s : RAMState) (h : s.regs 1 < s.regs 2) (hW : 1 < 2 ^ E.W) :
    runBlock blkCond.code E s
      = { s with pc := s.pc + 1, regs := Function.update s.regs r7 1 } := by
  simp [blkCond, Cond.code, runBlock_cons, runBlock_nil, execInstr, h, Nat.mod_eq_of_lt hW]

/-- The setup code of the dispatcher, run: the program counter. -/
theorem setup_pc (E : RAMEnv) (s : RAMState) : (runBlock blkSetup E s).pc = s.pc + 3 := by
  simp [blkSetup, runBlock_cons, runBlock_nil, execInstr]

/-- The setup code of the dispatcher, run: the register file. -/
theorem setup_regs (E : RAMEnv) (s : RAMState) :
    (runBlock blkSetup E s).regs
      = Function.update (Function.update (Function.update s.regs r14
          (s.regs 1 * s.regs 3 % 2 ^ E.W)) r7 ((s.regs 4 + s.regs 1) % 2 ^ E.W))
          r15 (E.det ((s.regs 4 + s.regs 1) % 2 ^ E.W) % 2 ^ E.W) := by
  simp [blkSetup, runBlock_cons, runBlock_nil, execInstr]

/-- The setup code of the dispatcher, run: the memory. -/
theorem setup_mem (E : RAMEnv) (s : RAMState) : (runBlock blkSetup E s).mem = s.mem := by
  simp [blkSetup, runBlock_cons, runBlock_nil, execInstr]

/-- The increment code of the dispatcher, run: the program counter. -/
theorem inc_pc (E : RAMEnv) (s : RAMState) : (runBlock blkInc E s).pc = s.pc + 2 := by
  simp [blkInc, runBlock_cons, runBlock_nil, execInstr]

/-- The increment code of the dispatcher, run: the register file. -/
theorem inc_regs (E : RAMEnv) (s : RAMState) :
    (runBlock blkInc E s).regs
      = Function.update (Function.update s.regs r7 (1 % 2 ^ E.W))
          r1 ((s.regs 1 + 1 % 2 ^ E.W) % 2 ^ E.W) := by
  simp [blkInc, runBlock_cons, runBlock_nil, execInstr]

/-- The increment code of the dispatcher, run: the memory. -/
theorem inc_mem (E : RAMEnv) (s : RAMState) : (runBlock blkInc E s).mem = s.mem := by
  simp [blkInc, runBlock_cons, runBlock_nil, execInstr]

/-- The increment's two updates leave registers `0`, `2`, `3`, `4` alone. -/
theorem upd2_zero {f : Fin 16 → ℕ} {x y : ℕ} :
    (Function.update (Function.update f r7 x) r1 y) (0 : Fin 16) = f 0 := by
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]

theorem upd2_two {f : Fin 16 → ℕ} {x y : ℕ} :
    (Function.update (Function.update f r7 x) r1 y) (2 : Fin 16) = f 2 := by
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]

theorem upd2_three {f : Fin 16 → ℕ} {x y : ℕ} :
    (Function.update (Function.update f r7 x) r1 y) (3 : Fin 16) = f 3 := by
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]

theorem upd2_four {f : Fin 16 → ℕ} {x y : ℕ} :
    (Function.update (Function.update f r7 x) r1 y) (4 : Fin 16) = f 4 := by
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]

/-- `j + 2` is below the word count. -/
lemma blk_fit_lt {Wd W j : ℕ} (hWd : 1 ≤ Wd) (h : (j + 2) * 2 ^ Wd ≤ W) : j + 2 < W := by
  have hp : 2 ≤ 2 ^ Wd := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ Wd := Nat.pow_le_pow_right (by norm_num) hWd
  have hlt : 1 < 2 ^ Wd := by omega
  have hpos : 0 < j + 2 := by omega
  have h2 : (j + 2) * 1 < (j + 2) * 2 ^ Wd := Nat.mul_lt_mul_of_pos_left hlt hpos
  rw [Nat.mul_one] at h2
  omega

/-- The block's `det` range fits in a word: from `(j+2)*2^Wd ≤ W`. -/
lemma blk_fit {Wd W j : ℕ} (h : (j + 2) * 2 ^ Wd ≤ W) :
    (j + 1) * 2 ^ Wd + 2 ^ Wd ≤ W ∧ (j + 1) * 2 ^ Wd < W := by
  have hp : 0 < 2 ^ Wd := Nat.two_pow_pos Wd
  have h1 : (j + 1) * 2 ^ Wd + 2 ^ Wd = (j + 2) * 2 ^ Wd := by ring
  have h2 : (j + 1) * 2 ^ Wd + 2 ^ Wd ≤ W := by rw [h1]; exact h
  exact ⟨h2, by omega⟩

set_option maxHeartbeats 1600000 in
/-- **One dispatch.**  From the loop body's entry (program counter `9`, `r1 = j+1`), the fixed setup,
one copy of `Sup` and the increment return to the loop head (`7`) with `r1 = j+2` and the payload
invariant advanced from `upPart w j` to `upPart w (j+1)`. -/
theorem upBody_step (P : Program) (Sup : Stmt) (E : RAMEnv)
    {l N Wd Rpad Rcr : ℕ} {f : Fin l → ℕ} {w : (s : Fin l) → Fin (f s) → ZMod 2}
    {Hs : (s : Fin l) → (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin (f s) → ZMod 2)}
    {dt : Fin l → ℕ → ℕ} {b : Fin l → ℕ} {Tu : ℝ} (hTu : 0 ≤ Tu)
    (hW : 0 < E.W) (hW1 : 1 < 2 ^ E.W) (hWd1 : 1 ≤ Wd) (hpad : ∀ s : Fin l, E.W * wordsOf E.W (f s) = f s)
    (hUp : UpChildSem Sup E Tu f Hs)
    (hdt : ∀ (s : Fin l) (a : ℕ), a < 2 ^ Wd → E.det ((s.val + 1) * 2 ^ Wd + a) = dt s a)
    (hb : ∀ s : Fin l, b s = blkOff E.W f s.val)
    (hfit2 : ∀ s : Fin l, (s.val + 2) * 2 ^ Wd ≤ 2 ^ E.W)
    (hPB : ∀ s : Fin l, compPayBase l Wd Rpad - 1 + (s.val + 1) = compPayBase l Wd Rpad + s.val)
    (hPBlt : ∀ s : Fin l, compPayBase l Wd Rpad + s.val < 2 ^ E.W)
    (hbw : ∀ s : Fin l, b s < 2 ^ E.W)
    (hpaydet : ∀ s : Fin l, E.det (compPayBase l Wd Rpad + s.val) = b s)
    (hAtSetup : At P 9 blkSetup) (hAtSup : At P 12 (Sup.compile 12))
    (hAtInc : At P (12 + Sup.len) blkInc) (hjmp : P[14 + Sup.len]? = some (iJmp 7))
    (y : Fin (E.W * blkTotal E.W f + Rcr) → ZMod 2) (i : Fin N) (j : Fin l) (s : RAMState)
    (hpc : s.pc = 9) (h0 : s.regs 0 = i.val) (h1 : s.regs 1 = j.val + 1)
    (h2 : s.regs 2 = l + 1) (h3 : s.regs 3 = 2 ^ Wd)
    (h4 : s.regs 4 = compPayBase l Wd Rpad - 1)
    (hw : w = fun (s : Fin l) => Hs s (Pi.single i 1))
    (hmem : ∀ q, s.mem q = packMem E.W (y + compAsm E.W hW f Rcr (upPart w j.val) 0) q) :
    ∃ (c : ℕ) (out : RAMState), (c : ℝ) ≤ Tu + 6 ∧ (step P E)^[c] s = out ∧
      out.pc = 7 ∧ out.regs 0 = i.val ∧ out.regs 1 = j.val + 2 ∧ out.regs 2 = l + 1 ∧
      out.regs 3 = 2 ^ Wd ∧ out.regs 4 = compPayBase l Wd Rpad - 1 ∧
      (∀ q, out.mem q = packMem E.W (y + compAsm E.W hW f Rcr (upPart w (j.val + 1)) 0) q) := by
  -- the setup, run
  have hs1pc : s.pc + 3 = 12 := by rw [hpc]
  have hreg14 : s.regs 1 * s.regs 3 % 2 ^ E.W = (j.val + 1) * 2 ^ Wd := by
    rw [h1, h3]
    exact Nat.mod_eq_of_lt (blk_fit (hfit2 j)).2
  have hreg7 : (s.regs 4 + s.regs 1) % 2 ^ E.W = compPayBase l Wd Rpad + j.val := by
    rw [h4, h1, hPB j]
    exact Nat.mod_eq_of_lt (hPBlt j)
  have hreg15 : E.det ((s.regs 4 + s.regs 1) % 2 ^ E.W) % 2 ^ E.W = b j := by
    rw [hreg7, hpaydet j]
    exact Nat.mod_eq_of_lt (hbw j)
  obtain ⟨hs2pc, hs2regs, hs2mem⟩ : (runBlock blkSetup E s).pc = 12 ∧
      (runBlock blkSetup E s).regs = Function.update (Function.update
        (Function.update s.regs r14 ((j.val + 1) * 2 ^ Wd)) r7 (compPayBase l Wd Rpad + j.val))
        r15 (b j) ∧ (runBlock blkSetup E s).mem = s.mem := by
    refine ⟨?_, ?_, ?_⟩
    · rw [setup_pc]; exact hs1pc
    · rw [setup_regs, hreg14, hreg15, hreg7]
    · rw [setup_mem]
  have hstep_setup : (step P E)^[3] s = runBlock blkSetup E s := by
    have h := iterate_runBlock_of_at P E blkSetup s (by rw [hpc]; exact hAtSetup) blkSetup_noBranch
    simpa [blkSetup] using h
  -- the register facts at the child's entry
  set s3 := runBlock blkSetup E s with hs3
  have hpc3 : s3.pc = 12 := hs2pc
  have hr14 : s3.regs 14 = (j.val + 1) * 2 ^ Wd := by
    rw [hs2regs]; simp
  have hr7 : s3.regs 7 = compPayBase l Wd Rpad + j.val := by
    rw [hs2regs]; simp
  have hr15 : s3.regs 15 = b j := by
    rw [hs2regs]; simp
  have hr0 : s3.regs 0 = i.val := by rw [hs2regs]; simp [h0]
  have hr1 : s3.regs 1 = j.val + 1 := by rw [hs2regs]; simp [h1]
  have hr2 : s3.regs 2 = l + 1 := by rw [hs2regs]; simp [h2]
  have hr3 : s3.regs 3 = 2 ^ Wd := by rw [hs2regs]; simp [h3]
  have hr4 : s3.regs 4 = compPayBase l Wd Rpad - 1 := by rw [hs2regs]; simp [h4]
  have hmem3 : s3.mem = s.mem := hs2mem
  -- the payload slice the block sees
  set ys : Fin (f j) → ZMod 2 :=
    fun k => y (blkEmb E.W hW f Rcr j k) + upPart w j.val j k with hys
  have hpay : ∀ q < wordsOf E.W (f j), s3.mem (b j + q) = packMem E.W ys q := by
    intro q hq
    rw [hmem3, hmem (b j + q), hb j]
    exact packMem_add_compAsm_blk E.W hW f hpad Rcr (upPart w j.val) 0 y j hq
  -- the per-block contract
  obtain ⟨k, s4, hk, hstep_child, hpc4, hpay4, hframe4, hr0', hr1', hr2', hr3', hr4'⟩ :=
    hUp j P 12 ((j.val + 1) * 2 ^ Wd) (b j) (2 ^ Wd) (dt j) ys i s3 hAtSup hpc3
      (blk_fit (hfit2 j)).1 (hdt j) hr14 hr15 hr0 hpay
  -- the increment, run
  have hpc4' : s4.pc = 12 + Sup.len := hpc4
  have hstep_inc : (step P E)^[2] s4 = runBlock blkInc E s4 := by
    have h := iterate_runBlock_of_at P E blkInc s4 (by rw [hpc4']; exact hAtInc) blkInc_noBranch
    simpa [blkInc] using h
  set s5 := runBlock blkInc E s4 with hs5
  have hpc5 : s5.pc = 14 + Sup.len := by rw [inc_pc, hpc4']; omega
  have hmem5 : s5.mem = s4.mem := inc_mem E s4
  have hstep_jmp : (step P E)^[1] s5 = { s5 with pc := 7 } := by
    rw [Function.iterate_one, step_eq_execInstr P E s5 (iJmp 7) (by rw [hpc5]; exact hjmp),
      execInstr_jmp]
  -- glue the iterates
  have glue : ∀ (m n : ℕ) (x y z : RAMState), (step P E)^[m] x = y →
      (step P E)^[n] y = z → (step P E)^[n + m] x = z := by
    intro m n x y z h1' h2'
    rw [Function.iterate_add_apply, h1', h2']
  have e1 : (step P E)^[k + 3] s = s4 := glue 3 k s s3 s4 hstep_setup hstep_child
  have e2 : (step P E)^[2 + (k + 3)] s = s5 := glue (k + 3) 2 s s4 s5 e1 hstep_inc
  have e3 : (step P E)^[1 + (2 + (k + 3))] s = { s5 with pc := 7 } :=
    glue (2 + (k + 3)) 1 s s5 { s5 with pc := 7 } e2 hstep_jmp
  have eall : (step P E)^[k + 6] s = { s5 with pc := 7 } := by
    rwa [show 1 + (2 + (k + 3)) = k + 6 from by omega] at e3
  have h1m : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hW1
  have hreg_out : ({ s5 with pc := 7 } : RAMState).regs
      = Function.update (Function.update s4.regs r7 (1 % 2 ^ E.W))
          r1 ((s4.regs 1 + 1 % 2 ^ E.W) % 2 ^ E.W) := by
    rw [hs5, inc_regs]
  refine ⟨k + 6, { s5 with pc := 7 }, ?_, eall, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- cost
    have hkR : (k : ℝ) ≤ Tu := hk
    have hk6 : ((k + 6 : ℕ) : ℝ) = (k : ℝ) + 6 := by push_cast; ring
    rw [hk6]; linarith
  · simp
  · rw [hreg_out, upd2_zero, hr0', hr0]
  · rw [hreg_out]
    have h5 : (Function.update (Function.update s4.regs r7 (1 % 2 ^ E.W))
        r1 ((s4.regs 1 + 1 % 2 ^ E.W) % 2 ^ E.W)) 1
        = (s4.regs 1 + 1 % 2 ^ E.W) % 2 ^ E.W := Function.update_self _ _ _
    rw [h5, hr1', hr1, h1m]
    rw [show j.val + 1 + 1 = j.val + 2 from by omega]
    exact Nat.mod_eq_of_lt (blk_fit_lt hWd1 (hfit2 j))
  · rw [hreg_out, upd2_two, hr2', hr2]
  · rw [hreg_out, upd2_three, hr3', hr3]
  · rw [hreg_out, upd2_four, hr4', hr4]
  · -- the payload invariant advances
    intro q
    have hmem5' : ({ s5 with pc := 7 } : RAMState).mem q = s4.mem q := by rw [hmem5]
    rw [hmem5']
    by_cases hq : b j ≤ q ∧ q < b j + wordsOf E.W (f j)
    · obtain ⟨hq1, hq2⟩ := hq
      have ha : q - b j < wordsOf E.W (f j) := by omega
      have hqe : b j + (q - b j) = q := by omega
      have hL : s4.mem q = packMem E.W (ys + Hs j (Pi.single i 1)) (q - b j) := by
        conv_lhs => rw [show q = b j + (q - b j) from by omega]
        exact hpay4 (q - b j) ha
      rw [hL]
      have hslice : (fun k : Fin (f j) => y (blkEmb E.W hW f Rcr j k)
            + upPart w (j.val + 1) j k) = ys + Hs j (Pi.single i 1) := by
        funext k
        have h1' : upPart w (j.val + 1) j k = w j k := by
          rw [upPart_apply, if_pos (by omega)]
        have h2' : upPart w j.val j k = 0 := by
          rw [upPart_apply, if_neg (by omega)]
        have h3' : w j k = Hs j (Pi.single i 1) k := by rw [hw]
        simp only [hys, Pi.add_apply, h1', h2', h3', add_zero, zero_add]
      have hstep := packMem_add_compAsm_blk E.W hW f hpad Rcr (upPart w (j.val + 1)) 0 y j ha
      rw [hslice, ← hb j, hqe] at hstep
      exact hstep.symm
    · have hout : s4.mem q = s.mem q := by
        rcases not_and_or.mp hq with h | h
        · exact hframe4 q (Or.inl (by omega))
        · exact hframe4 q (Or.inr (by omega))
      rw [hout, hmem q]
      exact (packMem_compAsmV_congr (W := E.W) (hW := hW) (f := f) (R := Rcr) (s := j)
        (v := upPart w j.val) (v' := upPart w (j.val + 1)) (u := 0) (u' := 0)
        (fun t ht => (upPart_of_ne (f := f) w (j := j.val) (s := t)
          (by intro hc; exact ht (Fin.ext hc))).symm) (fun _ => rfl) y (by
          intro hc
          exact hq ⟨by rw [hb j]; exact hc.1, by rw [hb j]; exact hc.2⟩))

/-- Gluing two exact iterates. -/
lemma step_glue (P : Program) (E : RAMEnv) : ∀ (m n : ℕ) (x y z : RAMState),
    (step P E)^[m] x = y → (step P E)^[n] y = z → (step P E)^[n + m] x = z := by
  intro m n x y z h1 h2
  rw [Function.iterate_add_apply, h1, h2]

set_option maxHeartbeats 1600000 in
/-- **The `l`-block stitching.**  From the loop head with `r1 = 1`, `l` iterations of the dispatch
reach the loop head again with `r1 = l+1` and the payload equal to `y` toggled by all `l` blocks. -/
theorem upLoop_iterate (P : Program) (Sup : Stmt) (E : RAMEnv)
    {l N Wd Rpad Rcr : ℕ} {f : Fin l → ℕ} {w : (s : Fin l) → Fin (f s) → ZMod 2}
    {Hs : (s : Fin l) → (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin (f s) → ZMod 2)}
    {dt : Fin l → ℕ → ℕ} {b : Fin l → ℕ} {Tu : ℝ} (hTu : 0 ≤ Tu)
    (hW : 0 < E.W) (hW1 : 1 < 2 ^ E.W) (hWd1 : 1 ≤ Wd)
    (hpad : ∀ s : Fin l, E.W * wordsOf E.W (f s) = f s)
    (hUp : UpChildSem Sup E Tu f Hs)
    (hdt : ∀ (s : Fin l) (a : ℕ), a < 2 ^ Wd → E.det ((s.val + 1) * 2 ^ Wd + a) = dt s a)
    (hb : ∀ s : Fin l, b s = blkOff E.W f s.val)
    (hfit2 : ∀ s : Fin l, (s.val + 2) * 2 ^ Wd ≤ 2 ^ E.W)
    (hPB : ∀ s : Fin l, compPayBase l Wd Rpad - 1 + (s.val + 1) = compPayBase l Wd Rpad + s.val)
    (hPBlt : ∀ s : Fin l, compPayBase l Wd Rpad + s.val < 2 ^ E.W)
    (hbw : ∀ s : Fin l, b s < 2 ^ E.W)
    (hpaydet : ∀ s : Fin l, E.det (compPayBase l Wd Rpad + s.val) = b s)
    (hAtCode : At P 7 blkCond.code) (hjz : ∃ t : ℕ, P[8]? = some (iJz r7 t))
    (hAtSetup : At P 9 blkSetup) (hAtSup : At P 12 (Sup.compile 12))
    (hAtInc : At P (12 + Sup.len) blkInc) (hjmp : P[14 + Sup.len]? = some (iJmp 7))
    (y : Fin (E.W * blkTotal E.W f + Rcr) → ZMod 2) (i : Fin N)
    (hw : w = fun (s : Fin l) => Hs s (Pi.single i 1)) (s0 : RAMState)
    (hpc0 : s0.pc = 7) (h0 : s0.regs 0 = i.val) (h10 : s0.regs 1 = 1)
    (h20 : s0.regs 2 = l + 1) (h30 : s0.regs 3 = 2 ^ Wd)
    (h40 : s0.regs 4 = compPayBase l Wd Rpad - 1)
    (hmem0 : ∀ q, s0.mem q = packMem E.W y q) :
    ∀ j, j ≤ l → ∃ (c : ℕ) (out : RAMState), (c : ℝ) ≤ 8 * (j : ℝ) + (j : ℝ) * Tu ∧
      (step P E)^[c] s0 = out ∧ out.pc = 7 ∧ out.regs 0 = i.val ∧
      out.regs 1 = j + 1 ∧ out.regs 2 = l + 1 ∧ out.regs 3 = 2 ^ Wd ∧
      out.regs 4 = compPayBase l Wd Rpad - 1 ∧
      (∀ q, out.mem q = packMem E.W (y + compAsm E.W hW f Rcr (upPart w j) 0) q) := by
  intro j
  induction j with
  | zero =>
      intro _
      refine ⟨0, s0, by simp, rfl, hpc0, h0, ?_, h20, h30, h40, ?_⟩
      · simpa using h10
      · intro q
        rw [hmem0 q, upPart_zero]
        have hz : compAsm E.W hW f Rcr (0 : (s : Fin l) → Fin (f s) → ZMod 2)
            (0 : Fin Rcr → ZMod 2) = 0 := compAsm_zero E.W hW f Rcr
        rw [hz, add_zero]
  | succ j ih =>
      intro hj
      have hj' : j < l := by omega
      obtain ⟨c, out, hc, hstep, hpc, h0, h1, h2, h3, h4, hmem⟩ := ih (by omega)
      -- the test and the `jz` fall-through
      have hlt : out.regs 1 < out.regs 2 := by rw [h1, h2]; omega
      have htest : (step P E)^[1] out = runBlock blkCond.code E out := by
        have h := iterate_runBlock_of_at P E blkCond.code out (by rw [hpc]; exact hAtCode)
          (Cond.noBranch_code _)
        simpa [blkCond, Cond.code] using h
      have hs1 : runBlock blkCond.code E out
          = { out with pc := out.pc + 1, regs := Function.update out.regs r7 1 } :=
        runBlock_test E out hlt hW1
      have hreg7 : (runBlock blkCond.code E out).regs r7 = 1 := by rw [hs1]; simp
      have hpc8 : (runBlock blkCond.code E out).pc = 8 := by rw [hs1]; simp [hpc]
      obtain ⟨tz, hjzt⟩ := hjz
      have hjz8 : P[(runBlock blkCond.code E out).pc]? = some (iJz r7 tz) := by
        rw [hpc8]; exact hjzt
      have hstep_jz : (step P E)^[1] (runBlock blkCond.code E out)
          = { runBlock blkCond.code E out with pc := 9 } := by
        rw [Function.iterate_one,
          step_eq_execInstr P E _ (iJz r7 tz) hjz8, execInstr_jz]
        rw [hreg7]
        simp [hpc8]
      -- the body
      obtain ⟨k, out', hk, hstep_body, hpc', h0', h1', h2', h3', h4', hmem'⟩ :=
        upBody_step P Sup E (l := l) (N := N) (Wd := Wd) (Rpad := Rpad) (Rcr := Rcr)
          (f := f) (w := w) (Hs := Hs) (dt := dt) (b := b) (Tu := Tu)
          hTu hW hW1 hWd1 hpad hUp hdt hb hfit2 hPB hPBlt hbw hpaydet
          hAtSetup hAtSup hAtInc hjmp y i ⟨j, hj'⟩
          { runBlock blkCond.code E out with pc := 9 } rfl
          (by rw [hs1]; simp [h0])
          (by rw [hs1]; simp [h1])
          (by rw [hs1]; simp [h2])
          (by rw [hs1]; simp [h3])
          (by rw [hs1]; simp [h4])
          hw
          (by intro q
              show (runBlock blkCond.code E out).mem q = _
              rw [show (runBlock blkCond.code E out).mem = out.mem from by rw [hs1]]
              exact hmem q)
      -- glue the pieces: test+jz (2 steps), then the body (`k` steps)
      have g1 : (step P E)^[1 + 1] out
          = { runBlock blkCond.code E out with pc := 9 } := by
        rw [Function.iterate_add_apply, htest, hstep_jz]
      have g2 : (step P E)^[k + 2] out = out' :=
        step_glue P E 2 k out { runBlock blkCond.code E out with pc := 9 } out'
          (by simpa using g1) hstep_body
      have gall : (step P E)^[(k + 2) + c] s0 = out' :=
        step_glue P E c (k + 2) s0 out out' hstep g2
      have hcost : ((c + (k + 2) : ℕ) : ℝ) ≤ 8 * ((j + 1 : ℕ) : ℝ)
          + ((j + 1 : ℕ) : ℝ) * Tu := by
        have hkR : (k : ℝ) ≤ Tu + 6 := hk
        have hcj : (c : ℝ) ≤ 8 * (j : ℝ) + (j : ℝ) * Tu := hc
        have hck : ((c + (k + 2) : ℕ) : ℝ) = (c : ℝ) + ((k : ℝ) + 2) := by
          push_cast; ring
        have hj1 : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
        rw [hck, hj1]
        have h1 : (k : ℝ) + 2 ≤ Tu + 8 := by linarith
        have h2 : (c : ℝ) + ((k : ℝ) + 2) ≤
            (8 * (j : ℝ) + (j : ℝ) * Tu) + (Tu + 8) := by linarith
        calc (c : ℝ) + ((k : ℝ) + 2)
            ≤ (8 * (j : ℝ) + (j : ℝ) * Tu) + (Tu + 8) := h2
          _ = 8 * ((j : ℝ) + 1) + ((j : ℝ) + 1) * Tu := by ring
      refine ⟨c + (k + 2), out', hcost, ?_, hpc', h0', ?_, h2', h3', h4', hmem'⟩
      · rw [show c + (k + 2) = (k + 2) + c from by omega]
        exact gall
      · show out'.regs 1 = j + 1 + 1
        rw [h1']
/-- `upPart` at the top is the whole vector. -/
lemma upPart_top {l : ℕ} {f : Fin l → ℕ} (w : (s : Fin l) → Fin (f s) → ZMod 2) :
    upPart w l = w := by
  funext s k
  simp only [upPart_apply]
  rw [if_pos s.isLt]

/-- The children's words of `compAsm` do not depend on the `CR` part. -/
theorem packMem_compAsmV_congr_v {L : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin L → ℕ) (R : ℕ)
    {v v' : (t : Fin L) → Fin (f t) → ZMod 2} {u u' : Fin R → ZMod 2} (hv : v = v')
    (z : Fin (W * blkTotal W f + R) → ZMod 2) {q : ℕ} (hq : q < blkTotal W f) :
    packMem W (fun p => z p + compAsm W hW f R v u p) q
      = packMem W (fun p => z p + compAsm W hW f R v' u' p) q := by
  refine packMem_congr_of_word W (z := fun p => z p + compAsm W hW f R v u p)
    (z' := fun p => z p + compAsm W hW f R v' u' p) (fun p hp => ?_)
  have hp' : p.val < W * blkTotal W f := by
    have h1 : p.val / W < blkTotal W f := by rw [hp]; exact hq
    have h2 : p.val = W * (p.val / W) + p.val % W := (Nat.div_add_mod p.val W).symm
    have h3 : p.val % W < W := Nat.mod_lt _ hW
    have h4 : W * (p.val / W) + W ≤ W * blkTotal W f := by
      rw [← Nat.mul_succ]
      exact Nat.mul_le_mul_left W (by omega)
    omega
  have hcomp : compAsm W hW f R v u p = compAsm W hW f R v' u' p := by
    show compAsmV W hW f R v u p.val = compAsmV W hW f R v' u' p.val
    unfold compAsmV
    rw [dif_pos hp', dif_pos hp', hv]
  rw [hcomp]

/-- The `CR` words of `y + compAsm` are the `CR` block's own packed words. -/
theorem packMem_add_compAsm_cr {L : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin L → ℕ) (R : ℕ)
    (v : (t : Fin L) → Fin (f t) → ZMod 2) (u : Fin R → ZMod 2)
    (y : Fin (W * blkTotal W f + R) → ZMod 2) {q : ℕ} (hq : q < wordsOf W R) :
    packMem W (fun x => y x + compAsm W hW f R v u x) (blkTotal W f + q)
      = packMem W (fun p : Fin R => y ⟨W * blkTotal W f + p.val, by
          have := p.isLt; omega⟩ + u p) q := by
  -- every coordinate of word `t + q` is `W*t + p`
  have hzero : ∀ p ∈ (Finset.univ : Finset (Fin (W * blkTotal W f + R))),
      p ∉ Finset.univ.image (fun r : Fin R => (⟨W * blkTotal W f + r.val, by have := r.isLt; omega⟩ :
        Fin (W * blkTotal W f + R))) →
      (if p.val / W = blkTotal W f + q ∧ (y p + compAsm W hW f R v u p) = 1 then 2 ^ (p.val % W) else 0) = 0 := by
    intro p _ hp
    rw [if_neg]
    rintro ⟨hdiv, -⟩
    apply hp
    have hge : W * blkTotal W f ≤ p.val := by
      have : blkTotal W f ≤ p.val / W := by omega
      have h2 : p.val = W * (p.val / W) + p.val % W := (Nat.div_add_mod p.val W).symm
      have h3 : p.val % W < W := Nat.mod_lt _ hW
      have : W * blkTotal W f ≤ W * (p.val / W) := Nat.mul_le_mul_left W (by omega)
      omega
    have hlt : p.val - W * blkTotal W f < R := by
      have := p.isLt
      omega
    refine Finset.mem_image.mpr ⟨⟨p.val - W * blkTotal W f, hlt⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    simp
    omega
  have hL : packMem W (fun x => y x + compAsm W hW f R v u x) (blkTotal W f + q)
      = ∑ p ∈ Finset.univ.image (fun r : Fin R => (⟨W * blkTotal W f + r.val, by
          have := r.isLt; omega⟩ : Fin (W * blkTotal W f + R))),
          (if p.val / W = blkTotal W f + q ∧ (y p + compAsm W hW f R v u p) = 1
            then 2 ^ (p.val % W) else 0) := by
    unfold packMem
    exact (Finset.sum_subset (Finset.subset_univ _) hzero).symm
  rw [hL, Finset.sum_image]
  · refine Finset.sum_congr rfl fun r _ => ?_
    have hdiv : (W * blkTotal W f + r.val) / W = blkTotal W f + r.val / W := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hW]
      omega
    have hmod : (W * blkTotal W f + r.val) % W = r.val % W := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left]
    have hcomp : compAsm W hW f R v u ⟨W * blkTotal W f + r.val, by have := r.isLt; omega⟩
        = u r := by
      have h := compAsmV_cr W hW f R v u r
      simpa [compAsm] using h
    rw [hdiv, hmod, hcomp]
    simp only [Nat.add_left_cancel_iff]
  · intro x _ y' _ hxy
    apply Fin.ext
    simp only [Fin.mk.injEq] at hxy
    omega

end

end LinearSetReconciliation327.Main


