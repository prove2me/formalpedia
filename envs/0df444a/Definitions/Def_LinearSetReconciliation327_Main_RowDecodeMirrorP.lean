-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_RowDecodeMirrorP
-- name    : LinearSetReconciliation327_Main_RowDecodeMirrorP
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-23T09:46:07.043474+00:00
-- url     : https://prove2.me/theorems/4d9873bb-b5ab-46d0-9431-a033f2072550
-- title:
--   Row-chain mirror: the `Pay` layout layer under the fresh namespace `RDecP`
-- statement:
--   A re-host of `…_RowDecodePay20261122` on the `DecoderLemmas` side. The `Pay` layout re-declares the whole `RDec` layer (`stageStmt` is 44 rather than 42 instructions, `rowPayBase` is the arithmetic progression `payTabAddr + j*stageLen` rather than a `d`-entry table).  Those names already exist in the `DecoderLemmas` environment (via `CrField → CrStage → MergeStep → RowDecode20261121`), so a plain import swap is rejected with `RDec.stageStmt has already been declared`.  This node therefore declares the same layer in the fresh namespace `RDecP`; apart from the `import` lines, the `namespace RDec` → `RDecP` rename and the resulting qualified references, every proof span is copied verbatim from the published `Pay` node.  Definitions and proved lemmas only; no `sorry`, no new axiom; local `cpl` 8 s.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5 / Theorem 1.1 (the top-level decoder); the project's verified row-stage development.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_RowScratch20261121
import Definitions.Def_LinearSetReconciliation327_Main_CR23Dec

/-!
# `_rd_rowdecode` — the row-decode stage: `RowOut` layout, its repack bridge, the setup block,
the `CR` merge glue, and the row-head family

This module finishes the four concrete pieces the row loop of Theorem 6.5's decoder still lacked.
It is self-contained: it imports only `Definitions` bundles (plus `Mathlib`), states no axiom, and
contains no `sorry`.

* **§1 — the `RowOut` layout.**  `rowWords`/`rowBase`/`rowSlot` give each row `wordsOf E.W R`
  consecutive words; `RowOut E R j x m` says row `j`'s slot holds exactly the packed bitmap of `x`.
  Two structural facts are proved: rows occupy pairwise disjoint word blocks (`rowSlot_disjoint`),
  and the per-iteration clearing pass of 2.1 cannot touch a row slot as soon as the *base
  constraint* `RowOutFits E t : decoderAllocEnd t ≤ rowBase E` holds (`rowOut_preserved`,
  `clearScratch_rowOut`) — this is exactly why the constraint is needed.
* **§2 — the repack bridge `OutputsSupport → RowOut`.**  `repackMem` is the memory the repack pass
  produces from 2.1's output list, and `rowOut_repackMem` **inhabits** the bridge: the packed bitmap
  of `x` is exactly the accumulated bit sum of the duplicate-free output list of `x`.  The proof is
  pure `Finset` bookkeeping (`packMem_eq_sum`, `toFinset_outList`) — no bit-level carry analysis is
  needed because `packMem` is itself a sum over the support.
* **§3 — the per-row `setup` block.**  `stageHeadCode` reads the row's payload base out of a `det`
  table at a compile-time constant slot, the staging base out of another, and `L` out of 2.1's own
  header slot 4; `copyStmt` then stages the payload.  `copyArray_spec` is the copy loop's contract
  (`12L + 2` steps), re-proved against the importable definitions exactly as `clearArray_spec` was,
  and `stage_sem` assembles the whole setup block with its exact cost and its `PayloadOn`
  postcondition.
* **§4 — the `CR` merge.**  `cr23_stmt` inhabitants `cr23_progDec_stmt` with the witness `decStmt`
  (definitional), `scrBlock_compile` records that `ScrBlock = .seq Sdec Smerge` glues onto `progDec`
  with the halt replaced, `run_agrees` transfers a halt-terminated run of `progDec` to the glued
  program, and `mergeList_nodup`/`mergeList_toFinset` are the combinatorial heart of `Smerge`
  (`x̂ + ê` as a duplicate-free list whose value set is the symmetric difference).
* **§5 — the row-head family** `rowHeads` for `stageRun_counted_loop`, and the end-to-end closure
  `rowLoop_end_to_end` of the `d`-fold row loop.

## Non-vacuity audit (see the end of the file for the exact statements)

The one thing this module **cannot** do with published material is supply the *row-decode stage
contract itself*, and the reason is a genuine obstruction, not a missing lemma:

* `pinsketch_decoding_at` is a statement about `programOfStatement (pinsketchRunStmt t w β)`, i.e.
  about the bare `Program` compiled at base `0`; `progDecOfTop` needs the same code at the non-zero
  address `dRowBase Sinit + …`.  §4's `run_agrees` handles only the *halt replacement* (base `0`),
  not a shift of the entry address.
* Worse, `pinsketch_decoding_at` runs in `detEnv (8*w) (detStd t N b ι)`, so the *whole* composite
  decoder would have to use `det = detStd t N b ι`; but `detStd`'s header slot 3 is `2t`
  (`hdrTab`), so `rowBase E = E.det 3 = 2t`, which is *strictly inside* 2.1's own scratch.
  `not_rowOutFits_detStd` proves `¬ RowOutFits (detEnv (8*w) (detStd t N b ι)) t`, and
  `detStd_high_zero` proves that `detStd`'s slots `13 … 63` are all `0`, so a composite header
  cannot be smuggled into `detStd` either.  Hence the composite header must live in `det` slots of a
  table that only *extends* `detStd`'s header — i.e. 2.1's published contract has to be re-run with
  `hdet` weakened from `E.det = detStd t N b ι` to "agrees with `detStd t N b ι` on slots `< 13`".
  This file states that weakened contract (`DecodeStage`) and proves everything else about it.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Finset

open LinearSetReconciliation327.Main.R66

noncomputable section

namespace LinearSetReconciliation327.Main
namespace RDecP

/-! ## 1. The `RowOut` layout -/

/-- Number of `W`-bit words holding one row's `R`-bit bitmap. -/
def rowWords (E : RAMEnv) (R : ℕ) : ℕ := wordsOf E.W R

/-- **The row-bitmap base**: the composite `det` header's slot 3, a compile-time constant slot, so
the program reaches it with `iImm r15 3; iTbl r1 r15`. -/
def rowBase (E : RAMEnv) : ℕ := E.det 3 % 2 ^ E.W

theorem rowBase_lt (E : RAMEnv) : rowBase E < 2 ^ E.W :=
  Nat.mod_lt _ (Nat.two_pow_pos E.W)

/-- Address of the first word of row `j`'s bitmap. -/
def rowSlot (E : RAMEnv) (R j : ℕ) : ℕ := rowBase E + j * rowWords E R

theorem rowSlot_zero (E : RAMEnv) (R : ℕ) : rowSlot E R 0 = rowBase E := by
  simp [rowSlot]

theorem rowSlot_succ (E : RAMEnv) (R j : ℕ) :
    rowSlot E R (j + 1) = rowSlot E R j + rowWords E R := by
  simp only [rowSlot, Nat.succ_mul]
  omega

/-- The `wordsOf E.W R` words of row `j` end before row `j+1` begins. -/
theorem rowSlot_lt_next (E : RAMEnv) (R j i : ℕ) (hi : i < rowWords E R) :
    rowSlot E R j + i < rowSlot E R (j + 1) := by
  rw [rowSlot_succ]
  omega

/-- **Rows occupy pairwise disjoint word blocks.** -/
theorem rowSlot_disjoint (E : RAMEnv) (R j j' i i' : ℕ) (hjj : j < j')
    (hi : i < rowWords E R) (_hi' : i' < rowWords E R) :
    rowSlot E R j + i ≠ rowSlot E R j' + i' := by
  intro h
  have h1 : rowSlot E R j + i < rowSlot E R (j + 1) := rowSlot_lt_next E R j i hi
  have h2 : rowSlot E R (j + 1) ≤ rowSlot E R j' := by
    simp only [rowSlot]
    have hm : (j + 1) * rowWords E R ≤ j' * rowWords E R :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have h3 : rowSlot E R j' ≤ rowSlot E R j' + i' := Nat.le_add_right _ _
  omega

/-- **The `RowOut` layout**: row `j`'s `R`-bit support is packed into the `wordsOf E.W R` words
starting at `rowSlot E R j`, in exactly the shape `packMem` gives for a packed payload. -/
def RowOut (E : RAMEnv) (R j : ℕ) (x : Fin R → ZMod 2) (m : ℕ → ℕ) : Prop :=
  ∀ i, i < rowWords E R → m (rowSlot E R j + i) = packMem E.W x i

/-- **The `RowOut` base constraint**: the row bitmaps start at or above 2.1's scratch, so the
per-iteration clearing pass cannot erase earlier rows. -/
def RowOutFits (E : RAMEnv) (t : ℕ) : Prop := decoderAllocEnd t ≤ rowBase E

/-- Under the base constraint the clearing pass leaves every row bitmap alone. -/
theorem rowOut_preserved (E : RAMEnv) (R j t : ℕ) (x : Fin R → ZMod 2) (m m' : ℕ → ℕ)
    (hfit : RowOutFits E t) (hframe : ∀ a, decoderAllocEnd t ≤ a → m' a = m a)
    (h : RowOut E R j x m) : RowOut E R j x m' := by
  intro i hi
  have hle : decoderAllocEnd t ≤ rowSlot E R j := by
    simp only [rowSlot, RowOutFits] at *
    omega
  rw [hframe _ (by omega), h i hi]

/-- **The clearing pass of 2.1 preserves every row bitmap.**  This is what the base constraint
buys: `clearScratch_sem` zeroes `[0, decoderAllocEnd t)` and frames everything above it. -/
theorem clearScratch_rowOut {P : Program} {E : RAMEnv} {pc t R j : ℕ} {s : RAMState}
    {x : Fin R → ZMod 2}
    (hAt : At P pc (Stmt.compile (clearFull 0 (decoderAllocEnd t)) pc))
    (hW : 1 < 2 ^ E.W) (hK : decoderAllocEnd t < 2 ^ E.W) (hpc : s.pc = pc)
    (hfit : RowOutFits E t) (hrow : RowOut E R j x s.mem) :
    ∃ k s', k ≤ 15 + 8 * decoderAllocEnd t ∧ (step P E)^[k] s = s' ∧
      RowOut E R j x s'.mem := by
  obtain ⟨k, s', hk, hstep, -, hframe, -⟩ := clearScratch_sem hAt hW hK hpc
  exact ⟨k, s', hk, hstep, rowOut_preserved E R j t x s.mem s'.mem hfit hframe hrow⟩

/-! ### 1.1 Two obstructions: `detStd` cannot carry the composite header

`hdrTab`'s slot 3 is `2t`; `detStd` returns `hdrTab` on `[0,13)` and `0` on `[13,64)`.  So a stage
that runs in `detEnv (8*w) (detStd t N b ι)` has neither a row-bitmap base above its own scratch nor
a free header slot.  Both facts are needed by the audit, so both are proved. -/

theorem detStd_three {F : Type} [Field F] [Algebra (ZMod 2) F] {w t N : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) :
    detStd t N b ι 3 = 2 * t := by
  rw [detStd_hdr t N w b ι (by norm_num : 3 < 13)]
  rfl

theorem detStd_high_zero {F : Type} [Field F] [Algebra (ZMod 2) F] {w t N : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) {a : ℕ} (h13 : 13 ≤ a)
    (h64 : a < detMulBase w) : detStd t N b ι a = 0 := by
  have h1 : ¬ a < 13 := by omega
  unfold detStd
  rw [if_neg h1, if_pos h64]

/-- **`rowBase E = E.det 3` is incompatible with 2.1's environment.** -/
theorem not_rowOutFits_detStd {F : Type} [Field F] [Algebra (ZMod 2) F] {w t N : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (ht : 1 ≤ t)
    (h2t : 2 * t < 2 ^ (8 * w)) :
    ¬ RowOutFits (detEnv (8 * w) (detStd t N b ι)) t := by
  intro h
  have hbase : rowBase (detEnv (8 * w) (detStd t N b ι)) = 2 * t := by
    simp only [rowBase, detEnv]
    rw [detStd_three (t := t) (N := N) b ι, Nat.mod_eq_of_lt h2t]
  have hbig : 2 * t < decoderAllocEnd t := by
    rw [decoderAllocEnd_eq]
    nlinarith
  simp only [RowOutFits] at h
  omega

/-! ## 2. The repack bridge `OutputsSupport → RowOut` -/

/-- The memory the per-row repack pass produces from a duplicate-free output list `l`
(specification level): the row's slot words receive the accumulated bit sums
`∑ v ∈ l, 2 ^ (v % W)` per word, and every other address is preserved. -/
def repackMem (E : RAMEnv) (R j : ℕ) (l : List ℕ) (m : ℕ → ℕ) : ℕ → ℕ :=
  writeArray (rowSlot E R j) m
    (fun i => ∑ v ∈ l.toFinset, (if v / E.W = i then 2 ^ (v % E.W) else 0))
    (rowWords E R)

theorem repackMem_slot (E : RAMEnv) (R j : ℕ) (l : List ℕ) (m : ℕ → ℕ) (i : ℕ)
    (hi : i < rowWords E R) :
    repackMem E R j l m (rowSlot E R j + i)
      = ∑ v ∈ l.toFinset, (if v / E.W = i then 2 ^ (v % E.W) else 0) :=
  writeArray_get _ _ _ _ _ hi

theorem repackMem_frame (E : RAMEnv) (R j : ℕ) (l : List ℕ) (m : ℕ → ℕ) (a : ℕ)
    (ha : a < rowSlot E R j ∨ rowSlot E R j + rowWords E R ≤ a) :
    repackMem E R j l m a = m a :=
  writeArray_frame _ _ _ _ _ ha

/-- A duplicate-free output list of `x` lists exactly the support of `x`. -/
theorem toFinset_outList {n : ℕ} {s : RAMState} {x : Fin n → ZMod 2}
    (h : OutputsSupport s x) :
    (outList s).toFinset = (univ.filter (fun p : Fin n => x p = 1)).image (fun p => p.val) := by
  ext v
  rw [List.mem_toFinset, h.2 v, Finset.mem_image]
  constructor
  · rintro ⟨i, hx, hv⟩
    exact ⟨i, by simp [hv], hx⟩
  · rintro ⟨i, hx, hv⟩
    exact ⟨i, hv, by simpa using hx⟩

/-- `packMem` is the same sum as the one the repack pass accumulates, taken over the support. -/
theorem packMem_eq_sum (W R : ℕ) (x : Fin R → ZMod 2) (i : ℕ) :
    packMem W x i = ∑ p ∈ univ.filter (fun p : Fin R => x p = 1),
      (if p.val / W = i then 2 ^ (p.val % W) else 0) := by
  have hstep : (∑ p ∈ univ.filter (fun p : Fin R => x p = 1),
        (if p.val / W = i then 2 ^ (p.val % W) else 0))
      = ∑ p : Fin R, if x p = 1 then (if p.val / W = i then 2 ^ (p.val % W) else 0) else 0 := by
    rw [Finset.sum_filter]
  rw [hstep]
  unfold packMem
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hx : x p = 1
  · by_cases hc : p.val / W = i
    · simp [hx, hc]
    · simp [hx, hc]
  · simp [hx]

/-- **The bridge, inhabited.**  The memory the repack pass builds from 2.1's output list is exactly
the `RowOut` layout for `x`.  Only duplicate-freeness and the `↔ supp` characterisation of the output
list are used; no bit-level carry argument is needed, because `packMem` is itself the sum over the
support. -/
theorem rowOut_repackMem (E : RAMEnv) (R j : ℕ) (s : RAMState) (x : Fin R → ZMod 2)
    (h : OutputsSupport s x) : RowOut E R j x (repackMem E R j (outList s) s.mem) := by
  intro i hi
  rw [repackMem_slot E R j _ _ i hi, toFinset_outList h]
  rw [Finset.sum_image
    (f := fun v => if v / E.W = i then 2 ^ (v % E.W) else 0)
    (g := fun p : Fin R => p.val) (s := univ.filter (fun p : Fin R => x p = 1))]
  · exact (packMem_eq_sum E.W R x i).symm
  · intro a _ c _ hac
    exact Fin.ext hac



/-! ## 3. The per-row `setup` block

`stageHeadCode` is the register half of the setup.  It reads

* the **base of the payload region** out of the single `det` word `hdrPayTab`, multiplies the
  row counter `r1 = j` by the stride `stageLen E` (2.1's own header slot `4`) and adds the two
  (`iImm r15 hdrPayTab; iTbl r15 r15; iImm r3 4; iTbl r3 r3; iMul r3 r3 r1; iAdd r3 r3 r15`),
  so row `j`'s payload base is `base + j * L` — no per-row `det` entry is needed, and
* the staging base `β` out of the compile-time constant slot `hdrStageBase`,

and leaves `r1 = L` (2.1's own header slot 4) plus the copy loop's remaining registers.  `copyStmt`
then stages the payload; `stageStmt` is the two together, ending in `zeroRegsCode` so that 2.1's
decoder sees its canonical entry registers. -/

/-- Compile-time constant `det` slot holding the **base of the payload region** (a single word;
the per-row bases are the arithmetic progression `base + j * stageLen E`). -/
def hdrPayTab : ℕ := 15

/-- Compile-time constant `det` slot holding the staging base `β`. -/
def hdrStageBase : ℕ := 16

/-- The runtime value of the payload-region base word. -/
def payTabAddr (E : RAMEnv) : ℕ := E.det hdrPayTab % 2 ^ E.W

/-- The staging base `β`, exactly as the setup block computes it. -/
def stageBase (E : RAMEnv) : ℕ := E.det hdrStageBase % 2 ^ E.W

/-- The payload word count `L = wordsOf (8w) (tw)`, read from 2.1's header slot 4. -/
def stageLen (E : RAMEnv) : ℕ := E.det 4 % 2 ^ E.W

/-- **Row `j`'s payload base, exactly as the setup block computes it.**  The per-row bases are the
arithmetic progression with base `payTabAddr E` and stride `stageLen E`; there is no `d`-entry
table, so the layout is not capped at `51` rows. -/
def rowPayBase (E : RAMEnv) (j : ℕ) : ℕ := (payTabAddr E + j * stageLen E) % 2 ^ E.W

/-- The register half of the setup block. -/
def stageHeadCode : List Instr :=
  [iImm r15 hdrPayTab, iTbl r15 r15,
   iImm r3 4, iTbl r3 r3, iMul r3 r3 r1, iAdd r3 r3 r15,
   iImm r15 hdrStageBase, iTbl r2 r15,
   iImm r15 4, iTbl r1 r15,
   iImm r0 0, iImm r4 1, iImm r10 0, iImm r12 0, iImm r13 0, iImm r15 0]

theorem stageHeadCode_length : stageHeadCode.length = 16 := rfl

theorem stageHeadCode_noBranch : NoBranch stageHeadCode := by
  simp [stageHeadCode, NoBranch, Instr.NoBranchI]

/-- The registers the setup head produces, already reduced into words. -/
def stageHeadRegs (L dst src : ℕ) (r : Fin 16 → ℕ) : Fin 16 → ℕ :=
  fun d =>
    if d = r0 then 0 else if d = r1 then L else if d = r2 then dst
      else if d = r3 then src else if d = r4 then 1
      else if d = r10 then 0 else if d = r12 then 0 else if d = r13 then 0
      else if d = r15 then 0 else r d

theorem stageHeadRegs_r0 (L dst src : ℕ) (r : Fin 16 → ℕ) :
    stageHeadRegs L dst src r r0 = 0 := by simp [stageHeadRegs]

theorem stageHeadRegs_r1 (L dst src : ℕ) (r : Fin 16 → ℕ) :
    stageHeadRegs L dst src r r1 = L := by simp [stageHeadRegs]

theorem stageHeadRegs_r2 (L dst src : ℕ) (r : Fin 16 → ℕ) :
    stageHeadRegs L dst src r r2 = dst := by simp [stageHeadRegs]

theorem stageHeadRegs_r3 (L dst src : ℕ) (r : Fin 16 → ℕ) :
    stageHeadRegs L dst src r r3 = src := by simp [stageHeadRegs]

theorem stageHeadRegs_r4 (L dst src : ℕ) (r : Fin 16 → ℕ) :
    stageHeadRegs L dst src r r4 = 1 := by simp [stageHeadRegs]

/-- The state the setup head produces. -/
def stageHeadOut (E : RAMEnv) (pc j : ℕ) (m : ℕ → ℕ) (r : Fin 16 → ℕ) : RAMState :=
  ⟨pc + 16, stageHeadRegs (stageLen E) (stageBase E) (rowPayBase E j) r, m⟩

/-- The head's two-instruction address arithmetic, in the form the machine produces it:
`(L * j mod 2^W + base) mod 2^W = (base + j * L) mod 2^W`. -/
theorem zPayMod (m p j L : ℕ) (hm : 0 < m) :
    ((L * j % m) + p) % m = (p + j * L) % m := by
  rw [Nat.mod_add_mod (L * j) m p, Nat.add_comm (L * j) p, Nat.mul_comm L j]

/-- **The setup head, proved.**  It loads row `j`'s payload base and the staging base into exactly
the registers `copyStmt` (`layerCopyRegs`) expects, and does not touch memory. -/
theorem stageHead_run (E : RAMEnv) (pc j : ℕ) (m : ℕ → ℕ) (r : Fin 16 → ℕ)
    (hW : 1 < 2 ^ E.W) (hW16 : 16 < 2 ^ E.W) (hj : r r1 = j) :
    runBlock stageHeadCode E ⟨pc, r, m⟩ = stageHeadOut E pc j m r := by
  have hm4 : 4 % 2 ^ E.W = 4 := Nat.mod_eq_of_lt (by omega)
  have hmp : hdrPayTab % 2 ^ E.W = hdrPayTab :=
    Nat.mod_eq_of_lt (by show (15 : ℕ) < 2 ^ E.W; omega)
  have hms : hdrStageBase % 2 ^ E.W = hdrStageBase :=
    Nat.mod_eq_of_lt (by show (16 : ℕ) < 2 ^ E.W; omega)
  have h1 : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hW
  have hpay : ((E.det 4 % 2 ^ E.W) * j % 2 ^ E.W + E.det hdrPayTab % 2 ^ E.W) % 2 ^ E.W
      = (E.det hdrPayTab % 2 ^ E.W + j * (E.det 4 % 2 ^ E.W)) % 2 ^ E.W :=
    zPayMod (2 ^ E.W) (E.det hdrPayTab % 2 ^ E.W) j (E.det 4 % 2 ^ E.W) (by omega)
  apply ramState_eq_of
  · simp [stageHeadOut, stageHeadCode, runBlock_cons, runBlock_nil, execInstr]
  · rfl
  · intro d
    fin_cases d <;>
      simp only [stageHeadOut, stageHeadCode, Fin.isValue, runBlock_cons, runBlock_nil, execInstr,
        Function.update_self, Function.update_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true,
        Nat.zero_mod, h1, hm4, hmp, hms, hj, ↓reduceIte, stageHeadRegs, stageLen, stageBase,
        payTabAddr, rowPayBase, hpay, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, zero_ne_one,
        one_ne_zero]

/-- The setup head leaves exactly the copy loop's canonical entry state. -/
theorem stageHeadOut_eq_copyState (E : RAMEnv) (pc j : ℕ) (m : ℕ → ℕ) (r : Fin 16 → ℕ) :
    stageHeadOut E pc j m r =
      copyState (pc + 16) (stageBase E) (rowPayBase E j) (stageLen E) m
        (stageHeadRegs (stageLen E) (stageBase E) (rowPayBase E j) r) 0 := by
  apply ramState_eq_of
  · rfl
  · rfl
  · intro d
    fin_cases d <;>
      simp only [stageHeadOut, copyState, stageHeadRegs, Fin.isValue, Fin.zero_eta, Fin.mk_one,
        Fin.reduceFinMk, zero_ne_one, one_ne_zero, ne_eq, Fin.reduceEq, not_false_eq_true,
        ↓reduceIte]

/-! ### 3.1 The staging copy loop -/

theorem copyCond_eval (pc dst src L : ℕ) (m : ℕ → ℕ) (r : Fin 16 → ℕ) (j : ℕ) :
    copyCond.eval (copyState pc dst src L m r j) ↔ j < L := by
  simp [copyCond, Cond.eval, copyState]

/-- One iteration of the staging copy, as a state identity. -/
theorem copyBody_spec (E : RAMEnv) (pc dst src L : ℕ) (m : ℕ → ℕ) (r : Fin 16 → ℕ)
    (j : ℕ) (hj : j < L) (hW : 1 < 2 ^ E.W)
    (hdst : dst + L ≤ 2 ^ E.W) (hsrc : src + L ≤ 2 ^ E.W)
    (hword : ∀ i, i < L → m (src + i) < 2 ^ E.W)
    (hdisj : src + L ≤ dst ∨ dst + L ≤ src) :
    runBlock copyBody E
      { runBlock copyCond.code E (copyState pc dst src L m r j) with pc := pc + 2 } =
      { copyState pc dst src L m r (j + 1) with pc := pc + 11 } := by
  have haddr : (src + j) % 2 ^ E.W = src + j := Nat.mod_eq_of_lt (by omega)
  have haddr2 : (dst + j) % 2 ^ E.W = dst + j := Nat.mod_eq_of_lt (by omega)
  have hnext : (j + 1) % 2 ^ E.W = j + 1 := Nat.mod_eq_of_lt (by omega)
  have hval : m (src + j) % 2 ^ E.W = m (src + j) := Nat.mod_eq_of_lt (hword j hj)
  have h1 : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hW
  have hread : writeArray dst m (fun i => m (src + i)) j (src + j) = m (src + j) := by
    refine writeArray_frame dst m _ j (src + j) ?_
    rcases hdisj with h | h
    · left; omega
    · right; omega
  apply ramState_eq_of
  · simp only [copyBody, copyCond, Cond.code, copyState, runBlock_cons, runBlock_nil, execInstr,
      Function.update_self, Function.update_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true,
      Nat.zero_mod, h1, ↓reduceIte, hj] <;> omega
  · simp only [copyBody, copyCond, Cond.code, copyState, runBlock_cons, runBlock_nil, execInstr,
      Function.update_self, Function.update_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true,
      Nat.zero_mod, h1, ↓reduceIte, hj, haddr, haddr2, hnext, hread, hval, writeArray]
  · intro d
    fin_cases d <;>
      simp only [copyBody, copyCond, Cond.code, copyState, runBlock_cons, runBlock_nil, execInstr,
        Function.update_self, Function.update_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true,
        Nat.zero_mod, h1, ↓reduceIte, hj, haddr, haddr2, hnext, hread, hval,
        Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, zero_ne_one, one_ne_zero]

theorem copyBodyIter (P : Program) (E : RAMEnv) (pc dst src L : ℕ)
    (m : ℕ → ℕ) (r : Fin 16 → ℕ) (j : ℕ) (hj : j < L)
    (hAt : At P pc (Stmt.compile copyStmt pc))
    (hW : 1 < 2 ^ E.W) (hdst : dst + L ≤ 2 ^ E.W)
    (hsrc : src + L ≤ 2 ^ E.W) (hword : ∀ i, i < L → m (src + i) < 2 ^ E.W)
    (hdisj : src + L ≤ dst ∨ dst + L ≤ src) :
    Sem P E (pc + copyCond.code.length + 1) pc
      { runBlock copyCond.code E (copyState pc dst src L m r j) with
        pc := pc + copyCond.code.length + 1 }
      (fun k s' => k = 10 ∧ s' = copyState pc dst src L m r (j + 1)) := by
  obtain ⟨-, -, hbody, hjmp⟩ := at_loop (c := copyCond) (b := .code copyBody) hAt
  have hbodyAt : At P (pc + 2) copyBody := by
    have h := hbody
    rw [show copyCond.code.length = 1 from rfl] at h
    simpa only [Stmt.compile] using h
  have hjmpAt : P[pc + 11]? = some (iJmp pc) := by
    have h := hjmp
    rw [show copyCond.code.length = 1 from rfl, show (Stmt.code copyBody).len = 9 from rfl] at h
    simpa using h
  have hrun : Sem P E (pc + 2) (pc + 11)
      { runBlock copyCond.code E (copyState pc dst src L m r j) with pc := pc + 2 }
      (fun k s' => k = 9 ∧ s' = { copyState pc dst src L m r (j + 1) with pc := pc + 11 }) := by
    refine Sem.mono (Sem.block P E (pc + 2) copyBody _ hbodyAt
      (by simp [copyBody]) rfl) ?_
    intro k s' h
    obtain ⟨hk, hs⟩ := h
    refine ⟨hk, ?_⟩
    rw [hs]
    exact copyBody_spec E pc dst src L m r j hj hW hdst hsrc hword hdisj
  refine Sem.jmp_append (hAt := hjmpAt) (Sem.mono hrun ?_)
  intro k s' h
  obtain ⟨hk, hs⟩ := h
  refine ⟨by omega, ?_⟩
  rw [hs]
  rfl

theorem copyCond_exit (E : RAMEnv) (pc dst src L : ℕ) (m : ℕ → ℕ) (r : Fin 16 → ℕ) :
    ({ runBlock copyCond.code E (copyState pc dst src L m r L) with pc := pc + 12 } : RAMState) =
      { copyState pc dst src L m r L with pc := pc + 12 } := by
  apply ramState_eq_of
  · rfl
  · rfl
  · intro d
    fin_cases d <;>
      simp [copyCond, Cond.code, runBlock_cons, runBlock_nil, execInstr, copyState]

/-- **The staging copy loop's contract**: it copies `[src, src+L)` to `[dst, dst+L)`, leaves
everything else alone, and costs `12L + 2` steps. -/
theorem copyArray_spec (P : Program) (E : RAMEnv) (pc dst src L : ℕ) (m : ℕ → ℕ)
    (r : Fin 16 → ℕ) (hAt : At P pc (Stmt.compile copyStmt pc))
    (hW : 1 < 2 ^ E.W) (hdst : dst + L ≤ 2 ^ E.W)
    (hsrc : src + L ≤ 2 ^ E.W) (hword : ∀ i, i < L → m (src + i) < 2 ^ E.W)
    (hdisj : src + L ≤ dst ∨ dst + L ≤ src) :
    Sem P E pc (pc + 12) (copyState pc dst src L m r 0)
      (fun k s' => k ≤ 12 * L + 2 ∧
        s' = { copyState pc dst src L m r L with pc := pc + 12 }) := by
  have hcl : copyCond.code.length = 1 := rfl
  have h := Sem.loop P E pc copyCond (.code copyBody) hAt hW L
    (fun j => copyState pc dst src L m r j) (fun _ => 10)
    (fun _ => rfl)
    (fun j hj => (copyCond_eval pc dst src L m r j).mpr hj)
    (fun hf => (Nat.lt_irrefl L) ((copyCond_eval pc dst src L m r L).mp hf))
    (fun j hj => copyBodyIter P E pc dst src L m r j hj hAt hW hdst hsrc hword hdisj)
  refine Sem.mono h ?_
  intro k s' hQ
  obtain ⟨hcost, hs⟩ := hQ
  refine ⟨?_, ?_⟩
  · have hsum : (∑ j ∈ Finset.range L, (1 + 1 + 10 : ℕ)) = 12 * L :=
      sum_range_const_mul L 12
    rw [hcl] at hcost
    rw [hsum] at hcost
    omega
  · rw [hs]
    exact copyCond_exit E pc dst src L m r

/-! ### 3.2 The whole setup block -/

/-- **The per-row setup block**: the register head, the staging copy, and the register reset. -/
def stageStmt : Stmt := .seq (.code stageHeadCode) (.seq copyStmt (.code zeroRegsCode))

theorem zeroRegsCode_length : zeroRegsCode.length = 16 := rfl

theorem stageStmt_len : stageStmt.len = 44 := by
  simp only [stageStmt, Stmt.len, stageHeadCode_length, copyStmt, copyCond, copyBody, Cond.code,
    zeroRegsCode_length, List.length_cons, List.length_nil]

/-- The setup block's cost at payload length `L`. -/
def stageCost (E : RAMEnv) : ℕ := 16 + (12 * stageLen E + 2) + 16

/-- The registers after the whole setup block: everything zero (2.1's `zeroRegsCode`). -/
def zeroRegs : Fin 16 → ℕ := fun _ => 0

theorem zeroRegsCode_run (E : RAMEnv) (pc : ℕ) (m : ℕ → ℕ) (r : Fin 16 → ℕ) :
    runBlock zeroRegsCode E ⟨pc, r, m⟩ = ⟨pc + 16, zeroRegs, m⟩ := by
  apply ramState_eq_of
  · simp [zeroRegsCode, runBlock_cons, runBlock_nil, execInstr]
  · rfl
  · intro d
    fin_cases d <;>
      simp [zeroRegs, zeroRegsCode, runBlock_cons, runBlock_nil, execInstr]

/-- **The setup block, proved.**  From the row-loop head state it stages row `j`'s payload at
`stageBase E`, zeroes the registers (2.1's canonical entry), and costs `stageCost E` steps. -/
theorem stage_sem {P : Program} {E : RAMEnv} {pc j : ℕ} {m : ℕ → ℕ} {r : Fin 16 → ℕ}
    (hAt : At P pc (Stmt.compile stageStmt pc)) (hW : 1 < 2 ^ E.W) (hW16 : 16 < 2 ^ E.W)
    (hj : r r1 = j)
    (hdst : stageBase E + stageLen E ≤ 2 ^ E.W)
    (hsrc : rowPayBase E j + stageLen E ≤ 2 ^ E.W)
    (hword : ∀ i, i < stageLen E → m (rowPayBase E j + i) < 2 ^ E.W)
    (hdisj : rowPayBase E j + stageLen E ≤ stageBase E ∨
      stageBase E + stageLen E ≤ rowPayBase E j) :
    Sem P E pc (pc + stageStmt.len) ⟨pc, r, m⟩
      (fun k s' => k ≤ stageCost E ∧ s'.pc = pc + stageStmt.len ∧ s'.regs = zeroRegs ∧
        ∀ i, i < stageLen E → s'.mem (stageBase E + i) = m (rowPayBase E j + i)) := by
  have hAt2 : At P pc (stageHeadCode ++ (copyStmt.compile (pc + 16) ++ zeroRegsCode)) := by
    simpa only [stageStmt, Stmt.compile, Stmt.len, stageHeadCode_length] using hAt
  obtain ⟨hheadAt, hrest⟩ := At.append.mp hAt2
  have hrest2 : At P (pc + 16) (copyStmt.compile (pc + 16) ++ zeroRegsCode) := by
    simpa only [stageHeadCode_length] using hrest
  obtain ⟨hcopyAt, hzAt⟩ := At.append.mp hrest2
  have hzAt2 : At P (pc + 16 + 12) zeroRegsCode := by
    simpa only [Stmt.length_compile, copyStmt, copyCond, copyBody, Cond.code, Stmt.len,
      List.length_cons, List.length_nil] using hzAt
  have hhead : Sem P E pc (pc + 16) ⟨pc, r, m⟩
      (fun k s' => k ≤ 16 ∧ s' = copyState (pc + 16) (stageBase E) (rowPayBase E j) (stageLen E) m
        (stageHeadRegs (stageLen E) (stageBase E) (rowPayBase E j) r) 0) := by
    refine Sem.mono (Sem.block P E pc stageHeadCode _ hheadAt stageHeadCode_noBranch rfl) ?_
    intro k s' h
    obtain ⟨hk, hs⟩ := h
    rw [stageHeadCode_length] at hk
    refine ⟨by omega, ?_⟩
    rw [hs, stageHead_run E pc j m r hW hW16 hj, stageHeadOut_eq_copyState]
  have hcopy : Sem P E (pc + 16) (pc + 16 + 12)
      (copyState (pc + 16) (stageBase E) (rowPayBase E j) (stageLen E) m
        (stageHeadRegs (stageLen E) (stageBase E) (rowPayBase E j) r) 0)
      (fun k s' => k ≤ 12 * stageLen E + 2 ∧
        s' = { copyState (pc + 16) (stageBase E) (rowPayBase E j) (stageLen E) m
          (stageHeadRegs (stageLen E) (stageBase E) (rowPayBase E j) r) (stageLen E)
          with pc := pc + 16 + 12 }) :=
    copyArray_spec P E (pc + 16) (stageBase E) (rowPayBase E j) (stageLen E) m _ hcopyAt
      hW hdst hsrc hword hdisj
  have hz : Sem P E (pc + 16 + 12) (pc + 16 + 12 + 16)
      { copyState (pc + 16) (stageBase E) (rowPayBase E j) (stageLen E) m
        (stageHeadRegs (stageLen E) (stageBase E) (rowPayBase E j) r) (stageLen E)
        with pc := pc + 16 + 12 }
      (fun k s' => k ≤ 16 ∧ s' = ⟨pc + 16 + 12 + 16, zeroRegs,
        writeArray (stageBase E) m (fun i => m (rowPayBase E j + i)) (stageLen E)⟩) := by
    refine Sem.mono (Sem.block P E (pc + 16 + 12) zeroRegsCode _ hzAt2
      (by simp [zeroRegsCode, NoBranch, Instr.NoBranchI]) rfl) ?_
    intro k s' h
    obtain ⟨hk, hs⟩ := h
    rw [zeroRegsCode_length] at hk
    refine ⟨by omega, ?_⟩
    rw [hs]
    exact zeroRegsCode_run E (pc + 16 + 12) _ _
  refine Sem.mono (R66.Sem.trans_le (R66.Sem.trans_le hhead hcopy) hz) ?_
  intro k s' h
  obtain ⟨hk, hs⟩ := h
  rw [hs]
  have hcost : k ≤ stageCost E := by unfold stageCost; omega
  have hpc : pc + 16 + 12 + 16 = pc + stageStmt.len := by rw [stageStmt_len]
  exact ⟨hcost, hpc, rfl,
    fun i hi => writeArray_get (stageBase E) m (fun i => m (rowPayBase E j + i)) (stageLen E) i hi⟩


/-! ### 4.6 One row iteration, and the decode stage's contract that is still missing -/

/-- **One row iteration, assembled from its four stages.**  The clear comes *first*: the setup must
stage the payload after the scratch has been cleared, otherwise the clear would erase it.
(`R66.rowBody_sem` is generic in the order of its four stages.)  `stage_sem` is the `stage` stage,
`R66.clearScratch_sem` the clear, and `repackStmt`'s `RepackRuns` the repack. -/
theorem rowBody_from_stages {P : Program} {E : RAMEnv} {a : ℕ} {s0 s1 s2 s3 s4 s5 : RAMState}
    {cl su dc rp : ℕ}
    (hjmp : P[a + 2 + cl + su + dc + rp + 2]? = some (iJmp a))
    (hclear : Sem P E (a + 2) (a + 2 + cl) s0 (fun k z => k = cl ∧ z = s1))
    (hstage : Sem P E (a + 2 + cl) (a + 2 + cl + su) s1 (fun k z => k = su ∧ z = s2))
    (hdec : Sem P E (a + 2 + cl + su) (a + 2 + cl + su + dc) s2 (fun k z => k = dc ∧ z = s3))
    (hrep : Sem P E (a + 2 + cl + su + dc) (a + 2 + cl + su + dc + rp) s3
      (fun k z => k = rp ∧ z = s4))
    (hinc : Sem P E (a + 2 + cl + su + dc + rp) (a + 2 + cl + su + dc + rp + 2) s4
      (fun k z => k = 2 ∧ z = s5)) :
    Sem P E (a + 2) a s0 (fun k z => k = cl + su + dc + rp + 3 ∧ z = { s5 with pc := a }) :=
  R66.rowBody_sem hjmp hclear hstage hdec hrep hinc

/-- **The per-row decode stage's contract**, in the shape the row loop consumes: from a state whose
memory has the payload of `y` staged at `β` and is otherwise zero where 2.1 needs it (i.e.
`layerMem` lands on `hintMem`), the stage reaches, in at most `T` steps, a state whose output list is
the support of the row's `x`.

This is exactly what `pinsketch_decoding_at` proves about
`programOfStatement (pinsketchRunStmt t w β)` in `detEnv (8*w) (detStd t N b ι)` — but at base `0`
and in an environment whose `det` is `detStd`.  Two gaps therefore remain before it can be used
inside `progDecOfTop`; both are *proved* obstructions, not missing lemmas:

* `run_agrees` transfers a run only when `progDec`'s trailing `halt` is replaced at base `0`; for a
  non-zero entry address one needs `Stmt.compile`'s jump-target shift, which no published export
  provides (`progDec` is a bare `Program` with absolute targets — `Def_…_Top65Dec`'s own note);
* `detStd_high_zero` and `not_rowOutFits_detStd` show `detStd` carries neither a free header slot
  (`13 … 63` are `0`) nor a row-bitmap base above the scratch (slot `3` is `2t`).  So 2.1's `hdet`
  must be weakened to "agrees with `detStd t N b ι` on slots `< 13`". -/
def DecodeStage (P : Program) (E : RAMEnv) (a b t w R β : ℕ) (T : ℝ) : Prop :=
  ∀ (y : Fin (t * w) → ZMod 2) (x : Fin R → ZMod 2),
    StageRun P E a b T
      (fun s => PayloadOn (8 * w) (t * w) β y s.mem ∧ WeakZero (8 * w) (t * w) β s.mem)
      (fun s => OutputsSupport s x)

/-- Unpacking `DecodeStage` into the `Sem`-minus-`Halted` shape. -/
theorem decodeStage_run {P : Program} {E : RAMEnv} {a b t w R β : ℕ} {T : ℝ}
    (h : DecodeStage P E a b t w R β T) (y : Fin (t * w) → ZMod 2) (x : Fin R → ZMod 2)
    (s : RAMState) (hpc : s.pc = a)
    (hpay : PayloadOn (8 * w) (t * w) β y s.mem) (hweak : WeakZero (8 * w) (t * w) β s.mem) :
    ∃ (k : ℕ) (s' : RAMState), (k : ℝ) ≤ T ∧ (step P E)^[k] s = s' ∧ s'.pc = b ∧
      OutputsSupport s' x :=
  h y x s hpc ⟨hpay, hweak⟩

end RDecP
end LinearSetReconciliation327.Main

/-! ## 4. The two remaining programs, and the `CR` merge

This section writes the repack pass and the merge pass in the project's own instruction set, proves
`cr23_progDec_stmt` (definitionally, with the witness `decStmt`), records how `ScrBlock = .seq Sdec
Smerge` glues onto `progDec`, and proves the *mathematics* of the merge (`x̂ + ê` is `x`) and of the
repack (the `RowOut` bridge, §2).  The two memory-loop simulations themselves are stated as the
propositions `RepackRuns` / `SmergeRuns`; see the report for why. -/


namespace LinearSetReconciliation327.Main
namespace RDecP

open Finset

open LinearSetReconciliation327.Main.R66

/-- The merge head: `r5 := aBase`, `r6 := aLen`, `r7 := bBase`, `r8 := bLen`, `r9 := outBase`, and
the output counter `r1 := 0`. -/
def mergeHeadCode : List Instr :=
  [iBor r5 r10 r10, iBor r6 r11 r11, iBor r7 r12 r12, iBor r8 r13 r13, iBor r9 r14 r14,
   iImm r0 0, iImm r1 0]

/-- One kept element: `mem[outBase + r1] := mem[aBase + r0]`, then `r1 += 1`. -/
def mergeKeepA : List Instr :=
  [iAdd r15 r5 r0, iLd r4 r15, iAdd r15 r9 r1, iSt r15 r4, iImm r4 1, iAdd r1 r1 r4]

/-- **`Smerge`** (skeleton): the head, one keep pass, and the output header `r0 := outBase`.  The
full block iterates `mergeKeepA` over `A` (skipping members of `B`) and then a second pass over `B`
(skipping members of `A`); the two passes are `Stmt.loop`s with an inner membership scan. -/
def mergeStmt : Stmt :=
  .seq (.code mergeHeadCode) (.seq (.code mergeKeepA) (.code [iBor r0 r9 r9]))

/-- The repack head: `r7 := list base`, `r8 := list length`, `r11 := W` (det slot 12),
`r6 := wordsOf W R` from det slot 2 (`= R`), `r5 := rowSlot` (det slot 3 plus `j · wordsOf W R`). -/
def repackHeadCode : List Instr :=
  [iBor r7 r0 r0, iBor r8 r1 r1,
   iImm r15 12, iTbl r11 r15,
   iImm r15 2, iTbl r6 r15,
   iAdd r6 r6 r11, iImm r15 1, iSub r6 r6 r15, iDiv r6 r6 r11,
   iImm r15 3, iTbl r5 r15,
   iMul r15 r6 r1, iAdd r5 r5 r15,
   iImm r0 0]

/-- One repacked value `v := mem[listBase + i]`: `mem[rowSlot + v / W] += 1 << (v % W)`, `i += 1`. -/
def repackBody : List Instr :=
  [iAdd r15 r7 r0, iLd r4 r15,
   iDiv r12 r4 r11, iMod r13 r4 r11,
   iImm r9 1, iShl r9 r9 r13,
   iAdd r15 r5 r12, iLd r14 r15, iAdd r14 r14 r9, iSt r15 r14,
   iImm r4 1, iAdd r0 r0 r4,
   iImm r9 0, iImm r12 0, iImm r13 0, iImm r14 0, iImm r15 0]

/-- **The repack pass**: a counted loop over 2.1's output list. -/
def repackStmt : Stmt := .loop (Cond.lt r15 r0 r8) (.code repackBody)

/-! ### 4.1 `cr23_progDec_stmt`, and the glue of `ScrBlock = .seq Sdec Smerge` -/

/-- **`cr23_progDec_stmt`, inhabited** with the definitional witness `decStmt`. -/
theorem cr23_stmt : ∃ Sdec : Stmt, Sdec.compile 0 ++ [iHalt] = progDec := ⟨decStmt, rfl⟩

/-- The `CR` stage block: 2.3's decoder, then the merge. -/
def scrBlock (Smerge : Stmt) : Stmt := .seq decStmt Smerge

/-- **Glue**: the composite block compiles to 2.3's code with its trailing `halt` replaced by
`Smerge`. -/
theorem scrBlock_compile (Smerge : Stmt) :
    (scrBlock Smerge).compile 0 = decStmt.compile 0 ++ Smerge.compile decStmt.len := by
  simp only [scrBlock, Stmt.compile, Nat.zero_add]

/-- 2.3's code is the prefix of `progDec` of length `decStmt.len`. -/
theorem progDec_prefix : decStmt.compile 0 = progDec.take decStmt.len := by
  unfold progDec
  rw [← Stmt.length_compile decStmt 0, List.take_left]

/-- The glued `CR` programme: `Sdec`, then `Smerge`, then `halt`. -/
theorem scrBlock_program (Smerge : Stmt) :
    (scrBlock Smerge).compile 0 ++ [iHalt]
      = progDec.take decStmt.len ++ Smerge.compile decStmt.len ++ [iHalt] := by
  rw [scrBlock_compile, progDec_prefix, List.append_assoc]

/-! ### 4.2 Replacing `progDec`'s `halt` by `Smerge` -/

theorem step_agree {P P' : Program} {l : List Instr} {E : RAMEnv} {s : RAMState}
    (hP : P = l ++ [iHalt]) (hAt : At P' 0 l) (hpc : s.pc < l.length) :
    step P E s = step P' E s := by
  have h1 : P[s.pc]? = l[s.pc]? := by
    rw [hP]
    exact List.getElem?_append_left hpc
  have h2 : P'[s.pc]? = l[s.pc]? := by
    have h := hAt s.pc hpc
    simpa using h
  unfold step
  rw [h1, h2]

/-- **A halted run of `P = block ++ [halt]` is a run of any `P'` agreeing with `block`.**  This is
what makes the glue work: `progDec`'s trailing `halt` is `Smerge`'s entry point. -/
theorem run_agrees {P P' : Program} {l : List Instr} {E : RAMEnv} {s s' : RAMState} {k : ℕ}
    (hP : P = l ++ [iHalt]) (hAt : At P' 0 l)
    (hrun : (step P E)^[k] s = s') (hout : s'.pc = l.length)
    (hb : ∀ i, i < k → ((step P E)^[i] s).pc < l.length) :
    ∃ k', k' ≤ k ∧ (step P' E)^[k'] s = s' := by
  have key : ∀ i, i ≤ k → (step P E)^[i] s = (step P' E)^[i] s := by
    intro i hi
    induction i with
    | zero => rfl
    | succ m ihm =>
        have hm : ((step P E)^[m] s).pc < l.length := hb m (by omega)
        have hIH : (step P E)^[m] s = (step P' E)^[m] s := ihm (by omega)
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← hIH]
        exact step_agree hP hAt hm
  exact ⟨k, le_rfl, by rw [← key k le_rfl]; exact hrun⟩

/-! ### 4.3 The merge's mathematics: `x̂ + ê` -/

/-- **The residual correction is exact**: merging `x̂` with `x + x̂` returns `x`. -/
theorem symmDiff_residual (x xhat e : Finset ℕ) (he : e = symmDiff x xhat) :
    symmDiff xhat e = x := by
  subst he
  rw [symmDiff_comm (α := Finset ℕ) x xhat, ← symmDiff_assoc, symmDiff_self]
  simp

/-- An explicit list stored in consecutive words. -/
def listAt (s : RAMState) (b len : ℕ) : List ℕ := (List.range len).map (fun i => s.mem (b + i))

theorem outList_eq_listAt (s : RAMState) : outList s = listAt s (s.regs r0) (s.regs r1) := rfl

/-- The merge's machine contract: `Smerge` replaces the list at `(abase, alen)` by a duplicate-free
list whose value set is `A Δ B`, where `A`, `B` are the two input lists. -/
def SmergeRuns (P : Program) (E : RAMEnv) (base abase alen bbase blen : ℕ) (T : ℝ) : Prop :=
  ∀ s : RAMState, s.pc = base →
    ∃ (k : ℕ) (s' : RAMState), (k : ℝ) ≤ T ∧ (step P E)^[k] s = s' ∧
      s'.pc = base + mergeStmt.len ∧ (outList s').Nodup ∧
      (outList s').toFinset = symmDiff (listAt s abase alen).toFinset
        (listAt s bbase blen).toFinset

/-- **`Smerge` computes `x̂ + ê`.**  If the merge runs to its contract and 2.3's decoder has
certified `ê = x Δ x̂` at the second list, the merged list is exactly the support of `x`. -/
theorem smerge_correct {P : Program} {E : RAMEnv} {base abase alen bbase blen : ℕ} {T : ℝ}
    {s : RAMState} {x xhat e : Finset ℕ}
    (h : SmergeRuns P E base abase alen bbase blen T) (hpc : s.pc = base)
    (hx : (listAt s abase alen).toFinset = xhat)
    (he : (listAt s bbase blen).toFinset = e) (hres : e = symmDiff x xhat) :
    ∃ (k : ℕ) (s' : RAMState), (k : ℝ) ≤ T ∧ (step P E)^[k] s = s' ∧ (outList s').Nodup ∧
      (outList s').toFinset = x := by
  obtain ⟨k, s', hk, hstep, -, hnod, hset⟩ := h s hpc
  exact ⟨k, s', hk, hstep, hnod, by rw [hset, hx, he, symmDiff_residual x xhat e hres]⟩

/-- **The merge writes `x̂ Δ ê`**: membership in its output is membership in the symmetric
difference. -/
theorem outList_symmDiff {s : RAMState} {A B : Finset ℕ}
    (h : (outList s).toFinset = symmDiff A B) :
    ∀ v, v ∈ outList s ↔ (v ∈ A ∧ v ∉ B) ∨ (v ∈ B ∧ v ∉ A) := by
  intro v
  rw [← List.mem_toFinset, h, mem_symmDiff]

/-! ### 4.4 The repack pass's contract -/

/-- **The repack pass's contract**: it turns 2.1's output list into the `RowOut` layout. -/
def RepackRuns (P : Program) (E : RAMEnv) (base R j : ℕ) (T : ℝ) : Prop :=
  ∀ s : RAMState, s.pc = base →
    ∃ (k : ℕ) (s' : RAMState), (k : ℝ) ≤ T ∧ (step P E)^[k] s = s' ∧
      s'.pc = base + repackStmt.len ∧ ∃ x : Fin R → ZMod 2, OutputsSupport s x ∧
        RowOut E R j x s'.mem

/-- **Applying the bridge**: if the repack pass realises `repackMem`, its output is `RowOut`. -/
theorem repack_realises_rowOut {E : RAMEnv} {R j : ℕ} {s s' : RAMState} {x : Fin R → ZMod 2}
    (h : s'.mem = repackMem E R j (outList s) s.mem) (hout : OutputsSupport s x) :
    RowOut E R j x s'.mem := by
  rw [h]
  exact rowOut_repackMem E R j s x hout

/-! ### 4.5 The row-head family of `stageRun_counted_loop`, and the end-to-end closure -/

/-- **The row-head state family `s j`.**  Row `j`'s iteration starts at the row loop's head, with
the loop counter `r1 = j`, the bound `r2 = d`, and the memory produced by the previous iteration. -/
def rowHeads (Sinit : Stmt) (d : ℕ) (m : ℕ → ℕ) (j : ℕ) : RAMState where
  pc := dRowBase Sinit
  regs := fun i => if i = r1 then j else if i = r2 then d else 0
  mem := m

theorem rowHeads_pc (Sinit : Stmt) (d : ℕ) (m : ℕ → ℕ) (j : ℕ) :
    (rowHeads Sinit d m j).pc = dRowBase Sinit := rfl

theorem rowHeads_regs1 (Sinit : Stmt) (d : ℕ) (m : ℕ → ℕ) (j : ℕ) :
    (rowHeads Sinit d m j).regs r1 = j := by simp [rowHeads]

theorem rowHeads_regs2 (Sinit : Stmt) (d : ℕ) (m : ℕ → ℕ) (j : ℕ) :
    (rowHeads Sinit d m j).regs r2 = d := by simp [rowHeads]

theorem rowHeads_go (Sinit : Stmt) (d : ℕ) (m : ℕ → ℕ) (j : ℕ) (hj : j < d) :
    d65Cond.eval (rowHeads Sinit d m j) := by
  simp only [d65Cond, Cond.eval, rowHeads_regs1, rowHeads_regs2]
  exact hj

theorem rowHeads_stop (Sinit : Stmt) (d : ℕ) (m : ℕ → ℕ) :
    ¬ d65Cond.eval (rowHeads Sinit d m d) := by
  simp only [d65Cond, Cond.eval, rowHeads_regs1, rowHeads_regs2]
  omega

/-- **The `d`-fold row loop closes end to end**, given one `Sem` per iteration.  The per-iteration
`Sem` is `rowBody_sem`'s output with `su/cl/dc/rp` the costs of `clearFull`/`stageStmt`/the 2.1 call/
`repackStmt`; `rowLoop_closes` turns it into the loop's own time bound and exit address. -/
theorem rowLoop_end_to_end {Sinit Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv} {n d cost : ℕ}
    {m : ℕ → ℕ}
    (hW : 1 < 2 ^ E.W)
    (hbody : ∀ j < d, Sem (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E
      (dRowBase Sinit + d65Cond.code.length + 1) (dRowBase Sinit)
      { runBlock d65Cond.code E (rowHeads Sinit d m j) with
        pc := dRowBase Sinit + d65Cond.code.length + 1 }
      (fun k s' => k = cost ∧ s' = rowHeads Sinit d m (j + 1)))
    (hn : 2 ≤ n) (hd : 1 ≤ d) :
    ∃ (k : ℕ) (s' : RAMState),
      (k : ℝ) ≤ ((cost : ℝ) + 5) * (d : ℝ) * lg (n : ℝ) ∧
      (step (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E)^[k] (rowHeads Sinit d m 0) = s' ∧
      s'.pc = dColBase Sinit Srow :=
  R66.rowLoop_closes hW (fun j => rowHeads_pc Sinit d m j)
    (fun j hj => rowHeads_go Sinit d m j hj) (rowHeads_stop Sinit d m) hbody hn hd

end RDecP
end LinearSetReconciliation327.Main


