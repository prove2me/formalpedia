-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_P21BndRead20261122
-- name    : LinearSetReconciliation327_Main_P21BndRead20261122
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T04:16:43.435989+00:00
-- url     : https://prove2.me/theorems/021c7707-e5fb-4cca-9035-9f650d3a2a50
-- title:
--   Proposition 2.1's read stage at a memory that is zero only inside the decoder's workspace (bounded-zero read contract, importable next to DecoderLemmas)
-- statement:
--   **The read stage of Proposition 2.1, weakened to a *bounded* zero hypothesis.**  Write
--   $L=\lceil tw/(8w)\rceil$ for the number of words holding the payload of $y\in\mathbb{F}_2^{tw}$, and
--   $\mathsf{decoderAllocEnd}(t)=8t^2+44t+144$ for the end of Proposition 2.1's scratch.
--
--   The published read contract `pinsketch_decoder_read` starts the 110-instruction stage
--   `inputSavedProcedure` at the *globally* zero memory `hintMem(8w,y,[])` — the memory the copy-in of
--   `pinsketchRunStmt` builds.  Theorem 6.5's row loop cannot supply that: it runs the decoder $d$ times
--   in one memory, and after iteration $j$ the row-$j$ bitmap sits *above* the scratch.  What its clearing
--   pass `clearFull 0 (decoderAllocEnd t)` gives instead is agreement with `hintMem(8w,y,[])` only on the
--   half-open interval $[0,\mathsf{decoderAllocEnd}(t))$.
--
--   This bundle re-derives the whole read stage at such a memory.  If $m$ agrees with
--   $\mathrm{hintMem}(8w,y,[])$ on $[0,\mathsf{decoderAllocEnd}(t))$, then in the same $62t+66$ steps the
--   stage reaches the canonical workspace memory on $[0,\mathsf{decoderAllocEnd}(t))$ — the same
--   `FieldArrayStored` and `PolynomialStored` facts, and zero on
--   $[\mathsf{decoderSavedBase}(t)+2t,\ \mathsf{decoderAllocEnd}(t))$ — **and leaves every word at or
--   above $\mathsf{decoderAllocEnd}(t)$ untouched**.  That frame is what preserves the earlier rows'
--   bitmaps, and every later stage (key solver, root search, verifier) then sees exactly the state it saw
--   at `hintMem`.
--
--   The device is the mask $\mathrm{maskMem}(N,c,m)(a) = $ `if` $a<N$ `then` $c(a)$ `else` $m(a)$ with
--   $N=\mathsf{decoderAllocEnd}(t)$: every memory the stage builds is the mask applied to the canonical
--   `readMem`/`expandMem`, and every case split is discharged by the one static layout bound
--   $S_0+2t\le \mathsf{decoderAllocEnd}(t)$, where $S_0=\lceil tw/(8w)\rceil$ is the syndrome base.  Since
--   the canonical memories are total functions of $(y,t)$ this adds no new mathematics: it is the read
--   stage's own lemmas, re-run at the masked memory (`readMemB`, `expandMemB`, `readBody_specB`,
--   `readLoop_specB`, `expandLoop_resultB`, `inputRead_specB`, `expandAt_specB`, `inputFront_specB`,
--   `saveSyndromeProcedure_specB`).
--
--   **Formalization note.**  The bundle carries the accepted read development verbatim — so the canonical
--   `readMem`/`expandMem` and their proofs are unchanged — plus the masked re-derivation, in the
--   sub-namespace `LinearSetReconciliation327.Main.P21Bnd`; the sub-namespace keeps the read
--   development's own copies of generic helpers (`ramState_eq_of`, `Sem.block`, `writeArray_frame`, …)
--   from clashing with `Definitions.Def_…_DecoderLemmas`, which every caller needs for `MemoryFrame`.  The
--   bundle is fully proved — `#print axioms LinearSetReconciliation327.Main.P21Bnd.pinsketch_decoder_readB`
--   reports `[propext, Classical.choice, Quot.sound]` — and compiles in 15 s under `autoImplicit false`.
--   It supersedes `LinearSetReconciliation327_Main_P21Bnd20261122`, which carries the same development in
--   the flat namespace and therefore cannot be imported together with `DecoderLemmas`.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), §2.1 (word-RAM model) and Proposition 2.1; the verified development of the project (`Solutions/Sol_p21_decode_at.lean`, accepted proof of `pinsketch_decoding_at`).

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_WordRAM
import Definitions.Def_LinearSetReconciliation327_Main_Pinsketch
import Definitions.Def_LinearSetReconciliation327_Main_DecoderModel
import Definitions.Def_LinearSetReconciliation327_Main_DecoderTables
import Definitions.Def_LinearSetReconciliation327_Main_DecoderProgram
import Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_syndrome_recovery

/-!
# Proposition 2.1's read stage at a memory that is zero only inside the workspace

Theorem 6.5's row loop runs the base-relative decoder `d` times in one memory.  After iteration `j`
the row-`j` bitmap sits *above* the decoder's scratch, so the published entry contract
`pinsketch_decoding_at` — which asks the staged memory to vanish outside the payload window
*unbounded above* — is simply false from the second row on.  What the row loop's own clearing pass
`clearFull 0 (decoderAllocEnd t)` does give is the **bounded** hypothesis

  `(∀ a, L ≤ a → a < β → m a = 0) ∧ (∀ a, β + L ≤ a → a < decoderAllocEnd t → m a = 0)`,

and the remaining cost of weakening `pinsketch_decoding_at` to it is exactly this one stage.

This bundle re-derives the read stage (`inputSavedProcedure`, 110 instructions) at an ambient memory
`m` that merely agrees with the canonical entry memory `hintMem (8w) y []` on
`[0, decoderAllocEnd t)`.  The device is the mask

  `maskMem N c m a = if a < N then c a else m a`,  `N = decoderAllocEnd t`:

every memory the stage builds is `maskMem` applied to the canonical `readMem`/`expandMem`, and every
`if` is discharged by the single static layout bound `S0 + 2t ≤ decoderAllocEnd t`.  The stage
therefore cannot disturb anything at or above `decoderAllocEnd t` — the frame the row loop needs —
and its output workspace is canonical, so the later stages see exactly what they saw at `hintMem`.

The contract, in `namespace LinearSetReconciliation327.Main.P21Bnd`:

```lean
theorem pinsketch_decoder_readB (E P base N t w y b ι m)
    (hAt : At P base (Stmt.compile inputSavedProcedure base))
    (hW hw1 hNw htN hdet)
    (hmem : ∀ a, a < decoderAllocEnd t → m a = hintMem (8 * w) y [] a) :
    Sem P E base (base + 110) ⟨base, (decoderStart (8 * w) y []).regs, m⟩
      (fun k z => k ≤ 62 * t + 66 ∧ ∃ m', z = boundaryState (base + 110) m' ∧
        FieldArrayStored b m' (decoderSavedBase t) (2 * t) (eSeq b y) ∧
        PolynomialStored b m' (decoderSavedBase t) (decoderCapacity t) (syndromePoly (eSeq b y) t) ∧
        (∀ addr, decoderSavedBase t + 2 * t ≤ addr → addr < decoderAllocEnd t → m' addr = 0) ∧
        (∀ addr, decoderAllocEnd t ≤ addr → m' addr = m addr))
```

The rest of the development is the read stage's own lemmas (copied verbatim from the accepted
`pinsketch_decoder_read` skeleton, so the canonical memory functions and their proofs are unchanged)
together with their masked copies `…B`.  Everything is proved (no placeholders, no new axiom):
`#print axioms` reports `[propext, Classical.choice, Quot.sound]`.

**Namespace.**  The read development already defines its own copies of a few generic helpers
(`ramState_eq_of`, `Sem.block`, `writeArray_frame`, …) which the platform also carries in
`Definitions.Def_…_DecoderLemmas`.  They are kept here under the sub-namespace `P21Bnd` so that this
bundle can be imported *together with* `DecoderLemmas` — which every caller of the read contract
needs for `MemoryFrame`.  The canonical definitions (`readMem`, `readBody`, `Sem`, …) are the ones
from `Definitions.Def_…_DecoderProgram`, unchanged.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped ENNReal
open Finset Polynomial

namespace LinearSetReconciliation327.Main

namespace P21Bnd


attribute [local simp] readState expandState

section FieldFacts

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

end FieldFacts

section PowerSums

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

variable {N : ℕ}

end PowerSums

/-- Packing a `Fin K`-indexed family is the same as the sum of shifted fields. -/
theorem packL_ofFn (w K : ℕ) (f : Fin K → ℕ) :
    packL w (List.ofFn f) = ∑ j : Fin K, f j * 2 ^ (j.val * w) := by
  induction K with
  | zero => simp [packL]
  | succ n ih =>
      rw [List.ofFn_succ, Fin.sum_univ_succ]
      simp only [packL, Fin.val_zero, Nat.zero_mul, Nat.pow_zero, Nat.mul_one, Fin.val_succ]
      rw [ih (fun i => f i.succ), Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      have h2 : 2 ^ ((j.val + 1) * w) = 2 ^ w * 2 ^ (j.val * w) := by
        rw [Nat.add_mul, Nat.one_mul, Nat.pow_add, Nat.mul_comm]
      rw [h2]
      ring

/-- Extracting the `k`-th `w`-bit field, in division form. -/
theorem extract_field_div (w : ℕ) (_hw : 0 < w) (l : List ℕ) (hx : ∀ x ∈ l, x < 2 ^ w)
    (k : ℕ) : packL w l / 2 ^ (k * w) % 2 ^ w = l.getD k 0 := by
  induction k generalizing l with
  | zero =>
      cases l with
      | nil => simp [packL]
      | cons x xs =>
          have hx' : x < 2 ^ w := hx x (by simp)
          simp only [Nat.zero_mul, Nat.pow_zero, Nat.div_one, packL, List.getD_cons_zero]
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx']
  | succ k ih =>
      cases l with
      | nil => simp [packL]
      | cons x xs =>
          have hx' : x < 2 ^ w := hx x (by simp)
          have hpw : 0 < 2 ^ w := Nat.two_pow_pos w
          have hsplit : 2 ^ ((k + 1) * w) = 2 ^ w * 2 ^ (k * w) := by
            rw [Nat.add_mul, Nat.one_mul, Nat.pow_add, Nat.mul_comm]
          have hlow : (x + 2 ^ w * packL w xs) / 2 ^ w = packL w xs := by
            rw [Nat.add_comm x (2 ^ w * packL w xs), Nat.mul_add_div hpw,
              Nat.div_eq_of_lt hx', Nat.add_zero]
          simp only [packL, List.getD_cons_succ, hsplit, ← Nat.div_div_eq_div_mul, hlow]
          exact ih xs (fun y hy => hx y (by simp [hy]))

/-- The `k`-th `w`-bit field of a packed word, extracted with `>>>` and `&&&`. -/
theorem extract_field (w : ℕ) (hw : 0 < w) (l : List ℕ) (hx : ∀ x ∈ l, x < 2 ^ w) (k : ℕ) :
    (packL w l >>> (k * w)) &&& (2 ^ w - 1) = l.getD k 0 := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  exact extract_field_div w hw l hx k

/-- Field extraction in the form used by the sketches: a word whose `j`-th `w`-bit field is
`f j` yields `f k` by shifting and masking. -/
theorem extract_field_sum (w K : ℕ) (hw : 0 < w) (f : Fin K → ℕ) (hf : ∀ j, f j < 2 ^ w)
    (k : Fin K) :
    ((∑ j : Fin K, f j * 2 ^ (j.val * w)) >>> (k.val * w)) &&& (2 ^ w - 1) = f k := by
  rw [← packL_ofFn w K f]
  rw [extract_field w hw (List.ofFn f) ?_ k.val]
  · have hk : k.val < (List.ofFn f).length := by simp only [List.length_ofFn]; exact k.isLt
    rw [List.getD_eq_getElem (List.ofFn f) 0 hk]
    simp [List.getElem_ofFn]
  · intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    exact hf j

theorem payloadBit_lt_two {M : ℕ} (y : Fin M → ZMod 2) (p : ℕ) : payloadBit y p < 2 :=
  ZMod.val_lt _

theorem payloadBit_le_one {M : ℕ} (y : Fin M → ZMod 2) (p : ℕ) : payloadBit y p ≤ 1 := by
  have h := payloadBit_lt_two y p
  omega

/-- In `ZMod 2` the value of an element is `1` exactly at `1`. -/
theorem zmod2_val (z : ZMod 2) : z.val = if z = 1 then 1 else 0 := by
  have h : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases h z with h | h
  · rw [h]; decide
  · rw [h]; decide

/-- Adding one payload bit at the end only changes the bit at position `M`. -/
theorem payloadBit_succ {M : ℕ} (y : Fin (M + 1) → ZMod 2) (p : ℕ) :
    payloadBit y p =
      payloadBit (fun i : Fin M => y i.castSucc) p +
        (if p = M then (if y (Fin.last M) = 1 then 1 else 0) else 0) := by
  have hlast : (⟨M, Nat.lt_succ_self M⟩ : Fin (M + 1)) = Fin.last M := Fin.ext rfl
  unfold payloadBit payloadAt
  by_cases h : p < M
  · rw [dif_pos h, dif_pos (Nat.lt_succ_of_lt h), if_neg (by omega)]
    simp
  · by_cases h2 : p = M
    · rw [h2, dif_pos (Nat.lt_succ_self M), if_pos rfl, hlast]
      simp [zmod2_val]
    · rw [dif_neg (by omega : ¬ p < M + 1), dif_neg (by omega : ¬ p < M), if_neg h2]
      simp

/-- Peeling the last payload bit off the word that holds it. -/
theorem packMem_succ {W M : ℕ} (y : Fin (M + 1) → ZMod 2) (addr : ℕ) :
    packMem W y addr =
      packMem W (fun i : Fin M => y i.castSucc) addr +
        (if M / W = addr ∧ y (Fin.last M) = 1 then 2 ^ (M % W) else 0) := by
  have hsplit := Fin.sum_univ_castSucc
    (f := fun p : Fin (M + 1) =>
      (if p.val / W = addr ∧ y p = 1 then 2 ^ (p.val % W) else 0))
  simp only [packMem]
  rw [hsplit]
  simp only [Fin.val_castSucc, Fin.val_last]

/-- The bit position inside a word determines the word index. -/
theorem div_eq_of_mul_add {W M c b : ℕ} (hW : 0 < W) (hb : b < W) (h : c * W + b = M) :
    M / W = c := by
  rw [← h, Nat.mul_comm c W, Nat.mul_add_div hW, Nat.div_eq_of_lt hb, Nat.add_zero]

/-- The word `addr` contributes to exactly one bit position, namely `M % W` when `M / W = addr`. -/
theorem sum_range_ite_bit {W M addr v : ℕ} (hW : 0 < W) :
    (∑ b ∈ Finset.range W, (if addr * W + b = M then v else 0) * 2 ^ b)
      = if M / W = addr then v * 2 ^ (M % W) else 0 := by
  by_cases h : M / W = addr
  · have hsingle : addr * W + M % W = M := by
      have h0 := Nat.div_add_mod M W
      rw [h] at h0
      rw [Nat.mul_comm W addr] at h0
      exact h0
    rw [if_pos h,
      Finset.sum_eq_single (M % W)
        (fun b _ hne => by
          rw [if_neg (by intro he; exact hne (by omega))]
          simp)
        (fun hmem => absurd (Finset.mem_range.mpr (Nat.mod_lt M hW)) hmem),
      if_pos hsingle]
  · rw [if_neg h]
    refine Finset.sum_eq_zero (fun b hb => ?_)
    rw [Finset.mem_range] at hb
    rw [if_neg (by intro he; exact h (div_eq_of_mul_add hW hb he))]
    simp

/-- **The packed-word layout**: a packed word is the sum of its payload bits, weighted by
position.  This is `packMem` seen bit by bit. -/
theorem packMem_eq_sum_bits {W : ℕ} (hW : 0 < W) :
    ∀ (M : ℕ) (y : Fin M → ZMod 2) (addr : ℕ),
      packMem W y addr = ∑ b ∈ Finset.range W, payloadBit y (addr * W + b) * 2 ^ b := by
  intro M
  induction M with
  | zero => intro y addr; simp [packMem, payloadBit, payloadAt]
  | succ M ih =>
      intro y addr
      have hstep :
          (∑ b ∈ Finset.range W, payloadBit y (addr * W + b) * 2 ^ b)
            = (∑ b ∈ Finset.range W,
                payloadBit (fun i : Fin M => y i.castSucc) (addr * W + b) * 2 ^ b)
              + (if M / W = addr ∧ y (Fin.last M) = 1 then 2 ^ (M % W) else 0) := by
        have hpt : ∀ b ∈ Finset.range W,
            payloadBit y (addr * W + b) * 2 ^ b
              = payloadBit (fun i : Fin M => y i.castSucc) (addr * W + b) * 2 ^ b
                + (if addr * W + b = M then (if y (Fin.last M) = 1 then 1 else 0) else 0)
                    * 2 ^ b := by
          intro b _
          rw [payloadBit_succ, Nat.add_mul]
        rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, sum_range_ite_bit hW]
        congr 1
        by_cases h1 : M / W = addr <;> by_cases h2 : y (Fin.last M) = 1 <;> simp [h1, h2]
      rw [packMem_succ y addr, ih (fun i : Fin M => y i.castSucc) addr, hstep]

theorem sum_range_two_pow_lt (w : ℕ) : (∑ k ∈ Finset.range w, 2 ^ k) < 2 ^ w := by
  induction w with
  | zero => simp
  | succ w ih =>
      rw [Finset.sum_range_succ, Nat.pow_succ]
      omega

/-- A `w`-bit field built from payload bits is a `w`-bit number. -/
theorem bits_sum_lt_two_pow {w M : ℕ} (y : Fin M → ZMod 2) (c : ℕ) :
    (∑ k ∈ Finset.range w, payloadBit y (c + k) * 2 ^ k) < 2 ^ w := by
  have h1 : (∑ k ∈ Finset.range w, payloadBit y (c + k) * 2 ^ k)
      ≤ ∑ k ∈ Finset.range w, 2 ^ k := by
    refine Finset.sum_le_sum (fun k _ => ?_)
    calc payloadBit y (c + k) * 2 ^ k ≤ 1 * 2 ^ k :=
          Nat.mul_le_mul_right _ (payloadBit_le_one y (c + k))
      _ = 2 ^ k := Nat.one_mul _
  exact lt_of_le_of_lt h1 (sum_range_two_pow_lt w)

/-- Splitting the bits of `n` words of `w` bits into `n` fields of `w` bits. -/
theorem sum_range_bits_split (w n : ℕ) (f : ℕ → ℕ) :
    (∑ b ∈ Finset.range (n * w), f b * 2 ^ b)
      = ∑ i ∈ Finset.range n,
          (∑ k ∈ Finset.range w, f (i * w + k) * 2 ^ k) * 2 ^ (i * w) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Nat.pow_add]
      ring

/-- The coordinates of `payloadField` are the payload bits. -/
theorem payloadField_apply {F : Type} [Field F] [Algebra (ZMod 2) F] {w M : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin M → ZMod 2) (j : ℕ) (k : Fin w) :
    b.repr (payloadField b y j) k = payloadAt y (j * w + k.val) := by
  rw [payloadField, LinearEquiv.apply_symm_apply]
  simp only [Finsupp.coe_equivFunOnFinite_symm]

@[simp] theorem execInstr_imm (E : RAMEnv) (s : RAMState) (d : Fin 16) (v : ℕ) :
    execInstr (.imm d v) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (v % 2 ^ E.W) } := rfl

@[simp] theorem execInstr_add (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.add d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (((s.regs a) + (s.regs b)) % 2 ^ E.W) } := rfl

@[simp] theorem execInstr_mul (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.mul d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (((s.regs a) * (s.regs b)) % 2 ^ E.W) } := rfl

@[simp] theorem execInstr_div (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.div d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (((s.regs a) / (s.regs b)) % 2 ^ E.W) } := rfl

@[simp] theorem execInstr_mod (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.mod d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (((s.regs a) % (s.regs b)) % 2 ^ E.W) } := rfl

@[simp] theorem execInstr_band (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.band d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (((s.regs a) &&& (s.regs b)) % 2 ^ E.W) } := rfl

@[simp] theorem execInstr_shr (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.shr d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (((s.regs a) / 2 ^ (s.regs b)) % 2 ^ E.W) } := rfl

@[simp] theorem execInstr_lt (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.lt d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d ((if (s.regs a) < (s.regs b) then 1 else 0) % 2 ^ E.W) } := rfl

@[simp] theorem execInstr_load (E : RAMEnv) (s : RAMState) (d a : Fin 16) :
    execInstr (.load d a) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d ((s.mem (s.regs a)) % 2 ^ E.W) } := rfl

@[simp] theorem execInstr_store (E : RAMEnv) (s : RAMState) (a v : Fin 16) :
    execInstr (.store a v) E s = { s with pc := s.pc + 1, mem := Function.update s.mem (s.regs a) (s.regs v) } := rfl

@[simp] theorem execInstr_jz (E : RAMEnv) (s : RAMState) (c : Fin 16) (t : ℕ) :
    execInstr (.jz c t) E s = { s with pc := if (s.regs c) = 0 then t else s.pc + 1 } := rfl

@[simp] theorem execInstr_jmp (E : RAMEnv) (s : RAMState) (t : ℕ) :
    execInstr (.jmp t) E s = { s with pc := t } := rfl

@[simp] theorem execInstr_qDet (E : RAMEnv) (s : RAMState) (d a : Fin 16) :
    execInstr (.qDet d a) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d ((E.det (s.regs a)) % 2 ^ E.W) } := rfl

/-- `step` runs the branch of `execInstr` at the current program counter. -/
theorem step_eq_execInstr (P : Program) (E : RAMEnv) (s : RAMState) (i : Instr)
    (h : P[s.pc]? = some i) : step P E s = execInstr i E s := by
  unfold step execInstr
  rw [h]
  cases i <;> rfl

/-- Two machine states with the same program counter, memory and registers are equal. -/
theorem ramState_eq_of (a b : RAMState) (hpc : a.pc = b.pc) (hmem : a.mem = b.mem)
    (hregs : ∀ d, a.regs d = b.regs d) : a = b := by
  obtain ⟨p1, r1', m1⟩ := a
  obtain ⟨p2, r2', m2⟩ := b
  simp only at hpc hmem hregs
  subst hpc
  subst hmem
  rw [funext hregs]

/-- A non-branching, non-halting instruction advances the program counter by one. -/
theorem execInstr_pc (i : Instr) (E : RAMEnv) (s : RAMState) (hno : i.NoBranchI) :
    (execInstr i E s).pc = s.pc + 1 := by
  obtain ⟨h1, h2, h3⟩ := hno
  cases i <;> simp_all [execInstr]

@[simp] theorem noBranch_nil : NoBranch ([] : List Instr) ↔ True := by simp [NoBranch]

@[simp] theorem noBranch_cons (i : Instr) (c : List Instr) :
    NoBranch (i :: c) ↔ i.NoBranchI ∧ NoBranch c := by simp [NoBranch]

@[simp] theorem noBranchI_imm (d : Fin 16) (v : ℕ) : (iImm d v).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h

@[simp] theorem noBranchI_add (d a b : Fin 16) : (iAdd d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h

@[simp] theorem noBranchI_mul (d a b : Fin 16) : (iMul d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h

@[simp] theorem noBranchI_div (d a b : Fin 16) : (iDiv d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h

@[simp] theorem noBranchI_mod (d a b : Fin 16) : (iMod d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h

@[simp] theorem noBranchI_band (d a b : Fin 16) : (iBand d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h

@[simp] theorem noBranchI_shr (d a b : Fin 16) : (iShr d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h

@[simp] theorem noBranchI_lt (d a b : Fin 16) : (iLt d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h

@[simp] theorem noBranchI_load (d a : Fin 16) : (iLd d a).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h

@[simp] theorem noBranchI_store (a v : Fin 16) : (iSt a v).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h

@[simp] theorem noBranchI_qDet (d a : Fin 16) : (iTbl d a).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h

@[simp] theorem runBlock_nil (E : RAMEnv) (s : RAMState) : runBlock [] E s = s := rfl

@[simp] theorem runBlock_cons (i : Instr) (code : List Instr) (E : RAMEnv) (s : RAMState) :
    runBlock (i :: code) E s = runBlock code E (execInstr i E s) := by
  simp [runBlock, List.foldl_cons]

/-- Concatenation of straight-line blocks. -/
theorem runBlock_append (c₁ c₂ : List Instr) (E : RAMEnv) (s : RAMState) :
    runBlock (c₁ ++ c₂) E s = runBlock c₂ E (runBlock c₁ E s) := by
  simp [runBlock, List.foldl_append]

/-- A straight-line block advances the program counter by its length. -/
theorem runBlock_pc (code : List Instr) (E : RAMEnv) (s : RAMState) (hno : NoBranch code) :
    (runBlock code E s).pc = s.pc + code.length := by
  induction code generalizing s with
  | nil => simp
  | cons i tl ih =>
      obtain ⟨hi, ht⟩ := hno
      rw [runBlock_cons, ih (s := execInstr i E s) ht, execInstr_pc i E s hi]
      simp only [List.length_cons]
      omega

/-- Front peeling of iterates: the first step is applied first. -/
theorem iterate_succ_apply_front {α : Type} (f : α → α) (n : ℕ) (x : α) :
    f^[n + 1] x = (f^[n]) (f x) := by
  rw [Function.iterate_add_apply]
  rfl

theorem At.cons {P : Program} {a : ℕ} {i : Instr} {l : List Instr} :
    At P a (i :: l) ↔ P[a]? = some i ∧ At P (a + 1) l := by
  constructor
  · intro h
    refine ⟨?_, fun r hr => ?_⟩
    · have h0 := h 0 (by simp)
      simpa using h0
    · have h1 := h (r + 1) (by simpa using hr)
      rw [show a + (r + 1) = a + 1 + r from by omega] at h1
      simpa using h1
  · rintro ⟨h1, h2⟩ r hr
    cases r with
    | zero => simpa using h1
    | succ r =>
        have h3 := h2 r (by simpa using hr)
        rw [show a + (r + 1) = a + 1 + r from by omega]
        simpa using h3

@[simp] theorem At.nil {P : Program} {a : ℕ} : At P a ([] : List Instr) ↔ True := by
  unfold At
  simp

theorem At.append {P : Program} {a : ℕ} {l₁ l₂ : List Instr} :
    At P a (l₁ ++ l₂) ↔ At P a l₁ ∧ At P (a + l₁.length) l₂ := by
  constructor
  · intro h
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · have h' := h r (by simp only [List.length_append]; omega)
      rwa [List.getElem?_append_left hr] at h'
    · have h' := h (l₁.length + r) (by simp only [List.length_append]; omega)
      rw [List.getElem?_append_right (by omega : l₁.length ≤ l₁.length + r)] at h'
      rw [show l₁.length + r - l₁.length = r from by omega] at h'
      rwa [show a + (l₁.length + r) = a + l₁.length + r from by omega] at h'
  · intro ⟨h₁, h₂⟩ r hr
    by_cases hlt : r < l₁.length
    · rw [List.getElem?_append_left hlt]
      exact h₁ r hlt
    · rw [List.getElem?_append_right (by omega : l₁.length ≤ r)]
      have hlen : (l₁ ++ l₂).length = l₁.length + l₂.length := List.length_append ..
      rw [hlen] at hr
      have h := h₂ (r - l₁.length) (by omega)
      rwa [show a + l₁.length + (r - l₁.length) = a + r from by omega] at h

/-- A block found by `At` runs exactly as `runBlock` says. -/
theorem iterate_runBlock_of_at (P : Program) (E : RAMEnv) :
    ∀ (l : List Instr) (s : RAMState), At P s.pc l → NoBranch l →
      (step P E)^[l.length] s = runBlock l E s
  | [], s, _, _ => by simp
  | i :: tl, s, ha, hno => by
      obtain ⟨hi, ht⟩ := hno
      have hg : P[s.pc]? = some i := by
        have h := ha 0 (by simp)
        simpa using h
      have hstep : step P E s = execInstr i E s := step_eq_execInstr P E s i hg
      have hpc : (execInstr i E s).pc = s.pc + 1 := execInstr_pc i E s hi
      have ha' : At P (execInstr i E s).pc tl := by
        intro r hr
        rw [hpc]
        have h := ha (r + 1) (by simpa using hr)
        rw [show s.pc + (r + 1) = s.pc + 1 + r from by omega] at h
        simpa using h
      rw [List.length_cons, iterate_succ_apply_front, hstep, runBlock_cons]
      exact iterate_runBlock_of_at P E tl (execInstr i E s) ha' ht

theorem Cond.noBranch_code (c : Cond) : NoBranch c.code := by
  cases c with
  | neqz r => simp [Cond.code]
  | lt d a b => simp [Cond.code]

/-- A test holds exactly when its test register, after the test code, is nonzero. -/
theorem Cond.eval_iff (c : Cond) (E : RAMEnv) (s : RAMState) (hW : 1 < 2 ^ E.W) :
    c.eval s ↔ (runBlock c.code E s).regs c.test ≠ 0 := by
  cases c with
  | neqz r => simp [Cond.eval, Cond.code, Cond.test]
  | lt d a b =>
      have hcode : Cond.code (Cond.lt d a b) = [iLt d a b] := rfl
      have htest : Cond.test (Cond.lt d a b) = d := rfl
      have hrun : (runBlock (Cond.code (Cond.lt d a b)) E s).regs (Cond.test (Cond.lt d a b))
          = (if s.regs a < s.regs b then 1 else 0) % 2 ^ E.W := by
        rw [hcode, htest, runBlock_cons, runBlock_nil, execInstr_lt]
        simp
      rw [hrun]
      by_cases h : s.regs a < s.regs b
      · rw [if_pos h, Nat.mod_eq_of_lt hW]
        exact ⟨fun _ => one_ne_zero, fun _ => h⟩
      · rw [if_neg h]
        exact ⟨fun hc => absurd hc h, fun hc => absurd hc (by simp)⟩

theorem Stmt.length_compile (s : Stmt) (base : ℕ) : (s.compile base).length = s.len := by
  induction s generalizing base with
  | code l => rfl
  | seq a b iha ihb =>
      simp only [Stmt.compile, Stmt.len, iha, ihb, List.length_append] <;> omega
  | ite c a b iha ihb =>
      simp only [Stmt.compile, Stmt.len, iha, ihb, List.length_append, List.length_singleton,
        List.length_cons, List.length_nil] <;> omega
  | loop c b ih =>
      simp only [Stmt.compile, Stmt.len, ih, List.length_append, List.length_singleton,
        List.length_cons, List.length_nil] <;> omega

theorem at_loop {P : Program} {a : ℕ} {c : Cond} {b : Stmt}
    (h : At P a (Stmt.compile (Stmt.loop c b) a)) :
    At P a c.code ∧ P[a + c.code.length]? = some (iJz c.test (a + c.code.length + b.len + 2)) ∧
      At P (a + c.code.length + 1) (b.compile (a + c.code.length + 1)) ∧
      P[a + c.code.length + 1 + b.len]? = some (iJmp a) := by
  simpa [Stmt.compile, Stmt.length_compile, At.append, At.cons, At.nil] using h

/-- A block runs exactly as `runBlock` says. -/
theorem Sem.block (P : Program) (E : RAMEnv) (a : ℕ) (l : List Instr) (s : RAMState)
    (hAt : At P a l) (hno : NoBranch l) (hpc : s.pc = a) :
    Sem P E a (a + l.length) s (fun k s' => k = l.length ∧ s' = runBlock l E s) := by
  refine ⟨hpc, l.length, runBlock l E s, ?_, ?_, rfl, rfl⟩
  · exact iterate_runBlock_of_at P E l s (hpc.symm ▸ hAt) hno
  · rw [runBlock_pc l E s hno, hpc]

/-- One instruction. -/
theorem Sem.exec (P : Program) (E : RAMEnv) (a b : ℕ) (s : RAMState) (i : Instr)
    (hAt : P[a]? = some i) (hpc : s.pc = a) (hb : (execInstr i E s).pc = b) :
    Sem P E a b s (fun k s' => k = 1 ∧ s' = execInstr i E s) := by
  refine ⟨hpc, 1, execInstr i E s, ?_, hb, rfl, rfl⟩
  rw [Function.iterate_one, step_eq_execInstr P E s i (by rwa [← hpc] at hAt)]

/-- Weakening the postcondition. -/
theorem Sem.mono {P : Program} {E : RAMEnv} {a b : ℕ} {s : RAMState}
    {Q Q' : ℕ → RAMState → Prop} (h : Sem P E a b s Q) (hQ : ∀ k s', Q k s' → Q' k s') :
    Sem P E a b s Q' := by
  obtain ⟨hpc, k, s', hstep, hb, hQ'⟩ := h
  exact ⟨hpc, k, s', hstep, hb, hQ k s' hQ'⟩

/-- A `jz` whose test register is zero takes its target, in one step. -/
theorem Sem.jz_taken (P : Program) (E : RAMEnv) (a t : ℕ) (c : Cond) (s : RAMState)
    (hAt : P[a]? = some (iJz c.test t)) (hpc : s.pc = a) (h0 : s.regs c.test = 0) :
    Sem P E a t s (fun k s' => k = 1 ∧ s' = { s with pc := t }) := by
  refine Sem.mono (Sem.exec P E a t s (iJz c.test t) hAt hpc ?_) ?_
  · simp [execInstr_jz, h0]
  · intro k s' h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by simp [execInstr_jz, h0]⟩

/-- A `jz` whose test register is nonzero falls through, in one step. -/
theorem Sem.jz_next (P : Program) (E : RAMEnv) (a t : ℕ) (c : Cond) (s : RAMState)
    (hAt : P[a]? = some (iJz c.test t)) (hpc : s.pc = a) (h0 : s.regs c.test ≠ 0) :
    Sem P E a (a + 1) s (fun k s' => k = 1 ∧ s' = { s with pc := a + 1 }) := by
  refine Sem.mono (Sem.exec P E a (a + 1) s (iJz c.test t) hAt hpc ?_) ?_
  · simp [execInstr_jz, h0, hpc]
  · intro k s' h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by simp [execInstr_jz, h0, hpc]⟩

/-- Two exact runs glue, and the costs add. -/
theorem Sem.trans {P : Program} {E : RAMEnv} {a b c : ℕ} {s : RAMState} {n₁ n₂ : ℕ}
    {s₁ s₂ : RAMState}
    (h₁ : Sem P E a b s (fun k s' => k = n₁ ∧ s' = s₁))
    (h₂ : Sem P E b c s₁ (fun k s' => k = n₂ ∧ s' = s₂)) :
    Sem P E a c s (fun k s' => k = n₁ + n₂ ∧ s' = s₂) := by
  obtain ⟨hpc, k₁, t₁, hs₁, -, hk₁, ht₁⟩ := h₁
  obtain ⟨-, k₂, t₂, hs₂, hc, hk₂, ht₂⟩ := h₂
  refine ⟨hpc, k₁ + k₂, s₂, ?_, ?_, by omega, rfl⟩
  · rw [Nat.add_comm k₁ k₂, Function.iterate_add_apply, hs₁, ht₁, hs₂, ht₂]
  · rw [← ht₂]
    exact hc

/-- Sequential composition: the second run may depend on the cost and the state of the first. -/
theorem Sem.seq {P : Program} {E : RAMEnv} {a b c : ℕ} {s : RAMState}
    {Q₁ : ℕ → RAMState → Prop} {Q₂ : ℕ → ℕ → RAMState → Prop}
    (h₁ : Sem P E a b s Q₁)
    (h₂ : ∀ (k₁ : ℕ) (s₁ : RAMState), Q₁ k₁ s₁ → Sem P E b c s₁ (Q₂ k₁)) :
    Sem P E a c s (fun k s' => ∃ k₁ k₂, k = k₁ + k₂ ∧ Q₂ k₁ k₂ s') := by
  obtain ⟨hpc, k₁, s₁, hs₁, -, hQ₁⟩ := h₁
  obtain ⟨-, k₂, s₂, hs₂, hc, hQ₂⟩ := h₂ k₁ s₁ hQ₁
  refine ⟨hpc, k₁ + k₂, s₂, ?_, hc, k₁, k₂, rfl, hQ₂⟩
  rw [Nat.add_comm k₁ k₂, Function.iterate_add_apply, hs₁, hs₂]

/-- Append a `jmp`: the postcondition sees the state with its program counter already moved. -/
theorem Sem.jmp_append {P : Program} {E : RAMEnv} {a b c : ℕ} {s : RAMState}
    {Q : ℕ → RAMState → Prop} (hAt : P[b]? = some (iJmp c))
    (h : Sem P E a b s (fun t s' => Q (t + 1) { s' with pc := c })) :
    Sem P E a c s Q := by
  obtain ⟨hpc, k, s', hstep, hpb, hQ⟩ := h
  have hstep' : (step P E)^[k + 1] s = { s' with pc := c } := by
    rw [show k + 1 = 1 + k from by omega, Function.iterate_add_apply, Function.iterate_one, hstep,
      step_eq_execInstr P E s' (iJmp c) (by rw [hpb]; exact hAt), execInstr_jmp]
  exact ⟨hpc, k + 1, { s' with pc := c }, hstep', rfl, hQ⟩

/-- Leaving the loop: the test fails, the `jz` fires, control lands past the statement. -/
theorem Sem.loopExit (P : Program) (E : RAMEnv) (a : ℕ) (c : Cond) (b : Stmt) (s : RAMState)
    (hAt : At P a (Stmt.compile (Stmt.loop c b) a)) (hW : 1 < 2 ^ E.W) (hpc : s.pc = a)
    (hstop : ¬ c.eval s) :
    Sem P E a (a + c.code.length + b.len + 2) s
      (fun k s' => k = c.code.length + 1 ∧
        s' = { runBlock c.code E s with pc := a + c.code.length + b.len + 2 }) := by
  obtain ⟨hcode, hjz, -, -⟩ := at_loop hAt
  have htest : Sem P E a (a + c.code.length) s
      (fun k s' => k = c.code.length ∧ s' = runBlock c.code E s) :=
    Sem.block P E a c.code s hcode (Cond.noBranch_code c) hpc
  have hpcT : (runBlock c.code E s).pc = a + c.code.length := by
    rw [runBlock_pc c.code E s (Cond.noBranch_code c), hpc]
  have h0 : (runBlock c.code E s).regs c.test = 0 := by
    by_contra hne
    exact hstop ((Cond.eval_iff c E s hW).mpr hne)
  exact Sem.trans htest
    (Sem.jz_taken P E (a + c.code.length) (a + c.code.length + b.len + 2) c _ hjz hpcT h0)

/-- One iteration that returns to the head: the test holds, the `jz` falls through, the body runs
from the body entry back to the loop head. -/
theorem Sem.loopStep (P : Program) (E : RAMEnv) (a : ℕ) (c : Cond) (b : Stmt)
    (s s' : RAMState) (cost : ℕ) (hAt : At P a (Stmt.compile (Stmt.loop c b) a)) (hW : 1 < 2 ^ E.W)
    (hpc : s.pc = a) (hgo : c.eval s)
    (hbody : Sem P E (a + c.code.length + 1) a { runBlock c.code E s with pc := a + c.code.length + 1 }
      (fun k s'' => k = cost ∧ s'' = s')) :
    Sem P E a a s (fun k s'' => k = (c.code.length + 1) + cost ∧ s'' = s') := by
  obtain ⟨hcode, hjz, -, -⟩ := at_loop hAt
  have htest : Sem P E a (a + c.code.length) s
      (fun k s' => k = c.code.length ∧ s' = runBlock c.code E s) :=
    Sem.block P E a c.code s hcode (Cond.noBranch_code c) hpc
  have hne : (runBlock c.code E s).regs c.test ≠ 0 := (Cond.eval_iff c E s hW).mp hgo
  have hpcT : (runBlock c.code E s).pc = a + c.code.length := by
    rw [runBlock_pc c.code E s (Cond.noBranch_code c), hpc]
  have hfall : Sem P E (a + c.code.length) (a + c.code.length + 1) (runBlock c.code E s)
      (fun k s' => k = 1 ∧ s' = { runBlock c.code E s with pc := a + c.code.length + 1 }) :=
    Sem.jz_next P E (a + c.code.length) (a + c.code.length + b.len + 2) c _ hjz hpcT hne
  exact Sem.trans (Sem.trans htest hfall) hbody

/-- **The loop rule.**  `n` iterations from the loop head, then the failing test.  The iteration
invariant is an explicit family `s : ℕ → RAMState` of loop-head states, with per-iteration costs
`cost : ℕ → ℕ`; the caller supplies one `Sem` per iteration. -/
theorem Sem.loop (P : Program) (E : RAMEnv) (a : ℕ) (c : Cond) (b : Stmt)
    (hAt : At P a (Stmt.compile (Stmt.loop c b) a)) (hW : 1 < 2 ^ E.W) :
    ∀ (n : ℕ) (s : ℕ → RAMState) (cost : ℕ → ℕ),
      (∀ j, (s j).pc = a) →
      (∀ j < n, c.eval (s j)) →
      (¬ c.eval (s n)) →
      (∀ j < n, Sem P E (a + c.code.length + 1) a
        { runBlock c.code E (s j) with pc := a + c.code.length + 1 }
        (fun k s' => k = cost j ∧ s' = s (j + 1))) →
      Sem P E a (a + c.code.length + b.len + 2) (s 0)
        (fun k s' => k ≤ (c.code.length + 1) +
            ∑ j ∈ Finset.range n, (c.code.length + 1 + cost j) ∧
          s' = { runBlock c.code E (s n) with pc := a + c.code.length + b.len + 2 }) := by
  intro n
  induction n with
  | zero =>
      intro s cost hpc _ hstop _
      refine Sem.mono (Sem.loopExit P E a c b (s 0) hAt hW (hpc 0) hstop) ?_
      intro k s' h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simp, rfl⟩
  | succ n ih =>
      intro s cost hpc hgo hstop hstep
      have hfirst : Sem P E a a (s 0) (fun k s' => k = (c.code.length + 1) + cost 0 ∧ s' = s 1) :=
        Sem.loopStep P E a c b (s 0) (s 1) (cost 0) hAt hW (hpc 0) (hgo 0 (by omega))
          (hstep 0 (by omega))
      have hrest : Sem P E a (a + c.code.length + b.len + 2) (s 1)
          (fun k s' => k ≤ (c.code.length + 1) +
              ∑ j ∈ Finset.range n, (c.code.length + 1 + cost (j + 1)) ∧
            s' = { runBlock c.code E (s (n + 1)) with pc := a + c.code.length + b.len + 2 }) :=
        ih (fun j => s (j + 1)) (fun j => cost (j + 1)) (fun j => hpc (j + 1))
          (fun j hj => hgo (j + 1) (by omega)) (by simpa using hstop)
          (fun j hj => hstep (j + 1) (by omega))
      refine Sem.mono (Sem.seq (Q₂ := fun k₁ k₂ s' =>
        k₁ = (c.code.length + 1) + cost 0 ∧
          (k₂ ≤ (c.code.length + 1) +
              ∑ j ∈ Finset.range n, (c.code.length + 1 + cost (j + 1)) ∧
            s' = { runBlock c.code E (s (n + 1)) with pc := a + c.code.length + b.len + 2 })) hfirst ?_) ?_
      · intro k₁ s₁ hQ₁
        obtain ⟨rfl, rfl⟩ : k₁ = (c.code.length + 1) + cost 0 ∧ s₁ = s 1 := hQ₁
        exact Sem.mono hrest (fun k s' h => ⟨rfl, h.1, h.2⟩)
      · intro k s' h
        obtain ⟨k₁, k₂, hk, h₁, h₂, hstate⟩ := h
        rw [Finset.sum_range_succ']
        exact ⟨by omega, hstate⟩

section Enc

variable {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}

/-- A bit of the integer spelling is the corresponding basis coordinate. -/
theorem enc_bit (b : Module.Basis (Fin w) (ZMod 2) F) (z : F) (k : Fin w) :
    enc b z / 2 ^ (k : ℕ) % 2 = (b.repr z k).val := by
  have hf : ∀ j : Fin w, (b.repr z j).val < 2 ^ 1 := by
    intro j
    have := ZMod.val_lt (b.repr z j)
    simpa using this
  have h := extract_field_sum 1 w (by norm_num) (fun j : Fin w => (b.repr z j).val) hf k
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow] at h
  simpa [enc, Nat.mul_one] using h

/-- `dec` inverts `enc`. -/
theorem dec_enc (b : Module.Basis (Fin w) (ZMod 2) F) (z : F) : dec b (enc b z) = z := by
  have h : ∀ k : Fin w, b.repr (dec b (enc b z)) k = b.repr z k := by
    intro k
    rw [dec, LinearEquiv.apply_symm_apply]
    simp only [Finsupp.coe_equivFunOnFinite_symm]
    rw [show (((enc b z / 2 ^ (k : ℕ)) % 2 : ℕ) : ZMod 2) = (((b.repr z k).val : ℕ) : ZMod 2) from by
      rw [enc_bit b z k]]
    exact ZMod.natCast_zmod_val (b.repr z k)
  apply b.repr.injective
  ext k
  exact h k

/-- The integer spelling of a field element is a `w`-bit number. -/
theorem enc_lt (b : Module.Basis (Fin w) (ZMod 2) F) (z : F) : enc b z < 2 ^ w := by
  have h1 : enc b z ≤ ∑ k : Fin w, 2 ^ (k : ℕ) := by
    refine Finset.sum_le_sum (fun k _ => ?_)
    calc (b.repr z k).val * 2 ^ (k : ℕ) ≤ 1 * 2 ^ (k : ℕ) := by
          refine Nat.mul_le_mul_right _ ?_
          have := ZMod.val_lt (b.repr z k)
          omega
      _ = 2 ^ (k : ℕ) := Nat.one_mul _
  have h2 : (∑ k : Fin w, 2 ^ (k : ℕ)) = ∑ k ∈ Finset.range w, 2 ^ k :=
    Fin.sum_univ_eq_sum_range (fun k => 2 ^ k) w
  rw [h2] at h1
  exact lt_of_le_of_lt h1 (sum_range_two_pow_lt w)

/-- **The bridge**: the integer the machine reads out of the packed payload is the integer spelling
of the `j`-th syndrome coordinate. -/
theorem enc_payloadField (b : Module.Basis (Fin w) (ZMod 2) F) {M : ℕ} (y : Fin M → ZMod 2)
    (j : ℕ) :
    enc b (payloadField b y j)
      = ∑ k ∈ Finset.range w, payloadBit y (j * w + k) * 2 ^ k := by
  have h : ∀ k : Fin w,
      (b.repr (payloadField b y j) k).val * 2 ^ (k : ℕ)
        = payloadBit y (j * w + k) * 2 ^ (k : ℕ) := by
    intro k
    rw [payloadField_apply b y j k]
    rfl
  rw [enc, Finset.sum_congr rfl (fun k _ => h k)]
  exact Fin.sum_univ_eq_sum_range (fun k => payloadBit y (j * w + k) * 2 ^ k) w

end Enc

section Tables

variable {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}

@[simp] theorem hdrTab_zero (t N w : ℕ) : hdrTab t N w 0 = t := rfl

@[simp] theorem hdrTab_one (t N w : ℕ) : hdrTab t N w 1 = w := rfl

@[simp] theorem hdrTab_four (t N w : ℕ) : hdrTab t N w 4 = wordsOf (8 * w) (t * w) := rfl

@[simp] theorem hdrTab_five (t N w : ℕ) : hdrTab t N w 5 = 2 ^ w - 1 := rfl

@[simp] theorem hdrTab_six (t N w : ℕ) : hdrTab t N w 6 = detSqBase w := rfl

@[simp] theorem hdrTab_twelve (t N w : ℕ) : hdrTab t N w 12 = 8 * w := rfl

theorem detStd_hdr (t N w : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) {a : ℕ}
    (ha : a < 13) : detStd t N b ι a = hdrTab t N w a := by
  simp [detStd, ha]

/-- `detSqBase` in explicit form. -/
theorem detSqBase_eq (w : ℕ) : detSqBase w = 64 + 2 ^ (2 * w) := rfl

/-- `detMulBase` in explicit form. -/
theorem detMulBase_eq (w : ℕ) : detMulBase w = 64 := rfl

/-- **The squaring table is at a known address**: `detSqBase w + a` holds `sqTab b a` for every
`w`-bit `a`. -/
theorem detStd_sq (t N w : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) {a : ℕ}
    (ha : a < 2 ^ w) : detStd t N b ι (detSqBase w + a) = sqTab b a := by
  have hpos : (0 : ℕ) < 2 ^ (2 * w) := Nat.two_pow_pos _
  have hwle : (2 : ℕ) ^ w ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h1 : ¬ (detSqBase w + a < 13) := by rw [detSqBase_eq]; omega
  have h2 : ¬ (detSqBase w + a < detMulBase w) := by rw [detSqBase_eq, detMulBase_eq]; omega
  have h3 : ¬ (detSqBase w + a < detSqBase w) := by omega
  have h4 : detSqBase w + a < detInvBase w := by unfold detInvBase; omega
  unfold detStd
  rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
  congr 1
  omega

end Tables

section ReadInt

/-- **Extraction of the `i`-th field of word `addr`**, for a word of `m * w` bits. -/
theorem packMem_field_mul {w m : ℕ} (hw : 0 < w) (hm : 0 < m) (M : ℕ) (y : Fin M → ZMod 2)
    (addr : ℕ) (i : Fin m) :
    packMem (m * w) y addr / 2 ^ (i.val * w) % 2 ^ w
      = ∑ k ∈ Finset.range w, payloadBit y (addr * (m * w) + i.val * w + k) * 2 ^ k := by
  have hmw : 0 < m * w := Nat.mul_pos hm hw
  have hpack : packMem (m * w) y addr
      = ∑ j : Fin m,
          (∑ k ∈ Finset.range w, payloadBit y (addr * (m * w) + j.val * w + k) * 2 ^ k)
            * 2 ^ (j.val * w) := by
    rw [packMem_eq_sum_bits hmw,
      sum_range_bits_split w m (fun b => payloadBit y (addr * (m * w) + b))]
    simp only [Nat.add_assoc]
    exact (Fin.sum_univ_eq_sum_range (fun j => (∑ k ∈ Finset.range w,
      payloadBit y (addr * (m * w) + (j * w + k)) * 2 ^ k) * 2 ^ (j * w)) m).symm
  rw [hpack, ← Nat.and_two_pow_sub_one_eq_mod, ← Nat.shiftRight_eq_div_pow]
  exact extract_field_sum w m hw _ (fun j => bits_sum_lt_two_pow y _) i

/-- **The read of syndrome coordinate `j`**: shift the payload word down by the offset of `j` and
mask the low `w` bits. -/
theorem read_syndrome {w : ℕ} (hw : 0 < w) (M : ℕ) (y : Fin M → ZMod 2) (j : ℕ) :
    ((packMem (8 * w) y (j / 8) >>> ((j % 8) * w)) &&& (2 ^ w - 1)) = syndromeInt w y j := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  rw [packMem_field_mul hw (by norm_num) M y (j / 8) ⟨j % 8, Nat.mod_lt _ (by norm_num)⟩]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have h1 : (j / 8) * 8 + j % 8 = j := by
    rw [Nat.mul_comm (j / 8) 8]
    exact Nat.div_add_mod j 8
  have h2 : (j / 8) * (8 * w) + (j % 8) * w = j * w := by
    rw [← Nat.mul_assoc, ← Nat.add_mul, h1]
  rw [h2]

theorem mul_div_eight (w : ℕ) (hw : 0 < w) (k : ℕ) : k * w / (8 * w) = k / 8 := by
  rw [Nat.mul_comm k w, Nat.mul_comm 8 w, Nat.mul_div_mul_left k 8 hw]

theorem mul_mod_eight (w : ℕ) (k : ℕ) : k * w % (8 * w) = k % 8 * w :=
  Nat.mul_mod_mul_right w k 8

/-- Divisions are unchanged by adding a remainder that stays below the divisor. -/
theorem add_div_of_mod_add_lt {A b c : ℕ} (h : A % c + b < c) : (A + b) / c = A / c := by
  have hc : 0 < c := by omega
  have h1 : c * (A / c) + (A % c + b) = A + b := by
    have h2 := Nat.div_add_mod A c
    omega
  rw [← h1, Nat.mul_add_div hc, Nat.div_eq_of_lt h, Nat.add_zero]

/-- `wordsOf` for a word that holds eight `w`-bit fields: `⌈t/8⌉` words.  `as in the paper`, the
payload of `tw` bits occupies `tw / W = ⌈t/8⌉` words of `W = 8w` bits. -/
theorem wordsOf_eight (w t : ℕ) (hw : 0 < w) : wordsOf (8 * w) (t * w) = (t + 7) / 8 := by
  unfold wordsOf
  have h1 : t * w + 8 * w - 1 = (t + 7) * w + (w - 1) := by
    have h2 : t * w + 8 * w = (t + 8) * w := by rw [Nat.add_mul]
    have h3 : (t + 8) * w = (t + 7) * w + w := by
      rw [show t + 8 = t + 7 + 1 from rfl, Nat.succ_mul]
    rw [h2, h3]
    omega
  rw [h1]
  have h4 : (t + 7) * w % (8 * w) + (w - 1) < 8 * w := by
    rw [Nat.mul_mod_mul_right w (t + 7) 8]
    have h5 : (t + 7) % 8 ≤ 7 := by
      have h6 : (t + 7) % 8 < 8 := Nat.mod_lt _ (by norm_num)
      omega
    have h6 : (t + 7) % 8 * w ≤ 7 * w := Nat.mul_le_mul_right w h5
    omega
  rw [add_div_of_mod_add_lt h4, Nat.mul_comm (t + 7) w, Nat.mul_comm 8 w,
    Nat.mul_div_mul_left (t + 7) 8 hw]

end ReadInt

section ReadLoop

/-- A packed word is a `W`-bit word. -/
theorem packMem_lt {w M : ℕ} (hw : 0 < w) (y : Fin M → ZMod 2) (addr : ℕ) :
    packMem (8 * w) y addr < 2 ^ (8 * w) := by
  have hW : 0 < 8 * w := by omega
  rw [packMem_eq_sum_bits hW]
  have h1 : (∑ b ∈ Finset.range (8 * w), payloadBit y (addr * (8 * w) + b) * 2 ^ b)
      ≤ ∑ b ∈ Finset.range (8 * w), 2 ^ b := by
    refine Finset.sum_le_sum (fun b _ => ?_)
    calc payloadBit y (addr * (8 * w) + b) * 2 ^ b ≤ 1 * 2 ^ b :=
          Nat.mul_le_mul_right _ (payloadBit_le_one y _)
      _ = 2 ^ b := Nat.one_mul _
  exact lt_of_le_of_lt h1 (sum_range_two_pow_lt (8 * w))

theorem readMem_zero {M : ℕ} (S0 w : ℕ) (y : Fin M → ZMod 2) :
    readMem S0 w y 0 = fun addr => if addr < S0 then packMem (8 * w) y addr else 0 := by
  funext addr
  simp only [readMem]
  by_cases h : addr < S0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    rw [if_neg (by omega : ¬ ((addr - S0) % 2 = 0 ∧ (addr - S0) / 2 < 0))]

theorem readMem_succ {M : ℕ} (S0 w : ℕ) (y : Fin M → ZMod 2) (k : ℕ) :
    readMem S0 w y (k + 1)
      = Function.update (readMem S0 w y k) (S0 + 2 * k) (syndromeInt w y k) := by
  funext addr
  by_cases h : addr = S0 + 2 * k
  · subst h
    rw [Function.update_self]
    simp only [readMem]
    rw [if_neg (by omega)]
    have h2 : S0 + 2 * k - S0 = 2 * k := by omega
    rw [h2, if_pos ⟨by omega, by omega⟩]
    norm_num
  · rw [Function.update_of_ne h]
    simp only [readMem]
    by_cases hlt : addr < S0
    · rw [if_pos hlt, if_pos hlt]
    · rw [if_neg hlt, if_neg hlt]
      by_cases hc : (addr - S0) % 2 = 0 ∧ (addr - S0) / 2 < k
      · rw [if_pos hc, if_pos ⟨hc.1, by omega⟩]
      · rw [if_neg hc, if_neg]
        intro hc'
        obtain ⟨h1, h2⟩ := hc'
        have h3 : (addr - S0) / 2 = k := by omega
        have h4 : (addr - S0) = 2 * k := by
          have h5 := Nat.div_add_mod (addr - S0) 2
          omega
        omega

theorem readMem_below {M : ℕ} (S0 w : ℕ) (y : Fin M → ZMod 2) (k : ℕ) {addr : ℕ}
    (h : addr < S0) : readMem S0 w y k addr = packMem (8 * w) y addr := by
  simp only [readMem]
  rw [if_pos h]

@[simp] theorem readBody_length : readBody.length = 16 := by simp [readBody]

@[simp] theorem readLoopAt_length (base : ℕ) : (readLoopAt base).length = 19 := by
  simp [readLoopAt]

end ReadLoop

section ProgramAt

end ProgramAt

section ReadSpec

/-- The read of coordinate `j` in division form, which is what the machine computes. -/
theorem read_syndrome_div {w : ℕ} (hw : 0 < w) (M : ℕ) (y : Fin M → ZMod 2) (j : ℕ) :
    packMem (8 * w) y (j / 8) / 2 ^ (j % 8 * w) % 2 ^ w = syndromeInt w y j := by
  rw [← Nat.and_two_pow_sub_one_eq_mod, ← Nat.shiftRight_eq_div_pow]
  exact read_syndrome hw M y j

/-- The value the machine ends up with when it reads coordinate `j`: the shift/mask pipeline applied
to the packed payload word. -/
theorem read_value {w : ℕ} {W : ℕ} (hwe : w ≤ W) (hw : 0 < w) (M : ℕ) (y : Fin M → ZMod 2) (j : ℕ) :
    (packMem (8 * w) y (j / 8) / 2 ^ (j % 8 * w)) % 2 ^ W % 2 ^ w = syndromeInt w y j := by
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hwe)]
  exact read_syndrome_div hw M y j

/-- The address the body computes (`j + j + S0`) is the syndrome address. -/
theorem haddr2_of {k S0 W : ℕ} (haddr : (S0 + 2 * k) % 2 ^ W = S0 + 2 * k) :
    (k + k + S0) % 2 ^ W = S0 + 2 * k := by
  have h : k + k + S0 = S0 + 2 * k := by omega
  rw [h, haddr]

/-- **The read-loop body, as a state map.**  One pass reads coordinate `k` out of the payload
(eight fields per word), stores `P_{2k+1}` at `S0 + 2k`, and clears the scratch registers so that
the loop invariant stays a function of the counter alone. -/
theorem readBody_spec (E : RAMEnv) (base S0 w t k : ℕ) (y : Fin (t * w) → ZMod 2) (s : RAMState)
    (hpc : s.pc = base + 2) (hregs : s.regs = Function.update (readState base S0 w t y k).regs r14 1)
    (hmem : s.mem = readMem S0 w y k)
    (hW : E.W = 8 * w) (hwe : w ≤ E.W) (hw : 0 < w)
    (hmul : k * w % 2 ^ E.W = k * w) (hdiv : k * w / (8 * w) % 2 ^ E.W = k / 8)
    (hmod : k * w % (8 * w) % 2 ^ E.W = k % 8 * w) (haddr : (S0 + 2 * k) % 2 ^ E.W = S0 + 2 * k)
    (hk1 : (k + 1) % 2 ^ E.W = k + 1) (hmask : (2 ^ w - 1) % 2 ^ E.W = 2 ^ w - 1)
    (hword : k / 8 < S0) (hpk : packMem (8 * w) y (k / 8) % 2 ^ E.W = packMem (8 * w) y (k / 8)) :
    runBlock readBody E s = { readState base S0 w t y (k + 1) with pc := base + 18 } := by
  have haddr2 : (k + k + S0) % 2 ^ E.W = S0 + 2 * k := haddr2_of haddr
  have hval : ((packMem (8 * w) y (k / 8) / 2 ^ (k % 8 * w)) % 2 ^ E.W % 2 ^ w) % 2 ^ E.W
      = syndromeInt w y k := by
    rw [Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos w))
      (Nat.pow_le_pow_right (by norm_num) hwe))]
    exact read_value hwe hw (t * w) y k
  have hpc' : (runBlock readBody E s).pc = base + 18 := by
    rw [runBlock_pc readBody E s (by simp [readBody]), hpc, readBody_length]
  refine ramState_eq_of _ _ hpc' ?_ ?_
  · funext addr
    show (runBlock readBody E s).mem addr = readMem S0 w y (k + 1) addr
    by_cases h : addr = S0 + 2 * k
    · rw [h, readMem_succ, Function.update_self]
      simp only [readBody, Fin.isValue, List.cons_append, List.nil_append, runBlock_cons, execInstr_mul,
        hregs, readState, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Matrix.cons_val,
        Matrix.cons_val_one, Matrix.cons_val_zero, hmul, hmem, execInstr_div, Function.update_self, hdiv,
        execInstr_mod, hmod, execInstr_load, readMem_below S0 w y k hword, hpk, execInstr_shr,
        Function.update_idem, execInstr_band, Nat.and_two_pow_sub_one_eq_mod, hval, execInstr_add,
        Nat.mod_add_mod, haddr2, execInstr_store, hk1, execInstr_imm, Nat.zero_mod, runBlock_nil]
    · rw [readMem_succ, Function.update_of_ne h]
      simp [readBody, runBlock_cons, runBlock_nil, hregs, hmem, readState, hmul, hdiv, hmod,
        haddr, haddr2, hk1, hmask, readMem_below S0 w y k hword, hpk, hval, Function.update_of_ne h]
  · intro d
    simp only [readBody, Fin.isValue, List.cons_append, List.nil_append, runBlock_cons, execInstr_mul,
      hregs, readState, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Matrix.cons_val,
      Matrix.cons_val_one, Matrix.cons_val_zero, hmul, execInstr_div, Function.update_self, hdiv,
      execInstr_mod, hmod, execInstr_load, execInstr_shr, Function.update_idem, execInstr_band,
      Nat.and_two_pow_sub_one_eq_mod, execInstr_add, Nat.mod_add_mod, execInstr_store, hk1, execInstr_imm,
      Nat.zero_mod, runBlock_nil]
    fin_cases d <;>
      simp only [readBody, Fin.isValue, List.cons_append, List.nil_append, runBlock_cons, execInstr_mul,
        hregs, readState, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Matrix.cons_val,
        Matrix.cons_val_one, Matrix.cons_val_zero, hmul, execInstr_div, Function.update_self, hdiv,
        execInstr_mod, hmod, execInstr_load, execInstr_shr, Function.update_idem, execInstr_band,
        Nat.and_two_pow_sub_one_eq_mod, execInstr_add, Nat.mod_add_mod, execInstr_store, hk1, execInstr_imm,
        Nat.zero_mod, runBlock_nil, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Nat.add_left_cancel_iff]

end ReadSpec

section ReadStmt

theorem readCond_code_length : readCond.code.length = 1 := rfl

/-- `readLoopAt` is exactly the compilation of the statement: `base + 19` is *computed*. -/
theorem readLoopStmt_compile (base : ℕ) : Stmt.compile readLoopStmt base = readLoopAt base := by
  simp [Stmt.compile, Stmt.len, Cond.code, Cond.test, readLoopAt, readBody_length]

theorem readLoopStmt_length (base : ℕ) : (Stmt.compile readLoopStmt base).length = 19 := by
  rw [readLoopStmt_compile, readLoopAt_length]

/-- The three facts a compiled read loop provides, read off `At` elementwise (so that no
`Stmt.compile` unfolding is needed at the use sites). -/
theorem at_loop_read {P : Program} {base : ℕ}
    (hAt : At P base (Stmt.compile readLoopStmt base)) :
    P[base + 1]? = some (iJz r14 (base + 19)) ∧ At P (base + 2) readBody ∧
      P[base + 18]? = some (iJmp base) := by
  have hlen := readLoopStmt_length base
  refine ⟨?_, ?_, ?_⟩
  · have h := hAt 1 (by omega)
    rw [readLoopStmt_compile] at h
    simpa [readLoopAt] using h
  · intro r hr
    have hr16 : r < 16 := by rw [← readBody_length]; exact hr
    have h := hAt (r + 2) (by omega)
    rw [readLoopStmt_compile] at h
    have hlist : (readLoopAt base)[r + 2]? = readBody[r]? := by
      simp only [readLoopAt]
      rw [List.append_assoc]
      rw [List.getElem?_append_right
        (by simp : ([iLt r14 r5 r0, iJz r14 (base + 19)]).length ≤ r + 2)]
      rw [show r + 2 - ([iLt r14 r5 r0, iJz r14 (base + 19)]).length = r from by simp]
      exact List.getElem?_append_left hr
    rw [hlist] at h
    rwa [show base + (r + 2) = base + 2 + r from by omega] at h
  · have h := hAt 18 (by omega)
    rw [readLoopStmt_compile] at h
    simpa [readLoopAt] using h

theorem readState_regs_eq (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    (readState base S0 w t y k).regs
      = ![t, w, S0, 2 ^ w - 1, detSqBase w, k, 0, 0, 1, 0, 0, 0, 0, 0, 0, 8 * w] := rfl

@[simp] theorem readState_r14 (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    (readState base S0 w t y k).regs r14 = 0 := by
  rw [readState_regs_eq]
  simp

/-- A loop-head state with its own program counter written back is unchanged. -/
theorem readState_eta (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    ({ readState base S0 w t y k with pc := base } : RAMState) = readState base S0 w t y k := by
  refine ramState_eq_of _ _ ?_ ?_ ?_
  · simp
  · simp
  · intro d; simp

/-- The loop test holds exactly when the counter is below `t`. -/
theorem readCond_eval (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    readCond.eval (readState base S0 w t y k) ↔ k < t := by
  simp [Cond.eval, readState_regs_eq]

/-- At the exit the test fails. -/
theorem readCond_false (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) :
    ¬ readCond.eval (readState base S0 w t y t) := by
  rw [readCond_eval]
  exact lt_irrefl t

/-- A constant sum over a range. -/
theorem sum_range_const_mul (t c : ℕ) : (∑ j ∈ Finset.range t, c) = c * t := by
  induction t with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- Overwriting a register whose value is already `0` changes nothing. -/
theorem update_zero_eq (s : RAMState) (h : s.regs r14 = 0) :
    Function.update s.regs r14 0 = s.regs := by
  rw [← h]
  exact Function.update_eq_self _ _

/-- Running the test materialises `r14 = (j < t)` and advances to the body. -/
theorem runBlock_readCond (E : RAMEnv) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    runBlock readCond.code E (readState base S0 w t y k) = { pc := base + 1, regs := Function.update (readState base S0 w t y k).regs r14 ((if k < t then 1 else 0) % 2 ^ E.W), mem := readMem S0 w y k } := by
  have hcode : readCond.code = [iLt r14 r5 r0] := rfl
  rw [hcode, runBlock_cons, runBlock_nil, execInstr_lt]
  dsimp only [readState]
  try rfl

/-- The same with the test known to hold: `r14` becomes `1`. -/
theorem runBlock_readCond_of_lt (E : RAMEnv) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) (k : ℕ)
    (hW : 1 < 2 ^ E.W) (hk : k < t) :
    runBlock readCond.code E (readState base S0 w t y k) = { readState base S0 w t y k with pc := base + 1, regs := Function.update (readState base S0 w t y k).regs r14 1 } := by
  rw [runBlock_readCond, if_pos hk, Nat.mod_eq_of_lt hW]
  try rfl

/-- The same with the test known to fail: `r14` becomes `0`. -/
theorem runBlock_readCond_of_ge (E : RAMEnv) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) (k : ℕ)
    (hk : ¬ k < t) :
    runBlock readCond.code E (readState base S0 w t y k) = { readState base S0 w t y k with pc := base + 1, regs := Function.update (readState base S0 w t y k).regs r14 0 } := by
  rw [runBlock_readCond, if_neg hk, Nat.zero_mod]
  try rfl

/-- At the exit, the test run leaves the state alone apart from the program counter. -/
theorem runBlock_readCond_exit (E : RAMEnv) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) :
    runBlock readCond.code E (readState base S0 w t y t) = { readState base S0 w t y t with pc := base + 1 } := by
  have h0 : (readState base S0 w t y t).regs r14 = 0 := readState_r14 base S0 w t y t
  have h := runBlock_readCond_of_ge E base S0 w t y t (lt_irrefl t)
  rw [update_zero_eq _ h0] at h
  refine ramState_eq_of _ _ ?_ ?_ ?_
  · rw [h]
  · rw [h]
  · intro d
    rw [h]

/-- The body entry state, in the shape the loop rule produces. -/
theorem readBodyIn_eq (E : RAMEnv) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) (k : ℕ)
    (hW : 1 < 2 ^ E.W) (hk : k < t) :
    ({ runBlock readCond.code E (readState base S0 w t y k) with pc := base + readCond.code.length + 1 } : RAMState) = readBodyIn base S0 w t y k := by
  have hcl : readCond.code.length = 1 := readCond_code_length
  have hrun := runBlock_readCond_of_lt E base S0 w t y k hW hk
  refine ramState_eq_of _ _ ?_ ?_ ?_
  · simp only [readBodyIn]
    rw [hcl]
  · simp only [readBodyIn]
    rw [hrun]
    simp
  · intro d
    simp only [readBodyIn]
    rw [hrun]

/-- The body of the read loop, as a `Sem` run: from the body entry to the `jmp`, in 16 steps. -/
theorem readBody_sem (P : Program) (E : RAMEnv) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2)
    (k : ℕ) (hAt : At P (base + 2) readBody)
    (hW : 1 < 2 ^ E.W) (hW8 : E.W = 8 * w) (hwe : w ≤ E.W) (hw : 0 < w)
    (hmul : k * w % 2 ^ E.W = k * w) (hdiv : k * w / (8 * w) % 2 ^ E.W = k / 8)
    (hmod : k * w % (8 * w) % 2 ^ E.W = k % 8 * w) (haddr : (S0 + 2 * k) % 2 ^ E.W = S0 + 2 * k)
    (hk1 : (k + 1) % 2 ^ E.W = k + 1) (hmask : (2 ^ w - 1) % 2 ^ E.W = 2 ^ w - 1)
    (hword : k / 8 < S0)
    (hpk : packMem (8 * w) y (k / 8) % 2 ^ E.W = packMem (8 * w) y (k / 8)) :
    Sem P E (base + 2) (base + 18) (readBodyIn base S0 w t y k)
      (fun c s' => c = 16 ∧ s' = { readState base S0 w t y (k + 1) with pc := base + 18 }) := by
  refine Sem.mono (Sem.block P E (base + 2) readBody (readBodyIn base S0 w t y k) hAt
    (by simp [readBody]) rfl) ?_
  intro c s' hQ
  obtain ⟨hc, hs⟩ := hQ
  refine ⟨?_, ?_⟩
  · rw [hc, readBody_length]
  · rw [hs]
    exact readBody_spec E base S0 w t k y (readBodyIn base S0 w t y k) rfl rfl rfl hW8 hwe hw hmul
      hdiv hmod haddr hk1 hmask hword hpk

/-- The iteration *after* the test: from the body entry back to the loop head, in 17 steps
(`16` for the body, `1` for the `jmp`).  This is what `Sem.loop` consumes. -/
theorem readBodyIter (P : Program) (E : RAMEnv) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2)
    (k : ℕ) (hAt : At P base (Stmt.compile readLoopStmt base)) (hW : 1 < 2 ^ E.W)
    (hW8 : E.W = 8 * w) (hwe : w ≤ E.W) (hw : 0 < w) (hk : k < t)
    (hmul : k * w % 2 ^ E.W = k * w) (hdiv : k * w / (8 * w) % 2 ^ E.W = k / 8)
    (hmod : k * w % (8 * w) % 2 ^ E.W = k % 8 * w) (haddr : (S0 + 2 * k) % 2 ^ E.W = S0 + 2 * k)
    (hk1 : (k + 1) % 2 ^ E.W = k + 1) (hmask : (2 ^ w - 1) % 2 ^ E.W = 2 ^ w - 1)
    (hword : k / 8 < S0)
    (hpk : packMem (8 * w) y (k / 8) % 2 ^ E.W = packMem (8 * w) y (k / 8)) :
    Sem P E (base + readCond.code.length + 1) base ({ runBlock readCond.code E (readState base S0 w t y k) with pc := base + readCond.code.length + 1 } : RAMState)
      (fun c s' => c = 17 ∧ s' = readState base S0 w t y (k + 1)) := by
  obtain ⟨hjz, hbodyAt, hjmp⟩ := at_loop_read hAt
  have hbody := readBody_sem P E base S0 w t y k hbodyAt hW hW8 hwe hw hmul hdiv hmod haddr hk1
    hmask hword hpk
  rw [readBodyIn_eq E base S0 w t y k hW hk]
  refine Sem.jmp_append (hAt := hjmp) ?_
  refine Sem.mono hbody ?_
  intro c s' hQ
  obtain ⟨hc, hs⟩ := hQ
  refine ⟨by omega, ?_⟩
  rw [hs]
  exact readState_eta base S0 w t y (k + 1)

/-- The exit state of the read loop: the test run only moves the program counter. -/
theorem readLoop_exit_state (E : RAMEnv) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) :
    ({ runBlock readCond.code E (readState base S0 w t y t) with pc := base + readCond.code.length + (Stmt.code readBody).len + 2 } : RAMState) = { readState base S0 w t y t with pc := base + 19 } := by
  have hcl : readCond.code.length = 1 := readCond_code_length
  have hbl : (Stmt.code readBody).len = 16 := readBody_length
  have hrun := runBlock_readCond_exit E base S0 w t y
  refine ramState_eq_of _ _ ?_ ?_ ?_
  · simp only [hcl, hbl]
  · simp only [hrun]
  · intro d
    simp only [hrun]

/-- **The read loop.**  One `Sem.loop` call: `t` iterations of `2 + 17` steps, then the failing
test (`2` more).  The state invariant is a function of the counter alone. -/
theorem readLoop_spec (P : Program) (E : RAMEnv) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2)
    (hAt : At P base (Stmt.compile readLoopStmt base)) (hW : 1 < 2 ^ E.W) (hW8 : E.W = 8 * w)
    (hwe : w ≤ E.W) (hw : 0 < w)
    (hmul : ∀ k < t, k * w % 2 ^ E.W = k * w)
    (hdiv : ∀ k < t, k * w / (8 * w) % 2 ^ E.W = k / 8)
    (hmod : ∀ k < t, k * w % (8 * w) % 2 ^ E.W = k % 8 * w)
    (haddr : ∀ k < t, (S0 + 2 * k) % 2 ^ E.W = S0 + 2 * k)
    (hk1 : ∀ k < t, (k + 1) % 2 ^ E.W = k + 1)
    (hmask : (2 ^ w - 1) % 2 ^ E.W = 2 ^ w - 1)
    (hword : ∀ k < t, k / 8 < S0)
    (hpk : ∀ k < t, packMem (8 * w) y (k / 8) % 2 ^ E.W = packMem (8 * w) y (k / 8)) :
    Sem P E base (base + 19) (readState base S0 w t y 0)
      (fun c s' => c ≤ 19 * t + 2 ∧ s' = { readState base S0 w t y t with pc := base + 19 }) := by
  have hloop := Sem.loop P E base readCond (Stmt.code readBody) hAt hW t
    (fun j => readState base S0 w t y j) (fun _ => 17)
    (fun j => rfl)
    (fun j hj => (readCond_eval base S0 w t y j).mpr hj)
    (readCond_false base S0 w t y)
    (fun j hj => readBodyIter P E base S0 w t y j hAt hW hW8 hwe hw hj (hmul j hj) (hdiv j hj)
      (hmod j hj) (haddr j hj) (hk1 j hj) hmask (hword j hj) (hpk j hj))
  have h19 : ((readCond.code.length + 1) + 17) = 19 := by
    rw [readCond_code_length]
  have hsum19 : (∑ j ∈ Finset.range t, (19 : ℕ)) = 19 * t := sum_range_const_mul t 19
  have hsum : (∑ j ∈ Finset.range t, ((readCond.code.length + 1) + 17)) = 19 * t := by
    rw [← hsum19]
    exact Finset.sum_congr rfl (fun j _ => h19)
  refine Sem.mono hloop ?_
  intro c s' hQ
  obtain ⟨hle, hs⟩ := hQ
  refine ⟨?_, ?_⟩
  · rw [hsum] at hle
    rw [readCond_code_length] at hle
    omega
  · rw [hs]
    exact readLoop_exit_state E base S0 w t y

end ReadStmt

section Bounds

/-- `k * w` and the syndrome addresses of the first `t` coordinates fit in a word. `as in the
paper`: the payload has `tw` bits and `W = 8w`, so every index the read loop forms is below `2^W`. -/
theorem mul_lt_two_pow_eight {w N k : ℕ} (hw1 : 1 ≤ w) (hNw : N < 2 ^ w) (hkN : k < N) :
    k * w < 2 ^ (8 * w) := by
  have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
  have hk2 : k ≤ 2 ^ w - 1 := by omega
  have hw2 : w ≤ 2 ^ w - 1 := by
    have := Nat.lt_two_pow_self (n := w)
    omega
  have h1 : k * w ≤ (2 ^ w - 1) * w := Nat.mul_le_mul_right w hk2
  have h2 : (2 ^ w - 1) * w ≤ (2 ^ w - 1) * (2 ^ w - 1) := Nat.mul_le_mul_left _ hw2
  have h4 : (2 ^ w - 1) < 2 ^ w := by omega
  have h3 : (2 ^ w - 1) * (2 ^ w - 1) < 2 ^ w * 2 ^ w := by
    calc (2 ^ w - 1) * (2 ^ w - 1) < 2 ^ w * (2 ^ w - 1) :=
          Nat.mul_lt_mul_of_pos_right h4 (by omega)
      _ < 2 ^ w * 2 ^ w := Nat.mul_lt_mul_of_pos_left h4 hpos
  have h5 : 2 ^ w * 2 ^ w = 2 ^ (2 * w) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have h6 : 2 ^ (2 * w) ≤ 2 ^ (8 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- The syndrome address `S0 + 2k` of coordinate `k < t` fits in a word. -/
theorem addr_lt_two_pow_eight {w t k S0 : ℕ} (hw1 : 1 ≤ w) (hNw : t < 2 ^ w)
    (hS0 : S0 ≤ t) (hk : k < t) : S0 + 2 * k < 2 ^ (8 * w) := by
  have hk2 : 2 * k < 2 ^ (w + 1) := by
    have h : 2 * k < 2 * 2 ^ w := by omega
    calc 2 * k < 2 * 2 ^ w := h
      _ = 2 ^ (w + 1) := by rw [Nat.pow_succ]; ring
  have h1 : S0 + 2 * k < 2 ^ w + 2 ^ (w + 1) := by omega
  have h2 : (2 : ℕ) ^ w + 2 ^ (w + 1) ≤ 2 ^ (w + 2) := by
    have e1 : (2 : ℕ) ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ]; ring
    have e2 : (2 : ℕ) ^ (w + 2) = 4 * 2 ^ w := by
      rw [show w + 2 = w + 1 + 1 from rfl, Nat.pow_succ, e1]
      ring
    omega
  have h3 : (2 : ℕ) ^ (w + 2) ≤ 2 ^ (8 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- The address `S0 + 2k + 1` the expansion loop stores at fits in a word. -/
theorem addr_succ_lt_two_pow_eight {w t k S0 : ℕ} (hw1 : 1 ≤ w) (hNw : t < 2 ^ w)
    (hS0 : S0 ≤ t) (hk : k < t) : S0 + 2 * k + 1 < 2 ^ (8 * w) := by
  have hk2 : 2 * k < 2 ^ (w + 1) := by
    have h : 2 * k < 2 * 2 ^ w := by omega
    calc 2 * k < 2 * 2 ^ w := h
      _ = 2 ^ (w + 1) := by rw [Nat.pow_succ]; ring
  have h1 : S0 + 2 * k + 1 < 2 ^ w + 2 ^ (w + 1) + 1 := by omega
  have h2 : (2 : ℕ) ^ w + 2 ^ (w + 1) + 1 ≤ 2 ^ (w + 2) := by
    have e1 : (2 : ℕ) ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ]; ring
    have e2 : (2 : ℕ) ^ (w + 2) = 4 * 2 ^ w := by
      rw [show w + 2 = w + 1 + 1 from rfl, Nat.pow_succ, e1]
      ring
    have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
    omega
  have h3 : (2 : ℕ) ^ (w + 2) ≤ 2 ^ (8 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- `wordsOf (8w) (tw) ≤ t`: the payload never needs more words than it has syndrome coordinates. -/
theorem wordsOf_le (w t : ℕ) (hw1 : 1 ≤ w) : wordsOf (8 * w) (t * w) ≤ t := by
  rw [wordsOf_eight w t (by omega)]
  omega

/-- The squaring table of `det` starts inside a word: `detSqBase w = 64 + 2^{2w} < 2^{8w}`. -/
theorem detSqBase_lt {w : ℕ} (hw1 : 1 ≤ w) : detSqBase w < 2 ^ (8 * w) := by
  by_cases hw4 : w ≤ 3
  · unfold detSqBase detMulBase
    interval_cases w <;> norm_num
  · have hw4' : 3 < w := by omega
    have h3 : (64 : ℕ) ≤ 2 ^ (2 * w) := by
      have h : (2 : ℕ) ^ 6 ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
      calc (64 : ℕ) = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ (2 * w) := h
    have h5 : (2 : ℕ) ^ (2 * w) + 2 ^ (2 * w) = 2 ^ (2 * w + 1) := by
      rw [Nat.pow_succ]
      ring
    have h6 : (2 : ℕ) ^ (2 * w + 1) < 2 ^ (8 * w) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h7 : 64 + 2 ^ (2 * w) ≤ 2 ^ (2 * w) + 2 ^ (2 * w) := by omega
    rw [detSqBase, detMulBase]
    calc 64 + 2 ^ (2 * w) ≤ 2 ^ (2 * w) + 2 ^ (2 * w) := h7
      _ = 2 ^ (2 * w + 1) := h5
      _ < 2 ^ (8 * w) := h6

/-- The whole table ends inside a word: `detInvBase w < 2^{8w}`. -/
theorem detInvBase_lt {w : ℕ} (hw1 : 1 ≤ w) : detInvBase w < 2 ^ (8 * w) := by
  by_cases hw3 : w ≤ 2
  · unfold detInvBase detSqBase detMulBase
    interval_cases w <;> norm_num
  · have h3 : (64 : ℕ) ≤ 2 ^ (2 * w) := by
      have h : (2 : ℕ) ^ 6 ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
      calc (64 : ℕ) = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ (2 * w) := h
    have hA : (2 : ℕ) ^ (2 * w) + 2 ^ (2 * w) = 2 ^ (2 * w + 1) := by
      rw [Nat.pow_succ]
      ring
    have hB : (2 : ℕ) ^ (2 * w + 1) + 2 ^ (2 * w + 1) = 2 ^ (2 * w + 2) := by
      rw [Nat.pow_succ]
      ring
    have h1 : detInvBase w ≤ 2 ^ (2 * w + 2) := by
      unfold detInvBase detSqBase detMulBase
      omega
    have h2 : (2 : ℕ) ^ (2 * w + 2) < 2 ^ (8 * w) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

/-- A squared table entry fits in a word: `detSqBase w + a < 2^{8w}` for every `w`-bit `a`. -/
theorem detSqBase_add_lt {w a : ℕ} (hw1 : 1 ≤ w) (ha : a < 2 ^ w) :
    detSqBase w + a < 2 ^ (8 * w) := by
  have hwle : (2 : ℕ) ^ w ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h1 : detSqBase w + a < detInvBase w := by
    unfold detInvBase
    omega
  exact lt_trans h1 (detInvBase_lt hw1)

end Bounds

section Prologue

@[simp] theorem paramBody_length : paramBody.length = 14 := by simp [paramBody]

/-- **The prologue, as a state map.**  It reads the six parameters it needs and nothing else; the
memory is untouched. -/
theorem paramBody_spec (E : RAMEnv) (N t w S0 : ℕ) (y : Fin (t * w) → ZMod 2)
    (hS0 : S0 = wordsOf (8 * w) (t * w)) (hW : E.W = 8 * w) (hw1 : 1 ≤ w)
    (h0 : E.det 0 % 2 ^ E.W = t) (h1 : E.det 1 % 2 ^ E.W = w) (h4 : E.det 4 % 2 ^ E.W = S0)
    (h5 : E.det 5 % 2 ^ E.W = 2 ^ w - 1) (h6 : E.det 6 % 2 ^ E.W = detSqBase w)
    (h12 : E.det 12 % 2 ^ E.W = 8 * w) (h1W : (1 : ℕ) % 2 ^ E.W = 1) :
    runBlock paramBody E (decoderStart (8 * w) y []) = readState paramBody.length S0 w t y 0 := by
  have hmem : (decoderStart (8 * w) y []).mem = readMem S0 w y 0 := by
    funext addr
    rw [show (decoderStart (8 * w) y []).mem = hintMem (8 * w) y ([] : List ℕ) from rfl]
    simp only [readMem_zero, hintMem, hS0, List.getD_nil]
  have hpc' : (runBlock paramBody E (decoderStart (8 * w) y [])).pc = paramBody.length := by
    rw [runBlock_pc paramBody E _ (by simp [paramBody])]
    simp [decoderStart, initState, paramBody_length]
  have hbig : 16 ≤ 2 ^ E.W := by
    rw [hW]
    have h2 : 2 ^ 8 ≤ 2 ^ (8 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h4m : (4 : ℕ) % 2 ^ E.W = 4 := Nat.mod_eq_of_lt (by omega)
  have h5m : (5 : ℕ) % 2 ^ E.W = 5 := Nat.mod_eq_of_lt (by omega)
  have h6m : (6 : ℕ) % 2 ^ E.W = 6 := Nat.mod_eq_of_lt (by omega)
  have h12m : (12 : ℕ) % 2 ^ E.W = 12 := Nat.mod_eq_of_lt (by omega)
  refine ramState_eq_of _ _ hpc' ?_ ?_
  · funext addr
    simp only [paramBody, Fin.isValue, List.cons_append, List.nil_append, runBlock_cons, execInstr_imm,
      Nat.zero_mod, hmem, execInstr_qDet, Function.update_self, runBlock_nil, readState, List.length_cons,
      List.length_nil, zero_add, Nat.reduceAdd]
  · intro d
    simp only [paramBody, readState, h0, h1, h4, h5, h6, h12, h1W, h4m, h5m, h6m, h12m,
      decoderStart, initState, runBlock_cons, runBlock_nil, execInstr_imm, execInstr_qDet,
      Function.update_idem]
    fin_cases d <;>
      simp [paramBody, readState, h0, h1, h4, h5, h6, h12, h1W, h4m, h5m, h6m, h12m,
        decoderStart, initState, runBlock_cons, runBlock_nil]

end Prologue

section ReadAssembly

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

end ReadAssembly

section Expand

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

/-- The successor step, stated with an explicit `Nat.succ` so that the generated `match`
reduces during elaboration. -/
theorem eSeq_succ {w : ℕ} (b : Module.Basis (Fin w) (ZMod 2) F) {M : ℕ} (y : Fin M → ZMod 2) (n : ℕ) :
    eSeq b y (Nat.succ n)
      = if Even (Nat.succ n) then payloadField b y (Nat.succ n / 2)
        else (eSeq b y (Nat.succ n / 2)) ^ 2 := by
  rw [eSeq.eq_def]

theorem eSeq_even {w : ℕ} (b : Module.Basis (Fin w) (ZMod 2) F) {M : ℕ} (y : Fin M → ZMod 2) (k : ℕ) :
    eSeq b y (2 * k) = payloadField b y k := by
  cases k with
  | zero => rw [eSeq.eq_def]
  | succ j =>
      have harg : 2 * (j + 1) = Nat.succ (2 * j + 1) := by omega
      rw [harg, eSeq_succ,
        if_pos (show Even (Nat.succ (2 * j + 1)) from ⟨j + 1, by omega⟩)]
      congr 1
      show (2 * j + 2) / 2 = j + 1
      omega

theorem eSeq_odd {w : ℕ} (b : Module.Basis (Fin w) (ZMod 2) F) {M : ℕ} (y : Fin M → ZMod 2) (k : ℕ) :
    eSeq b y (2 * k + 1) = (eSeq b y k) ^ 2 := by
  have harg : 2 * k + 1 = Nat.succ (2 * k) := by omega
  rw [harg, eSeq_succ,
    if_neg (show ¬ Even (Nat.succ (2 * k)) from by rintro ⟨r, hr⟩; omega)]
  rw [show Nat.succ (2 * k) / 2 = k from by
    show (2 * k + 1) / 2 = k
    omega]

/-- The squaring table, applied to a reading of `eSeq k`, returns `eSeq (2k+1)`. -/
theorem sqTab_enc {w : ℕ} (b : Module.Basis (Fin w) (ZMod 2) F) {M : ℕ} (y : Fin M → ZMod 2) (k : ℕ) :
    sqTab b (enc b (eSeq b y k)) = enc b (eSeq b y (2 * k + 1)) := by
  show enc b ((dec b (enc b (eSeq b y k))) ^ 2) = enc b (eSeq b y (2 * k + 1))
  rw [dec_enc, ← eSeq_odd]

/-- **The read loop's output is the expansion's input.** -/
theorem expandMem_zero {w M : ℕ} (S0 : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin M → ZMod 2) (t : ℕ) :
    expandMem S0 b y t 0 = readMem S0 w y t := by
  funext addr
  simp only [expandMem, readMem]
  by_cases h : addr < S0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    by_cases he : (addr - S0) % 2 = 0
    · rw [if_pos he]
      by_cases ht : (addr - S0) / 2 < t
      · rw [if_pos ht, if_pos ⟨he, ht⟩]
      · rw [if_neg ht, if_neg (fun hh => ht hh.2)]
    · rw [if_neg he]
      rw [if_neg (fun hh : (addr - S0) % 2 = 0 ∧ (addr - S0) / 2 < t => he hh.1)]
      rw [if_neg (Nat.not_lt_zero _)]

/-- **One expansion step**: the only memory cell that changes is `S0 + 2k + 1`. -/
theorem expandMem_succ {w M : ℕ} (S0 : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin M → ZMod 2) (t k : ℕ) :
    expandMem S0 b y t (k + 1)
      = Function.update (expandMem S0 b y t k) (S0 + 2 * k + 1) (enc b (eSeq b y (2 * k + 1))) := by
  funext addr
  by_cases h : addr = S0 + 2 * k + 1
  · subst h
    rw [Function.update_self]
    simp only [expandMem]
    rw [if_neg (by omega : ¬ S0 + 2 * k + 1 < S0)]
    rw [show S0 + 2 * k + 1 - S0 = 2 * k + 1 from by omega]
    rw [if_neg (by omega : ¬ (2 * k + 1) % 2 = 0)]
    rw [if_pos (by omega : (2 * k + 1) / 2 < k + 1)]
    rw [show 2 * ((2 * k + 1) / 2) + 1 = 2 * k + 1 from by omega]
  · rw [Function.update_of_ne h]
    simp only [expandMem]
    by_cases hs : addr < S0
    · rw [if_pos hs, if_pos hs]
    · rw [if_neg hs, if_neg hs]
      by_cases he : (addr - S0) % 2 = 0
      · rw [if_pos he, if_pos he]
      · rw [if_neg he, if_neg he]
        have hmod2 : (addr - S0) % 2 < 2 := Nat.mod_lt _ (by norm_num)
        have hne : (addr - S0) / 2 ≠ k := by
          intro hqk
          have h2 := Nat.div_add_mod (addr - S0) 2
          omega
        by_cases hq : (addr - S0) / 2 < k
        · rw [if_pos (by omega : (addr - S0) / 2 < k + 1), if_pos hq]
        · rw [if_neg (by omega : ¬ (addr - S0) / 2 < k + 1), if_neg hq]

/-- **The source slot is already final**: `mem[S0 + a] = enc (eSeq a)` while the loop runs. -/
theorem expandMem_get {w M : ℕ} (S0 : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin M → ZMod 2) (t k a : ℕ) (ht : a / 2 < t) (hk : a % 2 = 1 → a / 2 < k) :
    expandMem S0 b y t k (S0 + a) = enc b (eSeq b y a) := by
  simp only [expandMem]
  rw [if_neg (by omega : ¬ S0 + a < S0)]
  rw [show S0 + a - S0 = a from by omega]
  have hmod2 : a % 2 < 2 := Nat.mod_lt _ (by norm_num)
  by_cases he : a % 2 = 0
  · rw [if_pos he, if_pos ht]
    conv_rhs => rw [show a = 2 * (a / 2) from by omega]
    rw [eSeq_even]
    exact (enc_payloadField b y (a / 2)).symm
  · rw [if_neg he, if_pos (hk (by omega))]
    conv_rhs => rw [show a = 2 * (a / 2) + 1 from by omega]

/-- The slot the expansion loop reads: `e[k]`. -/
theorem expandMem_src {w M : ℕ} (S0 : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin M → ZMod 2) (t k : ℕ) (hk : k < t) :
    expandMem S0 b y t k (S0 + k) = enc b (eSeq b y k) :=
  expandMem_get S0 b y t k k (by omega) (fun _ => by omega)

/-- **The array is complete**: after `t` iterations every slot `S0 + a`, `a < 2t`, holds the
integer spelling of `eSeq a`. -/
theorem expandMem_complete {w M : ℕ} (S0 : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin M → ZMod 2) (t : ℕ) {a : ℕ} (ha : a < 2 * t) :
    expandMem S0 b y t t (S0 + a) = enc b (eSeq b y a) :=
  expandMem_get S0 b y t t a (by omega) (fun _ => by omega)

@[simp] theorem expandBody_length : expandBody.length = 16 := by simp [expandBody]

@[simp] theorem expandLoopAt_length (base : ℕ) : (expandLoopAt base).length = 19 := by
  simp [expandLoopAt]

theorem expandLoopStmt_compile (base : ℕ) : Stmt.compile expandLoopStmt base = expandLoopAt base := by
  simp [Stmt.compile, Stmt.len, Cond.code, Cond.test, expandLoopAt, expandBody_length]

theorem expandLoopStmt_length (base : ℕ) : (Stmt.compile expandLoopStmt base).length = 19 := by
  rw [expandLoopStmt_compile, expandLoopAt_length]

/-- The three facts a compiled expansion loop provides. -/
theorem at_loop_expand {P : Program} {base : ℕ}
    (hAt : At P base (Stmt.compile expandLoopStmt base)) :
    P[base + 1]? = some (iJz r14 (base + 19)) ∧ At P (base + 2) expandBody ∧
      P[base + 18]? = some (iJmp base) := by
  have hlen := expandLoopStmt_length base
  refine ⟨?_, ?_, ?_⟩
  · have h := hAt 1 (by omega)
    rw [expandLoopStmt_compile] at h
    simpa [expandLoopAt] using h
  · intro r hr
    have hr16 : r < 16 := by rw [← expandBody_length]; exact hr
    have h := hAt (r + 2) (by omega)
    rw [expandLoopStmt_compile] at h
    have hlist : (expandLoopAt base)[r + 2]? = expandBody[r]? := by
      simp only [expandLoopAt]
      rw [List.append_assoc]
      rw [List.getElem?_append_right
        (by simp : ([iLt r14 r5 r0, iJz r14 (base + 19)]).length ≤ r + 2)]
      rw [show r + 2 - ([iLt r14 r5 r0, iJz r14 (base + 19)]).length = r from by simp]
      exact List.getElem?_append_left hr
    rw [hlist] at h
    rwa [show base + (r + 2) = base + 2 + r from by omega] at h
  · have h := hAt 18 (by omega)
    rw [expandLoopStmt_compile] at h
    simpa [expandLoopAt] using h

theorem expandState_regs_eq (base S0 w t : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    (expandState base S0 w t b y k).regs
      = ![t, w, S0, 2 ^ w - 1, detSqBase w, k, 0, 0, 1, 0, 0, 0, 0, 0, 0, 8 * w] := rfl

@[simp] theorem expandState_r14 (base S0 w t : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin (t * w) → ZMod 2) (k : ℕ) : (expandState base S0 w t b y k).regs r14 = 0 := by
  rw [expandState_regs_eq]
  simp

/-- A loop-head state with its own program counter written back is unchanged. -/
theorem expandState_eta (base S0 w t : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    ({ expandState base S0 w t b y k with pc := base } : RAMState) = expandState base S0 w t b y k := by
  refine ramState_eq_of _ _ ?_ ?_ ?_
  · simp
  · simp
  · intro d; simp

/-- The loop test for the expansion loop. -/
theorem expandCond_eval (base S0 w t : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    readCond.eval (expandState base S0 w t b y k) ↔ k < t := by
  simp [Cond.eval, expandState_regs_eq]

theorem expandCond_false (base S0 w t : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin (t * w) → ZMod 2) : ¬ readCond.eval (expandState base S0 w t b y t) := by
  rw [expandCond_eval]
  exact lt_irrefl t

/-- Running the expansion test. -/
theorem runBlock_expandCond (E : RAMEnv) (base S0 w t : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    runBlock readCond.code E (expandState base S0 w t b y k) = { pc := base + 1, regs := Function.update (expandState base S0 w t b y k).regs r14 ((if k < t then 1 else 0) % 2 ^ E.W), mem := expandMem S0 b y t k } := by
  have hcode : readCond.code = [iLt r14 r5 r0] := rfl
  rw [hcode, runBlock_cons, runBlock_nil, execInstr_lt]
  dsimp only [expandState]
  try rfl

theorem runBlock_expandCond_of_lt (E : RAMEnv) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) (k : ℕ)
    (hW : 1 < 2 ^ E.W) (hk : k < t) :
    runBlock readCond.code E (expandState base S0 w t b y k) = { expandState base S0 w t b y k with pc := base + 1, regs := Function.update (expandState base S0 w t b y k).regs r14 1 } := by
  rw [runBlock_expandCond, if_pos hk, Nat.mod_eq_of_lt hW]
  try rfl

theorem runBlock_expandCond_of_ge (E : RAMEnv) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) (k : ℕ)
    (hk : ¬ k < t) :
    runBlock readCond.code E (expandState base S0 w t b y k) = { expandState base S0 w t b y k with pc := base + 1, regs := Function.update (expandState base S0 w t b y k).regs r14 0 } := by
  rw [runBlock_expandCond, if_neg hk, Nat.zero_mod]
  try rfl

theorem runBlock_expandCond_exit (E : RAMEnv) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) :
    runBlock readCond.code E (expandState base S0 w t b y t) = { expandState base S0 w t b y t with pc := base + 1 } := by
  have h0 : (expandState base S0 w t b y t).regs r14 = 0 := expandState_r14 base S0 w t b y t
  have h := runBlock_expandCond_of_ge E base S0 w t b y t (lt_irrefl t)
  rw [update_zero_eq _ h0] at h
  refine ramState_eq_of _ _ ?_ ?_ ?_
  · rw [h]
  · rw [h]
  · intro d
    rw [h]

theorem expandBodyIn_eq (E : RAMEnv) (base S0 w t : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin (t * w) → ZMod 2) (k : ℕ) (hW : 1 < 2 ^ E.W) (hk : k < t) :
    ({ runBlock readCond.code E (expandState base S0 w t b y k) with pc := base + readCond.code.length + 1 } : RAMState) = expandBodyIn base S0 w t b y k := by
  have hcl : readCond.code.length = 1 := readCond_code_length
  have hrun := runBlock_expandCond_of_lt E base S0 w t b y k hW hk
  refine ramState_eq_of _ _ ?_ ?_ ?_
  · simp only [expandBodyIn]
    rw [hcl]
  · simp only [expandBodyIn]
    rw [hrun]
    simp
  · intro d
    simp only [expandBodyIn]
    rw [hrun]

/-- **The expansion body, as a state map.**  It reads `e[k]`, squares it through the table at
`detSqBase`, stores the result at `S0 + 2k + 1`, advances the counter and clears the scratch
registers. -/
theorem expandBody_spec (E : RAMEnv) (base S0 w t k : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin (t * w) → ZMod 2) (s : RAMState)
    (hpc : s.pc = base + 2)
    (hregs : s.regs = Function.update (expandState base S0 w t b y k).regs r14 1)
    (hmem : s.mem = expandMem S0 b y t k)
    (hsrc : (S0 + k) % 2 ^ E.W = S0 + k)
    (hsrcval : expandMem S0 b y t k (S0 + k) = enc b (eSeq b y k))
    (hld : enc b (eSeq b y k) % 2 ^ E.W = enc b (eSeq b y k))
    (hsq : (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = detSqBase w + enc b (eSeq b y k))
    (htab : E.det (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = sqTab b (enc b (eSeq b y k)))
    (hval : sqTab b (enc b (eSeq b y k)) = enc b (eSeq b y (2 * k + 1)))
    (hkk : (k + k) % 2 ^ E.W = k + k)
    (hkkS0 : (k + k + S0) % 2 ^ E.W = S0 + 2 * k)
    (haddr : (S0 + 2 * k + 1) % 2 ^ E.W = S0 + 2 * k + 1)
    (hk1 : (k + 1) % 2 ^ E.W = k + 1) :
    runBlock expandBody E s = { expandState base S0 w t b y (k + 1) with pc := base + 18 } := by
  have hpc' : (runBlock expandBody E s).pc = base + 18 := by
    rw [runBlock_pc expandBody E s (by simp [expandBody]), hpc, expandBody_length]
  refine ramState_eq_of _ _ hpc' ?_ ?_
  · funext addr
    show (runBlock expandBody E s).mem addr = expandMem S0 b y t (k + 1) addr
    by_cases h : addr = S0 + 2 * k + 1
    · rw [h, expandMem_succ, Function.update_self]
      simp only [expandBody, Fin.isValue, List.cons_append, List.nil_append, runBlock_cons, execInstr_add,
        hregs, expandState, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Matrix.cons_val,
        hsrc, hmem, execInstr_load, Function.update_self, hsrcval, hld, hsq, execInstr_qDet, htab, hval, hkk,
        hkkS0, Function.update_idem, haddr, execInstr_store, hk1, execInstr_imm, Nat.zero_mod, runBlock_nil]
    · rw [expandMem_succ, Function.update_of_ne h]
      simp only [expandBody, Fin.isValue, List.cons_append, List.nil_append, runBlock_cons, execInstr_add,
        hregs, expandState, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Matrix.cons_val,
        hsrc, hmem, execInstr_load, Function.update_self, hsrcval, hld, hsq, execInstr_qDet, htab, hval, hkk,
        hkkS0, Function.update_idem, haddr, execInstr_store, hk1, execInstr_imm, Nat.zero_mod, runBlock_nil,
        Function.update_of_ne h]
  · intro d
    simp only [expandBody, Fin.isValue, List.cons_append, List.nil_append, runBlock_cons, execInstr_add,
      hregs, expandState, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Matrix.cons_val,
      hsrc, execInstr_load, Function.update_self, Nat.add_mod_mod, execInstr_qDet, hkk, hkkS0,
      Function.update_idem, haddr, execInstr_store, hk1, execInstr_imm, Nat.zero_mod, runBlock_nil]
    fin_cases d <;>
      simp only [expandBody, Fin.isValue, List.cons_append, List.nil_append, runBlock_cons, execInstr_add,
        hregs, expandState, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Matrix.cons_val,
        hsrc, execInstr_load, Function.update_self, Nat.add_mod_mod, execInstr_qDet, hkk, hkkS0,
        Function.update_idem, haddr, execInstr_store, hk1, execInstr_imm, Nat.zero_mod, runBlock_nil,
        Fin.zero_eta, Matrix.cons_val_zero, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
        Nat.add_left_cancel_iff]

/-- The expansion body as a `Sem` run. -/
theorem expandBody_sem (P : Program) (E : RAMEnv) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) (k : ℕ)
    (hAt : At P (base + 2) expandBody)
    (hsrc : (S0 + k) % 2 ^ E.W = S0 + k)
    (hsrcval : expandMem S0 b y t k (S0 + k) = enc b (eSeq b y k))
    (hld : enc b (eSeq b y k) % 2 ^ E.W = enc b (eSeq b y k))
    (hsq : (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = detSqBase w + enc b (eSeq b y k))
    (htab : E.det (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = sqTab b (enc b (eSeq b y k)))
    (hval : sqTab b (enc b (eSeq b y k)) = enc b (eSeq b y (2 * k + 1)))
    (hkk : (k + k) % 2 ^ E.W = k + k)
    (hkkS0 : (k + k + S0) % 2 ^ E.W = S0 + 2 * k)
    (haddr : (S0 + 2 * k + 1) % 2 ^ E.W = S0 + 2 * k + 1)
    (hk1 : (k + 1) % 2 ^ E.W = k + 1) :
    Sem P E (base + 2) (base + 18) (expandBodyIn base S0 w t b y k)
      (fun c s' => c = 16 ∧ s' = { expandState base S0 w t b y (k + 1) with pc := base + 18 }) := by
  refine Sem.mono (Sem.block P E (base + 2) expandBody (expandBodyIn base S0 w t b y k) hAt
    (by simp [expandBody]) rfl) ?_
  intro c s' hQ
  obtain ⟨hc, hs⟩ := hQ
  refine ⟨?_, ?_⟩
  · rw [hc, expandBody_length]
  · rw [hs]
    exact expandBody_spec E base S0 w t k b y (expandBodyIn base S0 w t b y k) rfl rfl rfl hsrc
      hsrcval hld hsq htab hval hkk hkkS0 haddr hk1

/-- The expansion iteration after the test: body entry back to the loop head, in 17 steps. -/
theorem expandBodyIter (P : Program) (E : RAMEnv) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) (k : ℕ)
    (hAt : At P base (Stmt.compile expandLoopStmt base)) (hW : 1 < 2 ^ E.W) (hk : k < t)
    (hsrc : (S0 + k) % 2 ^ E.W = S0 + k)
    (hsrcval : expandMem S0 b y t k (S0 + k) = enc b (eSeq b y k))
    (hld : enc b (eSeq b y k) % 2 ^ E.W = enc b (eSeq b y k))
    (hsq : (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = detSqBase w + enc b (eSeq b y k))
    (htab : E.det (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = sqTab b (enc b (eSeq b y k)))
    (hval : sqTab b (enc b (eSeq b y k)) = enc b (eSeq b y (2 * k + 1)))
    (hkk : (k + k) % 2 ^ E.W = k + k)
    (hkkS0 : (k + k + S0) % 2 ^ E.W = S0 + 2 * k)
    (haddr : (S0 + 2 * k + 1) % 2 ^ E.W = S0 + 2 * k + 1)
    (hk1 : (k + 1) % 2 ^ E.W = k + 1) :
    Sem P E (base + readCond.code.length + 1) base ({ runBlock readCond.code E (expandState base S0 w t b y k) with pc := base + readCond.code.length + 1 } : RAMState)
      (fun c s' => c = 17 ∧ s' = expandState base S0 w t b y (k + 1)) := by
  obtain ⟨hjz, hbodyAt, hjmp⟩ := at_loop_expand hAt
  have hbody := expandBody_sem P E base S0 w t b y k hbodyAt hsrc hsrcval hld hsq htab hval hkk hkkS0
    haddr hk1
  rw [expandBodyIn_eq E base S0 w t b y k hW hk]
  refine Sem.jmp_append (hAt := hjmp) ?_
  refine Sem.mono hbody ?_
  intro c s' hQ
  obtain ⟨hc, hs⟩ := hQ
  refine ⟨by omega, ?_⟩
  rw [hs]
  exact expandState_eta base S0 w t b y (k + 1)

/-- The exit state of the expansion loop. -/
theorem expandLoop_exit_state (E : RAMEnv) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) :
    ({ runBlock readCond.code E (expandState base S0 w t b y t) with pc := base + readCond.code.length + (Stmt.code expandBody).len + 2 } : RAMState) = { expandState base S0 w t b y t with pc := base + 19 } := by
  have hcl : readCond.code.length = 1 := readCond_code_length
  have hbl : (Stmt.code expandBody).len = 16 := expandBody_length
  have hrun := runBlock_expandCond_exit E base S0 w t b y
  refine ramState_eq_of _ _ ?_ ?_ ?_
  · simp only [hcl, hbl]
  · simp only [hrun]
  · intro d
    simp only [hrun]

/-- **The expansion loop.**  One `Sem.loop` call, exactly as for the read loop. -/
theorem expandLoop_spec (P : Program) (E : RAMEnv) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2)
    (hAt : At P base (Stmt.compile expandLoopStmt base)) (hW : 1 < 2 ^ E.W)
    (hsrc : ∀ k < t, (S0 + k) % 2 ^ E.W = S0 + k)
    (hsrcval : ∀ k < t, expandMem S0 b y t k (S0 + k) = enc b (eSeq b y k))
    (hld : ∀ k < t, enc b (eSeq b y k) % 2 ^ E.W = enc b (eSeq b y k))
    (hsq : ∀ k < t, (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = detSqBase w + enc b (eSeq b y k))
    (htab : ∀ k < t, E.det (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = sqTab b (enc b (eSeq b y k)))
    (hval : ∀ k < t, sqTab b (enc b (eSeq b y k)) = enc b (eSeq b y (2 * k + 1)))
    (hkk : ∀ k < t, (k + k) % 2 ^ E.W = k + k)
    (hkkS0 : ∀ k < t, (k + k + S0) % 2 ^ E.W = S0 + 2 * k)
    (haddr : ∀ k < t, (S0 + 2 * k + 1) % 2 ^ E.W = S0 + 2 * k + 1)
    (hk1 : ∀ k < t, (k + 1) % 2 ^ E.W = k + 1) :
    Sem P E base (base + 19) (expandState base S0 w t b y 0)
      (fun c s' => c ≤ 19 * t + 2 ∧ s' = { expandState base S0 w t b y t with pc := base + 19 }) := by
  have hloop := Sem.loop P E base readCond (Stmt.code expandBody) hAt hW t
    (fun j => expandState base S0 w t b y j) (fun _ => 17)
    (fun j => rfl)
    (fun j hj => (expandCond_eval base S0 w t b y j).mpr hj)
    (expandCond_false base S0 w t b y)
    (fun j hj => expandBodyIter P E base S0 w t b y j hAt hW hj (hsrc j hj) (hsrcval j hj) (hld j hj)
      (hsq j hj) (htab j hj) (hval j hj) (hkk j hj) (hkkS0 j hj) (haddr j hj) (hk1 j hj))
  have h19 : ((readCond.code.length + 1) + 17) = 19 := by
    rw [readCond_code_length]
  have hsum19 : (∑ j ∈ Finset.range t, (19 : ℕ)) = 19 * t := sum_range_const_mul t 19
  have hsum : (∑ j ∈ Finset.range t, ((readCond.code.length + 1) + 17)) = 19 * t := by
    rw [← hsum19]
    exact Finset.sum_congr rfl (fun j _ => h19)
  refine Sem.mono hloop ?_
  intro c s' hQ
  obtain ⟨hle, hs⟩ := hQ
  refine ⟨?_, ?_⟩
  · rw [hsum] at hle
    rw [readCond_code_length] at hle
    omega
  · rw [hs]
    exact expandLoop_exit_state E base S0 w t b y

/-- **The array is complete when the loop exits.**  The expansion trace above plus
`expandMem_complete`: after `t` iterations, every one of the `2t` syndrome slots holds the integer
spelling of `eSeq a`. -/
theorem expandLoop_result (P : Program) (E : RAMEnv) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2)
    (hAt : At P base (Stmt.compile expandLoopStmt base)) (hW : 1 < 2 ^ E.W)
    (hsrc : ∀ k < t, (S0 + k) % 2 ^ E.W = S0 + k)
    (hsrcval : ∀ k < t, expandMem S0 b y t k (S0 + k) = enc b (eSeq b y k))
    (hld : ∀ k < t, enc b (eSeq b y k) % 2 ^ E.W = enc b (eSeq b y k))
    (hsq : ∀ k < t, (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = detSqBase w + enc b (eSeq b y k))
    (htab : ∀ k < t, E.det (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = sqTab b (enc b (eSeq b y k)))
    (hval : ∀ k < t, sqTab b (enc b (eSeq b y k)) = enc b (eSeq b y (2 * k + 1)))
    (hkk : ∀ k < t, (k + k) % 2 ^ E.W = k + k)
    (hkkS0 : ∀ k < t, (k + k + S0) % 2 ^ E.W = S0 + 2 * k)
    (haddr : ∀ k < t, (S0 + 2 * k + 1) % 2 ^ E.W = S0 + 2 * k + 1)
    (hk1 : ∀ k < t, (k + 1) % 2 ^ E.W = k + 1) :
    Sem P E base (base + 19) (expandState base S0 w t b y 0)
      (fun c s' => c ≤ 19 * t + 2 ∧ s' = { expandState base S0 w t b y t with pc := base + 19 } ∧
        ∀ a, a < 2 * t → s'.mem (S0 + a) = enc b (eSeq b y a)) := by
  refine Sem.mono (expandLoop_spec P E base S0 w t b y hAt hW hsrc hsrcval hld hsq htab hval hkk
    hkkS0 haddr hk1) ?_
  intro c s' hQ
  obtain ⟨hle, hs⟩ := hQ
  refine ⟨hle, hs, ?_⟩
  intro a ha
  rw [hs]
  exact expandMem_complete S0 b y t ha

end Expand

section ExpandStd

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

end ExpandStd

@[simp] theorem enc_zero {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) : enc b 0 = 0 := by
  simp [enc]

theorem writeArray_frame (B : ℕ) (m f : ℕ → ℕ) (n a : ℕ)
    (ha : a < B ∨ B + n ≤ a) : writeArray B m f n a = m a := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [writeArray, Function.update_of_ne (by omega : a ≠ B + n)]
      exact ih (by omega)

theorem writeArray_get (B : ℕ) (m f : ℕ → ℕ) (n i : ℕ) (hi : i < n) :
    writeArray B m f n (B + i) = f i := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases h : i = n
      · subst i
        simp [writeArray]
      · rw [writeArray, Function.update_of_ne (by omega : B + i ≠ B + n)]
        exact ih (by omega)

theorem copyBody_spec (E : RAMEnv) (pc dst src L : ℕ) (m : ℕ → ℕ) (r : Fin 16 → ℕ)
    (j : ℕ) (hj : j < L) (hW : 1 < 2 ^ E.W) (hL : L < 2 ^ E.W)
    (hdst : dst + L ≤ 2 ^ E.W) (hsrc : src + L ≤ 2 ^ E.W)
    (hdisj : src + L ≤ dst ∨ dst + L ≤ src)
    (hword : ∀ i < L, m (src + i) < 2 ^ E.W) :
    runBlock copyBody E { runBlock copyCond.code E (copyState pc dst src L m r j) with pc := pc + 2 } =
      { copyState pc dst src L m r (j + 1) with pc := pc + 11 } := by
  have h1 : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hW
  have hsj : (src + j) % 2 ^ E.W = src + j := Nat.mod_eq_of_lt (by omega)
  have hdj : (dst + j) % 2 ^ E.W = dst + j := Nat.mod_eq_of_lt (by omega)
  have hj1 : (j + 1) % 2 ^ E.W = j + 1 := Nat.mod_eq_of_lt (by omega)
  have hm : writeArray dst m (fun i => m (src + i)) j (src + j) = m (src + j) :=
    writeArray_frame dst m _ j _ (by omega)
  have hv : m (src + j) % 2 ^ E.W = m (src + j) := Nat.mod_eq_of_lt (hword j hj)
  apply ramState_eq_of
  ·     simp only [copyBody, Fin.isValue, Cond.code, copyCond, copyState, runBlock_cons, execInstr, ↓reduceIte,
      one_ne_zero, runBlock_nil, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne,
      Function.update_self, Nat.zero_mod, Nat.add_right_cancel_iff, Nat.add_left_cancel_iff] <;> omega
  ·     simp only [copyBody, Fin.isValue, Cond.code, copyCond, copyState, runBlock_cons, execInstr, ↓reduceIte,
      one_ne_zero, runBlock_nil, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, hsj,
      Function.update_self, hm, hv, hdj, Nat.zero_mod, writeArray]
  · intro d
    fin_cases d <;>
      simp only [copyBody, Fin.isValue, Cond.code, copyCond, copyState, runBlock_cons, execInstr, ↓reduceIte,
        one_ne_zero, runBlock_nil, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne,
        Function.update_self, hj1, Nat.zero_mod, Fin.zero_eta, Nat.add_left_cancel_iff, Fin.mk_one,
        Fin.reduceFinMk]

theorem copyCond_eval (pc dst src L : ℕ) (m : ℕ → ℕ) (r : Fin 16 → ℕ) (j : ℕ) :
    copyCond.eval (copyState pc dst src L m r j) ↔ j < L := by
  simp [copyCond, Cond.eval, copyState]

theorem copyBodyIter (P : Program) (E : RAMEnv) (pc dst src L : ℕ)
    (m : ℕ → ℕ) (r : Fin 16 → ℕ) (j : ℕ) (hj : j < L)
    (hAt : At P pc (Stmt.compile copyStmt pc))
    (hW : 1 < 2 ^ E.W) (hL : L < 2 ^ E.W)
    (hdst : dst + L ≤ 2 ^ E.W) (hsrc : src + L ≤ 2 ^ E.W)
    (hdisj : src + L ≤ dst ∨ dst + L ≤ src)
    (hword : ∀ i < L, m (src + i) < 2 ^ E.W) :
    Sem P E (pc + copyCond.code.length + 1) pc
      { runBlock copyCond.code E (copyState pc dst src L m r j) with pc := pc + copyCond.code.length + 1 }
      (fun k s' => k = 10 ∧ s' = copyState pc dst src L m r (j + 1)) := by
  obtain ⟨_, _, hbody, hjmp⟩ := at_loop hAt
  have hbodyAt : At P (pc + 2) copyBody := hbody
  have hjmpAt : P[pc + 11]? = some (iJmp pc) := hjmp
  have hrun : Sem P E (pc + 2) (pc + 11)
      { runBlock copyCond.code E (copyState pc dst src L m r j) with pc := pc + 2 }
      (fun k s' => k = 9 ∧ s' = { copyState pc dst src L m r (j + 1) with pc := pc + 11 }) := by
    refine Sem.mono (Sem.block P E (pc + 2) copyBody _ hbodyAt (by simp [copyBody]) rfl) ?_
    intro k s' h
    obtain ⟨hk, hs⟩ := h
    refine ⟨hk, ?_⟩
    rw [hs]
    exact copyBody_spec E pc dst src L m r j hj hW hL hdst hsrc hdisj hword
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
    fin_cases d <;> simp [copyCond, Cond.code, copyState, runBlock_cons, runBlock_nil, execInstr]

/-- Copy a disjoint word array, preserving every address outside the target. -/
theorem copyArray_spec (P : Program) (E : RAMEnv) (pc dst src L : ℕ)
    (m : ℕ → ℕ) (r : Fin 16 → ℕ) (hAt : At P pc (Stmt.compile copyStmt pc))
    (hW : 1 < 2 ^ E.W) (hL : L < 2 ^ E.W)
    (hdst : dst + L ≤ 2 ^ E.W) (hsrc : src + L ≤ 2 ^ E.W)
    (hdisj : src + L ≤ dst ∨ dst + L ≤ src)
    (hword : ∀ i < L, m (src + i) < 2 ^ E.W) :
    Sem P E pc (pc + 12) (copyState pc dst src L m r 0)
      (fun k s' => k ≤ 12 * L + 2 ∧ s' = { copyState pc dst src L m r L with pc := pc + 12 }) := by
  have h := Sem.loop P E pc copyCond (.code copyBody) hAt hW L
    (fun j => copyState pc dst src L m r j) (fun _ => 10)
    (fun _ => rfl)
    (fun j hj => (copyCond_eval pc dst src L m r j).mpr hj)
    (fun hf => (Nat.lt_irrefl L) ((copyCond_eval pc dst src L m r L).mp hf))
    (fun j hj => copyBodyIter P E pc dst src L m r j hj hAt hW hL hdst hsrc hdisj hword)
  refine Sem.mono h ?_
  intro k s' hQ
  obtain ⟨hcost, hs⟩ := hQ
  refine ⟨?_, ?_⟩
  · have hsum : (∑ j ∈ Finset.range L, (copyCond.code.length + 1 + 10)) = 12 * L := by
      change (∑ j ∈ Finset.range L, (12 : ℕ)) = 12 * L
      exact sum_range_const_mul L 12
    rw [hsum] at hcost
    change k ≤ 2 + 12 * L at hcost
    omega
  · rw [hs]
    exact copyCond_exit E pc dst src L m r

theorem zeroRegs_spec (E : RAMEnv) (s : RAMState) :
    runBlock zeroRegsCode E s = boundaryState (s.pc + 16) s.mem := by
  apply ramState_eq_of
  ·     simp only [zeroRegsCode, Fin.isValue, runBlock_cons, execInstr, Nat.zero_mod, runBlock_nil,
      boundaryState, Nat.add_right_cancel_iff, Nat.add_left_cancel_iff] <;> omega
  · rfl
  · intro d
    fin_cases d <;>                     simp only [zeroRegsCode, Fin.isValue, runBlock_cons, execInstr, Nat.zero_mod,
                      runBlock_nil, Fin.zero_eta, ne_eq, Fin.reduceEq, not_false_eq_true,
                      Function.update_of_ne, zero_ne_one, Function.update_self, boundaryState, Fin.mk_one,
                      Fin.reduceFinMk]

/-- Read the two components of a compiled sequence inside a surrounding program. -/
theorem At.seqStmt {P : Program} {base : ℕ} {a b : Stmt}
    (h : At P base (Stmt.compile (.seq a b) base)) :
    At P base (Stmt.compile a base) ∧
      At P (base + a.len) (Stmt.compile b (base + a.len)) := by
  simpa only [Stmt.compile, At.append, Stmt.length_compile] using h

/-- Bounded-cost sequential composition with a state invariant. -/
theorem Sem.seq_bound {P : Program} {E : RAMEnv} {a b c A B : ℕ} {s : RAMState}
    {I J : RAMState → Prop}
    (h₁ : Sem P E a b s (fun k s' => k ≤ A ∧ I s'))
    (h₂ : ∀ s', s'.pc = b → I s' → Sem P E b c s' (fun k s'' => k ≤ B ∧ J s'')) :
    Sem P E a c s (fun k s' => k ≤ A + B ∧ J s') := by
  obtain ⟨hpc, k₁, s₁, hrun₁, hb, hcost₁, hI⟩ := h₁
  obtain ⟨_, k₂, s₂, hrun₂, hc, hcost₂, hJ⟩ := h₂ s₁ hb hI
  refine ⟨hpc, k₁ + k₂, s₂, ?_, hc, by omega, hJ⟩
  rw [Nat.add_comm k₁ k₂, Function.iterate_add_apply, hrun₁, hrun₂]

theorem decoderWorkspace_fits {w t : ℕ} (hw : 1 ≤ w) (ht : t < 2 ^ w) :
    decoderWorkspaceEnd t < 2 ^ (8 * w) := by
  let q : ℕ := 2 ^ w
  change t < q at ht
  have hq : 2 ≤ q := by
    have h := Nat.pow_le_pow_right (n := 2) (by norm_num) hw
    exact h
  have ht1 : t + 1 ≤ q := by omega
  have hsq : (t + 1) * (t + 1) ≤ q * q := Nat.mul_le_mul ht1 ht1
  have hq2 : 2 * q ≤ q * q := Nat.mul_le_mul_right q hq
  have hq4 : 4 ≤ q * q := by
    simpa using Nat.mul_le_mul hq hq
  have hfirst : decoderWorkspaceEnd t ≤ 8 * q * q + 48 * q + 104 := by
    unfold decoderWorkspaceEnd
    nlinarith only [hsq, ht1]
  have hsecond : 8 * q * q + 48 * q + 104 ≤ 58 * q * q := by
    nlinarith only [hq2, hq4]
  have hthird : 58 * q * q < 64 * q * q := by
    have hp : 0 < q * q := Nat.mul_pos (by omega) (by omega)
    nlinarith only [hp]
  have hpow : 64 * q * q = 2 ^ (w + w + 6) := by
    dsimp only [q]
    rw [Nat.pow_add, Nat.pow_add]
    norm_num <;> ring
  have hupper : (2 : ℕ) ^ (w + w + 6) ≤ 2 ^ (8 * w) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlower : decoderWorkspaceEnd t < 64 * q * q :=
    lt_of_le_of_lt hfirst (lt_of_le_of_lt hsecond hthird)
  rw [hpow] at hlower
  exact lt_of_lt_of_le hlower hupper

/-- Clear registers at a straight-line boundary without changing memory. -/
theorem Sem.zero_block (P : Program) (E : RAMEnv) (pc : ℕ) (s : RAMState)
    (hAt : At P pc zeroRegsCode) (hpc : s.pc = pc) :
    Sem P E pc (pc + 16) s (fun k z => k ≤ 16 ∧ z = boundaryState (pc + 16) s.mem) := by
  refine Sem.mono (Sem.block P E pc zeroRegsCode s hAt (by simp [zeroRegsCode]) hpc) ?_
  intro k z hQ
  obtain ⟨hk, hz⟩ := hQ
  refine ⟨by change k = 16 at hk; omega, ?_⟩
  rw [hz, zeroRegs_spec, hpc]

/-- A straight-line block can be placed at any program counter. -/
theorem runBlock_replace_pc (code : List Instr) (E : RAMEnv) (s : RAMState) (pc : ℕ) (hn : NoBranch code) :
    runBlock code E { s with pc := pc } = { runBlock code E s with pc := pc + code.length } := by
  induction code generalizing s pc with
  | nil => rfl
  | cons i code ih =>
      obtain ⟨hni, hnc⟩ := hn
      have hi : execInstr i E { s with pc := pc } = { execInstr i E s with pc := pc + 1 } := by
        cases i <;> simp_all [Instr.NoBranchI, execInstr]
      simp only [runBlock_cons, hi]
      rw [ih _ _ hnc]
      apply ramState_eq_of
      · simp only [List.length_cons]
        omega
      · rfl
      · intro _; rfl

/-- Reuse the verified header reader at the embedding address. -/
theorem paramBodyAt_spec (E : RAMEnv) (base N t w S0 : ℕ) (y : Fin (t * w) → ZMod 2)
    (hS0 : S0 = wordsOf (8 * w) (t * w)) (hW : E.W = 8 * w) (hw1 : 1 ≤ w)
    (h0 : E.det 0 % 2 ^ E.W = t) (h1 : E.det 1 % 2 ^ E.W = w) (h4 : E.det 4 % 2 ^ E.W = S0)
    (h5 : E.det 5 % 2 ^ E.W = 2 ^ w - 1) (h6 : E.det 6 % 2 ^ E.W = detSqBase w)
    (h12 : E.det 12 % 2 ^ E.W = 8 * w) (h1W : (1 : ℕ) % 2 ^ E.W = 1) :
    runBlock paramBody E { decoderStart (8 * w) y [] with pc := base } = readState (base + 14) S0 w t y 0 := by
  rw [runBlock_replace_pc paramBody E _ base (by simp [paramBody]),
    paramBody_spec E N t w S0 y hS0 hW hw1 h0 h1 h4 h5 h6 h12 h1W]
  rfl

theorem inputRead_spec {F : Type} [Field F] [Algebra (ZMod 2) F]
    (E : RAMEnv) (P : Program) (base N t w : ℕ) (y : Fin (t * w) → ZMod 2)
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (hAt : At P base (Stmt.compile inputReadStmt base))
    (hW : E.W = 8 * w) (hw1 : 1 ≤ w) (hNw : N < 2 ^ w) (htN : t ≤ N)
    (hdet : E.det = detStd t N b ι) :
    Sem P E base (base + 33) { decoderStart (8 * w) y [] with pc := base }
      (fun k z => k ≤ 19 * t + 16 ∧
        z = { readState (base + 14) (wordsOf (8 * w) (t * w)) w t y t with pc := base + 33 }) := by
  have hpos : 0 < w := by omega
  have h2w : (2 : ℕ) ^ w ≤ 2 ^ (8 * w) :=
    Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega : w ≤ 8 * w)
  have htW : t < 2 ^ (8 * w) := lt_of_le_of_lt htN (lt_of_lt_of_le hNw h2w)
  have hwW : w < 2 ^ (8 * w) := lt_of_lt_of_le (Nat.lt_two_pow_self (n := w)) h2w
  have hS0W : wordsOf (8 * w) (t * w) < 2 ^ (8 * w) :=
    lt_of_le_of_lt (wordsOf_le w t hw1) htW
  have hmaskW : 2 ^ w - 1 < 2 ^ (8 * w) := by
    have := Nat.two_pow_pos w
    omega
  have h1E : (1 : ℕ) < 2 ^ E.W := by
    rw [hW]
    have h0 : 0 < 8 * w := by omega
    have h := Nat.pow_lt_pow_right (by norm_num : 1 < 2) h0
    simpa using h
  -- the six header reads
  have h0 : E.det 0 % 2 ^ E.W = t := by
    rw [hdet, detStd_hdr t N w b ι (by norm_num : (0 : ℕ) < 13), hdrTab_zero, hW]
    exact Nat.mod_eq_of_lt htW
  have h1 : E.det 1 % 2 ^ E.W = w := by
    rw [hdet, detStd_hdr t N w b ι (by norm_num : (1 : ℕ) < 13), hdrTab_one, hW]
    exact Nat.mod_eq_of_lt hwW
  have h4 : E.det 4 % 2 ^ E.W = wordsOf (8 * w) (t * w) := by
    rw [hdet, detStd_hdr t N w b ι (by norm_num : (4 : ℕ) < 13), hdrTab_four, hW]
    exact Nat.mod_eq_of_lt hS0W
  have h5 : E.det 5 % 2 ^ E.W = 2 ^ w - 1 := by
    rw [hdet, detStd_hdr t N w b ι (by norm_num : (5 : ℕ) < 13), hdrTab_five, hW]
    exact Nat.mod_eq_of_lt hmaskW
  have h6 : E.det 6 % 2 ^ E.W = detSqBase w := by
    rw [hdet, detStd_hdr t N w b ι (by norm_num : (6 : ℕ) < 13), hdrTab_six, hW]
    exact Nat.mod_eq_of_lt (detSqBase_lt hw1)
  have h12 : E.det 12 % 2 ^ E.W = 8 * w := by
    rw [hdet, detStd_hdr t N w b ι (by norm_num : (12 : ℕ) < 13), hdrTab_twelve, hW]
    exact Nat.mod_eq_of_lt (Nat.lt_two_pow_self (n := 8 * w))
  have h1W : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt h1E
  -- per-iteration arithmetic
  have hmul : ∀ k < t, k * w % 2 ^ E.W = k * w := by
    intro k hk
    rw [hW]
    exact Nat.mod_eq_of_lt (mul_lt_two_pow_eight hw1 hNw (lt_of_lt_of_le hk htN))
  have hdiv : ∀ k < t, k * w / (8 * w) % 2 ^ E.W = k / 8 := by
    intro k hk
    rw [mul_div_eight w hpos k, hW]
    refine Nat.mod_eq_of_lt ?_
    calc k / 8 ≤ k := Nat.div_le_self _ _
      _ < 2 ^ w := by omega
      _ ≤ 2 ^ (8 * w) := h2w
  have hmod : ∀ k < t, k * w % (8 * w) % 2 ^ E.W = k % 8 * w := by
    intro k hk
    rw [mul_mod_eight, hW]
    refine Nat.mod_eq_of_lt ?_
    calc k % 8 * w ≤ 7 * w := Nat.mul_le_mul_right w (by
          have := Nat.mod_lt k (by norm_num : (0 : ℕ) < 8)
          omega)
      _ < 8 * w := by omega
      _ ≤ 2 ^ (8 * w) := le_of_lt (Nat.lt_two_pow_self (n := 8 * w))
  have haddr : ∀ k < t, (wordsOf (8 * w) (t * w) + 2 * k) % 2 ^ E.W
      = wordsOf (8 * w) (t * w) + 2 * k := by
    intro k hk
    rw [hW]
    exact Nat.mod_eq_of_lt (addr_lt_two_pow_eight hw1
      (lt_of_le_of_lt htN hNw) (wordsOf_le w t hw1) hk)
  have hk1 : ∀ k < t, (k + 1) % 2 ^ E.W = k + 1 := by
    intro k hk
    rw [hW]
    refine Nat.mod_eq_of_lt ?_
    have h1' : k + 1 ≤ t := by omega
    omega
  have hmask : (2 ^ w - 1) % 2 ^ E.W = 2 ^ w - 1 := by
    rw [hW]
    exact Nat.mod_eq_of_lt hmaskW
  have hword : ∀ k < t, k / 8 < wordsOf (8 * w) (t * w) := by
    intro k hk
    rw [wordsOf_eight w t hpos]
    omega
  have hpk : ∀ k < t, packMem (8 * w) y (k / 8) % 2 ^ E.W = packMem (8 * w) y (k / 8) := by
    intro k hk
    rw [hW]
    exact Nat.mod_eq_of_lt (packMem_lt hpos y (k / 8))
  obtain ⟨hParamAt, hLoopAt⟩ := At.seqStmt hAt
  have hPro : Sem P E base (base + 14) { decoderStart (8 * w) y [] with pc := base }
      (fun k z => k ≤ 14 ∧ z = readState (base + 14) (wordsOf (8 * w) (t * w)) w t y 0) := by
    refine Sem.mono (Sem.block P E base paramBody _ hParamAt (by simp [paramBody]) rfl) ?_
    intro k z hQ
    have hk : k = 14 := hQ.1
    exact ⟨by omega, hQ.2.trans (paramBodyAt_spec E base N t w (wordsOf (8 * w) (t * w)) y rfl
      hW hw1 h0 h1 h4 h5 h6 h12 h1W)⟩
  have hLoop := readLoop_spec P E (base + 14) (wordsOf (8 * w) (t * w)) w t y hLoopAt
    h1E hW (by rw [hW]; omega) hpos hmul hdiv hmod haddr hk1 hmask hword hpk
  have hFull := Sem.seq_bound hPro (fun z _ hz => by subst z; exact hLoop)
  exact Sem.mono hFull (fun k z hQ => ⟨by omega, hQ.2⟩)

theorem expandAt_spec {F : Type} [Field F] [Algebra (ZMod 2) F]
    (P : Program) (E : RAMEnv) (N t w base : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) (ι : ℕ → F)
    (hAt : At P base (Stmt.compile expandLoopStmt base))
    (hW : E.W = 8 * w) (hw1 : 1 ≤ w) (hNw : N < 2 ^ w) (htN : t ≤ N)
    (hdet : E.det = detStd t N b ι) :
    Sem P E base (base + 19) (expandState base (wordsOf (8 * w) (t * w)) w t b y 0)
      (fun k z => k ≤ 19 * t + 2 ∧
        z = { expandState base (wordsOf (8 * w) (t * w)) w t b y t with pc := base + 19 } ∧
        ∀ a, a < 2 * t → z.mem (wordsOf (8 * w) (t * w) + a) = enc b (eSeq b y a)) := by
  have hpos : 0 < w := by omega
  have h2w : (2 : ℕ) ^ w ≤ 2 ^ (8 * w) :=
    Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega : w ≤ 8 * w)
  have htW : t < 2 ^ (8 * w) := lt_of_le_of_lt htN (lt_of_lt_of_le hNw h2w)
  have hS0t : wordsOf (8 * w) (t * w) ≤ t := wordsOf_le w t hw1
  have h1E : (1 : ℕ) < 2 ^ E.W := by
    rw [hW]
    have h0 : 0 < 8 * w := by omega
    have h := Nat.pow_lt_pow_right (by norm_num : 1 < 2) h0
    simpa using h
  -- the per-iteration side conditions
  have hsrc : ∀ k < t, (wordsOf (8 * w) (t * w) + k) % 2 ^ E.W = wordsOf (8 * w) (t * w) + k := by
    intro k hk
    rw [hW]
    refine Nat.mod_eq_of_lt ?_
    have h1 : wordsOf (8 * w) (t * w) + k < 2 ^ w + 2 ^ w := by omega
    calc wordsOf (8 * w) (t * w) + k < 2 ^ w + 2 ^ w := h1
      _ = 2 ^ (w + 1) := by rw [Nat.pow_succ]; ring
      _ ≤ 2 ^ (8 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have henc : ∀ k < t, enc b (eSeq b y k) < 2 ^ E.W := by
    intro k hk
    rw [hW]
    exact lt_of_lt_of_le (enc_lt b _) h2w
  have hsrcval : ∀ k < t, expandMem (wordsOf (8 * w) (t * w)) b y t k
      (wordsOf (8 * w) (t * w) + k) = enc b (eSeq b y k) := by
    intro k hk
    exact expandMem_src (wordsOf (8 * w) (t * w)) b y t k hk
  have hld : ∀ k < t, enc b (eSeq b y k) % 2 ^ E.W = enc b (eSeq b y k) := by
    intro k hk
    exact Nat.mod_eq_of_lt (henc k hk)
  have hsq : ∀ k < t,
      (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = detSqBase w + enc b (eSeq b y k) := by
    intro k hk
    rw [hW]
    exact Nat.mod_eq_of_lt (detSqBase_add_lt hw1 (enc_lt b _))
  have htab : ∀ k < t,
      E.det (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = sqTab b (enc b (eSeq b y k)) := by
    intro k hk
    rw [hdet, detStd_sq t N w b ι (enc_lt b _), hW]
    exact Nat.mod_eq_of_lt (lt_of_lt_of_le (enc_lt b _) h2w)
  have hval : ∀ k < t, sqTab b (enc b (eSeq b y k)) = enc b (eSeq b y (2 * k + 1)) := by
    intro k hk
    exact sqTab_enc b y k
  have hkk : ∀ k < t, (k + k) % 2 ^ E.W = k + k := by
    intro k hk
    rw [hW]
    refine Nat.mod_eq_of_lt ?_
    have h1 : k + k < 2 ^ w + 2 ^ w := by omega
    calc k + k < 2 ^ w + 2 ^ w := h1
      _ = 2 ^ (w + 1) := by rw [Nat.pow_succ]; ring
      _ ≤ 2 ^ (8 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hkkS0 : ∀ k < t,
      (k + k + wordsOf (8 * w) (t * w)) % 2 ^ E.W = wordsOf (8 * w) (t * w) + 2 * k := by
    intro k hk
    have h := addr_lt_two_pow_eight (w := w) (t := t) (k := k)
      (S0 := wordsOf (8 * w) (t * w)) hw1 (lt_of_le_of_lt htN hNw) hS0t hk
    have h2 : k + k + wordsOf (8 * w) (t * w) = wordsOf (8 * w) (t * w) + 2 * k := by omega
    rw [h2, hW]
    exact Nat.mod_eq_of_lt h
  have haddr : ∀ k < t,
      (wordsOf (8 * w) (t * w) + 2 * k + 1) % 2 ^ E.W = wordsOf (8 * w) (t * w) + 2 * k + 1 := by
    intro k hk
    rw [hW]
    exact Nat.mod_eq_of_lt (addr_succ_lt_two_pow_eight hw1 (lt_of_le_of_lt htN hNw) hS0t hk)
  have hk1 : ∀ k < t, (k + 1) % 2 ^ E.W = k + 1 := by
    intro k hk
    rw [hW]
    refine Nat.mod_eq_of_lt ?_
    have h2 : k + 1 ≤ t := by omega
    omega
  exact expandLoop_result P E base (wordsOf (8 * w) (t * w)) w t b y
    hAt
    h1E hsrc hsrcval hld hsq htab hval hkk hkkS0 haddr hk1

theorem readToExpansion_spec {F : Type} [Field F] [Algebra (ZMod 2) F]
    (E : RAMEnv) (readBase pc S0 w t : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) :
    runBlock [iImm r5 0] E { readState readBase S0 w t y t with pc := pc } = expandState (pc + 1) S0 w t b y 0 := by
  apply ramState_eq_of
  · rfl
  · exact (expandMem_zero S0 b y t).symm
  · intro r
    fin_cases r <;> simp [runBlock_cons, runBlock_nil, execInstr, readState, expandState]

/-- The expanded input writes no words beyond the 2t coefficient array. -/
theorem expandMem_after_zero {F : Type} [Field F] [Algebra (ZMod 2) F] {w M : ℕ}
    (S0 : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin M → ZMod 2) (t addr : ℕ)
    (haddr : S0 + 2 * t ≤ addr) : expandMem S0 b y t t addr = 0 := by
  have h0 : ¬ addr < S0 := by omega
  have h1 : ¬ (addr - S0) / 2 < t := by omega
  simp [expandMem, h0, h1]

theorem inputFront_spec {F : Type} [Field F] [Algebra (ZMod 2) F]
    (E : RAMEnv) (P : Program) (base N t w : ℕ) (y : Fin (t * w) → ZMod 2)
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (hAt : At P base (Stmt.compile inputFrontStmt base))
    (hW : E.W = 8 * w) (hw1 : 1 ≤ w) (hNw : N < 2 ^ w) (htN : t ≤ N)
    (hdet : E.det = detStd t N b ι) :
    Sem P E base (base + 69) { decoderStart (8 * w) y [] with pc := base }
      (fun k z => k ≤ 38 * t + 35 ∧
        z = boundaryState (base + 69) (expandMem (wordsOf (8 * w) (t * w)) b y t t) ∧
        FieldArrayStored b z.mem (wordsOf (8 * w) (t * w)) (2 * t) (eSeq b y) ∧
        ∀ addr, wordsOf (8 * w) (t * w) + 2 * t ≤ addr → z.mem addr = 0) := by
  let S0 := wordsOf (8 * w) (t * w)
  obtain ⟨hReadAt, hRestAt⟩ := At.seqStmt hAt
  obtain ⟨hResetAt, hRest2At⟩ := At.seqStmt hRestAt
  obtain ⟨hExpandAt, hZeroAt⟩ := At.seqStmt hRest2At
  have hRead := inputRead_spec E P base N t w y b ι hReadAt hW hw1 hNw htN hdet
  have hReset : Sem P E (base + 33) (base + 34)
      { readState (base + 14) S0 w t y t with pc := base + 33 }
      (fun k z => k ≤ 1 ∧ z = expandState (base + 34) S0 w t b y 0) := by
    refine Sem.mono (Sem.block P E (base + 33) [iImm r5 0] _ hResetAt (by simp) rfl) ?_
    intro k z hQ
    have hk : k = 1 := hQ.1
    exact ⟨by omega, hQ.2.trans (readToExpansion_spec E (base + 14) (base + 33) S0 w t b y)⟩
  have hExpand := expandAt_spec P E N t w (base + 34) b y ι hExpandAt hW hw1 hNw htN hdet
  have hExpandExact : Sem P E (base + 34) (base + 53) (expandState (base + 34) S0 w t b y 0)
      (fun k z => k ≤ 19 * t + 2 ∧ z = { expandState (base + 34) S0 w t b y t with pc := base + 53 }) :=
    Sem.mono hExpand (fun _ _ hQ => ⟨hQ.1, hQ.2.1⟩)
  have hZero := Sem.zero_block P E (base + 53)
    { expandState (base + 34) S0 w t b y t with pc := base + 53 } hZeroAt rfl
  have hFull := Sem.seq_bound hRead (fun z _ hz => by
    subst z
    exact Sem.seq_bound hReset (fun z _ hz => by
      subst z
      exact Sem.seq_bound hExpandExact (fun z _ hz => by subst z; exact hZero)))
  refine Sem.mono hFull ?_
  intro k z hQ
  refine ⟨by omega, hQ.2, ?_, ?_⟩
  · rw [hQ.2]
    intro j hj
    exact expandMem_complete S0 b y t hj
  · rw [hQ.2]
    intro addr ha
    exact expandMem_after_zero S0 b y t addr ha

theorem decoderAllocEnd_eq (t : ℕ) : decoderAllocEnd t = 8 * t * t + 44 * t + 144 := by
  unfold decoderAllocEnd decoderVerifyBase decoderOutputBase decoderQueue1 decoderQueue0 decoderRowBase
    decoderSavedBase decoderCapacity decoderLength
  ring

theorem decoderAllocEnd_fits (t w : ℕ) (hw : 1 ≤ w) (ht : t < 2 ^ w) : decoderAllocEnd t < 2 ^ (8 * w) := by
  have h := decoderWorkspace_fits hw ht
  rw [decoderAllocEnd_eq]
  dsimp [decoderWorkspaceEnd] at h
  omega

theorem saveHeader_spec (E : RAMEnv) (s : RAMState) (t S0 : ℕ)
    (hmeta : (128 : ℕ) < 2 ^ E.W) (ht : 2 * t < 2 ^ E.W)
    (h0 : E.det 0 % 2 ^ E.W = t) (h4 : E.det 4 % 2 ^ E.W = S0) :
    runBlock saveHeaderCode E s =
      { s with pc := s.pc + 5, regs := Function.update (Function.update (Function.update s.regs r1 (2 * t)) r3 S0) r14 4 } := by
  have hsmall (i : ℕ) (hi : i ≤ 128) : i % 2 ^ E.W = i := Nat.mod_eq_of_lt (by omega)
  have h2t : (t + t) % 2 ^ E.W = 2 * t := by rw [show t + t = 2 * t by omega, Nat.mod_eq_of_lt ht]
  apply ramState_eq_of
  · simp [saveHeaderCode, runBlock_cons, runBlock_nil, execInstr] <;> omega
  · rfl
  · intro r
    fin_cases r <;> simp [saveHeaderCode, runBlock_cons, runBlock_nil, execInstr, hsmall, h0, h4, h2t]

theorem saveDestination_spec (E : RAMEnv) (s : RAMState) (t : ℕ)
    (hmeta : (128 : ℕ) < 2 ^ E.W) (hB : decoderSavedBase t < 2 ^ E.W)
    (h0 : E.det 0 % 2 ^ E.W = t) :
    runBlock saveDestinationCode E s =
      { s with pc := s.pc + 8, regs := Function.update (Function.update (Function.update s.regs r2 (decoderSavedBase t)) r4 1) r14 0 } := by
  have hsmall (i : ℕ) (hi : i ≤ 128) : i % 2 ^ E.W = i := Nat.mod_eq_of_lt (by omega)
  have hmul : (t * 3) % 2 ^ E.W = t * 3 := Nat.mod_eq_of_lt (by dsimp [decoderSavedBase] at hB; omega)
  have hadd : (t * 3 + 128) % 2 ^ E.W = decoderSavedBase t := by
    rw [show t * 3 + 128 = decoderSavedBase t by unfold decoderSavedBase; omega, Nat.mod_eq_of_lt hB]
  apply ramState_eq_of
  ·     simp only [saveDestinationCode, Fin.isValue, runBlock_cons, execInstr, Nat.zero_mod,
      Function.update_self, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Nat.mul_mod_mod,
      Nat.mod_mul_mod, Nat.add_mod_mod, Nat.mod_add_mod, runBlock_nil, Nat.add_right_cancel_iff,
      Nat.add_left_cancel_iff] <;> omega
  · rfl
  · intro r
    fin_cases r <;>                     simp only [saveDestinationCode, Fin.isValue, runBlock_cons, execInstr, zero_le, hsmall,
                      Function.update_self, h0, Nat.reduceLeDiff, ne_eq, Fin.reduceEq, not_false_eq_true,
                      Function.update_of_ne, hmul, Std.le_refl, hadd, Nat.one_le_ofNat, runBlock_nil,
                      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]

theorem saveArgs_spec (E : RAMEnv) (pc S0 t : ℕ) (m : ℕ → ℕ)
    (hmeta : (128 : ℕ) < 2 ^ E.W) (ht : 2 * t < 2 ^ E.W) (hB : decoderSavedBase t < 2 ^ E.W)
    (h0 : E.det 0 % 2 ^ E.W = t) (h4 : E.det 4 % 2 ^ E.W = S0) :
    runBlock saveArgsCode E (boundaryState pc m) = copyState (pc + 13) (decoderSavedBase t) S0 (2 * t) m (fun _ => 0) 0 := by
  rw [saveArgsCode, runBlock_append, saveHeader_spec E _ t S0 hmeta ht h0 h4, saveDestination_spec E _ t hmeta hB h0]
  apply ramState_eq_of
  · rfl
  · rfl
  · intro r
    fin_cases r <;> simp [boundaryState, copyState]

theorem saveSyndromeProcedure_spec {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (P : Program) (E : RAMEnv) (pc S0 t : ℕ) (e : ℕ → F) (m : ℕ → ℕ)
    (hAt : At P pc (Stmt.compile saveSyndromeProcedure pc))
    (hmeta : (128 : ℕ) < 2 ^ E.W) (hwe : w ≤ E.W)
    (hS0 : S0 ≤ t) (hword : decoderSavedBase t + 2 * t ≤ 2 ^ E.W) (hBfit : decoderSavedBase t < 2 ^ E.W)
    (h0 : E.det 0 % 2 ^ E.W = t) (h4 : E.det 4 % 2 ^ E.W = S0)
    (hsums : FieldArrayStored b m S0 (2 * t) e) (htail : ∀ addr, S0 + 2 * t ≤ addr → m addr = 0) :
    Sem P E pc (pc + 41) (boundaryState pc m)
      (fun k z => k ≤ 12 * (2 * t) + 31 ∧
        z = boundaryState (pc + 41) (writeArray (decoderSavedBase t) m (fun i => m (S0 + i)) (2 * t)) ∧
        FieldArrayStored b z.mem (decoderSavedBase t) (2 * t) e ∧
        ∀ addr, decoderSavedBase t + 2 * t ≤ addr → z.mem addr = 0) := by
  have hlen : 2 * t < 2 ^ E.W := by
    have hb : 128 ≤ decoderSavedBase t := by unfold decoderSavedBase; omega
    omega
  have hsrc : S0 + 2 * t ≤ 2 ^ E.W := by dsimp [decoderSavedBase] at hword; omega
  have hdisj : S0 + 2 * t ≤ decoderSavedBase t := by unfold decoderSavedBase; omega
  obtain ⟨hArgsAt, hRestAt⟩ := At.seqStmt hAt
  obtain ⟨hCopyAt, hZeroAt⟩ := At.seqStmt hRestAt
  have hArgs : Sem P E pc (pc + 13) (boundaryState pc m)
      (fun k z => k ≤ 13 ∧ z = copyState (pc + 13) (decoderSavedBase t) S0 (2 * t) m (fun _ => 0) 0) := by
    refine Sem.mono (Sem.block P E pc saveArgsCode _ hArgsAt (by simp [saveArgsCode, saveHeaderCode, saveDestinationCode]) rfl) ?_
    intro k z hQ
    have hk : k = 13 := hQ.1
    exact ⟨by omega, hQ.2.trans (saveArgs_spec E pc S0 t m hmeta hlen hBfit h0 h4)⟩
  have hCopy := copyArray_spec P E (pc + 13) (decoderSavedBase t) S0 (2 * t) m (fun _ => 0) hCopyAt (by omega)
    hlen hword hsrc (Or.inl hdisj) (by
      intro j hj
      rw [hsums j hj]
      exact lt_of_lt_of_le (enc_lt b _) (Nat.pow_le_pow_right (by norm_num) hwe))
  have hZero := Sem.zero_block P E (pc + 25)
    { copyState (pc + 13) (decoderSavedBase t) S0 (2 * t) m (fun _ => 0) (2 * t) with pc := pc + 25 } hZeroAt rfl
  have hFull := Sem.seq_bound hArgs (fun z _ hz => by
    subst z
    exact Sem.seq_bound hCopy (fun z _ hz => by subst z; exact hZero))
  refine Sem.mono hFull ?_
  intro k z hQ
  refine ⟨by omega, hQ.2, ?_, ?_⟩
  · rw [hQ.2]
    change FieldArrayStored b (writeArray (decoderSavedBase t) m (fun i => m (S0 + i)) (2 * t)) (decoderSavedBase t) (2 * t) e
    intro j hj
    rw [writeArray_get _ _ _ (2 * t) j hj]
    exact hsums j hj
  · rw [hQ.2]
    change ∀ addr, decoderSavedBase t + 2 * t ≤ addr → writeArray (decoderSavedBase t) m (fun i => m (S0 + i)) (2 * t) addr = 0
    intro addr ha
    rw [writeArray_frame _ _ _ _ addr (Or.inr ha)]
    apply htail
    dsimp [decoderSavedBase] at ha
    omega

theorem syndromePoly_coeff {F : Type} [Field F] (e : ℕ → F) (t j : ℕ) :
    (syndromePoly e t).coeff j = if j < 2 * t then e j else 0 := by
  classical
  simp [syndromePoly, Polynomial.coeff_C_mul_X_pow, eq_comm]

theorem saved_syndrome_polynomial {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (t : ℕ) (e : ℕ → F) (m : ℕ → ℕ)
    (hstored : FieldArrayStored b m (decoderSavedBase t) (2 * t) e)
    (htail : ∀ addr, decoderSavedBase t + 2 * t ≤ addr → m addr = 0) :
    PolynomialStored b m (decoderSavedBase t) (decoderCapacity t) (syndromePoly e t) := by
  intro j hj
  rw [syndromePoly_coeff]
  by_cases h : j < 2 * t
  · rw [if_pos h]
    exact hstored j h
  · rw [if_neg h, enc_zero]
    exact htail _ (by omega)

section PinBits

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

end PinBits

section Uniqueness

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

end Uniqueness

section Slp

variable {F : Type} [Field F]

end Slp

/-! ## The read stage at a memory that is zero only inside the workspace

The decoder stages keep their whole workspace in `[0, decoderAllocEnd t)`.  The published read
contract (`pinsketch_decoder_read`) is however stated at the *globally* zero memory
`hintMem (8w) y []`, because the copy-in of `pinsketchRunStmt` builds that memory exactly.  The row
loop of Theorem 6.5 only ever clears its own scratch, so here we re-run the same read stage from an
ambient memory `m` that merely agrees with `hintMem` on `[0, decoderAllocEnd t)`.

The device that makes the port mechanical is the mask

  `maskMem N c m a = if a < N then c a else m a`

with `N = decoderAllocEnd t`: every memory the stage builds is `maskMem` applied to the canonical
`readMem`/`expandMem`, and every `if` is discharged by the static layout bound
`S0 + 2t ≤ decoderAllocEnd t`.  The stage therefore *cannot* disturb anything at or above
`decoderAllocEnd t`, which is exactly the frame the row loop needs. -/

section BoundedRead

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

/-- `maskMem N c m` is `c` below `N` and the ambient memory `m` at and above `N`. -/
def maskMem (N : ℕ) (c m : ℕ → ℕ) : ℕ → ℕ := fun a => if a < N then c a else m a

theorem maskMem_lt {N : ℕ} {c m : ℕ → ℕ} {a : ℕ} (h : a < N) : maskMem N c m a = c a :=
  if_pos h

theorem maskMem_ge {N : ℕ} {c m : ℕ → ℕ} {a : ℕ} (h : N ≤ a) : maskMem N c m a = m a :=
  if_neg (by omega)

theorem maskMem_update {N : ℕ} {c m : ℕ → ℕ} {a v : ℕ} (h : a < N) :
    maskMem N (Function.update c a v) m = Function.update (maskMem N c m) a v := by
  funext x
  by_cases hx : x = a
  · subst hx
    rw [maskMem_lt h, Function.update_self, Function.update_self]
  · by_cases hN : x < N
    · rw [maskMem_lt hN, Function.update_of_ne hx, Function.update_of_ne hx, maskMem_lt hN]
    · rw [maskMem_ge (show N ≤ x by omega), Function.update_of_ne hx,
        maskMem_ge (show N ≤ x by omega)]

/-- The payload never needs more words than there are syndrome coordinates. -/
theorem frontBound {S0 t : ℕ} (hS0 : S0 ≤ t) : S0 + 2 * t ≤ decoderAllocEnd t := by
  rw [decoderAllocEnd_eq]
  omega

/-- The saved-syndrome block ends inside the decoder's scratch. -/
theorem savedBase_le_allocEnd (t : ℕ) : decoderSavedBase t + 2 * t ≤ decoderAllocEnd t := by
  rw [decoderAllocEnd_eq]
  unfold decoderSavedBase
  omega

/-- The syndrome-polynomial block `[decoderSavedBase t, decoderSavedBase t + decoderCapacity t)`
ends inside the decoder's scratch. -/
theorem savedCapBound (t j : ℕ) (hj : j < decoderCapacity t) :
    decoderSavedBase t + j < decoderAllocEnd t := by
  rw [decoderAllocEnd_eq]
  unfold decoderSavedBase
  unfold decoderCapacity decoderLength at hj
  omega

/-- **The bounded-tail form of `saved_syndrome_polynomial`**: zeros are needed only inside the
decoder's scratch. -/
theorem saved_syndrome_polynomialB {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (t : ℕ) (e : ℕ → F) (m : ℕ → ℕ)
    (hstored : FieldArrayStored b m (decoderSavedBase t) (2 * t) e)
    (htail : ∀ addr, decoderSavedBase t + 2 * t ≤ addr → addr < decoderAllocEnd t → m addr = 0) :
    PolynomialStored b m (decoderSavedBase t) (decoderCapacity t) (syndromePoly e t) := by
  intro j hj
  rw [syndromePoly_coeff]
  by_cases h : j < 2 * t
  · rw [if_pos h]
    exact hstored j h
  · rw [if_neg h, enc_zero]
    exact htail _ (by omega) (savedCapBound t j hj)

/-! ### The read loop at a masked memory -/

/-- The read-loop memory, masked at `N`. -/
noncomputable def readMemB {M : ℕ} (N : ℕ) (m : ℕ → ℕ) (S0 w : ℕ) (y : Fin M → ZMod 2) (k : ℕ) :
    ℕ → ℕ :=
  maskMem N (readMem S0 w y k) m

theorem readMemB_succ {M : ℕ} {N : ℕ} {m : ℕ → ℕ} {S0 w : ℕ} {y : Fin M → ZMod 2} {k : ℕ}
    (hk : S0 + 2 * k < N) :
    readMemB N m S0 w y (k + 1)
      = Function.update (readMemB N m S0 w y k) (S0 + 2 * k) (syndromeInt w y k) := by
  unfold readMemB
  rw [readMem_succ]
  exact maskMem_update hk

theorem readMemB_below {M : ℕ} {N : ℕ} {m : ℕ → ℕ} {S0 w : ℕ} {y : Fin M → ZMod 2} {k : ℕ}
    {addr : ℕ} (hN : S0 ≤ N) (h : addr < S0) :
    readMemB N m S0 w y k addr = packMem (8 * w) y addr := by
  unfold readMemB
  rw [maskMem_lt (by omega), readMem_below S0 w y k h]

/-- The read-loop state, at a memory masked at `decoderAllocEnd t`. -/
noncomputable def readStateB (m : ℕ → ℕ) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    RAMState where
  pc := base
  regs := ![t, w, S0, 2 ^ w - 1, detSqBase w, k, 0, 0, 1, 0, 0, 0, 0, 0, 0, 8 * w]
  mem := readMemB (decoderAllocEnd t) m S0 w y k

attribute [local simp] readStateB

theorem readStateB_regs_eq (m : ℕ → ℕ) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    (readStateB m base S0 w t y k).regs
      = ![t, w, S0, 2 ^ w - 1, detSqBase w, k, 0, 0, 1, 0, 0, 0, 0, 0, 0, 8 * w] := rfl

@[simp] theorem readStateB_r14 (m : ℕ → ℕ) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    (readStateB m base S0 w t y k).regs r14 = 0 := by
  rw [readStateB_regs_eq]
  simp

/-- The state at the entry of the loop body, at a masked memory. -/
noncomputable def readBodyInB (m : ℕ → ℕ) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    RAMState where
  pc := base + 2
  regs := Function.update (readStateB m base S0 w t y k).regs r14 1
  mem := readMemB (decoderAllocEnd t) m S0 w y k

/-- **The read-loop body, as a state map, at a masked memory.** -/
theorem readBody_specB (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t k : ℕ)
    (y : Fin (t * w) → ZMod 2) (s : RAMState)
    (hpc : s.pc = base + 2)
    (hregs : s.regs = Function.update (readStateB m base S0 w t y k).regs r14 1)
    (hmem : s.mem = readMemB (decoderAllocEnd t) m S0 w y k)
    (hW : E.W = 8 * w) (hwe : w ≤ E.W) (hw : 0 < w)
    (hmul : k * w % 2 ^ E.W = k * w) (hdiv : k * w / (8 * w) % 2 ^ E.W = k / 8)
    (hmod : k * w % (8 * w) % 2 ^ E.W = k % 8 * w) (haddr : (S0 + 2 * k) % 2 ^ E.W = S0 + 2 * k)
    (hk1 : (k + 1) % 2 ^ E.W = k + 1) (hmask : (2 ^ w - 1) % 2 ^ E.W = 2 ^ w - 1)
    (hword : k / 8 < S0) (hpk : packMem (8 * w) y (k / 8) % 2 ^ E.W = packMem (8 * w) y (k / 8))
    (hSN : S0 ≤ decoderAllocEnd t) (hkN : S0 + 2 * k < decoderAllocEnd t) :
    runBlock readBody E s = { readStateB m base S0 w t y (k + 1) with pc := base + 18 } := by
  have haddr2 : (k + k + S0) % 2 ^ E.W = S0 + 2 * k := haddr2_of haddr
  have hval : ((packMem (8 * w) y (k / 8) / 2 ^ (k % 8 * w)) % 2 ^ E.W % 2 ^ w) % 2 ^ E.W
      = syndromeInt w y k := by
    rw [Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos w))
      (Nat.pow_le_pow_right (by norm_num) hwe))]
    exact read_value hwe hw (t * w) y k
  have hbelow : readMemB (decoderAllocEnd t) m S0 w y k (k / 8) = packMem (8 * w) y (k / 8) :=
    readMemB_below hSN hword
  have hpc' : (runBlock readBody E s).pc = base + 18 := by
    rw [runBlock_pc readBody E s (by simp [readBody]), hpc, readBody_length]
  refine ramState_eq_of _ _ hpc' ?_ ?_
  · funext addr
    show (runBlock readBody E s).mem addr = readMemB (decoderAllocEnd t) m S0 w y (k + 1) addr
    by_cases h : addr = S0 + 2 * k
    · rw [h, readMemB_succ hkN, Function.update_self]
      simp only [readBody, Fin.isValue, List.cons_append, List.nil_append, runBlock_cons, execInstr_mul,
        hregs, readStateB, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Matrix.cons_val,
        Matrix.cons_val_one, Matrix.cons_val_zero, hmul, hmem, execInstr_div, Function.update_self, hdiv,
        execInstr_mod, hmod, execInstr_load, hbelow, hpk, execInstr_shr,
        Function.update_idem, execInstr_band, Nat.and_two_pow_sub_one_eq_mod, hval, execInstr_add,
        Nat.mod_add_mod, haddr2, execInstr_store, hk1, execInstr_imm, Nat.zero_mod, runBlock_nil]
    · rw [readMemB_succ hkN, Function.update_of_ne h]
      simp [readBody, runBlock_cons, runBlock_nil, hregs, hmem, readStateB, hmul, hdiv, hmod,
        haddr, haddr2, hk1, hmask, hbelow, hpk, hval, Function.update_of_ne h]
  · intro d
    simp only [readBody, Fin.isValue, List.cons_append, List.nil_append, runBlock_cons, execInstr_mul,
      hregs, readStateB, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Matrix.cons_val,
      Matrix.cons_val_one, Matrix.cons_val_zero, hmul, execInstr_div, Function.update_self, hdiv,
      execInstr_mod, hmod, execInstr_load, execInstr_shr, Function.update_idem, execInstr_band,
      Nat.and_two_pow_sub_one_eq_mod, execInstr_add, Nat.mod_add_mod, execInstr_store, hk1, execInstr_imm,
      Nat.zero_mod, runBlock_nil]
    fin_cases d <;>
      simp only [readBody, Fin.isValue, List.cons_append, List.nil_append, runBlock_cons, execInstr_mul,
        hregs, readStateB, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Matrix.cons_val,
        Matrix.cons_val_one, Matrix.cons_val_zero, hmul, execInstr_div, Function.update_self, hdiv,
        execInstr_mod, hmod, execInstr_load, execInstr_shr, Function.update_idem, execInstr_band,
        Nat.and_two_pow_sub_one_eq_mod, execInstr_add, Nat.mod_add_mod, execInstr_store, hk1, execInstr_imm,
        Nat.zero_mod, runBlock_nil, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Nat.add_left_cancel_iff]

/-- A loop-head state with its own program counter written back is unchanged. -/
theorem readStateB_eta (m : ℕ → ℕ) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    ({ readStateB m base S0 w t y k with pc := base } : RAMState) = readStateB m base S0 w t y k := by
  refine ramState_eq_of _ _ ?_ ?_ ?_
  · simp
  · simp
  · intro d; simp

/-- The loop test holds exactly when the counter is below `t`. -/
theorem readCond_evalB (m : ℕ → ℕ) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    readCond.eval (readStateB m base S0 w t y k) ↔ k < t := by
  simp [Cond.eval, readStateB_regs_eq]

/-- At the exit the test fails. -/
theorem readCond_falseB (m : ℕ → ℕ) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) :
    ¬ readCond.eval (readStateB m base S0 w t y t) := by
  rw [readCond_evalB]
  exact lt_irrefl t

/-- Running the test at a masked memory. -/
theorem runBlock_readCondB (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    runBlock readCond.code E (readStateB m base S0 w t y k)
      = { pc := base + 1,
          regs := Function.update (readStateB m base S0 w t y k).regs r14
            ((if k < t then 1 else 0) % 2 ^ E.W),
          mem := readMemB (decoderAllocEnd t) m S0 w y k } := by
  have hcode : readCond.code = [iLt r14 r5 r0] := rfl
  rw [hcode, runBlock_cons, runBlock_nil, execInstr_lt]
  dsimp only [readStateB]
  try rfl

theorem runBlock_readCondB_of_lt (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (y : Fin (t * w) → ZMod 2) (k : ℕ) (hW : 1 < 2 ^ E.W) (hk : k < t) :
    runBlock readCond.code E (readStateB m base S0 w t y k)
      = ⟨base + 1, Function.update (readStateB m base S0 w t y k).regs r14 1,
          readMemB (decoderAllocEnd t) m S0 w y k⟩ := by
  rw [runBlock_readCondB, if_pos hk, Nat.mod_eq_of_lt hW]

theorem runBlock_readCondB_of_ge (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (y : Fin (t * w) → ZMod 2) (k : ℕ) (hk : ¬ k < t) :
    runBlock readCond.code E (readStateB m base S0 w t y k)
      = ⟨base + 1, Function.update (readStateB m base S0 w t y k).regs r14 0,
          readMemB (decoderAllocEnd t) m S0 w y k⟩ := by
  rw [runBlock_readCondB, if_neg hk, Nat.zero_mod]

theorem runBlock_readCondB_exit (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (y : Fin (t * w) → ZMod 2) :
    runBlock readCond.code E (readStateB m base S0 w t y t)
      = ⟨base + 1, (readStateB m base S0 w t y t).regs,
          readMemB (decoderAllocEnd t) m S0 w y t⟩ := by
  have h0 : (readStateB m base S0 w t y t).regs r14 = 0 := readStateB_r14 m base S0 w t y t
  have h := runBlock_readCondB_of_ge E m base S0 w t y t (lt_irrefl t)
  rw [update_zero_eq _ h0] at h
  exact h

/-- The body entry state, in the shape the loop rule produces. -/
theorem readBodyInB_eq (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) (k : ℕ)
    (hW : 1 < 2 ^ E.W) (hk : k < t) :
    ({ runBlock readCond.code E (readStateB m base S0 w t y k) with
        pc := base + readCond.code.length + 1 } : RAMState) = readBodyInB m base S0 w t y k := by
  have hcl : readCond.code.length = 1 := readCond_code_length
  have hrun := runBlock_readCondB_of_lt E m base S0 w t y k hW hk
  refine ramState_eq_of _ _ ?_ ?_ ?_
  · simp only [readBodyInB]
    rw [hcl]
  · simp only [readBodyInB]
    rw [hrun]
  · intro d
    simp only [readBodyInB]
    rw [hrun]

/-- The body of the read loop, as a `Sem` run, at a masked memory. -/
theorem readBody_semB (P : Program) (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (y : Fin (t * w) → ZMod 2) (k : ℕ) (hAt : At P (base + 2) readBody)
    (hW : 1 < 2 ^ E.W) (hW8 : E.W = 8 * w) (hwe : w ≤ E.W) (hw : 0 < w)
    (hmul : k * w % 2 ^ E.W = k * w) (hdiv : k * w / (8 * w) % 2 ^ E.W = k / 8)
    (hmod : k * w % (8 * w) % 2 ^ E.W = k % 8 * w) (haddr : (S0 + 2 * k) % 2 ^ E.W = S0 + 2 * k)
    (hk1 : (k + 1) % 2 ^ E.W = k + 1) (hmask : (2 ^ w - 1) % 2 ^ E.W = 2 ^ w - 1)
    (hword : k / 8 < S0)
    (hpk : packMem (8 * w) y (k / 8) % 2 ^ E.W = packMem (8 * w) y (k / 8))
    (hSN : S0 ≤ decoderAllocEnd t) (hkN : S0 + 2 * k < decoderAllocEnd t) :
    Sem P E (base + 2) (base + 18) (readBodyInB m base S0 w t y k)
      (fun c s' => c = 16 ∧ s' = { readStateB m base S0 w t y (k + 1) with pc := base + 18 }) := by
  refine Sem.mono (Sem.block P E (base + 2) readBody (readBodyInB m base S0 w t y k) hAt
    (by simp [readBody]) rfl) ?_
  intro c s' hQ
  obtain ⟨hc, hs⟩ := hQ
  refine ⟨?_, ?_⟩
  · rw [hc, readBody_length]
  · rw [hs]
    exact readBody_specB E m base S0 w t k y (readBodyInB m base S0 w t y k) rfl rfl rfl hW8 hwe hw
      hmul hdiv hmod haddr hk1 hmask hword hpk hSN hkN

/-- The iteration *after* the test: body entry back to the loop head, at a masked memory. -/
theorem readBodyIterB (P : Program) (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (y : Fin (t * w) → ZMod 2) (k : ℕ) (hAt : At P base (Stmt.compile readLoopStmt base))
    (hW : 1 < 2 ^ E.W) (hW8 : E.W = 8 * w) (hwe : w ≤ E.W) (hw : 0 < w) (hk : k < t)
    (hmul : k * w % 2 ^ E.W = k * w) (hdiv : k * w / (8 * w) % 2 ^ E.W = k / 8)
    (hmod : k * w % (8 * w) % 2 ^ E.W = k % 8 * w) (haddr : (S0 + 2 * k) % 2 ^ E.W = S0 + 2 * k)
    (hk1 : (k + 1) % 2 ^ E.W = k + 1) (hmask : (2 ^ w - 1) % 2 ^ E.W = 2 ^ w - 1)
    (hword : k / 8 < S0)
    (hpk : packMem (8 * w) y (k / 8) % 2 ^ E.W = packMem (8 * w) y (k / 8))
    (hSN : S0 ≤ decoderAllocEnd t) (hkN : S0 + 2 * k < decoderAllocEnd t) :
    Sem P E (base + readCond.code.length + 1) base
      ({ runBlock readCond.code E (readStateB m base S0 w t y k) with
        pc := base + readCond.code.length + 1 } : RAMState)
      (fun c s' => c = 17 ∧ s' = readStateB m base S0 w t y (k + 1)) := by
  obtain ⟨hjz, hbodyAt, hjmp⟩ := at_loop_read hAt
  have hbody := readBody_semB P E m base S0 w t y k hbodyAt hW hW8 hwe hw hmul hdiv hmod haddr hk1
    hmask hword hpk hSN hkN
  rw [readBodyInB_eq E m base S0 w t y k hW hk]
  refine Sem.jmp_append (hAt := hjmp) ?_
  refine Sem.mono hbody ?_
  intro c s' hQ
  obtain ⟨hc, hs⟩ := hQ
  refine ⟨by omega, ?_⟩
  rw [hs]
  exact readStateB_eta m base S0 w t y (k + 1)

/-- The exit state of the read loop at a masked memory. -/
theorem readLoop_exit_stateB (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) :
    ({ runBlock readCond.code E (readStateB m base S0 w t y t) with
        pc := base + readCond.code.length + (Stmt.code readBody).len + 2 } : RAMState)
      = { readStateB m base S0 w t y t with pc := base + 19 } := by
  have hcl : readCond.code.length = 1 := readCond_code_length
  have hbl : (Stmt.code readBody).len = 16 := readBody_length
  have hrun := runBlock_readCondB_exit E m base S0 w t y
  rw [hrun]
  rfl

/-- **The read loop at a masked memory.** -/
theorem readLoop_specB (P : Program) (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (y : Fin (t * w) → ZMod 2)
    (hAt : At P base (Stmt.compile readLoopStmt base)) (hW : 1 < 2 ^ E.W) (hW8 : E.W = 8 * w)
    (hwe : w ≤ E.W) (hw : 0 < w)
    (hmul : ∀ k < t, k * w % 2 ^ E.W = k * w)
    (hdiv : ∀ k < t, k * w / (8 * w) % 2 ^ E.W = k / 8)
    (hmod : ∀ k < t, k * w % (8 * w) % 2 ^ E.W = k % 8 * w)
    (haddr : ∀ k < t, (S0 + 2 * k) % 2 ^ E.W = S0 + 2 * k)
    (hk1 : ∀ k < t, (k + 1) % 2 ^ E.W = k + 1)
    (hmask : (2 ^ w - 1) % 2 ^ E.W = 2 ^ w - 1)
    (hword : ∀ k < t, k / 8 < S0)
    (hpk : ∀ k < t, packMem (8 * w) y (k / 8) % 2 ^ E.W = packMem (8 * w) y (k / 8))
    (hSN : S0 ≤ decoderAllocEnd t) (hSt : S0 + 2 * t ≤ decoderAllocEnd t) :
    Sem P E base (base + 19) (readStateB m base S0 w t y 0)
      (fun c s' => c ≤ 19 * t + 2 ∧ s' = { readStateB m base S0 w t y t with pc := base + 19 }) := by
  have hloop := Sem.loop P E base readCond (Stmt.code readBody) hAt hW t
    (fun j => readStateB m base S0 w t y j) (fun _ => 17)
    (fun j => rfl)
    (fun j hj => (readCond_evalB m base S0 w t y j).mpr hj)
    (readCond_falseB m base S0 w t y)
    (fun j hj => readBodyIterB P E m base S0 w t y j hAt hW hW8 hwe hw hj (hmul j hj) (hdiv j hj)
      (hmod j hj) (haddr j hj) (hk1 j hj) hmask (hword j hj) (hpk j hj) hSN (by omega))
  have h19 : ((readCond.code.length + 1) + 17) = 19 := by
    rw [readCond_code_length]
  have hsum19 : (∑ j ∈ Finset.range t, (19 : ℕ)) = 19 * t := sum_range_const_mul t 19
  have hsum : (∑ j ∈ Finset.range t, ((readCond.code.length + 1) + 17)) = 19 * t := by
    rw [← hsum19]
    exact Finset.sum_congr rfl (fun j _ => h19)
  refine Sem.mono hloop ?_
  intro c s' hQ
  obtain ⟨hle, hs⟩ := hQ
  refine ⟨?_, ?_⟩
  · rw [hsum] at hle
    rw [readCond_code_length] at hle
    omega
  · rw [hs]
    exact readLoop_exit_stateB E m base S0 w t y

/-! ### The expansion loop at a masked memory -/

/-- The expansion-loop memory, masked at `N`. -/
noncomputable def expandMemB {w : ℕ} (N t : ℕ) (m : ℕ → ℕ) (S0 : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) {M : ℕ} (y : Fin M → ZMod 2) (k : ℕ) : ℕ → ℕ :=
  maskMem N (expandMem S0 b y t k) m

theorem expandMemB_zero {w M : ℕ} {N t : ℕ} {m : ℕ → ℕ} (S0 : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin M → ZMod 2) :
    expandMemB N t m S0 b y 0 = readMemB N m S0 w y t := by
  unfold expandMemB readMemB
  rw [expandMem_zero]

theorem expandMemB_succ {w M : ℕ} {N t : ℕ} {m : ℕ → ℕ} {S0 : ℕ}
    {b : Module.Basis (Fin w) (ZMod 2) F} {y : Fin M → ZMod 2} {k : ℕ}
    (hk : S0 + 2 * k + 1 < N) :
    expandMemB N t m S0 b y (k + 1)
      = Function.update (expandMemB N t m S0 b y k) (S0 + 2 * k + 1)
          (enc b (eSeq b y (2 * k + 1))) := by
  unfold expandMemB
  rw [expandMem_succ]
  exact maskMem_update hk

theorem expandMemB_get {w M : ℕ} {N t : ℕ} {m : ℕ → ℕ} {S0 : ℕ}
    {b : Module.Basis (Fin w) (ZMod 2) F} {y : Fin M → ZMod 2} {k a : ℕ}
    (hN : S0 + a < N) (ht : a / 2 < t) (hk : a % 2 = 1 → a / 2 < k) :
    expandMemB N t m S0 b y k (S0 + a) = enc b (eSeq b y a) := by
  unfold expandMemB
  rw [maskMem_lt hN]
  exact expandMem_get S0 b y t k a ht hk

theorem expandMemB_src {w M : ℕ} {N t : ℕ} {m : ℕ → ℕ} {S0 : ℕ}
    {b : Module.Basis (Fin w) (ZMod 2) F} {y : Fin M → ZMod 2} {k : ℕ}
    (hN : S0 + k < N) (hk : k < t) :
    expandMemB N t m S0 b y k (S0 + k) = enc b (eSeq b y k) :=
  expandMemB_get (a := k) (k := k) hN (by omega) (fun _ => by omega)

theorem expandMemB_complete {w M : ℕ} {N t : ℕ} {m : ℕ → ℕ} {S0 : ℕ}
    {b : Module.Basis (Fin w) (ZMod 2) F} {y : Fin M → ZMod 2} {a : ℕ}
    (hN : S0 + a < N) (ha : a < 2 * t) :
    expandMemB N t m S0 b y t (S0 + a) = enc b (eSeq b y a) :=
  expandMemB_get (a := a) (k := t) hN (by omega) (fun _ => by omega)

theorem expandMemB_after {w M : ℕ} {N t : ℕ} (m : ℕ → ℕ) (S0 : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin M → ZMod 2) (addr : ℕ) (haddr : N ≤ addr) :
    expandMemB N t m S0 b y t addr = m addr := by
  unfold expandMemB
  exact maskMem_ge haddr

/-- The expansion-loop state, at a memory masked at `decoderAllocEnd t`. -/
noncomputable def expandStateB (m : ℕ → ℕ) (base S0 w t : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin (t * w) → ZMod 2) (k : ℕ) : RAMState where
  pc := base
  regs := ![t, w, S0, 2 ^ w - 1, detSqBase w, k, 0, 0, 1, 0, 0, 0, 0, 0, 0, 8 * w]
  mem := expandMemB (decoderAllocEnd t) t m S0 b y k

attribute [local simp] expandStateB

theorem expandStateB_regs_eq (m : ℕ → ℕ) (base S0 w t : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    (expandStateB m base S0 w t b y k).regs
      = ![t, w, S0, 2 ^ w - 1, detSqBase w, k, 0, 0, 1, 0, 0, 0, 0, 0, 0, 8 * w] := rfl

@[simp] theorem expandStateB_r14 (m : ℕ → ℕ) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    (expandStateB m base S0 w t b y k).regs r14 = 0 := by
  rw [expandStateB_regs_eq]
  simp

/-- The state at the entry of the expansion body, at a masked memory. -/
noncomputable def expandBodyInB (m : ℕ → ℕ) (base S0 w t : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin (t * w) → ZMod 2) (k : ℕ) : RAMState where
  pc := base + 2
  regs := Function.update (expandStateB m base S0 w t b y k).regs r14 1
  mem := expandMemB (decoderAllocEnd t) t m S0 b y k

/-- A loop-head state with its own program counter written back is unchanged. -/
theorem expandStateB_eta (m : ℕ → ℕ) (base S0 w t : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    ({ expandStateB m base S0 w t b y k with pc := base } : RAMState)
      = expandStateB m base S0 w t b y k := by
  refine ramState_eq_of _ _ ?_ ?_ ?_
  · simp
  · simp
  · intro d; simp

/-- The loop test for the expansion loop, at a masked memory. -/
theorem expandCond_evalB (m : ℕ → ℕ) (base S0 w t : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    readCond.eval (expandStateB m base S0 w t b y k) ↔ k < t := by
  simp [Cond.eval, expandStateB_regs_eq]

theorem expandCond_falseB (m : ℕ → ℕ) (base S0 w t : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin (t * w) → ZMod 2) : ¬ readCond.eval (expandStateB m base S0 w t b y t) := by
  rw [expandCond_evalB]
  exact lt_irrefl t

/-- Running the expansion test at a masked memory. -/
theorem runBlock_expandCondB (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    runBlock readCond.code E (expandStateB m base S0 w t b y k)
      = { pc := base + 1,
          regs := Function.update (expandStateB m base S0 w t b y k).regs r14
            ((if k < t then 1 else 0) % 2 ^ E.W),
          mem := expandMemB (decoderAllocEnd t) t m S0 b y k } := by
  have hcode : readCond.code = [iLt r14 r5 r0] := rfl
  rw [hcode, runBlock_cons, runBlock_nil, execInstr_lt]
  dsimp only [expandStateB]
  try rfl

theorem runBlock_expandCondB_of_lt (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) (k : ℕ)
    (hW : 1 < 2 ^ E.W) (hk : k < t) :
    runBlock readCond.code E (expandStateB m base S0 w t b y k)
      = ⟨base + 1, Function.update (expandStateB m base S0 w t b y k).regs r14 1,
          expandMemB (decoderAllocEnd t) t m S0 b y k⟩ := by
  rw [runBlock_expandCondB, if_pos hk, Nat.mod_eq_of_lt hW]

theorem runBlock_expandCondB_of_ge (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) (k : ℕ)
    (hk : ¬ k < t) :
    runBlock readCond.code E (expandStateB m base S0 w t b y k)
      = ⟨base + 1, Function.update (expandStateB m base S0 w t b y k).regs r14 0,
          expandMemB (decoderAllocEnd t) t m S0 b y k⟩ := by
  rw [runBlock_expandCondB, if_neg hk, Nat.zero_mod]

theorem runBlock_expandCondB_exit (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) :
    runBlock readCond.code E (expandStateB m base S0 w t b y t)
      = ⟨base + 1, (expandStateB m base S0 w t b y t).regs,
          expandMemB (decoderAllocEnd t) t m S0 b y t⟩ := by
  have h0 : (expandStateB m base S0 w t b y t).regs r14 = 0 := expandStateB_r14 m base S0 w t b y t
  have h := runBlock_expandCondB_of_ge E m base S0 w t b y t (lt_irrefl t)
  rw [update_zero_eq _ h0] at h
  exact h

theorem expandBodyInB_eq (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) (k : ℕ)
    (hW : 1 < 2 ^ E.W) (hk : k < t) :
    ({ runBlock readCond.code E (expandStateB m base S0 w t b y k) with
        pc := base + readCond.code.length + 1 } : RAMState) = expandBodyInB m base S0 w t b y k := by
  have hcl : readCond.code.length = 1 := readCond_code_length
  have hrun := runBlock_expandCondB_of_lt E m base S0 w t b y k hW hk
  refine ramState_eq_of _ _ ?_ ?_ ?_
  · simp only [expandBodyInB]
    rw [hcl]
  · simp only [expandBodyInB]
    rw [hrun]
  · intro d
    simp only [expandBodyInB]
    rw [hrun]

/-- **The expansion body, as a state map, at a masked memory.** -/
theorem expandBody_specB (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t k : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) (s : RAMState)
    (hpc : s.pc = base + 2)
    (hregs : s.regs = Function.update (expandStateB m base S0 w t b y k).regs r14 1)
    (hmem : s.mem = expandMemB (decoderAllocEnd t) t m S0 b y k)
    (hsrc : (S0 + k) % 2 ^ E.W = S0 + k)
    (hsrcval : expandMemB (decoderAllocEnd t) t m S0 b y k (S0 + k) = enc b (eSeq b y k))
    (hld : enc b (eSeq b y k) % 2 ^ E.W = enc b (eSeq b y k))
    (hsq : (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = detSqBase w + enc b (eSeq b y k))
    (htab : E.det (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = sqTab b (enc b (eSeq b y k)))
    (hval : sqTab b (enc b (eSeq b y k)) = enc b (eSeq b y (2 * k + 1)))
    (hkk : (k + k) % 2 ^ E.W = k + k)
    (hkkS0 : (k + k + S0) % 2 ^ E.W = S0 + 2 * k)
    (haddr : (S0 + 2 * k + 1) % 2 ^ E.W = S0 + 2 * k + 1)
    (hk1 : (k + 1) % 2 ^ E.W = k + 1)
    (hkN : S0 + 2 * k + 1 < decoderAllocEnd t) :
    runBlock expandBody E s = { expandStateB m base S0 w t b y (k + 1) with pc := base + 18 } := by
  have hpc' : (runBlock expandBody E s).pc = base + 18 := by
    rw [runBlock_pc expandBody E s (by simp [expandBody]), hpc, expandBody_length]
  refine ramState_eq_of _ _ hpc' ?_ ?_
  · funext addr
    show (runBlock expandBody E s).mem addr
      = expandMemB (decoderAllocEnd t) t m S0 b y (k + 1) addr
    by_cases h : addr = S0 + 2 * k + 1
    · rw [h, expandMemB_succ hkN, Function.update_self]
      simp only [expandBody, Fin.isValue, List.cons_append, List.nil_append, runBlock_cons, execInstr_add,
        hregs, expandStateB, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Matrix.cons_val,
        hsrc, hmem, execInstr_load, Function.update_self, hsrcval, hld, hsq, execInstr_qDet, htab, hval, hkk,
        hkkS0, Function.update_idem, haddr, execInstr_store, hk1, execInstr_imm, Nat.zero_mod, runBlock_nil]
    · rw [expandMemB_succ hkN, Function.update_of_ne h]
      simp only [expandBody, Fin.isValue, List.cons_append, List.nil_append, runBlock_cons, execInstr_add,
        hregs, expandStateB, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Matrix.cons_val,
        hsrc, hmem, execInstr_load, Function.update_self, hsrcval, hld, hsq, execInstr_qDet, htab, hval, hkk,
        hkkS0, Function.update_idem, haddr, execInstr_store, hk1, execInstr_imm, Nat.zero_mod, runBlock_nil,
        Function.update_of_ne h]
  · intro d
    simp only [expandBody, Fin.isValue, List.cons_append, List.nil_append, runBlock_cons, execInstr_add,
      hregs, expandStateB, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Matrix.cons_val,
      hsrc, execInstr_load, Function.update_self, Nat.add_mod_mod, execInstr_qDet, hkk, hkkS0,
      Function.update_idem, haddr, execInstr_store, hk1, execInstr_imm, Nat.zero_mod, runBlock_nil]
    fin_cases d <;>
      simp only [expandBody, Fin.isValue, List.cons_append, List.nil_append, runBlock_cons, execInstr_add,
        hregs, expandStateB, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Matrix.cons_val,
        hsrc, execInstr_load, Function.update_self, Nat.add_mod_mod, execInstr_qDet, hkk, hkkS0,
        Function.update_idem, haddr, execInstr_store, hk1, execInstr_imm, Nat.zero_mod, runBlock_nil,
        Fin.zero_eta, Matrix.cons_val_zero, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
        Nat.add_left_cancel_iff]

/-- The expansion body as a `Sem` run, at a masked memory. -/
theorem expandBody_semB (P : Program) (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) (k : ℕ)
    (hAt : At P (base + 2) expandBody)
    (hsrc : (S0 + k) % 2 ^ E.W = S0 + k)
    (hsrcval : expandMemB (decoderAllocEnd t) t m S0 b y k (S0 + k) = enc b (eSeq b y k))
    (hld : enc b (eSeq b y k) % 2 ^ E.W = enc b (eSeq b y k))
    (hsq : (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = detSqBase w + enc b (eSeq b y k))
    (htab : E.det (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = sqTab b (enc b (eSeq b y k)))
    (hval : sqTab b (enc b (eSeq b y k)) = enc b (eSeq b y (2 * k + 1)))
    (hkk : (k + k) % 2 ^ E.W = k + k)
    (hkkS0 : (k + k + S0) % 2 ^ E.W = S0 + 2 * k)
    (haddr : (S0 + 2 * k + 1) % 2 ^ E.W = S0 + 2 * k + 1)
    (hk1 : (k + 1) % 2 ^ E.W = k + 1)
    (hkN : S0 + 2 * k + 1 < decoderAllocEnd t) :
    Sem P E (base + 2) (base + 18) (expandBodyInB m base S0 w t b y k)
      (fun c s' => c = 16 ∧ s' = { expandStateB m base S0 w t b y (k + 1) with pc := base + 18 }) := by
  refine Sem.mono (Sem.block P E (base + 2) expandBody (expandBodyInB m base S0 w t b y k) hAt
    (by simp [expandBody]) rfl) ?_
  intro c s' hQ
  obtain ⟨hc, hs⟩ := hQ
  refine ⟨?_, ?_⟩
  · rw [hc, expandBody_length]
  · rw [hs]
    exact expandBody_specB E m base S0 w t k b y (expandBodyInB m base S0 w t b y k) rfl rfl rfl hsrc
      hsrcval hld hsq htab hval hkk hkkS0 haddr hk1 hkN

/-- The expansion iteration after the test, at a masked memory. -/
theorem expandBodyIterB (P : Program) (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) (k : ℕ)
    (hAt : At P base (Stmt.compile expandLoopStmt base)) (hW : 1 < 2 ^ E.W) (hk : k < t)
    (hsrc : (S0 + k) % 2 ^ E.W = S0 + k)
    (hsrcval : expandMemB (decoderAllocEnd t) t m S0 b y k (S0 + k) = enc b (eSeq b y k))
    (hld : enc b (eSeq b y k) % 2 ^ E.W = enc b (eSeq b y k))
    (hsq : (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = detSqBase w + enc b (eSeq b y k))
    (htab : E.det (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = sqTab b (enc b (eSeq b y k)))
    (hval : sqTab b (enc b (eSeq b y k)) = enc b (eSeq b y (2 * k + 1)))
    (hkk : (k + k) % 2 ^ E.W = k + k)
    (hkkS0 : (k + k + S0) % 2 ^ E.W = S0 + 2 * k)
    (haddr : (S0 + 2 * k + 1) % 2 ^ E.W = S0 + 2 * k + 1)
    (hk1 : (k + 1) % 2 ^ E.W = k + 1)
    (hkN : S0 + 2 * k + 1 < decoderAllocEnd t) :
    Sem P E (base + readCond.code.length + 1) base
      ({ runBlock readCond.code E (expandStateB m base S0 w t b y k) with
        pc := base + readCond.code.length + 1 } : RAMState)
      (fun c s' => c = 17 ∧ s' = expandStateB m base S0 w t b y (k + 1)) := by
  obtain ⟨hjz, hbodyAt, hjmp⟩ := at_loop_expand hAt
  have hbody := expandBody_semB P E m base S0 w t b y k hbodyAt hsrc hsrcval hld hsq htab hval hkk hkkS0
    haddr hk1 hkN
  rw [expandBodyInB_eq E m base S0 w t b y k hW hk]
  refine Sem.jmp_append (hAt := hjmp) ?_
  refine Sem.mono hbody ?_
  intro c s' hQ
  obtain ⟨hc, hs⟩ := hQ
  refine ⟨by omega, ?_⟩
  rw [hs]
  exact expandStateB_eta m base S0 w t b y (k + 1)

/-- The exit state of the expansion loop, at a masked memory. -/
theorem expandLoop_exit_stateB (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) :
    ({ runBlock readCond.code E (expandStateB m base S0 w t b y t) with
        pc := base + readCond.code.length + (Stmt.code expandBody).len + 2 } : RAMState)
      = { expandStateB m base S0 w t b y t with pc := base + 19 } := by
  have hcl : readCond.code.length = 1 := readCond_code_length
  have hbl : (Stmt.code expandBody).len = 16 := expandBody_length
  have hrun := runBlock_expandCondB_exit E m base S0 w t b y
  rw [hrun]
  rfl

/-- **The expansion loop at a masked memory.** -/
theorem expandLoop_specB (P : Program) (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2)
    (hAt : At P base (Stmt.compile expandLoopStmt base)) (hW : 1 < 2 ^ E.W)
    (hsrc : ∀ k < t, (S0 + k) % 2 ^ E.W = S0 + k)
    (hsrcval : ∀ k < t, expandMemB (decoderAllocEnd t) t m S0 b y k (S0 + k) = enc b (eSeq b y k))
    (hld : ∀ k < t, enc b (eSeq b y k) % 2 ^ E.W = enc b (eSeq b y k))
    (hsq : ∀ k < t, (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = detSqBase w + enc b (eSeq b y k))
    (htab : ∀ k < t, E.det (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = sqTab b (enc b (eSeq b y k)))
    (hval : ∀ k < t, sqTab b (enc b (eSeq b y k)) = enc b (eSeq b y (2 * k + 1)))
    (hkk : ∀ k < t, (k + k) % 2 ^ E.W = k + k)
    (hkkS0 : ∀ k < t, (k + k + S0) % 2 ^ E.W = S0 + 2 * k)
    (haddr : ∀ k < t, (S0 + 2 * k + 1) % 2 ^ E.W = S0 + 2 * k + 1)
    (hk1 : ∀ k < t, (k + 1) % 2 ^ E.W = k + 1)
    (hSt : S0 + 2 * t ≤ decoderAllocEnd t) :
    Sem P E base (base + 19) (expandStateB m base S0 w t b y 0)
      (fun c s' => c ≤ 19 * t + 2 ∧ s' = { expandStateB m base S0 w t b y t with pc := base + 19 }) := by
  have hloop := Sem.loop P E base readCond (Stmt.code expandBody) hAt hW t
    (fun j => expandStateB m base S0 w t b y j) (fun _ => 17)
    (fun j => rfl)
    (fun j hj => (expandCond_evalB m base S0 w t b y j).mpr hj)
    (expandCond_falseB m base S0 w t b y)
    (fun j hj => expandBodyIterB P E m base S0 w t b y j hAt hW hj (hsrc j hj) (hsrcval j hj)
      (hld j hj) (hsq j hj) (htab j hj) (hval j hj) (hkk j hj) (hkkS0 j hj) (haddr j hj) (hk1 j hj)
      (by omega))
  have h19 : ((readCond.code.length + 1) + 17) = 19 := by
    rw [readCond_code_length]
  have hsum19 : (∑ j ∈ Finset.range t, (19 : ℕ)) = 19 * t := sum_range_const_mul t 19
  have hsum : (∑ j ∈ Finset.range t, ((readCond.code.length + 1) + 17)) = 19 * t := by
    rw [← hsum19]
    exact Finset.sum_congr rfl (fun j _ => h19)
  refine Sem.mono hloop ?_
  intro c s' hQ
  obtain ⟨hle, hs⟩ := hQ
  refine ⟨?_, ?_⟩
  · rw [hsum] at hle
    rw [readCond_code_length] at hle
    omega
  · rw [hs]
    exact expandLoop_exit_stateB E m base S0 w t b y

/-- **The array is complete when the expansion loop exits**, at a masked memory. -/
theorem expandLoop_resultB (P : Program) (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2)
    (hAt : At P base (Stmt.compile expandLoopStmt base)) (hW : 1 < 2 ^ E.W)
    (hsrc : ∀ k < t, (S0 + k) % 2 ^ E.W = S0 + k)
    (hsrcval : ∀ k < t, expandMemB (decoderAllocEnd t) t m S0 b y k (S0 + k) = enc b (eSeq b y k))
    (hld : ∀ k < t, enc b (eSeq b y k) % 2 ^ E.W = enc b (eSeq b y k))
    (hsq : ∀ k < t, (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = detSqBase w + enc b (eSeq b y k))
    (htab : ∀ k < t, E.det (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = sqTab b (enc b (eSeq b y k)))
    (hval : ∀ k < t, sqTab b (enc b (eSeq b y k)) = enc b (eSeq b y (2 * k + 1)))
    (hkk : ∀ k < t, (k + k) % 2 ^ E.W = k + k)
    (hkkS0 : ∀ k < t, (k + k + S0) % 2 ^ E.W = S0 + 2 * k)
    (haddr : ∀ k < t, (S0 + 2 * k + 1) % 2 ^ E.W = S0 + 2 * k + 1)
    (hk1 : ∀ k < t, (k + 1) % 2 ^ E.W = k + 1)
    (hSt : S0 + 2 * t ≤ decoderAllocEnd t) :
    Sem P E base (base + 19) (expandStateB m base S0 w t b y 0)
      (fun c s' => c ≤ 19 * t + 2 ∧ s' = { expandStateB m base S0 w t b y t with pc := base + 19 } ∧
        ∀ a, a < 2 * t → s'.mem (S0 + a) = enc b (eSeq b y a)) := by
  refine Sem.mono (expandLoop_specB P E m base S0 w t b y hAt hW hsrc hsrcval hld hsq htab hval hkk
    hkkS0 haddr hk1 hSt) ?_
  intro c s' hQ
  obtain ⟨hle, hs⟩ := hQ
  refine ⟨hle, hs, ?_⟩
  intro a ha
  rw [hs]
  exact expandMemB_complete (by omega) ha

/-! ### The read prologue and the front of the stage, at a masked memory -/

/-- `readMem` at counter `0` is `hintMem`, so the mask at `0` is the ambient memory itself. -/
theorem readMemB_zero {M : ℕ} {N : ℕ} {m : ℕ → ℕ} {S0 w : ℕ} {y : Fin M → ZMod 2}
    (hS0 : S0 = wordsOf (8 * w) M)
    (hmem : ∀ a, a < N → m a = hintMem (8 * w) y [] a) :
    readMemB N m S0 w y 0 = m := by
  funext a
  by_cases ha : a < N
  · rw [readMemB, maskMem_lt ha]
    have hz : readMem S0 w y 0 a = hintMem (8 * w) y [] a := by
      rw [readMem_zero]
      simp only [hS0, hintMem, List.getD_nil]
    rw [hz, hmem a ha]
  · rw [readMemB, maskMem_ge (by omega)]

/-- **The prologue, at a masked memory.**  `paramBody` reads only registers, so it leaves `m` alone. -/
theorem paramBodyAt_specB (E : RAMEnv) (m : ℕ → ℕ) (base N t w S0 : ℕ)
    (y : Fin (t * w) → ZMod 2)
    (hS0 : S0 = wordsOf (8 * w) (t * w)) (hW : E.W = 8 * w) (hw1 : 1 ≤ w)
    (h0 : E.det 0 % 2 ^ E.W = t) (h1 : E.det 1 % 2 ^ E.W = w) (h4 : E.det 4 % 2 ^ E.W = S0)
    (h5 : E.det 5 % 2 ^ E.W = 2 ^ w - 1) (h6 : E.det 6 % 2 ^ E.W = detSqBase w)
    (h12 : E.det 12 % 2 ^ E.W = 8 * w) (h1W : (1 : ℕ) % 2 ^ E.W = 1)
    (hmem : ∀ a, a < decoderAllocEnd t → m a = hintMem (8 * w) y [] a) :
    runBlock paramBody E ⟨base, (decoderStart (8 * w) y []).regs, m⟩
      = readStateB m (base + 14) S0 w t y 0 := by
  have hmem0 : readMemB (decoderAllocEnd t) m S0 w y 0 = m := readMemB_zero hS0 hmem
  have hpc' : (runBlock paramBody E ⟨base, (decoderStart (8 * w) y []).regs, m⟩).pc
      = base + 14 := by
    rw [runBlock_pc paramBody E _ (by simp [paramBody]), paramBody_length]
  have h4m : (4 : ℕ) % 2 ^ E.W = 4 := Nat.mod_eq_of_lt (by
    have hp : (2 : ℕ) ^ 8 ≤ 2 ^ E.W := by rw [hW]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega)
  have h5m : (5 : ℕ) % 2 ^ E.W = 5 := Nat.mod_eq_of_lt (by
    have hp : (2 : ℕ) ^ 8 ≤ 2 ^ E.W := by rw [hW]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega)
  have h6m : (6 : ℕ) % 2 ^ E.W = 6 := Nat.mod_eq_of_lt (by
    have hp : (2 : ℕ) ^ 8 ≤ 2 ^ E.W := by rw [hW]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega)
  have h12m : (12 : ℕ) % 2 ^ E.W = 12 := Nat.mod_eq_of_lt (by
    have hp : (2 : ℕ) ^ 8 ≤ 2 ^ E.W := by rw [hW]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega)
  refine ramState_eq_of _ _ hpc' ?_ ?_
  · funext addr
    show (runBlock paramBody E ⟨base, (decoderStart (8 * w) y []).regs, m⟩).mem addr
      = readMemB (decoderAllocEnd t) m S0 w y 0 addr
    rw [hmem0]
    simp only [paramBody, Fin.isValue, List.cons_append, List.nil_append, runBlock_cons, execInstr_imm,
      Nat.zero_mod, execInstr_qDet, Function.update_self, runBlock_nil]
  · intro d
    simp only [paramBody, readStateB, h0, h1, h4, h5, h6, h12, h1W, h4m, h5m, h6m, h12m,
      decoderStart, initState, runBlock_cons, runBlock_nil, execInstr_imm, execInstr_qDet,
      Function.update_idem]
    fin_cases d <;>
      simp [paramBody, readStateB, h0, h1, h4, h5, h6, h12, h1W, h4m, h5m, h6m, h12m,
        decoderStart, initState, runBlock_cons, runBlock_nil]

/-- **The read loop's input stage, at a masked memory.** -/
theorem inputRead_specB {F : Type} [Field F] [Algebra (ZMod 2) F]
    (E : RAMEnv) (P : Program) (m : ℕ → ℕ) (base N t w : ℕ) (y : Fin (t * w) → ZMod 2)
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (hAt : At P base (Stmt.compile inputReadStmt base))
    (hW : E.W = 8 * w) (hw1 : 1 ≤ w) (hNw : N < 2 ^ w) (htN : t ≤ N)
    (hdet : E.det = detStd t N b ι)
    (hmem : ∀ a, a < decoderAllocEnd t → m a = hintMem (8 * w) y [] a) :
    Sem P E base (base + 33) ⟨base, (decoderStart (8 * w) y []).regs, m⟩
      (fun k z => k ≤ 19 * t + 16 ∧
        z = { readStateB m (base + 14) (wordsOf (8 * w) (t * w)) w t y t with pc := base + 33 }) := by
  have hpos : 0 < w := by omega
  have h2w : (2 : ℕ) ^ w ≤ 2 ^ (8 * w) :=
    Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega : w ≤ 8 * w)
  have htW : t < 2 ^ (8 * w) := lt_of_le_of_lt htN (lt_of_lt_of_le hNw h2w)
  have hwW : w < 2 ^ (8 * w) := lt_of_lt_of_le (Nat.lt_two_pow_self (n := w)) h2w
  have hS0W : wordsOf (8 * w) (t * w) < 2 ^ (8 * w) :=
    lt_of_le_of_lt (wordsOf_le w t hw1) htW
  have hmaskW : 2 ^ w - 1 < 2 ^ (8 * w) := by
    have := Nat.two_pow_pos w
    omega
  have h1E : (1 : ℕ) < 2 ^ E.W := by
    rw [hW]
    have h0 : 0 < 8 * w := by omega
    have h := Nat.pow_lt_pow_right (by norm_num : 1 < 2) h0
    simpa using h
  have h0 : E.det 0 % 2 ^ E.W = t := by
    rw [hdet, detStd_hdr t N w b ι (by norm_num : (0 : ℕ) < 13), hdrTab_zero, hW]
    exact Nat.mod_eq_of_lt htW
  have h1 : E.det 1 % 2 ^ E.W = w := by
    rw [hdet, detStd_hdr t N w b ι (by norm_num : (1 : ℕ) < 13), hdrTab_one, hW]
    exact Nat.mod_eq_of_lt hwW
  have h4 : E.det 4 % 2 ^ E.W = wordsOf (8 * w) (t * w) := by
    rw [hdet, detStd_hdr t N w b ι (by norm_num : (4 : ℕ) < 13), hdrTab_four, hW]
    exact Nat.mod_eq_of_lt hS0W
  have h5 : E.det 5 % 2 ^ E.W = 2 ^ w - 1 := by
    rw [hdet, detStd_hdr t N w b ι (by norm_num : (5 : ℕ) < 13), hdrTab_five, hW]
    exact Nat.mod_eq_of_lt hmaskW
  have h6 : E.det 6 % 2 ^ E.W = detSqBase w := by
    rw [hdet, detStd_hdr t N w b ι (by norm_num : (6 : ℕ) < 13), hdrTab_six, hW]
    exact Nat.mod_eq_of_lt (detSqBase_lt hw1)
  have h12 : E.det 12 % 2 ^ E.W = 8 * w := by
    rw [hdet, detStd_hdr t N w b ι (by norm_num : (12 : ℕ) < 13), hdrTab_twelve, hW]
    exact Nat.mod_eq_of_lt (Nat.lt_two_pow_self (n := 8 * w))
  have h1W : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt h1E
  have hmul : ∀ k < t, k * w % 2 ^ E.W = k * w := by
    intro k hk
    rw [hW]
    exact Nat.mod_eq_of_lt (mul_lt_two_pow_eight hw1 hNw (lt_of_lt_of_le hk htN))
  have hdiv : ∀ k < t, k * w / (8 * w) % 2 ^ E.W = k / 8 := by
    intro k hk
    rw [mul_div_eight w hpos k, hW]
    refine Nat.mod_eq_of_lt ?_
    calc k / 8 ≤ k := Nat.div_le_self _ _
      _ < 2 ^ w := by omega
      _ ≤ 2 ^ (8 * w) := h2w
  have hmod : ∀ k < t, k * w % (8 * w) % 2 ^ E.W = k % 8 * w := by
    intro k hk
    rw [mul_mod_eight, hW]
    refine Nat.mod_eq_of_lt ?_
    calc k % 8 * w ≤ 7 * w := Nat.mul_le_mul_right w (by
          have := Nat.mod_lt k (by norm_num : (0 : ℕ) < 8)
          omega)
      _ < 8 * w := by omega
      _ ≤ 2 ^ (8 * w) := le_of_lt (Nat.lt_two_pow_self (n := 8 * w))
  have haddr : ∀ k < t, (wordsOf (8 * w) (t * w) + 2 * k) % 2 ^ E.W
      = wordsOf (8 * w) (t * w) + 2 * k := by
    intro k hk
    rw [hW]
    exact Nat.mod_eq_of_lt (addr_lt_two_pow_eight hw1
      (lt_of_le_of_lt htN hNw) (wordsOf_le w t hw1) hk)
  have hk1 : ∀ k < t, (k + 1) % 2 ^ E.W = k + 1 := by
    intro k hk
    rw [hW]
    refine Nat.mod_eq_of_lt ?_
    have h1' : k + 1 ≤ t := by omega
    omega
  have hmask : (2 ^ w - 1) % 2 ^ E.W = 2 ^ w - 1 := by
    rw [hW]
    exact Nat.mod_eq_of_lt hmaskW
  have hword : ∀ k < t, k / 8 < wordsOf (8 * w) (t * w) := by
    intro k hk
    rw [wordsOf_eight w t hpos]
    omega
  have hpk : ∀ k < t, packMem (8 * w) y (k / 8) % 2 ^ E.W = packMem (8 * w) y (k / 8) := by
    intro k hk
    rw [hW]
    exact Nat.mod_eq_of_lt (packMem_lt hpos y (k / 8))
  have hS0le : wordsOf (8 * w) (t * w) ≤ decoderAllocEnd t := by
    have h1' : wordsOf (8 * w) (t * w) ≤ t := wordsOf_le w t hw1
    rw [decoderAllocEnd_eq]
    omega
  have hSt : wordsOf (8 * w) (t * w) + 2 * t ≤ decoderAllocEnd t :=
    frontBound (wordsOf_le w t hw1)
  obtain ⟨hParamAt, hLoopAt⟩ := At.seqStmt hAt
  have hPro : Sem P E base (base + 14) ⟨base, (decoderStart (8 * w) y []).regs, m⟩
      (fun k z => k ≤ 14 ∧ z = readStateB m (base + 14) (wordsOf (8 * w) (t * w)) w t y 0) := by
    refine Sem.mono (Sem.block P E base paramBody _ hParamAt (by simp [paramBody]) rfl) ?_
    intro k z hQ
    have hk : k = 14 := hQ.1
    exact ⟨by omega, hQ.2.trans (paramBodyAt_specB E m base N t w (wordsOf (8 * w) (t * w)) y rfl
      hW hw1 h0 h1 h4 h5 h6 h12 h1W hmem)⟩
  have hLoop := readLoop_specB P E m (base + 14) (wordsOf (8 * w) (t * w)) w t y hLoopAt
    h1E hW (by rw [hW]; omega) hpos hmul hdiv hmod haddr hk1 hmask hword hpk hS0le hSt
  have hFull := Sem.seq_bound hPro (fun z _ hz => by subst z; exact hLoop)
  exact Sem.mono hFull (fun k z hQ => ⟨by omega, hQ.2⟩)

/-- **The read loop's output is the expansion's input, at a masked memory.** -/
theorem readToExpansion_specB {F : Type} [Field F] [Algebra (ZMod 2) F]
    (E : RAMEnv) (m : ℕ → ℕ) (readBase pc S0 w t : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin (t * w) → ZMod 2) :
    runBlock [iImm r5 0] E { readStateB m readBase S0 w t y t with pc := pc }
      = expandStateB m (pc + 1) S0 w t b y 0 := by
  apply ramState_eq_of
  · rfl
  · show readMemB (decoderAllocEnd t) m S0 w y t
      = (expandStateB m (pc + 1) S0 w t b y 0).mem
    exact (expandMemB_zero S0 b y).symm
  · intro r
    fin_cases r <;> simp [runBlock_cons, runBlock_nil, execInstr, readStateB, expandStateB]

/-- **The expansion stage at a masked memory.** -/
theorem expandAt_specB {F : Type} [Field F] [Algebra (ZMod 2) F]
    (P : Program) (E : RAMEnv) (m : ℕ → ℕ) (N t w base : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) (ι : ℕ → F)
    (hAt : At P base (Stmt.compile expandLoopStmt base))
    (hW : E.W = 8 * w) (hw1 : 1 ≤ w) (hNw : N < 2 ^ w) (htN : t ≤ N)
    (hdet : E.det = detStd t N b ι) :
    Sem P E base (base + 19) (expandStateB m base (wordsOf (8 * w) (t * w)) w t b y 0)
      (fun k z => k ≤ 19 * t + 2 ∧
        z = { expandStateB m base (wordsOf (8 * w) (t * w)) w t b y t with pc := base + 19 } ∧
        ∀ a, a < 2 * t → z.mem (wordsOf (8 * w) (t * w) + a) = enc b (eSeq b y a)) := by
  have hpos : 0 < w := by omega
  have h2w : (2 : ℕ) ^ w ≤ 2 ^ (8 * w) :=
    Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega : w ≤ 8 * w)
  have htW : t < 2 ^ (8 * w) := lt_of_le_of_lt htN (lt_of_lt_of_le hNw h2w)
  have hS0t : wordsOf (8 * w) (t * w) ≤ t := wordsOf_le w t hw1
  have hSt : wordsOf (8 * w) (t * w) + 2 * t ≤ decoderAllocEnd t := frontBound hS0t
  have h1E : (1 : ℕ) < 2 ^ E.W := by
    rw [hW]
    have h0 : 0 < 8 * w := by omega
    have h := Nat.pow_lt_pow_right (by norm_num : 1 < 2) h0
    simpa using h
  have hsrc : ∀ k < t, (wordsOf (8 * w) (t * w) + k) % 2 ^ E.W
      = wordsOf (8 * w) (t * w) + k := by
    intro k hk
    rw [hW]
    refine Nat.mod_eq_of_lt ?_
    have h1 : wordsOf (8 * w) (t * w) + k < 2 ^ w + 2 ^ w := by omega
    calc wordsOf (8 * w) (t * w) + k < 2 ^ w + 2 ^ w := h1
      _ = 2 ^ (w + 1) := by rw [Nat.pow_succ]; ring
      _ ≤ 2 ^ (8 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have henc : ∀ k < t, enc b (eSeq b y k) < 2 ^ E.W := by
    intro k hk
    rw [hW]
    exact lt_of_lt_of_le (enc_lt b _) h2w
  have hsrcval : ∀ k < t, expandMemB (decoderAllocEnd t) t m (wordsOf (8 * w) (t * w)) b y k
      (wordsOf (8 * w) (t * w) + k) = enc b (eSeq b y k) := by
    intro k hk
    exact expandMemB_src (by omega) hk
  have hld : ∀ k < t, enc b (eSeq b y k) % 2 ^ E.W = enc b (eSeq b y k) := by
    intro k hk
    exact Nat.mod_eq_of_lt (henc k hk)
  have hsq : ∀ k < t,
      (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = detSqBase w + enc b (eSeq b y k) := by
    intro k hk
    rw [hW]
    exact Nat.mod_eq_of_lt (detSqBase_add_lt hw1 (enc_lt b _))
  have htab : ∀ k < t,
      E.det (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = sqTab b (enc b (eSeq b y k)) := by
    intro k hk
    rw [hdet, detStd_sq t N w b ι (enc_lt b _), hW]
    exact Nat.mod_eq_of_lt (lt_of_lt_of_le (enc_lt b _) h2w)
  have hval : ∀ k < t, sqTab b (enc b (eSeq b y k)) = enc b (eSeq b y (2 * k + 1)) := by
    intro k hk
    exact sqTab_enc b y k
  have hkk : ∀ k < t, (k + k) % 2 ^ E.W = k + k := by
    intro k hk
    rw [hW]
    refine Nat.mod_eq_of_lt ?_
    have h1 : k + k < 2 ^ w + 2 ^ w := by omega
    calc k + k < 2 ^ w + 2 ^ w := h1
      _ = 2 ^ (w + 1) := by rw [Nat.pow_succ]; ring
      _ ≤ 2 ^ (8 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hkkS0 : ∀ k < t,
      (k + k + wordsOf (8 * w) (t * w)) % 2 ^ E.W = wordsOf (8 * w) (t * w) + 2 * k := by
    intro k hk
    have h := addr_lt_two_pow_eight (w := w) (t := t) (k := k)
      (S0 := wordsOf (8 * w) (t * w)) hw1 (lt_of_le_of_lt htN hNw) hS0t hk
    have h2 : k + k + wordsOf (8 * w) (t * w) = wordsOf (8 * w) (t * w) + 2 * k := by omega
    rw [h2, hW]
    exact Nat.mod_eq_of_lt h
  have haddr : ∀ k < t,
      (wordsOf (8 * w) (t * w) + 2 * k + 1) % 2 ^ E.W = wordsOf (8 * w) (t * w) + 2 * k + 1 := by
    intro k hk
    rw [hW]
    exact Nat.mod_eq_of_lt (addr_succ_lt_two_pow_eight hw1 (lt_of_le_of_lt htN hNw) hS0t hk)
  have hk1 : ∀ k < t, (k + 1) % 2 ^ E.W = k + 1 := by
    intro k hk
    rw [hW]
    refine Nat.mod_eq_of_lt ?_
    have h2 : k + 1 ≤ t := by omega
    omega
  exact expandLoop_resultB P E m base (wordsOf (8 * w) (t * w)) w t b y hAt
    h1E hsrc hsrcval hld hsq htab hval hkk hkkS0 haddr hk1 hSt

/-- **The input front of the read stage, at a masked memory.** -/
theorem inputFront_specB {F : Type} [Field F] [Algebra (ZMod 2) F]
    (E : RAMEnv) (P : Program) (m : ℕ → ℕ) (base N t w : ℕ) (y : Fin (t * w) → ZMod 2)
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (hAt : At P base (Stmt.compile inputFrontStmt base))
    (hW : E.W = 8 * w) (hw1 : 1 ≤ w) (hNw : N < 2 ^ w) (htN : t ≤ N)
    (hdet : E.det = detStd t N b ι)
    (hmem : ∀ a, a < decoderAllocEnd t → m a = hintMem (8 * w) y [] a) :
    Sem P E base (base + 69) ⟨base, (decoderStart (8 * w) y []).regs, m⟩
      (fun k z => k ≤ 38 * t + 35 ∧
        z = boundaryState (base + 69)
          (expandMemB (decoderAllocEnd t) t m (wordsOf (8 * w) (t * w)) b y t) ∧
        FieldArrayStored b z.mem (wordsOf (8 * w) (t * w)) (2 * t) (eSeq b y) ∧
        (∀ addr, decoderAllocEnd t ≤ addr → z.mem addr = m addr)) := by
  let S0 := wordsOf (8 * w) (t * w)
  have hSt : S0 + 2 * t ≤ decoderAllocEnd t := frontBound (wordsOf_le w t hw1)
  obtain ⟨hReadAt, hRestAt⟩ := At.seqStmt hAt
  obtain ⟨hResetAt, hRest2At⟩ := At.seqStmt hRestAt
  obtain ⟨hExpandAt, hZeroAt⟩ := At.seqStmt hRest2At
  have hRead := inputRead_specB E P m base N t w y b ι hReadAt hW hw1 hNw htN hdet hmem
  have hReset : Sem P E (base + 33) (base + 34)
      { readStateB m (base + 14) S0 w t y t with pc := base + 33 }
      (fun k z => k ≤ 1 ∧ z = expandStateB m (base + 34) S0 w t b y 0) := by
    refine Sem.mono (Sem.block P E (base + 33) [iImm r5 0] _ hResetAt (by simp) rfl) ?_
    intro k z hQ
    have hk : k = 1 := hQ.1
    exact ⟨by omega, hQ.2.trans (readToExpansion_specB E m (base + 14) (base + 33) S0 w t b y)⟩
  have hExpand := expandAt_specB P E m N t w (base + 34) b y ι hExpandAt hW hw1 hNw htN hdet
  have hExpandExact : Sem P E (base + 34) (base + 53) (expandStateB m (base + 34) S0 w t b y 0)
      (fun k z => k ≤ 19 * t + 2 ∧
        z = { expandStateB m (base + 34) S0 w t b y t with pc := base + 53 }) :=
    Sem.mono hExpand (fun _ _ hQ => ⟨hQ.1, hQ.2.1⟩)
  have hZero := Sem.zero_block P E (base + 53)
    { expandStateB m (base + 34) S0 w t b y t with pc := base + 53 } hZeroAt rfl
  have hFull := Sem.seq_bound hRead (fun z _ hz => by
    subst z
    exact Sem.seq_bound hReset (fun z _ hz => by
      subst z
      exact Sem.seq_bound hExpandExact (fun z _ hz => by subst z; exact hZero)))
  refine Sem.mono hFull ?_
  intro k z hQ
  obtain ⟨hk, hz⟩ := hQ
  refine ⟨by omega, ⟨hz, ⟨?_, ?_⟩⟩⟩
  · rw [hz]
    intro j hj
    exact expandMemB_complete (by omega) hj
  · rw [hz]
    intro addr ha
    exact expandMemB_after m S0 b y addr ha

/-- **The syndrome-saving stage at a masked memory.** -/
theorem saveSyndromeProcedure_specB {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (P : Program) (E : RAMEnv) (pc S0 t : ℕ)
    (e : ℕ → F) (m : ℕ → ℕ)
    (hAt : At P pc (Stmt.compile saveSyndromeProcedure pc))
    (hmeta : (128 : ℕ) < 2 ^ E.W) (hwe : w ≤ E.W)
    (hS0 : S0 ≤ t) (hword : decoderSavedBase t + 2 * t ≤ 2 ^ E.W)
    (hBfit : decoderSavedBase t < 2 ^ E.W)
    (h0 : E.det 0 % 2 ^ E.W = t) (h4 : E.det 4 % 2 ^ E.W = S0)
    (hsums : FieldArrayStored b m S0 (2 * t) e)
    (htail : ∀ addr, decoderSavedBase t + 2 * t ≤ addr → addr < decoderAllocEnd t → m addr = 0) :
    Sem P E pc (pc + 41) (boundaryState pc m)
      (fun k z => k ≤ 12 * (2 * t) + 31 ∧
        z = boundaryState (pc + 41)
          (writeArray (decoderSavedBase t) m (fun i => m (S0 + i)) (2 * t)) ∧
        FieldArrayStored b z.mem (decoderSavedBase t) (2 * t) e ∧
        (∀ addr, decoderSavedBase t + 2 * t ≤ addr → addr < decoderAllocEnd t → z.mem addr = 0) ∧
        (∀ addr, decoderAllocEnd t ≤ addr → z.mem addr = m addr)) := by
  have hlen : 2 * t < 2 ^ E.W := by
    have hb : 128 ≤ decoderSavedBase t := by unfold decoderSavedBase; omega
    omega
  have hsrc : S0 + 2 * t ≤ 2 ^ E.W := by dsimp [decoderSavedBase] at hword; omega
  have hdisj : S0 + 2 * t ≤ decoderSavedBase t := by unfold decoderSavedBase; omega
  have hsaved : decoderSavedBase t + 2 * t ≤ decoderAllocEnd t := savedBase_le_allocEnd t
  obtain ⟨hArgsAt, hRestAt⟩ := At.seqStmt hAt
  obtain ⟨hCopyAt, hZeroAt⟩ := At.seqStmt hRestAt
  have hArgs : Sem P E pc (pc + 13) (boundaryState pc m)
      (fun k z => k ≤ 13 ∧
        z = copyState (pc + 13) (decoderSavedBase t) S0 (2 * t) m (fun _ => 0) 0) := by
    refine Sem.mono (Sem.block P E pc saveArgsCode _ hArgsAt
      (by simp [saveArgsCode, saveHeaderCode, saveDestinationCode]) rfl) ?_
    intro k z hQ
    have hk : k = 13 := hQ.1
    exact ⟨by omega, hQ.2.trans (saveArgs_spec E pc S0 t m hmeta hlen hBfit h0 h4)⟩
  have hCopy := copyArray_spec P E (pc + 13) (decoderSavedBase t) S0 (2 * t) m (fun _ => 0) hCopyAt
    (by omega) hlen hword hsrc (Or.inl hdisj) (by
      intro j hj
      rw [hsums j hj]
      exact lt_of_lt_of_le (enc_lt b _) (Nat.pow_le_pow_right (by norm_num) hwe))
  have hZero := Sem.zero_block P E (pc + 25)
    { copyState (pc + 13) (decoderSavedBase t) S0 (2 * t) m (fun _ => 0) (2 * t) with pc := pc + 25 }
    hZeroAt rfl
  have hFull := Sem.seq_bound hArgs (fun z _ hz => by
    subst z
    exact Sem.seq_bound hCopy (fun z _ hz => by subst z; exact hZero))
  refine Sem.mono hFull ?_
  intro k z hQ
  obtain ⟨hk, hz⟩ := hQ
  refine ⟨by omega, ⟨hz, ⟨?_, ⟨?_, ?_⟩⟩⟩⟩
  · rw [hz]
    change FieldArrayStored b (writeArray (decoderSavedBase t) m (fun i => m (S0 + i)) (2 * t))
      (decoderSavedBase t) (2 * t) e
    intro j hj
    rw [writeArray_get _ _ _ (2 * t) j hj]
    exact hsums j hj
  · rw [hz]
    change ∀ addr, decoderSavedBase t + 2 * t ≤ addr → addr < decoderAllocEnd t →
      writeArray (decoderSavedBase t) m (fun i => m (S0 + i)) (2 * t) addr = 0
    intro addr ha hlt
    rw [writeArray_frame _ _ _ _ addr (Or.inr ha)]
    exact htail addr ha hlt
  · rw [hz]
    change ∀ addr, decoderAllocEnd t ≤ addr →
      writeArray (decoderSavedBase t) m (fun i => m (S0 + i)) (2 * t) addr = m addr
    intro addr ha
    rw [writeArray_frame _ _ _ _ addr (Or.inr (by omega))]

/-- **The read stage of Proposition 2.1 at a memory that is zero only inside the decoder's own
workspace.**  If `m` agrees with the canonical entry memory `hintMem (8w) y []` on
`[0, decoderAllocEnd t)`, the read stage runs in the same `62t + 66` steps, produces the same
workspace on `[0, decoderAllocEnd t)`, and **leaves every word at or above `decoderAllocEnd t`
untouched**. -/
theorem pinsketch_decoder_readB {F : Type} [Field F] [Algebra (ZMod 2) F]
    (E : RAMEnv) (P : Program) (base N t w : ℕ) (y : Fin (t * w) → ZMod 2)
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (m : ℕ → ℕ)
    (hAt : At P base (Stmt.compile inputSavedProcedure base))
    (hW : E.W = 8 * w) (hw1 : 1 ≤ w) (hNw : N < 2 ^ w) (htN : t ≤ N)
    (hdet : E.det = detStd t N b ι)
    (hmem : ∀ a, a < decoderAllocEnd t → m a = hintMem (8 * w) y [] a) :
    Sem P E base (base + 110) ⟨base, (decoderStart (8 * w) y []).regs, m⟩
      (fun k z => k ≤ 62 * t + 66 ∧
        ∃ m', z = boundaryState (base + 110) m' ∧
          FieldArrayStored b m' (decoderSavedBase t) (2 * t) (eSeq b y) ∧
          PolynomialStored b m' (decoderSavedBase t) (decoderCapacity t)
            (syndromePoly (eSeq b y) t) ∧
          (∀ addr, decoderSavedBase t + 2 * t ≤ addr → addr < decoderAllocEnd t → m' addr = 0) ∧
          (∀ addr, decoderAllocEnd t ≤ addr → m' addr = m addr)) := by
  let S0 := wordsOf (8 * w) (t * w)
  have hAlloc : decoderAllocEnd t < 2 ^ E.W := by
    rw [hW]
    exact decoderAllocEnd_fits t w hw1 (lt_of_le_of_lt htN hNw)
  have hEBword : decoderSavedBase t + 2 * t ≤ 2 ^ E.W := by
    have hE : decoderSavedBase t + 2 * t ≤ decoderAllocEnd t := savedBase_le_allocEnd t
    omega
  have hEBfit : decoderSavedBase t < 2 ^ E.W := by
    have he : decoderSavedBase t ≤ decoderAllocEnd t := by
      have h := savedBase_le_allocEnd t
      unfold decoderSavedBase at *
      omega
    omega
  have hmeta : (128 : ℕ) < 2 ^ E.W := by
    have hp : (2 : ℕ) ^ 8 ≤ 2 ^ E.W := by
      rw [hW]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact lt_of_lt_of_le (by norm_num : 128 < 2 ^ 8) hp
  have hS0 : S0 ≤ t := wordsOf_le w t hw1
  have h0 : E.det 0 % 2 ^ E.W = t := by
    rw [hdet, detStd_hdr t N w b ι (by norm_num : 0 < 13), hdrTab_zero,
      Nat.mod_eq_of_lt (by omega)]
  have h4 : E.det 4 % 2 ^ E.W = S0 := by
    rw [hdet, detStd_hdr t N w b ι (by norm_num : 4 < 13), hdrTab_four,
      Nat.mod_eq_of_lt (by omega)]
  have hSt : S0 + 2 * t ≤ decoderAllocEnd t := frontBound hS0
  obtain ⟨hFrontAt, hSaveAt⟩ := At.seqStmt hAt
  have hFront := inputFront_specB E P m base N t w y b ι hFrontAt hW hw1 hNw htN hdet hmem
  have hFrontExact : Sem P E base (base + 69) ⟨base, (decoderStart (8 * w) y []).regs, m⟩
      (fun k z => k ≤ 38 * t + 35 ∧
        z = boundaryState (base + 69) (expandMemB (decoderAllocEnd t) t m S0 b y t)) := by
    refine Sem.mono hFront ?_
    intro k z hQ
    exact ⟨hQ.1, hQ.2.1⟩
  have hValues : FieldArrayStored b (expandMemB (decoderAllocEnd t) t m S0 b y t) S0 (2 * t)
      (eSeq b y) := by
    intro j hj
    exact expandMemB_complete (by omega) hj
  have hTail : ∀ addr, decoderSavedBase t + 2 * t ≤ addr → addr < decoderAllocEnd t →
      expandMemB (decoderAllocEnd t) t m S0 b y t addr = 0 := by
    intro addr ha hlt
    rw [expandMemB, maskMem_lt hlt]
    exact expandMem_after_zero S0 b y t addr (by dsimp [S0, decoderSavedBase] at ha; omega)
  have hSave := saveSyndromeProcedure_specB b P E (base + 69) S0 t (eSeq b y)
    (expandMemB (decoderAllocEnd t) t m S0 b y t) hSaveAt hmeta (by omega) hS0 hEBword hEBfit h0 h4
    hValues hTail
  have hFull := Sem.seq_bound hFrontExact (fun z _ hz => by subst z; exact hSave)
  refine Sem.mono hFull ?_
  intro k z hQ
  obtain ⟨hk, hz, hsums, htail, hframe⟩ := hQ
  have hzmem : z.mem = writeArray (decoderSavedBase t)
      (expandMemB (decoderAllocEnd t) t m S0 b y t)
      (fun i => expandMemB (decoderAllocEnd t) t m S0 b y t (S0 + i)) (2 * t) := by
    rw [hz]
    rfl
  rw [hzmem] at hsums htail hframe
  have hframe2 : ∀ addr, decoderAllocEnd t ≤ addr →
      writeArray (decoderSavedBase t) (expandMemB (decoderAllocEnd t) t m S0 b y t)
        (fun i => expandMemB (decoderAllocEnd t) t m S0 b y t (S0 + i)) (2 * t) addr = m addr := by
    intro addr ha
    rw [hframe addr ha]
    exact expandMemB_after m S0 b y addr ha
  have hpoly : PolynomialStored b
      (writeArray (decoderSavedBase t) (expandMemB (decoderAllocEnd t) t m S0 b y t)
        (fun i => expandMemB (decoderAllocEnd t) t m S0 b y t (S0 + i)) (2 * t))
      (decoderSavedBase t) (decoderCapacity t) (syndromePoly (eSeq b y) t) :=
    saved_syndrome_polynomialB b t (eSeq b y) _ hsums htail
  exact ⟨by omega,
    writeArray (decoderSavedBase t) (expandMemB (decoderAllocEnd t) t m S0 b y t)
      (fun i => expandMemB (decoderAllocEnd t) t m S0 b y t (S0 + i)) (2 * t),
    hz, hsums, hpoly, htail, hframe2⟩

end BoundedRead

end P21Bnd

end LinearSetReconciliation327.Main


