-- Prove2me | Definitions.Def_Def_LinearSetReconciliation327_Main_P21DetBndKey20261122
-- name    : Def_LinearSetReconciliation327_Main_P21DetBndKey20261122
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T08:43:26.785369+00:00
-- url     : https://prove2.me/theorems/10442c0f-fff8-43c4-b941-249edada0feb
-- title:
--   Proposition 2.1's key-solver stage at bounded zero **and** with the weakened `det` contract (combined weakening, node 2/3)
-- statement:
--   **The key-solver stage of Proposition 2.1 at the *combined* weakening.**  The published
--   `Def_..._P21BndKey20261122` re-derives the 960-instruction key solver at the bounded tail
--   hypothesis `decoderSavedBase t + 2t <= addr -> addr < decoderAllocEnd t -> m addr = 0`, with the
--   solver frame `MemoryFrame (solverInitWritable t)`, but keeps `hdet : E.det = detStd t N b iota`.
--   This bundle keeps the bounded tail and weakens `hdet` to `DetAgrees` (agreement on the ten header
--   slots and on $[\mathsf{detMulBase}(w),\infty)$).  The six new declarations of the published bounded
--   bundle (`rowBoundB_arith`, `savedCapBoundB`, `rowBoundB`, `saved_rows_zeroB`,
--   `saved_syndrome_polynomialB`, `pinsketch_decoder_key_solverB`) plus the re-proved
--   `solverInitializationProcedure_spec` are carried verbatim with the two `hdet` binders re-pointed;
--   the rest of the solver stack (the whole pade chain, the metadata block,
--   `RootConstants.after_pade`, ...) is *not* copied --- it resolves to the `DetAgrees` versions already
--   published in `Def_..._P21DetFront20261121`.  Axioms:
--   `[propext, Classical.choice, Quot.sound]`.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Proposition 2.1 (the base-relative decoder), Theorem 6.5 (the row loop) and its row body; the project's verified development, whose two published weakenings (`pinsketch_decoding_at_bounded`, `pinsketch_decoding_at_det`) are combined here.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_WordRAM
import Definitions.Def_LinearSetReconciliation327_Main_Pinsketch
import Definitions.Def_LinearSetReconciliation327_Main_DecoderModel
import Definitions.Def_LinearSetReconciliation327_Main_DecoderTables
import Definitions.Def_LinearSetReconciliation327_Main_DecoderProgram
import Definitions.Def_LinearSetReconciliation327_Main_P21RunStmt
import Definitions.Def_LinearSetReconciliation327_Main_P21DetFront20261121

/-!
# Proposition 2.1's key solver: bounded zero **and** the weakened `det` contract

`Definitions.Def_..._P21BndKey20261122` re-derives the key solver at the *bounded* tail hypothesis
`hTail : ... -> addr < decoderAllocEnd t -> m addr = 0`, but keeps `hdet : E.det = detStd t N b iota`.
Here the same six new declarations are carried verbatim with the three `hdet` binders re-pointed to
`DetAgrees E t N b iota` (the ten header slots and `[detMulBase w, inf)`), which is exactly the
hypothesis `Definitions.Def_..._P21DetFront20261121` proves the rest of the solver stack at.

The 39 declarations of the published bundle that the Front bundle already carries (the whole pade
stack, the metadata block, `RootConstants.after_pade`, ...) are *not* copied: they resolve to the
`DetAgrees` versions from the Front bundle.  `solverInitializationProcedure_spec` **is** re-emitted
here, because the published one has the unbounded `hTail`; it shadows the Front copy inside
`P21Bnd` exactly as the published bounded bundle shadows the `DecoderLemmas` copy.
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

/-- The polynomial core of `rowBoundB`, stated over the two variables only.  `nlinarith` in the key
solver's 40-hypothesis context has cost 18-29 s in this project; here it sees three hypotheses. -/
theorem rowBoundB_arith (t k : ℕ) (hk : k ≤ 7) :
    decoderSavedBase t + 2 * t + k * decoderCapacity t + decoderCapacity t
      ≤ 8 * t * t + 44 * t + 144 := by
  unfold decoderSavedBase decoderCapacity decoderLength
  have h : k * (4 * t + 2) ≤ 7 * (4 * t + 2) := Nat.mul_le_mul_right _ hk
  nlinarith


/-- The syndrome-polynomial slot block ends inside the decoder's scratch. -/
theorem savedCapBoundB (t j : ℕ) (hj : j < decoderCapacity t) :
    decoderSavedBase t + j < decoderAllocEnd t := by
  rw [decoderAllocEnd_eq]
  unfold decoderSavedBase
  unfold decoderCapacity decoderLength at hj
  omega

/-- Any row block of the eight first rows ends inside the decoder's scratch. -/
theorem rowBoundB (t k : ℕ) (hk : k ≤ 7) :
    decoderRowBase t k + decoderCapacity t ≤ decoderAllocEnd t := by
  rw [decoderAllocEnd_eq]
  unfold decoderRowBase
  exact rowBoundB_arith t k hk


/-- **The bounded-tail form of `saved_rows_zero`**: a row of the first eight ends inside the
decoder's scratch, so zeros are needed only there. -/
theorem saved_rows_zeroB {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (t : ℕ) (m : ℕ → ℕ)
    (htail : ∀ addr, decoderSavedBase t + 2 * t ≤ addr → addr < decoderAllocEnd t → m addr = 0)
    (k : ℕ) (hk : k ≤ 7) :
    PolynomialStored b m (decoderRowBase t k) (decoderCapacity t) 0 := by
  intro j hj
  rw [Polynomial.coeff_zero, enc_zero]
  apply htail
  · unfold decoderRowBase
    omega
  · exact lt_of_lt_of_le (Nat.add_lt_add_left hj _) (rowBoundB t k hk)

/-- **The bounded-tail form of `saved_syndrome_polynomial`**: the syndrome slot block is
`[decoderSavedBase t, decoderSavedBase t + decoderCapacity t)`, which ends inside the scratch, so
zeros are needed only there. -/
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
    exact htail _ (by omega) (savedCapBoundB t j hj)


theorem solverInitializationProcedure_spec {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (t N : ℕ) (P : Program) (E : RAMEnv) (pc : ℕ)
    (e : ℕ → F) (m : ℕ → ℕ) (hAt : At P pc (Stmt.compile solverInitializationProcedure pc))
    (hw : 1 ≤ w) (hW : E.W = 8 * w) (hdet : DetAgrees E t N b ι)
    (hEnd : decoderAllocEnd t < 2 ^ E.W) (h0 : ι 0 ≠ 0)
    (hh0 : E.det 0 % 2 ^ E.W = t) (hh1 : E.det 1 % 2 ^ E.W = w) (hh2 : E.det 2 % 2 ^ E.W = N)
    (hSaved : FieldArrayStored b m (decoderSavedBase t) (2 * t) e)
    (hTail : ∀ addr, decoderSavedBase t + 2 * t ≤ addr → addr < decoderAllocEnd t → m addr = 0) :
    Sem P E pc (pc + 391) (boundaryState pc m)
      (fun k z => k ≤ 12 * decoderCapacity t + 381 ∧ ∃ m', z = boundaryState (pc + 391) m' ∧
        DecoderMetadata t w N m' ∧
        PadeRows b E (decoderRowBase t 0) (decoderRowBase t 1) (decoderRowBase t 2) (decoderRowBase t 3)
          (decoderLength t) (decoderCapacity t) m' (padeInitial e t) ∧
        RootConstants b (decoderRowBase t 0) (decoderRowBase t 6) (decoderRowBase t 1) (decoderRowBase t 7)
          (decoderRowBase t 4) (decoderRowBase t 5) (decoderCapacity t) (decoderLength t) m' ∧
        FieldArrayStored b m' (decoderSavedBase t) (2 * t) e ∧ MemoryFrame (solverInitWritable t) m m') := by
  let R := decoderRowBase t 0
  let U := decoderRowBase t 1
  let D := decoderRowBase t 2
  let C := decoderRowBase t 3
  let cap := decoderCapacity t
  let L := decoderLength t
  have hl := decoderRows_pade t
  have hcap2 : 2 ≤ cap := decoderCapacity_pos t
  have hindex : 2 * t < cap := by dsimp [cap, decoderCapacity, decoderLength]; omega
  have hmeta : (108 : ℕ) < 2 ^ E.W := by
    have hh := decoderAllocEnd_eq t
    omega
  have hword (j : ℕ) (hj : j < 8) : decoderRowBase t j + cap ≤ 2 ^ E.W := decoderRow_word E t j hj (le_of_lt hEnd)
  have hSourceWord : decoderSavedBase t + cap ≤ 2 ^ E.W := by
    have hDword := hword 2 (by norm_num)
    dsimp [decoderRowBase] at hDword
    omega
  let m1 := decoderMetadataMemory E t m
  let m2 := Function.update m1 78 (enc b 1)
  have hm1 := decoderMetadataMemory_spec E t w N m hh1 hh2
  have hm2 : DecoderMetadata t w N m2 := hm1.of_preserved (by
    intro slot hs
    have hne : slot ≠ 78 := by dsimp [decoderMetadataSlots] at hs; omega
    simp [m2, m1, hne])
  have hf01 := decoderMetadataMemory_frame E t m
  have hf12 : MemoryFrame (fun addr => addr < 128) m1 m2 := MemoryFrame.meta_update m1 78 (enc b 1) (by norm_num)
  have hf02 := MemoryFrame.trans hf01 hf12
  have hSource2 : PolynomialStored b m2 (decoderSavedBase t) cap (syndromePoly e t) :=
    (saved_syndrome_polynomialB b t e m hSaved hTail).of_frame hf02 (by intro j hj; dsimp [decoderSavedBase]; omega)
  have hZero2 (j : ℕ) (hj7 : j ≤ 7) : PolynomialStored b m2 (decoderRowBase t j) cap 0 :=
    (saved_rows_zeroB b t m hTail j hj7).of_frame hf02 (by intro i hi; exact not_lt_of_ge (le_trans (decoderRow_low t j) (by omega)))
  obtain ⟨hMetaAt, hRestRaw⟩ := At.seqStmt hAt
  have hRestAt : At P (pc + 248)
      (Stmt.compile (.seq (.code cacheUnitCode) (.seq (copyFromSlotsProcedure 74 79) (.code initialPolynomialsCode))) (pc + 248)) := by
    simpa only [Stmt.len, decoderMetadataCode_length] using hRestRaw
  obtain ⟨hUnitAt, hRest2⟩ := At.seqStmt hRestAt
  obtain ⟨hCopyAt, hInitialAt⟩ := At.seqStmt hRest2
  have hMetadata : Sem P E pc (pc + 248) (boundaryState pc m)
      (fun k z => k ≤ 248 ∧ z = boundaryState (pc + 248) m1) := by
    have hrun : runBlock decoderMetadataCode E (boundaryState pc m) = boundaryState (pc + decoderMetadataCode.length) m1 := by
      rw [decoderMetadataCode_length]
      exact decoderMetadataCode_spec E pc t m hEnd hh0
    have hs := Sem.boundary_block P E pc decoderMetadataCode m m1 hMetaAt decoderMetadataCode_noBranch hrun
    simpa only [decoderMetadataCode_length] using hs
  have hUnit : Sem P E (pc + 248) (pc + 288) (boundaryState (pc + 248) m1)
      (fun k z => k ≤ 40 ∧ z = boundaryState (pc + 288) m2) :=
    Sem.boundary_block P E _ cacheUnitCode m1 m2 hUnitAt
      (by simp [cacheUnitCode, metaReadCode, imageZeroCode, fieldInvCode, fieldMulCode, metaStoreCode, zeroRegsCode])
      (cacheUnit_spec b ι t N E _ hw hW hdet h0 hm1.dimension)
  have hCopy := copyFromSlots_spec b P E (pc + 288) 74 79 D (decoderSavedBase t) cap (syndromePoly e t) m2 hCopyAt
    (by omega) (by omega) (by omega) (by omega) (by omega) hl.Dlow (by dsimp [decoderSavedBase]; omega)
    (hword 2 (by norm_num)) hSourceWord (by left; dsimp [D, decoderRowBase]; omega) hSource2 hm2.rowD hm2.saved hm2.capacity
  obtain ⟨_, k3, z3, hRun3, hPc3, hCost3, m3, hz3, hD3, hf23raw⟩ := hCopy
  have hm3 : DecoderMetadata t w N m3 := hm2.of_preserved (by
    intro slot hs
    apply root_copy_meta hf23raw hl.Dlow
    · dsimp [decoderMetadataSlots] at hs; omega
    · dsimp [decoderMetadataSlots] at hs; omega)
  have hunit3 : m3 78 = enc b (1 : F) :=
    (root_copy_meta hf23raw hl.Dlow (by norm_num) (by norm_num)).trans (by simp [m2])
  have hR3 : PolynomialStored b m3 R cap 0 :=
    (hZero2 0 (by norm_num)).after_root_copy hl.Rlow (hl.RD.elim Or.inr Or.inl) hf23raw
  have hU3 : PolynomialStored b m3 U cap 0 :=
    (hZero2 1 (by norm_num)).after_root_copy hl.Ulow (hl.UD.elim Or.inr Or.inl) hf23raw
  have hC3 : PolynomialStored b m3 C cap 0 := (hZero2 3 (by norm_num)).after_root_copy hl.Clow hl.DC hf23raw
  let mR := Function.update m3 (R + 2 * t) (enc b 1)
  let m4 := Function.update mR C (enc b 1)
  have hPointFrame : MemoryFrame (fun addr => addr = R + 2 * t ∨ addr = C) m3 m4 :=
    MemoryFrame.trans (MemoryFrame.update_allowed _ m3 (R + 2 * t) _ (Or.inl rfl))
      (MemoryFrame.update_allowed _ _ C _ (Or.inr rfl))
  have hm4 : DecoderMetadata t w N m4 := hm3.of_preserved (by
    intro slot hs
    have hslt : slot < 128 := by dsimp [decoderMetadataSlots] at hs; omega
    apply hPointFrame
    change ¬ (slot = R + 2 * t ∨ slot = C)
    have hRlo := hl.Rlow
    have hClo := hl.Clow
    omega)
  have hunit4 : m4 78 = enc b (1 : F) := by
    have hRlo := hl.Rlow
    have hClo := hl.Clow
    simpa [m4, mR, show 78 ≠ C by omega, show 78 ≠ R + 2 * t by omega] using hunit3
  have hR4 : PolynomialStored b m4 R cap (Polynomial.X ^ (2 * t)) :=
    (hR3.zero_to_X_pow (2 * t)).of_frame (MemoryFrame.update _ C (enc b 1)) (by
      intro j hj
      have hsep := hl.RC
      change R + j ≠ C
      omega)
  have hU4 : PolynomialStored b m4 U cap 0 := hU3.of_frame hPointFrame (by
    intro j hj
    have hRsep := hl.RU
    have hCsep := hl.UC
    change ¬ (U + j = R + 2 * t ∨ U + j = C)
    omega)
  have hD4 : PolynomialStored b m4 D cap (syndromePoly e t) := hD3.of_frame hPointFrame (by
    intro j hj
    have hRsep := hl.RD
    have hCsep := hl.DC
    change ¬ (D + j = R + 2 * t ∨ D + j = C)
    omega)
  have hCzeroR : PolynomialStored b mR C cap 0 := hC3.of_frame (MemoryFrame.update _ (R + 2 * t) (enc b 1)) (by
    intro j hj
    have hsep := hl.RC
    change C + j ≠ R + 2 * t
    omega)
  have hC4 : PolynomialStored b m4 C cap 1 := by
    simpa only [Nat.add_zero, pow_zero] using hCzeroR.zero_to_X_pow 0
  have hf23 : MemoryFrame (solverInitWritable t) m2 m3 := hf23raw.mono (by
    intro addr ha
    dsimp [copyFromSlotsWritable] at ha
    dsimp [solverInitWritable, D, decoderRowBase, cap] at ha ⊢
    omega)
  have hf34 : MemoryFrame (solverInitWritable t) m3 m4 := hPointFrame.mono (by
    intro addr ha
    dsimp [solverInitWritable, R, C, decoderRowBase, cap] at ha ⊢
    dsimp only [cap] at hindex
    omega)
  have hf04 : MemoryFrame (solverInitWritable t) m m4 :=
    MemoryFrame.trans (MemoryFrame.trans (hf02.mono (fun _ ha => Or.inl ha)) hf23) hf34
  have hSaved4 : FieldArrayStored b m4 (decoderSavedBase t) (2 * t) e := hSaved.of_frame hf04 (by
    intro j hj
    dsimp [solverInitWritable, decoderRowBase, decoderSavedBase]
    omega)
  have hZero4 : PolynomialStored b m4 (decoderRowBase t 5) cap 0 :=
    (saved_rows_zeroB b t m hTail 5 (by norm_num)).of_frame hf04 (by
    intro j hj
    dsimp [solverInitWritable, decoderRowBase, decoderSavedBase]
    have hc := decoderCapacity_pos t
    omega)
  have hRows4 : PadeRows b E R U D C L cap m4 (padeInitial e t) :=
    ⟨hl, hword 0 (by norm_num), hword 1 (by norm_num), hword 2 (by norm_num), hword 3 (by norm_num),
      hR4, hU4, hD4, hC4, hm4.rowR, hm4.rowU, hm4.rowD, hm4.rowC, hm4.length, hm4.dimension, hm4.capacity⟩
  have hRoot4 : RootConstants b R (decoderRowBase t 6) U (decoderRowBase t 7) (decoderRowBase t 4) (decoderRowBase t 5) cap L m4 :=
    ⟨hm4.length, hm4.dimension, hunit4, hm4.capacity, hm4.fixedR, hm4.fixedD, hm4.fixedU, hm4.fixedC, hm4.fixedT, hm4.fixedZ, hZero4⟩
  have hCopyExact : Sem P E (pc + 288) (pc + 358) (boundaryState (pc + 288) m2)
      (fun k z => k ≤ 12 * cap + 60 ∧ z = boundaryState (pc + 358) m3) :=
    ⟨rfl, k3, z3, hRun3, hPc3, hCost3, hz3⟩
  have hInitial : Sem P E (pc + 358) (pc + 391) (boundaryState (pc + 358) m3)
      (fun k z => k ≤ 33 ∧ z = boundaryState (pc + 391) m4) :=
    Sem.boundary_block P E _ initialPolynomialsCode m3 m4 hInitialAt
      (by simp [initialPolynomialsCode, initialRowOffsetCode, metaReadCode, zeroRegsCode])
      (by
        have hp := initialPolynomials_spec b E (boundaryState (pc + 358) m3) R C L (by omega) (by omega) hl.Rlow
          (by have hh := hword 3 (by norm_num); omega) (by dsimp [L, decoderLength]; omega)
          (by have hh := hword 0 (by norm_num); dsimp [cap, decoderCapacity] at hh; omega)
          (by have hh := hword 0 (by norm_num); dsimp [cap, decoderCapacity] at hh; omega)
          hm3.rowR hm3.rowC hm3.length hunit3
        simpa [L, decoderLength, m4, mR, boundaryState, initialPolynomialsCode_length] using hp)
  have hFull := Sem.seq_bound hMetadata (fun z _ hz => by
    subst z
    exact Sem.seq_bound hUnit (fun z _ hz => by
      subst z
      exact Sem.seq_bound hCopyExact (fun z _ hz => by subst z; exact hInitial)))
  exact Sem.mono hFull (fun k z hQ => ⟨by omega, m4, hQ.2, hm4, hRows4, hRoot4, hSaved4, hf04⟩)

theorem pade_write_le_solver_init (t addr : ℕ)
    (ha : padeLoopWritable (decoderRowBase t 0) (decoderRowBase t 1) (decoderRowBase t 2) (decoderRowBase t 3) (decoderCapacity t) addr) :
    solverInitWritable t addr := by
  dsimp [padeLoopWritable, padeWritable, decoderRowBase] at ha
  dsimp [solverInitWritable, decoderRowBase]
  omega

theorem solver_saved_readonly (t j : ℕ) (hj : j < 2 * t) : ¬ solverInitWritable t (decoderSavedBase t + j) := by
  dsimp [solverInitWritable, decoderRowBase, decoderSavedBase]
  omega

theorem solver_zero_readonly (t j : ℕ) : ¬ solverInitWritable t (decoderRowBase t 5 + j) := by
  dsimp [solverInitWritable, decoderRowBase, decoderSavedBase]
  have hc := decoderCapacity_pos t
  omega

theorem pade_preserved_meta {t : ℕ} {m m' : ℕ → ℕ}
    (hf : MemoryFrame (padeLoopWritable (decoderRowBase t 0) (decoderRowBase t 1) (decoderRowBase t 2) (decoderRowBase t 3) (decoderCapacity t)) m m')
    (slot : ℕ) (hlo : 76 ≤ slot) (hhi : slot < 128) (h94 : slot ≠ 94) (h95 : slot ≠ 95) : m' slot = m slot := by
  apply hf
  have hR := decoderRow_low t 0
  have hU := decoderRow_low t 1
  have hD := decoderRow_low t 2
  have hC := decoderRow_low t 3
  dsimp [padeLoopWritable, padeWritable]
  omega

/-- **The key solver at a memory that is zero only inside the decoder's scratch.**  Everything the
solver reads of the ambient memory lies in `[0, decoderAllocEnd t)`, so the published unbounded tail
hypothesis can be weakened to the bounded one that Theorem 6.5's clearing pass supplies. -/
theorem pinsketch_decoder_key_solverB {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (t N : ℕ) (P : Program) (E : RAMEnv) (pc : ℕ)
    (e : ℕ → F) (m : ℕ → ℕ) (hAt : At P pc (Stmt.compile keySolverProcedure pc))
    (hw : 1 ≤ w) (hW : E.W = 8 * w) (hdet : DetAgrees E t N b ι) (ht : 1 ≤ t)
    (hEnd : decoderAllocEnd t < 2 ^ E.W) (h0 : ι 0 ≠ 0)
    (hh0 : E.det 0 % 2 ^ E.W = t) (hh1 : E.det 1 % 2 ^ E.W = w) (hh2 : E.det 2 % 2 ^ E.W = N)
    (hSaved : FieldArrayStored b m (decoderSavedBase t) (2 * t) e)
    (hTail : ∀ addr, decoderSavedBase t + 2 * t ≤ addr → addr < decoderAllocEnd t → m addr = 0) :
    Sem P E pc (pc + 960) (boundaryState pc m)
      (fun k z => k ≤ (34 * decoderCapacity t + (48 * decoderLength t + 187) * decoderLength t + 289) * decoderLength t +
          12 * decoderCapacity t + 385 ∧ ∃ m', z = boundaryState (pc + 960) m' ∧
        KeyReady b E t N e m' ∧
        MemoryFrame (solverInitWritable t) m m') := by
  obtain ⟨hInitAt, hPadeRaw⟩ := At.seqStmt hAt
  have hPadeAt : At P (pc + 391) (Stmt.compile padeSolveProcedure (pc + 391)) := by
    simpa only [solverInitializationProcedure_length] using hPadeRaw
  have hInit := solverInitializationProcedure_spec b ι t N P E pc e m hInitAt hw hW hdet hEnd h0 hh0 hh1 hh2
    hSaved hTail
  obtain ⟨_, k1, z1, hRun1, hPc1, hCost1, m1, hz1, hm1, hRows1, hRoot1, hSaved1, hf01⟩ := hInit
  have hInitExact : Sem P E pc (pc + 391) (boundaryState pc m)
      (fun k z => k ≤ 12 * decoderCapacity t + 381 ∧ z = boundaryState (pc + 391) m1) :=
    ⟨rfl, k1, z1, hRun1, hPc1, hCost1, hz1⟩
  have hPade := padeSolveProcedure_minimal_strong b ι t N P E (pc + 391)
    (decoderRowBase t 0) (decoderRowBase t 1) (decoderRowBase t 2) (decoderRowBase t 3)
    (decoderLength t) (decoderCapacity t) e m1 hPadeAt hw hW hdet ht rfl rfl hRows1 hm1.capacityParameter hm1.padeCounter
  have hFull := Sem.seq_bound hInitExact (fun z _ hz => by subst z; exact hPade)
  refine Sem.mono hFull ?_
  intro k z hQ
  obtain ⟨hk, m2, R', U', D', C', hz2, hRows2, hmin, hf12, hfoot⟩ := hQ
  have hRoot2 := hRoot1.after_pade hf12
  have hSaved2 := hSaved1.of_frame (hf12.mono (pade_write_le_solver_init t)) (solver_saved_readonly t)
  have hm (slot : ℕ) (hs : 76 ≤ slot) (hh : slot < 128) (h94 : slot ≠ 94) (h95 : slot ≠ 95) :=
    pade_preserved_meta hf12 slot hs hh h94 h95
  have hrange : ∀ j < decoderCapacity t, padeWritable (decoderRowBase t 0) (decoderRowBase t 1)
      (decoderRowBase t 2) (decoderRowBase t 3) (decoderCapacity t) (C' + j) := by
    intro j hj
    apply (hfoot (C' + j)).mp
    dsimp [padeWritable]
    omega
  have hdisj := (decoderQueue0_pade_separated t).gcd_output_disjoint (decoderRow_low t 8)
    (by have h := decoderCapacity_pos t; omega) ht hrange
  have hReady : KeyReady b E t N e m2 := by
    refine ⟨hRoot2, hSaved2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, C', hRows2.ptr75, hRows2.layout.Clow, hRows2.Cword,
      hRows2.curC, hdisj⟩
    · exact (hm 79 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans hm1.saved
    · exact (hm 80 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans hm1.capacityParameter
    · exact (hm 82 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans hm1.universeSize
    · exact (hm 83 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans hm1.firstQueue
    · exact (hm 85 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans hm1.output
    · exact (hm 86 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans hm1.verification
    · exact (hm 107 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans hm1.fixedQ1
  exact ⟨by omega, m2, hz2, hReady, MemoryFrame.trans hf01 (hf12.mono (pade_write_le_solver_init t))⟩
end P21Bnd

end LinearSetReconciliation327.Main


