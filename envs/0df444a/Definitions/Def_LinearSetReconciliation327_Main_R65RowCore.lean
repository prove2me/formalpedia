-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_R65RowCore
-- name    : LinearSetReconciliation327_Main_R65RowCore
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-25T14:32:37.236048+00:00
-- url     : https://prove2.me/theorems/ee87822d-0617-4db9-9950-1f7085cc7a71
-- title:
--   Theorem 6.5: executable Pinsketch row decoder
-- statement:
--   Verifies the row decoder on every row syndrome, including its bounds on time and storage and the normalization of rejected outputs.
-- source:
--   Linear Set Reconciliation with O(d) Additive Redundancy, Proposition 2.1 and Section 9.2

import Definitions.Def_LinearSetReconciliation327_Main_R65RowKey
import Definitions.Def_LinearSetReconciliation327_Main_B65_19
import Definitions.Def_LinearSetReconciliation327_Main_B65_20
import Definitions.Def_LinearSetReconciliation327_Main_HintCRFrame20261120

set_option autoImplicit false

section S_P21CoreFor6520261123
/-!
# Proposition 2.1's decoder: bounded zero **and** the weakened `det` contract

The two published weakenings are combined here.

* `Definitions.Def_..._P21BndRead20261122` / `..._P21BndKey20261122` weaken the zero hypothesis to
  the *bounded* one that Theorem 6.5's row loop supplies, but keep `E.det = detStd t N b iota`.
* `Definitions.Def_..._P21DetFront20261121` / `..._P21DetBack20261121` weaken the environment to
  `DetAgrees E t N b iota` (agreement on the ten header slots and on `[detMulBase w, inf)`), but
  keep the *unbounded* `hzero`.

The row body of Theorem 6.5 needs both at once: it must carry `det 2 = R`, `det 3 = rowBase`,
`det 4 = stageLen`, `det 12 = W`, `det 15 = payTab`, `det 16 = stageBase` in the *same* environment
that runs the decoder (`zDetStd_no_rowBody` shows the `detStd` environment cannot even stage a
payload), while the row bitmaps above `decoderAllocEnd t` must survive the run.  So the four stage
contracts are taken at the *combined* weakening:

* `P21DetBnd.pinsketch_decoder_readB` -- read stage, bounded tail, frame, `DetAgrees`;
* `P21Bnd.pinsketch_decoder_key_solverB` -- key solver, bounded `hTail`, solver frame, `DetAgrees`;
* `pinsketch_decoder_root_search` (`Def_..._P21DetBack20261121`) -- `DetAgrees`, with its frame;
* `verifierFrameDet` (below) -- the verifier *with* `MemoryFrame (verifierWritable ...)`,
  `DetAgrees`, reconstructed from the Back bundle's `verifierProcedure_spec` and
  `finishOutput_spec` (the published `pinsketch_decoder_verifier_frame` is stated at `detStd`).

`verifierFrameDet` also records **where the output list lives**:
`s'.regs r0 + s'.regs r1 <= decoderAllocEnd t` (the finish block loads `r0 := outputBase`,
`r1 := count <= t`), which is residual B of the row stage: `RepackPre`'s `listBase + len <= rowSlot j`
follows from it together with the layout facts, and `decoderPost` alone says nothing about it.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 40000
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

namespace P21DetBndComp

/-! The Back bundle's stage contracts were generated from fully qualified declaration texts, so
inside the `Main` namespace they are reachable only under the doubled prefix. -/
alias pinsketch_decoder_root_search :=
  _root_.LinearSetReconciliation327.Main.LinearSetReconciliation327.Main.pinsketch_decoder_root_search

theorem decoderQueue0_eq (t : ℕ) : decoderQueue0 t = 144 + 37 * t := by
  unfold decoderQueue0 decoderRowBase decoderSavedBase decoderCapacity decoderLength
  ring

theorem decoderQueue1_eq (t : ℕ) : decoderQueue1 t = 4 * t * t + 39 * t + 144 := by
  unfold decoderQueue1 decoderCapacity decoderLength
  rw [decoderQueue0_eq]
  ring

theorem decoderOutputBase_eq (t : ℕ) : decoderOutputBase t = 8 * t * t + 41 * t + 144 := by
  unfold decoderOutputBase decoderQueue1 decoderCapacity decoderLength
  rw [decoderQueue0_eq]
  ring

/-! ## 2. The nonlinear estimates, each over `t` (and one index) alone -/

/-- Every one of the eight first row blocks ends inside the scratch.  (`<` would be false at
`t = 0, k = 7`, where both sides equal `144`; `≤` is what the inclusions need.) -/
theorem rowBlock_le (t k : ℕ) (hk : k ≤ 7) :
    decoderRowBase t k + decoderCapacity t ≤ decoderAllocEnd t := by
  rw [decoderAllocEnd_eq]
  unfold decoderRowBase decoderSavedBase decoderCapacity decoderLength
  have h : k * (2 * (2 * t + 1)) ≤ 7 * (2 * (2 * t + 1)) := Nat.mul_le_mul_right _ hk
  nlinarith

/-- The scratch always contains the 144 metadata words. -/
theorem allocEnd_ge_144 (t : ℕ) : 144 ≤ decoderAllocEnd t := by
  rw [decoderAllocEnd_eq]
  nlinarith

/-- The bounded companions of the three metadata predicates of the root search.  Naming their
bounds separately keeps `omega` at the inclusion sites down to *linear* atoms. -/
theorem rootBasisMeta_le (a : ℕ) (h : rootBasisMeta a) : a ≤ 112 := by
  unfold rootBasisMeta rootLevelMeta rootNodeMeta rootComputeMeta at h
  omega

theorem rootComputeMeta_le (a : ℕ) (h : rootComputeMeta a) : a ≤ 98 := by
  unfold rootComputeMeta at h
  omega

theorem rootEmissionMeta_le (a : ℕ) (h : rootEmissionMeta a) : a ≤ 111 := by
  unfold rootEmissionMeta at h
  omega

/-- The first queue block `[decoderQueue0 t, decoderQueue0 t + t·decoderCapacity t)` ends strictly
inside the scratch: `4t² + 39t + 144 < 8t² + 44t + 144`. -/
theorem queue0Block_lt (t : ℕ) (ht : 1 ≤ t) :
    decoderQueue0 t + t * decoderCapacity t < decoderAllocEnd t := by
  rw [decoderAllocEnd_eq, decoderQueue0_eq]
  unfold decoderCapacity decoderLength
  nlinarith

/-- The second queue block ends strictly inside the scratch:
`8t² + 41t + 144 < 8t² + 44t + 144`. -/
theorem queue1Block_lt (t : ℕ) (ht : 1 ≤ t) :
    decoderQueue1 t + t * decoderCapacity t < decoderAllocEnd t := by
  rw [decoderAllocEnd_eq, decoderQueue1_eq]
  unfold decoderCapacity decoderLength
  nlinarith

/-- The root search's output block `[decoderOutputBase t, decoderOutputBase t + t)` ends strictly
inside the scratch: `8t² + 42t + 144 < 8t² + 44t + 144`. -/
theorem outputBlock_lt (t : ℕ) (ht : 1 ≤ t) :
    decoderOutputBase t + t < decoderAllocEnd t := by
  rw [decoderAllocEnd_eq, decoderOutputBase_eq]
  nlinarith


/-! ## 3. The writable sets stay inside `[0, decoderAllocEnd t)` -/

/-- The key solver's write set is inside the scratch. -/
theorem solverInitWritable_lt_allocEnd (t a : ℕ) (ht : 1 ≤ t)
    (h : solverInitWritable t a) : a < decoderAllocEnd t := by
  have h3 := rowBlock_le t 3 (by norm_num)
  have h144 := allocEnd_ge_144 t
  have h4 : decoderRowBase t 4 = decoderRowBase t 3 + decoderCapacity t := by
    unfold decoderRowBase
    ring
  unfold solverInitWritable at h
  omega

/-- The root search's write set is inside the scratch.  This is the inclusion that `omega` cannot
prove directly: `rootBasisWritable` contains the two queue blocks whose ends are the products
`t · decoderCapacity t`, supplied here as the linear atoms `queue0Block_lt` / `queue1Block_lt`. -/
theorem rootSearchWritable_lt_allocEnd (t a : ℕ) (ht : 1 ≤ t)
    (h : rootSearchWritable (decoderRowBase t 0) (decoderRowBase t 6) (decoderRowBase t 1)
          (decoderRowBase t 7) (decoderRowBase t 4) (decoderCapacity t) (decoderQueue0 t)
          (decoderQueue1 t) (decoderOutputBase t) t a) :
    a < decoderAllocEnd t := by
  have h0 := rowBlock_le t 0 (by norm_num)
  have h1 := rowBlock_le t 1 (by norm_num)
  have h4 := rowBlock_le t 4 (by norm_num)
  have h6 := rowBlock_le t 6 (by norm_num)
  have h7 := rowBlock_le t 7 (by norm_num)
  have hq0 := queue0Block_lt t ht
  have hq1 := queue1Block_lt t ht
  have ho := outputBlock_lt t ht
  have h144 := allocEnd_ge_144 t
  unfold rootSearchWritable rootBasisWritable rootComputeWritable rootEmissionWritable at h
  rcases h with hb | he
  · rcases hb with hmeta | hcomp | hq0' | hq1'
    · exact lt_of_le_of_lt (rootBasisMeta_le a hmeta) (by omega)
    · rcases hcomp with hcm | hr | hu | hd | hc | htb
      · exact lt_of_le_of_lt (rootComputeMeta_le a hcm) (by omega)
      · omega
      · omega
      · omega
      · omega
      · omega
    · omega
    · omega
  · rcases he with hemeta | hB
    · exact lt_of_le_of_lt (rootEmissionMeta_le a hemeta) (by omega)
    · omega

/-- The verifier's write set is inside the scratch. -/
theorem verifierWritable_lt_allocEnd (t a : ℕ)
    (h : verifierWritable (decoderVerifyBase t) (2 * t) a) : a < decoderAllocEnd t := by
  have h144 := allocEnd_ge_144 t
  have hE : decoderVerifyBase t + 2 * t = decoderAllocEnd t := rfl
  unfold verifierWritable verifierCoreWritable at h
  omega

/-- **All three stage frames preserve `[decoderAllocEnd t, ∞)`.** -/
theorem frame_above_of_writable {A : ℕ → Prop} {m m' : ℕ → ℕ} {t : ℕ}
    (hA : ∀ a, A a → a < decoderAllocEnd t) (hf : MemoryFrame A m m') :
    ∀ a, decoderAllocEnd t ≤ a → m' a = m a :=
  fun a ha => hf a (fun hc => absurd (hA a hc) (by omega))




/-- **The verifier stage with its frame and the output-location bound, at the weakened `det`
contract.**  The published `pinsketch_decoder_verifier_frame` is stated at
`E.det = detStd t N b iota`; this is the `DetAgrees` form of the same statement, proved from the
Back bundle's `verifierProcedure_spec` (which already returns the `MemoryFrame`) and
`finishOutput_spec` (which shows the finish block does not touch memory and loads
`r0 := output base`, `r1 := count`).  The last conjunct is the row stage's residual B. -/
theorem verifierFrameDet {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {N t w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (y : Fin (t * w) → ZMod 2) (e : ℕ → F)
    (P : Program) (E : RAMEnv) (pc : ℕ) (m : ℕ → ℕ)
    (hAt : At P pc (Stmt.compile verificationFinalProcedure pc))
    (hN : 1 ≤ N) (ht : 1 ≤ t) (hw : 1 ≤ w) (hW : E.W = 8 * w) (hdet : DetAgrees E t N b ι)
    (hEnd : decoderAllocEnd t < 2 ^ E.W) (hNw : N < 2 ^ w)
    (h0 : ∀ i < N, ι i ≠ 0) (hinj : Set.InjOn ι (Set.Iio N))
    (hodd : ∀ k : Fin t, e (2 * k.val) = payloadField b y k)
    (heven : ∀ a : ℕ, 0 < a → e (2 * a - 1) = e (a - 1) ^ 2)
    (hReady : CandidateReady b ι t N e m) :
    Sem P E pc (pc + 432) (boundaryState pc m)
      (fun k z => k ≤ (170 * t + 117) * t + 172 * t + 149 ∧ decoderPost (N := N) b ι y z ∧
        (∀ a, decoderAllocEnd t ≤ a → z.mem a = m a) ∧
        z.regs r0 + z.regs r1 ≤ decoderAllocEnd t) := by
  let us := rootsByBasis b (padeSolve e t).curC
  let xs := rootPositionList N ι us
  have hmin := padeSolve_minimal e t ht
  have hsound := rootsByBasis_sound b (padeSolve e t).curC hmin.1.1
  have hlen : us.length ≤ t := le_trans hsound.2.2 hmin.1.2.1
  have hxslen : xs.length = us.length := by simp [xs, rootPositionList]
  have hg := decoderGeometry_spec E t hEnd
  obtain ⟨hVerAt, hFinishAt⟩ := At.seqStmt hAt
  have hVer := verifierProcedure_spec b ι t N P E pc (decoderSavedBase t) (decoderOutputBase t)
    (decoderVerifyBase t) t (rootPositionFlag N ι us) e xs m hVerAt hw hW hdet
    (by have hh := hg.metadata; omega)
    hNw (rootPositionFlag_le_one N ι us) hg.outputLow hg.outputWord hg.verifyLow hg.verifyFits
    hg.verifyWord hg.savedLow hg.savedWord (Or.inl hg.outputVerify) (Or.inl hg.savedVerify)
    (by rw [hxslen]; exact hlen) (rootPositionList_range N ι us hN) hReady.positions hReady.saved
    hReady.savedBase hReady.output hReady.verification hReady.dimension hReady.tValue
    (by simpa only [hxslen] using hReady.count) hReady.flag
  obtain ⟨_, k1, z1, hrun1, hpc1, hk1, m1, hz1, h100, hbit, hchecks, h85, h101, hout, hf⟩ := hVer
  have hVerExact : Sem P E pc (pc + 423) (boundaryState pc m)
      (fun k z => k ≤ (85 * (2 * t) + 117) * xs.length + 86 * (2 * t) + 140 ∧
        z = boundaryState (pc + 423) m1) :=
    ⟨rfl, k1, z1, hrun1, hpc1, hk1, hz1⟩
  have hc : m1 101 ≤ t := h101.trans_le (hxslen.trans_le hlen)
  obtain ⟨z2, hz2, hpc2, hmem2, hr0, hr1, hr2⟩ := finishOutput_spec E (pc + 423) m1 hg.metadata
    (by rw [h85]; have hh := hg.outputWord; omega)
    (by have hh := hg.outputWord; have hl := hg.outputLow; omega) (by have hh := hg.metadata; omega)
  have hFinish : Sem P E (pc + 423) (pc + 432) (boundaryState (pc + 423) m1)
      (fun k z => k ≤ 9 ∧ z = z2) := by
    have hh := Sem.block P E (pc + 423) finishOutputCode (boundaryState (pc + 423) m1) hFinishAt
      (by simp [finishOutputCode, metaReadCode]) rfl
    exact Sem.mono hh (fun k z hq => ⟨by simpa [finishOutputCode, metaReadCode] using hq.1.le,
      hq.2.trans hz2⟩)
  have hFull := Sem.seq_bound hVerExact (fun z _ hz => by subst z; exact hFinish)
  refine Sem.mono hFull ?_
  intro k z hQ
  obtain ⟨hk, rfl⟩ := hQ
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hh : (85 * (2 * t) + 117) * xs.length ≤ (170 * t + 117) * t := by
      calc
        _ = (170 * t + 117) * xs.length := by ring
        _ ≤ _ := Nat.mul_le_mul_left (170 * t + 117) (hxslen.trans_le hlen)
    omega
  · apply decoder_correct_of_candidate_checks b ι y e z (decoderOutputBase t) hN ht (by omega) h0
      hinj hodd heven
    · rw [hr2]; exact hbit
    · exact hr0.trans h85
    · exact hr1.trans (h101.trans hxslen)
    · rw [hmem2]; exact hout
    · rw [hr2]; exact hchecks
  · intro a ha
    rw [hmem2]
    exact frame_above_of_writable (verifierWritable_lt_allocEnd t) hf a ha
  · rw [hr0, hr1, h85, h101]
    have hl : xs.length ≤ t := hxslen.trans_le hlen
    unfold decoderAllocEnd decoderVerifyBase
    omega


section Glue




end Glue



section Main

variable {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {N t w : ℕ}

/-- The universe embeds into the field, so `N < 2^w`. -/
theorem layerUniverse_lt_two_pow {N w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (h0 : ∀ i < N, ι i ≠ 0) (hinj : Set.InjOn ι (Set.Iio N)) : N < 2 ^ w := by
  classical
  letI : Fintype F := Fintype.ofEquiv (Fin w → ZMod 2) b.equivFun.toEquiv.symm
  have hcard : Fintype.card F = 2 ^ w := by
    calc
      Fintype.card F = Fintype.card (Fin w → ZMod 2) := Fintype.card_congr b.equivFun.toEquiv
      _ = 2 ^ w := by simp
  let D : Finset F := Finset.univ.image (fun i : Fin N => ι i.val)
  have hDcard : D.card = N := by
    dsimp only [D]
    rw [Finset.card_image_of_injOn (fun i _ j _ hij => Fin.ext (hinj i.isLt j.isLt hij))]
    simp
  have hD0 : (0 : F) ∉ D := by
    intro hz
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hz
    exact h0 i.val i.isLt hi
  have hle : (insert 0 D).card ≤ (Finset.univ : Finset F).card :=
    Finset.card_le_card (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_insert_of_notMem hD0, Finset.card_univ, hcard, hDcard] at hle
  omega

/-- A nonempty universe forces a nonzero word width. -/
theorem layerDimension_pos {N w : ℕ} (hN : 1 ≤ N) (hNw : N < 2 ^ w) : 1 ≤ w := by
  by_contra h
  have hw : w = 0 := by omega
  rw [hw] at hNw
  norm_num at hNw
  omega





theorem layerInputSaved_length : inputSavedProcedure.len = 110 := rfl

theorem layerKeySolver_length : keySolverProcedure.len = 960 := by
  simp only [keySolverProcedure, Stmt.len, solverInitializationProcedure_length]
  rfl

theorem layerRootSearch_length : rootSearchProcedure.len = 4047 := rfl







/-! ## The bounded composition -/




/-- **The decoder core at the bounded hypothesis.**  The accepted `positiveDecoderStmt_spec`,
re-derived from the bounded read stage (started at an arbitrary ambient memory `m` that agrees with
`hintMem` only on the workspace), the bounded key solver, the root search and the verifier with its
frame.  The conclusion adds `∀ a ≥ decoderAllocEnd t, z.mem a = m a`. -/
theorem layerPositiveDecoder_semB (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (y : Fin (t * w) → ZMod 2) (P : Program) (E : RAMEnv) (pc : ℕ) (m : ℕ → ℕ)
    (hAt : At P pc (Stmt.compile positiveDecoderStmt pc))
    (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N) (hW : E.W = 8 * w)
    (hdet : DetAgrees E t N b ι) (h0 : ∀ i < N, ι i ≠ 0) (hinj : Set.InjOn ι (Set.Iio N))
    (hmem : ∀ a, a < decoderAllocEnd t → m a = hintMem (8 * w) y [] a) :
    Sem P E pc (pc + positiveDecoderStmt.len) ⟨pc, (decoderStart (8 * w) y []).regs, m⟩
      (fun k z => k ≤ positiveDecoderBudget t w ∧ decoderPost (N := N) b ι y z ∧
        (∀ a, decoderAllocEnd t ≤ a → z.mem a = m a) ∧
        z.regs r0 + z.regs r1 ≤ decoderAllocEnd t) := by
  have hNw := layerUniverse_lt_two_pow b ι h0 hinj
  have hw := layerDimension_pos hN hNw
  have hEnd : decoderAllocEnd t < 2 ^ E.W := by
    rw [hW]
    exact decoderAllocEnd_fits t w hw (lt_of_le_of_lt htN hNw)
  have hpow : 2 ^ w ≤ 2 ^ E.W := Nat.pow_le_pow_right (by norm_num) (by omega)
  have htfit : t < 2 ^ E.W := lt_of_lt_of_le (lt_of_le_of_lt htN hNw) hpow
  have hwfit : w < 2 ^ E.W := lt_of_lt_of_le Nat.lt_two_pow_self hpow
  have hNfit : N < 2 ^ E.W := lt_of_lt_of_le hNw hpow
  have hh0 : E.det 0 % 2 ^ E.W = t := by
    rw [hdet.1 0 (by decide), detStd_hdr t N w b ι (by norm_num : 0 < 13), hdrTab_zero, Nat.mod_eq_of_lt htfit]
  have hh1 : E.det 1 % 2 ^ E.W = w := by
    rw [hdet.1 1 (by decide), detStd_hdr t N w b ι (by norm_num : 1 < 13), hdrTab_one, Nat.mod_eq_of_lt hwfit]
  have hh2 : E.det 2 % 2 ^ E.W = N := by
    rw [hdet.1 2 (by decide), detStd_hdr t N w b ι (by norm_num : 2 < 13)]
    exact Nat.mod_eq_of_lt hNfit
  obtain ⟨hInputAt, hTailAt⟩ := At.seqStmt hAt
  have hTailAt' : At P (pc + 110)
      (Stmt.compile (.seq keySolverProcedure (.seq rootSearchProcedure verificationFinalProcedure))
        (pc + 110)) := by
    simpa only [layerInputSaved_length] using hTailAt
  obtain ⟨hKeyAt, hRootFinalAt⟩ := At.seqStmt hTailAt'
  have hRootFinalAt' : At P (pc + 1070)
      (Stmt.compile (.seq rootSearchProcedure verificationFinalProcedure) (pc + 1070)) := by
    simpa only [layerKeySolver_length] using hRootFinalAt
  obtain ⟨hRootAt, hFinalRaw⟩ := At.seqStmt hRootFinalAt'
  have hFinalAt : At P (pc + 5117) (Stmt.compile verificationFinalProcedure (pc + 5117)) := by
    simpa only [layerRootSearch_length] using hFinalRaw
  have hFull := Sem.seq_bound (P21DetBnd.pinsketch_decoder_readB E P pc N t w y b ι m hInputAt hW hw
      hNw htN hdet hmem) (fun z _ hz => by
      obtain ⟨m1, rfl, hSaved, hPoly, hZero, hFrame⟩ := hz
      have hf1 : ∀ a, decoderAllocEnd t ≤ a → m1 a = m a := hFrame
      exact Sem.seq_bound (P21Bnd.pinsketch_decoder_key_solverB b ι t N P E (pc + 110) (eSeq b y) m1
          hKeyAt hw hW hdet ht hEnd (h0 0 (by omega)) hh0 hh1 hh2 hSaved hZero) (fun z _ hz => by
        obtain ⟨m2, rfl, hReady, hfSolver⟩ := hz
        have hf2 : ∀ a, decoderAllocEnd t ≤ a → m2 a = m1 a :=
          frame_above_of_writable (fun x hx => solverInitWritable_lt_allocEnd t x ht hx) hfSolver
        exact Sem.seq_bound (pinsketch_decoder_root_search b ι t N P E (pc + 1070) (eSeq b y) m2
            hRootAt hw hW hdet ht hEnd hNw hReady) (fun z _ hz => by
          obtain ⟨m3, rfl, hCandidate, hfRoot⟩ := hz
          have hf3 : ∀ a, decoderAllocEnd t ≤ a → m3 a = m2 a :=
            frame_above_of_writable (fun x hx => rootSearchWritable_lt_allocEnd t x ht hx) hfRoot
          have hVerFrame : Sem P E (pc + 5117) (pc + 5117 + 432) (boundaryState (pc + 5117) m3)
              (fun k z => k ≤ (170 * t + 117) * t + 172 * t + 149 ∧ decoderPost (N := N) b ι y z ∧
                (∀ a, decoderAllocEnd t ≤ a → z.mem a = m3 a) ∧
                z.regs r0 + z.regs r1 ≤ decoderAllocEnd t) :=
            verifierFrameDet b ι y (eSeq b y) P E (pc + 5117) m3
              hFinalAt hN ht hw hW hdet hEnd hNw h0 hinj (fun k => eSeq_even b y k.val)
              (fun a _ => by
                rw [show 2 * a - 1 = 2 * (a - 1) + 1 by omega]
                exact eSeq_odd b y (a - 1))
              hCandidate
          have hVerAll : Sem P E (pc + 5117) (pc + 5117 + 432) (boundaryState (pc + 5117) m3)
              (fun k z => k ≤ (170 * t + 117) * t + 172 * t + 149 ∧ decoderPost (N := N) b ι y z ∧
                (∀ a, decoderAllocEnd t ≤ a → z.mem a = m a) ∧
                z.regs r0 + z.regs r1 ≤ decoderAllocEnd t) :=
            Sem.mono (Q' := fun k z => k ≤ (170 * t + 117) * t + 172 * t + 149 ∧
                decoderPost (N := N) b ι y z ∧ (∀ a, decoderAllocEnd t ≤ a → z.mem a = m a) ∧
                z.regs r0 + z.regs r1 ≤ decoderAllocEnd t)
              hVerFrame (fun k z hq => by
                obtain ⟨hk, hpost, hf4, hloc⟩ := hq
                exact ⟨hk, hpost, fun a ha => by rw [hf4 a ha, hf3 a ha, hf2 a ha, hf1 a ha], hloc⟩)
          exact hVerAll)))
  refine Sem.mono hFull ?_
  intro k z hz
  obtain ⟨hk, hpost, hfr, hloc⟩ := hz
  refine ⟨?_, hpost, hfr, hloc⟩
  dsimp only [positiveDecoderBudget] at hk ⊢
  omega





end Main

end P21DetBndComp

end LinearSetReconciliation327.Main
end S_P21CoreFor6520261123

section S_RowNormalize6520261123
set_option autoImplicit false
namespace LinearSetReconciliation327.Main.RSD

/-- Keep a successful row list. Use the empty estimate on decoder rejection. -/
def rowNormalizeOutput : List Instr :=
  [iImm r3 0, iLt r3 r3 r2, iMul r1 r1 r3]



end LinearSetReconciliation327.Main.RSD
end S_RowNormalize6520261123

section S_RowSourceCompat6520261123
set_option autoImplicit false
namespace LinearSetReconciliation327.Main.Top65

/-- Only the fixed Pinsketch core is used in a virtual row arena. Its initial
registers and memory have the source word width and its own deterministic table. -/
def rowSource : Program := positiveDecoderStmt.compile 0 ++ [.halt]

theorem rowSource_halts {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F]
    {w t N : ℕ} (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (y : Fin (t * w) → ZMod 2)
    (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (h0 : ∀ i < N, ι i ≠ 0) (hinj : Set.InjOn ι (Set.Iio N)) :
    ∃ out, HaltsWithin rowSource (detEnv (8 * w) (detStd t N b ι))
      (positiveDecoderBudget t w : ℝ) (decoderStart (8 * w) y []) out ∧
      out.pc = positiveDecoderStmt.len ∧ decoderPost (N := N) b ι y out ∧
      out.regs r0 + out.regs r1 ≤ decoderAllocEnd t := by
  let W := 8 * w
  let dt := detStd t N b ι
  let E := detEnv W dt
  let s : RAMState := decoderStart W y []
  have hAt : At rowSource 0 (positiveDecoderStmt.compile 0) := by
    intro a ha
    rw [Nat.zero_add]
    exact List.getElem?_append_left ha
  have hAgrees : DetAgrees E t N b ι := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hRun := P21DetBndComp.layerPositiveDecoder_semB b ι y rowSource E 0 s.mem hAt
    hN ht htN rfl hAgrees h0 hinj (fun _ _ => rfl)
  obtain ⟨_, k, out, hStep, hPc, hk, hPost, _, hLoc⟩ := hRun
  have he : (⟨0, (decoderStart (8 * w) y []).regs, s.mem⟩ : RAMState) = s := rfl
  rw [he] at hStep
  have hEnd : out.pc = positiveDecoderStmt.len := by simpa only [Nat.zero_add] using hPc
  have hHalt : Halted rowSource out := by
    unfold Halted
    rw [hEnd, ← Stmt.length_compile positiveDecoderStmt 0]
    simp [rowSource]
  exact ⟨out, ⟨k, by exact_mod_cast hk, hStep, hHalt⟩, hEnd, hPost, hLoc⟩

end LinearSetReconciliation327.Main.Top65
end S_RowSourceCompat6520261123

section S_RowBudget6520261123
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
theorem positiveDecoderBudget_mono {t w s : ℕ} (ht : t ≤ s) (hw : w ≤ s) :
    positiveDecoderBudget t w ≤ positiveDecoderBudget s s := by
  unfold positiveDecoderBudget rootPhaseBudget rootNodeBudget decoderCapacity decoderLength
  gcongr

theorem positiveDecoderBudget_diagonal (s : ℕ) :
    positiveDecoderBudget s s = 960 * s ^ 5 + 3606 * s ^ 4 + 5061 * s ^ 3 + 4695 * s ^ 2 + 2861 * s + 1681 := by
  unfold positiveDecoderBudget rootPhaseBudget rootNodeBudget decoderCapacity decoderLength
  ring

theorem decoderBudget_bound (t w : ℕ) :
    positiveDecoderBudget t w + 10 ≤ 20000 * (t + w + 1) ^ 6 := by
  let s := t + w + 1
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hm := positiveDecoderBudget_mono (show t ≤ s by dsimp [s]; omega) (show w ≤ s by dsimp [s]; omega)
  rw [positiveDecoderBudget_diagonal] at hm
  have hp (i : ℕ) (hi : i ≤ 6) : s ^ i ≤ s ^ 6 := Nat.pow_le_pow_right hs hi
  have h0 := hp 0 (by norm_num)
  have h1 := hp 1 (by norm_num)
  have h2 := hp 2 (by norm_num)
  have h3 := hp 3 (by norm_num)
  have h4 := hp 4 (by norm_num)
  have h5 := hp 5 (by norm_num)
  change positiveDecoderBudget t w + 10 ≤ 20000 * s ^ 6
  simp only [pow_zero, pow_one] at h0 h1
  omega


end LinearSetReconciliation327.Main
end S_RowBudget6520261123


