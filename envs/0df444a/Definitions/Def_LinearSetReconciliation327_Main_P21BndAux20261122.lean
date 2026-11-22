-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_P21BndAux20261122
-- name    : LinearSetReconciliation327_Main_P21BndAux20261122
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T06:02:17.161571+00:00
-- url     : https://prove2.me/theorems/d9781956-e3c5-4d41-a8a4-93f7c831d14e
-- title:
--   The row-loop side conditions of Proposition 2.1 at a bounded zero hypothesis: writable sets inside the scratch, and the beta = L layout
-- statement:
--   **The row-loop side conditions for Proposition 2.1 at a bounded zero hypothesis.**
--
--   Theorem 6.5 runs Proposition 2.1's decoder $d$ times inside one memory, driving it from the bounded
--   zero hypothesis $m = 0$ on $[L,\beta)$ and on $[\beta+L,\mathsf{decoderAllocEnd}(t))$, where
--   $L=\lceil tw/(8w)\rceil$ and $\beta$ is the staging base.  This bundle supplies the two side
--   conditions that the composition needs and that ordinary linear arithmetic cannot see.
--
--   *Writable sets inside the scratch.*  Each stage carries a frame `MemoryFrame A m m'` for its own
--   write set $A$; to conclude that nothing at or above $\mathsf{decoderAllocEnd}(t)=8t^2+44t+144$ moves,
--   one needs $A\subseteq[0,\mathsf{decoderAllocEnd}(t))$.  For the key solver
--   ($A=\mathsf{solverInitWritable}(t)$) and the verifier ($A=\mathsf{verifierWritable}$) this is linear.
--   For the root search the write set contains the two queue blocks
--   $[\mathsf{decoderQueue0}(t),\ \mathsf{decoderQueue0}(t)+t\cdot\mathsf{decoderCapacity}(t))$ and
--   $[\mathsf{decoderQueue1}(t),\ \mathsf{decoderQueue1}(t)+t\cdot\mathsf{decoderCapacity}(t))$ and the
--   output block $[\mathsf{decoderOutputBase}(t),\ \mathsf{decoderOutputBase}(t)+t)$, whose right ends are
--
--   $$4t^2+39t+144,\qquad 8t^2+41t+144,\qquad 8t^2+42t+144,$$
--
--   all strictly below $8t^2+44t+144$ for $t\ge 1$.  These are *nonlinear* in $t$ ($t\cdot\mathsf{cap}$ is
--   a product of variables), so $\omega$ cannot prove them; each is proved here as a standalone lemma
--   over $t$ alone by `nlinarith` in a three-hypothesis context (this project has measured 18–29 s
--   `nlinarith` explosions in the key solver's 40-hypothesis context), after which the set inclusions go
--   through by $\omega$ over the resulting linear atoms.
--
--   *$hzeroB$ is inhabited.*  The clearing pass `clearFull 0 (decoderAllocEnd t)` zeroes exactly the
--   scratch and frames everything above it, so the memory it produces is the pure function
--   $\mathrm{clearMem}(0,m,\mathsf{decoderAllocEnd}(t))$; the staging block of the row loop writes
--   exactly the block $[\beta,\beta+L)$ and nothing else, so it cannot disturb zeros outside that block.
--   The bundle proves the staging block's *memory equation* — which the published `stage_sem` discards —
--   and hence that staging preserves `hzeroB`'s two zero intervals.
--
--   *$\beta=L$ satisfies the layout condition.*  With $\beta=L$ the condition $\beta+2L\le
--   \mathsf{decoderAllocEnd}(t)$ reads $3L\le 8t^2+44t+144$, true for every $t\ge 1$ because
--   $L=\lceil tw/(8w)\rceil\le t$.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5 (the row loop) driving Proposition 2.1's decoder; the verified development of the project (`Definitions.Def_…_RowScratch20261121`, `Definitions.Def_…_RowDecode20261121`).

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_DecoderLemmas
import Definitions.Def_LinearSetReconciliation327_Main_RowScratch20261121
import Definitions.Def_LinearSetReconciliation327_Main_RowDecode20261121

/-!
# The bounded-zero row-loop side conditions: writable-set bounds and the `β = L` layout

Theorem 6.5's row loop drives Proposition 2.1's decoder from the *bounded* zero hypothesis

  `(∀ a, L ≤ a → a < β → m a = 0) ∧ (∀ a, β + L ≤ a → a < decoderAllocEnd t → m a = 0)`

(`hzeroB`) with the layout side condition `hβ2 : β + 2L ≤ decoderAllocEnd t`.  Two gaps remain
after the three bounded stage contracts are published:

* **the writable sets must stay inside the scratch.**  The key solver's frame is
  `solverInitWritable t`, the root search's is `rootSearchWritable …`, the verifier's is
  `verifierWritable …`; to turn them into "nothing at or above `decoderAllocEnd t` moves" one needs
  `A addr → addr < decoderAllocEnd t`.  For the root search this is *nonlinear*: its two queue blocks
  end at `decoderQueue0 t + t·decoderCapacity t = 4t² + 39t + 144` and
  `decoderQueue1 t + t·decoderCapacity t = 8t² + 41t + 144`, and the output block at
  `8t² + 42t + 144`, all against `decoderAllocEnd t = 8t² + 44t + 144`; `omega` cannot see this
  because `t · decoderCapacity t` is a product of variables.  Each estimate is proved here as a
  standalone lemma over `(t, ·)` alone — `nlinarith` in the key solver's 40-hypothesis context has
  cost 18–29 s in this project, while here it sees three hypotheses — and the set inclusions then
  follow by `omega` over the resulting *linear* atoms.

* **`hzeroB` is inhabited and `hβ2` is satisfiable.**  `clearScratch_sem` zeroes exactly
  `[0, decoderAllocEnd t)` and frames everything above it, so the memory after the clearing pass is
  the pure function `clearMem 0 m (decoderAllocEnd t)`; the staging block writes exactly the block
  `[stageBase E, stageBase E + stageLen E)` (`stage_mem_writeArray`, proved from the same run
  decomposition as `stage_sem` but carrying the memory equation that `stage_sem` discards), hence it
  cannot disturb zeros outside that block (`stage_preserves_zero_outside`).  With `β = L` the layout
  condition is `3L ≤ 8t² + 44t + 144`, which holds for every `t ≥ 1` because `L = wordsOf (8w) (tw)
  ≤ t` (`stageBase_self_fits`).

**Reported gap (not vacuous, and not repairable from the published interface).**  The two blocks
cannot be glued into a single `Sem` from the published contracts alone: `clearScratch_sem` leaves
`r1 = decoderAllocEnd t` in the register file (`clearInit` loads `r1 := L`), while `stage_sem` needs
`r1 = j` to read the row-`j` payload table entry.  The row loop therefore needs a one-instruction
`r1 := j` reload between the clearing pass and the staging block; that instruction is not part of
either published interface, so the glue theorem is stated here at the memory level (where it is
kernel-checked) rather than as one `Sem` chain.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Finset

namespace LinearSetReconciliation327.Main

open LinearSetReconciliation327.Main.R66
open LinearSetReconciliation327.Main.RDec

/-! ## 1. Concrete layout values of the decoder's scratch -/

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

theorem scratch_pos (t : ℕ) : 0 < decoderAllocEnd t := by
  rw [decoderAllocEnd_eq]
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

/-! ## 4. The staging block writes exactly one block -/

/-- **The memory equation `stage_sem` discards.**  The staging block (`stageStmt`, 42 instructions)
leaves the memory equal to `writeArray (stageBase E) m (fun i => m (rowPayBase E j + i))
(stageLen E)`.  Same run decomposition as `stage_sem` (`head ++ copy ++ zeroRegsCode`), but the
conclusion keeps the final memory. -/
theorem stage_mem_writeArray {P : Program} {E : RAMEnv} {pc j : ℕ} {m : ℕ → ℕ}
    {r : Fin 16 → ℕ}
    (hAt : At P pc (Stmt.compile stageStmt pc)) (hW : 1 < 2 ^ E.W) (hW16 : 16 < 2 ^ E.W)
    (hj : r r1 = j)
    (hdst : stageBase E + stageLen E ≤ 2 ^ E.W)
    (hsrc : rowPayBase E j + stageLen E ≤ 2 ^ E.W)
    (hword : ∀ i, i < stageLen E → m (rowPayBase E j + i) < 2 ^ E.W)
    (hdisj : rowPayBase E j + stageLen E ≤ stageBase E ∨
      stageBase E + stageLen E ≤ rowPayBase E j) :
    Sem P E pc (pc + stageStmt.len) ⟨pc, r, m⟩
      (fun k s' => k ≤ stageCost E ∧
        s' = ⟨pc + stageStmt.len, zeroRegs,
          writeArray (stageBase E) m (fun i => m (rowPayBase E j + i)) (stageLen E)⟩) := by
  have hAt2 : At P pc (stageHeadCode ++ (copyStmt.compile (pc + 14) ++ zeroRegsCode)) := by
    simpa only [stageStmt, Stmt.compile, Stmt.len, stageHeadCode_length] using hAt
  obtain ⟨hheadAt, hrest⟩ := At.append.mp hAt2
  have hrest2 : At P (pc + 14) (copyStmt.compile (pc + 14) ++ zeroRegsCode) := by
    simpa only [stageHeadCode_length] using hrest
  obtain ⟨hcopyAt, hzAt⟩ := At.append.mp hrest2
  have hzAt2 : At P (pc + 14 + 12) zeroRegsCode := by
    simpa only [Stmt.length_compile, copyStmt, copyCond, copyBody, Cond.code, Stmt.len,
      List.length_cons, List.length_nil] using hzAt
  have hhead : Sem P E pc (pc + 14) ⟨pc, r, m⟩
      (fun k s' => k ≤ 14 ∧ s' = copyState (pc + 14) (stageBase E) (rowPayBase E j) (stageLen E) m
        (stageHeadRegs (stageLen E) (stageBase E) (rowPayBase E j) r) 0) := by
    refine Sem.mono (Sem.block P E pc stageHeadCode _ hheadAt stageHeadCode_noBranch rfl) ?_
    intro k s' h
    obtain ⟨hk, hs⟩ := h
    rw [stageHeadCode_length] at hk
    refine ⟨by omega, ?_⟩
    rw [hs, stageHead_run E pc j m r hW hW16 hj, stageHeadOut_eq_copyState]
  have hcopy : Sem P E (pc + 14) (pc + 14 + 12)
      (copyState (pc + 14) (stageBase E) (rowPayBase E j) (stageLen E) m
        (stageHeadRegs (stageLen E) (stageBase E) (rowPayBase E j) r) 0)
      (fun k s' => k ≤ 12 * stageLen E + 2 ∧
        s' = { copyState (pc + 14) (stageBase E) (rowPayBase E j) (stageLen E) m
          (stageHeadRegs (stageLen E) (stageBase E) (rowPayBase E j) r) (stageLen E)
          with pc := pc + 14 + 12 }) :=
    RDec.copyArray_spec P E (pc + 14) (stageBase E) (rowPayBase E j) (stageLen E) m _ hcopyAt
      hW hdst hsrc hword hdisj
  have hz : Sem P E (pc + 14 + 12) (pc + 14 + 12 + 16)
      { copyState (pc + 14) (stageBase E) (rowPayBase E j) (stageLen E) m
        (stageHeadRegs (stageLen E) (stageBase E) (rowPayBase E j) r) (stageLen E)
        with pc := pc + 14 + 12 }
      (fun k s' => k ≤ 16 ∧ s' = ⟨pc + 14 + 12 + 16, zeroRegs,
        writeArray (stageBase E) m (fun i => m (rowPayBase E j + i)) (stageLen E)⟩) := by
    refine Sem.mono (Sem.block P E (pc + 14 + 12) zeroRegsCode _ hzAt2
      (by simp [zeroRegsCode, NoBranch, Instr.NoBranchI]) rfl) ?_
    intro k s' h
    obtain ⟨hk, hs⟩ := h
    rw [zeroRegsCode_length] at hk
    refine ⟨by omega, ?_⟩
    rw [hs]
    exact zeroRegsCode_run E (pc + 14 + 12) _ _
  refine Sem.mono (R66.Sem.trans_le (R66.Sem.trans_le hhead hcopy) hz) ?_
  intro k s' h
  obtain ⟨hk, hs⟩ := h
  rw [hs]
  have hcost : k ≤ stageCost E := by unfold stageCost; omega
  exact ⟨hcost, by rw [stageStmt_len]⟩

/-- **The staging block does not disturb zeros outside `[stageBase E, stageBase E + stageLen E)`.**
So if the scratch is zero on `[0, K)` and the payload sits above `K` (`K ≤ rowPayBase E j`), then
after staging the memory is zero on `[stageLen E, stageBase E)` and on
`[stageBase E + stageLen E, K)` — the two conjuncts of `hzeroB` (with `L = stageLen E`,
`β = stageBase E`). -/
theorem stage_preserves_zero_outside {P : Program} {E : RAMEnv} {pc j K : ℕ} {m : ℕ → ℕ}
    {r : Fin 16 → ℕ}
    (hAt : At P pc (Stmt.compile stageStmt pc)) (hW : 1 < 2 ^ E.W) (hW16 : 16 < 2 ^ E.W)
    (hj : r r1 = j)
    (hdst : stageBase E + stageLen E ≤ 2 ^ E.W)
    (hsrc : rowPayBase E j + stageLen E ≤ 2 ^ E.W)
    (hword : ∀ i, i < stageLen E → m (rowPayBase E j + i) < 2 ^ E.W)
    (hdisj : rowPayBase E j + stageLen E ≤ stageBase E ∨
      stageBase E + stageLen E ≤ rowPayBase E j)
    (hzeroK : ∀ a, a < K → m a = 0)
    (hβL : stageBase E + stageLen E ≤ K) :
    Sem P E pc (pc + stageStmt.len) ⟨pc, r, m⟩
      (fun k s' => k ≤ stageCost E ∧
        (∀ a, stageLen E ≤ a → a < stageBase E → s'.mem a = 0) ∧
        (∀ a, stageBase E + stageLen E ≤ a → a < K → s'.mem a = 0)) := by
  have hword' : ∀ i, i < stageLen E → m (rowPayBase E j + i) < 2 ^ E.W := hword
  refine Sem.mono (stage_mem_writeArray (P := P) (E := E) (pc := pc) (j := j) (m := m) (r := r)
    hAt hW hW16 hj hdst hsrc hword' hdisj) ?_
  intro k s' h
  obtain ⟨hk, hs⟩ := h
  refine ⟨hk, ?_, ?_⟩
  · intro a hLa haβ
    rw [hs]
    show writeArray (stageBase E) m (fun i => m (rowPayBase E j + i)) (stageLen E) a = 0
    rw [writeArray_frame (stageBase E) m _ (stageLen E) a (Or.inl haβ)]
    exact hzeroK a (by omega)
  · intro a ha haK
    rw [hs]
    show writeArray (stageBase E) m (fun i => m (rowPayBase E j + i)) (stageLen E) a = 0
    rw [writeArray_frame (stageBase E) m _ (stageLen E) a (Or.inr ha)]
    exact hzeroK a (by omega)

/-! ## 5. The clearing pass leaves exactly `clearMem 0 m (decoderAllocEnd t)` -/

/-- `clearScratch_sem`, repackaged as "the memory after the clearing pass is the pure function
`clearMem 0 m (decoderAllocEnd t)`".  This is the first half of `hzeroB`: zeros on the whole scratch
and a frame above it. -/
theorem clearScratch_mem_eq {P : Program} {E : RAMEnv} {pc t : ℕ} {s : RAMState}
    (hAt : At P pc (Stmt.compile (clearFull 0 (decoderAllocEnd t)) pc))
    (hW : 1 < 2 ^ E.W) (hK : decoderAllocEnd t < 2 ^ E.W) (hpc : s.pc = pc) :
    ∃ k s', k ≤ 15 + 8 * decoderAllocEnd t ∧ (step P E)^[k] s = s' ∧
      s'.mem = clearMem 0 s.mem (decoderAllocEnd t) ∧ s'.pc = pc + 15 := by
  obtain ⟨k, s', hk, hstep, hz, hfr, hpc'⟩ :=
    clearScratch_sem (P := P) (E := E) (pc := pc) (t := t) (s := s) hAt hW hK hpc
  refine ⟨k, s', hk, hstep, ?_, hpc'⟩
  funext a
  by_cases ha : a < decoderAllocEnd t
  · rw [hz a ha]
    symm
    simpa using clearMem_get 0 s.mem (decoderAllocEnd t) a ha
  · rw [hfr a (by omega)]
    symm
    simpa using clearMem_frame 0 s.mem (decoderAllocEnd t) a (Or.inr (by omega))

/-! ## 6. `β = L` satisfies the layout condition `β + 2L ≤ decoderAllocEnd t` -/

/-- **`hβ2` at `β = L`.**  With `L = stageLen E = wordsOf (8w) (tw)` and `L ≤ t`, the layout
condition reads `3L ≤ 8t² + 44t + 144`, true for every `t ≥ 1`. -/
theorem stageBase_self_fits {E : RAMEnv} {t w : ℕ}
    (hL : stageLen E = wordsOf (8 * w) (t * w)) (hβ : stageBase E = stageLen E) (hw : 1 ≤ w) :
    stageBase E + 2 * stageLen E ≤ decoderAllocEnd t := by
  have hle : wordsOf (8 * w) (t * w) ≤ t := wordsOf_le w t hw
  rw [hβ, hL, decoderAllocEnd_eq]
  nlinarith

end LinearSetReconciliation327.Main


