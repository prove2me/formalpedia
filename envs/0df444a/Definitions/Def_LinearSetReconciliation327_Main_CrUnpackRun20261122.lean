-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_CrUnpackRun20261122
-- name    : LinearSetReconciliation327_Main_CrUnpackRun20261122
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T07:08:32.021656+00:00
-- url     : https://prove2.me/theorems/d96ac8f8-46a0-4148-a1ec-aa61466f1393
-- title:
--   The unpack block of the CR stage: a packed estimate becomes a coordinate list
-- statement:
--   This bundle supplies the missing `StageRun` of the unpack block `upkStmt` that Proposition 2.3's decoder must be followed by before the merge of Theorem 6.5 can run. The block reads the packed `m`-word payload at word $x_{\mathrm{base}}$, walks the $mW$ bits one by one, and writes the coordinates of the set bits into the list block $[ab, ab+\#\mathrm{supp})$, restoring the decoder's output window $(r_0,r_1)=(b_b,b_l)$ and loading the merge's five arguments $r_{10}\dots r_{14}$ on the way out.  The theorem `stageRun_unpack` says: from any state satisfying `UpkIn` (the seven entry registers plus the packed-payload invariant `HoldsVecPad`), the compiled block reaches `base + 31` within $16\,m\,W + 17$ word-RAM steps and leaves `UpkOut` \u2014 the list at $[ab, ab+\#\mathrm{supp})$ *is* `packedSupp`, the payload invariant is still in force, and the decoder's window is intact.  Nothing is assumed beyond the word-fit side conditions $W\cdot m < 2^W$ and $ab + W\cdot m + 1 < 2^W$ (the scan's stores must not wrap) and the disjointness $x_{\mathrm{base}} + m \le ab$ of the payload from the list destination (which is what makes the scan's frame lemma applicable).
-- source:
--   arXiv:2611.11409 (Liu, Xu, Yang, Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5's `cr` stage and \u00a72.3; the program and its three `runBlock` lemmas are the accepted development `Solutions/Sol_proposition_2_3.lean`'s unpack block, published as `Def_LinearSetReconciliation327_Main_CrStageDec20261122`. This bundle adds the `Sem` composition, the `HaltsWithin` bridge and the relocation.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_CrStageDec20261122
import Definitions.Def_LinearSetReconciliation327_Main_CrStage20261122

/-!
# The unpack block's `StageRun`: packed estimate → coordinate list

`Def_…_CrStageDec20261122` defines the unpack program `upkStmt` (`upkPre`; a single scan loop over
`p < m·W`; `upkEpilogue`), proves its three straight-line runs and its loop head as `runBlock`
equations, and proves the semantic content `upkList W xbase s.mem (W·m) = packedSupp W m y`.

What was missing is the assembled `StageRun`: the `Sem` composition of the three pieces
(`Sem.block` / `Sem.loop` / `Sem.seq`), the bridge to `HaltsWithin`, and the relocation to an
arbitrary base by `stageRun_of_haltsWithin_shift`.  That is what this file supplies.  The cost is
`16·m·W + 17 = 11 + (16·m·W + 2) + 4`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

open scoped ENNReal
open Finset

noncomputable section

namespace LinearSetReconciliation327.Main
namespace CRS

/-! ## 0. `At` for the unpack statement -/

theorem at_self_zero (P : Program) : At P 0 P := by
  intro r hr
  rw [Nat.zero_add]

/-- The unpack program, spelled out. -/
abbrev upkProg : Program :=
  (upkPre ++ (Stmt.compile (Stmt.loop upkCond (.code upkBody)) 11 ++ upkEpilogue)) ++ [iHalt]

theorem upk_prog_eq : programOfStatement upkStmt = upkProg := rfl

theorem upk_at_pre : At (programOfStatement upkStmt) 0 upkPre := by
  rw [upk_prog_eq]
  have h : At upkProg 0 upkProg := at_self_zero _
  exact (At.append.mp (At.append.mp h).1).1

theorem upk_at_loop :
    At (programOfStatement upkStmt) 11 (Stmt.compile (Stmt.loop upkCond (.code upkBody)) 11) := by
  rw [upk_prog_eq]
  have h : At upkProg 0 upkProg := at_self_zero _
  have h2 := (At.append.mp (At.append.mp h).1).2
  rw [show (0 : ℕ) + upkPre.length = 11 from by rw [upkPre_length]] at h2
  exact (At.append.mp h2).1

theorem upk_at_epi : At (programOfStatement upkStmt) 27 upkEpilogue := by
  rw [upk_prog_eq]
  have h : At upkProg 0 upkProg := at_self_zero _
  have h2 := (At.append.mp (At.append.mp h).1).2
  rw [show (0 : ℕ) + upkPre.length = 11 from by rw [upkPre_length]] at h2
  have h3 := (At.append.mp h2).2
  rw [show 11 + (Stmt.compile (Stmt.loop upkCond (.code upkBody)) 11).length = 27 from by
    rw [Stmt.length_compile, upkLoop_len]] at h3
  exact h3

theorem upk_at_body : At (programOfStatement upkStmt) 13 upkBody := by
  have h := (at_loop upk_at_loop).2.2.1
  rw [show (11 : ℕ) + upkCond.code.length + 1 = 13 from by simp [upkCond, Cond.code]] at h
  simpa [Stmt.compile] using h

theorem upk_at_jmp : (programOfStatement upkStmt)[26]? = some (iJmp 11) := by
  have h := (at_loop upk_at_loop).2.2.2
  rw [show (11 : ℕ) + upkCond.code.length + 1 + (Stmt.code upkBody).len = 26 from by
    simp [upkCond, Cond.code, Stmt.len, upkBody]] at h
  exact h

theorem upk_halt_at : (programOfStatement upkStmt)[upkStmt.len]? = some iHalt := by
  have hlen : (Stmt.compile upkStmt 0).length = upkStmt.len := Stmt.length_compile _ _
  have h : programOfStatement upkStmt = Stmt.compile upkStmt 0 ++ [iHalt] := rfl
  rw [h, List.getElem?_append_right (by rw [hlen])]
  rw [show upkStmt.len - (Stmt.compile upkStmt 0).length = 0 by rw [hlen]; exact Nat.sub_self _]
  rfl

theorem upkStmt_len_eq : upkStmt.len = 31 := upkStmt_len

theorem upkStmt_noJumpB : sNoJumpB upkStmt = true := by decide

theorem upkStmt_haltFreeB : sHaltFreeB upkStmt = true := by decide

/-! ## 0b. The loop rule -/

/-- The loop rule (the published Sem.loop, restated here because the two bundles that carry it
cannot be imported together). -/
theorem sem_loop (P : Program) (E : RAMEnv) (a : ℕ) (c : Cond) (b : Stmt)
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

/-! ## 1. Projections of the loop head -/

theorem upkSt_r0 (W a : ℕ) (s : RAMState) (xbase m ab bb bl ob j : ℕ) :
    (upkSt W a s xbase m ab bb bl ob j).regs r0 = j := by simp [upkSt]

theorem upkSt_r1 (W a : ℕ) (s : RAMState) (xbase m ab bb bl ob j : ℕ) :
    (upkSt W a s xbase m ab bb bl ob j).regs r1 = (upkList W xbase s.mem j).length := by
  simp [upkSt]

theorem upkSt_r4 (W a : ℕ) (s : RAMState) (xbase m ab bb bl ob j : ℕ) :
    (upkSt W a s xbase m ab bb bl ob j).regs r4 = ab := by simp [upkSt]

theorem upkSt_r5 (W a : ℕ) (s : RAMState) (xbase m ab bb bl ob j : ℕ) :
    (upkSt W a s xbase m ab bb bl ob j).regs r5 = W * m := by simp [upkSt]

theorem upkSt_r12 (W a : ℕ) (s : RAMState) (xbase m ab bb bl ob j : ℕ) :
    (upkSt W a s xbase m ab bb bl ob j).regs r12 = bb := by simp [upkSt]

theorem upkSt_r13 (W a : ℕ) (s : RAMState) (xbase m ab bb bl ob j : ℕ) :
    (upkSt W a s xbase m ab bb bl ob j).regs r13 = bl := by simp [upkSt]

theorem upkSt_r14 (W a : ℕ) (s : RAMState) (xbase m ab bb bl ob j : ℕ) :
    (upkSt W a s xbase m ab bb bl ob j).regs r14 = ob := by simp [upkSt]

theorem upkSt_mem (W a : ℕ) (s : RAMState) (xbase m ab bb bl ob j : ℕ) :
    (upkSt W a s xbase m ab bb bl ob j).mem = upkMem W xbase s.mem ab j := rfl

theorem upkSt_withPc (W a : ℕ) (s : RAMState) (xbase m ab bb bl ob j : ℕ) :
    { upkSt W a s xbase m ab bb bl ob j with pc := a } = upkSt W a s xbase m ab bb bl ob j := by
  simp [upkSt]

/-- The loop test at the exit state: `r15` becomes `0`, nothing else moves. -/
theorem upkHead_exit_regs (E : RAMEnv) (A : ℕ) (s : RAMState) (xbase m ab bb bl ob : ℕ)
    (d : Fin 16) (hd : d ≠ r15) :
    (runBlock upkCond.code E (upkSt E.W A s xbase m ab bb bl ob (E.W * m))).regs d
      = (upkSt E.W A s xbase m ab bb bl ob (E.W * m)).regs d := by
  simp only [upkCond, Cond.code, runBlock_cons, runBlock_nil, execInstr]
  exact Function.update_of_ne hd _ _

theorem upkHead_exit_mem (E : RAMEnv) (A : ℕ) (s : RAMState) (xbase m ab bb bl ob : ℕ) :
    (runBlock upkCond.code E (upkSt E.W A s xbase m ab bb bl ob (E.W * m))).mem
      = (upkSt E.W A s xbase m ab bb bl ob (E.W * m)).mem := by
  simp [upkCond, Cond.code, runBlock_cons, runBlock_nil, execInstr]

/-! ## 1b. The scan's bit and list, with only `0 < W` -/

/-- `upkBit_eq_decide` with `0 < W` instead of `1 < W` (the published version asks for the stronger
hypothesis; only positivity is used). -/
theorem upkBit_eq_decide' {W m xbase : ℕ} (hW : 0 < W) {y : Fin (W * m) → ZMod 2}
    {s : RAMState} (hpad : C8R.HoldsVecPad W m xbase s y) {p : ℕ} (hp : p < W * m) :
    upkBit W xbase s.mem p
      = if decide (∃ i : Fin (W * m), i.val = p ∧ y i = 1) then 1 else 0 := by
  have hpw : p / W < m := by
    rw [Nat.div_lt_iff_lt_mul hW]; rwa [Nat.mul_comm]
  have hmemp : s.mem (xbase + p / W) = packMem W y (p / W) := by
    have hm := hpad
    unfold C8R.HoldsVecPad at hm
    rw [C8R.asm_words_eq_padded W m hW] at hm
    exact hm (p / W) hpw
  show s.mem (xbase + p / W) / 2 ^ (p % W) % 2 = _
  rw [hmemp, div_two_pow_mod_two_eq_testBit]
  rw [C8R.RP.testBit_packMem W hW y (p / W) (p % W) (Nat.mod_lt p hW)]
  rw [show p / W * W + p % W = p from by rw [Nat.mul_comm]; exact Nat.div_add_mod p W]

theorem upkList_eq_packedSupp' {W m xbase : ℕ} (hW : 0 < W) {y : Fin (W * m) → ZMod 2}
    {s : RAMState} (hpad : C8R.HoldsVecPad W m xbase s y) :
    upkList W xbase s.mem (W * m) = packedSupp W m y := by
  unfold upkList packedSupp
  refine List.filter_congr ?_
  intro p hp
  have hp' : p < W * m := List.mem_range.mp hp
  rw [upkBit_eq_decide' hW hpad hp']
  by_cases h : ∃ i : Fin (W * m), i.val = p ∧ y i = 1
  · simp [h]
  · simp [h]

theorem sum_range_const16 (n : ℕ) :
    (∑ j ∈ Finset.range n, (1 + 1 + 14 : ℕ)) = 16 * n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-! ## 2. The list the scan writes is the packed support -/

theorem upk_mList (E : RAMEnv) (xbase m ab : ℕ) (y : Fin (E.W * m) → ZMod 2) (s : RAMState)
    (hW : 0 < E.W) (hpad : C8R.HoldsVecPad E.W m xbase s y) :
    RMR.mList (upkMem E.W xbase s.mem ab (E.W * m)) ab (packedSupp E.W m y).length
      = packedSupp E.W m y := by
  have hlist : upkList E.W xbase s.mem (E.W * m) = packedSupp E.W m y :=
    upkList_eq_packedSupp' hW hpad
  rw [← hlist, RMR.mList]
  rw [show (List.range (upkList E.W xbase s.mem (E.W * m)).length).map
        (fun i => upkMem E.W xbase s.mem ab (E.W * m) (ab + i))
      = (List.range (upkList E.W xbase s.mem (E.W * m)).length).map
        (fun i => (upkList E.W xbase s.mem (E.W * m)).getD i 0) from by
    refine List.map_congr_left (fun i hi => ?_)
    exact upkMem_read E.W xbase s.mem ab (E.W * m) i (List.mem_range.mp hi)]
  exact map_getD_range_self _

/-! ## 3. The epilogue's exit state -/

/-- The state the unpack block leaves: the epilogue's four stores applied to the loop's exit state. -/
def upkEpi (E : RAMEnv) (xbase m ab bb bl ob : ℕ) (s : RAMState) : RAMState :=
  let s0 := runBlock upkCond.code E (upkSt E.W 11 s xbase m ab bb bl ob (E.W * m))
  ⟨31,
    (fun d => if d = r0 then s0.regs r12 else if d = r1 then s0.regs r13
      else if d = r10 then s0.regs r4 else if d = r11 then s0.regs 1 else s0.regs d),
    s0.mem⟩

theorem upkEpi_pc (E : RAMEnv) (xbase m ab bb bl ob : ℕ) (s : RAMState) :
    (upkEpi E xbase m ab bb bl ob s).pc = 31 := rfl

theorem upkEpi_mem (E : RAMEnv) (xbase m ab bb bl ob : ℕ) (s : RAMState) :
    (upkEpi E xbase m ab bb bl ob s).mem
      = (runBlock upkCond.code E (upkSt E.W 11 s xbase m ab bb bl ob (E.W * m))).mem := rfl

/-! ## 4. The base-0 run of the unpack statement -/

/-- **One scan iteration**, as the `Sem` rule `Sem.loop`'s per-iteration hypothesis asks for: from
the loop head at `11` (test passed, `jz` fallen through) the body runs from `13` back to the loop head
at `11`, in `14` steps, and advances the loop head from `j` to `j+1`. -/
theorem upk_body_step (E : RAMEnv) (s : RAMState) (xbase m ab bb bl ob j : ℕ)
    (hW : 1 < 2 ^ E.W) (hj : j < E.W * m) (hWm : E.W * m < 2 ^ E.W)
    (hdisj : xbase + m ≤ ab) (hab : ab + E.W * m + 1 < 2 ^ E.W)
    (hword : s.mem (xbase + j / E.W) < 2 ^ E.W) :
    Sem (programOfStatement upkStmt) E 13 11
      { runBlock upkCond.code E (upkSt E.W 11 s xbase m ab bb bl ob j) with pc := 13 }
      (fun k s' => k = 14 ∧ s' = upkSt E.W 11 s xbase m ab bb bl ob (j + 1)) := by
  have hstart : ({ runBlock upkCond.code E (upkSt E.W 11 s xbase m ab bb bl ob j)
      with pc := 13 } : RAMState)
      = { upkSt E.W 11 s xbase m ab bb bl ob j with pc := 13 } := by
    have h := upkHead_eq E 11 j s xbase m ab bb bl ob hW hj
    rwa [show (11 : ℕ) + 2 = 13 from rfl] at h
  simp only []
  rw [hstart]
  have hbody := upkBody_run E 11 13 s xbase m ab bb bl ob j hW hj hWm hdisj hab hword
  have hblk := Sem.block (programOfStatement upkStmt) E 13 upkBody
    { upkSt E.W 11 s xbase m ab bb bl ob j with pc := 13 } upk_at_body upkBody_noBranch rfl
  rw [show (13 : ℕ) + upkBody.length = 26 from by rw [upkBody_length]] at hblk
  rw [hbody] at hblk
  refine Sem.jmp_append (c := 11) upk_at_jmp (Sem.mono hblk (fun k s' h => ?_))
  obtain ⟨hk, hs'⟩ := h
  rw [upkBody_length] at hk
  refine ⟨by omega, ?_⟩
  rw [hs']
  simp [upkSt]

theorem upk_halts (E : RAMEnv) (xbase m ab bb bl ob : ℕ) (y : Fin (E.W * m) → ZMod 2)
    (s : RAMState) (hIn : UpkIn E xbase m ab bb bl ob y s) (hpc0 : s.pc = 0)
    (hW : 1 < 2 ^ E.W) (hWm : E.W * m < 2 ^ E.W) (hdisj : xbase + m ≤ ab)
    (hab : ab + E.W * m + 1 < 2 ^ E.W) (hbb : bb < 2 ^ E.W) (hbl : bl < 2 ^ E.W)
    (hob : ob < 2 ^ E.W) :
    ∃ s' : RAMState,
      HaltsWithin (programOfStatement upkStmt) E ((16 * (E.W * m) + 17 : ℕ) : ℝ) s s' ∧
        UpkOut E.W m xbase ab bb bl ob y s' := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, hpad⟩ := hIn
  have hWpos : 0 < E.W := by
    rcases Nat.eq_zero_or_pos E.W with h | h
    · rw [h] at hW; simp at hW
    · exact h
  have hwords : wordsOf E.W (E.W * m) = m := C8R.asm_words_eq_padded E.W m hWpos
  -- (1) the prologue
  have hpre : Sem (programOfStatement upkStmt) E 0 11 s
      (fun k s' => k = 11 ∧
        s' = { upkSt E.W 11 s xbase m ab bb bl ob 0 with pc := 11 }) := by
    have hb := Sem.block (programOfStatement upkStmt) E 0 upkPre s upk_at_pre
      upkPre_noBranch hpc0
    rw [show (0 : ℕ) + upkPre.length = 11 from by rw [upkPre_length]] at hb
    refine Sem.mono hb (fun k s' h => ?_)
    obtain ⟨hk, rfl⟩ := h
    rw [upkPre_length] at hk
    have hs : ({ s with pc := 0 } : RAMState) = s := by
      simpa [withPc] using withPc_congr hpc0
    refine ⟨hk, ?_⟩
    conv_lhs => rw [← hs]
    rw [upkPre_run E 0 s xbase m ab bb bl ob h0 h1 h2 h3 h4 h5 h6 hW hWm hbb hbl hob]
  -- (2) the scan loop
  have hloop : Sem (programOfStatement upkStmt) E 11 27
      (upkSt E.W 11 s xbase m ab bb bl ob 0)
      (fun k s' => k ≤ 2 + 16 * (E.W * m) ∧
        s' = { runBlock upkCond.code E (upkSt E.W 11 s xbase m ab bb bl ob (E.W * m))
                with pc := 27 }) := by
    have hl := sem_loop (programOfStatement upkStmt) E 11 upkCond (.code upkBody)
      upk_at_loop hW (E.W * m) (fun j => upkSt E.W 11 s xbase m ab bb bl ob j)
      (fun _ => 14) (fun j => rfl)
      (fun j hj => by
        show (upkSt E.W 11 s xbase m ab bb bl ob j).regs r0
            < (upkSt E.W 11 s xbase m ab bb bl ob j).regs r5
        rw [upkSt_r0, upkSt_r5]
        exact hj)
      (fun hcontra => by
        have h' : (upkSt E.W 11 s xbase m ab bb bl ob (E.W * m)).regs r0
            < (upkSt E.W 11 s xbase m ab bb bl ob (E.W * m)).regs r5 := hcontra
        rw [upkSt_r0, upkSt_r5] at h'
        omega)
      (fun j hj => by
        have hjw : j / E.W < m := by
          rw [Nat.div_lt_iff_lt_mul hWpos, Nat.mul_comm]
          exact hj
        have hword : s.mem (xbase + j / E.W) < 2 ^ E.W := by
          rw [hpad _ (by rw [hwords]; exact hjw)]
          exact C8R.RP.packMem_lt E.W hWpos y (j / E.W)
        simpa [upkCond, Cond.code] using
          upk_body_step E s xbase m ab bb bl ob j hW hj hWm hdisj hab hword)
    rw [show (11 : ℕ) + upkCond.code.length + (Stmt.code upkBody).len + 2 = 27 from by
      simp [upkCond, Cond.code, Stmt.len, upkBody]] at hl
    refine Sem.mono hl (fun k s' h => ⟨?_, h.2⟩)
    have hk := h.1
    rw [show upkCond.code.length = 1 from rfl] at hk
    have hsum : (1 : ℕ) + 1 + ∑ j ∈ Finset.range (E.W * m), (1 + 1 + 14)
        = 2 + 16 * (E.W * m) := by
      rw [sum_range_const16]
    rw [hsum] at hk
    exact hk
  -- (3) the epilogue
  have hleg : Sem (programOfStatement upkStmt) E 27 31
      { runBlock upkCond.code E (upkSt E.W 11 s xbase m ab bb bl ob (E.W * m)) with pc := 27 }
      (fun k s' => k = 4 ∧ s' = upkEpi E xbase m ab bb bl ob s) := by
    have hb := Sem.block (programOfStatement upkStmt) E 27 upkEpilogue
      { runBlock upkCond.code E (upkSt E.W 11 s xbase m ab bb bl ob (E.W * m)) with pc := 27 }
      upk_at_epi upkEpilogue_noBranch rfl
    rw [show (27 : ℕ) + upkEpilogue.length = 31 from by rw [upkEpilogue_length]] at hb
    have hr1 : (runBlock upkCond.code E
        (upkSt E.W 11 s xbase m ab bb bl ob (E.W * m))).regs 1 < 2 ^ E.W := by
      rw [upkHead_exit_regs E 11 s xbase m ab bb bl ob r1 (by decide), upkSt_r1]
      exact lt_of_le_of_lt (upkList_length_le E.W xbase s.mem (E.W * m)) (by omega)
    have hr4 : (runBlock upkCond.code E
        (upkSt E.W 11 s xbase m ab bb bl ob (E.W * m))).regs 4 < 2 ^ E.W := by
      rw [upkHead_exit_regs E 11 s xbase m ab bb bl ob r4 (by decide), upkSt_r4]
      exact lt_of_le_of_lt (Nat.le_add_right ab (E.W * m)) (by omega)
    have hr12 : (runBlock upkCond.code E
        (upkSt E.W 11 s xbase m ab bb bl ob (E.W * m))).regs r12 < 2 ^ E.W := by
      rw [upkHead_exit_regs E 11 s xbase m ab bb bl ob r12 (by decide), upkSt_r12]
      exact hbb
    have hr13 : (runBlock upkCond.code E
        (upkSt E.W 11 s xbase m ab bb bl ob (E.W * m))).regs r13 < 2 ^ E.W := by
      rw [upkHead_exit_regs E 11 s xbase m ab bb bl ob r13 (by decide), upkSt_r13]
      exact hbl
    rw [upkEpilogue_run E 27 _ hr1 hr4 hr12 hr13] at hb
    exact hb
  -- (4) glue
  obtain ⟨-, k1, s1, hstep1, hpc1, hk1, hs1⟩ := hpre
  have hloop' : Sem (programOfStatement upkStmt) E 11 27 s1
      (fun k s' => k ≤ 2 + 16 * (E.W * m) ∧
        s' = { runBlock upkCond.code E (upkSt E.W 11 s xbase m ab bb bl ob (E.W * m))
                with pc := 27 }) := by
    rw [hs1, upkSt_withPc]
    exact hloop
  obtain ⟨-, k2, s2, hstep2, hpc2, hk2, hs2⟩ := hloop'
  have hleg' : Sem (programOfStatement upkStmt) E 27 31 s2
      (fun k s' => k = 4 ∧ s' = upkEpi E xbase m ab bb bl ob s) := by
    rw [hs2]
    exact hleg
  obtain ⟨-, k3, s3, hstep3, hpc3, hk3, hs3⟩ := hleg'
  refine ⟨s3, ⟨k1 + k2 + k3, ?_, ?_, ?_⟩, ?_⟩
  · have h1' : (k1 : ℝ) = 11 := by exact_mod_cast hk1
    have h2' : (k2 : ℝ) ≤ 2 + 16 * ((E.W * m : ℕ) : ℝ) := by exact_mod_cast hk2
    have h3' : (k3 : ℝ) = 4 := by exact_mod_cast hk3
    have hcast : ((k1 + k2 + k3 : ℕ) : ℝ) = (k1 : ℝ) + (k2 : ℝ) + (k3 : ℝ) := by
      push_cast
      ring
    have hrhs : ((16 * (E.W * m) + 17 : ℕ) : ℝ) = 16 * ((E.W * m : ℕ) : ℝ) + 17 := by
      push_cast
      ring
    rw [hcast, hrhs]
    linarith
  · have e : k1 + k2 + k3 = k3 + (k2 + k1) := by omega
    rw [e, Function.iterate_add_apply, Function.iterate_add_apply, hstep1, hstep2, hstep3]
  · rw [hs3]
    have hpc : (upkEpi E xbase m ab bb bl ob s).pc = upkStmt.len := by
      rw [upkEpi_pc, upkStmt_len]
    simp only [Halted, hpc, upk_halt_at]
  · rw [hs3]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [upkEpi, upkHead_exit_regs E 11 s xbase m ab bb bl ob r12 (by decide), upkSt_r12]
    · simp [upkEpi, upkHead_exit_regs E 11 s xbase m ab bb bl ob r13 (by decide), upkSt_r13]
    · simp [upkEpi, upkHead_exit_regs E 11 s xbase m ab bb bl ob r4 (by decide), upkSt_r4]
    · simp [upkEpi, upkHead_exit_regs E 11 s xbase m ab bb bl ob r1 (by decide), upkSt_r1,
        upkList_eq_packedSupp' hWpos hpad]
    · simp [upkEpi, upkHead_exit_regs E 11 s xbase m ab bb bl ob r12 (by decide), upkSt_r12]
    · simp [upkEpi, upkHead_exit_regs E 11 s xbase m ab bb bl ob r13 (by decide), upkSt_r13]
    · simp [upkEpi, upkHead_exit_regs E 11 s xbase m ab bb bl ob r14 (by decide), upkSt_r14]
    · intro j hj
      have hj' : j < m := by rwa [hwords] at hj
      have hmem : (upkEpi E xbase m ab bb bl ob s).mem
          = upkMem E.W xbase s.mem ab (E.W * m) := by
        rw [upkEpi_mem, upkHead_exit_mem]
        exact upkSt_mem E.W 11 s xbase m ab bb bl ob (E.W * m)
      rw [hmem, upkMem_frame E.W xbase s.mem ab (E.W * m) (xbase + j) (Or.inl (by omega))]
      exact hpad j (by rw [hwords]; exact hj')
    · rw [upkEpi_mem, upkHead_exit_mem, upkSt_mem]
      exact upk_mList E xbase m ab y s hWpos hpad

/-! ## 5. The relocated `StageRun` -/

/-- **The unpack block is a `StageRun`.**  From any state satisfying `UpkIn` at `base`, the compiled
block reaches `base + 31` within `16·m·W + 17` steps and leaves `UpkOut`: the packed estimate is now
the coordinate list `packedSupp W m y` at `[ab, ab + #list)`, the merge's five arguments sit in
`r10 … r14`, and 2.3's output window `(r0, r1) = (bb, bl)` is restored. -/
theorem stageRun_unpack {G : Program} {E : RAMEnv} {base xbase m ab bb bl ob : ℕ}
    {y : Fin (E.W * m) → ZMod 2}
    (hAt : At G base (upkStmt.compile base)) (hW : 1 < 2 ^ E.W) (hWm : E.W * m < 2 ^ E.W)
    (hdisj : xbase + m ≤ ab) (hab : ab + E.W * m + 1 < 2 ^ E.W) (hbb : bb < 2 ^ E.W)
    (hbl : bl < 2 ^ E.W) (hob : ob < 2 ^ E.W) :
    StageRun G E base (base + upkStmt.len) ((16 * (E.W * m) + 17 : ℕ) : ℝ)
      (UpkIn E xbase m ab bb bl ob y) (UpkOut E.W m xbase ab bb bl ob y) :=
  stageRun_of_haltsWithin_shift (S := upkStmt) hAt upkStmt_noJumpB upkStmt_haltFreeB
    (fun s hpc hIn => upk_halts E xbase m ab bb bl ob y s hIn hpc hW hWm hdisj hab hbb hbl hob)

/-! ## 6. Non-vacuity: the entry predicate is inhabited -/

/-- The unpack block's entry state at the witness `W = 8`, `m = 1`, `xbase = 0`, `ab = 10`,
`(bb, bl) = (20, 1)`, `ob = 40`. -/
def upkW : RAMState where
  pc := 0
  regs := fun d =>
    if d = r0 then 20 else if d = r1 then 1 else if d = r2 then 0 else if d = r3 then 8
      else if d = r4 then 10 else if d = r5 then 40 else if d = r6 then 1 else 0
  mem := fun _ => 0

/-- **`UpkIn` is inhabited** at a non-degenerate `m = 1`, so `stageRun_unpack` is not a vacuously
true contract. -/
theorem upkIn_witness : UpkIn RMR.mrgEnv8 0 1 10 20 1 40 (fun _ : Fin 8 => 0) upkW := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  intro j hj
  have hW8 : RMR.mrgEnv8.W = 8 := rfl
  have hw : wordsOf RMR.mrgEnv8.W (RMR.mrgEnv8.W * 1) = 1 := by
    rw [hW8]
    exact C8R.asm_words_eq_padded 8 1 (by norm_num)
  rw [hw] at hj
  have hj0 : j = 0 := by omega
  subst hj0
  have hmem : upkW.mem (0 + 0) = 0 := rfl
  rw [hmem]
  show (0 : ℕ) = packMem 8 (fun _ : Fin 8 => 0) 0
  simp [packMem]

#print axioms stageRun_unpack
#print axioms upk_halts
#print axioms upkIn_witness

end CRS
end LinearSetReconciliation327.Main


