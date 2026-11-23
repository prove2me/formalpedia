-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_DecOutFrame20261123
-- name    : LinearSetReconciliation327_Main_DecOutFrame20261123
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-23T13:15:28.867591+00:00
-- url     : https://prove2.me/theorems/c7b6df01-8474-418f-b991-e8ae0965ee37
-- title:
--   Proposition 2.3's decoder memory frame: the corrected entry-conditioned lemma at decOutBase + (2t+1), the decOutBase + N form, and a machine-checked disproof of the unconditional DecMemFrame
-- statement:
--   The `cr` stage of Theorem 6.5 needs the estimate buffer at `xbase >= decOutBase N t + N`, so the decoder must not write at or above `decOutBase N t + N`.  This bundle proves the sharp memory frame: from the entry conditions of Proposition 2.3 (`pc = 0`, `r0 = 0`, the packed payload on `[0, wordsOf)` and zeros on `[wordsOf, decZeroBound)`) the decoder `decStmt` writes nothing at or above `decEmFrame N t = decOutBase N t + (2t+1)`; since `decEmFrame <= decFrameBound = decOutBase + N` when `2t+1 <= N`, this gives the published `decFrameBound` form in that regime.  The proof is an engine copy: `DecParInv` gains the frame above `decOutBase`, `DecEmitInv` gains the frame above `decOutBase + (2t+1)`, and the par, emit, round-body, round-loop, prologue and full-decoder specs are re-run with the frame in their postconditions; `HaltsWithin` determinism (`HaltsWithin_unique`) transfers the canonical run to an arbitrary halting run.  The bundle also records, machine-checked, that the *unconditional* published `DecMemFrame` (quantifying over every start state) is FALSE: entering the program at the emit walk's output store (pc 277) with the address register set to `decFrameBound 1 1` and `r0 = r2 = 0` reaches `halt` in 7 steps after writing at `decFrameBound 1 1` (`decMemFrameAtOut_false`).  The missing hypotheses are exactly the entry conditions `pc = 0`, `r0 = 0` (and the payload/zero window), which `CrStageInWz` supplies.  Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Proposition 2.3 / Theorem 6.5; the project's published `CR23DecRun20261122`, `CR23DecExit20261122`, `CR23DecExitWz20261123`, `CrSlot20261123` and `DecOutBase20261123` bundles.  Copy spans are the decoder engine, changed only by the frame conjuncts and their plumbing.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_DecOutBase20261123

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped ENNReal
open Finset

noncomputable section

namespace LinearSetReconciliation327.Main
-- ===== DecOutFrame.lean =====


/-! ## Frame-carrying parity pass (body (d)) -/

/-- **`DecParInvF`** — the loop-head invariant of body (d) at step `j`: the parity bitmap holds the
set `S j` (the round's initial parity set toggled by the first `j` candidate values), the candidate
list is intact, and the master list has received `l[0..j)`. -/
def DecParInvF (N t : ℕ) (S : ℕ → Finset ℕ) (l mst : List ℕ) (mstLen j : ℕ) (mb : ℕ → ℕ)
    (st : RAMState) : Prop :=
  st.regs r0 = j ∧
  st.regs r1 = l.length ∧
  st.regs r4 = 1 ∧
  st.regs r5 = decCandBase N t ∧
  st.regs r6 = decParBase N t ∧
  st.regs r7 = decMstBase N t + mstLen + j ∧
  (∀ i, i < l.length → st.mem (decCandBase N t + i) = l.getD i 0) ∧
  (∀ v, v < 2 ^ (cr23Lb N + 1) →
      st.mem (decParBase N t + v) = if v ∈ S j then 1 else 0) ∧
  (∀ a, a < decMstBase N t → st.mem a = mb a) ∧
  (∀ i, i < mstLen → st.mem (decMstBase N t + i) = mst.getD i 0) ∧
  (∀ k, k < j → st.mem (decMstBase N t + mstLen + k) = l.getD k 0) ∧
  (∀ a, decOutBase N t ≤ a → st.mem a = mb a)
/-- `DecParInvF` never looks at the program counter. -/
theorem DecParInvF_pc (N t : ℕ) (S : ℕ → Finset ℕ) (l mst : List ℕ) (mstLen j : ℕ)
    (mb : ℕ → ℕ) (p : ℕ) (st : RAMState) (h : DecParInvF N t S l mst mstLen j mb st) :
    DecParInvF N t S l mst mstLen j mb { st with pc := p } := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩
/-- **The initialisation establishes the invariant at `j = 0`**: the four frame slots are read out
of the round-head memory `mb`, which is what `DecData` provides. -/
theorem decParInit_dataF (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (E : RAMEnv) (hEW : E.W = cr23Word N)
    (S : ℕ → Finset ℕ) (l mst : List ℕ) (mstLen : ℕ) (mb : ℕ → ℕ) (st : RAMState)
    (h14 : st.regs r14 = cr23DecFrame N t) (h2 : st.regs r2 = l.length)
    (hcand : ∀ i, i < l.length → mb (decCandBase N t + i) = l.getD i 0)
    (hbelow : ∀ b, b < decMstBase N t → st.mem b = mb b)
    (hsl9 : mb (decSlot N t 9) = decCandBase N t)
    (hsl11 : mb (decSlot N t 11) = decMstBase N t)
    (hsl12 : mb (decSlot N t 12) = decParBase N t)
    (hsl14 : mb (decSlot N t 14) = mstLen)
    (hmst : ∀ i, i < mstLen → st.mem (decMstBase N t + i) = mst.getD i 0)
    (hcap : mstLen + l.length ≤ 2 * t + 1)
    (hpar0 : ∀ v, v < 2 ^ (cr23Lb N + 1) →
      st.mem (decParBase N t + v) = if v ∈ S 0 then 1 else 0)
    (hframe : ∀ a, decOutBase N t ≤ a → st.mem a = mb a) :
    DecParInvF N t S l mst mstLen 0 mb (runBlock decParInit E st) := by
  have hW1 : 1 < 2 ^ E.W := by rw [hEW]; exact cr23_one_lt_word N hN
  have hbig : 1024 < 2 ^ E.W := by rw [hEW]; exact dec_1024_lt_word N
  have hW10 : 10 < 2 ^ E.W := by omega
  have hW12 : 12 < 2 ^ E.W := by omega
  have hW13 : 13 < 2 ^ E.W := by omega
  have hW15 : 15 < 2 ^ E.W := by omega
  have hW0 : 0 < 2 ^ E.W := by omega
  have hF10 : cr23DecFrame N t + 10 < 2 ^ E.W := by
    rw [hEW]; exact dec_frame_add_lt_word N t hN htN (by norm_num)
  have hF12 : cr23DecFrame N t + 12 < 2 ^ E.W := by
    rw [hEW]; exact dec_frame_add_lt_word N t hN htN (by norm_num)
  have hF13 : cr23DecFrame N t + 13 < 2 ^ E.W := by
    rw [hEW]; exact dec_frame_add_lt_word N t hN htN (by norm_num)
  have hF15 : cr23DecFrame N t + 15 < 2 ^ E.W := by
    rw [hEW]; exact dec_frame_add_lt_word N t hN htN (by norm_num)
  have hcb : decCandBase N t < 2 ^ E.W := by rw [hEW]; exact dec_candBase_lt_word N t hN htN
  have hpb : decParBase N t < 2 ^ E.W := by rw [hEW]; exact dec_parBase_lt_word N t hN htN
  have hmb : decMstBase N t < 2 ^ E.W := by rw [hEW]; exact dec_mstBase_lt_word N t hN htN
  have h2t : 2 * t + 1 < 2 ^ E.W := by rw [hEW]; exact dec_two_t_lt_word N t hN htN
  have hml : mstLen < 2 ^ E.W := by omega
  have hlenW : l.length < 2 ^ E.W := by omega
  have hsum : decMstBase N t + mstLen < 2 ^ E.W := by
    have h1 : decMstBase N t + mstLen ≤ decMstBase N t + (2 * t + 1) :=
      Nat.add_le_add_left (by omega) _
    have h2 : decMstBase N t + (2 * t + 1) = decParBase N t := by simp only [decParBase]
    omega
  have hslot : ∀ (k : ℕ) (_ : k < 15) (val : ℕ), mb (decSlot N t k) = val →
      st.mem (decSlot N t k) = val := by
    intro k hk val hv
    rw [hbelow _ (decSlot_lt_mstBase N t hk)]
    exact hv
  have hc10 : st.mem (cr23DecFrame N t + 10) = decCandBase N t := by
    have := hslot 9 (by norm_num) _ hsl9
    rwa [decSlot_nine] at this
  have hc12 : st.mem (cr23DecFrame N t + 12) = decMstBase N t := by
    have := hslot 11 (by norm_num) _ hsl11
    rwa [decSlot_eleven] at this
  have hc13 : st.mem (cr23DecFrame N t + 13) = decParBase N t := by
    have := hslot 12 (by norm_num) _ hsl12
    rwa [decSlot_twelve] at this
  have hc15 : st.mem (cr23DecFrame N t + 15) = mstLen := by
    have := hslot 14 (by norm_num) _ hsl14
    rwa [decSlot_fourteen] at this
  obtain ⟨hr0, hr1, hr4, hr5, hr6, hr7⟩ :=
    decParInit_regs E st (cr23DecFrame N t) (decCandBase N t) (decParBase N t)
      (decMstBase N t) mstLen (l.length) h14 h2 hW1 hW10 hW12 hW13 hW15 hW0 hF10 hF12 hF13 hF15
      hc10 hc12 hc13 hc15 hcb hpb hmb hml hsum hlenW
  have hmem : (runBlock decParInit E st).mem = st.mem := decParInit_mem E st
  refine ⟨hr0, hr1, hr4, hr5, hr6, hr7, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hi2 : i < 2 * t + 1 := by omega
    have hcm : decCandBase N t + i < decMstBase N t :=
      lt_of_lt_of_le (dec_cand_add_lt_tag N t hi2) (decTagBase_le_mstBase N t)
    rw [hmem, hbelow _ hcm]
    exact hcand i hi
  · intro v hv
    rw [hmem]
    exact hpar0 v hv
  · intro b hb
    rw [hmem]
    exact hbelow b hb
  · intro i hi
    rw [hmem]
    exact hmst i hi
  · intro k hk
    omega
  · intro a ha
    rw [hmem]
    exact hframe a ha
theorem decParBody_dataF (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (E : RAMEnv) (hEW : E.W = cr23Word N)
    (S : ℕ → Finset ℕ) (l mst : List ℕ) (mstLen j : ℕ) (mb : ℕ → ℕ) (st : RAMState)
    (hj : j < l.length) (hcap : mstLen + l.length ≤ 2 * t + 1)
    (hlN : ∀ i ∈ l, i < N) (hS : S (j + 1) = decSymm (S j) {l.getD j 0})
    (hI : DecParInvF N t S l mst mstLen j mb st) :
    DecParInvF N t S l mst mstLen (j + 1) mb (runBlock decParBody E st) := by
  obtain ⟨h0, h1, h4, h5, h6, h7, hcand, hpar, hbelow, hmst, hnew, hframe⟩ := hI
  set x : ℕ := l.getD j 0 with hx
  set o : ℕ := if x ∈ S j then 1 else 0 with ho
  have hW : 1 < 2 ^ E.W := by rw [hEW]; exact cr23_one_lt_word N hN
  have hxmem : x ∈ l := by rw [hx]; exact dec_getD_mem hj
  have hxN : x < N := hlN x hxmem
  have hexp : cr23Lb N + 1 ≤ cr23Word N := by
    simp only [cr23Word]
    have := cr23Lb_succ_pos N
    omega
  have hxLb : x < 2 ^ (cr23Lb N + 1) := by
    have h1 : N ≤ 2 ^ cr23Lb N := cr23_le_pow_lb N
    have h2 : 2 ^ cr23Lb N ≤ 2 ^ (cr23Lb N + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hxW : x < 2 ^ E.W := by
    rw [hEW]
    exact lt_of_lt_of_le hxLb (Nat.pow_le_pow_right (by norm_num) hexp)
  have ho1 : o ≤ 1 := by rw [ho]; split_ifs <;> omega
  have hlt2t : j < 2 * t + 1 := by omega
  have hci : decCandBase N t + j < 2 ^ E.W := by
    rw [hEW]; exact dec_cand_add_lt_word N t hN htN (by omega)
  have hpv : decParBase N t + x < 2 ^ E.W := by
    rw [hEW]; exact dec_par_add_lt_word N t hN htN hxLb
  have h2t : 2 * t + 1 < 2 ^ E.W := by rw [hEW]; exact dec_two_t_lt_word N t hN htN
  have hjW : j + 1 < 2 ^ E.W := by omega
  have hcap2 : mstLen + j < 2 * t + 1 := by omega
  have hmpPar : decMstBase N t + mstLen + j < decParBase N t :=
    dec_mst_add_lt_parBase N t hcap2
  have hmpPar' : decMstBase N t + mstLen + j < decParBase N t + x :=
    lt_of_lt_of_le hmpPar (dec_le_add_r _ _)
  have hmpLt : decMstBase N t + mstLen + j < 2 ^ E.W := by
    have h2 : decParBase N t < 2 ^ E.W := by rw [hEW]; exact dec_parBase_lt_word N t hN htN
    exact lt_trans hmpPar h2
  have hmp1 : decMstBase N t + mstLen + j + 1 < 2 ^ E.W := by omega
  have hmstLt : decMstBase N t ≤ decParBase N t := decMstBase_le_parBase N t
  have hbelow' : decMstBase N t ≤ decMstBase N t + mstLen + j := by omega
  -- every candidate lives below the master list
  have hcm : ∀ i, i < l.length → decCandBase N t + i < decMstBase N t := by
    intro i hi
    have hi2 : i < 2 * t + 1 := by omega
    exact lt_of_lt_of_le (dec_cand_add_lt_tag N t hi2) (decTagBase_le_mstBase N t)
  have hcandx : st.mem (decCandBase N t + j) = x := by
    rw [hx]; exact hcand j hj
  have hparx : st.mem (decParBase N t + x) = o := by
    rw [ho]; exact hpar x hxLb
  -- chunk A
  set st1 : RAMState := runBlock decParBA E st with hst1
  have hBA := decParBA_spec E st (decCandBase N t) (decParBase N t) j x o hW h4 h5 h0 h6 hcandx
    hci hxW hparx ho1 hpv
  have hA2 : st1.regs r2 = x := hBA.1
  have hA3 : st1.regs r3 = 1 - o := hBA.2.1
  have hA9 : st1.regs r9 = decParBase N t + x := hBA.2.2
  have hA0 : st1.regs r0 = j := by
    rw [hst1]; exact (decParBA_frame E st r0 (by decide) (by decide) (by decide)).trans h0
  have hA4 : st1.regs r4 = 1 := by
    rw [hst1]; exact (decParBA_frame E st r4 (by decide) (by decide) (by decide)).trans h4
  have hA5 : st1.regs r5 = decCandBase N t := by
    rw [hst1]; exact (decParBA_frame E st r5 (by decide) (by decide) (by decide)).trans h5
  have hA6 : st1.regs r6 = decParBase N t := by
    rw [hst1]; exact (decParBA_frame E st r6 (by decide) (by decide) (by decide)).trans h6
  have hA7 : st1.regs r7 = decMstBase N t + mstLen + j := by
    rw [hst1]; exact (decParBA_frame E st r7 (by decide) (by decide) (by decide)).trans h7
  -- chunk B
  have hBB := decParBB_spec E st1 (decParBase N t + x) (decMstBase N t + mstLen + j) x (1 - o) j
    hA9 hA3 hA7 hA2 hA4 hA0 hmp1 hjW
  have hB7 : (runBlock decParBody E st).regs r7 = decMstBase N t + mstLen + j + 1 := by
    rw [decParBody_split, runBlock_appendA, ← hst1]
    exact hBB.2.1
  have hB0 : (runBlock decParBody E st).regs r0 = j + 1 := by
    rw [decParBody_split, runBlock_appendA, ← hst1]
    exact hBB.2.2
  have hBmem : (runBlock decParBody E st).mem
      = Function.update (Function.update st.mem (decParBase N t + x) (1 - o))
          (decMstBase N t + mstLen + j) x := by
    rw [decParBody_split, runBlock_appendA, ← hst1]
    exact hBB.1
  have hrest : ∀ d : Fin 16, d ≠ r9 → d ≠ r2 → d ≠ r3 → d ≠ r7 → d ≠ r0 →
      (runBlock decParBody E st).regs d = st.regs d := by
    intro d h9 h2 h3 h7' h0'
    rw [decParBody_split, runBlock_appendA, ← hst1]
    exact (decParBB_frame E (runBlock decParBA E st) d h7' h0').trans
      (decParBA_frame E st d h9 h2 h3)
  have hAx : decParBase N t + x < decOutBase N t := by
    have h3 : decParBase N t + 2 ^ (cr23Lb N + 1) = decOutBase N t := by
      simp only [decOutBase]
    have h4 : decParBase N t + x < decParBase N t + 2 ^ (cr23Lb N + 1) :=
      Nat.add_lt_add_left hxLb _
    omega
  refine ⟨hB0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrest r1 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h1
  · rw [hrest r4 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h4
  · rw [hrest r5 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h5
  · rw [hrest r6 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h6
  · rw [hB7]; omega
  · intro i hi
    rw [hBmem, dec_upd2_lt st.mem (decParBase N t + x) (decMstBase N t + mstLen + j) (1 - o) x
      (decCandBase N t + i) hmpPar' (lt_of_lt_of_le (hcm i hi) hbelow')]
    exact hcand i hi
  · intro v hv
    rw [hS]
    by_cases hvx : v = x
    · subst hvx
      rw [hBmem, dec_upd2_fst (show decMstBase N t + mstLen + j ≠ decParBase N t + x from by omega),
        ho, dec_toggle]
    · have hiff : (v ∈ decSymm (S j) {x}) ↔ v ∈ S j := decSymm_singleton_ne (S j) hvx
      rw [hBmem, dec_upd2_ne
        (show decParBase N t + v ≠ decParBase N t + x from fun h => hvx (by omega))
        (show decParBase N t + v ≠ decMstBase N t + mstLen + j from by omega), hpar v hv]
      by_cases hm : v ∈ S j
      · rw [if_pos hm, if_pos (hiff.mpr hm)]
      · rw [if_neg hm, if_neg (fun hh => hm (hiff.mp hh))]
  · intro a ha
    rw [hBmem, dec_upd2_lt st.mem (decParBase N t + x) (decMstBase N t + mstLen + j) (1 - o) x a
      hmpPar' (lt_of_lt_of_le ha hbelow')]
    exact hbelow a ha
  · intro i hi
    have h1 : decMstBase N t + i < decMstBase N t + mstLen := Nat.add_lt_add_left hi _
    have h2 : decMstBase N t + mstLen ≤ decMstBase N t + mstLen + j := dec_le_add_r _ _
    rw [hBmem, dec_upd2_lt st.mem (decParBase N t + x) (decMstBase N t + mstLen + j) (1 - o) x
      (decMstBase N t + i) hmpPar' (lt_of_lt_of_le h1 h2)]
    exact hmst i hi
  · intro k hk
    by_cases hk' : k = j
    · subst hk'
      rw [hBmem, dec_upd2_snd, ← hx]
    · have h1 : decMstBase N t + mstLen + k < decMstBase N t + mstLen + j :=
        Nat.add_lt_add_left (by omega) _
      rw [hBmem, dec_upd2_lt st.mem (decParBase N t + x) (decMstBase N t + mstLen + j) (1 - o) x
        (decMstBase N t + mstLen + k) hmpPar' h1]
      exact hnew k (by omega)
  · intro a ha
    rw [hBmem, dec_upd2_ne
      (dec_ne_of_lt' (lt_of_lt_of_le hAx ha))
      (dec_ne_of_lt' (lt_of_lt_of_le (lt_of_lt_of_le hmpPar (decParBase_le_outBase N t)) ha))]
    exact hframe a ha
/-- **One iteration of the parity pass, with the frame register.**  `decPar_bodyIter` plus the
observation that the body's block leaves `r14` alone. -/
theorem decPar_bodyIter_r14F (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (E : RAMEnv) (hEW : E.W = cr23Word N)
    (S : ℕ → Finset ℕ) (l mst : List ℕ) (mstLen j : ℕ) (mb : ℕ → ℕ)
    (Pgm : Program) (a : ℕ)
    (hAtBody : At Pgm (a + (Cond.lt r13 r0 r1).code.length + 1) decParBody)
    (hjmpAt : Pgm[(a + (Cond.lt r13 r0 r1).code.length + 1) + decParBody.length]? =
      some (iJmp a))
    (hcap : mstLen + l.length ≤ 2 * t + 1) (hlN : ∀ i ∈ l, i < N)
    (hS : S (j + 1) = decSymm (S j) {l.getD j 0})
    (st : RAMState) (hpc : st.pc = a + (Cond.lt r13 r0 r1).code.length + 1)
    (hR : DecParInvF N t S l mst mstLen j mb st) (hj : j < l.length) :
    Sem Pgm E (a + (Cond.lt r13 r0 r1).code.length + 1) a
      { st with pc := a + (Cond.lt r13 r0 r1).code.length + 1 }
      (fun k s' => k = decParBody.length + 1 ∧
        DecParInvF N t S l mst mstLen (j + 1) mb s' ∧ s'.pc = a ∧
        s'.regs r14 = st.regs r14) := by
  set b : ℕ := a + (Cond.lt r13 r0 r1).code.length + 1 with hb
  have hblk : Sem Pgm E b (b + decParBody.length) { st with pc := b }
      (fun k s' => k = decParBody.length ∧ s' = runBlock decParBody E { st with pc := b }) :=
    Sem.blockA Pgm E b decParBody { st with pc := b } hAtBody decParBody_noBranch rfl
  have hpcB : (runBlock decParBody E { st with pc := b }).pc = b + decParBody.length := by
    rw [runBlock_pcA decParBody E _ decParBody_noBranch]
  have hjmpSem : Sem Pgm E (b + decParBody.length) a
      (runBlock decParBody E { st with pc := b })
      (fun k s' => k = 1 ∧ s' = { runBlock decParBody E { st with pc := b } with pc := a }) :=
    Sem.execA Pgm E (b + decParBody.length) a _ (iJmp a) hjmpAt hpcB rfl
  refine Sem.monoA (Sem.transA hblk hjmpSem) ?_
  intro k s' hk
  obtain ⟨rfl, rfl⟩ := hk
  have hfr : (runBlock decParBody E { st with pc := b }).regs r14 = st.regs r14 := by
    simpa using decParBody_frame14 E { st with pc := b }
  exact ⟨rfl, DecParInvF_pc N t S l mst mstLen (j + 1) mb a _
    (decParBody_dataF N t hN htN E hEW S l mst mstLen j mb { st with pc := b } hj hcap hlN hS
      hR), rfl, hfr⟩
/-- **The parity loop, with the frame register.**  `DecParInvF ∧ r14 = F` is the loop invariant. -/
theorem decPar_loop_r14F (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (E : RAMEnv) (hEW : E.W = cr23Word N)
    (S : ℕ → Finset ℕ) (l mst : List ℕ) (mstLen : ℕ) (mb : ℕ → ℕ)
    (Pgm : Program) (a : ℕ) (F : ℕ)
    (hAt : At Pgm a (Stmt.compile (Stmt.loop (Cond.lt r13 r0 r1) (Stmt.code decParBody)) a))
    (hcap : mstLen + l.length ≤ 2 * t + 1) (hlN : ∀ i ∈ l, i < N)
    (hS : ∀ j, j < l.length → S (j + 1) = decSymm (S j) {l.getD j 0})
    (st : RAMState) (hpc : st.pc = a) (hF : st.regs r14 = F)
    (hR : DecParInvF N t S l mst mstLen 0 mb st) :
    Sem Pgm E a (a + (Cond.lt r13 r0 r1).code.length + (Stmt.code decParBody).len + 2) st
      (fun k s' => k ≤ 2 + 12 * l.length ∧
        DecParInvF N t S l mst mstLen l.length mb s' ∧
        s'.pc = a + (Cond.lt r13 r0 r1).code.length + (Stmt.code decParBody).len + 2 ∧
        s'.regs r14 = F) := by
  have hW : 1 < 2 ^ E.W := by rw [hEW]; exact cr23_one_lt_word N hN
  have hirr : ∀ (j : ℕ) (s s' : RAMState), (∀ d : Fin 16, d ≠ r13 → s.regs d = s'.regs d) →
      s.mem = s'.mem → (DecParInvF N t S l mst mstLen j mb s ∧ s.regs r14 = F) →
        (DecParInvF N t S l mst mstLen j mb s' ∧ s'.regs r14 = F) := by
    intro j s s' hd hm' h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h1
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [← hd r0 (by decide)]; exact a1
    · rw [← hd r1 (by decide)]; exact a2
    · rw [← hd r4 (by decide)]; exact a3
    · rw [← hd r5 (by decide)]; exact a4
    · rw [← hd r6 (by decide)]; exact a5
    · rw [← hd r7 (by decide)]; exact a6
    · intro i hi; rw [← hm']; exact a7 i hi
    · intro v hv; rw [← hm']; exact a8 v hv
    · intro b hb; rw [← hm']; exact a9 b hb
    · intro i hi; rw [← hm']; exact a10 i hi
    · intro k hk; rw [← hm']; exact a11 k hk
    · intro a ha; rw [← hm']; exact a12 a ha
    · rw [← hd r14 (by decide)]; exact h2
  have hgo : ∀ j, j < l.length → ∀ s, (DecParInvF N t S l mst mstLen j mb s ∧ s.regs r14 = F) →
      (Cond.lt r13 r0 r1).eval s := by
    intro j hj s h
    obtain ⟨h1, -⟩ := h
    obtain ⟨h0, h1', -⟩ := h1
    show s.regs r0 < s.regs r1
    rw [h0, h1']; exact hj
  have hstop : ∀ s, (DecParInvF N t S l mst mstLen l.length mb s ∧ s.regs r14 = F) →
      ¬ (Cond.lt r13 r0 r1).eval s := by
    intro s h
    obtain ⟨h1, -⟩ := h
    obtain ⟨h0, h1', -⟩ := h1
    show ¬ (s.regs r0 < s.regs r1)
    rw [h0, h1']; omega
  have hstep : ∀ j, j < l.length → ∀ s, s.pc = a →
      (DecParInvF N t S l mst mstLen j mb s ∧ s.regs r14 = F) →
      Sem Pgm E (a + (Cond.lt r13 r0 r1).code.length + 1) a
        { runBlock (Cond.lt r13 r0 r1).code E s with
          pc := a + (Cond.lt r13 r0 r1).code.length + 1 }
        (fun k s' => k ≤ decParBody.length + 1 ∧
          (DecParInvF N t S l mst mstLen (j + 1) mb s' ∧ s'.regs r14 = F) ∧ s'.pc = a) := by
    intro j hj s hpc' hRs
    obtain ⟨hRj, hFrj⟩ := hRs
    obtain ⟨-, hjz, hbody, hjmp⟩ := at_loopA hAt
    have hlen : (Stmt.code decParBody).len = decParBody.length := rfl
    have hbody' : At Pgm (a + (Cond.lt r13 r0 r1).code.length + 1) decParBody := hbody
    have hjmpAt : Pgm[(a + (Cond.lt r13 r0 r1).code.length + 1) + decParBody.length]? =
        some (iJmp a) := by
      rw [← hlen]
      exact hjmp
    have hR' : DecParInvF N t S l mst mstLen j mb
        { runBlock (Cond.lt r13 r0 r1).code E s with
          pc := a + (Cond.lt r13 r0 r1).code.length + 1 } :=
      (hirr j (runBlock (Cond.lt r13 r0 r1).code E s) s
        (fun d hd => runBlock_cond_regs (Cond.lt r13 r0 r1) E s d hd)
        (runBlock_cond_mem (Cond.lt r13 r0 r1) E s) ⟨hRj, hFrj⟩).1
    have hFr' : (runBlock (Cond.lt r13 r0 r1).code E s).regs r14 = F := by
      rw [runBlock_cond_regs (Cond.lt r13 r0 r1) E s r14 (by decide)]
      exact hFrj
    refine Sem.monoA (decPar_bodyIter_r14F N t hN htN E hEW S l mst mstLen j mb Pgm a hbody' hjmpAt
      hcap hlN (hS j hj) { runBlock (Cond.lt r13 r0 r1).code E s with
        pc := a + (Cond.lt r13 r0 r1).code.length + 1 } rfl hR' hj) ?_
    intro k s' hk
    obtain ⟨hk1, hInv, hpc, hfr⟩ := hk
    exact ⟨le_of_eq hk1, ⟨hInv, by rw [hfr]; exact hFr'⟩, hpc⟩
  have hloop := Sem.loopPredLe Pgm E a (Cond.lt r13 r0 r1) (Stmt.code decParBody) hAt hW
    l.length (fun j s => DecParInvF N t S l mst mstLen j mb s ∧ s.regs r14 = F)
    (fun _ => decParBody.length + 1) hirr hgo hstop hstep st hpc ⟨hR, hF⟩
  refine Sem.monoA hloop (fun k s' h => ⟨?_, h.2.1.1, h.2.2, h.2.1.2⟩)
  obtain ⟨h1, h2⟩ := h
  have hsum : (∑ j ∈ Finset.range l.length,
        ((Cond.lt r13 r0 r1).code.length + 1 + (decParBody.length + 1)))
      = 12 * l.length := by
    simp [Finset.sum_const, Finset.card_range, Cond.code, decParBody_len, Nat.mul_comm]
  rw [hsum] at h1
  have hcl : (Cond.lt r13 r0 r1).code.length = 1 := rfl
  rw [hcl] at h1
  omega
/-- **Body (d), end to end, with the frame register.**  `decParStmt_spec`'s statement plus
`s'.regs r14 = cr23DecFrame N t`. -/
theorem decParStmt_specF_r14 (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (E : RAMEnv) (hEW : E.W = cr23Word N)
    (S : ℕ → Finset ℕ) (l mst : List ℕ) (mstLen : ℕ) (mb : ℕ → ℕ)
    (Pgm : Program) (a : ℕ)
    (hAt : At Pgm a (Stmt.compile decParStmt a))
    (st : RAMState) (hpc : st.pc = a)
    (h14 : st.regs r14 = cr23DecFrame N t) (h2 : st.regs r2 = l.length)
    (hcand : ∀ i, i < l.length → mb (decCandBase N t + i) = l.getD i 0)
    (hbelow : ∀ b, b < decMstBase N t → st.mem b = mb b)
    (hsl9 : mb (decSlot N t 9) = decCandBase N t)
    (hsl11 : mb (decSlot N t 11) = decMstBase N t)
    (hsl12 : mb (decSlot N t 12) = decParBase N t)
    (hsl14 : mb (decSlot N t 14) = mstLen)
    (hmst : ∀ i, i < mstLen → st.mem (decMstBase N t + i) = mst.getD i 0)
    (hcap : mstLen + l.length ≤ 2 * t + 1) (hlN : ∀ i ∈ l, i < N)
    (hS : ∀ j, j < l.length → S (j + 1) = decSymm (S j) {l.getD j 0})
    (hpar0 : ∀ v, v < 2 ^ (cr23Lb N + 1) →
      st.mem (decParBase N t + v) = if v ∈ S 0 then 1 else 0)
    (hframe : ∀ a, decOutBase N t ≤ a → st.mem a = mb a) :
    Sem Pgm E a (a + (Stmt.code decParInit).len + (Cond.lt r13 r0 r1).code.length
        + (Stmt.code decParBody).len + 2) st
      (fun k s' => k ≤ (Stmt.code decParInit).len + (2 + 12 * l.length) ∧
        DecParInvF N t S l mst mstLen l.length mb s' ∧
        s'.pc = a + (Stmt.code decParInit).len + (Cond.lt r13 r0 r1).code.length
          + (Stmt.code decParBody).len + 2 ∧
        s'.regs r14 = cr23DecFrame N t) := by
  have hcs : decParStmt = Stmt.seq (Stmt.code decParInit)
      (Stmt.loop (Cond.lt r13 r0 r1) (Stmt.code decParBody)) := rfl
  have hAt' : At Pgm a (decParInit ++ Stmt.compile
      (Stmt.loop (Cond.lt r13 r0 r1) (Stmt.code decParBody)) (a + (Stmt.code decParInit).len)) := by
    rw [hcs] at hAt
    simpa only [Stmt.compile, Stmt.len] using hAt
  obtain ⟨hAtInit, hAtLoop⟩ := At.appendA.mp hAt'
  have hinit : Sem Pgm E a (a + decParInit.length) st
      (fun k s' => k = decParInit.length ∧ s' = runBlock decParInit E st) :=
    Sem.blockA Pgm E a decParInit st hAtInit decParInit_noBranch hpc
  have hpcI : (runBlock decParInit E st).pc = a + decParInit.length := by
    rw [runBlock_pcA decParInit E st decParInit_noBranch, hpc]
  refine Sem.monoA (Sem.seqA (Q₂ := fun k1 k2 s' => k1 = (Stmt.code decParInit).len ∧
    (k2 ≤ 2 + 12 * l.length ∧
      DecParInvF N t S l mst mstLen l.length mb s' ∧
      s'.pc = a + (Stmt.code decParInit).len + (Cond.lt r13 r0 r1).code.length
        + (Stmt.code decParBody).len + 2 ∧
      s'.regs r14 = cr23DecFrame N t)) hinit ?_) ?_
  · intro k1 s1 h1
    obtain ⟨rfl, rfl⟩ := h1
    have hR0 : DecParInvF N t S l mst mstLen 0 mb (runBlock decParInit E st) :=
      decParInit_dataF N t hN htN E hEW S l mst mstLen mb st h14 h2 hcand hbelow hsl9 hsl11 hsl12
        hsl14 hmst (by omega) hpar0 hframe
    have hF0 : (runBlock decParInit E st).regs r14 = cr23DecFrame N t := by
      rw [decParInit_frame14]; exact h14
    refine Sem.monoA (decPar_loop_r14F N t hN htN E hEW S l mst mstLen mb Pgm _
      (cr23DecFrame N t) hAtLoop hcap hlN hS _ (by rw [hpcI]) hF0 hR0) ?_
    intro k s' hk
    exact ⟨rfl, hk⟩
  · intro k s' h
    obtain ⟨k1, k2, hk, h1, h2, h3, h4, h5⟩ := h
    exact ⟨by omega, h3, h4, h5⟩


-- ===== emitF.lean =====


/-- The first address above the emit pass's output window, uniformly. -/
def decEmFrame (N t : ℕ) : ℕ := decOutBase N t + (2 * t + 1)

/-! ## Frame-carrying emit pass (body (e)) -/

/-- **`DecEmitInvF`** — the loop-head invariant of body (e) at step `j`: the output words spell the
duplicate-free list `lacc`, the parity bitmap holds the *remaining* set `P \ lacc`, and every entry
of `mst` before `j` that lies in `P` has already been emitted. -/
def DecEmitInvF (N t : ℕ) (P : Finset ℕ) (mst : List ℕ) (j cnt : ℕ) (lacc : List ℕ)
    (mb : ℕ → ℕ) (st : RAMState) : Prop :=
  st.regs r0 = j ∧
  st.regs r1 = cnt ∧
  st.regs r2 = mst.length ∧
  st.regs r6 = 1 ∧
  st.regs r8 = decMstBase N t ∧
  st.regs r9 = decParBase N t ∧
  st.regs r10 = decOutBase N t ∧
  st.regs r11 = 0 ∧
  cnt ≤ j ∧
  (∀ k, k < cnt → st.mem (decOutBase N t + k) = lacc.getD k 0) ∧
  lacc.Nodup ∧ lacc.length = cnt ∧
  (∀ v, v ∈ lacc → v ∈ P) ∧
  (∀ k, k < j → mst.getD k 0 ∈ P → mst.getD k 0 ∈ lacc) ∧
  (∀ v, v < 2 ^ (cr23Lb N + 1) →
      st.mem (decParBase N t + v) = if v ∈ P \ lacc.toFinset then 1 else 0) ∧
  (∀ a, a < decParBase N t → st.mem a = mb a) ∧
  (∀ a, decEmFrame N t ≤ a → st.mem a = mb a)
/-- `DecEmitInvF` never looks at the program counter. -/
theorem DecEmitInvF_pc (N t : ℕ) (P : Finset ℕ) (mst : List ℕ) (j cnt : ℕ) (lacc : List ℕ)
    (mb : ℕ → ℕ) (p : ℕ) (st : RAMState) (h : DecEmitInvF N t P mst j cnt lacc mb st) :
    DecEmitInvF N t P mst j cnt lacc mb { st with pc := p } := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩
/-- At the end of the pass the emitted list is exactly the parity set. -/
theorem DecEmitInvF_set (N t : ℕ) (P : Finset ℕ) (mst : List ℕ) (cnt : ℕ) (lacc : List ℕ)
    (mb : ℕ → ℕ) (st : RAMState) (hsub : ∀ v, v ∈ P → v ∈ mst)
    (h : DecEmitInvF N t P mst mst.length cnt lacc mb st) : lacc.toFinset = P := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hsubP, hseen, -, -, -⟩ := h
  ext v
  constructor
  · intro hv
    exact hsubP v (List.mem_toFinset.mp hv)
  · intro hvP
    obtain ⟨k, hk, hget⟩ := dec_mem_getD (hsub v hvP)
    have hkP : mst.getD k 0 ∈ P := by rw [hget]; exact hvP
    rw [← hget]
    exact List.mem_toFinset.mpr (hseen k hk hkP)
theorem decEmitInit_dataF (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (E : RAMEnv) (hEW : E.W = cr23Word N)
    (P : Finset ℕ) (mst : List ℕ) (mb : ℕ → ℕ) (st : RAMState)
    (h14 : st.regs r14 = cr23DecFrame N t)
    (hbelow : ∀ b, b < decParBase N t → st.mem b = mb b)
    (hsl11 : mb (decSlot N t 11) = decMstBase N t)
    (hsl12 : mb (decSlot N t 12) = decParBase N t)
    (hsl13 : mb (decSlot N t 13) = decOutBase N t)
    (hsl14 : mb (decSlot N t 14) = mst.length)
    (hcap : mst.length ≤ 2 * t + 1)
    (hpar0 : ∀ v, v < 2 ^ (cr23Lb N + 1) →
      st.mem (decParBase N t + v) = if v ∈ P then 1 else 0)
    (hframe : ∀ a, decEmFrame N t ≤ a → st.mem a = mb a) :
    DecEmitInvF N t P mst 0 0 [] mb (runBlock decEmitInit E st) := by
  have hbig : 1024 < 2 ^ E.W := by rw [hEW]; exact dec_1024_lt_word N
  have hW1 : 1 < 2 ^ E.W := by omega
  have hW12 : 12 < 2 ^ E.W := by omega
  have hW13 : 13 < 2 ^ E.W := by omega
  have hW14 : 14 < 2 ^ E.W := by omega
  have hW15 : 15 < 2 ^ E.W := by omega
  have hW0 : 0 < 2 ^ E.W := by omega
  have hF12 : cr23DecFrame N t + 12 < 2 ^ E.W := by
    rw [hEW]; exact dec_frame_add_lt_word N t hN htN (by norm_num)
  have hF13 : cr23DecFrame N t + 13 < 2 ^ E.W := by
    rw [hEW]; exact dec_frame_add_lt_word N t hN htN (by norm_num)
  have hF14 : cr23DecFrame N t + 14 < 2 ^ E.W := by
    rw [hEW]; exact dec_frame_add_lt_word N t hN htN (by norm_num)
  have hF15 : cr23DecFrame N t + 15 < 2 ^ E.W := by
    rw [hEW]; exact dec_frame_add_lt_word N t hN htN (by norm_num)
  have hmbW : decMstBase N t < 2 ^ E.W := by rw [hEW]; exact dec_mstBase_lt_word N t hN htN
  have hpbW : decParBase N t < 2 ^ E.W := by rw [hEW]; exact dec_parBase_lt_word N t hN htN
  have hobW : decOutBase N t < 2 ^ E.W := by
    have h := dec_out_add_lt_word N t hN htN (j := 0) (by omega)
    rw [hEW]
    omega
  have hmlW : mst.length < 2 ^ E.W := by
    have h2t := dec_two_t_lt_word N t hN htN
    rw [hEW]
    omega
  have hslot : ∀ (k : ℕ) (_ : k < 15) (val : ℕ), mb (decSlot N t k) = val →
      st.mem (decSlot N t k) = val := by
    intro k hk val hv
    rw [hbelow _ (lt_of_lt_of_le (decSlot_lt_mstBase N t hk) (decMstBase_le_parBase N t))]
    exact hv
  have hc12 : st.mem (cr23DecFrame N t + 12) = decMstBase N t := by
    have := hslot 11 (by norm_num) _ hsl11
    rwa [decSlot_eleven] at this
  have hc13 : st.mem (cr23DecFrame N t + 13) = decParBase N t := by
    have := hslot 12 (by norm_num) _ hsl12
    rwa [decSlot_twelve] at this
  have hc14 : st.mem (cr23DecFrame N t + 14) = decOutBase N t := by
    have := hslot 13 (by norm_num) _ hsl13
    rwa [decSlot_thirteen] at this
  have hc15 : st.mem (cr23DecFrame N t + 15) = mst.length := by
    have := hslot 14 (by norm_num) _ hsl14
    rwa [decSlot_fourteen] at this
  obtain ⟨hr0, hr1, hr2, hr6, hr8, hr9, hr10, hr11⟩ :=
    decEmitInit_regs E st (cr23DecFrame N t) (decMstBase N t) (decParBase N t)
      (decOutBase N t) (mst.length) h14 hW1 hW12 hW13 hW14 hW15 hW0 hF12 hF13 hF14 hF15 hc12 hc13
      hc14 hc15 hmbW hpbW hobW hmlW
  have hmem : (runBlock decEmitInit E st).mem = st.mem := decEmitInit_mem E st
  refine ⟨hr0, hr1, hr2, hr6, hr8, hr9, hr10, hr11, by omega, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    omega
  · exact List.nodup_nil
  · intro v hv
    exact absurd hv (by simp)
  · intro k hk
    omega
  · intro v hv
    rw [hmem]
    have h : P \ ([] : List ℕ).toFinset = P := by simp
    rw [h]
    exact hpar0 v hv
  · intro b hb
    rw [hmem]
    exact hbelow b hb
  · intro a ha
    rw [hmem]
    exact hframe a ha
theorem decEmitBody_dataF (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (E : RAMEnv) (hEW : E.W = cr23Word N)
    (P : Finset ℕ) (mst : List ℕ) (j cnt : ℕ) (lacc : List ℕ) (mb : ℕ → ℕ) (st : RAMState)
    (hj : j < mst.length) (hcap : mst.length ≤ 2 * t + 1) (hmstN : ∀ v ∈ mst, v < N)
    (hmstm : ∀ i, i < mst.length → mb (decMstBase N t + i) = mst.getD i 0)
    (hI : DecEmitInvF N t P mst j cnt lacc mb st) :
    DecEmitInvF N t P mst (j + 1) (cnt + decEmitSel P lacc (mst.getD j 0))
      (decEmitApp P lacc (mst.getD j 0)) mb (runBlock decEmitBody E st) := by
  obtain ⟨h0, h1, h2, h6, h8, h9, h10, h11, hcj, hout, hnd, hlen, hsubP, hseen, hpar,
    hbelow, hframe⟩ := hI
  have hW : 1 < 2 ^ E.W := by rw [hEW]; exact cr23_one_lt_word N hN
  set x : ℕ := mst.getD j 0 with hx
  set sel : ℕ := decEmitSel P lacc x with hsel
  have hxmem : x ∈ mst := by rw [hx]; exact dec_getD_mem hj
  have hxN : x < N := hmstN x hxmem
  have hxl : x < 2 ^ (cr23Lb N + 1) := by
    have h1' : N ≤ 2 ^ cr23Lb N := cr23_le_pow_lb N
    have h2' : 2 ^ cr23Lb N ≤ 2 ^ (cr23Lb N + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hxW : x < 2 ^ E.W := by
    have hexp : cr23Lb N + 1 ≤ cr23Word N := by
      simp only [cr23Word]
      have := cr23Lb_succ_pos N
      omega
    rw [hEW]
    exact lt_of_lt_of_le hxl (Nat.pow_le_pow_right (by norm_num) hexp)
  have hsel1 : sel ≤ 1 := by rw [hsel]; exact decEmitSel_le P lacc x
  have h2t : 2 * t + 1 < 2 ^ E.W := by rw [hEW]; exact dec_two_t_lt_word N t hN htN
  have hjW : j + 1 < 2 ^ E.W := by omega
  have hparOut : decParBase N t ≤ decOutBase N t := decParBase_le_outBase N t
  have hmstjPar : decMstBase N t + j < decParBase N t := by
    have h2' : decMstBase N t + mst.length ≤ decMstBase N t + (2 * t + 1) :=
      Nat.add_le_add_left hcap _
    have h3 : decMstBase N t + (2 * t + 1) = decParBase N t := by simp only [decParBase]
    have h1' : decMstBase N t + j < decMstBase N t + mst.length := Nat.add_lt_add_left hj _
    omega
  have hlenW : decMstBase N t + j < 2 ^ E.W := by
    have h5 : decParBase N t < 2 ^ E.W := by rw [hEW]; exact dec_parBase_lt_word N t hN htN
    omega
  have hparxW : decParBase N t + x < 2 ^ E.W := by
    rw [hEW]; exact dec_par_add_lt_word N t hN htN hxl
  have houtcW : decOutBase N t + cnt < 2 ^ E.W := by
    have h4 := dec_out_add_lt_word N t hN htN (j := 2 * t + 1) (le_refl _)
    rw [hEW]
    omega
  have hcsW : cnt + sel < 2 ^ E.W := by omega
  have hAx : decParBase N t + x < decOutBase N t := by
    have h3 : decParBase N t + 2 ^ (cr23Lb N + 1) = decOutBase N t := by simp only [decOutBase]
    have h4 : decParBase N t + x < decParBase N t + 2 ^ (cr23Lb N + 1) :=
      Nat.add_lt_add_left hxl _
    omega
  have hxmem' : st.mem (decMstBase N t + j) = x := by
    rw [hbelow _ hmstjPar, hx]
    exact hmstm j hj
  have hparx : st.mem (decParBase N t + x) = sel := by
    rw [hsel]
    exact hpar x hxl
  -- chunk A
  set st1 : RAMState := runBlock decEmitBA E st with hst1
  have hBA := decEmitBA_spec E st (decMstBase N t) (decParBase N t) j x sel h8 h9 h0 h11
    hW hlenW hxmem' hxW hparxW hparx hsel1
  have hA0 : st1.regs r0 = j := by
    rw [hst1]; exact (decEmitBA_frame E st r0 (by decide) (by decide) (by decide)).trans h0
  have hA1 : st1.regs r1 = cnt := by
    rw [hst1]; exact (decEmitBA_frame E st r1 (by decide) (by decide) (by decide)).trans h1
  have hA3 : st1.regs r3 = x := hBA.1
  have hA4 : st1.regs r4 = sel := hBA.2.1
  have hA6 : st1.regs r6 = 1 := by
    rw [hst1]; exact (decEmitBA_frame E st r6 (by decide) (by decide) (by decide)).trans h6
  have hA10 : st1.regs r10 = decOutBase N t := by
    rw [hst1]; exact (decEmitBA_frame E st r10 (by decide) (by decide) (by decide)).trans h10
  have hAmem : st1.mem = Function.update st.mem (decParBase N t + x) 0 := hBA.2.2
  -- chunk B
  have hBB := decEmitBB_spec E st1 (decOutBase N t) cnt x sel j hA10 hA1 hA3 hA4 hA6 hA0 houtcW
    hcsW hjW
  have hB0 : (runBlock decEmitBody E st).regs r0 = j + 1 := by
    rw [decEmitBody_split, runBlock_appendA, ← hst1]; exact hBB.2.1
  have hB1 : (runBlock decEmitBody E st).regs r1 = cnt + sel := by
    rw [decEmitBody_split, runBlock_appendA, ← hst1]; exact hBB.2.2
  have hBmem : (runBlock decEmitBody E st).mem
      = Function.update (Function.update st.mem (decParBase N t + x) 0)
          (decOutBase N t + cnt) x := by
    rw [decEmitBody_split, runBlock_appendA, ← hst1, hBB.1, hAmem]
  have hrest : ∀ d : Fin 16, d ≠ r5 → d ≠ r3 → d ≠ r4 → d ≠ r0 → d ≠ r1 →
      (runBlock decEmitBody E st).regs d = st.regs d := by
    intro d h5 h3 h4 h0' h1'
    rw [decEmitBody_split, runBlock_appendA, ← hst1]
    exact (decEmitBB_frame E (runBlock decEmitBA E st) d h5 h0' h1').trans
      (decEmitBA_frame E st d h5 h3 h4)
  refine ⟨hB0, hB1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrest r2 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h2
  · rw [hrest r6 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h6
  · rw [hrest r8 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h8
  · rw [hrest r9 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h9
  · rw [hrest r10 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h10
  · rw [hrest r11 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h11
  · omega
  · -- the output words
    intro k hk
    rcases lt_or_eq_of_le (by omega : k ≤ cnt) with hkc | hkc
    · rw [hBmem, dec_upd2_ne
        (dec_ne_of_lt' (lt_of_lt_of_le hAx (dec_le_add_r _ _)))
        (dec_ne_add_l (ne_of_lt hkc)), decEmitApp_getD P lacc x (by omega)]
      exact hout k hkc
    · subst hkc
      have hpos : x ∈ P \ lacc.toFinset := by
        rw [← decEmitSel_one, ← hsel]
        omega
      rw [hBmem, dec_upd2_snd, decEmitApp_pos P lacc hpos, ← hlen]
      exact (dec_getD_append_add lacc [x] (k := 0) (by simp)).symm
  · -- `Nodup`
    exact decEmitApp_nodup P lacc x hnd
  · -- the length
    rw [decEmitApp_length P lacc x, hlen, hsel]
  · -- emitted values lie in `P`
    exact decEmitApp_sub P lacc x hsubP
  · -- every `P`-entry of the master list up to `j+1` is emitted
    exact decEmitApp_seen P lacc mst j x hx hseen
  · -- the parity bitmap
    intro w hw
    by_cases hwx : w = x
    · subst hwx
      rw [hBmem, dec_upd2_fst (dec_ne_of_lt' (lt_of_lt_of_le hAx (dec_le_add_r _ _)))]
      by_cases hsel : x ∈ P \ lacc.toFinset
      · rw [if_neg (decEmitApp_self P lacc hsel)]
      · rw [if_neg (decEmitApp_self_neg P lacc hsel)]
    · have hAw : decParBase N t + w < decOutBase N t := by
        have h3 : decParBase N t + 2 ^ (cr23Lb N + 1) = decOutBase N t := by
          simp only [decOutBase]
        have h4 : decParBase N t + w < decParBase N t + 2 ^ (cr23Lb N + 1) :=
          Nat.add_lt_add_left hw _
        omega
      rw [hBmem, dec_upd2_ne (dec_ne_add_l hwx)
        (dec_ne_of_lt (lt_of_lt_of_le hAw (dec_le_add_r _ _))), hpar w hw]
      by_cases hwP : w ∈ P \ lacc.toFinset
      · rw [if_pos hwP, if_pos ((decEmitApp_sdiff P lacc hwx).mpr hwP)]
      · rw [if_neg hwP, if_neg (fun hh => hwP ((decEmitApp_sdiff P lacc hwx).mp hh))]
  · -- the frame below the parity bitmap
    intro a ha
    rw [hBmem, dec_upd2_ne
      (dec_ne_of_lt (lt_of_lt_of_le ha (dec_le_add_r _ _)))
      (dec_ne_of_lt (lt_of_lt_of_le (lt_of_lt_of_le ha hparOut) (dec_le_add_r _ _)))]
    exact hbelow a ha
  · -- the frame above the output window
    intro a ha
    have hcnt : cnt < 2 * t + 1 := by omega
    have h2 : decOutBase N t + cnt < decEmFrame N t := by
      simp only [decEmFrame]
      exact Nat.add_lt_add_left hcnt _
    rw [hBmem, dec_upd2_ne
      (dec_ne_of_lt' (lt_of_lt_of_le hAx (le_trans (Nat.le_add_right (decOutBase N t) (2 * t + 1)) ha)))
      (dec_ne_of_lt' (lt_of_lt_of_le h2 ha))]
    exact hframe a ha
/-- **One iteration of the emit pass**: the test, the `jz`, the 9-instruction body and the `jmp`. -/
theorem decEmit_bodyIterF (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (E : RAMEnv) (hEW : E.W = cr23Word N)
    (P : Finset ℕ) (mst : List ℕ) (j cnt : ℕ) (lacc : List ℕ) (mb : ℕ → ℕ)
    (Pgm : Program) (a : ℕ)
    (hAtBody : At Pgm (a + (Cond.lt r13 r0 r2).code.length + 1) decEmitBody)
    (hjmpAt : Pgm[(a + (Cond.lt r13 r0 r2).code.length + 1) + decEmitBody.length]? =
      some (iJmp a))
    (hcap : mst.length ≤ 2 * t + 1) (hmstN : ∀ v ∈ mst, v < N)
    (hmstm : ∀ i, i < mst.length → mb (decMstBase N t + i) = mst.getD i 0)
    (st : RAMState) (hpc : st.pc = a + (Cond.lt r13 r0 r2).code.length + 1)
    (hR : DecEmitInvF N t P mst j cnt lacc mb st) (hj : j < mst.length) :
    Sem Pgm E (a + (Cond.lt r13 r0 r2).code.length + 1) a
      { st with pc := a + (Cond.lt r13 r0 r2).code.length + 1 }
      (fun k s' => k = decEmitBody.length + 1 ∧
        DecEmitInvF N t P mst (j + 1) (cnt + decEmitSel P lacc (mst.getD j 0))
          (decEmitApp P lacc (mst.getD j 0)) mb s' ∧ s'.pc = a) := by
  set b : ℕ := a + (Cond.lt r13 r0 r2).code.length + 1 with hb
  have hblk : Sem Pgm E b (b + decEmitBody.length) { st with pc := b }
      (fun k s' => k = decEmitBody.length ∧ s' = runBlock decEmitBody E { st with pc := b }) :=
    Sem.blockA Pgm E b decEmitBody { st with pc := b } hAtBody decEmitBody_noBranch rfl
  have hpcB : (runBlock decEmitBody E { st with pc := b }).pc = b + decEmitBody.length := by
    rw [runBlock_pcA decEmitBody E _ decEmitBody_noBranch]
  have hjmpSem : Sem Pgm E (b + decEmitBody.length) a
      (runBlock decEmitBody E { st with pc := b })
      (fun k s' => k = 1 ∧ s' = { runBlock decEmitBody E { st with pc := b } with pc := a }) :=
    Sem.execA Pgm E (b + decEmitBody.length) a _ (iJmp a) hjmpAt hpcB rfl
  refine Sem.monoA (Sem.transA hblk hjmpSem) ?_
  intro k s' hk
  obtain ⟨rfl, rfl⟩ := hk
  exact ⟨rfl, DecEmitInvF_pc N t P mst (j + 1) (cnt + decEmitSel P lacc (mst.getD j 0))
    (decEmitApp P lacc (mst.getD j 0)) mb a _
    (decEmitBody_dataF N t hN htN E hEW P mst j cnt lacc mb { st with pc := b } hj hcap hmstN
      hmstm hR), rfl⟩
/-- **The emit loop**: `mst.length` iterations, then the failing test. -/
theorem decEmit_loopF (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (E : RAMEnv) (hEW : E.W = cr23Word N)
    (P : Finset ℕ) (mst : List ℕ) (mb : ℕ → ℕ) (Pgm : Program) (a : ℕ)
    (hAt : At Pgm a (Stmt.compile (Stmt.loop (Cond.lt r13 r0 r2) (Stmt.code decEmitBody)) a))
    (hcap : mst.length ≤ 2 * t + 1) (hmstN : ∀ v ∈ mst, v < N)
    (hmstm : ∀ i, i < mst.length → mb (decMstBase N t + i) = mst.getD i 0)
    (st : RAMState) (hpc : st.pc = a) (hR : DecEmitInvF N t P mst 0 0 [] mb st) :
    Sem Pgm E a (a + (Cond.lt r13 r0 r2).code.length + (Stmt.code decEmitBody).len + 2) st
      (fun k s' => k ≤ 2 + 12 * mst.length ∧
        (∃ cnt lacc, DecEmitInvF N t P mst mst.length cnt lacc mb s') ∧
        s'.pc = a + (Cond.lt r13 r0 r2).code.length + (Stmt.code decEmitBody).len + 2) := by
  have hW : 1 < 2 ^ E.W := by rw [hEW]; exact cr23_one_lt_word N hN
  have htrans : ∀ (j : ℕ) (s s' : RAMState), (∀ d : Fin 16, d ≠ r13 → s.regs d = s'.regs d) →
      s.mem = s'.mem → ∀ cnt lacc, DecEmitInvF N t P mst j cnt lacc mb s →
        DecEmitInvF N t P mst j cnt lacc mb s' := by
    rintro j s s' hd hm' cnt lacc h
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩ := h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hd r0 (by decide)]; exact a1
    · rw [← hd r1 (by decide)]; exact a2
    · rw [← hd r2 (by decide)]; exact a3
    · rw [← hd r6 (by decide)]; exact a4
    · rw [← hd r8 (by decide)]; exact a5
    · rw [← hd r9 (by decide)]; exact a6
    · rw [← hd r10 (by decide)]; exact a7
    · rw [← hd r11 (by decide)]; exact a8
    · exact a9
    · intro k hk; rw [← hm']; exact a10 k hk
    · exact a11
    · exact a12
    · exact a13
    · exact a14
    · intro v hv; rw [← hm']; exact a15 v hv
    · intro b hb; rw [← hm']; exact a16 b hb
    · intro a ha; rw [← hm']; exact a17 a ha
  have hirr : ∀ (j : ℕ) (s s' : RAMState), (∀ d : Fin 16, d ≠ r13 → s.regs d = s'.regs d) →
      s.mem = s'.mem → (∃ cnt lacc, DecEmitInvF N t P mst j cnt lacc mb s) →
        (∃ cnt lacc, DecEmitInvF N t P mst j cnt lacc mb s') := by
    rintro j s s' hd hm' ⟨cnt, lacc, h⟩
    exact ⟨cnt, lacc, htrans j s s' hd hm' cnt lacc h⟩
  have hgo : ∀ j, j < mst.length → ∀ s, (∃ cnt lacc, DecEmitInvF N t P mst j cnt lacc mb s) →
      (Cond.lt r13 r0 r2).eval s := by
    rintro j hj s ⟨cnt, lacc, h⟩
    obtain ⟨h0, -, h2, -⟩ := h
    show s.regs r0 < s.regs r2
    rw [h0, h2]; exact hj
  have hstop : ∀ s, (∃ cnt lacc, DecEmitInvF N t P mst mst.length cnt lacc mb s) →
      ¬ (Cond.lt r13 r0 r2).eval s := by
    rintro s ⟨cnt, lacc, h⟩
    obtain ⟨h0, -, h2, -⟩ := h
    show ¬ (s.regs r0 < s.regs r2)
    rw [h0, h2]; omega
  have hstep : ∀ j, j < mst.length → ∀ s, s.pc = a →
      (∃ cnt lacc, DecEmitInvF N t P mst j cnt lacc mb s) →
      Sem Pgm E (a + (Cond.lt r13 r0 r2).code.length + 1) a
        { runBlock (Cond.lt r13 r0 r2).code E s with
          pc := a + (Cond.lt r13 r0 r2).code.length + 1 }
        (fun k s' => k ≤ decEmitBody.length + 1 ∧
          (∃ cnt lacc, DecEmitInvF N t P mst (j + 1) cnt lacc mb s') ∧ s'.pc = a) := by
    rintro j hj s hpc' ⟨cnt, lacc, hRs⟩
    obtain ⟨-, hjz, hbody, hjmp⟩ := at_loopA hAt
    have hlen : (Stmt.code decEmitBody).len = decEmitBody.length := rfl
    have hbody' : At Pgm (a + (Cond.lt r13 r0 r2).code.length + 1) decEmitBody := hbody
    have hjmpAt : Pgm[(a + (Cond.lt r13 r0 r2).code.length + 1) + decEmitBody.length]? =
        some (iJmp a) := by
      rw [← hlen]
      exact hjmp
    have hR' : DecEmitInvF N t P mst j cnt lacc mb
        { runBlock (Cond.lt r13 r0 r2).code E s with
          pc := a + (Cond.lt r13 r0 r2).code.length + 1 } :=
      htrans j (runBlock (Cond.lt r13 r0 r2).code E s) s
        (fun d hd => runBlock_cond_regs (Cond.lt r13 r0 r2) E s d hd)
        (runBlock_cond_mem (Cond.lt r13 r0 r2) E s) cnt lacc hRs
    refine Sem.monoA (decEmit_bodyIterF N t hN htN E hEW P mst j cnt lacc mb Pgm a hbody' hjmpAt
      hcap hmstN hmstm { runBlock (Cond.lt r13 r0 r2).code E s with
        pc := a + (Cond.lt r13 r0 r2).code.length + 1 } rfl hR' hj) ?_
    intro k s' hk
    exact ⟨le_of_eq hk.1, ⟨_, _, hk.2.1⟩, hk.2.2⟩
  have hloop := Sem.loopPredLe Pgm E a (Cond.lt r13 r0 r2) (Stmt.code decEmitBody) hAt hW
    mst.length (fun j s => ∃ cnt lacc, DecEmitInvF N t P mst j cnt lacc mb s)
    (fun _ => decEmitBody.length + 1) hirr hgo hstop hstep st hpc ⟨0, [], hR⟩
  refine Sem.monoA hloop (fun k s' h => ⟨?_, h.2.1, h.2.2⟩)
  obtain ⟨h1, h2, h3⟩ := h
  have hsum : (∑ j ∈ Finset.range mst.length,
        ((Cond.lt r13 r0 r2).code.length + 1 + (decEmitBody.length + 1)))
      = 12 * mst.length := by
    simp [Finset.sum_const, Finset.card_range, Cond.code, decEmitBody_len, Nat.mul_comm]
  rw [hsum] at h1
  have hcl : (Cond.lt r13 r0 r2).code.length = 1 := rfl
  rw [hcl] at h1
  omega
/-- The loop's final invariant, read as the output-list facts. -/
theorem decEmit_finalF (N t : ℕ) (P : Finset ℕ) (mst : List ℕ) (mb : ℕ → ℕ) (st : RAMState)
    (hsub : ∀ v, v ∈ P → v ∈ mst)
    (h : ∃ cnt lacc, DecEmitInvF N t P mst mst.length cnt lacc mb st) :
    ∃ lacc : List ℕ, lacc.Nodup ∧ st.regs r1 = lacc.length ∧
      (∀ k, k < lacc.length → st.mem (decOutBase N t + k) = lacc.getD k 0) ∧
      lacc.toFinset = P := by
  obtain ⟨cnt, lacc, hI⟩ := h
  have hcopy := hI
  obtain ⟨-, h1, -, -, -, -, -, -, -, hout, hnd, hlen, -, -, -, -, -⟩ := hI
  exact ⟨lacc, hnd, by rw [h1, hlen], by rw [hlen]; exact hout,
    DecEmitInvF_set N t P mst cnt lacc mb st hsub hcopy⟩
/-- The output reading, with the invariant taken on the state *before* the postlude and the
`r0`/`r1`/memory facts taken after it. -/
theorem decEmit_outputsSupport_postF (N t : ℕ) (P : Finset ℕ) (mst : List ℕ) (mb : ℕ → ℕ)
    (s1 s : RAMState) (x z : Fin N → ZMod 2)
    (hP : P = cr23NumSet (cr23Supp (x + z))) (hK : cr23Supp z = ∅)
    (hsub : ∀ v, v ∈ P → v ∈ mst)
    (h0 : s.regs r0 = decOutBase N t) (hmem : s.mem = s1.mem) (h1 : s.regs r1 = s1.regs r1)
    (hInv : ∃ cnt lacc, DecEmitInvF N t P mst mst.length cnt lacc mb s1) :
    OutputsSupport s x := by
  obtain ⟨lacc, hnd, hlen, hout, hset⟩ := decEmit_finalF N t P mst mb s1 hsub hInv
  refine decOutputsSupport_of_mem s x (decOutBase N t) lacc.length lacc h0 ?_ rfl ?_ hnd ?_
  · rw [h1, hlen]
  · intro k hk
    rw [hmem, hout k hk]
  · intro v
    rw [← List.mem_toFinset, hset]
    exact decRounds_final_support x z P hP hK v
theorem decEmitStmt_specF (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x z : Fin N → ZMod 2)
    (w tag : ℕ) (P : Finset ℕ) (mst : List ℕ) (st : RAMState) (Pgm : Program) (a : ℕ)
    (hAt : At Pgm a (Stmt.compile decEmitStmt a))
    (hpc : st.pc = a) (hw : w = 0)
    (hH : DecHead1 N t C x z w tag P mst st) (hK : cr23Supp z = ∅) :
    Sem Pgm (detEnv (cr23Word N) (cr23DecDet N t C)) a (a + decEmitStmt.len) st
      (fun k s' => k ≤ decEmitStmtCost N t ∧ OutputsSupport s' x ∧
        (∀ a, decEmFrame N t ≤ a → s'.mem a = st.mem a)) := by
  subst hw
  obtain ⟨hHead, hmstN, hpar1⟩ := hH
  obtain ⟨hD, h14, hP', hsub, hcap0, hcard⟩ := hHead
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h11s, h12s, h13s, h14s, -, -, hpar, hmst⟩ := hD
  have hcap : mst.length ≤ 2 * t + 1 := by
    have h := hcap0
    omega
  set E : RAMEnv := detEnv (cr23Word N) (cr23DecDet N t C) with hE
  have hEW : E.W = cr23Word N := rfl
  have hpar0 := decPar_if_eq N t P st hpar1 hpar
  have hbel : ∀ b, b < decParBase N t → st.mem b = st.mem b := fun _ _ => rfl
  have hsl11 : st.mem (decSlot N t 11) = decMstBase N t := h11s
  have hsl12 : st.mem (decSlot N t 12) = decParBase N t := h12s
  have hsl13 : st.mem (decSlot N t 13) = decOutBase N t := h13s
  have hsl14 : st.mem (decSlot N t 14) = mst.length := h14s
  -- split the compile: init · (loop · post)
  have hAtAll : At Pgm a (decEmitInit ++ (Stmt.compile
      (Stmt.loop (Cond.lt r13 r0 r2) (Stmt.code decEmitBody)) (a + decEmitInit.length)
        ++ decEmitPost)) := hAt
  obtain ⟨hAtI, hAtAll⟩ := At.appendA.mp hAtAll
  obtain ⟨hAtL0, hAtP0⟩ := At.appendA.mp hAtAll
  have hlooplen : (Stmt.compile (Stmt.loop (Cond.lt r13 r0 r2) (Stmt.code decEmitBody))
      (a + decEmitInit.length)).length = 12 := by
    rw [Stmt.length_compileA]
    simp only [Stmt.len, Cond.code, decEmitBody_len, List.length_cons, List.length_nil]
  have hAtPost : At Pgm (a + decEmitInit.length + 12) decEmitPost := by
    have h := hAtP0
    rw [hlooplen] at h
    exact h
  -- the initialisation
  have hInitInv : DecEmitInvF N t P mst 0 0 [] st.mem (runBlock decEmitInit E st) :=
    decEmitInit_dataF N t hN htN E hEW P mst st.mem st h14 hbel hsl11 hsl12 hsl13 hsl14 hcap hpar0
      (fun _ _ => rfl)
  have hInitPc : (runBlock decEmitInit E st).pc = a + decEmitInit.length := by
    rw [runBlock_pcA decEmitInit E st decEmitInit_noBranch, hpc]
  -- the walk
  have hLoop := decEmit_loopF N t hN htN E hEW P mst st.mem Pgm (a + decEmitInit.length) hAtL0
    hcap hmstN hmst (runBlock decEmitInit E st) hInitPc hInitInv
  have hLoopP : Sem Pgm E (a + decEmitInit.length) (a + decEmitInit.length + 12)
      (runBlock decEmitInit E st)
      (fun k s' => k ≤ 2 + 12 * mst.length ∧
        (∃ cnt lacc, DecEmitInvF N t P mst mst.length cnt lacc st.mem s') ∧
        s'.pc = a + decEmitInit.length + 12) :=
    Sem.monoA hLoop (fun k s' h => ⟨h.1, h.2.1, h.2.2⟩)
  -- the postlude
  have hOutW : decOutBase N t < 2 ^ E.W := by
    rw [hEW]; exact dec_out_add_lt_word N t hN htN (j := 0) (by omega)
  have hPostSem : ∀ (s1 : RAMState),
      (∃ cnt lacc, DecEmitInvF N t P mst mst.length cnt lacc st.mem s1) →
      s1.pc = a + decEmitInit.length + 12 →
      Sem Pgm E (a + decEmitInit.length + 12)
        (a + decEmitInit.length + 12 + decEmitPost.length) s1
        (fun k s' => k = decEmitPost.length ∧ s'.regs r0 = decOutBase N t ∧
          s'.mem = s1.mem ∧ s'.regs r1 = s1.regs r1 ∧
          (∀ a, decEmFrame N t ≤ a → s'.mem a = st.mem a)) := by
    intro s1 hInv1 hpc1
    obtain ⟨cnt, lacc, hI1⟩ := hInv1
    obtain ⟨-, -, -, -, -, -, h10, -, -, -, -, -, -, -, -, -, hframe1⟩ := hI1
    refine Sem.monoA (Sem.blockA Pgm E (a + decEmitInit.length + 12) decEmitPost s1 hAtPost
      decEmitPost_noBranch hpc1) ?_
    rintro k s' ⟨hk, rfl⟩
    exact ⟨hk, decEmitPost_spec E s1 (decOutBase N t) h10 hOutW,
      decEmitPost_mem E s1, decEmitPost_frame E s1 r1 (by decide),
      fun a ha => by rw [decEmitPost_mem E s1]; exact hframe1 a ha⟩
  -- init · (loop · post)
  refine Sem.monoA (Sem.seqA
    (Q₁ := fun k0 s0 => k0 = decEmitInit.length ∧ s0 = runBlock decEmitInit E st)
    (Q₂ := fun k0 k' s' => ∃ k1 k2, k' = k1 + k2 ∧ k0 = decEmitInit.length ∧
      k1 ≤ 2 + 12 * mst.length ∧ k2 = decEmitPost.length ∧ OutputsSupport s' x ∧
      (∀ a, decEmFrame N t ≤ a → s'.mem a = st.mem a))
    (Sem.blockA Pgm E a decEmitInit st hAtI decEmitInit_noBranch hpc) ?_) ?_
  · intro k0 s0 hQ0
    obtain ⟨hk0, rfl⟩ := hQ0
    refine Sem.seqA
      (Q₁ := fun k1 s1 => k1 ≤ 2 + 12 * mst.length ∧
        (∃ cnt lacc, DecEmitInvF N t P mst mst.length cnt lacc st.mem s1) ∧
        s1.pc = a + decEmitInit.length + 12)
      (Q₂ := fun k1 k2 s' => k0 = decEmitInit.length ∧ k1 ≤ 2 + 12 * mst.length ∧
        k2 = decEmitPost.length ∧ OutputsSupport s' x ∧
        (∀ a, decEmFrame N t ≤ a → s'.mem a = st.mem a)) hLoopP ?_
    intro k1 s1 hQ1
    obtain ⟨hk1, hInv1, hpc1⟩ := hQ1
    refine Sem.monoA (hPostSem s1 hInv1 hpc1) (fun k s' hh => ⟨hk0, hk1, hh.1, ?_, hh.2.2.2.2⟩)
    exact decEmit_outputsSupport_postF N t P mst st.mem s1 s' x z hP' hK hsub
      hh.2.1 hh.2.2.1 hh.2.2.2.1 hInv1
  · rintro k s' ⟨k0, k', hk, k1, k2, hk', h16, hk1, hk2, hout, hfr⟩
    refine ⟨?_, hout, hfr⟩
    have hle := decEmitStmtCost_le N t mst hcap
    omega


-- ===== bodyF.lean =====


open DecCandPay

/-- **One round**: from a round head at `(w, tag, P, mst)` the five legs reach a round head at
`(w/4, tag+1, decSymm P l.toFinset, mst ++ l)` for the candidate list `l` the scan produced. -/
theorem decRoundBody_specF (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x z : Fin N → ZMod 2)
    (w tag : ℕ) (P : Finset ℕ) (mst : List ℕ) (eps : ℝ)
    (hexp : IsLayeredExpander C (2 * t) eps) (heps : 16 * eps ≤ 1)
    (Pgm : Program) (b : ℕ) (hAt : At Pgm b (Stmt.compile decRoundBody b))
    (st : RAMState) (hpc : st.pc = b) (hR : DecHead1 N t C x z w tag P mst st)
    (h9 : st.regs r9 = w)
    (hwW : w < 2 ^ cr23Word N) (htagW : tag + 1 < 2 ^ cr23Word N)
    (h2tW : 2 * t + 1 < 2 ^ cr23Word N) :
    Sem Pgm (detEnv (cr23Word N) (cr23DecDet N t C)) b (b + decRoundBody.len) st
      (fun k s' => k ≤ decRoundCost N t ∧
        (∃ z' P' mst', DecHead1 N t C x z' (w / 4) (tag + 1) P' mst' s') ∧ s'.regs r9 = w / 4 ∧
        s'.pc = b + decRoundBody.len ∧
        (∀ a, decOutBase N t ≤ a → s'.mem a = st.mem a)) := by
  obtain ⟨hHead, hmstN, hpar1⟩ := hR
  obtain ⟨hD, h14, hP, hsub, hcap, hcard⟩ := hHead
  have hDp : DecDataN N t C z w tag mst.length P mst st := hD
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9s, h10s, h11s, h12s, h13s, h14s, hpay, htaglt,
    hpar, hmst⟩ := hD
  have hsup : (cr23Supp z).card ≤ t := by omega
  set E : RAMEnv := detEnv (cr23Word N) (cr23DecDet N t C) with hE
  have hEW : E.W = cr23Word N := by rw [hE]; rfl
  -- flatten the compile, one leg at a time
  have hcs : decRoundBody = decScanStmt.seq
      ((decCandStmtFull.seq (Stmt.code [iImm r1 0])).seq
        (decXorStmt.seq (decParStmt.seq (Stmt.code decAdvance)))) := rfl
  have h1' : At Pgm b (Stmt.compile decRoundBody b) := hAt
  rw [hcs] at h1'
  simp only [Stmt.compile, Stmt.length_compileA, Stmt.len, List.append_assoc, List.length_cons,
    List.length_nil] at h1'
  obtain ⟨hAtS, h1'⟩ := At.appendA.mp h1'
  simp only [Stmt.length_compileA] at h1'
  obtain ⟨hAtC, h1'⟩ := At.appendA.mp h1'
  simp only [Stmt.length_compileA] at h1'
  obtain ⟨hAtR, h1'⟩ := At.appendA.mp h1'
  simp only [List.length_cons, List.length_nil] at h1'
  obtain ⟨hAtX, h1'⟩ := At.appendA.mp h1'
  simp only [Stmt.length_compileA] at h1'
  obtain ⟨hAtP, h1'⟩ := At.appendA.mp h1'
  simp only [Stmt.length_compileA] at h1'
  set b1 : ℕ := b + decScanStmt.len with hb1def
  set b2 : ℕ := b1 + decCandStmtFull.len with hb2def
  set b3 : ℕ := b2 + 1 with hb3def
  set b4 : ℕ := b3 + decXorStmt.len with hb4def
  set b5 : ℕ := b4 + decParStmt.len with hb5def
  set b6 : ℕ := b5 + decAdvance.length with hb6def
  have hAtA : At Pgm b5 decAdvance := h1'
  have hb1end : b1 = (b + (Stmt.code decScanInit).len) + (Cond.lt r13 r0 r1).code.length
      + (Stmt.code decScanBody).len + 2 := by
    rw [hb1def]
    show b + ((Stmt.code decScanInit).len +
        (((Cond.lt r13 r0 r1).code.length + (Stmt.code decScanBody).len) + 2))
      = (b + (Stmt.code decScanInit).len) + (Cond.lt r13 r0 r1).code.length
        + (Stmt.code decScanBody).len + 2
    omega
  have hb2end : b2 = (b1 + (Stmt.code decCandInit).len) + (Cond.lt r15 r0 r7).code.length
      + (Stmt.code decCandBody).len + 2 := by
    rw [hb2def, hb1def]
    show (b + decScanStmt.len) + ((Stmt.code decCandInit).len +
        (((Cond.lt r15 r0 r7).code.length + (Stmt.code decCandBody).len) + 2))
      = ((b + decScanStmt.len) + (Stmt.code decCandInit).len) + (Cond.lt r15 r0 r7).code.length
        + (Stmt.code decCandBody).len + 2
    omega
  have hb4end : b4 = b3 + (Cond.lt r8 r1 r2).code.length + decXorBody.len + 2 := by
    rw [hb4def, hb3def]
    show b3 + (((Cond.lt r8 r1 r2).code.length + decXorBody.len) + 2)
      = b3 + (Cond.lt r8 r1 r2).code.length + decXorBody.len + 2
    omega
  have hb5end : b5 = (b4 + (Stmt.code decParInit).len) + (Cond.lt r13 r0 r1).code.length
      + (Stmt.code decParBody).len + 2 := by
    rw [hb5def, hb4def, hb3def]
    show b3 + decXorStmt.len + ((Stmt.code decParInit).len +
        (((Cond.lt r13 r0 r1).code.length + (Stmt.code decParBody).len) + 2))
      = ((b3 + decXorStmt.len) + (Stmt.code decParInit).len) + (Cond.lt r13 r0 r1).code.length
        + (Stmt.code decParBody).len + 2
    omega
  have hb6 : b6 = b + decRoundBody.len := by
    have hlen6 : decRoundBody.len = decScanStmt.len +
        ((decCandStmtFull.len + 1) + (decXorStmt.len + (decParStmt.len + decAdvance.length))) := rfl
    rw [hb6def, hb5def, hb4def, hb3def, hb2def, hb1def, hlen6]
    omega
  -- leg (a)
  have hscan : Sem Pgm E b b1 st
      (fun k s' => k ≤ (Stmt.code decScanInit).len + (2 + 30 * (cr23D N * cr23M t)) ∧
        DecScanInv N t C z w (cr23D N * cr23M t) st.mem s' ∧ s'.pc = b1) := by
    have h := decScanStmt_spec_at N t hN ht htN C z w st.mem Pgm b hAtS st hpc rfl h9 h14
      h0 h2 h3 h4 hpay
    rw [← hb1end] at h
    exact h
  refine Sem.monoA (Sem.seqA (Q₂ := fun k1 k2 s' =>
      k1 ≤ (Stmt.code decScanInit).len + (2 + 30 * (cr23D N * cr23M t)) ∧
      (k2 ≤ (Stmt.code decCandInit).len + (2 + 39 * cr23M t) +
          (1 + ((2 + (2 * t + 1) * (cr23D N * 10 + 24)) +
            ((Stmt.code decParInit).len + (2 + 12 * (2 * t + 1)) + decAdvance.length))) ∧
        ((∃ z' P' mst', DecHead1 N t C x z' (w / 4) (tag + 1) P' mst' s') ∧ s'.regs r9 = w / 4 ∧
          s'.pc = b6 ∧
          (∀ a, decOutBase N t ≤ a → s'.mem a = st.mem a)))) hscan ?_) ?_
  · intro k1 s1 hQ1
    obtain ⟨hk1, hInv1, hpc1⟩ := hQ1
    obtain ⟨hmaxAll, sstar, h4s, h3s⟩ := decScan_result' N t hN ht htN C z w st.mem s1 hInv1
    obtain ⟨hmem1, hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr10, hr11, hr12, hr9, hr14⟩ := hInv1
    have hmax : ∀ s' : Fin (cr23D N), (cr23OddB C (cr23Supp z) s').card ≤
        (cr23OddB C (cr23Supp z) sstar).card := by
      intro s'; rw [h3s]; exact hmaxAll s'
    have hcand := decCandStmtP_spec N t hN ht htN C z sstar tag st.mem Pgm b1 hAtC s1 hpc1
      hmem1 h4s hr14 h2 h3 h4 h8 h1 h9s h10s hsup (by omega) htaglt hpay
    rw [← hb2end] at hcand
    have hInner1 : Sem Pgm E b1 b6 s1
        (fun k s' => k ≤ (Stmt.code decCandInit).len + (2 + 39 * cr23M t) +
            (1 + ((2 + (2 * t + 1) * (cr23D N * 10 + 24)) +
              ((Stmt.code decParInit).len + (2 + 12 * (2 * t + 1)) + decAdvance.length))) ∧
          ((∃ z' P' mst', DecHead1 N t C x z' (w / 4) (tag + 1) P' mst' s') ∧ s'.regs r9 = w / 4 ∧
            s'.pc = b6 ∧
          (∀ a, decOutBase N t ≤ a → s'.mem a = st.mem a))) := by
      refine Sem.monoA (Sem.seqA (Q₂ := fun k2 k3 s' =>
          k2 ≤ (Stmt.code decCandInit).len + (2 + 39 * cr23M t) ∧
          (k3 ≤ 1 + ((2 + (2 * t + 1) * (cr23D N * 10 + 24)) +
              ((Stmt.code decParInit).len + (2 + 12 * (2 * t + 1)) + decAdvance.length)) ∧
            ((∃ z' P' mst', DecHead1 N t C x z' (w / 4) (tag + 1) P' mst' s') ∧ s'.regs r9 = w / 4 ∧
              s'.pc = b6 ∧
          (∀ a, decOutBase N t ≤ a → s'.mem a = st.mem a)))) hcand ?_) ?_
      · intro k2 s2 hQ2
        obtain ⟨hk2, ⟨len, l, hInvP, hFrame⟩, hpc2⟩ := hQ2
        have hci := decCandInvP_final N t C z sstar tag len l s2 hInvP
        obtain ⟨-, -, -, hciNodup, hciLen, hciEntries, -, -, hciSet⟩ := hci
        have hcle : len ≤ (cr23Supp z).card := decCandLen_le_wP N t hN ht C z sstar tag len l s2 hInvP
        have hInvP0 : DecCandInvP N t C z sstar tag (cr23M t) len l s2 := hInvP
        obtain ⟨hc0, hc2, hc3, hc4, hc7, hc8, hc10, hc11, hc12, hc14, hcList, hcNodup, hcLen,
          hcEntries, hcTagEq, hcTagLe, hcSet, hcPay, hcS1, hcS9, hcS10⟩ := hInvP
        have hreset : Sem Pgm E b2 b3 s2
            (fun k s' => k = 1 ∧ s' = runBlock [iImm r1 0] E s2) := by
          have h := Sem.blockA Pgm E b2 [iImm r1 0] s2 hAtR decReset1_noBranch hpc2
          simpa only [List.length_cons, List.length_nil] using h
        have hpc3 : (runBlock [iImm r1 0] E s2).pc = b3 := by
          rw [runBlock_pcA [iImm r1 0] E s2 decReset1_noBranch, hpc2]; rfl
        have h13mem : (runBlock [iImm r1 0] E s2).mem = s2.mem := (decReset1_spec E s2).2.1
        have hXorInv : DecXorInv N t C (cr23Sketch N t C z) l len 0
            (runBlock [iImm r1 0] E s2) :=
          decXorInv_of_cand N t hN ht htN C z sstar tag len l st.mem s2 hInvP0 hFrame h0 hpay
        have hlen2t : len ≤ 2 * t + 1 := by omega
        have hl2 : l.length ≤ 2 * t + 1 := by rw [← hcLen]; exact hlen2t
        have hxor := decXorStmt_specF N t hN htN C (cr23Sketch N t C z) l len Pgm b3 hAtX
          (runBlock [iImm r1 0] E s2) hpc3 hXorInv hlen2t
        rw [← hb4end] at hxor
        have hxc : 2 + len * (cr23D N * 10 + 24) ≤
            2 + (2 * t + 1) * (cr23D N * 10 + 24) := by
          have := Nat.mul_le_mul_right (cr23D N * 10 + 24) hlen2t
          omega
        have hInner2 : Sem Pgm E b2 b6 s2
            (fun k s' => k ≤ 1 + ((2 + (2 * t + 1) * (cr23D N * 10 + 24)) +
                ((Stmt.code decParInit).len + (2 + 12 * (2 * t + 1)) + decAdvance.length)) ∧
              ((∃ z' P' mst', DecHead1 N t C x z' (w / 4) (tag + 1) P' mst' s') ∧ s'.regs r9 = w / 4 ∧
                s'.pc = b6 ∧
          (∀ a, decOutBase N t ≤ a → s'.mem a = st.mem a))) := by
          refine Sem.monoA (Sem.seqA (Q₂ := fun k3 k4 s' => k3 = 1 ∧
              (k4 ≤ 2 + (2 * t + 1) * (cr23D N * 10 + 24) +
                  ((Stmt.code decParInit).len + (2 + 12 * (2 * t + 1)) + decAdvance.length) ∧
                ((∃ z' P' mst', DecHead1 N t C x z' (w / 4) (tag + 1) P' mst' s') ∧ s'.regs r9 = w / 4 ∧
                  s'.pc = b6 ∧
          (∀ a, decOutBase N t ≤ a → s'.mem a = st.mem a)))) hreset ?_) ?_
          · intro k3 s3 hQ3
            obtain ⟨hk3, rfl⟩ := hQ3
            have hInner3 : Sem Pgm E b3 b6 (runBlock [iImm r1 0] E s2)
                (fun k s' => k ≤ 2 + (2 * t + 1) * (cr23D N * 10 + 24) +
                    ((Stmt.code decParInit).len + (2 + 12 * (2 * t + 1)) + decAdvance.length) ∧
                  ((∃ z' P' mst', DecHead1 N t C x z' (w / 4) (tag + 1) P' mst' s') ∧ s'.regs r9 = w / 4 ∧
                    s'.pc = b6 ∧
          (∀ a, decOutBase N t ≤ a → s'.mem a = st.mem a))) := by
              refine Sem.monoA (Sem.seqA (Q₂ := fun k4 k5 s' =>
                  k4 ≤ 2 + (2 * t + 1) * (cr23D N * 10 + 24) ∧
                  (k5 ≤ (Stmt.code decParInit).len + (2 + 12 * (2 * t + 1)) + decAdvance.length ∧
                    ((∃ z' P' mst', DecHead1 N t C x z' (w / 4) (tag + 1) P' mst' s') ∧ s'.regs r9 = w / 4 ∧
                      s'.pc = b6 ∧
          (∀ a, decOutBase N t ≤ a → s'.mem a = st.mem a)))) hxor ?_) ?_
              · intro k4 s4 hQ4
                obtain ⟨hk4, hXI, hXF, hpc4⟩ := hQ4
                set S : ℕ → Finset ℕ := decParSet P l with hSdef
                have hS0 : S 0 = P := by rw [hSdef]; exact decParFamily_zero P l
                have hSstep : ∀ j, j < l.length → S (j + 1) = decSymm (S j) {l.getD j 0} :=
                  decParFamily hcNodup P
                have hSlen : S l.length = decSymm P l.toFinset := by
                  rw [hSdef]; simp only [decParSet, List.take_length]
                have hsl9 : s4.mem (decSlot N t 9) = decCandBase N t := by
                  rw [hXF _ (decWordsOf_le_slot N t hN 9), h13mem]
                  rw [hFrame _ (Or.inl (decSlot_lt_candBase N t (k := 9) (by norm_num)))]
                  exact h9s
                have hsl11 : s4.mem (decSlot N t 11) = decMstBase N t := by
                  rw [hXF _ (decWordsOf_le_slot N t hN 11), h13mem]
                  rw [hFrame _ (Or.inl (decSlot_lt_candBase N t (k := 11) (by norm_num)))]
                  exact h11s
                have hsl12 : s4.mem (decSlot N t 12) = decParBase N t := by
                  rw [hXF _ (decWordsOf_le_slot N t hN 12), h13mem]
                  rw [hFrame _ (Or.inl (decSlot_lt_candBase N t (k := 12) (by norm_num)))]
                  exact h12s
                have hsl14 : s4.mem (decSlot N t 14) = mst.length := by
                  rw [hXF _ (decWordsOf_le_slot N t hN 14), h13mem]
                  rw [hFrame _ (Or.inl (decSlot_lt_candBase N t (k := 14) (by norm_num)))]
                  exact h14s
                have hmst4 : ∀ i, i < mst.length → s4.mem (decMstBase N t + i) = mst.getD i 0 := by
                  intro i hi
                  rw [hXF _ (le_trans (decWordsOf_le_mstBase N t hN) (by omega)), h13mem]
                  rw [hFrame _ (Or.inr (by simp only [decMstBase, decTagBase]; omega))]
                  exact hmst i hi
                have hpar04 : ∀ v, v < 2 ^ (cr23Lb N + 1) →
                    s4.mem (decParBase N t + v) = if v ∈ S 0 then 1 else 0 := by
                  intro v hv
                  rw [hS0]
                  rw [hXF _ (le_trans (decWordsOf_le_parBase N t hN) (by omega)), h13mem]
                  rw [hFrame _ (Or.inr (by simp only [decMstBase, decParBase]; omega))]
                  exact decDataN_par_if N t C z w tag mst.length P mst st hDp hpar1 v hv
                have hcapP : mst.length + l.length ≤ 2 * t + 1 := by
                  have h1 : l.length ≤ w := by
                    rw [← hcLen]
                    exact le_trans hcle hcard
                  omega
                have hpar := decParStmt_specF_r14 N t hN htN E hEW S l mst mst.length s4.mem Pgm b4 hAtP s4 hpc4
                  hXI.2.2.1 (by rw [hXI.2.1, hcLen])
                  (fun i hi => hXI.2.2.2.2.2.1 i (by omega))
                  (fun _ _ => rfl) hsl9 hsl11 hsl12 hsl14 hmst4
                  hcapP hcEntries hSstep hpar04 (fun _ _ => rfl)
                rw [← hb5end] at hpar
                have hInner4 : Sem Pgm E b4 b6 s4
                    (fun k s' => k ≤ (Stmt.code decParInit).len + (2 + 12 * (2 * t + 1))
                        + decAdvance.length ∧
                      ((∃ z' P' mst', DecHead1 N t C x z' (w / 4) (tag + 1) P' mst' s') ∧ s'.regs r9 = w / 4 ∧
                        s'.pc = b6 ∧
          (∀ a, decOutBase N t ≤ a → s'.mem a = st.mem a))) := by
                  refine Sem.monoA (Sem.seqA (Q₂ := fun k5 k6 s' =>
                      k5 ≤ (Stmt.code decParInit).len + (2 + 12 * (2 * t + 1)) ∧
                      (k6 ≤ decAdvance.length ∧
                        ((∃ z' P' mst', DecHead1 N t C x z' (w / 4) (tag + 1) P' mst' s') ∧ s'.regs r9 = w / 4 ∧
                          s'.pc = b6 ∧
          (∀ a, decOutBase N t ≤ a → s'.mem a = st.mem a)))) hpar ?_) ?_
                  · intro k5 s5 hQ5
                    obtain ⟨hk5, hPI, hpc5', h14s5'⟩ := hQ5
                    obtain ⟨hp0, hp1, hp4, hp5, hp6, hp7, hpcand5, hppar5, hpbelow, hpmst5, hpnew5, hframe5⟩ := hPI
                    have hs5_7 : s5.mem (decSlot N t 7) = w := by
                      rw [hpbelow _ (decSlot_lt_mstBase N t (by norm_num))]
                      rw [hXF _ (decWordsOf_le_slot N t hN 7), h13mem]
                      rw [hFrame _ (Or.inl (decSlot_lt_candBase N t (k := 7) (by norm_num)))]
                      exact h7
                    have hs5_8 : s5.mem (decSlot N t 8) = tag := by
                      rw [hpbelow _ (decSlot_lt_mstBase N t (by norm_num))]
                      rw [hXF _ (decWordsOf_le_slot N t hN 8), h13mem]
                      rw [hFrame _ (Or.inl (decSlot_lt_candBase N t (k := 8) (by norm_num)))]
                      exact h8
                    have hs5_14 : s5.mem (decSlot N t 14) = mst.length := by
                      rw [hpbelow _ (decSlot_lt_mstBase N t (by norm_num))]
                      rw [hXF _ (decWordsOf_le_slot N t hN 14), h13mem]
                      rw [hFrame _ (Or.inl (decSlot_lt_candBase N t (k := 14) (by norm_num)))]
                      exact h14s
                    have h1lt : s5.regs r1 < 2 ^ cr23Word N := by
                      rw [hp1]; exact lt_of_le_of_lt (by omega) h2tW
                    have h14vlt : s5.mem (decSlot N t 14) + s5.regs r1 < 2 ^ cr23Word N := by
                      rw [hs5_14, hp1]; exact lt_of_le_of_lt hcapP h2tW
                    have hAdv := decAdvance_data N t hN htN C s5 h14s5'
                      (by rw [hs5_7]; exact hwW)
                      (by rw [hs5_8]; exact htagW)
                      h14vlt h1lt
                    have hadv : Sem Pgm E b5 b6 s5
                        (fun k s' => k = decAdvance.length ∧ s' = runBlock decAdvance E s5) := by
                      have h := Sem.blockA Pgm E b5 decAdvance s5 hAtA decAdvance_noBranch hpc5'
                      simpa using h
                    have hres := cr23_round_residual N t hN C z l hcNodup hcEntries sstar hciSet
                    have hshrink := cr23_shrink_argmax C hexp heps (cr23Supp z) hsup (cr23D_pos N hN) sstar hmax
                    have hcard' : (cr23Supp (z + decLstVec N l l.length)).card ≤ w / 4 := by
                      have h1 : 4 * (cr23Supp (z + decLstVec N l l.length)).card ≤ (cr23Supp z).card := by
                        rw [hres.2]; exact hshrink
                      have h2 : 4 * (cr23Supp (z + decLstVec N l l.length)).card ≤ w := le_trans h1 hcard
                      exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).mpr (by omega)
                    have hcap' : (mst ++ l).length + 2 * (w / 4) ≤ 2 * t + 1 := by
                      rw [List.length_append]
                      have hlw : l.length ≤ w := by
                        rw [← hcLen]
                        exact le_trans hcle hcard
                      have hdiv : 2 * (w / 4) ≤ w := by
                        have h4 := Nat.div_mul_le_self w 4
                        omega
                      omega
                    have hsub' : ∀ v ∈ decSymm P l.toFinset, v ∈ mst ++ l := by
                      intro v hv
                      rw [decSymm, Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff] at hv
                      rcases hv with ⟨hvP, -⟩ | ⟨hvl, -⟩
                      · exact List.mem_append.mpr (Or.inl (hsub v hvP))
                      · exact List.mem_append.mpr (Or.inr (List.mem_toFinset.mp hvl))
                    have hP' : decSymm P l.toFinset
                        = cr23NumSet (cr23Supp (x + (z + decLstVec N l l.length))) :=
                      cr23Parity_step hN x z l P hcNodup hcEntries hP
                    have hslot : ∀ k, k < 15 → k ≠ 7 → k ≠ 8 → k ≠ 14 →
                        (runBlock decAdvance E s5).mem (decSlot N t k) = st.mem (decSlot N t k) := by
                      intro k hk h7' h8' h14'
                      rw [hAdv.2.2.2.1 _ (decSlot_ne N t k 7 h7') (decSlot_ne N t k 8 h8')
                        (decSlot_ne N t k 14 h14')]
                      rw [hpbelow _ (decSlot_lt_mstBase N t hk)]
                      rw [hXF _ (decWordsOf_le_slot N t hN k), h13mem]
                      rw [hFrame _ (Or.inl (decSlot_lt_candBase N t hk))]
                    have hmem6 : ∀ a, a < wordsOf (cr23Word N) (cr23R N t) →
                        (runBlock decAdvance E s5).mem a
                          = packMem (cr23Word N) (cr23Sketch N t C (z + decLstVec N l l.length)) a := by
                      intro a ha
                      rw [hAdv.2.2.2.1 a
                        (decSlot_ne_lt N t 7 a ha hN) (decSlot_ne_lt N t 8 a ha hN)
                        (decSlot_ne_lt N t 14 a ha hN)]
                      rw [hpbelow a (by have h1 := cr23_wordsOf_le_frame N t hN; simp only [decMstBase, decTagBase, decCandBase] at h1 ⊢; omega)]
                      rw [hXI.2.2.2.2.2.2.2 a ha]
                      rw [hres.1, hcLen]
                    have htag6 : ∀ v, v < 2 ^ (cr23Lb N + 1) →
                        (runBlock decAdvance E s5).mem (decTagBase N t + v) < tag + 1 := by
                      intro v hv
                      rw [hAdv.2.2.2.1 (decTagBase N t + v)
                        (decSlot_ne_ge N t 7 (decTagBase N t + v) (by norm_num) (by simp only [decTagBase, decCandBase]; omega))
                        (decSlot_ne_ge N t 8 (decTagBase N t + v) (by norm_num) (by simp only [decTagBase, decCandBase]; omega))
                        (decSlot_ne_ge N t 14 (decTagBase N t + v) (by norm_num) (by simp only [decTagBase, decCandBase]; omega))]
                      rw [hpbelow _ (by simp only [decMstBase]; omega)]
                      rw [hXF _ (le_trans (decWordsOf_le_tagBase N t hN) (by omega)), h13mem]
                      have h := hcTagLe v hv
                      omega
                    have hpar6 : ∀ v, v < 2 ^ (cr23Lb N + 1) →
                        ((runBlock decAdvance E s5).mem (decParBase N t + v) = 1
                          ↔ v ∈ decSymm P l.toFinset) := by
                      intro v hv
                      rw [hAdv.2.2.2.1 (decParBase N t + v)
                        (decSlot_ne_ge N t 7 (decParBase N t + v) (by norm_num) (by simp only [decParBase, decTagBase, decCandBase, decMstBase]; omega))
                        (decSlot_ne_ge N t 8 (decParBase N t + v) (by norm_num) (by simp only [decParBase, decTagBase, decCandBase, decMstBase]; omega))
                        (decSlot_ne_ge N t 14 (decParBase N t + v) (by norm_num) (by simp only [decParBase, decTagBase, decCandBase, decMstBase]; omega))]
                      rw [hppar5 v hv, hSlen]
                      by_cases hvP : v ∈ decSymm P l.toFinset <;> simp [hvP]
                    have hpar6le : ∀ v, v < 2 ^ (cr23Lb N + 1) →
                        (runBlock decAdvance E s5).mem (decParBase N t + v) ≤ 1 := by
                      intro v hv
                      rw [hAdv.2.2.2.1 (decParBase N t + v)
                        (decSlot_ne_ge N t 7 (decParBase N t + v) (by norm_num) (by simp only [decParBase, decTagBase, decCandBase, decMstBase]; omega))
                        (decSlot_ne_ge N t 8 (decParBase N t + v) (by norm_num) (by simp only [decParBase, decTagBase, decCandBase, decMstBase]; omega))
                        (decSlot_ne_ge N t 14 (decParBase N t + v) (by norm_num) (by simp only [decParBase, decTagBase, decCandBase, decMstBase]; omega))]
                      rw [hppar5 v hv, hSlen]
                      by_cases hvP : v ∈ decSymm P l.toFinset <;> simp [hvP]
                    have hmst6 : ∀ i, i < (mst ++ l).length →
                        (runBlock decAdvance E s5).mem (decMstBase N t + i) = (mst ++ l).getD i 0 := by
                      intro i hi
                      rw [hAdv.2.2.2.1 (decMstBase N t + i)
                        (decSlot_ne_ge N t 7 (decMstBase N t + i) (by norm_num) (by simp only [decMstBase, decTagBase, decCandBase]; omega))
                        (decSlot_ne_ge N t 8 (decMstBase N t + i) (by norm_num) (by simp only [decMstBase, decTagBase, decCandBase]; omega))
                        (decSlot_ne_ge N t 14 (decMstBase N t + i) (by norm_num) (by simp only [decMstBase, decTagBase, decCandBase]; omega))]
                      exact dec_mst_concat s5.mem (decMstBase N t) mst l hpmst5 (fun k hk => by rw [← Nat.add_assoc]; exact hpnew5 k hk) i hi
                    have hmst6N : ∀ v, v ∈ mst ++ l → v < N := by
                      intro v hv
                      rw [List.mem_append] at hv
                      rcases hv with hv | hv
                      · exact hmstN v hv
                      · exact hcEntries v hv
                    have hHead1 : DecHead1 N t C x (z + decLstVec N l l.length) (w / 4) (tag + 1)
                        (decSymm P l.toFinset) (mst ++ l) (runBlock decAdvance E s5) := by
                      refine ⟨⟨?_, hAdv.2.2.2.2.2, hP', hsub', hcap', hcard'⟩, hmst6N, hpar6le⟩
                      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmem6, htag6,
                        hpar6, hmst6⟩
                      · rw [hslot 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact h0
                      · rw [hslot 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact h1
                      · rw [hslot 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact h2
                      · rw [hslot 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact h3
                      · rw [hslot 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact h4
                      · rw [hslot 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact h5
                      · rw [hslot 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact h6
                      · rw [hAdv.1, hs5_7]
                      · rw [hAdv.2.1, hs5_8]
                      · rw [hslot 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact h9s
                      · rw [hslot 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact h10s
                      · rw [hslot 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact h11s
                      · rw [hslot 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact h12s
                      · rw [hslot 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact h13s
                      · rw [hAdv.2.2.1, hs5_14, hp1, List.length_append]
                    have hpc6 : (runBlock decAdvance E s5).pc = b6 := by
                      rw [runBlock_pcA decAdvance E s5 decAdvance_noBranch, hpc5']
                    have hframe6 : ∀ a, decOutBase N t ≤ a →
                        (runBlock decAdvance E s5).mem a = st.mem a := by
                      intro a ha
                      have hw : wordsOf (cr23Word N) (cr23R N t) ≤ a :=
                        le_trans (cr23_wordsOf_le_frame N t hN)
                          (le_trans (decFrame_le_parBase N t)
                            (le_trans (decParBase_le_outBase N t) ha))
                      have hmst : decMstBase N t ≤ a :=
                        le_trans (decMstBase_le_parBase N t)
                          (le_trans (decParBase_le_outBase N t) ha)
                      rw [hAdv.2.2.2.1 a
                        (ne_of_gt (lt_of_lt_of_le (decSlot_lt_mstBase N t (by norm_num)) hmst))
                        (ne_of_gt (lt_of_lt_of_le (decSlot_lt_mstBase N t (by norm_num)) hmst))
                        (ne_of_gt (lt_of_lt_of_le (decSlot_lt_mstBase N t (by norm_num)) hmst)),
                        hframe5 a ha, hXF a hw, h13mem, hFrame a (Or.inr hmst)]
                    have hInner5 : Sem Pgm E b5 b6 s5
                        (fun k s' => k ≤ decAdvance.length ∧
                          ((∃ z' P' mst', DecHead1 N t C x z' (w / 4) (tag + 1) P' mst' s') ∧ s'.regs r9 = w / 4 ∧
                            s'.pc = b6 ∧
          (∀ a, decOutBase N t ≤ a → s'.mem a = st.mem a))) := by
                      have hr9 : (runBlock decAdvance E s5).regs r9 = w / 4 := by
                        rw [hAdv.2.2.2.2.1, hs5_7]
                      refine Sem.monoA hadv (fun k s' hk => ?_)
                      obtain ⟨rfl, rfl⟩ := hk
                      exact ⟨le_rfl, ⟨_, _, _, hHead1⟩, hr9, hpc6, hframe6⟩
                    exact Sem.monoA hInner5 (fun k s' h => ⟨by have h12 := Nat.mul_le_mul_left 12 hl2; omega, h⟩)
                  · intro k s' h
                    obtain ⟨k5, k6, hk, h1, h2, h3⟩ := h
                    exact ⟨by omega, h3⟩
                exact Sem.monoA hInner4 (fun k s' h => ⟨le_trans hk4 hxc, h⟩)
              · intro k s' h
                obtain ⟨k4, k5, hk, h1, h2, h3⟩ := h
                exact ⟨by omega, h3⟩
            exact Sem.monoA hInner3 (fun k s' h => ⟨hk3, h⟩)
          · intro k s' h
            obtain ⟨k3, k4, hk, h1, h2, h3⟩ := h
            exact ⟨by omega, h3⟩
        exact Sem.monoA hInner2 (fun k s' h => ⟨hk2, h⟩)
      · intro k s' h
        obtain ⟨k2, k3, hk, h1, h2, h3⟩ := h
        exact ⟨by omega, h3⟩
    exact Sem.monoA hInner1 (fun k s' h => ⟨hk1, h⟩)
  · intro k s' h
    obtain ⟨k1, k2, hk, h1, h2, h3⟩ := h
    have hcost : decRoundCost N t
        = ((Stmt.code decScanInit).len + (2 + 30 * (cr23D N * cr23M t))) +
          ((Stmt.code decCandInit).len + (2 + 39 * cr23M t) +
            (1 + ((2 + (2 * t + 1) * (cr23D N * 10 + 24)) +
              ((Stmt.code decParInit).len + (2 + 12 * (2 * t + 1)) + decAdvance.length)))) := rfl
    refine ⟨?_, h3⟩
    rw [hcost]; omega


-- ===== loopF.lean =====


/-- **The round loop**: `Nat.clog 4 (t+1)` rounds, then the failing test on `r9 = w = 0`. -/
theorem decRoundStmt_specF (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2) (eps : ℝ)
    (hexp : IsLayeredExpander C (2 * t) eps) (heps : 16 * eps ≤ 1)
    (Pgm : Program) (a : ℕ) (hAt : At Pgm a (Stmt.compile decRoundStmt a))
    (st : RAMState) (hpc : st.pc = a)
    (hR : DecHead1 N t C x x t 1 ∅ [] st) (h9 : st.regs r9 = t) :
    Sem Pgm (detEnv (cr23Word N) (cr23DecDet N t C)) a
      (a + decRoundBody.len + 2) st
      (fun k s' => k ≤ 1 + Nat.clog 4 (t + 1) * (decRoundCost N t + 2) ∧
        DecLoopInv N t C x (Nat.clog 4 (t + 1)) s' ∧
        s'.pc = a + decRoundBody.len + 2 ∧
        (∀ x, decOutBase N t ≤ x → s'.mem x = st.mem x)) := by
  set E : RAMEnv := detEnv (cr23Word N) (cr23DecDet N t C) with hE
  set n : ℕ := Nat.clog 4 (t + 1) with hn
  have hW : 1 < 2 ^ E.W := by rw [hE]; exact cr23_one_lt_word N hN
  have hnL : n ≤ cr23Lb N := by
    rw [hn, Nat.clog_le_iff_le_pow (by norm_num : 1 < 4)]
    calc t + 1 ≤ N + 1 := by omega
      _ ≤ 2 ^ cr23Lb N := Nat.le_pow_clog (by norm_num : 1 < 2) (N + 1)
      _ ≤ 4 ^ cr23Lb N := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpcirr : ∀ (j : ℕ) (s : RAMState) (p : ℕ),
      (DecLoopInv N t C x j s ∧ (∀ x, decOutBase N t ≤ x → s.mem x = st.mem x)) →
      (DecLoopInv N t C x j { s with pc := p } ∧
        (∀ x, decOutBase N t ≤ x → { s with pc := p }.mem x = st.mem x)) := by
    intro j s p h
    obtain ⟨⟨z, P, mst, hH, h9'⟩, hfr⟩ := h
    exact ⟨⟨z, P, mst, hH, h9'⟩, hfr⟩
  have hgo : ∀ j, j < n → ∀ s,
      (DecLoopInv N t C x j s ∧ (∀ x, decOutBase N t ≤ x → s.mem x = st.mem x)) →
      s.regs r9 ≠ 0 := by
    intro j hj s h
    obtain ⟨⟨z, P, mst, hH, h9'⟩, -⟩ := h
    rw [h9']
    have hpow : ¬ (t + 1 ≤ 4 ^ j) := by
      intro hp
      have h1 : Nat.clog 4 (t + 1) ≤ j :=
        (Nat.clog_le_iff_le_pow (by norm_num : 1 < 4)).mpr hp
      rw [← hn] at h1
      omega
    have h4j : 4 ^ j ≤ t := by omega
    exact Nat.pos_iff_ne_zero.mp (Nat.div_pos h4j (pow_pos (by norm_num) j))
  have hstop : ∀ s,
      (DecLoopInv N t C x n s ∧ (∀ x, decOutBase N t ≤ x → s.mem x = st.mem x)) →
      s.regs r9 = 0 := by
    intro s h
    obtain ⟨⟨z, P, mst, hH, h9'⟩, -⟩ := h
    rw [h9']
    apply Nat.div_eq_of_lt
    have hlt : t < 4 ^ n := by
      have h := Nat.le_pow_clog (b := 4) (by norm_num : 1 < 4) (t + 1)
      rw [← hn] at h
      omega
    omega
  have hstep : ∀ j, j < n → ∀ s, s.pc = a →
      (DecLoopInv N t C x j s ∧ (∀ x, decOutBase N t ≤ x → s.mem x = st.mem x)) →
      Sem Pgm E (a + (Cond.neqz r9).code.length + 1) a
        { runBlock (Cond.neqz r9).code E s with pc := a + (Cond.neqz r9).code.length + 1 }
        (fun k s' => k ≤ decRoundCost N t + 1 ∧
          (DecLoopInv N t C x (j + 1) s' ∧ (∀ x, decOutBase N t ≤ x → s'.mem x = st.mem x)) ∧
          s'.pc = a) := by
    intro j hj s hp hRj
    obtain ⟨⟨z, P, mst, hHead, h9eq⟩, hfrj⟩ := hRj
    obtain ⟨-, -, hAtBody, hjmp⟩ := at_loopA hAt
    have hsup : (cr23Supp z).card ≤ t := by
      obtain ⟨hD, -⟩ := hHead
      obtain ⟨-, -, -, -, hcap, hcard⟩ := hD
      have hdw : t / 4 ^ j ≤ t := Nat.div_le_self _ _
      omega
    have hwW : t / 4 ^ j < 2 ^ cr23Word N :=
      lt_of_le_of_lt (Nat.div_le_self _ _) (lt_of_le_of_lt htN (cr23N_lt_word N hN))
    have htagW : (1 + j) + 1 < 2 ^ cr23Word N := by
      have h1 : 1 + j + 1 ≤ cr23Lb N + 1 := by omega
      exact lt_of_le_of_lt h1 (cr23_lb1_lt_word N hN)
    have h2tW : 2 * t + 1 < 2 ^ cr23Word N := dec_two_t_lt_word N t hN htN
    refine Sem.jmp_appendA hjmp ?_
    refine Sem.monoA (decRoundBody_specF N t hN ht htN C x z (t / 4 ^ j) (1 + j) P mst eps hexp
      heps Pgm (a + (Cond.neqz r9).code.length + 1) hAtBody
      { runBlock (Cond.neqz r9).code E s with pc := a + (Cond.neqz r9).code.length + 1 }
      rfl hHead h9eq hwW htagW h2tW) ?_
    intro k s' h
    obtain ⟨hk, ⟨z', P', mst', hHead'⟩, hr9, hpc6, hbodyfr⟩ := h
    have hw' : (t / 4 ^ j) / 4 = t / 4 ^ (j + 1) := by
      rw [Nat.div_div_eq_div_mul, ← pow_succ]
    have ht' : 1 + j + 1 = 1 + (j + 1) := by omega
    rw [hw', ht'] at hHead'
    rw [hw'] at hr9
    exact ⟨by omega, ⟨⟨z', P', mst', hHead', hr9⟩,
      fun x hx => by rw [hbodyfr x hx]; exact hfrj x hx⟩, rfl⟩
  have hR0 : DecLoopInv N t C x 0 st ∧ (∀ x, decOutBase N t ≤ x → st.mem x = st.mem x) := by
    refine ⟨⟨x, ∅, [], ?_, ?_⟩, fun _ _ => rfl⟩
    · simpa only [pow_zero, Nat.div_one, Nat.add_zero] using hR
    · simpa only [pow_zero, Nat.div_one] using h9
  have hloop := Sem.loopPredLe_neqz Pgm E a r9 decRoundBody hAt hW n
    (fun j s => DecLoopInv N t C x j s ∧ (∀ x, decOutBase N t ≤ x → s.mem x = st.mem x))
    (fun _ => decRoundCost N t + 1) hpcirr hgo hstop hstep st hpc hR0
  refine Sem.monoA hloop ?_
  intro k s' h
  obtain ⟨hk, ⟨hInv, hfr⟩, hpc'⟩ := h
  have hsum : (∑ j ∈ Finset.range n, ((Cond.neqz r9).code.length + 1 + (decRoundCost N t + 1)))
      = n * (decRoundCost N t + 2) := by
    have hcl : (Cond.neqz r9).code.length = 0 := rfl
    rw [hcl]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    simp only [Nat.cast_id]
    ring
  have hk' : k ≤ 1 + n * (decRoundCost N t + 2) := by
    rw [hsum] at hk
    have hcl2 : (Cond.neqz r9).code.length = 0 := rfl
    rw [hcl2] at hk
    omega
  exact ⟨hk', hInv, hpc', hfr⟩

/-- The prologue with the frame above the output window. -/
theorem decPrologue_specF (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2)
    (hsup : (cr23Supp x).card ≤ t) (Pgm : Program) (hAt : At Pgm 0 progDecPre)
    (st : RAMState) (hpc : st.pc = 0) (h0 : st.regs r0 = 0)
    (hpay : ∀ a, a < wordsOf (cr23Word N) (cr23R N t) →
      st.mem a = packMem (cr23Word N) (cr23Sketch N t C x) a)
    (hzero : ∀ a, wordsOf (cr23Word N) (cr23R N t) ≤ a → a < decZeroBound N t → st.mem a = 0) :
    Sem Pgm (detEnv (cr23Word N) (cr23DecDet N t C)) 0 progDecPre.length st
      (fun k s' => k = progDecPre.length ∧ DecHead1 N t C x x t 1 ∅ [] s' ∧
        s'.regs r14 = cr23DecFrame N t ∧
        (∀ a, decEmFrame N t ≤ a → s'.mem a = st.mem a)) := by
  refine Sem.monoA (Sem.blockA Pgm (detEnv (cr23Word N) (cr23DecDet N t C)) 0 progDecPre st hAt
    progDecPre_noBranch hpc) ?_
  rintro k s' ⟨rfl, rfl⟩
  refine ⟨rfl, decPrologueDecHeadZ N t hN htN C x hsup st h0 hpay hzero,
    decPreState_regs14 N t hN htN C st h0, ?_⟩
  intro a ha
  exact decPreState_mem_out N t hN htN C st h0 (fun k hk => by
    have h1 : decSlot N t k < decCandBase N t := decSlot_lt_candBase N t hk
    have h2 : decCandBase N t ≤ decTagBase N t := decCandBase_le_tagBase N t
    have h3 : decTagBase N t ≤ decMstBase N t := decTagBase_le_mstBase N t
    have h4 : decMstBase N t ≤ decParBase N t := decMstBase_le_parBase N t
    have h5 : decParBase N t < decOutBase N t := by
      simp only [decOutBase]
      exact Nat.lt_add_of_pos_right (Nat.two_pow_pos _)
    have h6 : decOutBase N t ≤ decEmFrame N t := by
      simp only [decEmFrame]
      exact Nat.le_add_right _ _
    exact ne_of_gt (lt_of_lt_of_le
      (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1 h2) h3) h4) (le_of_lt h5))
      (le_trans h6 ha)))


-- ===== engineF.lean =====


/-- **The decoder's frame run**: from the finite-zero window, the decoder reaches the end of
`decStmt` and writes nothing at or above `decEmFrame N t = decOutBase N t + (2t+1)`. -/
theorem decStmt_frameSem (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2) (eps : ℝ)
    (hexp : IsLayeredExpander C (2 * t) eps) (heps : 16 * eps ≤ 1)
    (hsup : (cr23Supp x).card ≤ t)
    (Pgm : Program) (hAt : At Pgm 0 (Stmt.compile decStmt 0))
    (st : RAMState) (hpc : st.pc = 0) (h0 : st.regs r0 = 0)
    (hpay : ∀ a, a < wordsOf (cr23Word N) (cr23R N t) →
      st.mem a = packMem (cr23Word N) (cr23Sketch N t C x) a)
    (hzero : ∀ a, wordsOf (cr23Word N) (cr23R N t) ≤ a → a < decZeroBound N t →
      st.mem a = 0) :
    Sem Pgm (detEnv (cr23Word N) (cr23DecDet N t C)) 0 decStmt.len st
      (fun k s' => k ≤ decStmtCost N t ∧
        (∀ a, decEmFrame N t ≤ a → s'.mem a = st.mem a)) := by
  set E : RAMEnv := detEnv (cr23Word N) (cr23DecDet N t C) with hE
  set n : ℕ := Nat.clog 4 (t + 1) with hn
  -- the compile, peeled one `Stmt.compile` step at a time
  have h1 : At Pgm 0 (Stmt.compile decStmt 0) := hAt
  rw [decStmt_eq1] at h1
  obtain ⟨hAtC0, h1⟩ := At.append.mp h1
  simp only [Stmt.length_compile, Stmt.len, progDecPreC_len, Nat.zero_add] at h1
  obtain ⟨hAtS0, h1⟩ := At.append.mp h1
  simp only [Stmt.length_compile, Stmt.len, progDecPreS_len, Nat.zero_add] at h1
  obtain ⟨hAtL0, h1⟩ := At.append.mp h1
  simp only [Stmt.length_compile, Stmt.len, decLoadW_len, Nat.zero_add] at h1
  obtain ⟨hAtR, hAtE0⟩ := At.append.mp h1
  have hAtC : At Pgm 0 progDecPreC := hAtC0
  have hAtS : At Pgm 22 progDecPreS := hAtS0
  have hAtL63 : At Pgm 63 decLoadW := hAtL0
  have hAtPre : At Pgm 0 progDecPre := by
    rw [progDecPre]
    exact At.append.mpr ⟨hAtC, hAtS⟩
  have hpre : progDecPre.length = 63 := progDecPre_len
  have hAtE : At Pgm (66 + decRoundBody.len + 2)
      (Stmt.compile decEmitStmt (66 + decRoundBody.len + 2)) := by
    have h := hAtE0
    simp only [Stmt.length_compile, decRoundStmt_len_form, Nat.zero_add] at h
    exact h
  have hW1 : 1 < 2 ^ E.W := by rw [hE]; exact cr23_one_lt_word N hN
  have hF8 : cr23DecFrame N t + 8 < 2 ^ E.W := by
    rw [hE]; exact dec_frame_add_lt_word N t hN htN (by norm_num)
  have htW : t < 2 ^ E.W := by
    rw [hE]; exact lt_of_le_of_lt htN (cr23N_lt_word N hN)
  -- leg 1: the prologue (with its frame)
  have hProl : Sem Pgm E 0 63 st
      (fun k s' => (k = 63 ∧ DecHead1 N t C x x t 1 ∅ [] s' ∧
        s'.regs r14 = cr23DecFrame N t ∧
        (∀ a, decEmFrame N t ≤ a → s'.mem a = st.mem a)) ∧ s'.pc = 63) := by
    have h := decPrologue_specF N t hN htN C x hsup Pgm hAtPre st hpc h0 hpay hzero
    rw [hpre] at h
    exact Sem.add_pc h
  -- leg 2: the counter reload (memory is untouched)
  have hL2 : ∀ (s1 : RAMState), s1.pc = 63 → DecHead1 N t C x x t 1 ∅ [] s1 →
      s1.regs r14 = cr23DecFrame N t →
      (∀ a, decEmFrame N t ≤ a → s1.mem a = st.mem a) →
      Sem Pgm E 63 66 s1
        (fun k s' => k = decLoadW.length ∧ DecHead1 N t C x x t 1 ∅ [] s' ∧
          s'.regs r9 = t ∧ s'.pc = 66 ∧
          (∀ a, decEmFrame N t ≤ a → s'.mem a = st.mem a)) := by
    intro s1 hpc1 hH1 h141 hfr1
    have hblk := Sem.block Pgm E 63 decLoadW s1 hAtL63 decLoadW_noBranch hpc1
    have hspec := decLoadW_spec E s1 (cr23DecFrame N t) hW1 h141 hF8
    obtain ⟨h9, hmem, hpc3, hframe⟩ := hspec
    have h7 : s1.mem (cr23DecFrame N t + 8) = t := by
      obtain ⟨hD0, -, -⟩ := hH1
      obtain ⟨hD1, -, -, -, -, -⟩ := hD0
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
        a19⟩ := hD1
      have h := a8
      rwa [decSlot_seven] at h
    have h9' : (runBlock decLoadW E s1).regs r9 = t := by
      rw [h9, h7, Nat.mod_eq_of_lt htW]
    have hH1' : DecHead1 N t C x x t 1 ∅ [] (runBlock decLoadW E s1) :=
      DecHead1_congr hmem.symm (hframe r14 (by decide) (by decide)).symm hH1
    refine Sem.mono hblk (fun k s' hh => ?_)
    obtain ⟨hk, rfl⟩ := hh
    exact ⟨hk, hH1', h9', by rw [hpc3, hpc1], by intro a ha; rw [hmem]; exact hfr1 a ha⟩
  -- leg 3: the round loop
  have hL3 : ∀ (s2 : RAMState), s2.pc = 66 → DecHead1 N t C x x t 1 ∅ [] s2 →
      s2.regs r9 = t →
      (∀ a, decEmFrame N t ≤ a → s2.mem a = st.mem a) →
      Sem Pgm E 66 (66 + decRoundBody.len + 2) s2
        (fun k s' => k ≤ 1 + n * (decRoundCost N t + 2) ∧
          DecLoopInv N t C x n s' ∧ s'.pc = (66 + decRoundBody.len + 2) ∧
          (∀ a, decEmFrame N t ≤ a → s'.mem a = st.mem a)) := by
    intro s2 hpc2 hH2 h92 hfr2
    refine Sem.monoA (decRoundStmt_specF N t hN ht htN C x eps hexp heps Pgm 66 hAtR s2 hpc2
      hH2 h92) (fun k s' h => ⟨h.1, h.2.1, h.2.2.1, ?_⟩)
    intro a ha
    rw [h.2.2.2 a (le_trans (by simp only [decEmFrame]; exact Nat.le_add_right _ _) ha)]
    exact hfr2 a ha
  -- leg 4: the emit pass
  have hw0 : t / 4 ^ n = 0 := by
    rw [hn]
    refine Nat.div_eq_of_lt ?_
    have h := Nat.le_pow_clog (b := 4) (by norm_num : 1 < 4) (t + 1)
    omega
  have hL4 : ∀ (s3 : RAMState), s3.pc = (66 + decRoundBody.len + 2) →
      DecLoopInv N t C x n s3 →
      (∀ a, decEmFrame N t ≤ a → s3.mem a = st.mem a) →
      Sem Pgm E (66 + decRoundBody.len + 2)
        (66 + decRoundBody.len + 2 + decEmitStmt.len) s3
        (fun k s' => k ≤ decEmitStmtCost N t ∧ OutputsSupport s' x ∧
          (∀ a, decEmFrame N t ≤ a → s'.mem a = st.mem a)) := by
    intro s3 hpc3 hInv hfr3
    obtain ⟨z, P, mst, hH3, -⟩ := hInv
    rw [hw0] at hH3
    have hH3' := hH3
    obtain ⟨⟨-, -, -, -, -, hwc⟩, -, -⟩ := hH3'
    have hK : cr23Supp z = ∅ := Finset.card_eq_zero.mp (by omega)
    refine Sem.monoA (decEmitStmt_specF N t hN htN C x z 0 (1 + n) P mst s3 Pgm
      (66 + decRoundBody.len + 2) hAtE hpc3 rfl hH3 hK) (fun k s' h => ⟨h.1, h.2.1, ?_⟩)
    intro a ha
    rw [h.2.2 a ha]
    exact hfr3 a ha
  -- 1 · 2
  have h12 : Sem Pgm E 0 66 st
      (fun k s' => k = 63 + decLoadW.length ∧ DecHead1 N t C x x t 1 ∅ [] s' ∧
        s'.regs r9 = t ∧ s'.pc = 66 ∧
        (∀ a, decEmFrame N t ≤ a → s'.mem a = st.mem a)) := by
    refine Sem.mono (Sem.seq (Q₁ := fun k1 s1 => (k1 = 63 ∧ DecHead1 N t C x x t 1 ∅ [] s1 ∧
        s1.regs r14 = cr23DecFrame N t ∧
        (∀ a, decEmFrame N t ≤ a → s1.mem a = st.mem a)) ∧ s1.pc = 63)
      (Q₂ := fun k1 k2 s' => k1 = 63 ∧ k2 = decLoadW.length ∧
        DecHead1 N t C x x t 1 ∅ [] s' ∧ s'.regs r9 = t ∧ s'.pc = 66 ∧
        (∀ a, decEmFrame N t ≤ a → s'.mem a = st.mem a)) hProl ?_) ?_
    · intro k1 s1 hQ1
      obtain ⟨⟨hk1, hH1, h141, hfr1⟩, hpc1⟩ := hQ1
      exact Sem.mono (hL2 s1 hpc1 hH1 h141 hfr1)
        (fun k s' hh => ⟨hk1, hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2⟩)
    · rintro k s' ⟨k1, k2, hk, h1, h2, h3, h4, h5, h6⟩
      exact ⟨by omega, h3, h4, h5, h6⟩
  -- (1 · 2) · 3
  have h123 : Sem Pgm E 0 (66 + decRoundBody.len + 2) st
      (fun k s' => k ≤ 63 + decLoadW.length + (1 + n * (decRoundCost N t + 2)) ∧
        DecLoopInv N t C x n s' ∧ s'.pc = (66 + decRoundBody.len + 2) ∧
        (∀ a, decEmFrame N t ≤ a → s'.mem a = st.mem a)) := by
    refine Sem.mono (Sem.seq (Q₁ := fun k1 s1 => k1 = 63 + decLoadW.length ∧
        DecHead1 N t C x x t 1 ∅ [] s1 ∧ s1.regs r9 = t ∧ s1.pc = 66 ∧
        (∀ a, decEmFrame N t ≤ a → s1.mem a = st.mem a))
      (Q₂ := fun k1 k2 s' => k1 = 63 + decLoadW.length ∧
        k2 ≤ 1 + n * (decRoundCost N t + 2) ∧ DecLoopInv N t C x n s' ∧
        s'.pc = (66 + decRoundBody.len + 2) ∧
        (∀ a, decEmFrame N t ≤ a → s'.mem a = st.mem a)) h12 ?_) ?_
    · intro k1 s1 hQ1
      obtain ⟨hk1, hH1, h91, hpc1, hfr1⟩ := hQ1
      exact Sem.mono (hL3 s1 hpc1 hH1 h91 hfr1)
        (fun k s' hh => ⟨hk1, hh.1, hh.2.1, hh.2.2.1, hh.2.2.2⟩)
    · rintro k s' ⟨k1, k2, hk, h1, h2, h3, h4, h5⟩
      exact ⟨by omega, h3, h4, h5⟩
  -- everything
  have htotal : (66 + decRoundBody.len + 2 + decEmitStmt.len) = decStmt.len := by
    rw [decStmt_len_form, progDecPreC_len, progDecPreS_len, decLoadW_len, decRoundStmt_len_form,
      decEmitStmt_len_form]
    omega
  refine Sem.end_congr (Sem.mono (Sem.seq
    (Q₁ := fun k1 s1 => k1 ≤ 63 + decLoadW.length + (1 + n * (decRoundCost N t + 2)) ∧
      DecLoopInv N t C x n s1 ∧ s1.pc = (66 + decRoundBody.len + 2) ∧
      (∀ a, decEmFrame N t ≤ a → s1.mem a = st.mem a))
    (Q₂ := fun k1 k2 s' => k1 ≤ 63 + decLoadW.length + (1 + n * (decRoundCost N t + 2)) ∧
      k2 ≤ decEmitStmtCost N t ∧ OutputsSupport s' x ∧
      (∀ a, decEmFrame N t ≤ a → s'.mem a = st.mem a)) h123 ?_) ?_) htotal
  · intro k1 s1 hQ1
    obtain ⟨hk1, hInv1, hpc1, hfr1⟩ := hQ1
    exact Sem.mono (hL4 s1 hpc1 hInv1 hfr1)
      (fun k s' hh => ⟨hk1, hh.1, hh.2.1, hh.2.2⟩)
  · rintro k s' ⟨k1, k2, hk, h1, h2, h3, h4⟩
    refine ⟨?_, h4⟩
    have hle := decStmtCost_le N t k1 k2 h1 h2
    omega


-- ===== finalF.lean =====


/-- **Halting runs are unique**: a deterministic machine that is absorbing at `halt` has at most one
final state, whatever the step budget. -/
theorem HaltsWithin_unique {P : Program} {E : RAMEnv} {T1 T2 : ℝ} {s s1 s2 : RAMState}
    (h1 : HaltsWithin P E T1 s s1) (h2 : HaltsWithin P E T2 s s2) : s1 = s2 := by
  obtain ⟨k1, -, hs1, hh1⟩ := h1
  obtain ⟨k2, -, hs2, hh2⟩ := h2
  have hfix : ∀ (st : RAMState), Halted P st → ∀ m : ℕ, (step P E)^[m] st = st := by
    intro st hst m
    have hhalt : P[st.pc]? = some .halt := (halted_iffA P st).mp hst
    have hstep : step P E st = st := step_halt P E st hhalt
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', ih, hstep]
  rcases le_total k1 k2 with hle | hle
  · have hk : k2 = (k2 - k1) + k1 := (Nat.sub_add_cancel hle).symm
    have hlast : (step P E)^[k2] s = s1 := by
      rw [hk, Function.iterate_add_apply, hs1]
      exact hfix s1 hh1 (k2 - k1)
    exact hlast.symm.trans hs2
  · have hk : k1 = (k1 - k2) + k2 := (Nat.sub_add_cancel hle).symm
    have hlast : (step P E)^[k1] s = s2 := by
      rw [hk, Function.iterate_add_apply, hs2]
      exact hfix s2 hh2 (k1 - k2)
    exact hs1.symm.trans hlast

/-- **The decoder's frame run, as a halting statement.** -/
theorem decStmt_halts_frame (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2) (eps : ℝ)
    (hexp : IsLayeredExpander C (2 * t) eps) (heps : 16 * eps ≤ 1)
    (hsup : (cr23Supp x).card ≤ t)
    (st : RAMState) (hpc : st.pc = 0) (h0 : st.regs r0 = 0)
    (hpay : ∀ a, a < wordsOf (cr23Word N) (cr23R N t) →
      st.mem a = packMem (cr23Word N) (cr23Sketch N t C x) a)
    (hzero : ∀ a, wordsOf (cr23Word N) (cr23R N t) ≤ a → a < decZeroBound N t →
      st.mem a = 0) :
    ∃ s' : RAMState,
      HaltsWithin progDec (detEnv (cr23Word N) (cr23DecDet N t C))
        ((decStmtCost N t : ℝ) + 1) st s' ∧
        (∀ a, decEmFrame N t ≤ a → s'.mem a = st.mem a) := by
  have hsem := decStmt_frameSem N t hN ht htN C x eps hexp heps hsup progDec progDec_at_main
    st hpc h0 hpay hzero
  refine halts_of_run progDec (detEnv (cr23Word N) (cr23DecDet N t C)) 0 decStmt.len
    st ((decStmtCost N t : ℝ) + 1)
    (fun k s' => k ≤ decStmtCost N t ∧
      (∀ a, decEmFrame N t ≤ a → s'.mem a = st.mem a))
    (fun s' => ∀ a, decEmFrame N t ≤ a → s'.mem a = st.mem a) progDec_at_halt hsem ?_
  rintro k s' ⟨hk, hfr⟩
  refine ⟨?_, hfr⟩
  have hk' : (k : ℝ) ≤ (decStmtCost N t : ℝ) := by exact_mod_cast hk
  linarith

/-- **The decoder memory frame at the entry states of Proposition 2.3** — the sharp form, at
`decEmFrame N t = decOutBase N t + (2t+1)`.

The hypotheses are exactly the ones `CRS.hdecW` / `CrStageInWz` provide (`pc = 0`, `r0 = 0`, the
payload window, the finite zero window).  Without them the statement is false: starting at an
arbitrary program counter (or with `r0 ≠ 0`, which moves `decOutBase`) a `store` inside the emit loop
can be executed with an arbitrary address register. -/
theorem decMemFrameAtOut_entry (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2) (eps : ℝ)
    (hexp : IsLayeredExpander C (2 * t) eps) (heps : 16 * eps ≤ 1)
    (hsup : (cr23Supp x).card ≤ t) (T : ℝ) (hT : (decStmtCost N t : ℝ) + 1 ≤ T) :
    ∀ s s' : RAMState, s.pc = 0 → s.regs r0 = 0 →
      (∀ a, a < wordsOf (cr23Word N) (cr23R N t) →
        s.mem a = packMem (cr23Word N) (cr23Sketch N t C x) a) →
      (∀ a, wordsOf (cr23Word N) (cr23R N t) ≤ a → a < decZeroBound N t → s.mem a = 0) →
      HaltsWithin progDec (detEnv (cr23Word N) (cr23DecDet N t C)) T s s' →
      ∀ a, decEmFrame N t ≤ a → s'.mem a = s.mem a := by
  intro s s' hpc h0 hpay hzero hrun a ha
  obtain ⟨s0, hrun0, hfr0⟩ := decStmt_halts_frame N t hN ht htN C x eps hexp heps hsup s hpc h0
    hpay hzero
  have heq : s' = s0 := HaltsWithin_unique hrun hrun0
  rw [heq]
  exact hfr0 a ha

/-- **The frame at the published bound `decFrameBound N t = decOutBase N t + N`**, in the regime
`2t+1 ≤ N` in which `decEmFrame ≤ decFrameBound`. -/
theorem decMemFrameAtOut_pre (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (hreg : 2 * t + 1 ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2) (eps : ℝ)
    (hexp : IsLayeredExpander C (2 * t) eps) (heps : 16 * eps ≤ 1)
    (hsup : (cr23Supp x).card ≤ t) (T : ℝ) (hT : (decStmtCost N t : ℝ) + 1 ≤ T) :
    ∀ s s' : RAMState, s.pc = 0 → s.regs r0 = 0 →
      (∀ a, a < wordsOf (cr23Word N) (cr23R N t) →
        s.mem a = packMem (cr23Word N) (cr23Sketch N t C x) a) →
      (∀ a, wordsOf (cr23Word N) (cr23R N t) ≤ a → a < decZeroBound N t → s.mem a = 0) →
      HaltsWithin progDec (detEnv (cr23Word N) (cr23DecDet N t C)) T s s' →
      ∀ a, CRS.decFrameBound N t ≤ a → s'.mem a = s.mem a := by
  intro s s' hpc h0 hpay hzero hrun a ha
  have hle : decEmFrame N t ≤ CRS.decFrameBound N t := by
    simp only [decEmFrame, CRS.decFrameBound]
    omega
  exact decMemFrameAtOut_entry N t hN ht htN C x eps hexp heps hsup T hT s s' hpc h0 hpay hzero
    hrun a (le_trans hle ha)



/-! ## The published unconditional `DecMemFrame` is false

`CRS.DecMemFrame` quantifies over **all** start states.  The decoder's code contains a store in the
emit walk; entering the program at that store (pc `277`) with the address register set to
`decFrameBound 1 1` and with `r0 = r2 = 0` reaches the `halt` in 7 steps and writes `1` at
`decFrameBound 1 1`.  So the unconditional statement is not provable; the missing hypotheses are the
entry conditions `pc = 0`, `r0 = 0` (and the payload/zero window), which are exactly what
`CrStageInWz` supplies. -/

def pStoreC : ℕ := 277
def B1C : ℕ := CRS.decFrameBound 1 1

def CC : Fin 1 → Fin (cr23D 1) → Fin (cr23M 1) := fun _ _ => ⟨0, by decide⟩

def s0C : RAMState where
  pc := pStoreC
  regs := fun i => if i = 5 then B1C else if i = 3 then 1 else 0
  mem := fun _ => 0

def E0C : RAMEnv := detEnv (cr23Word 1) (cr23DecDet 1 1 CC)
def PC : Program := programOfStatement decStmt
def runC (k : ℕ) : RAMState := (step PC E0C)^[k] s0C

def haltedBool (P : Program) (s : RAMState) : Bool :=
  match P[s.pc]? with
  | some .halt => true
  | _ => false

theorem haltedBool_iff (P : Program) (s : RAMState) : Halted P s ↔ haltedBool P s = true := by
  unfold Halted haltedBool
  split <;> simp_all

/-- **Machine-checked disproof of the published unconditional obligation**: the decoder started at
the emit loop's output store writes at `decFrameBound 1 1`. -/
theorem decMemFrameAtOut_false :
    ¬ CRS.decMemFrameAtOut 1 1 CC ((decStmtCost 1 1 : ℝ) + 1) := by
  intro h
  have h7r : ((7 : ℕ) : ℝ) ≤ (decStmtCost 1 1 : ℝ) + 1 := by
    have h7 : (7 : ℕ) ≤ decStmtCost 1 1 + 1 := by decide
    exact_mod_cast h7
  have hrun : HaltsWithin PC E0C ((decStmtCost 1 1 : ℝ) + 1) s0C (runC 7) := by
    refine ⟨7, h7r, rfl, ?_⟩
    exact (haltedBool_iff PC (runC 7)).mpr (by decide)
  have hf := h s0C (runC 7) hrun B1C (le_refl B1C)
  have h1 : (runC 7).mem B1C = 1 := by decide
  have h0 : s0C.mem B1C = 0 := by decide
  rw [h1, h0] at hf
  exact one_ne_zero hf

end LinearSetReconciliation327.Main

#print axioms LinearSetReconciliation327.Main.decParStmt_specF_r14
#print axioms LinearSetReconciliation327.Main.decEmitStmt_specF
#print axioms LinearSetReconciliation327.Main.decRoundBody_specF
#print axioms LinearSetReconciliation327.Main.decRoundStmt_specF
#print axioms LinearSetReconciliation327.Main.decPrologue_specF
#print axioms LinearSetReconciliation327.Main.decStmt_frameSem
#print axioms LinearSetReconciliation327.Main.decStmt_halts_frame
#print axioms LinearSetReconciliation327.Main.decMemFrameAtOut_entry
#print axioms LinearSetReconciliation327.Main.decMemFrameAtOut_pre
#print axioms LinearSetReconciliation327.Main.decMemFrameAtOut_false


