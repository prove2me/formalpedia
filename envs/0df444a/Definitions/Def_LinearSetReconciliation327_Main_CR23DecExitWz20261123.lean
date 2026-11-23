-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_CR23DecExitWz20261123
-- name    : LinearSetReconciliation327_Main_CR23DecExitWz20261123
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-23T11:28:28.626189+00:00
-- url     : https://prove2.me/theorems/e40dec58-8362-46d5-b665-c6781fd4a758
-- title:
--   Proposition 2.3's decoder from a finite zero tail: the bound Z = decOutBase N t and the re-proved engine decStmt_sem_exit_wz
-- statement:
--   The published proof of Proposition 2.3 (`decStmt_sem_exit`) consumes the decoder's start memory as (i) the payload on `[0, wordsOf W M)` and (ii) **infinitely many** zeros above it. This bundle determines exactly where the zero tail is read and re-proves the engine from a **finite** tail.
--
--   *Every* consumption of the zero hypothesis in the whole 282-instruction proof is in the prologue, at three sites: `decTagBase N t + v` and `decParBase N t + v` for `v < 2 ^ (cr23Lb N + 1)` (twice), all of them to establish that the tag/parity region starts at zero. The largest address is `decParBase N t + (2 ^ (cr23Lb N + 1) - 1)`, so the exact bound is `Z = decOutBase N t` (= `decZeroBound N t`). The bundle proves the closed forms `Z = cr23DecFrame N t + 34 + 4t + 2^(Lb+2)` and `Z = M + 3·N·(W - 1024) + N + 4·t + 37 + 2^(Lb+2)` with `M = cr23R N t`, `W = cr23Word N`, `Lb = cr23Lb N`, and shows the bound is attained (`Z - 1` is read), so no smaller window suffices. It then re-proves the prologue lemmas `decPrepareZ`, `decPreState_par_zeroZ`, `decPrologueDecHeadZ`, `decPrologue_specZ` with the finite hypothesis, re-runs the engine as `decStmt_sem_exit_wz`, and exports `decStmt_halts_exit_wz`: from **any** start state with `pc = 0`, `r0 = 0`, the payload on `[0, wordsOf W M)` and zeros on `[wordsOf W M, Z)`, the decoder `progDec` halts within the published budget, outputs the support of `x` and leaves `r0 = decOutBase N t` — memory at `>= Z` is unconstrained (the old whole-memory hypothesis is the `Z = infinity` case, `decStmt_sem_exit_wz_of_infinite`). This is the finite obligation left open by the window-pin repair of `CrStageIn`, and it is the only place the published Proposition 2.3 uses the infinite tail.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Proposition 2.3 / Theorem 6.5; the project's published `CR23DecRun20261122`, `CR23DecExit20261122` and `CrStageInWz20261123` bundles. The prologue proofs are copied byte-identically from `CR23DecRun20261122` except for the zero hypothesis and its three instantiation sites.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_CR23DecExit20261122

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped ENNReal
open Finset

noncomputable section

namespace LinearSetReconciliation327.Main

/-! # Proposition 2.3 with a **finite** zero tail: the closed form of `Z` and the re-proved engine

The published engine `decStmt_sem_exit` (`CR23DecExit20261122`) takes the zero tail of the decoder's
start memory as an **infinite** hypothesis

```lean
(hzero : ∀ a, wordsOf (cr23Word N) (cr23R N t) ≤ a → st.mem a = 0)
```

which is why the window pin `CrStageInW` cannot be transported through the `cr` field.  This bundle
does the two things that repair needs:

1. it determines, **concretely**, the largest address at which that proof instantiates `hzero`, and
   states it as the closed form `decZeroBound N t = decOutBase N t`;
2. it **re-runs** the engine with `hzero` restricted to `[wordsOf …, decZeroBound N t)`, obtaining
   `decStmt_sem_exit_wz` and `decStmt_halts_exit_wz` for an arbitrary start state that only pins the
   payload on the window and the zeros on that finite range.

## 1. Where `hzero` is consumed

The whole proof of `decStmt_sem_exit` consumes `hzero` in exactly **one** place: the prologue
(`decPrologue_spec`, via `decPrologueDecHead` → `decPrepare` and `decPreState_par_zero`).  The
`loadW`, round-loop and emit legs only read registers, the fifteen frame slots (written by the
prologue) and the payload window.  Inside the prologue there are exactly **three** instantiation
sites, all of them establishing "the parity/tag region starts at zero":

| site | lemma | address instantiated |
|---|---|---|
| 1 | `decPrepare`, tag clause | `decTagBase N t + v`, `v < 2 ^ (cr23Lb N + 1)` |
| 2 | `decPrepare`, parity clause | `decParBase N t + v`, `v < 2 ^ (cr23Lb N + 1)` |
| 3 | `decPrologueDecHead`, third `DecHead1` clause | `decParBase N t + v`, `v < 2 ^ (cr23Lb N + 1)` |

The largest of these is `decParBase N t + (2 ^ (cr23Lb N + 1) - 1)`, i.e. **`decOutBase N t - 1`**
(`decOutBase N t = decParBase N t + 2 ^ (cr23Lb N + 1)` by definition).  So

```
Z = decOutBase N t
```

is the exact bound: `decZeroBound_tight` shows the bound is attained (site 2/3 with
`v = 2 ^ (cr23Lb N + 1) - 1`), and `decZeroBound_eq_closed` expands it in `N`, `t`, `W = cr23Word N`,
`M = cr23R N t` and `Lb = cr23Lb N`:

```
Z = M + 3·N·(W - 1024) + N + 4·t + 37 + 2^(Lb+2)      (D = 1024·Lb = W - 1024).
```

`decOutBase N t` is also the base of the decoder's **output** window, which is the natural reading:
the decoder needs the zero tail only strictly below the window it writes.
-/

/-! ## 2. The bound `Z` -/

/-- **The zero-tail bound of Proposition 2.3's decoder**: the first address at which the published
proof of `decStmt_sem_exit` never reads the zero tail.  Equals `decOutBase N t`. -/
def decZeroBound (N t : ℕ) : ℕ := decOutBase N t

/-- `Z` is the decoder's output base. -/
theorem decZeroBound_eq_outBase (N t : ℕ) : decZeroBound N t = decOutBase N t := rfl

/-- **The bound is attained**: site 2/3 of the prologue instantiates `hzero` at
`decParBase N t + (2 ^ (cr23Lb N + 1) - 1) = Z - 1`, so no smaller window suffices. -/
theorem decZeroBound_tight (N t : ℕ) :
    decParBase N t + (2 ^ (cr23Lb N + 1) - 1) = decZeroBound N t - 1 := by
  have hpos : 0 < 2 ^ (cr23Lb N + 1) := Nat.two_pow_pos _
  simp only [decZeroBound, decOutBase]
  omega

/-- **`Z` in terms of the frame**: the five region bases between the frame start and the output
window contribute `34 + 4t + 2·2^(Lb+1)`. -/
theorem decZeroBound_eq_frame (N t : ℕ) :
    decZeroBound N t = cr23DecFrame N t + 34 + 4 * t + 2 ^ (cr23Lb N + 2) := by
  have h2 : 2 ^ (cr23Lb N + 2) = 2 ^ (cr23Lb N + 1) + 2 ^ (cr23Lb N + 1) := by
    rw [show cr23Lb N + 2 = (cr23Lb N + 1) + 1 by omega, pow_succ]
    ring
  simp only [decZeroBound, decOutBase, decParBase, decMstBase, decTagBase, decCandBase]
  omega

/-- **`Z` in the paper's parameters**: `M = cr23R N t` rows, `D = cr23D N` seeds, `Lb = cr23Lb N`. -/
theorem decZeroBound_eq_words (N t : ℕ) :
    decZeroBound N t = cr23R N t + 3 * N * cr23D N + N + 4 * t + 37 + 2 ^ (cr23Lb N + 2) := by
  rw [decZeroBound_eq_frame]
  simp only [cr23DecFrame, cr23Graph0, cr23PairEnd]
  ring

/-- **`Z` with the word width substituted**: `cr23D N = cr23Word N - 1024`. -/
theorem cr23D_eq_word_sub (N : ℕ) : cr23D N = cr23Word N - 1024 := by
  simp only [cr23D, cr23Word]
  omega

/-- **`Z` as a closed form in `N`, `t`, `W = cr23Word N` and `M = cr23R N t`** (with
`Lb = cr23Lb N`): `Z = M + 3·N·(W − 1024) + N + 4·t + 37 + 2^(Lb+2)`. -/
theorem decZeroBound_eq_closed (N t : ℕ) :
    decZeroBound N t
      = cr23R N t + 3 * N * (cr23Word N - 1024) + N + 4 * t + 37 + 2 ^ (cr23Lb N + 2) := by
  rw [decZeroBound_eq_words, cr23D_eq_word_sub]

/-- **The old infinite tail gives the finite window at every `Z`** — the `Z = ∞` case. -/
theorem decZeroBound_of_infinite {N t : ℕ} {st : RAMState}
    (h : ∀ a, wordsOf (cr23Word N) (cr23R N t) ≤ a → st.mem a = 0) :
    ∀ a, wordsOf (cr23Word N) (cr23R N t) ≤ a → a < decZeroBound N t → st.mem a = 0 :=
  fun a ha _ => h a ha

/-! ## 3. The prologue, with zeros only below `Z` -/

/-- **The prologue's invariant from a finite zero window.**  Same proof as the published
`decPrepare`, with `hzero` instantiated at `decTagBase N t + v` and `decParBase N t + v`
(`v < 2 ^ (cr23Lb N + 1)`), both `< decZeroBound N t`. -/
theorem decPrepareZ (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2) (s : RAMState)
    (h0 : s.regs r0 = 0)
    (hpay : ∀ a < wordsOf (cr23Word N) (cr23R N t),
      s.mem a = packMem (cr23Word N) (cr23Sketch N t C x) a)
    (hzero : ∀ a, wordsOf (cr23Word N) (cr23R N t) ≤ a → a < decZeroBound N t → s.mem a = 0) :
    DecData N t C x t 1 0 ∅ [] (decPreState N t C s) := by
  have hmem := decPreS_data N t hN htN C s h0
  have hnod := decSlotList_keys_nodup N t
  have hget : ∀ k < 15, (decPreState N t C s).mem (decSlot N t k) = decSlotVal N t k := by
    intro k hk
    rw [hmem]
    exact writeList_get s.mem (decSlotList N t) (decSlot N t k) (decSlotVal N t k) hnod
      (decSlotList_mem N t hk)
  have hout : ∀ a, (∀ k < 15, a ≠ decSlot N t k) →
      (decPreState N t C s).mem a = s.mem a := by
    intro a ha
    rw [hmem]
    refine writeList_out s.mem (decSlotList N t) a (fun p hp hpa => ?_)
    rw [decSlotList] at hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    exact ha k (List.mem_range.mp hk) hpa.symm
  refine ⟨hget 0 (by norm_num), hget 1 (by norm_num), hget 2 (by norm_num), hget 3 (by norm_num),
    hget 4 (by norm_num), hget 5 (by norm_num), hget 6 (by norm_num), hget 7 (by norm_num),
    hget 8 (by norm_num), hget 9 (by norm_num), hget 10 (by norm_num), hget 11 (by norm_num),
    hget 12 (by norm_num), hget 13 (by norm_num), hget 14 (by norm_num), ?_, ?_, ?_, ?_⟩
  · intro a ha
    have houta : (decPreState N t C s).mem a = s.mem a := by
      refine hout a (fun k hk => ?_)
      have h1 : a < cr23DecFrame N t := lt_of_lt_of_le ha (cr23_wordsOf_le_frame N t hN)
      simp only [decSlot]
      omega
    rw [houta]
    exact hpay a ha
  · intro v hv
    have hz : s.mem (decTagBase N t + v) = 0 := by
      refine hzero _ (le_trans (cr23_wordsOf_le_frame N t hN)
        (le_trans (decFrame_le_tagBase N t) (dec_le_add_self _ v))) ?_
      have h1 : decTagBase N t + 2 ^ (cr23Lb N + 1) = decMstBase N t := rfl
      have h2 := decMstBase_le_parBase N t
      have hpos : 0 < 2 ^ (cr23Lb N + 1) := Nat.two_pow_pos _
      simp only [decZeroBound, decOutBase]
      omega
    have houta : (decPreState N t C s).mem (decTagBase N t + v)
        = s.mem (decTagBase N t + v) := by
      refine hout _ (fun k hk => ?_)
      exact ne_of_gt (lt_of_lt_of_le (decSlot_lt_candBase N t hk)
        (le_trans (decCandBase_le_tagBase N t) (dec_le_add_self _ v)))
    rw [houta, hz]
    omega
  · intro v hv
    have hz : s.mem (decParBase N t + v) = 0 := by
      refine hzero _ (le_trans (cr23_wordsOf_le_frame N t hN)
        (le_trans (decFrame_le_parBase N t) (dec_le_add_self _ v))) ?_
      have hpos : 0 < 2 ^ (cr23Lb N + 1) := Nat.two_pow_pos _
      simp only [decZeroBound, decOutBase]
      omega
    have houta : (decPreState N t C s).mem (decParBase N t + v)
        = s.mem (decParBase N t + v) := by
      refine hout _ (fun k hk => ?_)
      exact ne_of_gt (lt_of_lt_of_le (decSlot_lt_candBase N t hk)
        (le_trans (decCandBase_le_tagBase N t)
          (le_trans (decTagBase_le_mstBase N t)
            (le_trans (decMstBase_le_parBase N t) (dec_le_add_self _ v)))))
    rw [houta, hz]
    simp
  · intro i hi
    omega

/-- **Every parity cell starts at zero**, from the finite window only. -/
theorem decPreState_par_zeroZ (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (s : RAMState) (h0 : s.regs r0 = 0)
    (hzero : ∀ a, wordsOf (cr23Word N) (cr23R N t) ≤ a → a < decZeroBound N t → s.mem a = 0)
    (v : ℕ) (hv : decParBase N t + v < decZeroBound N t) :
    (decPreState N t C s).mem (decParBase N t + v) = 0 := by
  rw [decPreState_mem_out N t hN htN C s h0 (fun k hk => ?_)]
  · exact hzero _ (le_trans (cr23_wordsOf_le_frame N t hN)
      (le_trans (decFrame_le_parBase N t) (dec_le_add_self _ v))) hv
  · exact ne_of_gt (lt_of_lt_of_le (decSlot_lt_candBase N t hk)
      (le_trans (decCandBase_le_tagBase N t)
        (le_trans (decTagBase_le_mstBase N t)
          (le_trans (decMstBase_le_parBase N t) (dec_le_add_self _ v)))))

/-- **The prologue establishes `DecHead1`** at `(z = x, w = t, tag = 1, P = ∅, mst = [])`, from the
finite zero window. -/
theorem decPrologueDecHeadZ (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2)
    (hsup : (cr23Supp x).card ≤ t) (s : RAMState) (h0 : s.regs r0 = 0)
    (hpay : ∀ a, a < wordsOf (cr23Word N) (cr23R N t) →
      s.mem a = packMem (cr23Word N) (cr23Sketch N t C x) a)
    (hzero : ∀ a, wordsOf (cr23Word N) (cr23R N t) ≤ a → a < decZeroBound N t → s.mem a = 0) :
    DecHead1 N t C x x t 1 ∅ [] (decPreState N t C s) := by
  have hD := decPrepareZ N t hN htN C x s h0 hpay hzero
  have h14D := decPreState_regs14 N t hN htN C s h0
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19⟩ := hD
  have hDN' : DecDataN N t C x t 1 ([] : List ℕ).length (∅ : Finset ℕ) []
      (decPreState N t C s) := by
    refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, ?_, a19⟩
    intro v hv
    constructor
    · intro h
      obtain ⟨i, -, hi⟩ := (a18 v hv).mp h
      exact absurd hi (by simp)
    · intro h
      exact absurd h (by simp)
  refine ⟨⟨hDN', ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact h14D
  · rw [cr23_add_self_eq_zero]
    simp [cr23Supp, cr23NumSet]
  · intro v hv
    simp at hv
  · simp only [List.length_nil]
    omega
  · exact hsup
  · intro v hv
    simp at hv
  · intro v hv
    have hv' : decParBase N t + v < decZeroBound N t := by
      have hpos : 0 < 2 ^ (cr23Lb N + 1) := Nat.two_pow_pos _
      simp only [decZeroBound, decOutBase]
      omega
    rw [decPreState_par_zeroZ N t hN htN C s h0 hzero v hv']
    omega

/-- **The prologue block**, as a `Sem` from `0` to `progDecPre.length`, from the finite window. -/
theorem decPrologue_specZ (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2)
    (hsup : (cr23Supp x).card ≤ t) (Pgm : Program) (hAt : At Pgm 0 progDecPre)
    (st : RAMState) (hpc : st.pc = 0) (h0 : st.regs r0 = 0)
    (hpay : ∀ a, a < wordsOf (cr23Word N) (cr23R N t) →
      st.mem a = packMem (cr23Word N) (cr23Sketch N t C x) a)
    (hzero : ∀ a, wordsOf (cr23Word N) (cr23R N t) ≤ a → a < decZeroBound N t → st.mem a = 0) :
    Sem Pgm (detEnv (cr23Word N) (cr23DecDet N t C)) 0 progDecPre.length st
      (fun k s' => k = progDecPre.length ∧ DecHead1 N t C x x t 1 ∅ [] s' ∧
        s'.regs r14 = cr23DecFrame N t) := by
  refine Sem.monoA (Sem.blockA Pgm (detEnv (cr23Word N) (cr23DecDet N t C)) 0 progDecPre st hAt
    progDecPre_noBranch hpc) ?_
  rintro k s' ⟨rfl, rfl⟩
  exact ⟨rfl, decPrologueDecHeadZ N t hN htN C x hsup st h0 hpay hzero,
    decPreState_regs14 N t hN htN C st h0⟩

/-! ## 4. The engine, re-run with the finite zero tail -/

/-- **Proposition 2.3's decoder, from a state with zeros only on `[wordsOf …, Z)`.**

Identical to the published `decStmt_sem_exit` except that the zero hypothesis is restricted to the
finite range `[wordsOf (cr23Word N) (cr23R N t), decZeroBound N t)`; memory at
`≥ decZeroBound N t` is arbitrary.  The only place the published proof used the infinite tail is the
prologue, so only the prologue leg changes (`decPrologue_specZ`). -/
theorem decStmt_sem_exit_wz (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
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
      (fun k s' => k ≤ decStmtCost N t ∧ OutputsSupport s' x ∧ s'.regs r0 = decOutBase N t) := by
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
  -- leg 1: the prologue
  have hProl : Sem Pgm E 0 63 st
      (fun k s' => (k = 63 ∧ DecHead1 N t C x x t 1 ∅ [] s' ∧
        s'.regs r14 = cr23DecFrame N t) ∧ s'.pc = 63) := by
    have h := decPrologue_specZ N t hN htN C x hsup Pgm hAtPre st hpc h0 hpay hzero
    rw [hpre] at h
    exact Sem.add_pc h
  -- leg 2: the counter reload
  have hL2 : ∀ (s1 : RAMState), s1.pc = 63 → DecHead1 N t C x x t 1 ∅ [] s1 →
      s1.regs r14 = cr23DecFrame N t →
      Sem Pgm E 63 66 s1
        (fun k s' => k = decLoadW.length ∧ DecHead1 N t C x x t 1 ∅ [] s' ∧
          s'.regs r9 = t ∧ s'.pc = 66) := by
    intro s1 hpc1 hH1 h141
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
    exact ⟨hk, hH1', h9', by rw [hpc3, hpc1]⟩
  -- leg 3: the round loop
  have hL3 : ∀ (s2 : RAMState), s2.pc = 66 → DecHead1 N t C x x t 1 ∅ [] s2 →
      s2.regs r9 = t →
      Sem Pgm E 66 (66 + decRoundBody.len + 2) s2
        (fun k s' => k ≤ 1 + n * (decRoundCost N t + 2) ∧
          DecLoopInv N t C x n s' ∧ s'.pc = (66 + decRoundBody.len + 2)) := by
    intro s2 hpc2 hH2 h92
    exact decRoundStmt_spec N t hN ht htN C x eps hexp heps Pgm 66 hAtR s2 hpc2 hH2 h92
  -- leg 4: the emit pass
  have hw0 : t / 4 ^ n = 0 := by
    rw [hn]
    refine Nat.div_eq_of_lt ?_
    have h := Nat.le_pow_clog (b := 4) (by norm_num : 1 < 4) (t + 1)
    omega
  have hL4 : ∀ (s3 : RAMState), s3.pc = (66 + decRoundBody.len + 2) →
      DecLoopInv N t C x n s3 →
      Sem Pgm E (66 + decRoundBody.len + 2)
        (66 + decRoundBody.len + 2 + decEmitStmt.len) s3
        (fun k s' => k ≤ decEmitStmtCost N t ∧ OutputsSupport s' x ∧ s'.regs r0 = decOutBase N t) := by
    intro s3 hpc3 hInv
    obtain ⟨z, P, mst, hH3, -⟩ := hInv
    rw [hw0] at hH3
    have hH3' := hH3
    obtain ⟨⟨-, -, -, -, -, hwc⟩, -, -⟩ := hH3'
    have hK : cr23Supp z = ∅ := Finset.card_eq_zero.mp (by omega)
    exact decEmitStmt_spec_exit N t hN htN C x z 0 (1 + n) P mst s3 Pgm (66 + decRoundBody.len + 2)
      hAtE hpc3 rfl hH3 hK
  -- 1 · 2
  have h12 : Sem Pgm E 0 66 st
      (fun k s' => k = 63 + decLoadW.length ∧ DecHead1 N t C x x t 1 ∅ [] s' ∧
        s'.regs r9 = t ∧ s'.pc = 66) := by
    refine Sem.mono (Sem.seq (Q₁ := fun k1 s1 => (k1 = 63 ∧ DecHead1 N t C x x t 1 ∅ [] s1 ∧
        s1.regs r14 = cr23DecFrame N t) ∧ s1.pc = 63)
      (Q₂ := fun k1 k2 s' => k1 = 63 ∧ k2 = decLoadW.length ∧
        DecHead1 N t C x x t 1 ∅ [] s' ∧ s'.regs r9 = t ∧ s'.pc = 66) hProl ?_) ?_
    · intro k1 s1 hQ1
      obtain ⟨⟨hk1, hH1, h141⟩, hpc1⟩ := hQ1
      exact Sem.mono (hL2 s1 hpc1 hH1 h141)
        (fun k s' hh => ⟨hk1, hh.1, hh.2.1, hh.2.2.1, hh.2.2.2⟩)
    · rintro k s' ⟨k1, k2, hk, h1, h2, h3, h4, h5⟩
      exact ⟨by omega, h3, h4, h5⟩
  -- (1 · 2) · 3
  have h123 : Sem Pgm E 0 (66 + decRoundBody.len + 2) st
      (fun k s' => k ≤ 63 + decLoadW.length + (1 + n * (decRoundCost N t + 2)) ∧
        DecLoopInv N t C x n s' ∧ s'.pc = (66 + decRoundBody.len + 2)) := by
    refine Sem.mono (Sem.seq (Q₁ := fun k1 s1 => k1 = 63 + decLoadW.length ∧
        DecHead1 N t C x x t 1 ∅ [] s1 ∧ s1.regs r9 = t ∧ s1.pc = 66)
      (Q₂ := fun k1 k2 s' => k1 = 63 + decLoadW.length ∧
        k2 ≤ 1 + n * (decRoundCost N t + 2) ∧ DecLoopInv N t C x n s' ∧
        s'.pc = (66 + decRoundBody.len + 2)) h12 ?_) ?_
    · intro k1 s1 hQ1
      obtain ⟨hk1, hH1, h91, hpc1⟩ := hQ1
      exact Sem.mono (hL3 s1 hpc1 hH1 h91)
        (fun k s' hh => ⟨hk1, hh.1, hh.2.1, hh.2.2⟩)
    · rintro k s' ⟨k1, k2, hk, h1, h2, h3, h4⟩
      exact ⟨by omega, h3, h4⟩
  -- everything
  have htotal : (66 + decRoundBody.len + 2 + decEmitStmt.len) = decStmt.len := by
    rw [decStmt_len_form, progDecPreC_len, progDecPreS_len, decLoadW_len, decRoundStmt_len_form,
      decEmitStmt_len_form]
    omega
  refine Sem.end_congr (Sem.mono (Sem.seq
    (Q₁ := fun k1 s1 => k1 ≤ 63 + decLoadW.length + (1 + n * (decRoundCost N t + 2)) ∧
      DecLoopInv N t C x n s1 ∧ s1.pc = (66 + decRoundBody.len + 2))
    (Q₂ := fun k1 k2 s' => k1 ≤ 63 + decLoadW.length + (1 + n * (decRoundCost N t + 2)) ∧
      k2 ≤ decEmitStmtCost N t ∧ OutputsSupport s' x ∧ s'.regs r0 = decOutBase N t) h123 ?_) ?_) htotal
  · intro k1 s1 hQ1
    obtain ⟨hk1, hInv1, hpc1⟩ := hQ1
    exact Sem.mono (hL4 s1 hpc1 hInv1) (fun k s' hh => ⟨hk1, hh.1, hh.2.1, hh.2.2⟩)
  · rintro k s' ⟨k1, k2, hk, h1, h2, h3, h4⟩
    refine ⟨?_, h3, h4⟩
    have hle := decStmtCost_le N t k1 k2 h1 h2
    omega

/-- **Proposition 2.3's decoder halts from a finite zero tail.**  `HaltsWithin progDec` at the
published budget, with the decoded support and `r0 = decOutBase N t`, from an arbitrary start state
that presents the payload on `[0, wordsOf …)` and zeros on `[wordsOf …, Z)`; memory at `≥ Z` is
arbitrary. -/
theorem decStmt_halts_exit_wz (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
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
        OutputsSupport s' x ∧ s'.regs r0 = decOutBase N t := by
  have hsem := decStmt_sem_exit_wz N t hN ht htN C x eps hexp heps hsup progDec progDec_at_main
    st hpc h0 hpay hzero
  refine halts_of_run progDec (detEnv (cr23Word N) (cr23DecDet N t C)) 0 decStmt.len
    st ((decStmtCost N t : ℝ) + 1)
    (fun k s' => k ≤ decStmtCost N t ∧ OutputsSupport s' x ∧ s'.regs r0 = decOutBase N t)
    (fun s' => OutputsSupport s' x ∧ s'.regs r0 = decOutBase N t) progDec_at_halt hsem ?_
  rintro k s' ⟨hk, hout, hr0⟩
  refine ⟨?_, hout, hr0⟩
  have hk' : (k : ℝ) ≤ (decStmtCost N t : ℝ) := by exact_mod_cast hk
  linarith

/-- **The finite hypothesis is the only thing used**: the published infinite-tail engine
`decStmt_sem_exit` is the special case of `decStmt_sem_exit_wz` in which the tail is infinite
(no hypothesis on memory at `≥ Z` is needed there). -/
theorem decStmt_sem_exit_wz_of_infinite (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2) (eps : ℝ)
    (hexp : IsLayeredExpander C (2 * t) eps) (heps : 16 * eps ≤ 1)
    (hsup : (cr23Supp x).card ≤ t)
    (Pgm : Program) (hAt : At Pgm 0 (Stmt.compile decStmt 0))
    (st : RAMState) (hpc : st.pc = 0) (h0 : st.regs r0 = 0)
    (hpay : ∀ a, a < wordsOf (cr23Word N) (cr23R N t) →
      st.mem a = packMem (cr23Word N) (cr23Sketch N t C x) a)
    (hzero : ∀ a, wordsOf (cr23Word N) (cr23R N t) ≤ a → st.mem a = 0) :
    Sem Pgm (detEnv (cr23Word N) (cr23DecDet N t C)) 0 decStmt.len st
      (fun k s' => k ≤ decStmtCost N t ∧ OutputsSupport s' x ∧ s'.regs r0 = decOutBase N t) :=
  decStmt_sem_exit_wz N t hN ht htN C x eps hexp heps hsup Pgm hAt st hpc h0 hpay
    (decZeroBound_of_infinite hzero)

/-- **`Z` is computable**: at the smallest admissible instance `(N,t) = (1,1)` it is the concrete
number `2^79 + 3122` (`cr23R 1 1 = 2^79`, `cr23D 1 = 1024`, `cr23Lb 1 = 1`). -/
theorem decZeroBound_one_one : decZeroBound 1 1 = 2 ^ 79 + 3122 := by decide

end LinearSetReconciliation327.Main

#print axioms LinearSetReconciliation327.Main.decZeroBound_tight
#print axioms LinearSetReconciliation327.Main.decZeroBound_eq_frame
#print axioms LinearSetReconciliation327.Main.decZeroBound_eq_words
#print axioms LinearSetReconciliation327.Main.decZeroBound_eq_closed
#print axioms LinearSetReconciliation327.Main.decPrepareZ
#print axioms LinearSetReconciliation327.Main.decPreState_par_zeroZ
#print axioms LinearSetReconciliation327.Main.decPrologueDecHeadZ
#print axioms LinearSetReconciliation327.Main.decPrologue_specZ
#print axioms LinearSetReconciliation327.Main.decStmt_sem_exit_wz
#print axioms LinearSetReconciliation327.Main.decStmt_halts_exit_wz
#print axioms LinearSetReconciliation327.Main.decStmt_sem_exit_wz_of_infinite
#print axioms LinearSetReconciliation327.Main.decZeroBound_one_one


