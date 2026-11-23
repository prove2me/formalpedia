-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_CrStageInWz20261123
-- name    : LinearSetReconciliation327_Main_CrStageInWz20261123
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-23T11:06:54.12256+00:00
-- url     : https://prove2.me/theorems/4594efaf-53c5-47c5-8d82-f8853b2ef043
-- title:
--   Theorem 6.5: the finite payload-plus-zeros window for the CR stage
-- statement:
--   The entry condition of the `CR` stage of Theorem 6.5 with a **finite** window: the state presents the decoder's payload on `[0, wordsOf E.W M)` and zeros on `[wordsOf E.W M, Z)`, with memory at `>= Z` free, where `Z` bounds the addresses at which the decoder's correctness proof reads the zero tail.  It implies the payload-window condition, it is implied by the old whole-memory condition (which is the `Z = infinity` case), and it is non-degenerately inhabited for every `k` by a state whose word `Z + k` is `1`.  Its two projections are exactly the payload hypothesis and the zero hypothesis that the published proof of Proposition 2.3 consumes, so re-proving that proposition with the zero hypothesis restricted to this finite range discharges the only obligation that the window repair leaves open.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5 / Proposition 2.3; the project's published `CrField20261122`, `CR23DecExit20261122` and the new `CrStageInW20261123` bundle.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_CrStageInW20261123

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 40000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Finset

noncomputable section

namespace LinearSetReconciliation327.Main
namespace CRS

/-! # The finite-zero window: the version of the pin that Proposition 2.3 actually consumes

The weakened `CrStageInW` (`CrStageInW20261123`) pins only the payload words
`[0, wordsOf E.W M)`.  That is enough for the *statement* of the residual stage, but **not** for the
published proof of Proposition 2.3: `decStmt_sem_exit` (`CR23DecExit20261122`, the engine of
`decStmt_halts_exit` and hence of `proposition_2_3`) takes two hypotheses on the start memory,

```lean
(hpay : ∀ a, a < wordsOf (cr23Word N) (cr23R N t) → st.mem a = packMem … a)
(hzero : ∀ a, wordsOf (cr23Word N) (cr23R N t) ≤ a → st.mem a = 0)
```

The second one is an **infinite** zero tail — the half of the old whole-memory pin that no finite
program can restore, and the reason `CrStageInW → CrStageIn` is false.

This bundle states the window that is both finite and strong enough:
`CrStageInWz E M Z y …` pins the payload on `[0, wordsOf E.W M)` and **zeros on
`[wordsOf E.W M, Z)`**, with memory at `≥ Z` free.  It

* implies `CrStageInW` (`crStageInW_of_crStageInWz`), so every consumer of the weakened pin is
  served;
* supplies exactly the two hypotheses above, restricted to a finite range
  (`crStageInWz_pay`, `crStageInWz_zero`);
* is implied by the old whole-memory `CrStageIn` (`crStageInWz_of_crStageIn`), so the old pin is the
  `Z = ∞` case;
* is non-degenerately inhabited for every `k` (`crStageInWz_inhabited_nondegen`).

The remaining obligation is then exactly: re-run `decStmt_sem_exit` with `hzero` restricted to the
finite set of addresses at which its proof instantiates it — an entirely finite task, and the only
new lemma the window repair leaves open.
-/

/-! ## 1. The finite-zero window -/

/-- **The `cr` entry with a finite payload-plus-zeros window.**  `Z` is the bound of the decoder's
zero reads (`wordsOf E.W M ≤ Z`); memory at `≥ Z` is unconstrained. -/
def CrStageInWz (E : RAMEnv) (M Z : ℕ) (y : Fin M → ZMod 2)
    (ab al bb bl ob : ℕ) (Lx : List ℕ) (t : RAMState) : Prop :=
  t.regs = (decoderStart E.W y []).regs ∧
    (∀ j : ℕ, j < wordsOf E.W M → t.mem j = packMem E.W y j) ∧
    (∀ a : ℕ, wordsOf E.W M ≤ a → a < Z → t.mem a = 0) ∧
    CrMergeData E ab al bb bl ob Lx

/-! ## 2. Its two payload/zero projections (the shapes of `hpay` and `hzero`) -/

/-- The `hpay` shape: the payload on `[0, wordsOf E.W M)`. -/
theorem crStageInWz_pay {E : RAMEnv} {M Z : ℕ} {y : Fin M → ZMod 2} {ab al bb bl ob : ℕ}
    {Lx : List ℕ} {t : RAMState} (h : CrStageInWz E M Z y ab al bb bl ob Lx t) :
    ∀ j : ℕ, j < wordsOf E.W M → t.mem j = packMem E.W y j := h.2.1

/-- The **finite** `hzero` shape: zeros on `[wordsOf E.W M, Z)`. -/
theorem crStageInWz_zero {E : RAMEnv} {M Z : ℕ} {y : Fin M → ZMod 2} {ab al bb bl ob : ℕ}
    {Lx : List ℕ} {t : RAMState} (h : CrStageInWz E M Z y ab al bb bl ob Lx t) :
    ∀ a : ℕ, wordsOf E.W M ≤ a → a < Z → t.mem a = 0 := h.2.2.1

/-- The merge data, verbatim. -/
theorem crStageInWz_data {E : RAMEnv} {M Z : ℕ} {y : Fin M → ZMod 2} {ab al bb bl ob : ℕ}
    {Lx : List ℕ} {t : RAMState} (h : CrStageInWz E M Z y ab al bb bl ob Lx t) :
    CrMergeData E ab al bb bl ob Lx := h.2.2.2

/-! ## 3. It implies the weakened payload window -/

/-- **The finite-zero window serves every `CrStageInW` consumer.** -/
theorem crStageInW_of_crStageInWz {E : RAMEnv} {M Z : ℕ} {y : Fin M → ZMod 2}
    {ab al bb bl ob : ℕ} {Lx : List ℕ} {t : RAMState}
    (h : CrStageInWz E M Z y ab al bb bl ob Lx t) : CrStageInW E M y ab al bb bl ob Lx t := by
  obtain ⟨hr, hpay, -, hd⟩ := h
  refine ⟨hr, ⟨fun j hj => ?_, ?_, ?_, ?_⟩, hd⟩
  · rw [List.length_nil, Nat.add_zero] at hj
    rw [show hintMem E.W y [] j = packMem E.W y j from by
      unfold hintMem
      rw [if_pos hj]]
    simpa using hpay j hj
  · rw [hr]; simp [decoderStart, initState]
  · rw [hr]; simp [decoderStart, initState]
  · rw [hr]; simp [decoderStart, initState]

/-! ## 4. The old whole-memory pin is the `Z = ∞` case -/

/-- **The old whole-memory `CrStageIn` gives the finite-zero window at every `Z`.** -/
theorem crStageInWz_of_crStageIn {E : RAMEnv} {M Z : ℕ} {y : Fin M → ZMod 2}
    {ab al bb bl ob : ℕ} {Lx : List ℕ} {t : RAMState}
    (h : CrStageIn E M y ab al bb bl ob Lx t) : CrStageInWz E M Z y ab al bb bl ob Lx t := by
  obtain ⟨hr, hm, hd⟩ := h
  refine ⟨hr, ?_, ?_, hd⟩
  · intro j hj
    rw [hm]
    show hintMem E.W y [] j = packMem E.W y j
    unfold hintMem
    rw [if_pos hj]
  · intro a ha _
    rw [hm]
    show hintMem E.W y [] a = 0
    unfold hintMem
    rw [if_neg (by omega)]
    rfl

/-! ## 5. Inhabitants -/

/-- The decoder's own start state satisfies the finite-zero window (its memory is the payload and
then zeros). -/
theorem crStageInWz_decoderStart (E : RAMEnv) (M Z : ℕ) (y : Fin M → ZMod 2)
    (ab al bb bl ob : ℕ) (Lx : List ℕ) (hdata : CrMergeData E ab al bb bl ob Lx) :
    CrStageInWz E M Z y ab al bb bl ob Lx (decoderStart E.W y []) := by
  refine ⟨rfl, ?_, ?_, hdata⟩
  · intro j hj
    show hintMem E.W y [] j = packMem E.W y j
    unfold hintMem
    rw [if_pos hj]
  · intro a ha _
    show hintMem E.W y [] a = 0
    unfold hintMem
    rw [if_neg (by omega)]
    rfl

/-- **The finite-zero window is non-degenerately inhabited**: for every `k` a state satisfying it
whose word `Z + k` is `1` — memory past the window is completely free. -/
theorem crStageInWz_inhabited_nondegen {E : RAMEnv} {M Z : ℕ} {y : Fin M → ZMod 2}
    {ab al bb bl ob : ℕ} {Lx : List ℕ} (hZ : wordsOf E.W M ≤ Z)
    (hdata : CrMergeData E ab al bb bl ob Lx) (k : ℕ) :
    ∃ t : RAMState, CrStageInWz E M Z y ab al bb bl ob Lx t ∧ t.mem (Z + k) = 1 := by
  classical
  refine ⟨⟨0, (decoderStart E.W y []).regs,
      fun a => if a < wordsOf E.W M then packMem E.W y a else if a < Z then 0 else 1⟩,
    ⟨rfl, ?_, ?_, hdata⟩, ?_⟩
  · intro j hj
    change (if j < wordsOf E.W M then packMem E.W y j else if j < Z then 0 else 1)
      = packMem E.W y j
    rw [if_pos hj]
  · intro a ha haZ
    change (if a < wordsOf E.W M then packMem E.W y a else if a < Z then 0 else 1) = 0
    rw [if_neg (by omega), if_pos haZ]
  · change (if Z + k < wordsOf E.W M then packMem E.W y (Z + k)
      else if Z + k < Z then 0 else 1) = 1
    rw [if_neg (by omega), if_neg (by omega)]

/-- **Strictly weaker than the old pin**, and non-degenerate at a concrete `y ≠ 0` witness. -/
theorem crStageInWz_nondegen_concrete :
    ∃ t : RAMState, CrStageInWz E8 8 (wordsOf 8 8 + 3) y8 10 1 20 1 40 [5] t ∧
      t.mem (wordsOf 8 8 + 3 + 1) = 1 :=
  crStageInWz_inhabited_nondegen (by omega : wordsOf 8 8 ≤ wordsOf 8 8 + 3) data8 1

end CRS
end LinearSetReconciliation327.Main

#print axioms LinearSetReconciliation327.Main.CRS.crStageInWz_pay
#print axioms LinearSetReconciliation327.Main.CRS.crStageInWz_zero
#print axioms LinearSetReconciliation327.Main.CRS.crStageInW_of_crStageInWz
#print axioms LinearSetReconciliation327.Main.CRS.crStageInWz_of_crStageIn
#print axioms LinearSetReconciliation327.Main.CRS.crStageInWz_decoderStart
#print axioms LinearSetReconciliation327.Main.CRS.crStageInWz_inhabited_nondegen
#print axioms LinearSetReconciliation327.Main.CRS.crStageInWz_nondegen_concrete


