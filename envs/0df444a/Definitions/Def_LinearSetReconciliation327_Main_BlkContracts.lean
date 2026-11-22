-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_BlkContracts
-- name    : LinearSetReconciliation327_Main_BlkContracts
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-21T14:12:07.356145+00:00
-- url     : https://prove2.me/theorems/f02df03d-672c-4c44-a021-6d9264a3bdcf
-- title:
--   The per-block run contracts of Theorem 6.5's conjunct 6 (`UpBlkSem`, `UpChildSem`, `CrSem`)
-- statement:
--   Theorem 6.5's conjunct-6 assembly is conditional on exactly two hypotheses: the per-block contract supplied by Theorem 5.1's export (`hUp`) and the same contract supplied by Proposition 2.3's export for the composite's last (`CR`) block (`hCr`).  A *block* is a statement $S$ of the word-RAM language, compiled at an arbitrary base $b$ and started there with three registers set by the caller: $r_{14}$ is the base $\delta$ of the block's slice of the preprocessed table, $r_{15}$ is the payload word base $\beta$, and $r_0$ is the coordinate $i$ to toggle.  The contract `UpBlkSem` says that, provided the environment's table agrees with the block's own table on the window $[\delta,\delta+Bw)$, the block
--
--   $$\text{reaches } b+\mathrm{len}(S),\quad \text{XORs } H e_i \text{ into the words } [\beta,\beta+\mathrm{wordsOf}(M_s)),\quad \text{leaves every other address alone,}$$
--
--   and preserves $r_0,\dots,r_4$ — the dispatcher's loop counter, bound, stride and base-table pointer.  `UpChildSem` is the same predicate one per child block, and `CrSem` drops the five register clauses: it is what a block that is *last* in the composite has to satisfy, and it is the only part of `UpBlkSem` that Proposition 2.3's block can meet, since its prologue writes $r_3$.  The bundle also records, machine-checked, that 2.3's published start state has $r_{15}=0$ and $r_1=0$, so it cannot satisfy the register premises of either contract as published.
-- source:
--   Theorem 6.5 (conjunct 6) of arXiv:2611.11409, Liu--Xu--Yang--Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*; the contract layer of the verified development (`Definitions.Def_..._Top65Up` section U4 and `Definitions.Def_..._Conj6Asm` section H), with 2.3's program and start state from `Definitions.Def_..._CR23`.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_CR23
import Definitions.Def_LinearSetReconciliation327_Main_DecoderLemmas
/-!
# `BlkContracts`: the per-block run contracts of Theorem 6.5's conjunct 6

Theorem 6.5's conjunct-6 assembly (`conj6_assembly`) is conditional on exactly two hypotheses: the
per-block contract `UpBlkSem` supplied by Theorem 5.1's export (`hUp`), and the same contract
supplied by Proposition 2.3's export for the composite's last (`CR`) block (`hCr`).  This bundle
publishes that vocabulary — `UpBlkSem`, `UpChildSem`, the register-free variant `CrSem` and the
projection `upBlkSem_to_crSem` — together with the machine-checked facts about 2.3's block that
plainly contradict it:

* `cr23_progUpPre_third` / `cr23_iTbl_r3`: the prologue's third instruction is `iTbl r3 r1`, i.e. it
  *writes* `r3`, whereas `UpBlkSem` concludes `out.regs 3 = s.regs 3` (`upBlkSem_r3_frame`);
* `cr23_payStart_regs15` / `cr23_payStart_regs1`: 2.3's start state `payStart` has `r15 = 0` and
  `r1 = 0`, while the contract's premises want `r15 = β` and the `det` window at `r1 = δ`.

The declarations are copied verbatim from the accepted development's contract layer
(`Definitions.Def_…_Top65Up` §U4 and `Definitions.Def_…_Conj6Asm` §H); nothing here is new
mathematics.  `Definitions.Def_…_CR23` supplies 2.3's program and `payStart`, and
`Definitions.Def_…_DecoderLemmas` supplies the machine (`Stmt`, `At`, `step`, `packMem`, `wordsOf`).
-/

set_option autoImplicit false

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

noncomputable section

/-- `UpBlkSem Sup E T Hs` is the run contract of *one* block: `Sup` compiled at an arbitrary base,
started at that base with `r14` the `det` base, `r15` the payload word base and `r0` the coordinate,
run in an environment whose `det` agrees with the block's table on the block's `Bw` addresses.  It
must reach `base + Sup.len`, XOR `Hs (single i 1)` into the payload words `[β, β + wordsOf E.W Ms)`,
leave every other address alone (two-sided frame), and preserve `r0`–`r4` (the dispatcher's loop
counter, bound, stride and base-table pointer). -/
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

/-- `UpBlkSem` without the five register-preservation conjuncts: what a block that is *last* in the
programme has to satisfy.  `UpBlkSem` itself cannot be met by 2.3's block, because it overwrites
`r3` (`cr23_upBlockSem_obstruction`). -/
def CrSem (Sup : Stmt) (E : RAMEnv) (T : ℝ) {N Ms : ℕ}
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
      (∀ a, a < β ∨ β + wordsOf E.W Ms ≤ a → out.mem a = s.mem a)

/-- Every `UpBlkSem` is a `CrSem`. -/
theorem upBlkSem_to_crSem {Sup : Stmt} {E : RAMEnv} {T : ℝ} {N Ms : ℕ}
    {Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)}
    (h : UpBlkSem Sup E T Hs) : CrSem Sup E T Hs := by
  intro G base δ β Bw dt y i s hAt hpc hfit hdet h14 h15 h0 hmem
  obtain ⟨k, out, hk, hstep, hpc', hpay, hframe, -⟩ :=
    h G base δ β Bw dt y i s hAt hpc hfit hdet h14 h15 h0 hmem
  exact ⟨k, out, hk, hstep, hpc', hpay, hframe⟩

/-! ## 2.3's block against the register clauses -/

/-- 2.3's start state, at its published statement: `r15 = 0`. -/
theorem cr23_payStart_regs15 (W : ℕ) {M : ℕ} (β : ℕ) (y : Fin M → ZMod 2) (i : ℕ) :
    (payStart W β y i).regs 15 = 0 := rfl

/-- 2.3's start state leaves `r1` at `0`, which its prologue *reads* (`iTbl r3 r1`). -/
theorem cr23_payStart_regs1 (W : ℕ) {M : ℕ} (β : ℕ) (y : Fin M → ZMod 2) (i : ℕ) :
    (payStart W β y i).regs 1 = 0 := rfl

/-- 2.3's prologue *writes* `r3`: `iTbl r3 r1` is its third instruction. -/
theorem cr23_progUpPre_third : progUpPre[2]? = some (iTbl r3 r1) := rfl

/-- Executing `iTbl r3 r1` overwrites `r3` by a table value. -/
theorem cr23_iTbl_r3 (E : RAMEnv) (s : RAMState) :
    (execInstr (iTbl r3 r1) E s).regs 3 = E.det (s.regs 1) % 2 ^ E.W := rfl

/-- `UpBlkSem`'s conclusion includes `r3`-preservation for the *arbitrary* starting value
`s.regs 3`: this is the clause 2.3's block cannot meet, because its third instruction writes
`r3` (`cr23_progUpPre_third`, `cr23_iTbl_r3`). -/
theorem upBlkSem_r3_frame {Sup : Stmt} {E : RAMEnv} {T : ℝ} {N Ms : ℕ}
    {Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)}
    (h : UpBlkSem Sup E T Hs)
    (G : Program) (base δ β Bw : ℕ) (dt : ℕ → ℕ) (y : Fin Ms → ZMod 2) (i : Fin N)
    (s : RAMState)
    (hAt : At G base (Sup.compile base)) (hpc : s.pc = base)
    (hfit : δ + Bw ≤ 2 ^ E.W) (hdet : ∀ a < Bw, E.det (δ + a) = dt a)
    (h14 : s.regs 14 = δ) (h15 : s.regs 15 = β) (h0 : s.regs 0 = i.val)
    (hmem : ∀ q < wordsOf E.W Ms, s.mem (β + q) = packMem E.W y q) :
    ∃ (k : ℕ) (out : RAMState), (k : ℝ) ≤ T ∧ (step G E)^[k] s = out ∧
      out.pc = base + Sup.len ∧ out.regs 3 = s.regs 3 := by
  obtain ⟨k, out, hk, hstep, hpc', -, -, -, -, -, hr3, -⟩ :=
    h G base δ β Bw dt y i s hAt hpc hfit hdet h14 h15 h0 hmem
  exact ⟨k, out, hk, hstep, hpc', hr3⟩

end

end LinearSetReconciliation327.Main


