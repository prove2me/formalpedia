-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintDecAtModel20261122
-- name    : LinearSetReconciliation327_Main_HintDecAtModel20261122
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T08:47:02.837628+00:00
-- url     : https://prove2.me/theorems/dc2e2ede-a982-4856-b769-994cb9d5f566
-- title:
--   Theorem 5.1's decoder entry `det[3]`, the relocation wrapper, and the `DownBlkSem` contract
-- statement:
--   Theorem 5.1's word-RAM decoder locates its deterministic table through a single **absolute** entry, $\mathrm{det}[3]$.  Its prologue executes $r_3\leftarrow 3$, $r_6\leftarrow \mathrm{det}[r_3]$, so $r_6$ becomes the *header address* $h=\mathrm{det}[3]$; every later table access of the decoder is either $\mathrm{det}(h+k)$ or at a pointer value stored in the table (the dispatch table $\mathrm{det}(h+12)$, row descriptors, and so on).  The header's slots are therefore of three different kinds: slot $12$ is a $\mathrm{det}$ **index**, slots $9,11,14,15$ are ordinary **memory addresses**, and slots $10,13$ are **scalars**; a single global shift can rebase none of them uniformly.
--
--   The bundle defines the naive relocation wrapper $\mathrm{hintDecAt}=\mathrm{prefix}\cdot\mathrm{prologue}\cdot\mathrm{body}$, where the prefix writes $3+\delta$ into $r_3$ and $\beta+\mathrm{wordsOf}$ into $r_1$ (the caller's table base and payload base), and proves the **entry obstruction**: after the prefix and the prologue's own $r_3\leftarrow 3$ and $r_6\leftarrow\mathrm{det}[3]$, the header register is still $\mathrm{det}[3]$, whatever $\delta$ was placed in $r_{14}$ or $r_3$.  Equivalently, a prefix cannot make the decoder read $\mathrm{det}(\delta+3)$; the body must be edited at its $\mathrm{det}[3]$ reads (exactly as Proposition 2.3's `cr23UpPreAt` inserts $r_5\leftarrow r_5+\delta$ *after* its table read, rather than merely prefixing).
--
--   The bundle also defines the per-block contract `DownBlkSem` (pinned table width $B_w$, the $\mathrm{det}$ base in $r_{14}$, the payload base in $r_{15}$, the payload-word fit, and a two-sided frame) and proves that its $\beta=0$ instance at $\delta=0$, $\mathrm{dt}=\mathrm{det}$ and the standard `decoderStart` state reduces to Theorem 5.1's own halting conjunct, so the contract is non-vacuous in the intended direction.  It also proves that the literal contract is false at $T=0$ for every positive-length program: the budget must be pinned positive, just as the table must be pinned.
-- source:
--   Theorem 5.1 and Theorem 6.5 of arXiv:2611.11409 (Liu--Xu--Yang--Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*).  The prologue is copied byte for byte from `hintRootHintArgs` of the verified 5.1 development (Definitions.Def_LinearSetReconciliation327_Main_HintRootHeader20261120), which is not a published platform Definition; the contract shape follows Proposition 2.3's `CrSemAtW`.

import Definitions.Def_LinearSetReconciliation327_Main_DecoderLemmas
/-!
# `HintDecAtModel`: 5.1's decoder prologue and the `det[3]` entry obstruction

Theorem 5.1's decoder `hintNativeRoot` is not a published `Definitions` bundle (the `Hint*` native
program chain is local; `theorem_5_1` is still an Open platform node), so this file carries its
**entry prologue byte for byte** and proves the obstruction against a generic continuation `body`.

The prologue is

```
hintRootHintArgs = [imm 3 3, qDet 6 3, imm 3 0, add 0 1 3, add 1 2 3]
```

so the first table access is the **absolute** entry `E.det 3`, stored in `r6` as the *header*
address; every further read of 5.1's decoder is `E.det (header + k)` or at a pointer value stored
in the table.  Consequently a prefix such as

```
hintDecPre = [imm r3 3, add r3 r3 r14, add r1 r1 r15]
```

(which puts `3 + δ` in the entry register `r3` and `β + wordsOf` in the hint-address register
`r1`) is overwritten by the prologue's own `imm 3 3`; the decoder still reads `E.det 3`.  This is
the precise reason why Proposition 2.3's precedent `cr23UpPreAt` is *not* a pure prefix: it
inserts `iAdd r5 r5 r14` **after** the table read.

The file also defines the task's `DownBlkSem` contract and proves its `β = 0` reduction to 5.1's
`HaltsWithin` conjunct (non-vacuity) and its `T = 0` refutation (the budget must be pinned
positive).
-/
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

/-! ## 1. The entry prologue, byte-identical to 5.1's `hintRootHintArgs` -/

/-- Theorem 5.1's decoder prologue: `r3 := 3`, `r6 := E.det 3`, `r0 := r1`, `r1 := r2`. -/
def hintRootHintArgs : List Instr :=
  [Instr.imm (3 : Fin 16) 3, Instr.qDet (6 : Fin 16) (3 : Fin 16), Instr.imm (3 : Fin 16) 0,
   Instr.add (0 : Fin 16) (1 : Fin 16) (3 : Fin 16), Instr.add (1 : Fin 16) (2 : Fin 16) (3 : Fin 16)]

@[simp] theorem hintRootHintArgs_length : hintRootHintArgs.length = 5 := rfl

/-- The first two instructions of the prologue. -/
theorem hintRootHintArgs_head :
    hintRootHintArgs[0]? = some (Instr.imm (3 : Fin 16) 3) ∧
    hintRootHintArgs[1]? = some (Instr.qDet (6 : Fin 16) (3 : Fin 16)) := ⟨rfl, rfl⟩

/-- The prologue reads the absolute entry `det[3]` into `r6`. -/
theorem hintRootHintArgs_det3 (E : RAMEnv) (s : RAMState) (hW : 3 < 2 ^ E.W) :
    (runBlock hintRootHintArgs E s).regs 6 = E.det 3 % 2 ^ E.W := by
  simp [hintRootHintArgs, runBlock, execInstr, Nat.mod_eq_of_lt hW]

/-! ## 2. The naive relocation prefix and the model wrapper -/

/-- `r3 := 3 + δ` and `r1 := β + wordsOf`. -/
def hintDecPre : List Instr :=
  [iImm (3 : Fin 16) 3, iAdd (3 : Fin 16) (3 : Fin 16) (14 : Fin 16),
   iAdd (1 : Fin 16) (1 : Fin 16) (15 : Fin 16)]

@[simp] theorem hintDecPre_length : hintDecPre.length = 3 := rfl

/-- The model wrapper: the naive prefix, 5.1's prologue, then any continuation. -/
def hintDecAtModel (body : Stmt) : Stmt :=
  .seq (.code hintDecPre) (.seq (.code hintRootHintArgs) body)

@[simp] theorem hintDecAtModel_len (body : Stmt) :
    (hintDecAtModel body).len = 3 + (5 + body.len) := rfl

/-- The compiled model wrapper at an arbitrary base. -/
theorem hintDecAtModel_compile_eq (body : Stmt) (base : ℕ) :
    (hintDecAtModel body).compile base = hintDecPre ++ (hintRootHintArgs ++ body.compile (base + 8)) :=
  rfl

/-! ## 3. `At` plumbing -/

theorem At.take' {P : Program} {a : ℕ} {A B : List Instr} (h : At P a (A ++ B)) : At P a A := by
  intro r hr
  have h' := h r (by simp only [List.length_append]; omega)
  rwa [List.getElem?_append_left hr] at h'

/-! ## 4. The entry obstruction -/

/-- **The entry obstruction.**  Start the model wrapper at any state whose `pc` is the compilation
base.  After the three prefix instructions and the prologue's first two instructions, `r6` is
`E.det 3 % 2^E.W` — the *absolute* `det[3]` entry, independent of `s.regs 14` and of the `δ` the
prefix put in `r3`, because the prologue's own `imm 3 3` overwrites `r3` before its `qDet`. -/
theorem hintDecAtModel_entry_absolute (body : Stmt) :
    ∀ (G : Program) (base : ℕ) (E : RAMEnv) (s : RAMState),
      At G base ((hintDecAtModel body).compile base) → s.pc = base → 3 < 2 ^ E.W →
      ((step G E)^[hintDecPre.length + 2] s).regs 6 = E.det 3 % 2 ^ E.W := by
  intro G base E s hAt hpc hW
  have hAt' : At G base (hintDecPre ++ (hintRootHintArgs ++ body.compile (base + 8))) := by
    rwa [hintDecAtModel_compile_eq] at hAt
  have hpreAt : At G base hintDecPre := (At.append.mp hAt').1
  have hrest : At G (base + hintDecPre.length) (hintRootHintArgs ++ body.compile (base + 8)) :=
    (At.append.mp hAt').2
  have hhead : At G (base + 3) hintRootHintArgs := by
    simpa [hintDecPre_length] using At.take' hrest
  have hrun : (step G E)^[hintDecPre.length] s = runBlock hintDecPre E s :=
    iterate_runBlock_of_at G E hintDecPre s (by rw [hpc]; exact hpreAt)
      (by simp [hintDecPre, NoBranch, Instr.NoBranchI])
  let t := runBlock hintDecPre E s
  have htpc : t.pc = base + 3 := by
    dsimp [t]
    rw [runBlock_pc hintDecPre E s (by simp [hintDecPre, NoBranch, Instr.NoBranchI]), hpc,
      hintDecPre_length]
  have h1 : G[t.pc]? = some (Instr.imm (3 : Fin 16) 3) := by
    have h := hhead 0 (by simp [hintRootHintArgs])
    simpa [hintRootHintArgs, htpc] using h
  have hstep1 : step G E t = execInstr (Instr.imm (3 : Fin 16) 3) E t :=
    step_eq_execInstr G E t _ h1
  let t1 := step G E t
  have ht1pc : t1.pc = base + 4 := by
    dsimp [t1]
    rw [hstep1]
    simp [execInstr, htpc]
  have h2 : G[t1.pc]? = some (Instr.qDet (6 : Fin 16) (3 : Fin 16)) := by
    have h := hhead 1 (by simp [hintRootHintArgs])
    simpa [hintRootHintArgs, ht1pc] using h
  have hstep2 : step G E t1 = execInstr (Instr.qDet (6 : Fin 16) (3 : Fin 16)) E t1 :=
    step_eq_execInstr G E t1 _ h2
  have ht1r3 : t1.regs 3 = 3 := by
    dsimp [t1]
    rw [hstep1]
    simp [execInstr, Nat.mod_eq_of_lt hW]
  have h3 : (execInstr (Instr.qDet (6 : Fin 16) (3 : Fin 16)) E t1).regs 6 =
      E.det 3 % 2 ^ E.W := by
    simp [execInstr, ht1r3]
  have h2t : (step G E)^[2] t = step G E (step G E t) := by
    rw [show (2 : ℕ) = Nat.succ 1 from rfl, Function.iterate_succ_apply', Function.iterate_one]
  calc
    ((step G E)^[hintDecPre.length + 2] s).regs 6
        = ((step G E)^[2] t).regs 6 := by
          rw [show hintDecPre.length + 2 = 2 + hintDecPre.length by omega,
            Function.iterate_add_apply, hrun]
    _ = (execInstr (Instr.qDet (6 : Fin 16) (3 : Fin 16)) E t1).regs 6 := by
          rw [h2t]
          change (step G E t1).regs 6 = _
          rw [hstep2]
    _ = E.det 3 % 2 ^ E.W := h3

/-- The result does not depend on the `det` base the caller put in `r14`. -/
theorem hintDecAtModel_entry_ignores_detBase (body : Stmt) (G : Program) (base : ℕ)
    (E : RAMEnv) (s s' : RAMState) (hW : 3 < 2 ^ E.W)
    (hAt : At G base ((hintDecAtModel body).compile base))
    (hpc : s.pc = base) (hpc' : s'.pc = base) :
    ((step G E)^[hintDecPre.length + 2] s).regs 6 =
      ((step G E)^[hintDecPre.length + 2] s').regs 6 := by
  rw [hintDecAtModel_entry_absolute body G base E s hAt hpc hW,
    hintDecAtModel_entry_absolute body G base E s' hAt hpc' hW]

/-! ## 5. The `DownBlkSem` contract, its `β = 0` reduction, and its `T = 0` refutation -/

/-- The task's per-block decoder contract. -/
def DownBlkSem (Sdec : Stmt) (E : RAMEnv) (T : ℝ) (Bw : ℕ) {N Ms : ℕ}
    (Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)) : Prop :=
  ∀ (G : Program) (base δ β : ℕ), β + wordsOf E.W Ms ≤ 2 ^ E.W →
  ∀ (dt : ℕ → ℕ) (y : Fin Ms → ZMod 2) (J : List ℕ) (s : RAMState),
    At G base (Sdec.compile base) → s.pc = base → δ + Bw ≤ 2 ^ E.W →
    (∀ a < Bw, E.det (δ + a) = dt a) →
    s.regs 14 = δ → s.regs 15 = β →
    (∀ q < wordsOf E.W Ms, s.mem (β + q) = packMem E.W y q) →
    ∃ (k : ℕ) (out : RAMState), (k : ℝ) ≤ T ∧ (step G E)^[k] s = out ∧
      out.pc = base + Sdec.len ∧
      (∀ a, a < β ∨ β + wordsOf E.W Ms ≤ a → out.mem a = s.mem a)

/-- **The `β = 0` reduction.**  At `base = δ = β = 0`, `dt = E.det` and `s = decoderStart`, the
contract yields 5.1's own `HaltsWithin` conjunct. -/
theorem downBlkSem_betaZero {Sdec : Stmt} {E : RAMEnv} {T : ℝ} {Bw N Ms : ℕ}
    {Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)}
    (h : DownBlkSem Sdec E T Bw Hs) (hBw : Bw ≤ 2 ^ E.W)
    (hfit : wordsOf E.W Ms ≤ 2 ^ E.W)
    (y : Fin Ms → ZMod 2) (J : List ℕ) :
    ∃ s', HaltsWithin (Sdec.compile 0 ++ [Instr.halt]) E T (decoderStart E.W y J) s' := by
  let G : Program := Sdec.compile 0 ++ [Instr.halt]
  have hAt : At G 0 (Sdec.compile 0) := by
    intro r hr
    simpa [G] using List.getElem?_append_left (l₁ := Sdec.compile 0) (l₂ := [Instr.halt])
      (by simpa using hr)
  have hpc : (decoderStart E.W y J).pc = 0 := rfl
  have h14 : (decoderStart E.W y J).regs 14 = 0 := rfl
  have h15 : (decoderStart E.W y J).regs 15 = 0 := rfl
  have hmem : ∀ q < wordsOf E.W Ms, (decoderStart E.W y J).mem (0 + q) = packMem E.W y q := by
    intro q hq
    simp [decoderStart, initState, hintMem, hq]
  obtain ⟨k, out, hk, hstep, hpcOut, -⟩ :=
    h G 0 0 0 (by simpa using hfit) (fun a => E.det a) y J (decoderStart E.W y J)
      hAt hpc (by simpa using hBw) (fun a _ => by rw [Nat.zero_add]) h14 h15 hmem
  have hlen : (Sdec.compile 0).length = Sdec.len := Stmt.length_compile Sdec 0
  have hhalt : G[out.pc]? = some Instr.halt := by
    rw [hpcOut, show 0 + Sdec.len = Sdec.len by omega]
    rw [List.getElem?_append_right (by omega : (Sdec.compile 0).length ≤ Sdec.len)]
    simp [hlen]
  have hHalted : Halted G out := by
    simp [Halted, hhalt]
  exact ⟨out, k, hk, hstep, hHalted⟩

/-- **The `T = 0` refutation.**  A positive-length program cannot reach `base + len` in zero
steps, so the contract must pin `0 < T`. -/
theorem downBlkSem_T_zero_false {Sdec : Stmt} {E : RAMEnv} {Bw N Ms : ℕ}
    {Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)}
    (hlen : 0 < Sdec.len) (hBw : Bw ≤ 2 ^ E.W) (hfit : wordsOf E.W Ms ≤ 2 ^ E.W) :
    ¬ DownBlkSem Sdec E 0 Bw Hs := by
  intro h
  let G : Program := Sdec.compile 0 ++ [Instr.halt]
  let s : RAMState := initState (fun _ => 0) 0 0 0
  have hAt : At G 0 (Sdec.compile 0) := by
    intro r hr
    simpa [G] using List.getElem?_append_left (l₁ := Sdec.compile 0) (l₂ := [Instr.halt])
      (by simpa using hr)
  have hmem : ∀ q < wordsOf E.W Ms, s.mem (0 + q) =
      packMem E.W (0 : Fin Ms → ZMod 2) q := by
    intro q _
    simp [s, initState, packMem]
  obtain ⟨k, out, hk, hstep, hpcOut, -⟩ :=
    h G 0 0 0 (by simpa using hfit) (fun a => E.det a) (0 : Fin Ms → ZMod 2) [] s
      hAt rfl (by simpa using hBw) (fun a _ => by rw [Nat.zero_add]) rfl rfl hmem
  have hk0 : k = 0 := by
    have hk' : (k : ℝ) = 0 := le_antisymm hk (by positivity)
    exact_mod_cast hk'
  subst k
  simp only [Function.iterate_zero_apply] at hstep
  subst out
  simp only [s, initState] at hpcOut
  omega

/-- **The published obstruction package** (model form). -/
theorem hintDecAtModel_obstruction (body : Stmt) :
    (∀ (G : Program) (base : ℕ) (E : RAMEnv) (s : RAMState),
      At G base ((hintDecAtModel body).compile base) → s.pc = base → 3 < 2 ^ E.W →
      ((step G E)^[hintDecPre.length + 2] s).regs 6 = E.det 3 % 2 ^ E.W) ∧
    (∀ {Sdec : Stmt} {E : RAMEnv} {T : ℝ} {Bw N Ms : ℕ}
      {Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)},
      DownBlkSem Sdec E T Bw Hs → Bw ≤ 2 ^ E.W → wordsOf E.W Ms ≤ 2 ^ E.W →
      ∀ (y : Fin Ms → ZMod 2) (J : List ℕ),
        ∃ s', HaltsWithin (Sdec.compile 0 ++ [Instr.halt]) E T (decoderStart E.W y J) s') ∧
    (∀ {Sdec : Stmt} {E : RAMEnv} {Bw N Ms : ℕ}
      {Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)},
      0 < Sdec.len → Bw ≤ 2 ^ E.W → wordsOf E.W Ms ≤ 2 ^ E.W →
      ¬ DownBlkSem Sdec E 0 Bw Hs) :=
  ⟨hintDecAtModel_entry_absolute body,
   fun h hBw hfit y J => downBlkSem_betaZero h hBw hfit y J,
   fun hlen hBw hfit => downBlkSem_T_zero_false hlen hBw hfit⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDecAtModel_entry_absolute
#print axioms LinearSetReconciliation327.Main.downBlkSem_betaZero
#print axioms LinearSetReconciliation327.Main.downBlkSem_T_zero_false
#print axioms LinearSetReconciliation327.Main.hintDecAtModel_obstruction


