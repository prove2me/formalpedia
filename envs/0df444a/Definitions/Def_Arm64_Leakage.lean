-- Prove2me | Definitions.Def_Arm64_Leakage
-- name    : Arm64_Leakage
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-25T23:56:23.609173+00:00
-- url     : https://prove2.me/theorems/14ceec5c-a685-59b3-aea2-cc53c31cc7d1
-- title:
--   Constant-time execution on the AArch64 semantics: the leakage model of constant-time programming
-- statement:
--   A leakage model for the AArch64 semantics of google-deepmind/code-verification (republished as the `Def_Arm64_*` bundles), and the judgment that a subroutine is constant-time in it. The model is the one of constant-time programming as formalized by Almeida, Barbosa, Barthe, Dupressoir and Emmi, *Verifying Constant-Time Implementations*, USENIX Security 2016, Section 3 (p. 58, Definition 1: “A program is secure when all of its initially $X_{\mathrm i}$-equivalent and finally $X_{\mathrm o}$-equivalent executions are indistinguishable.”), with the leakage of control flow (their Example 1, p. 57), of memory access addresses (Example 2) and of the operands of division (Example 3), at the level of machine instructions; Barthe, Betarte, Campo, Luna and Pichardie, *System-level non-interference for constant-time cryptography*, CCS 2014, is the formal precedent for a machine-level model.
--
--   **Observations.**
--   - `Obs` is a pair: the address of the instruction executed, and a list of 64-bit values it reveals.
--   - `leakedValues i s` is what instruction `i` reveals in state `s`: for each memory access, its address as the semantics computes it (`evalAddrMode` for the addressing-mode loads and stores, including pairs and SIMD registers and the prefetch `PRFM`; `pc + offset` for the literal loads and literal prefetch; base register plus offset for the non-temporal pairs and `LDAPUR`/`STLUR`; the base register for acquire/release, exclusive and atomic accesses, the SIMD structure loads and stores, and the register operand of `DC ZVA`, not rounded down to its block); for `UDIV` and `SDIV` both operands, read at the instruction's width and zero-extended; nothing for every other instruction. Prefetches reveal their address although the semantics executes them as no-ops, since on hardware they touch the cache.
--   - `hookName? prog pc` is the name of the hooked function whose entry point is `pc`, found as the semantics finds the hook (the first extern stub at that offset with a hook, else the first defined symbol there with an override). `args k s` is the list of the first `k` argument registers `x0, …, x(k−1)`.
--   - `stepObs prog arity s` is the observation of the step from `s`: at a hooked function `n`, the address and its `arity n` arguments; otherwise the address and `leakedValues` of the instruction fetched there (from memory, as `Step` fetches), or nothing if none can be fetched.
--
--   **Runs and equivalence.**
--   - `ObsUntil prog arity stop s t s'`: execution of `prog` by `Arm64.Step` from `s` to `s'`, taking a step only from a state where `stop` does not hold, and `t` lists the observation of each step taken, in order. It may stop anywhere, so it describes every finite prefix of a run up to `stop`.
--   - `ObsIncluded prog arity stop₁ stop₂ s₁ s₂`: for every such prefix from `s₁` with observations `t` ending in `f₁`, there is one from `s₂` with the same observations ending in some `f₂`, with `stop₁ f₁` exactly when `stop₂ f₂`. `ObsEquiv` is inclusion both ways. Since `Step` is deterministic, this says the two runs reveal the same sequence of observations and stop at the same step; a run that halts or faults stops making steps without satisfying `stop`, and is compared as a finite run.
--   - `SameExceptMem s₁ s₂`: the two states are equal in every field except memory (registers, SIMD registers, stack pointer, program counter, flags, the other system fields).
--
--   **The judgment.** `ct_subroutine_ok prog arity entry_pc spec Pub` says: for all ghost values `x₁ x₂` with `Pub x₁ x₂`, all frames `R₁ R₂`, and all states `s₁ s₂` that are AAPCS entries at `entry_pc` (`AapcsEntry`), have the code of `prog` loaded, whose memories satisfy `spec.pre xᵢ sᵢ ∗ Rᵢ`, and that differ at most in memory, the runs from `s₁` and `s₂` up to their return (`SubroutineStop s₁`, `SubroutineStop s₂`) are `ObsEquiv`. The registers are thus public; secrets live in memory, and `Pub` says which parts of the ghost data are public. The frames may differ arbitrarily. `spec.post` is not used.
-- source:
--   J. B. Almeida, M. Barbosa, G. Barthe, F. Dupressoir, M. Emmi, "Verifying Constant-Time Implementations", 25th USENIX Security Symposium (2016), pp. 53-70, ISBN 978-1-931971-32-4, https://www.usenix.org/conference/usenixsecurity16/technical-sessions/presentation/almeida, the constant-time leakage model (control flow and memory addresses; Section 3, Definition 1, p. 58, with the leakage models of Examples 1-3, p. 57), on the AArch64 semantics of Google DeepMind code-verification as republished in the Def_Arm64_* bundles

module

public import Definitions.Def_Arm64_Spec_Hoare

/-!
# Constant-time execution on the AArch64 semantics

The leakage model of constant-time programming (Almeida, Barbosa, Barthe, Dupressoir, Emmi,
*Verifying Constant-Time Implementations*, USENIX Security 2016; Barthe, Betarte, Campo, Luna,
Pichardie, *System-level non-interference for constant-time cryptography*, CCS 2014), on the
small-step semantics `Arm64.Step` (bundle `Arm64_ISA_Semantics`).

Each step reveals an observation: the address of the instruction executed, the addresses of the
memory it accesses, and the operands of a division. At a hooked function (an extern or override, `Program.externAt?`) the step
reveals the address and the function's arguments `x0, …, x(k-1)`, where `k` is the arity the caller
assigns to the function's name. A subroutine is constant-time for a precondition and a relation on
public data when two runs from entry states that differ only in memory, both meeting the
precondition, with related public data, reveal the same observations and return at the same step.
-/

@[expose] public section

namespace Leakage

open Arm64

/-- One observation: the address of the instruction executed, and the values it reveals. -/
abbrev Obs := BitVec 64 × List (BitVec 64)

/-- The value of register `r` read at width `w`, zero-extended to 64 bits. -/
def regAt (s : State) (w : RegWidth) (r : Reg) : BitVec 64 :=
  match w with
  | .W32 => (s.readReg32 r).zeroExtend 64
  | .W64 => s.readReg64 r

/-- The values instruction `i` leaks when executed in state `s`: for a memory access (loads,
stores, pairs, exclusives, atomics, SIMD structure loads and stores, prefetches, `DC ZVA`) its
address, computed as the semantics computes it (`evalAddrMode`, `pc + offset` for a literal, the base
register otherwise); for `UDIV` and `SDIV` both operands; nothing for any other instruction. -/
def leakedValues (i : Instr) (s : State) : List (BitVec 64) :=
  match i with
  | .ldr _ _ _ _ a | .str _ _ a | .ldp _ _ _ _ a | .stp _ _ _ a | .prfm _ a
  | .ldrSimd _ _ a | .strSimd _ _ a | .ldpSimd _ _ _ a | .stpSimd _ _ _ a => [(evalAddrMode s a).1]
  | .ldrLit _ _ _ off | .prfmLit _ off | .ldrSimdLit _ _ off => [s.pc + off]
  | .ldnp _ rn _ _ off | .stnp _ rn _ _ off | .ldapurStlur _ _ rn _ off
  | .ldnpSimd _ _ _ rn off | .stnpSimd _ _ _ rn off => [s.readReg64 rn + off]
  | .ldarStlr _ _ rn _ | .ldxr _ _ rn _ | .stxr _ _ _ rn _ | .ldxp _ _ rn _ _ | .stxp _ _ _ rn _ _
  | .cas _ _ _ _ rn _ | .casp _ _ _ _ _ rn _ _ | .atomicRmw _ _ _ _ _ rn _ | .ldapr _ rn _ =>
    [s.readReg64 rn]
  | .st1SinglePost _ _ _ _ _ rn _ | .simdLdSt1Single _ _ _ _ _ _ _ rn _
  | .simdLdSt1Multi _ _ _ _ rn _ _ _ | .simdLdStMulti _ _ _ _ rn _ _ _ | .simdLd1r _ _ rn _ _ _ =>
    [s.readReg64 rn]
  | .dcZva rt => [s.readReg64 rt]
  | .dataProc2 w .UDIV _ rn rm | .dataProc2 w .SDIV _ rn rm => [regAt s w rn, regAt s w rm]
  | _ => []

/-- The name of the hooked function whose entry point is `pc`, chosen as `Program.hookAtOff?`
chooses the hook: the first extern stub at that offset with a hook, otherwise the first defined
symbol there with an override. -/
def hookName? (prog : Program) (pc : BitVec 64) : Option String :=
  let off := (pc - prog.base).toNat
  (prog.stubs.findSome? fun (n, o) => if o == off && (prog.externs n).isSome then some n else none).or
    (prog.symbols.findSome? fun (n, o) => if o == off && (prog.overrides n).isSome then some n else none)

/-- The first `k` argument registers `x0, …, x(k-1)`. -/
def args (k : Nat) (s : State) : List (BitVec 64) :=
  (List.range k).map fun i => s.readReg64 (.gpr (BitVec.ofNat 5 i))

/-- The observation of the step taken from `s`: at a hooked function named `n`, the address and
its `arity n` arguments; otherwise the address and `leakedValues` of the instruction fetched there
(nothing if none can be fetched). -/
def stepObs (prog : Program) (arity : String → Nat) (s : State) : Obs :=
  match hookName? prog s.pc with
  | some n => (s.pc, args (arity n) s)
  | none =>
    match prog.fetchMem s.mem s.pc with
    | some i => (s.pc, leakedValues i s)
    | none => (s.pc, [])

/-- Execution of `prog` from `s` to `s'` that stops as soon as `stop` holds (as `StepsUntil`),
revealing the observations `t`, one per step. -/
inductive ObsUntil (prog : Program) (arity : String → Nat) (stop : State → Prop) :
    State → List Obs → State → Prop where
  | refl (s : State) : ObsUntil prog arity stop s [] s
  | step {s₁ s₂ s₃ : State} {t : List Obs}
      (h_cont : ¬ stop s₁)
      (h_step : Step prog s₁ s₂)
      (h_rest : ObsUntil prog arity stop s₂ t s₃) :
      ObsUntil prog arity stop s₁ (stepObs prog arity s₁ :: t) s₃

/-- Every observation sequence `t` of a run from `s₁` (stopping at `stop₁`) is one of a run from
`s₂` (stopping at `stop₂`), ending in a state that has stopped exactly when the first has. -/
def ObsIncluded (prog : Program) (arity : String → Nat) (stop₁ stop₂ : State → Prop)
    (s₁ s₂ : State) : Prop :=
  ∀ t f₁, ObsUntil prog arity stop₁ s₁ t f₁ →
    ∃ f₂, ObsUntil prog arity stop₂ s₂ t f₂ ∧ (stop₁ f₁ ↔ stop₂ f₂)

/-- The runs from `s₁` and `s₂` cannot be told apart by their observations: each one's
observation sequences, and when it stops, are the other's. -/
def ObsEquiv (prog : Program) (arity : String → Nat) (stop₁ stop₂ : State → Prop)
    (s₁ s₂ : State) : Prop :=
  ObsIncluded prog arity stop₁ stop₂ s₁ s₂ ∧ ObsIncluded prog arity stop₂ stop₁ s₂ s₁

/-- `s₁` and `s₂` differ at most in memory. -/
def SameExceptMem (s₁ s₂ : State) : Prop :=
  { s₁ with mem := Memory.empty } = { s₂ with mem := Memory.empty }

/-- The subroutine of `prog` at `entry_pc` is constant-time for `spec.pre` and the public-data
relation `Pub`, with hooks revealing `arity`-many arguments: for all ghost values `x₁ x₂` with
`Pub x₁ x₂`, frames `R₁ R₂`, and entry states `s₁ s₂` that are AAPCS entries at `entry_pc` with the
code of `prog` loaded, satisfy `spec.pre xᵢ sᵢ ∗ Rᵢ`, and differ at most in memory, the runs from
`s₁` and `s₂` up to their return (`SubroutineStop`) are observationally equivalent. -/
def ct_subroutine_ok {α : Type} (prog : Program) (arity : String → Nat) (entry_pc : BitVec 64)
    (spec : Spec α) (Pub : α → α → Prop) : Prop :=
  ∀ (x₁ x₂ : α) (R₁ R₂ : SepProp) (s₁ s₂ : State),
    AapcsEntry s₁ entry_pc → AapcsEntry s₂ entry_pc →
    prog.CodeLoaded s₁.mem → prog.CodeLoaded s₂.mem →
    (s₁.mem ⊨ spec.pre x₁ s₁ ∗ R₁) → (s₂.mem ⊨ spec.pre x₂ s₂ ∗ R₂) →
    SameExceptMem s₁ s₂ → Pub x₁ x₂ →
    ObsEquiv prog arity (SubroutineStop s₁) (SubroutineStop s₂) s₁ s₂

end Leakage

end


