-- Prove2me | Definitions.Def_Musl_ExternHooks
-- name    : Musl_ExternHooks
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-24T16:55:54.160828+00:00
-- url     : https://prove2.me/theorems/513547f7-bc1f-4d66-97b2-c179ed8421c0
-- title:
--   DeepMind's contracts for C library calls from verified AArch64 code — cExtern, memcpy, memmove, memset, bcmp hooks
-- statement:
--   Contracts that a C library function called by verified code must meet, for use as hypotheses: verified code calls a function outside the verified object through a hook, and a hook `f` meets a contract `spec` when `HookOk f spec` (bundle `Arm64_Spec_Hoare`). From google-deepmind/code-verification (Apache License 2.0): the definitions section of [VerifiedLibraries/Musl/Proofs/CryptoHooks.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/VerifiedLibraries/Musl/Proofs/CryptoHooks.lean) and the abbreviation `stackAt` from `ProofLib/SepLogic/Stack.lean`, with names unchanged.
--
--   `cExtern regs pre post` is a contract whose precondition is the register condition `regs`, the memory `pre`, and `externStack` = 4096 bytes of stack below the caller's stack pointer (`stackAt sp 4096`, the bytes from $sp - 4096$ to $sp$), and whose postcondition is `post` with those stack bytes still owned. With the return conditions of `HookOk`, the hook returns to `x30` with `sp` and the callee-saved registers preserved. Its instances here are `cryptoMemcpySpec`, `cryptoMemcpyROSpec`, `cryptoMemmoveSpec`, `cryptoMemsetSpec`, `cryptoBcmpSpec` and `cryptoBcmpROSpec`, stated with the byte models of the bundle `Musl_StringContracts`. The upstream file's last two abbreviations (`cryptoBcmpPreservingSpec`, `cryptoBcmpROPreservingSpec`) are left out because they use a helper from its proofs. The "MODIFIED for prove2.me" notice states this; the module docstring and the imports are new.
-- source:
--   Google DeepMind, code-verification (arm64-semantics), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, VerifiedLibraries/Musl/Proofs/CryptoHooks.lean (cExtern and the crypto*Spec hook contracts) and ProofLib stackAt, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/VerifiedLibraries/Musl/Proofs/CryptoHooks.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's code-verification, commit 8c8d371f): this bundle
collects two excerpts, unchanged: the abbreviation `ProofLib.stackAt` from
`ProofLib/SepLogic/Stack.lean`, and the definitions section of
`VerifiedLibraries/Musl/Proofs/CryptoHooks.lean` (its external C hook contracts `externStack`,
`cExtern`, `cryptoMemcpySpec`, `cryptoMemcpyROSpec`, `cryptoMemmoveSpec`, `cryptoMemsetSpec`,
`cryptoBcmpSpec`, `cryptoBcmpROSpec`), without its last two abbreviations
(`cryptoBcmpPreservingSpec`, `cryptoBcmpROPreservingSpec`, which use a proof-file helper). The proofs
that follow upstream are not part of a definitions bundle; this header, the module docstring and the imports are new.
-/

module

public import Definitions.Def_Musl_StringContracts

/-!
# External C hook contracts

Contracts for calls from verified code to C library functions that are not part of the verified
object (`externs` hooks, `Step.externHook`): a hook `f` meets contract `spec` when
`HookOk f spec` (`Definitions.Def_Arm64_Spec_Hoare`). Each contract lets the callee use
`externStack` bytes of stack below the caller's stack pointer.
-/

@[expose] public section

namespace ProofLib

open Arm64

/-- `n` bytes of stack below `sp` (`memRegion (sp - n) n`). -/
abbrev stackAt (sp : BitVec 64) (n : Nat) : SepProp :=
  memRegion (sp - BitVec.ofNat 64 n) n

end ProofLib

namespace VerifiedLibraries.Musl

open Arm64 ProofLib

/-! ## `crypto-verification` (`cExtern`) hook specifications -/

/-- Default stack allowance (`4096` bytes) for external C hooks in `crypto-verification`. -/
abbrev externStack : Nat := 4096

/-- External C hook wrapper for `crypto-verification`: pairs register preconditions `regs x s0`,
    spatial precondition `pre x`, and `stackAt s0.sp externStack` with postcondition
    `post x sf ∗ stackAt s0.sp externStack`. -/
def cExtern {α : Type} (regs : α → State → Prop) (pre : α → SepProp)
    (post : α → State → SepProp) : Spec α where
  pre x s0 := ⌜regs x s0⌝ ∗ pre x ∗ stackAt s0.sp externStack
  post x s0 sf := post x sf ∗ stackAt s0.sp externStack

/-- `crypto-verification`'s `memcpySpec` (`src ↦ₛ bs`). -/
def cryptoMemcpySpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  cExtern
    (fun (dst, src, bs) s =>
      s.readReg64 .x0 = dst ∧ s.readReg64 .x1 = src ∧
      s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (fun (dst, src, bs) => memRegion dst bs.length ∗ (src ↦ₛ bs))
    (fun (dst, src, bs) sf => ⌜sf.readReg64 .x0 = dst⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ₛ bs))

/-- `crypto-verification`'s `memcpyROSpec` (`src ↦ᵣ bs`). -/
def cryptoMemcpyROSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  cExtern
    (fun (dst, src, bs) s =>
      s.readReg64 .x0 = dst ∧ s.readReg64 .x1 = src ∧
      s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (fun (dst, src, bs) => memRegion dst bs.length ∗ (src ↦ᵣ bs))
    (fun (dst, src, bs) sf => ⌜sf.readReg64 .x0 = dst⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ᵣ bs))

/-- `crypto-verification`'s `memmoveSpec` (with non-wrapping buffer bounds
    `base.toNat + buf.length ≤ 2 ^ 64 ∧ buf.length < 2 ^ 63`). -/
def cryptoMemmoveSpec : Spec (BitVec 64 × List (BitVec 8) × Nat × Nat × Nat) :=
  cExtern
    (fun (base, buf, dst, src, len) s =>
      s.readReg64 .x0 = base + BitVec.ofNat 64 dst ∧
      s.readReg64 .x1 = base + BitVec.ofNat 64 src ∧
      s.readReg64 .x2 = BitVec.ofNat 64 len ∧
      dst + len ≤ buf.length ∧ src + len ≤ buf.length ∧
      base.toNat + buf.length ≤ 2 ^ 64 ∧ buf.length < 2 ^ 63)
    (fun (base, buf, _, _, _) => base ↦ₛ buf)
    (fun (base, buf, dst, src, len) sf =>
      ⌜sf.readReg64 .x0 = base + BitVec.ofNat 64 dst⌝ ∗
      (base ↦ₛ moveBytes buf dst src len))

/-- `crypto-verification`'s `memsetSpec`. -/
def cryptoMemsetSpec : Spec (BitVec 64 × BitVec 8 × Nat) :=
  cExtern
    (fun (p, c, n) s =>
      s.readReg64 .x0 = p ∧ (s.readReg32 .x1).truncate 8 = c ∧
      (s.readReg64 .x2).toNat = n)
    (fun (p, _, n) => memRegion p n)
    (fun (p, c, n) sf =>
      ⌜sf.readReg64 .x0 = p⌝ ∗ (p ↦ₛ List.replicate n c))

/-- `crypto-verification`'s `bcmpSpec` (`p ↦ₛ bs`, `q ↦ₛ cs`). -/
def cryptoBcmpSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) :=
  cExtern
    (fun (p, q, bs, cs) s =>
      s.readReg64 .x0 = p ∧ s.readReg64 .x1 = q ∧
      s.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧ cs.length = bs.length)
    (fun (p, q, bs, cs) => (p ↦ₛ bs) ∗ (q ↦ₛ cs))
    (fun (p, q, bs, cs) sf =>
      ⌜(sf.readReg32 .x0 = 0#32 ↔ bs = cs)⌝ ∗ (p ↦ₛ bs) ∗ (q ↦ₛ cs))

/-- `crypto-verification`'s read-only `bcmpROSpec` (`p ↦ᵣ bs`, `q ↦ᵣ cs`). -/
def cryptoBcmpROSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) :=
  cExtern
    (fun (p, q, bs, cs) s =>
      s.readReg64 .x0 = p ∧ s.readReg64 .x1 = q ∧
      s.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧ cs.length = bs.length)
    (fun (p, q, bs, cs) => (p ↦ᵣ bs) ∗ (q ↦ᵣ cs))
    (fun (p, q, bs, cs) sf =>
      ⌜(sf.readReg32 .x0 = 0#32 ↔ bs = cs)⌝ ∗ (p ↦ᵣ bs) ∗ (q ↦ᵣ cs))

end VerifiedLibraries.Musl


