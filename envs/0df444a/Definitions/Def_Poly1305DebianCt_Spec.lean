-- Prove2me | Definitions.Def_Poly1305DebianCt_Spec
-- name    : Poly1305DebianCt_Spec
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-26T10:19:14.925799+00:00
-- url     : https://prove2.me/theorems/bb1de09c-bc47-5cda-893d-30657cf13e7e
-- title:
--   Constant-time judgments for Debian's libsodium Poly1305 and crypto_verify_16 on AArch64
-- statement:
--   The hypotheses on a link, the two constant-time judgments, and the precondition and public data of each function of `libsodiumDebianOnetimeauthCtLib` (bundle `Poly1305DebianCt_PlacedObj`). Constant time is `Leakage.ct_subroutine_ok` (bundle `Arm64_Leakage`). The state layout comes from the bundle `Poly1305Libsodium_Spec`, which describes the same C source: `u64At` reads a little-endian 64-bit word of a byte list, `bytesIn ro a bs` is the bytes `bs` at `a`, read-only if `ro` and owned otherwise, and `MemzeroOk` says the hook for `sodium_memzero` meets `Libc.explicitBzeroSpec`.
--
--   **Hooks and their arities.** `arity` gives the number of arguments a call of each external function reveals, its C arity: 2 for `sodium_memzero(pnt, len)`, 3 for `memset(dst, c, n)`, 2 for `randombytes_buf(buf, size)` and 0 for every other name, among them `__stack_chk_fail(void)`. `MemsetOk externs`: the hook for `memset` meets DeepMind's contract `VerifiedLibraries.Musl.cryptoMemsetSpec`.
--
--   **The stack guard.** `guardSites` is the list of offsets of the code's GOT accesses to `__stack_chk_guard`. `guardDirect pl off` says the linker relaxed the access at `off` into a direct computation of the guard's address, and `GuardUniform pl` says all accesses are relaxed or none is. `guardRes pl ga g` is the guard with value `g`, read-only, where the code reads it: the 8 bytes of `g` at the address the placement gives `__stack_chk_guard` when the accesses are relaxed, otherwise a GOT slot there holding the address `ga` and the 8 bytes of `g` at `ga`. The address `ga` is a parameter rather than hidden by an existential so that the judgments below can make it public: the code loads from `ga`, so two runs with different `ga` would reveal different addresses.
--
--   **Judgments.** Both quantify over every placement `pl` under which the library is `Placeable` and `GuardUniform pl` holds, and every hook table `externs` with `MemzeroOk externs`, `MemsetOk externs` and `Link.PlacedLib.LinkOk libsodiumDebianOnetimeauthCtLib pl externs` (two external functions at one address have the same hook, no external function lies in the code or a data object, and the data objects are disjoint from each other and from the code). `preSpec pre` is the `Spec` with precondition `pre` and a trivial postcondition.
--   - `ctInternalOk f pre Pub`: `f` is a symbol of the code block, and the placed program is `ct_subroutine_ok` at `f`'s address with the arities `arity`, the precondition `pre pl` and the public-data relation `Pub`.
--   - `ctPublicOk f pre Pub`: `f` is an export, and the same holds with the library's data objects in their initial state (`PlacedLib.dataInit`: the pointer `implementation`, the table, the string and `optblocker_u16`) added to the precondition.
--
--   So two runs from entry states at `f` that follow the calling convention, have the code loaded and agree on every register, whose memories each satisfy the precondition for their own ghost value separately from an arbitrary frame of their own, with ghost values related by `Pub`, reveal the same observations up to their return and stop together.
--
--   **Preconditions and public data.** Each precondition asks only for the memory a run needs: the bytes the function reads and writes, their lengths, and its stack frame (`stackFrame s0 n`, the `n` bytes below the stack pointer; for a function that reaches `memset` or `sodium_memzero` it includes the 4096 bytes their contracts let them use). No functional invariant is assumed. In the internal state, `leftover` is the word at byte 64 and `final` the byte at 88.
--   - `verifyNPre n`, `crypto_verify_n(x, y)` for $n$ = 16, 32, 64, ghost $(roX, roY, a, b)$: $n$ bytes $a$ at `x` and $n$ bytes $b$ at `y`, each owned or read-only, and a 32-byte frame. `verifyNPub`: $roX$ and $roY$ agree.
--   - `blocksPre`, `poly1305_blocks(st, m, bytes)`, ghost $(ro, rh, fin, m)$: 48 owned bytes $rh$ (`r` and `h`) at `st`, the owned `final` byte $fin$ at `st + 88`, the bytes $m$ at `m`, and `bytes` $= |m|$, a nonzero multiple of 16. No stack. `blocksPub`: $ro$ and $fin$ agree.
--   - `finishPre`, `poly1305_finish(st, mac)`, ghost $(st, mac)$: 96 owned bytes $st$ at `st` with `leftover` below 16, 16 owned bytes at `mac`, and a 4128-byte frame. `leftoverPub`: the two `leftover` words agree.
--   - `updateIntPre`, `poly1305_update(st, m, bytes)`, ghost $(ro, st, m)$: 96 owned bytes $st$ with `leftover` below 16, the bytes $m$ at `m` with `bytes` $= |m|$, and a 32-byte frame. `updatePub`: $ro$ and the `leftover` words agree.
--   - `initPre`, `crypto_onetimeauth_init(state, key)`, ghost $(ro, st, key)$: 256 owned bytes at `state`, 32 bytes at `key`, no stack. `initPub`: $ro$ agrees.
--   - `updatePre`, `crypto_onetimeauth_update(state, in, inlen)`, ghost $(ro, st, inp)$: 256 owned bytes $st$ with `leftover` below 16, the bytes $inp$ at `in` with `inlen` $= |inp|$, and a 48-byte frame. Public data `updatePub`.
--   - `finalPre`, `crypto_onetimeauth_final(state, out)`, ghost $(st, mac)$: 256 owned bytes $st$ with `leftover` below 16, 16 owned bytes at `out`, and a 4144-byte frame. Public data `leftoverPub`.
--   - `oneshotPre pl`, `crypto_onetimeauth(out, in, inlen, k)`, ghost $(roM, roK, ga, out, m, key, g)$: 16 owned bytes at `out`, the bytes $m$ at `in` with `inlen` $= |m|$, 32 bytes at `k`, the guard `guardRes pl ga g`, and a 4320-byte frame. `oneshotPub`: $roM$, $roK$ and $ga$ agree.
--   - `verifyPre pl`, `crypto_onetimeauth_verify(h, in, inlen, k)`, ghost $(roH, roM, roK, ga, h, m, key, g)$: 16 bytes at `h`, the bytes $m$ at `in` with `inlen` $= |m|$, 32 bytes at `k`, each owned or read-only, the guard `guardRes pl ga g`, and a 4352-byte frame. `verifyPub`: $roH$, $roM$, $roK$ and $ga$ agree.
--
--   Everything else is secret: the key, the message, the tag, the bytes compared, the state's other bytes (`r`, `h`, `pad`, the buffer, and except for `poly1305_blocks` the `final` byte) and the guard's value. The pointers and lengths are public because they are in registers.
--
--   **Where the source says it.** The notion of constant time is libsodium's, `helpers/README.md`, line 9: “When a comparison involves secret data (e.g. a key, an authentication tag, etc.), it is critical to use a constant-time comparison function. This property does not relate to computational complexity: it means the time needed to perform the comparison is the same for all data of the same size.” The documentation defines it for comparisons; this bundle applies it to every function it covers, reading it in the leakage model of constant-time programming (equal instruction addresses, memory addresses, division operands and hooked calls' arguments for equal public data). The comparisons it names are `internals/README.md`, line 50: “Secrets are always compared in constant time using `sodium_memcmp()` or `crypto_verify_(16|32|64)()`.” The functions are documented in `advanced/poly1305.md`, lines 65, 72, 94, 96, 98 and 100: “The `crypto_onetimeauth()` function authenticates a message `in` whose length is `inlen` using a secret key `k` (`crypto_onetimeauth_KEYBYTES` bytes) and puts the authenticator into `out` (`crypto_onetimeauth_BYTES` bytes).”, “The `crypto_onetimeauth_verify()` function verifies, in constant time, that `h` is a correct authenticator for the message `in` whose length is `inlen` bytes, using the secret key `k`.”, “The `crypto_onetimeauth_init()` function initializes a structure pointed by `state` using a key `key`.”, “A 16-byte alignment is required for the address of `state`.”, “`crypto_onetimeauth_update()` can then be called more than once in order to compute the authenticator from sequential chunks of the message.”, “Finally, `crypto_onetimeauth_final()` puts the authenticator into `out`.” The preconditions do not ask for the alignment: they hold for a state at any address. The sizes are `crypto_onetimeauth_poly1305.h`, lines 26 and 30: “#define crypto_onetimeauth_poly1305_BYTES 16U”, “#define crypto_onetimeauth_poly1305_KEYBYTES 32U”, the `crypto_onetimeauth_BYTES` and `crypto_onetimeauth_KEYBYTES` of `advanced/poly1305.md`, line 65. `advanced/poly1305.md`, lines 61–62, 68–69, 79–80, 84–86 and 90–91 give the prototypes: “int crypto_onetimeauth(unsigned char *out, const unsigned char *in, unsigned long long inlen, const unsigned char *k);”, “int crypto_onetimeauth_verify(const unsigned char *h, const unsigned char *in, unsigned long long inlen, const unsigned char *k);”, “int crypto_onetimeauth_init(crypto_onetimeauth_state *state, const unsigned char *key);”, “int crypto_onetimeauth_update(crypto_onetimeauth_state *state, const unsigned char *in, unsigned long long inlen);”, “int crypto_onetimeauth_final(crypto_onetimeauth_state *state, unsigned char *out);”. `poly1305_donna64.h`, lines 25–32, give the internal state: “typedef struct poly1305_state_internal_t { unsigned long long r[3]; unsigned long long h[3]; unsigned long long pad[2]; unsigned long long leftover; unsigned char buffer[poly1305_block_size]; unsigned char final; } poly1305_state_internal_t;”, which with 8-byte `unsigned long long` puts `leftover` at offset 64 and `final` at 88. The frame sizes are read off the disassembly: each function's own frame (32 bytes for `crypto_verify_16`, `_32`, `_64`, `poly1305_finish` and `poly1305_update`, 48 for the public update and final, 224 for the one-shot, 256 for verify), plus 4096 where a hook may be reached.
-- source:
--   libsodium documentation, Secret-key single-message authentication using Poly1305 (https://doc.libsodium.org/advanced/poly1305; source jedisct1/libsodium-doc, commit 5adaf345, https://github.com/jedisct1/libsodium-doc/blob/5adaf34515b79d0b37bd8edbe042f20f3bdba2c6/advanced/poly1305.md), lines 61–104 (the prototypes and argument conventions of crypto_onetimeauth, _verify, _init, _update, _final), with the state layout of src/libsodium/crypto_onetimeauth/poly1305/donna/poly1305_donna64.h lines 25–32 and the stack protector and sodium_memzero of the objects

import Definitions.Def_Poly1305DebianCt_PlacedObj
import Definitions.Def_Poly1305Libsodium_Spec
import Definitions.Def_Musl_ExternHooks
import Definitions.Def_Link_LinkOk
import Definitions.Def_Arm64_Leakage

/-!
# Constant-time judgments for Debian's libsodium Poly1305 and `crypto_verify_16` on AArch64

The library is `libsodiumDebianOnetimeauthCtLib` (bundle `Poly1305DebianCt_PlacedObj`): the objects of
`crypto_onetimeauth.c`, `onetimeauth_poly1305.c`, `poly1305_donna.c` and `crypto_verify/verify.c` from
Debian's libsodium 1.0.22-2 for arm64, linked into one text block. Constant-time is
`Leakage.ct_subroutine_ok` (bundle `Arm64_Leakage`): two runs from entry states that differ only in
memory, with related public data, reveal the same instruction addresses, memory addresses and hook
arguments, and return at the same step.

Each precondition below states only what a run needs to stay in owned memory: the bytes the function
reads and writes, their lengths, and its stack frame. The state layout is libsodium's
`poly1305_state_internal_t` (offsets as in bundle `Poly1305Libsodium_Spec`): `leftover` at byte 64 and
`final` at byte 88. Public data, besides the registers: the lengths (passed in registers), which
inputs are read-only, and the stored `leftover` (and, for the block routine, `final`). Secret: keys,
message bytes, tags and the other state bytes.
-/

namespace Poly1305DebianCt

open Arm64 Arm64.Obj Leakage
open Poly1305Libsodium (u64At bytesIn MemzeroOk)

/-! ## The library, its hooks and their arities -/

/-- The library. -/
abbrev lib : PlacedLib := libsodiumDebianOnetimeauthCtLib

/-- The number of arguments a call to each external function reveals: its C arity
(`sodium_memzero(pnt, len)`, `memset(dst, c, n)`, `randombytes_buf(buf, size)`,
`__stack_chk_fail(void)`). -/
def arity (name : String) : Nat :=
  if name = "sodium_memzero" then 2
  else if name = "memset" then 3
  else if name = "randombytes_buf" then 2
  else 0

/-- The hooks `externs` call, for `memset`, a function meeting `VerifiedLibraries.Musl.cryptoMemsetSpec`. -/
def MemsetOk (externs : String → Option (State → State)) : Prop :=
  HookSat externs "memset" VerifiedLibraries.Musl.cryptoMemsetSpec

/-- Byte offsets in the text block of the `ADRP` instructions that start a GOT access to
`__stack_chk_guard` (an `adrGotPage` relocation; the `LDR` follows at the next word). -/
def guardSites : List Nat :=
  (libsodiumDebianOnetimeauthCtText.relocs.filter fun r =>
    r.kind == .adrGotPage && r.sym == "__stack_chk_guard").map (·.off)

/-- Under `pl`, the GOT access to `__stack_chk_guard` at `off` is relaxed by the linker, to
`NOP` + `ADR` (`pl.relax off`) or to `ADRP` + `ADD` (`pl.relax (off + 4)`). -/
def guardDirect (pl : Placement) (off : Nat) : Bool :=
  pl.relax off || pl.relax (off + 4)

/-- `pl` treats every GOT access to `__stack_chk_guard` alike: all relaxed, or none. -/
def GuardUniform (pl : Placement) : Prop :=
  ∀ off ∈ guardSites, guardDirect pl off = guardDirect pl (guardSites.headD 0)

/-- The stack-protector guard with value `g`, readable where the code reads it under `pl`: the
8 little-endian bytes of `g` at `pl.ρ "__stack_chk_guard"` when the GOT accesses are relaxed;
otherwise a GOT slot there holding the address `ga` and the 8 bytes of `g` at `ga`. Read-only.
(`ga` is a parameter, not hidden, so that the judgments below can make it public: the code loads
from `ga`, so two runs with different `ga` reveal different addresses.) -/
def guardRes (pl : Placement) (ga g : BitVec 64) : SepProp :=
  if guardDirect pl (guardSites.headD 0) then pl.ρ "__stack_chk_guard" ↦ᵣ bytesLE 8 g
  else (pl.ρ "__stack_chk_guard" ↦ᵣ bytesLE 8 ga) ∗ (ga ↦ᵣ bytesLE 8 g)

/-! ## Judgments -/

/-- The precondition `pre` as an `Arm64.Spec` (its postcondition is not used). -/
def preSpec {α : Type} (pre : α → State → SepProp) : Spec α where
  pre := pre
  post := fun _ _ _ => ⌜True⌝

/-- A function of the library that need not be exported is constant-time: `fnName` is a symbol of
the text block, and for every placement `pl` under which the library is `Placeable`, with
`GuardUniform pl`, and all hooks `externs` with `MemzeroOk externs`, `MemsetOk externs` and
`Link.PlacedLib.LinkOk lib pl externs`, the placed program at the address of `fnName` is
`ct_subroutine_ok` for `pre pl`, the public-data relation `Pub` and `arity`. -/
def ctInternalOk {α : Type} (fnName : String) (pre : Placement → α → State → SepProp)
    (Pub : α → α → Prop) : Prop :=
  fnName ∈ libsodiumDebianOnetimeauthCtText.symbols.map Prod.fst ∧
  ∀ pl : Placement, lib.Placeable pl → GuardUniform pl →
    ∀ externs : String → Option (State → State), MemzeroOk externs → MemsetOk externs →
      Link.PlacedLib.LinkOk lib pl externs →
        ct_subroutine_ok (lib.program pl externs) arity (lib.fnAddr pl fnName) (preSpec (pre pl)) Pub

/-- An exported function of the library is constant-time: `fnName` is one of its exports and, with
the hypotheses of `ctInternalOk`, the placed program at its address is `ct_subroutine_ok` for
`pre pl` with the library's data objects in their initial state (`PlacedLib.dataInit`) added. -/
def ctPublicOk {α : Type} (fnName : String) (pre : Placement → α → State → SepProp)
    (Pub : α → α → Prop) : Prop :=
  fnName ∈ lib.exports ∧
  ∀ pl : Placement, lib.Placeable pl → GuardUniform pl →
    ∀ externs : String → Option (State → State), MemzeroOk externs → MemsetOk externs →
      Link.PlacedLib.LinkOk lib pl externs →
        ct_subroutine_ok (lib.program pl externs) arity (lib.fnAddr pl fnName)
          (preSpec fun x s0 => pre pl x s0 ∗ lib.dataInit pl) Pub

/-! ## Preconditions and public data -/

/-- `crypto_verify_n(x, y)` for `n` = 16, 32, 64 (`x0 = x`, `x1 = y`), ghost `(roX, roY, a, b)`: the `n`
bytes `a` at `x` and `b` at `y` (each owned or read-only, by `roX`, `roY`) and a 32-byte stack frame. -/
def verifyNPre (n : Nat) (_ : Placement) :
    Bool × Bool × List (BitVec 8) × List (BitVec 8) → State → SepProp
  | (roX, roY, a, b), s0 =>
    ⌜a.length = n ∧ b.length = n⌝ ∗ bytesIn roX (s0.readReg64 Reg.x0) a ∗
      bytesIn roY (s0.readReg64 Reg.x1) b ∗ stackFrame s0 32

/-- Public for `crypto_verify_16`, `_32` and `_64`: which inputs are read-only. The bytes are secret. -/
def verifyNPub : Bool × Bool × List (BitVec 8) × List (BitVec 8) →
    Bool × Bool × List (BitVec 8) × List (BitVec 8) → Prop
  | (roX, roY, _, _), (roX', roY', _, _) => roX = roX' ∧ roY = roY'

/-- `poly1305_blocks(st, m, bytes)` (`x0 = st`, `x1 = m`, `x2 = bytes`), ghost `(ro, rh, fin, m)`:
the 48 bytes `rh` (`r` and `h`) at `st`, the `final` byte `fin` at `st + 88`, the message bytes `m`
at `m` (owned or read-only, by `ro`), with `bytes = m.length` a nonzero multiple of 16. No stack. -/
def blocksPre (_ : Placement) :
    Bool × List (BitVec 8) × BitVec 8 × List (BitVec 8) → State → SepProp
  | (ro, rh, fin, m), s0 =>
    ⌜rh.length = 48 ∧ (s0.readReg64 Reg.x2).toNat = m.length ∧ 16 ≤ m.length ∧ m.length % 16 = 0⌝ ∗
      (s0.readReg64 Reg.x0 ↦ₛ rh) ∗ ((s0.readReg64 Reg.x0 + 88#64) ↦ₛ [fin]) ∗
      bytesIn ro (s0.readReg64 Reg.x1) m

/-- Public for `poly1305_blocks`: `ro` and the `final` byte. `r`, `h` and the message are secret. -/
def blocksPub : Bool × List (BitVec 8) × BitVec 8 × List (BitVec 8) →
    Bool × List (BitVec 8) × BitVec 8 × List (BitVec 8) → Prop
  | (ro, _, fin, _), (ro', _, fin', _) => ro = ro' ∧ fin = fin'

/-- `poly1305_finish(st, mac)` (`x0 = st`, `x1 = mac`), ghost `(st, mac)`: the 96 state bytes `st` at
`st` with `leftover` (byte 64) below 16, the 16 bytes `mac` at `mac`, and a 4128-byte stack frame. -/
def finishPre (_ : Placement) : List (BitVec 8) × List (BitVec 8) → State → SepProp
  | (st, mac), s0 =>
    ⌜st.length = 96 ∧ u64At st 64 < 16 ∧ mac.length = 16⌝ ∗
      (s0.readReg64 Reg.x0 ↦ₛ st) ∗ (s0.readReg64 Reg.x1 ↦ₛ mac) ∗ stackFrame s0 4128

/-- Public for `poly1305_finish` and `crypto_onetimeauth_final`: the stored `leftover`. -/
def leftoverPub : List (BitVec 8) × List (BitVec 8) → List (BitVec 8) × List (BitVec 8) → Prop
  | (st, _), (st', _) => u64At st 64 = u64At st' 64

/-- `poly1305_update(st, m, bytes)` (`x0 = st`, `x1 = m`, `x2 = bytes`), ghost `(ro, st, m)`: the 96
state bytes `st` at `st` with `leftover` below 16, the message bytes `m` at `m` (owned or read-only,
by `ro`), `bytes = m.length`, and a 32-byte stack frame. -/
def updateIntPre (_ : Placement) : Bool × List (BitVec 8) × List (BitVec 8) → State → SepProp
  | (ro, st, m), s0 =>
    ⌜st.length = 96 ∧ u64At st 64 < 16 ∧ (s0.readReg64 Reg.x2).toNat = m.length⌝ ∗
      (s0.readReg64 Reg.x0 ↦ₛ st) ∗ bytesIn ro (s0.readReg64 Reg.x1) m ∗ stackFrame s0 32

/-- Public for `poly1305_update` and the public `update`: `ro` and the stored `leftover`. -/
def updatePub : Bool × List (BitVec 8) × List (BitVec 8) → Bool × List (BitVec 8) × List (BitVec 8) → Prop
  | (ro, st, _), (ro', st', _) => ro = ro' ∧ u64At st 64 = u64At st' 64

/-- `crypto_onetimeauth_init(state, key)` (`x0 = state`, `x1 = key`), ghost `(ro, st, key)`: the 256
bytes `st` at `state` and the 32 bytes `key` at `key` (owned or read-only, by `ro`). No stack. -/
def initPre (_ : Placement) : Bool × List (BitVec 8) × List (BitVec 8) → State → SepProp
  | (ro, st, key), s0 =>
    ⌜st.length = 256 ∧ key.length = 32⌝ ∗
      (s0.readReg64 Reg.x0 ↦ₛ st) ∗ bytesIn ro (s0.readReg64 Reg.x1) key

/-- Public for `crypto_onetimeauth_init`: `ro`. The key and the old state bytes are secret. -/
def initPub : Bool × List (BitVec 8) × List (BitVec 8) → Bool × List (BitVec 8) × List (BitVec 8) → Prop
  | (ro, _, _), (ro', _, _) => ro = ro'

/-- `crypto_onetimeauth_update(state, in, inlen)` (`x0 = state`, `x1 = in`, `x2 = inlen`), ghost
`(ro, st, inp)`: the 256 bytes `st` at `state` with `leftover` below 16, the bytes `inp` at `in`
(owned or read-only, by `ro`), `inlen = inp.length`, and a 48-byte stack frame. -/
def updatePre (_ : Placement) : Bool × List (BitVec 8) × List (BitVec 8) → State → SepProp
  | (ro, st, inp), s0 =>
    ⌜st.length = 256 ∧ u64At st 64 < 16 ∧ (s0.readReg64 Reg.x2).toNat = inp.length⌝ ∗
      (s0.readReg64 Reg.x0 ↦ₛ st) ∗ bytesIn ro (s0.readReg64 Reg.x1) inp ∗ stackFrame s0 48

/-- `crypto_onetimeauth_final(state, out)` (`x0 = state`, `x1 = out`), ghost `(st, mac)`: the 256
bytes `st` at `state` with `leftover` below 16, the 16 bytes `mac` at `out`, and a 4144-byte stack
frame. -/
def finalPre (_ : Placement) : List (BitVec 8) × List (BitVec 8) → State → SepProp
  | (st, mac), s0 =>
    ⌜st.length = 256 ∧ u64At st 64 < 16 ∧ mac.length = 16⌝ ∗
      (s0.readReg64 Reg.x0 ↦ₛ st) ∗ (s0.readReg64 Reg.x1 ↦ₛ mac) ∗ stackFrame s0 4144

/-- `crypto_onetimeauth(out, in, inlen, k)` (`x0 = out`, `x1 = in`, `x2 = inlen`, `x3 = k`), ghost
`(roM, roK, ga, out, m, key, g)`: the 16 bytes `out` at `out`, the message bytes `m` at `in` and the
32 bytes `key` at `k` (each owned or read-only, by `roM`, `roK`), `inlen = m.length`, the
stack-protector guard `g` readable (`guardRes pl ga g`), and a 4320-byte stack frame. -/
def oneshotPre (pl : Placement) :
    Bool × Bool × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8) × BitVec 64 →
      State → SepProp
  | (roM, roK, ga, out, m, key, g), s0 =>
    ⌜out.length = 16 ∧ (s0.readReg64 Reg.x2).toNat = m.length ∧ key.length = 32⌝ ∗
      (s0.readReg64 Reg.x0 ↦ₛ out) ∗ bytesIn roM (s0.readReg64 Reg.x1) m ∗
      bytesIn roK (s0.readReg64 Reg.x3) key ∗ guardRes pl ga g ∗ stackFrame s0 4320

/-- Public for `crypto_onetimeauth`: `roM`, `roK` and the guard's address `ga`. Message, key, output
bytes and guard value are secret. -/
def oneshotPub :
    Bool × Bool × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8) × BitVec 64 →
    Bool × Bool × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8) × BitVec 64 → Prop
  | (roM, roK, ga, _, _, _, _), (roM', roK', ga', _, _, _, _) => roM = roM' ∧ roK = roK' ∧ ga = ga'

/-- `crypto_onetimeauth_verify(h, in, inlen, k)` (`x0 = h`, `x1 = in`, `x2 = inlen`, `x3 = k`), ghost
`(roH, roM, roK, ga, h, m, key, g)`: the 16 bytes `h` at `h`, the message bytes `m` at `in` and the
32 bytes `key` at `k` (each owned or read-only, by `roH`, `roM`, `roK`), `inlen = m.length`, the
stack-protector guard `g` readable (`guardRes pl ga g`), and a 4352-byte stack frame. -/
def verifyPre (pl : Placement) :
    Bool × Bool × Bool × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8) × BitVec 64 →
      State → SepProp
  | (roH, roM, roK, ga, h, m, key, g), s0 =>
    ⌜h.length = 16 ∧ (s0.readReg64 Reg.x2).toNat = m.length ∧ key.length = 32⌝ ∗
      bytesIn roH (s0.readReg64 Reg.x0) h ∗ bytesIn roM (s0.readReg64 Reg.x1) m ∗
      bytesIn roK (s0.readReg64 Reg.x3) key ∗ guardRes pl ga g ∗ stackFrame s0 4352

/-- Public for `crypto_onetimeauth_verify`: `roH`, `roM`, `roK` and the guard's address `ga`. Tag,
message, key and guard value are secret. -/
def verifyPub :
    Bool × Bool × Bool × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8) × BitVec 64 →
    Bool × Bool × Bool × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8) × BitVec 64 →
      Prop
  | (roH, roM, roK, ga, _, _, _, _), (roH', roM', roK', ga', _, _, _, _) =>
    roH = roH' ∧ roM = roM' ∧ roK = roK' ∧ ga = ga'

end Poly1305DebianCt


