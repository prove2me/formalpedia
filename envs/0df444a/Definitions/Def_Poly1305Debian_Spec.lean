-- Prove2me | Definitions.Def_Poly1305Debian_Spec
-- name    : Poly1305Debian_Spec
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-25T16:38:02.901356+00:00
-- url     : https://prove2.me/theorems/db19c8f3-39ab-4656-967c-8d20b16dccbe
-- title:
--   Contracts of Debian's libsodium Poly1305 on AArch64
-- statement:
--   The hypotheses on a link, the two judgments, and the contracts of the functions of `libsodiumDebianOnetimeauthLib` (bundle `Poly1305Debian_PlacedObj`). The state layout and its helpers come from the bundle `Poly1305Libsodium_Spec`, which describes the same C source: `u64At`, the limbs `rLimb` and `hLimb` and their value `limbVal`, the invariant `StateOk` on the 48 bytes of `r` and `h` (`r` at most the clamping masks, `h[0] < 2^44`, `h[1] < 2^44 + 64`, `h[2] < 2^42`), `hibit`, the block step `blocksAcc`, `bytesIn` (owned or read-only bytes), `MemzeroOk`, the tag `finishTag` and the representation predicates `StateRep`.
--
--   **Hypotheses.**
--   - `MemsetOk externs`: the hook for `memset` meets DeepMind's published contract `VerifiedLibraries.Musl.cryptoMemsetSpec` (it sets the `x2` bytes at `x0` to the low byte of `x1`, returns `x0`, and may use 4096 bytes of stack).
--   - `guardSites` is the list of offsets of the code's GOT accesses to `__stack_chk_guard`. `guardDirect pl off` says the linker relaxed the access at `off` into a direct computation of the guard's address. `GuardUniform pl` says all accesses are relaxed or none is, as a linker does for one symbol. `guardRes pl g` is the guard with value `g`, read-only, where the code reads it: the 8 bytes of `g` at the address the placement gives `__stack_chk_guard` when the accesses are relaxed, otherwise a GOT slot there holding an address $a$ and the 8 bytes of `g` at $a$.
--
--   **Judgments.** Both quantify over every placement `pl` under which the library is `Placeable` and `GuardUniform pl` holds, and every hook table `externs` with `MemzeroOk externs`, `MemsetOk externs` and `Link.PlacedLib.LinkOk libsodiumDebianOnetimeauthLib pl externs`. `LinkOk` says the library is laid out as a real link lays it out: two external functions at one address have the same hook, no external function lies in the code or a data object, and the data objects are disjoint from each other and from the code.
--   - `internalOk f spec`: `f` is a symbol of the code block, and the placed program meets `spec pl` at `f`.
--   - `publicOk f spec`: `f` is an export, and the placed program meets `withData pl (spec pl)` at `f`, where `withData` adds the library's data objects in their initial state (`PlacedLib.dataInit`: the pointer `implementation` and the table, owned since they are writable, and the read-only string; their source lines are quoted in the note of `Poly1305Debian_PlacedObj`) to the precondition and to the postcondition.
--   "Meets" is `subroutine_ok`. Take every entry state at the function with the stack pointer 16-byte aligned and every frame $R$ held separately. Execution terminates and returns to the caller with the stack pointer and the callee-saved registers restored, $R$ untouched and the postcondition holding. It never panics, exits or runs out of memory.
--
--   **Contracts.** In each, the stack frame is the bytes below the stack pointer that the caller lends, covering the function's own use and 4096 bytes for any `memset` or `sodium_memzero` hook it reaches.
--   - `blocksSpec`, for `poly1305_blocks(st, m, bytes)`, ghost $(ro, rh, fin, m)$. Before: `st` owns the 48 bytes $rh$ with `StateOk`, and the `final` byte $fin$ at offset 88. The bytes $m$ are at `m` (`bytesIn ro`), with `bytes` $= |m| \ge 16$. After: `x0` and `x18` are unchanged, and `st` holds 48 bytes $rh'$ with `StateOk`, the same $r$ (first 24 bytes), and `limbVal (hLimb rh')` $\equiv$ `blocksAcc (limbVal (rLimb rh)) (hibit fin) (limbVal (hLimb rh)) m` $\pmod{2^{130}-5}$. $fin$ and $m$ are handed back. No stack is used.
--   - `Absorbs st m st'` relates 96 state bytes before and after absorbing message bytes $m$. Let $L$ be `leftover` (offset 64), $t$ the first $L$ bytes of `buffer` (offset 72) followed by $m$, and $k = 16\lfloor |t|/16 \rfloor$. Then $st'$ keeps `r` (bytes 0–23), `pad` (48–63) and `final` (88) of $st$, satisfies `StateOk` on its first 48 bytes, has `leftover` $= |t| - k$ with the last $|t| - k$ bytes of $t$ at the start of `buffer`, and has an accumulator congruent modulo $2^{130} - 5$ to `blocksAcc` run on the first $k$ bytes of $t$ with $r$, `hibit final` and the old accumulator.
--   - `updateIntSpec`, for `poly1305_update(st, m, bytes)`, ghost $(ro, st, m)$. Before: `st` owns 96 bytes $st$ with `StateOk` on the first 48 and `leftover` $< 16$. The bytes $m$ are at `m` (`bytesIn ro`), with `bytes` $= |m|$, and the frame is 32 bytes. After: `x0` is unchanged, and `st` holds 96 bytes $st'$ with `Absorbs st m st'`. $m$ and the frame are handed back.
--   - `finishSpec`, for `poly1305_finish(st, mac)`, ghost $(st, mac)$. Before: `st` owns 96 bytes $st$ with `StateOk` on the first 48 and `leftover` $< 16$, `mac` owns 16 bytes, and the frame is 4128 bytes. After: the 96 state bytes are zero, `mac` holds `finishTag st`, and the frame is handed back.
--   - `initSpec Rep`, `updateSpec Rep`, `finalSpec Rep` and `oneshotSpec pl` are the contracts of `init(state, key)`, `update(state, in, inlen)`, `final(state, out)` and the one-shot `(out, m, inlen, key)`. A representation predicate $\mathrm{Rep}(a, st, key, m)$ relates the address of a 256-byte state, its bytes, a key and the bytes absorbed. Each returns `0` in `w0`, and inputs may be owned or read-only.
--     - Init, with no stack, turns 256 owned bytes into $st'$ with $\mathrm{Rep}(\mathtt{state}, st', key, [\,])$.
--     - Update, with a 48-byte frame, turns $\mathrm{Rep}(\mathtt{state}, st, key, m)$ into $\mathrm{Rep}(\mathtt{state}, st', key, m \mathbin{+\!\!+} inp)$.
--     - Final, with a 4144-byte frame, writes `poly1305Mac m key` to the 16 bytes at `out` and leaves the first 96 bytes of the state zero and the other 160 unchanged.
--     - The one-shot, with a 4320-byte frame and the guard `guardRes pl g` lent and handed back, writes `poly1305Mac m key` to `out`.
--   - `donnaInitOk`, `donnaUpdateOk`, `donnaFinalOk` and `donnaOneshotOk` are `internalOk` of the four donna functions with these contracts. `initPublicOk`, `updatePublicOk`, `finalPublicOk` and `oneshotPublicOk` are `publicOk` of `crypto_onetimeauth_init`, `_update`, `_final` and `crypto_onetimeauth`.
--
--   **Why the register clauses.** `poly1305_blocks` and `poly1305_update` are `static`, and the compiler's calls to them rely on more than the calling convention guarantees. After `poly1305_blocks` returns, `poly1305_update` goes on using `x0` and `x18` without having saved them, and after `poly1305_update` returns, the one-shot passes the state pointer still in `x0` to `poly1305_finish`. The contracts state these facts so that the callers' correctness follows from them.
--
--   **Where the source says it.** `crypto_onetimeauth_poly1305.h`, lines 19–21, 26 and 30: “typedef struct CRYPTO_ALIGN(16) crypto_onetimeauth_poly1305_state { unsigned char opaque[256]; } crypto_onetimeauth_poly1305_state;”, “#define crypto_onetimeauth_poly1305_BYTES 16U”, “#define crypto_onetimeauth_poly1305_KEYBYTES 32U”. The contracts hold for a state at any address, not only a 16-byte-aligned one. `poly1305_donna64.h`, lines 22 and 25–32: “#define poly1305_block_size 16”, “typedef struct poly1305_state_internal_t { unsigned long long r[3]; unsigned long long h[3]; unsigned long long pad[2]; unsigned long long leftover; unsigned char buffer[poly1305_block_size]; unsigned char final; } poly1305_state_internal_t;”; with 8-byte `unsigned long long` this puts `r` at offset 0, `h` at 24, `pad` at 48, `leftover` at 64, `buffer` at 72 and `final` at 88, the offsets the contracts read. The functions with contracts here, by their definitions: `poly1305_donna64.h`, lines 61–63, “static void poly1305_blocks(poly1305_state_internal_t *st, const unsigned char *m, unsigned long long bytes)”, whose loop “while (bytes >= poly1305_block_size) {” (line 84) does “/* h += m[i] */”, “/* h *= r */” and “/* (partial) h %= p */”; lines 135–136, “static POLY1305_NOINLINE void poly1305_finish(poly1305_state_internal_t *st, unsigned char mac[16])”; `poly1305_donna.c`, lines 14–16, “static void poly1305_update(poly1305_state_internal_t *st, const unsigned char *m, unsigned long long bytes)”, whose steps are “/* handle leftover */”, “/* process full blocks */” and “/* store leftover */”; lines 58–61, “static int crypto_onetimeauth_poly1305_donna(unsigned char *out, const unsigned char *m, unsigned long long inlen, const unsigned char *key)”, whose body is “poly1305_init(&state, key); poly1305_update(&state, m, inlen); poly1305_finish(&state, out);” on a local state, then “return 0;”; lines 72–74, 83–86 and 93–95, “static int crypto_onetimeauth_poly1305_donna_init(crypto_onetimeauth_poly1305_state *state, const unsigned char *key)”, “static int crypto_onetimeauth_poly1305_donna_update( crypto_onetimeauth_poly1305_state *state, const unsigned char *in, unsigned long long inlen)” and “static int crypto_onetimeauth_poly1305_donna_final( crypto_onetimeauth_poly1305_state *state, unsigned char *out)”, which run `poly1305_init`, `poly1305_update` and `poly1305_finish` on the state and return 0; and `crypto_onetimeauth.c`, lines 23–60, “int crypto_onetimeauth(unsigned char *out, const unsigned char *in, unsigned long long inlen, const unsigned char *k) { return crypto_onetimeauth_poly1305(out, in, inlen, k); }”, “int crypto_onetimeauth_init(crypto_onetimeauth_state *state, const unsigned char *key) { return crypto_onetimeauth_poly1305_init ((crypto_onetimeauth_poly1305_state *) state, key); }”, “int crypto_onetimeauth_update(crypto_onetimeauth_state *state, const unsigned char *in, unsigned long long inlen) { return crypto_onetimeauth_poly1305_update ((crypto_onetimeauth_poly1305_state *) state, in, inlen); }”, “int crypto_onetimeauth_final(crypto_onetimeauth_state *state, unsigned char *out) { return crypto_onetimeauth_poly1305_final ((crypto_onetimeauth_poly1305_state *) state, out); }”.
-- source:
--   libsodium 1.0.22-RELEASE, commit 77e1ce5d6dee871c49ef211222ba18ef0c486bda (https://github.com/jedisct1/libsodium/tree/77e1ce5d6dee871c49ef211222ba18ef0c486bda), src/libsodium/crypto_onetimeauth/poly1305/donna/poly1305_donna64.h lines 25–32 (poly1305_state_internal_t), src/libsodium/crypto_onetimeauth/poly1305/donna/poly1305_donna.c lines 14–100, src/libsodium/crypto_onetimeauth/crypto_onetimeauth.c lines 23–60 and src/libsodium/include/sodium/crypto_onetimeauth_poly1305.h lines 19–62

import Definitions.Def_Poly1305Libsodium_Spec
import Definitions.Def_Poly1305Debian_PlacedObj
import Definitions.Def_Link_LinkOk
import Definitions.Def_Arm64_Spec_Placed

/-!
# Contracts of Debian's libsodium Poly1305 on AArch64

The library is `libsodiumDebianOnetimeauthLib` (bundle `Poly1305Debian_PlacedObj`): the objects of
`crypto_onetimeauth.c`, `onetimeauth_poly1305.c` and `poly1305_donna.c` from Debian's libsodium 1.0.22-2
for arm64, linked into one text block. The state layout `poly1305_state_internal_t`, the limb invariant
`StateOk`, the block step `blocksAcc`, the tag `finishTag` and the representation predicates `StateRep`
are those of bundle `Poly1305Libsodium_Spec`, which describe the same C source.

Every judgment quantifies over the placements of the library (`Placeable`) that are laid out as a real
link lays them out (`Link.PlacedLib.LinkOk`) and treat every GOT access to `__stack_chk_guard` alike
(`GuardUniform`), and over the hooks that call, for `sodium_memzero`, a function meeting
`Libc.explicitBzeroSpec` (`MemzeroOk`) and, for `memset`, one meeting
`VerifiedLibraries.Musl.cryptoMemsetSpec` (`MemsetOk`).
-/

namespace Poly1305Debian

open Arm64 Arm64.Obj Poly1305Boringssl
open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag
  StateRep)

/-! ## Hypotheses on the link and the hooks -/

/-- The hooks `externs` call, for `memset`, a function meeting `VerifiedLibraries.Musl.cryptoMemsetSpec`. -/
def MemsetOk (externs : String → Option (State → State)) : Prop :=
  HookSat externs "memset" VerifiedLibraries.Musl.cryptoMemsetSpec

/-- Byte offsets in the text block of the `ADRP` instructions that start a GOT access to
`__stack_chk_guard` (an `adrGotPage` relocation; the `LDR` follows at the next word). -/
def guardSites : List Nat :=
  (libsodiumDebianOnetimeauthText.relocs.filter fun r =>
    r.kind == .adrGotPage && r.sym == "__stack_chk_guard").map (·.off)

/-- Under `pl`, the GOT access to `__stack_chk_guard` at `off` is relaxed by the linker, to
`NOP` + `ADR` (`pl.relax off`) or to `ADRP` + `ADD` (`pl.relax (off + 4)`), so that it computes the
guard's address `pl.ρ "__stack_chk_guard"`; otherwise it loads the address from the GOT slot at
`pl.ρ "__stack_chk_guard"`. -/
def guardDirect (pl : Placement) (off : Nat) : Bool :=
  pl.relax off || pl.relax (off + 4)

/-- `pl` treats every GOT access to `__stack_chk_guard` alike: all relaxed, or none. -/
def GuardUniform (pl : Placement) : Prop :=
  ∀ off ∈ guardSites, guardDirect pl off = guardDirect pl (guardSites.headD 0)

/-- The stack-protector guard with value `g`, readable where the code reads it under `pl`: the
8 little-endian bytes of `g` at `pl.ρ "__stack_chk_guard"` when the GOT accesses are relaxed;
otherwise a GOT slot there holding an address `a` and the 8 bytes of `g` at `a`. Read-only. -/
def guardRes (pl : Placement) (g : BitVec 64) : SepProp :=
  if guardDirect pl (guardSites.headD 0) then pl.ρ "__stack_chk_guard" ↦ᵣ bytesLE 8 g
  else ∃∗ a : BitVec 64, (pl.ρ "__stack_chk_guard" ↦ᵣ bytesLE 8 a) ∗ (a ↦ᵣ bytesLE 8 g)

/-! ## Judgments -/

/-- Correctness of a function of `libsodiumDebianOnetimeauthLib` that need not be exported: `fnName`
is a symbol of the text block, and for every placement `pl` under which the library is `Placeable`
with `GuardUniform pl`, and all hooks `externs` with `MemzeroOk externs`, `MemsetOk externs` and
`Link.PlacedLib.LinkOk libsodiumDebianOnetimeauthLib pl externs`, `subroutine_ok` holds for the placed
program at the address of `fnName`. -/
def internalOk {α : Type} (fnName : String) (spec : Placement → Spec α) : Prop :=
  fnName ∈ libsodiumDebianOnetimeauthText.symbols.map Prod.fst ∧
  ∀ pl : Placement, libsodiumDebianOnetimeauthLib.Placeable pl → GuardUniform pl →
    ∀ externs : String → Option (State → State), MemzeroOk externs → MemsetOk externs →
      Link.PlacedLib.LinkOk libsodiumDebianOnetimeauthLib pl externs →
        subroutine_ok (libsodiumDebianOnetimeauthLib.program pl externs)
          (libsodiumDebianOnetimeauthLib.fnAddr pl fnName) (spec pl)

/-- `spec` with the library's data objects, in their initial state under `pl`
(`PlacedLib.dataInit`), added to the precondition and to the postcondition. -/
def withData {α : Type} (pl : Placement) (spec : Spec α) : Spec α :=
  { spec with
    pre := fun x s0 => spec.pre x s0 ∗ libsodiumDebianOnetimeauthLib.dataInit pl
    post := fun x s0 sf => spec.post x s0 sf ∗ libsodiumDebianOnetimeauthLib.dataInit pl }

/-- Correctness of an exported function of `libsodiumDebianOnetimeauthLib`: `fnName` is one of its
exports, and with the hypotheses of `internalOk`, `subroutine_ok` holds for the placed program at the
address of `fnName`, for `spec pl` with the library's data objects lent to the call (`withData`). -/
def publicOk {α : Type} (fnName : String) (spec : Placement → Spec α) : Prop :=
  fnName ∈ libsodiumDebianOnetimeauthLib.exports ∧
  ∀ pl : Placement, libsodiumDebianOnetimeauthLib.Placeable pl → GuardUniform pl →
    ∀ externs : String → Option (State → State), MemzeroOk externs → MemsetOk externs →
      Link.PlacedLib.LinkOk libsodiumDebianOnetimeauthLib pl externs →
        subroutine_ok (libsodiumDebianOnetimeauthLib.program pl externs)
          (libsodiumDebianOnetimeauthLib.fnAddr pl fnName) (withData pl (spec pl))

/-! ## The block routine -/

/-- Contract of the internal `poly1305_blocks(st, m, bytes)` (`x0 = st`, `x1 = m`, `x2 = bytes`),
ghost `(ro, rh, fin, m)`: entered owning the 48 bytes `rh` (`r` and `h`) at `st` with `StateOk rh`,
the `final` byte `fin` at `st + 88`, the message bytes `m` at `m` (owned or read-only, by `ro`), and
`bytes = m.length` at least 16, it returns with `x0` and `x18` unchanged, with 48 bytes `rh'` at `st`
that satisfy `StateOk`, keep `r` (the first 24 bytes), and whose accumulator is congruent modulo
`2^130 - 5` to `blocksAcc` run on `m` with `r`, `hibit fin` and the old accumulator; `fin` and `m` are
handed back. It uses no stack. -/
def blocksSpec : Spec (Bool × List (BitVec 8) × BitVec 8 × List (BitVec 8)) where
  pre g s0 :=
    match g with
    | (ro, rh, fin, m) =>
      ⌜StateOk rh ∧ (s0.readReg64 Reg.x2).toNat = m.length ∧ 16 ≤ m.length⌝ ∗
        (s0.readReg64 Reg.x0 ↦ₛ rh) ∗ ((s0.readReg64 Reg.x0 + 88#64) ↦ₛ [fin]) ∗
        bytesIn ro (s0.readReg64 Reg.x1) m
  post g s0 sf :=
    match g with
    | (ro, rh, fin, m) =>
      ⌜sf.readReg64 Reg.x0 = s0.readReg64 Reg.x0 ∧ sf.readReg64 Reg.x18 = s0.readReg64 Reg.x18⌝ ∗
        (∃∗ rh' : List (BitVec 8), (s0.readReg64 Reg.x0 ↦ₛ rh') ∗
          ⌜StateOk rh' ∧ rh'.take 24 = rh.take 24 ∧
            limbVal (hLimb rh') % p1305 =
              blocksAcc (limbVal (rLimb rh)) (hibit fin) (limbVal (hLimb rh)) m % p1305⌝) ∗
        ((s0.readReg64 Reg.x0 + 88#64) ↦ₛ [fin]) ∗ bytesIn ro (s0.readReg64 Reg.x1) m

/-! ## Absorbing input -/

/-- The 96 state bytes `st'` are the 96 state bytes `st` after absorbing the message bytes `m`:
with `L = leftover st` (offset 64), the pending bytes `t = buffer[0..L] ++ m` (buffer at offset 72)
and `k = 16 * ⌊|t| / 16⌋`, the bytes `st'` keep `r` (offsets 0–23), `pad` (48–63) and `final` (88)
of `st`, satisfy `StateOk` on their first 48 bytes, have `leftover = |t| - k`, hold the last `|t| - k`
bytes of `t` at the start of `buffer`, and have an accumulator congruent modulo `2^130 - 5` to
`blocksAcc` run on the first `k` bytes of `t` with `r`, `hibit final` and the accumulator of `st`. -/
def Absorbs (st m st' : List (BitVec 8)) : Prop :=
  let L := u64At st 64
  let t := (st.drop 72).take L ++ m
  let k := 16 * (t.length / 16)
  st'.length = 96 ∧ st'.take 24 = st.take 24 ∧ (st'.drop 48).take 16 = (st.drop 48).take 16 ∧
    st'.getD 88 0#8 = st.getD 88 0#8 ∧ StateOk (st'.take 48) ∧ u64At st' 64 = t.length - k ∧
    (st'.drop 72).take (t.length - k) = t.drop k ∧
    limbVal (hLimb st') % p1305 =
      blocksAcc (limbVal (rLimb st)) (hibit (st.getD 88 0#8)) (limbVal (hLimb st)) (t.take k) % p1305

/-- Contract of the internal `poly1305_update(st, m, bytes)` (`x0 = st`, `x1 = m`, `x2 = bytes`),
ghost `(ro, st, m)`: entered owning the 96 state bytes `st` at `st`, whose first 48 bytes satisfy
`StateOk` and whose `leftover` is below 16, with the message bytes `m` at `m` (owned or read-only, by
`ro`), `bytes = m.length` and a 32-byte stack frame below `sp`, it returns with `x0` unchanged, 96 bytes
`st'` at `st` such that `Absorbs st m st'`, and `m` and the stack frame handed back. -/
def updateIntSpec : Spec (Bool × List (BitVec 8) × List (BitVec 8)) where
  pre g s0 :=
    match g with
    | (ro, st, m) =>
      ⌜st.length = 96 ∧ StateOk (st.take 48) ∧ u64At st 64 < 16 ∧
          (s0.readReg64 Reg.x2).toNat = m.length⌝ ∗
        (s0.readReg64 Reg.x0 ↦ₛ st) ∗ bytesIn ro (s0.readReg64 Reg.x1) m ∗ stackFrame s0 32
  post g s0 sf :=
    match g with
    | (ro, st, m) =>
      ⌜sf.readReg64 Reg.x0 = s0.readReg64 Reg.x0⌝ ∗
        (∃∗ st' : List (BitVec 8), ⌜Absorbs st m st'⌝ ∗ (s0.readReg64 Reg.x0 ↦ₛ st')) ∗
        bytesIn ro (s0.readReg64 Reg.x1) m ∗ stackFrame s0 32

/-! ## The final step -/

/-- Contract of the internal `poly1305_finish(st, mac)` (`x0 = st`, `x1 = mac`), ghost `(st, mac)`:
entered owning the 96 state bytes `st` at `st`, whose first 48 bytes satisfy `StateOk` and whose
`leftover` (offset 64) is below 16, the 16 bytes `mac` at `mac`, and a 4128-byte stack frame below
`sp`, it returns with the 96 state bytes zero, the 16 bytes `finishTag st` at `mac`, and the stack
frame handed back. -/
def finishSpec : Spec (List (BitVec 8) × List (BitVec 8)) where
  pre g s0 :=
    match g with
    | (st, mac) =>
      ⌜st.length = 96 ∧ StateOk (st.take 48) ∧ u64At st 64 < 16 ∧ mac.length = 16⌝ ∗
        (s0.readReg64 Reg.x0 ↦ₛ st) ∗ (s0.readReg64 Reg.x1 ↦ₛ mac) ∗ stackFrame s0 4128
  post g s0 _ :=
    match g with
    | (st, _) =>
      (s0.readReg64 Reg.x0 ↦ₛ List.replicate 96 0#8) ∗
        (s0.readReg64 Reg.x1 ↦ₛ finishTag st) ∗ stackFrame s0 4128

/-! ## The streaming functions and the one-shot -/

/-- Contract of `init(state, key)` (`x0 = state`, `x1 = key`), ghost `(ro, st, key)`: entered owning
the 256 bytes `st` at `state` and with the 32 bytes `key` at `key` (owned or read-only, by `ro`), it
returns `0` in `w0`, with 256 bytes `st'` at `state` such that `Rep state st' key []`, and `key`
handed back. It uses no stack. -/
def initSpec (Rep : StateRep) : Spec (Bool × List (BitVec 8) × List (BitVec 8)) where
  pre g s0 :=
    match g with
    | (ro, st, key) =>
      ⌜st.length = 256 ∧ key.length = 32⌝ ∗
        (s0.readReg64 Reg.x0 ↦ₛ st) ∗ bytesIn ro (s0.readReg64 Reg.x1) key
  post g s0 sf :=
    match g with
    | (ro, _, key) =>
      ⌜sf.readReg32 Reg.x0 = 0#32⌝ ∗
        (∃∗ st' : List (BitVec 8),
          ⌜st'.length = 256 ∧ Rep (s0.readReg64 Reg.x0) st' key []⌝ ∗
            (s0.readReg64 Reg.x0 ↦ₛ st')) ∗
        bytesIn ro (s0.readReg64 Reg.x1) key

/-- Contract of `update(state, in, inlen)` (`x0 = state`, `x1 = in`, `x2 = inlen`), ghost
`(ro, st, key, m, inp)`: entered owning the 256 bytes `st` at `state` with `Rep state st key m`, the
bytes `inp` at `in` (owned or read-only, by `ro`), `inlen = inp.length` and a 48-byte stack frame
below `sp`, it returns `0` in `w0`, with 256 bytes `st'` at `state` such that
`Rep state st' key (m ++ inp)`, and `inp` and the stack frame handed back. -/
def updateSpec (Rep : StateRep) :
    Spec (Bool × List (BitVec 8) × List (BitVec 8) × List (BitVec 8) × List (BitVec 8)) where
  pre g s0 :=
    match g with
    | (ro, st, key, m, inp) =>
      ⌜st.length = 256 ∧ Rep (s0.readReg64 Reg.x0) st key m ∧
          (s0.readReg64 Reg.x2).toNat = inp.length⌝ ∗
        (s0.readReg64 Reg.x0 ↦ₛ st) ∗ bytesIn ro (s0.readReg64 Reg.x1) inp ∗ stackFrame s0 48
  post g s0 sf :=
    match g with
    | (ro, _, key, m, inp) =>
      ⌜sf.readReg32 Reg.x0 = 0#32⌝ ∗
        (∃∗ st' : List (BitVec 8),
          ⌜st'.length = 256 ∧ Rep (s0.readReg64 Reg.x0) st' key (m ++ inp)⌝ ∗
            (s0.readReg64 Reg.x0 ↦ₛ st')) ∗
        bytesIn ro (s0.readReg64 Reg.x1) inp ∗ stackFrame s0 48

/-- Contract of `final(state, out)` (`x0 = state`, `x1 = out`), ghost `(st, key, m, mac)`: entered
owning the 256 bytes `st` at `state` with `Rep state st key m`, the 16 bytes `mac` at `out` and a
4144-byte stack frame below `sp`, it returns `0` in `w0`, with the first 96 bytes of the state zero
and the other 160 unchanged, the 16 bytes `poly1305Mac m key` at `out`, and the stack frame handed
back. -/
def finalSpec (Rep : StateRep) :
    Spec (List (BitVec 8) × List (BitVec 8) × List (BitVec 8) × List (BitVec 8)) where
  pre g s0 :=
    match g with
    | (st, key, m, mac) =>
      ⌜st.length = 256 ∧ Rep (s0.readReg64 Reg.x0) st key m ∧ mac.length = 16⌝ ∗
        (s0.readReg64 Reg.x0 ↦ₛ st) ∗ (s0.readReg64 Reg.x1 ↦ₛ mac) ∗ stackFrame s0 4144
  post g s0 sf :=
    match g with
    | (st, key, m, _) =>
      ⌜sf.readReg32 Reg.x0 = 0#32⌝ ∗
        (s0.readReg64 Reg.x0 ↦ₛ (List.replicate 96 0#8 ++ st.drop 96)) ∗
        (s0.readReg64 Reg.x1 ↦ₛ poly1305Mac m key) ∗ stackFrame s0 4144

/-- Contract of the one-shot `(out, m, inlen, key)` (`x0 = out`, `x1 = m`, `x2 = inlen`, `x3 = key`)
under the placement `pl`, ghost `(roM, roK, out, m, key, g)`: entered owning the 16 bytes `out` at
`out`, with the message bytes `m` at `m` (owned or read-only, by `roM`), `inlen = m.length`, the
32 bytes `key` at `key` (owned or read-only, by `roK`), the stack-protector guard `g` readable
(`guardRes pl g`) and a 4320-byte stack frame below `sp`, it returns `0` in `w0`, with the 16 bytes
`poly1305Mac m key` at `out`, and `m`, `key`, the guard and the stack frame handed back. -/
def oneshotSpec (pl : Placement) :
    Spec (Bool × Bool × List (BitVec 8) × List (BitVec 8) × List (BitVec 8) × BitVec 64) where
  pre g s0 :=
    match g with
    | (roM, roK, out, m, key, gd) =>
      ⌜out.length = 16 ∧ (s0.readReg64 Reg.x2).toNat = m.length ∧ key.length = 32⌝ ∗
        (s0.readReg64 Reg.x0 ↦ₛ out) ∗ bytesIn roM (s0.readReg64 Reg.x1) m ∗
        bytesIn roK (s0.readReg64 Reg.x3) key ∗ guardRes pl gd ∗ stackFrame s0 4320
  post g s0 sf :=
    match g with
    | (roM, roK, _, m, key, gd) =>
      ⌜sf.readReg32 Reg.x0 = 0#32⌝ ∗
        (s0.readReg64 Reg.x0 ↦ₛ poly1305Mac m key) ∗ bytesIn roM (s0.readReg64 Reg.x1) m ∗
        bytesIn roK (s0.readReg64 Reg.x3) key ∗ guardRes pl gd ∗ stackFrame s0 4320

/-! ## The donna functions (internal) -/

/-- The donna `_init` meets `initSpec Rep`. -/
def donnaInitOk (Rep : StateRep) : Prop :=
  internalOk "crypto_onetimeauth_poly1305_donna_init [libsodium_la_poly1305_donna]"
    (fun _ => initSpec Rep)

/-- The donna `_update` meets `updateSpec Rep`. -/
def donnaUpdateOk (Rep : StateRep) : Prop :=
  internalOk "crypto_onetimeauth_poly1305_donna_update [libsodium_la_poly1305_donna]"
    (fun _ => updateSpec Rep)

/-- The donna `_final` meets `finalSpec Rep`. -/
def donnaFinalOk (Rep : StateRep) : Prop :=
  internalOk "crypto_onetimeauth_poly1305_donna_final [libsodium_la_poly1305_donna]"
    (fun _ => finalSpec Rep)

/-- The donna one-shot meets `oneshotSpec`. -/
def donnaOneshotOk : Prop :=
  internalOk "crypto_onetimeauth_poly1305_donna [libsodium_la_poly1305_donna]" oneshotSpec

/-! ## The public functions -/

/-- `crypto_onetimeauth_init` meets `initSpec Rep`. -/
def initPublicOk (Rep : StateRep) : Prop :=
  publicOk "crypto_onetimeauth_init" (fun _ => initSpec Rep)

/-- `crypto_onetimeauth_update` meets `updateSpec Rep`. -/
def updatePublicOk (Rep : StateRep) : Prop :=
  publicOk "crypto_onetimeauth_update" (fun _ => updateSpec Rep)

/-- `crypto_onetimeauth_final` meets `finalSpec Rep`. -/
def finalPublicOk (Rep : StateRep) : Prop :=
  publicOk "crypto_onetimeauth_final" (fun _ => finalSpec Rep)

/-- `crypto_onetimeauth` meets `oneshotSpec`. -/
def oneshotPublicOk : Prop :=
  publicOk "crypto_onetimeauth" oneshotSpec

end Poly1305Debian


