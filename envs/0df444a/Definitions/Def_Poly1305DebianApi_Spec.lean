-- Prove2me | Definitions.Def_Poly1305DebianApi_Spec
-- name    : Poly1305DebianApi_Spec
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-26T11:23:39.558465+00:00
-- url     : https://prove2.me/theorems/e9f115b0-01ac-4fd1-8aba-fef7b3e917df
-- title:
--   Contracts of the public API of Debian's libsodium Poly1305 and crypto_verify on AArch64
-- statement:
--   The judgments and the contracts of every public function of `libsodiumDebianOnetimeauthCtLib` (bundle `Poly1305DebianCt_PlacedObj`: Debian's objects of `crypto_onetimeauth.c`, `onetimeauth_poly1305.c`, `poly1305_donna.c` and `crypto_verify/verify.c`), and of the internal functions their proofs go through. The library `lib`, `MemsetOk`, `GuardUniform` and `guardRes` come from the bundle `Poly1305DebianCt_Spec`. The state layout and its helpers come from the bundle `Poly1305Libsodium_Spec`, which describes the same C source: `u64At`, the limbs `rLimb` and `hLimb` and their value `limbVal`, the invariant `StateOk` on the 48 bytes of `r` and `h` (`r` at most the clamping masks, `h[0] < 2^44`, `h[1] < 2^44 + 64`, `h[2] < 2^42`), `hibit`, the block step `blocksAcc`, `bytesIn` (owned or read-only bytes), `MemzeroOk`, the tag `finishTag` and the representation predicates `StateRep`.
--
--   **Hypotheses.**
--   - `MemsetOk externs` (bundle `Poly1305DebianCt_Spec`): the hook for `memset` meets DeepMind's published contract `VerifiedLibraries.Musl.cryptoMemsetSpec` (it sets the `x2` bytes at `x0` to the low byte of `x1`, returns `x0`, and may use 4096 bytes of stack). `MemzeroOk externs` (bundle `Poly1305Libsodium_Spec`): the hook for `sodium_memzero` meets `Libc.explicitBzeroSpec`.
--   - `GuardUniform pl` (bundle `Poly1305DebianCt_Spec`) says the linker relaxed all of the code's GOT accesses to `__stack_chk_guard` or none of them. `guard pl g` is the guard with value `g`, read-only, where the code reads it: `guardRes pl ga g` for some address `ga`, that is, the 8 bytes of `g` at the address the placement gives `__stack_chk_guard` when the accesses are relaxed, otherwise a GOT slot there holding `ga` and the 8 bytes of `g` at `ga`.
--   - `randombytesSpec R`, for a property `R n bs` of a requested length `n` and a byte string `bs`, is a contract for `randombytes_buf(buf, size)` in the form of DeepMind's C hooks (`VerifiedLibraries.Musl.cExtern`: arguments in `x0` and `x1`, callee-saved registers preserved, 4096 bytes of stack): entered owning the `size` bytes at `buf`, it returns with `size` bytes `bs` there such that `R size bs`. `RandomOk R externs` says the hook for `randombytes_buf` meets it.
--
--   **Judgments.** All three quantify over every placement `pl` under which the library is `Placeable` and `GuardUniform pl` holds, and every hook table `externs` with `MemzeroOk externs`, `MemsetOk externs` and `Link.PlacedLib.LinkOk lib pl externs`. `LinkOk` says the library is laid out as a real link lays it out: two external functions at one address have the same hook, no external function lies in the code or a data object, and the data objects are disjoint from each other and from the code. Each also asks that `f` be a symbol of the code block; the bundle's export list is not used, since it names only some of the public functions.
--   - `internalOk f spec`: the placed program meets `spec pl` at `f`.
--   - `dataOk f spec`: the placed program meets `withData pl (spec pl)` at `f`, where `withData` adds the library's data objects in their initial state (`PlacedLib.dataInit`: the pointer `implementation`, the table and `optblocker_u16`, owned since they are writable, and the read-only string) to the precondition and to the postcondition.
--   - `randomOk R f spec`: as `dataOk`, for hook tables that in addition satisfy `RandomOk R externs`.
--
--   "Meets" is `subroutine_ok`. Take every entry state at the function with the stack pointer 16-byte aligned and every frame $R$ held separately. Execution terminates and returns to the caller with the stack pointer and the callee-saved registers restored, $R$ untouched and the postcondition holding. It never panics, exits or runs out of memory.
--
--   **Contracts.** In each, the stack frame is the bytes below the stack pointer that the caller lends, covering the function's own use and 4096 bytes for any `memset` or `sodium_memzero` hook it reaches.
--   - `blocksSpec`, for `poly1305_blocks(st, m, bytes)`, ghost $(ro, rh, fin, m)$. Before: `st` owns the 48 bytes $rh$ with `StateOk`, and the `final` byte $fin$ at offset 88. The bytes $m$ are at `m` (`bytesIn ro`), with `bytes` $= |m| \ge 16$ and a multiple of 16. After: `x0` and `x18` are unchanged, and `st` holds 48 bytes $rh'$ with `StateOk`, the same $r$ (first 24 bytes), and `limbVal (hLimb rh')` $\equiv$ `blocksAcc (limbVal (rLimb rh)) (hibit fin) (limbVal (hLimb rh)) m` $\pmod{2^{130}-5}$. $fin$ and $m$ are handed back. No stack is used.
--   - `Absorbs st m st'` relates 96 state bytes before and after absorbing message bytes $m$. Let $L$ be `leftover` (offset 64), $t$ the first $L$ bytes of `buffer` (offset 72) followed by $m$, and $k = 16\lfloor |t|/16 \rfloor$. Then $st'$ keeps `r` (bytes 0–23), `pad` (48–63) and `final` (88) of $st$, satisfies `StateOk` on its first 48 bytes, has `leftover` $= |t| - k$ with the last $|t| - k$ bytes of $t$ at the start of `buffer`, and has an accumulator congruent modulo $2^{130} - 5$ to `blocksAcc` run on the first $k$ bytes of $t$ with $r$, `hibit final` and the old accumulator.
--   - `updateIntSpec`, for `poly1305_update(st, m, bytes)`, ghost $(ro, st, m)$. Before: `st` owns 96 bytes $st$ with `StateOk` on the first 48 and `leftover` $< 16$. The bytes $m$ are at `m` (`bytesIn ro`), with `bytes` $= |m|$, and the frame is 32 bytes. After: `x0` is unchanged, and `st` holds 96 bytes $st'$ with `Absorbs st m st'`. $m$ and the frame are handed back.
--   - `finishSpec`, for `poly1305_finish(st, mac)`, ghost $(st, mac)$. Before: `st` owns 96 bytes $st$ with `StateOk` on the first 48 and `leftover` $< 16$, `mac` owns 16 bytes, and the frame is 4128 bytes. After: the 96 state bytes are zero, `mac` holds `finishTag st`, and the frame is handed back.
--   - `initSpec Rep`, `updateSpec Rep`, `finalSpec Rep` and `oneshotSpec pl` are the contracts of `init(state, key)`, `update(state, in, inlen)`, `final(state, out)` and the one-shot `(out, m, inlen, key)`. A representation predicate $\mathrm{Rep}(a, st, key, m)$ relates the address of a 256-byte state, its bytes, a key and the bytes absorbed. Each returns `0` in `w0`, and inputs may be owned or read-only.
--     - Init, with no stack, turns 256 owned bytes into $st'$ with $\mathrm{Rep}(\mathtt{state}, st', key, [\,])$.
--     - Update, with a 48-byte frame, turns $\mathrm{Rep}(\mathtt{state}, st, key, m)$ into $\mathrm{Rep}(\mathtt{state}, st', key, m \mathbin{+\!\!+} inp)$.
--     - Final, with a 4144-byte frame, writes `poly1305Mac m key` to the 16 bytes at `out` and leaves the first 96 bytes of the state zero and the other 160 unchanged.
--     - The one-shot, with a 4320-byte frame and the guard `guard pl g` lent and handed back, writes `poly1305Mac m key` to `out`.
--   - `okResult ok` is the C `int` result `0` if `ok` and `-1` otherwise, as the 32 bits of `w0`.
--   - `verifySpec pl`, for the verification `(h, in, inlen, k)`, ghost $(roH, roM, roK, h, m, key, g)$. Before: the 16 bytes $h$ at `h`, the bytes $m$ at `in` with `inlen` $= |m|$ and the 32 bytes $key$ at `k`, each owned or read-only; the guard `guard pl g`; a 4352-byte frame. After: `w0` is `okResult` of $h$ = `poly1305Mac m key`, and everything is handed back unchanged.
--   - `verifyNSpec n`, for `crypto_verify_n(x, y)`, ghost $(roX, roY, a, b)$. Before: the $n$ bytes $a$ at `x` and $b$ at `y`, each owned or read-only; a 32-byte frame. After: `w0` is `okResult` of $a = b$, and everything is handed back unchanged.
--   - `keygenSpec R`, for `keygen(k)`. Before: 32 owned bytes at `k` and a 4096-byte frame. After: 32 bytes `bs` with `R 32 bs` at `k`, and the frame handed back.
--   - `constSpec n`, for a getter: nothing before; `x0` $= n$ after. `primitiveSpec pl`, for `crypto_onetimeauth_primitive()`: nothing before; after, `x0` is the address `pl.ρ primitiveSym` of the library's data object `primitiveSym`, and that object's bytes are `poly1305Str`, the bytes of the C string `"poly1305"` with its terminating zero.
--   - `initOk Rep f`, `updateOk Rep f`, `finalOk Rep f`, `oneshotOk f`, `verifyOk f` and `constOk f n` are `dataOk` of `f` with `initSpec Rep`, `updateSpec Rep`, `finalSpec Rep`, `oneshotSpec`, `verifySpec` and `constSpec n`; `keygenOk f` is `randomOk R f (keygenSpec R)` for every `R`.
--
--   **Why the register clauses.** `poly1305_blocks` and `poly1305_update` are `static`, and the compiler's calls to them rely on more than the calling convention guarantees. After `poly1305_blocks` returns, `poly1305_update` goes on using `x0` and `x18` without having saved them, and after `poly1305_update` returns, the one-shot passes the state pointer still in `x0` to `poly1305_finish`. The contracts state these facts so that the callers' correctness follows from them.
--
--   **Where the source says it.** `crypto_onetimeauth_poly1305.h`, lines 19–21, 26 and 30: “typedef struct CRYPTO_ALIGN(16) crypto_onetimeauth_poly1305_state { unsigned char opaque[256]; } crypto_onetimeauth_poly1305_state;”, “#define crypto_onetimeauth_poly1305_BYTES 16U”, “#define crypto_onetimeauth_poly1305_KEYBYTES 32U”. The contracts hold for a state at any address, not only a 16-byte-aligned one. `poly1305_donna64.h`, lines 22 and 25–32: “#define poly1305_block_size 16”, “typedef struct poly1305_state_internal_t { unsigned long long r[3]; unsigned long long h[3]; unsigned long long pad[2]; unsigned long long leftover; unsigned char buffer[poly1305_block_size]; unsigned char final; } poly1305_state_internal_t;”; with 8-byte `unsigned long long` this puts `r` at offset 0, `h` at 24, `pad` at 48, `leftover` at 64, `buffer` at 72 and `final` at 88, the offsets the contracts read. The functions with contracts here, by their definitions: `poly1305_donna64.h`, lines 61–63, “static void poly1305_blocks(poly1305_state_internal_t *st, const unsigned char *m, unsigned long long bytes)”, whose loop “while (bytes >= poly1305_block_size) {” (line 84) does “/* h += m[i] */”, “/* h *= r */” and “/* (partial) h %= p */”; lines 135–136, “static POLY1305_NOINLINE void poly1305_finish(poly1305_state_internal_t *st, unsigned char mac[16])”; `poly1305_donna.c`, lines 14–16, “static void poly1305_update(poly1305_state_internal_t *st, const unsigned char *m, unsigned long long bytes)”, whose steps are “/* handle leftover */”, “/* process full blocks */” and “/* store leftover */”; lines 58–61, “static int crypto_onetimeauth_poly1305_donna(unsigned char *out, const unsigned char *m, unsigned long long inlen, const unsigned char *key)”, whose body is “poly1305_init(&state, key); poly1305_update(&state, m, inlen); poly1305_finish(&state, out);” on a local state, then “return 0;”; lines 72–74, 83–86 and 93–95, “static int crypto_onetimeauth_poly1305_donna_init(crypto_onetimeauth_poly1305_state *state, const unsigned char *key)”, “static int crypto_onetimeauth_poly1305_donna_update( crypto_onetimeauth_poly1305_state *state, const unsigned char *in, unsigned long long inlen)” and “static int crypto_onetimeauth_poly1305_donna_final( crypto_onetimeauth_poly1305_state *state, unsigned char *out)”, which run `poly1305_init`, `poly1305_update` and `poly1305_finish` on the state and return 0; and `crypto_onetimeauth.c`, lines 23–60, “int crypto_onetimeauth(unsigned char *out, const unsigned char *in, unsigned long long inlen, const unsigned char *k) { return crypto_onetimeauth_poly1305(out, in, inlen, k); }”, “int crypto_onetimeauth_init(crypto_onetimeauth_state *state, const unsigned char *key) { return crypto_onetimeauth_poly1305_init ((crypto_onetimeauth_poly1305_state *) state, key); }”, “int crypto_onetimeauth_update(crypto_onetimeauth_state *state, const unsigned char *in, unsigned long long inlen) { return crypto_onetimeauth_poly1305_update ((crypto_onetimeauth_poly1305_state *) state, in, inlen); }”, “int crypto_onetimeauth_final(crypto_onetimeauth_state *state, unsigned char *out) { return crypto_onetimeauth_poly1305_final ((crypto_onetimeauth_poly1305_state *) state, out); }”.
--
--   **The functions this bundle adds.** Verification: libsodium's documentation, *Secret-key single-message authentication using Poly1305*, lines 72 and 74, “The `crypto_onetimeauth_verify()` function verifies, in constant time, that `h` is a correct authenticator for the message `in` whose length is `inlen` bytes, using the secret key `k`.” and “It returns `-1` if the verification fails, or `0` on success.” (`verifySpec` states the functional half; the constant-time half is the subject of the companion constant-time mission). The code: `crypto_onetimeauth.c`, lines 31–34, “return crypto_onetimeauth_poly1305_verify(h, in, inlen, k);”; `onetimeauth_poly1305.c`, lines 25–30, “return implementation->onetimeauth_verify(h, in, inlen, k);”; `poly1305_donna.c`, lines 102–113, “unsigned char correct[16]; crypto_onetimeauth_poly1305_donna(correct, in, inlen, k); return crypto_verify_16(h, correct);”; `verify.c`, lines 87–103, “return crypto_verify_n(x, y, crypto_verify_16_BYTES);” and likewise for 32 and 64 (`verifyNSpec`). Key generation: documentation line 110, “The `crypto_onetimeauth_keygen()` function fills `k` with a random key.”, and `crypto_onetimeauth.c`, lines 68–71, “randombytes_buf(k, crypto_onetimeauth_KEYBYTES);” (`onetimeauth_poly1305.c`, lines 74–78, likewise); `keygenSpec R` states it relative to `randombytes_buf`'s output, since randomness is not modelled. Constants: `crypto_onetimeauth.c`, lines 5–20 and 62–66, “return sizeof(crypto_onetimeauth_state);”, “return crypto_onetimeauth_BYTES;”, “return crypto_onetimeauth_KEYBYTES;” and “return crypto_onetimeauth_PRIMITIVE;”, and `onetimeauth_poly1305.c`, lines 55–72, likewise for the `crypto_onetimeauth_poly1305_` getters (`constSpec`, `primitiveSpec`). The state: documentation lines 96, 102 and 104, “A 16-byte alignment is required for the address of `state`.”, “The state must be initialized with `crypto_onetimeauth_init()` before updating or finalizing it.” and “After `crypto_onetimeauth_final()` returns, the state should not be used any more, unless it is reinitialized using `crypto_onetimeauth_init()`.”; the contracts hold at any address, and `Rep` carries the protocol. The dispatch: `onetimeauth_poly1305.c`, lines 14–15, “static const crypto_onetimeauth_poly1305_implementation *implementation = &crypto_onetimeauth_poly1305_donna_implementation;”, the pointer the data objects hold in their initial state; `poly1305_init` (`poly1305_donna64.h`, lines 34–59) has no contract of its own and is part of the donna `_init` and the one-shot.
-- source:
--   libsodium 1.0.22-RELEASE, commit 77e1ce5d6dee871c49ef211222ba18ef0c486bda (https://github.com/jedisct1/libsodium/tree/77e1ce5d6dee871c49ef211222ba18ef0c486bda), src/libsodium/crypto_onetimeauth/poly1305/donna/poly1305_donna64.h lines 25–32 (poly1305_state_internal_t) and 61–221, src/libsodium/crypto_onetimeauth/poly1305/donna/poly1305_donna.c lines 14–124, src/libsodium/crypto_onetimeauth/crypto_onetimeauth.c, poly1305/onetimeauth_poly1305.c, src/libsodium/crypto_verify/verify.c lines 60–103 and src/libsodium/include/sodium/crypto_onetimeauth_poly1305.h lines 19–62

import Definitions.Def_Poly1305DebianCt_Spec

/-!
# Contracts of the public API of Debian's libsodium Poly1305 on AArch64

The library is `libsodiumDebianOnetimeauthCtLib` (bundle `Poly1305DebianCt_PlacedObj`): the objects of
`crypto_onetimeauth.c`, `onetimeauth_poly1305.c`, `poly1305_donna.c` and `crypto_verify/verify.c` from
Debian's libsodium 1.0.22-2 for arm64, unmodified, linked into one text block. The state layout
`poly1305_state_internal_t`, the limb invariant `StateOk`, the block step `blocksAcc`, the tag
`finishTag` and the representation predicates `StateRep` are those of bundle `Poly1305Libsodium_Spec`;
the placement conditions `GuardUniform`, the guard resource `guardRes` and the hook condition `MemsetOk`
are those of bundle `Poly1305DebianCt_Spec`.

Every judgment quantifies over the placements of the library (`Placeable`) that are laid out as a real
link lays them out (`Link.PlacedLib.LinkOk`) and treat every GOT access to `__stack_chk_guard` alike
(`GuardUniform`), and over the hooks that call, for `sodium_memzero`, a function meeting
`Libc.explicitBzeroSpec` (`MemzeroOk`) and, for `memset`, one meeting
`VerifiedLibraries.Musl.cryptoMemsetSpec` (`MemsetOk`). The key-generation judgment also assumes a
contract for `randombytes_buf` (`RandomOk`).
-/

namespace Poly1305DebianApi

open Arm64 Arm64.Obj Poly1305Boringssl
open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag
  StateRep)
open Poly1305DebianCt (lib MemsetOk GuardUniform guardRes)

/-! ## The guard and `randombytes_buf` -/

/-- The stack-protector guard with value `g`, readable where the code reads it under `pl`
(`Poly1305DebianCt.guardRes pl ga g` for some GOT target `ga`). Read-only. -/
def guard (pl : Placement) (g : BitVec 64) : SepProp :=
  ∃∗ ga : BitVec 64, guardRes pl ga g

/-- Contract of `randombytes_buf(buf, size)` (`x0 = buf`, `x1 = size`) given a property `R` of its
output, ghost `(buf, n)`: a C function (`VerifiedLibraries.Musl.cExtern`) that, entered owning the
`n` bytes at `buf`, returns with `n` bytes `bs` at `buf` such that `R n bs`. -/
def randombytesSpec (R : Nat → List (BitVec 8) → Prop) : Spec (BitVec 64 × Nat) :=
  VerifiedLibraries.Musl.cExtern
    (fun (p, n) s => s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = n)
    (fun (p, n) => memRegion p n)
    (fun (p, n) _ => ∃∗ bs : List (BitVec 8), ⌜bs.length = n ∧ R n bs⌝ ∗ (p ↦ₛ bs))

/-- The hooks `externs` call, for `randombytes_buf`, a function meeting `randombytesSpec R`. -/
def RandomOk (R : Nat → List (BitVec 8) → Prop) (externs : String → Option (State → State)) : Prop :=
  HookSat externs "randombytes_buf" (randombytesSpec R)

/-! ## Judgments -/

/-- Correctness of the function `fnName` of the library, without its data: `fnName` is a symbol of
the text block, and for every placement `pl` under which the library is `Placeable` with
`GuardUniform pl`, and all hooks `externs` with `MemzeroOk externs`, `MemsetOk externs` and
`Link.PlacedLib.LinkOk lib pl externs`, `subroutine_ok` holds for the placed program at the address
of `fnName`. -/
def internalOk {α : Type} (fnName : String) (spec : Placement → Spec α) : Prop :=
  fnName ∈ lib.text.symbols.map Prod.fst ∧
  ∀ pl : Placement, lib.Placeable pl → GuardUniform pl →
    ∀ externs : String → Option (State → State), MemzeroOk externs → MemsetOk externs →
      Link.PlacedLib.LinkOk lib pl externs →
        subroutine_ok (lib.program pl externs) (lib.fnAddr pl fnName) (spec pl)

/-- `spec` with the library's data objects, in their initial state under `pl`
(`PlacedLib.dataInit`), added to the precondition and to the postcondition. -/
def withData {α : Type} (pl : Placement) (spec : Spec α) : Spec α :=
  { spec with
    pre := fun x s0 => spec.pre x s0 ∗ lib.dataInit pl
    post := fun x s0 sf => spec.post x s0 sf ∗ lib.dataInit pl }

/-- Correctness of the function `fnName` of the library, with its data: as `internalOk`, for
`spec pl` with the library's data objects lent to the call (`withData`). -/
def dataOk {α : Type} (fnName : String) (spec : Placement → Spec α) : Prop :=
  fnName ∈ lib.text.symbols.map Prod.fst ∧
  ∀ pl : Placement, lib.Placeable pl → GuardUniform pl →
    ∀ externs : String → Option (State → State), MemzeroOk externs → MemsetOk externs →
      Link.PlacedLib.LinkOk lib pl externs →
        subroutine_ok (lib.program pl externs) (lib.fnAddr pl fnName) (withData pl (spec pl))

/-- `dataOk` with, in addition, hooks whose `randombytes_buf` meets `randombytesSpec R`
(`RandomOk R externs`). -/
def randomOk {α : Type} (R : Nat → List (BitVec 8) → Prop) (fnName : String)
    (spec : Placement → Spec α) : Prop :=
  fnName ∈ lib.text.symbols.map Prod.fst ∧
  ∀ pl : Placement, lib.Placeable pl → GuardUniform pl →
    ∀ externs : String → Option (State → State), MemzeroOk externs → MemsetOk externs →
      RandomOk R externs → Link.PlacedLib.LinkOk lib pl externs →
        subroutine_ok (lib.program pl externs) (lib.fnAddr pl fnName) (withData pl (spec pl))

/-! ## The block routine, `poly1305_update` and `poly1305_finish` (internal) -/

/-- Contract of the internal `poly1305_blocks(st, m, bytes)` (`x0 = st`, `x1 = m`, `x2 = bytes`),
ghost `(ro, rh, fin, m)`: entered owning the 48 bytes `rh` (`r` and `h`) at `st` with `StateOk rh`,
the `final` byte `fin` at `st + 88`, the message bytes `m` at `m` (owned or read-only, by `ro`), and
`bytes = m.length`, a multiple of 16 and at least 16, it returns with `x0` and `x18` unchanged, with
48 bytes `rh'` at `st` that satisfy `StateOk`, keep `r` (the first 24 bytes), and whose accumulator is
congruent modulo `2^130 - 5` to `blocksAcc` run on `m` with `r`, `hibit fin` and the old accumulator;
`fin` and `m` are handed back. It uses no stack. -/
def blocksSpec : Spec (Bool × List (BitVec 8) × BitVec 8 × List (BitVec 8)) where
  pre g s0 :=
    match g with
    | (ro, rh, fin, m) =>
      ⌜StateOk rh ∧ (s0.readReg64 Reg.x2).toNat = m.length ∧ 16 ≤ m.length ∧ m.length % 16 = 0⌝ ∗
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

/-! ## The streaming functions, the one-shot and verification -/

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
(`guard pl g`) and a 4320-byte stack frame below `sp`, it returns `0` in `w0`, with the 16 bytes
`poly1305Mac m key` at `out`, and `m`, `key`, the guard and the stack frame handed back. -/
def oneshotSpec (pl : Placement) :
    Spec (Bool × Bool × List (BitVec 8) × List (BitVec 8) × List (BitVec 8) × BitVec 64) where
  pre g s0 :=
    match g with
    | (roM, roK, out, m, key, gd) =>
      ⌜out.length = 16 ∧ (s0.readReg64 Reg.x2).toNat = m.length ∧ key.length = 32⌝ ∗
        (s0.readReg64 Reg.x0 ↦ₛ out) ∗ bytesIn roM (s0.readReg64 Reg.x1) m ∗
        bytesIn roK (s0.readReg64 Reg.x3) key ∗ guard pl gd ∗ stackFrame s0 4320
  post g s0 sf :=
    match g with
    | (roM, roK, _, m, key, gd) =>
      ⌜sf.readReg32 Reg.x0 = 0#32⌝ ∗
        (s0.readReg64 Reg.x0 ↦ₛ poly1305Mac m key) ∗ bytesIn roM (s0.readReg64 Reg.x1) m ∗
        bytesIn roK (s0.readReg64 Reg.x3) key ∗ guard pl gd ∗ stackFrame s0 4320

/-- The C `int` result `0` when `ok`, `-1` otherwise, as the 32 bits of `w0`. -/
def okResult (ok : Bool) : BitVec 32 :=
  if ok then 0#32 else BitVec.allOnes 32

/-- Contract of the verification `(h, in, inlen, k)` (`x0 = h`, `x1 = in`, `x2 = inlen`, `x3 = k`)
under the placement `pl`, ghost `(roH, roM, roK, h, m, key, g)`: entered with the 16 bytes `h` at `h`,
the message bytes `m` at `in` with `inlen = m.length` and the 32 bytes `key` at `k` (each owned or
read-only, by `roH`, `roM`, `roK`), the stack-protector guard `g` readable (`guard pl g`) and a
4352-byte stack frame below `sp`, it returns in `w0` `0` if `h = poly1305Mac m key` and `-1`
otherwise, with `h`, `m`, `key`, the guard and the stack frame handed back. -/
def verifySpec (pl : Placement) :
    Spec (Bool × Bool × Bool × List (BitVec 8) × List (BitVec 8) × List (BitVec 8) × BitVec 64) where
  pre g s0 :=
    match g with
    | (roH, roM, roK, h, m, key, gd) =>
      ⌜h.length = 16 ∧ (s0.readReg64 Reg.x2).toNat = m.length ∧ key.length = 32⌝ ∗
        bytesIn roH (s0.readReg64 Reg.x0) h ∗ bytesIn roM (s0.readReg64 Reg.x1) m ∗
        bytesIn roK (s0.readReg64 Reg.x3) key ∗ guard pl gd ∗ stackFrame s0 4352
  post g s0 sf :=
    match g with
    | (roH, roM, roK, h, m, key, gd) =>
      ⌜sf.readReg32 Reg.x0 = okResult (decide (h = poly1305Mac m key))⌝ ∗
        bytesIn roH (s0.readReg64 Reg.x0) h ∗ bytesIn roM (s0.readReg64 Reg.x1) m ∗
        bytesIn roK (s0.readReg64 Reg.x3) key ∗ guard pl gd ∗ stackFrame s0 4352

/-- Contract of `crypto_verify_n(x, y)` (`x0 = x`, `x1 = y`) for `n` = 16, 32 or 64, ghost
`(roX, roY, a, b)`: entered with the `n` bytes `a` at `x` and `b` at `y` (each owned or read-only, by
`roX`, `roY`) and a 32-byte stack frame below `sp`, it returns in `w0` `0` if `a = b` and `-1`
otherwise, with `a`, `b` and the stack frame handed back. -/
def verifyNSpec (n : Nat) : Spec (Bool × Bool × List (BitVec 8) × List (BitVec 8)) where
  pre g s0 :=
    match g with
    | (roX, roY, a, b) =>
      ⌜a.length = n ∧ b.length = n⌝ ∗ bytesIn roX (s0.readReg64 Reg.x0) a ∗
        bytesIn roY (s0.readReg64 Reg.x1) b ∗ stackFrame s0 32
  post g s0 sf :=
    match g with
    | (roX, roY, a, b) =>
      ⌜sf.readReg32 Reg.x0 = okResult (decide (a = b))⌝ ∗ bytesIn roX (s0.readReg64 Reg.x0) a ∗
        bytesIn roY (s0.readReg64 Reg.x1) b ∗ stackFrame s0 32

/-! ## Key generation and the constants -/

/-- Contract of `keygen(k)` (`x0 = k`) given the property `R` of `randombytes_buf`'s output, ghost
`()`: entered owning the 32 bytes at `k` and a 4096-byte stack frame below `sp`, it returns with 32
bytes `bs` at `k` such that `R 32 bs`, and the stack frame handed back. -/
def keygenSpec (R : Nat → List (BitVec 8) → Prop) : Spec Unit where
  pre _ s0 := memRegion (s0.readReg64 Reg.x0) 32 ∗ stackFrame s0 4096
  post _ s0 _ :=
    (∃∗ bs : List (BitVec 8), ⌜bs.length = 32 ∧ R 32 bs⌝ ∗ (s0.readReg64 Reg.x0 ↦ₛ bs)) ∗
      stackFrame s0 4096

/-- Contract of a constant getter returning the number `n`: entered with nothing, it returns `n` in
`x0`. -/
def constSpec (n : Nat) : Spec Unit where
  pre _ _ := emp
  post _ _ sf := ⌜sf.readReg64 Reg.x0 = BitVec.ofNat 64 n⌝

/-- The library's data object holding the string `crypto_onetimeauth_primitive` returns. -/
def primitiveSym : String := "libsodium_la_crypto_onetimeauth:.rodata.str1.8+0x0"

/-- The bytes of the C string `"poly1305"`, with its terminating zero. -/
def poly1305Str : List (BitVec 8) := ("poly1305".toUTF8.toList ++ [0]).map (fun b : UInt8 => BitVec.ofNat 8 b.toNat)

/-- Contract of `crypto_onetimeauth_primitive()` under `pl`: it returns in `x0` the address of the
library's data object `primitiveSym`, whose bytes are `poly1305Str`. -/
def primitiveSpec (pl : Placement) : Spec Unit where
  pre _ _ := emp
  post _ _ sf :=
    ⌜sf.readReg64 Reg.x0 = pl.ρ primitiveSym ∧
      (lib.data.find? (·.sym = primitiveSym)).map (·.bytes) = some poly1305Str⌝

/-! ## The functions -/

/-- `fnName` meets `initSpec Rep`, with the library's data. -/
def initOk (Rep : StateRep) (fnName : String) : Prop := dataOk fnName (fun _ => initSpec Rep)

/-- `fnName` meets `updateSpec Rep`, with the library's data. -/
def updateOk (Rep : StateRep) (fnName : String) : Prop := dataOk fnName (fun _ => updateSpec Rep)

/-- `fnName` meets `finalSpec Rep`, with the library's data. -/
def finalOk (Rep : StateRep) (fnName : String) : Prop := dataOk fnName (fun _ => finalSpec Rep)

/-- `fnName` meets `oneshotSpec`, with the library's data. -/
def oneshotOk (fnName : String) : Prop := dataOk fnName oneshotSpec

/-- `fnName` meets `verifySpec`, with the library's data. -/
def verifyOk (fnName : String) : Prop := dataOk fnName verifySpec

/-- `fnName` meets `keygenSpec R` whenever `randombytes_buf` meets `randombytesSpec R`, for every `R`. -/
def keygenOk (fnName : String) : Prop :=
  ∀ R : Nat → List (BitVec 8) → Prop, randomOk R fnName (fun _ => keygenSpec R)

/-- `fnName` returns the constant `n`. -/
def constOk (fnName : String) (n : Nat) : Prop := dataOk fnName (fun _ => constSpec n)

end Poly1305DebianApi


