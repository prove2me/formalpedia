-- Prove2me | Definitions.Def_Poly1305Libsodium_Spec
-- name    : Poly1305Libsodium_Spec
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-24T20:58:14.367502+00:00
-- url     : https://prove2.me/theorems/ed643ee4-5375-4db9-98f1-69c47c8758cb
-- title:
--   Contracts of libsodium's Poly1305 (donna64) on AArch64
-- statement:
--   The layout of libsodium's Poly1305 state with an invariant, and contracts for five functions of `libsodiumPoly1305Lib`: the block routine `poly1305_blocks`, the final step `poly1305_finish`, the streaming functions `crypto_onetimeauth_poly1305_donna_init`, `_update` and `_final`, and the one-shot `crypto_onetimeauth_poly1305_donna`. All of them are `static` in the source, so `internalOk f spec` is used in place of the `Arm64` bundles' `subroutineOk`. It says that `f` is a symbol of the code block and that, for every placement of the library the linker could produce and every way of linking `sodium_memzero` allowed by `MemzeroOk`, the placed program meets `spec` at `f` with total correctness. For every ghost value, every frame $R$ and every entry state at `f` with a 16-byte-aligned stack pointer whose memory satisfies the precondition separately from $R$, execution terminates. It returns to the link register with the stack pointer and the AAPCS64 callee-saved registers restored, and the memory satisfies the postcondition, again with $R$ separate. Panics, process exits and running out of memory are excluded. Arguments are in `x0`–`x3` and an `int` result in `w0` (AAPCS64).
--
--   **`sodium_memzero`.** `poly1305_finish` ends with “sodium_memzero((void *) st, sizeof *st);” (`poly1305_donna64.h`, line 220), compiled as a tail call into another file of libsodium. When the C library has `explicit_bzero` and no `memset_s`, as glibc and musl on Linux, that function calls it (`utils.c`, line 132, under `HAVE_EXPLICIT_BZERO`: “explicit_bzero(pnt, len);”). The model treats the call as an external hook: `MemzeroOk externs` says the hook for `sodium_memzero` is present and meets `Libc.explicitBzeroSpec` (bundle `Libc_ExplicitBzero`). Entered with `x0` $= p$ and `x1` $= n$, owning the $n$ bytes at $p$ and the 4096 bytes below the stack pointer, it returns with those $n$ bytes zero and the stack region handed back. The contracts hold for every such hook.
--
--   **The state.** `poly1305_donna64.h`, lines 25–32, declares it:
--
--       typedef struct poly1305_state_internal_t {
--           unsigned long long r[3];
--           unsigned long long h[3];
--           unsigned long long pad[2];
--           unsigned long long leftover;
--           unsigned char      buffer[poly1305_block_size];
--           unsigned char      final;
--       } poly1305_state_internal_t;
--
--   So `r` is at byte offsets 0, 8, 16, `h` at 24, 32, 40, `pad` at 48 and 56, `leftover` at 64, the 16-byte `buffer` at 72 and `final` at 88, 96 bytes in all with padding. The streaming functions use the first 96 bytes of the caller's `crypto_onetimeauth_poly1305_state` (`crypto_onetimeauth_poly1305.h`, lines 19–21: “typedef struct CRYPTO_ALIGN(16) crypto_onetimeauth_poly1305_state { unsigned char opaque[256]; } crypto_onetimeauth_poly1305_state;”). The contracts hold whatever the alignment of the state. `u64At bs off` is the little-endian 64-bit word at byte `off`; `rLimb st i` and `hLimb st i` are the fields `r[i]` and `h[i]` of the bytes `st`; `limbVal f` is $f_0 + 2^{44} f_1 + 2^{88} f_2$.
--
--   `StateOk rh` says that `rh` has 48 bytes (the fields `r` and `h`) and
--   - $r_0 \le$ `0xffc0fffffff`, $r_1 \le$ `0xfffffc0ffff`, $r_2 \le$ `0x00ffffffc0f` (the masks of `poly1305_init`, lines 44–46: “`st->r[0] = (t0) & 0xffc0fffffff;`”, “`st->r[1] = ((t0 >> 44) | (t1 << 20)) & 0xfffffc0ffff;`”, “`st->r[2] = ((t1 >> 24)) & 0x00ffffffc0f;`”);
--   - $h_0 < 2^{44}$, $h_1 < 2^{44} + 64$ and $h_2 < 2^{42}$.
--
--   It is an invariant of our choosing, not libsodium's: the code's 64-bit additions and 128-bit products are exact under bounds of this kind, and the block routine's contract says it preserves these.
--
--   **The block routine** `poly1305_blocks(st, m, bytes)` (lines 61–133). `hibit fin` is $2^{128}$ when the `final` byte `fin` is 0 and 0 otherwise (lines 65–66: “const unsigned long long hibit = (st->final) ? 0ULL : (1ULL << 40); /* 1 << 128 */”, $2^{40}$ in the top limb). `blocksAcc r hb a m` runs $a \leftarrow r \cdot (a + n + hb) \bmod p$, with $p = 2^{130} - 5$, over the $\lfloor |m|/16 \rfloor$ complete 16-byte blocks of $m$ in order, $n$ the little-endian value of the block. `bytesIn ro p bs` is the bytes $bs$ at $p$, owned (`p ↦ₛ bs`) if `ro` is false and read-only (`p ↦ᵣ bs`) if it is true. The contracts state every input both ways, since in the `Arm64` separation logic owned bytes can be lent as read-only ones but not recovered as owned afterwards; `poly1305_finish` passes its own `buffer` to the block routine. `blocksSpec` has ghost value $(ro, rh, fin, m)$. Before: `x0` points to the 48 owned bytes $rh$ with `StateOk` $rh$ and to the owned byte $fin$ at offset 88, the bytes $m$ are at `x1`, `x2` $= |m| \ge 16$, and the caller lends the 64 bytes below the stack pointer. After: `x0` points to 48 bytes $rh'$ with `StateOk` $rh'$, the same first 24 bytes ($r$), and `limbVal (hLimb rh')` $\equiv$ `blocksAcc (limbVal (rLimb rh)) (hibit fin) (limbVal (hLimb rh)) m` $\pmod p$; $fin$, $m$ and the stack frame are handed back. The bytes after the last complete block are not read into the accumulator, as in the source's `while (bytes >= poly1305_block_size)`. The compiled loop processes one block before it first tests the length, so lengths below 16, which the source loop would skip, are excluded.
--
--   **The final step** `poly1305_finish(st, mac)` (lines 135–221). `finishTag st` is the tag computed from the 96 state bytes: with $L$ = `leftover`, $a$ = `limbVal` of $h$ and $r$ = `limbVal` of $r$, if $L \ne 0$ first $a \leftarrow r \cdot (a + n) \bmod p$ with $n$ the little-endian value of the $L$ bytes of `buffer` followed by the byte `0x01`; then the 16 little-endian bytes of $(a \bmod p) + s$, with $s$ the 128-bit little-endian value of `pad`. `finishSpec` has ghost value $(st, mac)$. Before: `x0` points to the 96 owned bytes $st$ whose first 48 satisfy `StateOk` and whose `leftover` is below 16, `x1` to 16 owned bytes, and the caller lends the 4096 bytes below the stack pointer. After: the 96 state bytes are zero, `mac` holds `finishTag st`, and the stack frame is handed back.
--
--   **The streaming functions and the one-shot.** A representation predicate $\mathrm{Rep}$ (of type `StateRep`) relates an address $a$, the 256 bytes at $a$, a key and the bytes absorbed so far. `poly1305Mac` is RFC 8439's `poly1305_mac` (bundle `Poly1305Boringssl_Rfc8439`). Every result is `0` in `w0`.
--   - `initSpec Rep`, for `crypto_onetimeauth_poly1305_donna_init(state, key)`, ghost $(ro, st, key)$. Before: `state` owns 256 bytes $st$, and the 32 bytes $key$ are at `key` (`bytesIn ro`). After: `state` holds 256 bytes $st'$ with $\mathrm{Rep}(\mathtt{state}, st', key, [\,])$; $key$ is handed back. No stack is used.
--   - `updateSpec Rep`, for `crypto_onetimeauth_poly1305_donna_update(state, in, inlen)`, ghost $(ro, st, key, m, inp)$. Before: `state` owns 256 bytes $st$ with $\mathrm{Rep}(\mathtt{state}, st, key, m)$, the bytes $inp$ are at `in` (`bytesIn ro`), `inlen` $= |inp|$, and the caller lends the 112 bytes below the stack pointer. After: `state` holds 256 bytes $st'$ with $\mathrm{Rep}(\mathtt{state}, st', key, m \mathbin{+\!\!+} inp)$; $inp$ and the stack frame are handed back.
--   - `finalSpec Rep`, for `crypto_onetimeauth_poly1305_donna_final(state, out)`, ghost $(st, key, m, mac)$. Before: `state` owns 256 bytes $st$ with $\mathrm{Rep}(\mathtt{state}, st, key, m)$, `out` owns 16 bytes, and the caller lends the 4112 bytes below the stack pointer. After: `state` holds 96 zero bytes followed by the last 160 bytes of $st$, `out` holds `poly1305Mac m key`, and the stack frame is handed back.
--   - `oneshotSpec`, for `crypto_onetimeauth_poly1305_donna(out, m, inlen, key)`, ghost $(roM, roK, out, m, key)$. Before: `out` owns 16 bytes, the bytes $m$ are at `m` (`bytesIn roM`), `inlen` $= |m|$, the 32 bytes $key$ are at `key` (`bytesIn roK`), and the caller lends the 4336 bytes below the stack pointer. After: `out` holds `poly1305Mac m key`; $m$, $key$ and the stack frame are handed back.
--   - `initOk Rep`, `updateOk Rep`, `finalOk Rep` and `oneshotOk` are `internalOk` of the four functions with these contracts.
--
--   `internalOk` admits placements that give `sodium_memzero` and `crypto_verify_16` one address, under which the model runs `crypto_verify_16`'s hook at `poly1305_finish`'s tail call; for that reason `Poly1305Libsodium.internalOk_poly1305_finish` and `Poly1305Libsodium.internalOk_init_update_final_oneshot`, through `oneshotOk`, are Disproved. The bundle `Poly1305Debian_Spec`, for Debian's compiled libsodium, adds `Link.PlacedLib.LinkOk` (bundle `Link_LinkOk`) to its contracts, under which externs placed at one address have the same hook.
--
--   The separating conjunctions make the state, the key, the input, the output and the stack frame pairwise disjoint. The stack sizes cover each function's own use and the hook's 4096 bytes. `poly1305_blocks` saves 64 bytes. `_update` saves 48 and calls it. `poly1305_finish` saves 32 and calls it, then restores its frame and branches to `sodium_memzero`, so the hook runs with the stack pointer `poly1305_finish` was entered with. `_final` saves 16 and calls `poly1305_finish`. The one-shot saves 48, keeps its state in a 64-byte-aligned frame of 144 bytes (at most 240 bytes below its entry stack pointer), and calls both.
-- source:
--   libsodium 1.0.22-RELEASE, commit 77e1ce5d6dee871c49ef211222ba18ef0c486bda (https://github.com/jedisct1/libsodium/tree/77e1ce5d6dee871c49ef211222ba18ef0c486bda), src/libsodium/crypto_onetimeauth/poly1305/donna/poly1305_donna64.h lines 25–32 (poly1305_state_internal_t) and src/libsodium/include/sodium/crypto_onetimeauth_poly1305.h lines 19–62

import Definitions.Def_Poly1305Boringssl_Rfc8439
import Definitions.Def_Poly1305Libsodium_PlacedObj
import Definitions.Def_Libc_ExplicitBzero

/-!
# Contracts of libsodium's Poly1305 (`poly1305_donna.c`, donna64) on AArch64

The layout of libsodium 1.0.22's `poly1305_state_internal_t` (`poly1305_donna64.h`), an invariant on
its limbs, and contracts (`Arm64.Spec`) for functions of the placed library `libsodiumPoly1305Lib`:
the block routine `poly1305_blocks`, the streaming functions
`crypto_onetimeauth_poly1305_donna_init`, `_update` and `_final`, and the one-shot
`crypto_onetimeauth_poly1305_donna`. All of them are `static` in the C source, so they are not
exports of the library. The call to `sodium_memzero` is an external hook, assumed to meet the
`explicit_bzero` contract `Libc.explicitBzeroSpec`.

Registers follow AAPCS64: arguments in `x0`, `x1`, `x2`, `x3`; an `int` result in `w0`.
-/

namespace Poly1305Libsodium

open Arm64 Poly1305Boringssl

/-! ## The state

`poly1305_state_internal_t` is `unsigned long long r[3]` (byte offsets 0, 8, 16),
`unsigned long long h[3]` (24, 32, 40), `unsigned long long pad[2]` (48, 56),
`unsigned long long leftover` (64), `unsigned char buffer[16]` (72-87) and
`unsigned char final` (88): 96 bytes with padding. -/

/-- The 64-bit little-endian word at byte offset `off` of `bs`, as a natural number. -/
def u64At (bs : List (BitVec 8)) (off : Nat) : Nat :=
  leBytesToNum ((bs.drop off).take 8)

/-- Limb `r[i]` (`i ≤ 2`) of the state bytes `st`. -/
def rLimb (st : List (BitVec 8)) (i : Nat) : Nat := u64At st (8 * i)

/-- Limb `h[i]` (`i ≤ 2`) of the state bytes `st`. -/
def hLimb (st : List (BitVec 8)) (i : Nat) : Nat := u64At st (24 + 8 * i)

/-- The number with limbs `f 0, f 1, f 2` of 44, 44 and 42 bits: `f 0 + 2^44 f 1 + 2^88 f 2`. -/
def limbVal (f : Nat → Nat) : Nat :=
  f 0 + 2 ^ 44 * f 1 + 2 ^ 88 * f 2

/-- An invariant of the first 48 bytes (`r` and `h`) of the state: `r[i]` at most the masks
`poly1305_init` applies (`0xffc0fffffff`, `0xfffffc0ffff`, `0x00ffffffc0f`), and the accumulator
limbs bounded (`h[0] < 2^44`, `h[1] < 2^44 + 64`, `h[2] < 2^42`). -/
def StateOk (rh : List (BitVec 8)) : Prop :=
  rh.length = 48 ∧
  rLimb rh 0 ≤ 0xffc0fffffff ∧ rLimb rh 1 ≤ 0xfffffc0ffff ∧ rLimb rh 2 ≤ 0x00ffffffc0f ∧
  hLimb rh 0 < 2 ^ 44 ∧ hLimb rh 1 < 2 ^ 44 + 64 ∧ hLimb rh 2 < 2 ^ 42

/-- The term `poly1305_blocks` adds to each 16-byte block: `2^128` when the state's `final` byte
is `0`, and `0` otherwise. -/
def hibit (fin : BitVec 8) : Nat := if fin = 0#8 then 2 ^ 128 else 0

/-- The block loop on the accumulator value `a`: for each complete 16-byte block `c` of `m`
(`m.length / 16` of them, in order), `a := r * (a + le_bytes_to_num(c) + hb) mod p`. -/
def blocksAcc (r hb a : Nat) (m : List (BitVec 8)) : Nat :=
  (List.range (m.length / 16)).foldl
    (fun a i => r * (a + leBytesToNum ((m.drop (16 * i)).take 16) + hb) % p1305) a

/-- Bytes `bs` at `p`, owned (`p ↦ₛ bs`) when `ro = false` and read-only (`p ↦ᵣ bs`) when
`ro = true`. -/
def bytesIn (ro : Bool) (p : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  if ro then p ↦ᵣ bs else p ↦ₛ bs

/-! ## Judgments -/

/-- The hooks `externs` call, for `sodium_memzero`, a function meeting `Libc.explicitBzeroSpec`. -/
def MemzeroOk (externs : String → Option (State → State)) : Prop :=
  HookSat externs "sodium_memzero" Libc.explicitBzeroSpec

/-- Correctness of a function of `libsodiumPoly1305Lib` that need not be exported: `fnName` is a
symbol of the text block, and for every placement `pl` under which the library is `Placeable` and
all hooks `externs` with `MemzeroOk externs`, `subroutine_ok` holds for the placed program at the
address of `fnName`. -/
def internalOk {S α : Type} [ToBaseSpec S α] (fnName : String) (spec : Obj.Placement → S) : Prop :=
  fnName ∈ libsodiumPoly1305Lib.text.symbols.map Prod.fst ∧
  ∀ pl : Obj.Placement, libsodiumPoly1305Lib.Placeable pl →
    ∀ externs : String → Option (State → State), MemzeroOk externs →
      subroutine_ok (libsodiumPoly1305Lib.program pl externs)
        (libsodiumPoly1305Lib.fnAddr pl fnName) (ToBaseSpec.toSpec (spec pl) pl.base)

/-! ## The block routine -/

/-- Contract of the internal `poly1305_blocks(st, m, bytes)` (`x0 = st`, `x1 = m`, `x2 = bytes`),
ghost `(ro, rh, fin, m)`: entered owning the 48 bytes `rh` (`r` and `h`) at `st` with
`StateOk rh`, the `final` byte `fin` at `st + 88`, the message bytes `m` at `m` (owned or
read-only, by `ro`), `bytes = m.length` at least 16, and a 64-byte stack frame below `sp`, it returns with 48 bytes `rh'` at `st` that satisfy `StateOk`, keep `r` (the first 24 bytes),
and whose accumulator is congruent modulo `2^130 - 5` to `blocksAcc` run on `m` with `r`,
`hibit fin` and the old accumulator; `fin`, `m` and the stack frame are handed back. -/
def blocksSpec : Spec (Bool × List (BitVec 8) × BitVec 8 × List (BitVec 8)) where
  pre g s0 :=
    match g with
    | (ro, rh, fin, m) =>
      ⌜StateOk rh ∧ (s0.readReg64 Reg.x2).toNat = m.length ∧ 16 ≤ m.length⌝ ∗
        (s0.readReg64 Reg.x0 ↦ₛ rh) ∗ ((s0.readReg64 Reg.x0 + 88#64) ↦ₛ [fin]) ∗
        bytesIn ro (s0.readReg64 Reg.x1) m ∗ stackFrame s0 64
  post g s0 sf :=
    match g with
    | (ro, rh, fin, m) =>
      (∃∗ rh' : List (BitVec 8), (s0.readReg64 Reg.x0 ↦ₛ rh') ∗
          ⌜StateOk rh' ∧ rh'.take 24 = rh.take 24 ∧
            limbVal (hLimb rh') % p1305 =
              blocksAcc (limbVal (rLimb rh)) (hibit fin) (limbVal (hLimb rh)) m % p1305⌝) ∗
        ((s0.readReg64 Reg.x0 + 88#64) ↦ₛ [fin]) ∗
        bytesIn ro (s0.readReg64 Reg.x1) m ∗ stackFrame sf 64

/-! ## The final step -/

/-- The tag `poly1305_finish` computes from the 96 state bytes `st`: with `L = leftover`
(offset 64), the accumulator `a = limbVal h`, if `L ≠ 0` first one more step
`a := r * (a + le_bytes_to_num(buffer[0..L] ++ [0x01])) mod p` on the `L` buffered bytes (offset 72),
then `num_to_16_le_bytes((a mod p) + pad)`, where `pad` is the 128-bit little-endian value at
offset 48. -/
def finishTag (st : List (BitVec 8)) : List (BitVec 8) :=
  let L := u64At st 64
  let r := limbVal (rLimb st)
  let a := limbVal (hLimb st)
  let a' := if L = 0 then a else r * (a + leBytesToNum (((st.drop 72).take L) ++ [1#8])) % p1305
  numTo16LeBytes (a' % p1305 + leBytesToNum ((st.drop 48).take 16))

/-- Contract of the internal `poly1305_finish(st, mac)` (`x0 = st`, `x1 = mac`), ghost
`(st, mac)`: entered owning the 96 state bytes `st` at `st`, whose first 48 bytes satisfy `StateOk`
and whose `leftover` (offset 64) is below 16, the 16 bytes `mac` at `mac`, and a 4096-byte stack
frame below `sp`, it returns with the 96 state bytes zero, the 16 bytes `finishTag st` at `mac`,
and the stack frame handed back. -/
def finishSpec : Spec (List (BitVec 8) × List (BitVec 8)) where
  pre g s0 :=
    match g with
    | (st, mac) =>
      ⌜st.length = 96 ∧ StateOk (st.take 48) ∧ u64At st 64 < 16 ∧ mac.length = 16⌝ ∗
        (s0.readReg64 Reg.x0 ↦ₛ st) ∗ (s0.readReg64 Reg.x1 ↦ₛ mac) ∗ stackFrame s0 4096
  post g s0 _ :=
    match g with
    | (st, _) =>
      (s0.readReg64 Reg.x0 ↦ₛ List.replicate 96 0#8) ∗
        (s0.readReg64 Reg.x1 ↦ₛ finishTag st) ∗ stackFrame s0 4096

/-! ## The streaming functions and the one-shot

A representation predicate `Rep a st key m` relates the address `a` of a
`crypto_onetimeauth_poly1305_state` (256 bytes), its bytes `st`, a 32-byte key and the message
bytes absorbed so far. -/

/-- Representation predicates: address, state bytes, key, message so far. -/
abbrev StateRep : Type :=
  BitVec 64 → List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Prop

/-- Contract of `crypto_onetimeauth_poly1305_donna_init(state, key)` (`x0 = state`, `x1 = key`),
ghost `(ro, st, key)`: entered owning the 256 bytes `st` at `state` and with the 32 bytes `key` at
`key` (owned or read-only, by `ro`), it returns `0` in `w0`, with 256 bytes `st'` at `state` such
that `Rep state st' key []`, and `key` handed back. -/
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

/-- Contract of `crypto_onetimeauth_poly1305_donna_update(state, in, inlen)` (`x0 = state`,
`x1 = in`, `x2 = inlen`), ghost `(ro, st, key, m, inp)`: entered owning the 256 bytes `st` at
`state` with `Rep state st key m`, the bytes `inp` at `in` (owned or read-only, by `ro`),
`inlen = inp.length` and a 112-byte stack frame below `sp`, it returns `0` in `w0`, with 256 bytes
`st'` at `state` such that `Rep state st' key (m ++ inp)`, and `inp` and the stack frame handed
back. -/
def updateSpec (Rep : StateRep) :
    Spec (Bool × List (BitVec 8) × List (BitVec 8) × List (BitVec 8) × List (BitVec 8)) where
  pre g s0 :=
    match g with
    | (ro, st, key, m, inp) =>
      ⌜st.length = 256 ∧ Rep (s0.readReg64 Reg.x0) st key m ∧
          (s0.readReg64 Reg.x2).toNat = inp.length⌝ ∗
        (s0.readReg64 Reg.x0 ↦ₛ st) ∗ bytesIn ro (s0.readReg64 Reg.x1) inp ∗ stackFrame s0 112
  post g s0 sf :=
    match g with
    | (ro, _, key, m, inp) =>
      ⌜sf.readReg32 Reg.x0 = 0#32⌝ ∗
        (∃∗ st' : List (BitVec 8),
          ⌜st'.length = 256 ∧ Rep (s0.readReg64 Reg.x0) st' key (m ++ inp)⌝ ∗
            (s0.readReg64 Reg.x0 ↦ₛ st')) ∗
        bytesIn ro (s0.readReg64 Reg.x1) inp ∗ stackFrame s0 112

/-- Contract of `crypto_onetimeauth_poly1305_donna_final(state, out)` (`x0 = state`, `x1 = out`),
ghost `(st, key, m, mac)`: entered owning the 256 bytes `st` at `state` with `Rep state st key m`,
the 16 bytes `mac` at `out` and a 4112-byte stack frame below `sp`, it returns `0` in `w0`, with
the first 96 bytes of the state zero and the other 160 unchanged, the 16 bytes
`poly1305Mac m key` at `out`, and the stack frame handed back. -/
def finalSpec (Rep : StateRep) :
    Spec (List (BitVec 8) × List (BitVec 8) × List (BitVec 8) × List (BitVec 8)) where
  pre g s0 :=
    match g with
    | (st, key, m, mac) =>
      ⌜st.length = 256 ∧ Rep (s0.readReg64 Reg.x0) st key m ∧ mac.length = 16⌝ ∗
        (s0.readReg64 Reg.x0 ↦ₛ st) ∗ (s0.readReg64 Reg.x1 ↦ₛ mac) ∗ stackFrame s0 4112
  post g s0 sf :=
    match g with
    | (st, key, m, _) =>
      ⌜sf.readReg32 Reg.x0 = 0#32⌝ ∗
        (s0.readReg64 Reg.x0 ↦ₛ (List.replicate 96 0#8 ++ st.drop 96)) ∗
        (s0.readReg64 Reg.x1 ↦ₛ poly1305Mac m key) ∗ stackFrame s0 4112

/-- Contract of the one-shot `crypto_onetimeauth_poly1305_donna(out, m, inlen, key)` (`x0 = out`,
`x1 = m`, `x2 = inlen`, `x3 = key`), ghost `(roM, roK, out, m, key)`: entered owning the 16 bytes
`out` at `out`, with the message bytes `m` at `m` (owned or read-only, by `roM`),
`inlen = m.length`, the 32 bytes `key` at `key` (owned or read-only, by `roK`) and a 4336-byte
stack frame below `sp`, it returns `0` in `w0`, with the 16 bytes `poly1305Mac m key` at `out`,
and `m`, `key` and the stack frame handed back. -/
def oneshotSpec :
    Spec (Bool × Bool × List (BitVec 8) × List (BitVec 8) × List (BitVec 8)) where
  pre g s0 :=
    match g with
    | (roM, roK, out, m, key) =>
      ⌜out.length = 16 ∧ (s0.readReg64 Reg.x2).toNat = m.length ∧ key.length = 32⌝ ∗
        (s0.readReg64 Reg.x0 ↦ₛ out) ∗ bytesIn roM (s0.readReg64 Reg.x1) m ∗
        bytesIn roK (s0.readReg64 Reg.x3) key ∗ stackFrame s0 4336
  post g s0 sf :=
    match g with
    | (roM, roK, _, m, key) =>
      ⌜sf.readReg32 Reg.x0 = 0#32⌝ ∗
        (s0.readReg64 Reg.x0 ↦ₛ poly1305Mac m key) ∗ bytesIn roM (s0.readReg64 Reg.x1) m ∗
        bytesIn roK (s0.readReg64 Reg.x3) key ∗ stackFrame s0 4336

/-- `crypto_onetimeauth_poly1305_donna_init` meets `initSpec Rep`. -/
def initOk (Rep : StateRep) : Prop :=
  internalOk "crypto_onetimeauth_poly1305_donna_init [libsodium_poly1305_donna]"
    (fun _ => initSpec Rep)

/-- `crypto_onetimeauth_poly1305_donna_update` meets `updateSpec Rep`. -/
def updateOk (Rep : StateRep) : Prop :=
  internalOk "crypto_onetimeauth_poly1305_donna_update [libsodium_poly1305_donna]"
    (fun _ => updateSpec Rep)

/-- `crypto_onetimeauth_poly1305_donna_final` meets `finalSpec Rep`. -/
def finalOk (Rep : StateRep) : Prop :=
  internalOk "crypto_onetimeauth_poly1305_donna_final [libsodium_poly1305_donna]"
    (fun _ => finalSpec Rep)

/-- `crypto_onetimeauth_poly1305_donna` meets `oneshotSpec`. -/
def oneshotOk : Prop :=
  internalOk "crypto_onetimeauth_poly1305_donna [libsodium_poly1305_donna]" (fun _ => oneshotSpec)

end Poly1305Libsodium


