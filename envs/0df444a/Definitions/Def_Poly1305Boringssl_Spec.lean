-- Prove2me | Definitions.Def_Poly1305Boringssl_Spec
-- name    : Poly1305Boringssl_Spec
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-24T10:01:26.787545+00:00
-- url     : https://prove2.me/theorems/6fa5e13a-c02a-47eb-b367-ca0bdf56c260
-- title:
--   Contracts of BoringSSL's Poly1305 on AArch64
-- statement:
--   The layout of BoringSSL's Poly1305 state with an invariant, and contracts for the three exported functions of `boringsslPoly1305Lib` and its internal block routine. A statement `boringsslPoly1305Lib.subroutineOk "f" spec` (from the `Arm64` bundles) is total correctness of `f` under `spec` for every valid placement of the library. For every ghost value, every frame $R$ and every entry state at `f` with a 16-byte-aligned stack pointer whose memory satisfies the precondition separately from $R$, execution terminates. It returns to the link register with the stack pointer and the AAPCS64 callee-saved registers restored, and the memory satisfies the postcondition, again with $R$ separate. Panics, process exits and running out of memory are excluded. Arguments are in `x0`, `x1`, `x2` (AAPCS64).
--
--   **BoringSSL's state.** `poly1305_state` is a 512-byte buffer (poly1305.h, line 28: “typedef uint8_t poly1305_state[512];”). The functions work on a `struct poly1305_state_st` at the first 64-byte-aligned address in it (`poly1305_aligned_state`, poly1305.cc lines 49–51). poly1305.cc, lines 36–43, declares it:
--
--       struct poly1305_state_st {
--         uint32_t r0, r1, r2, r3, r4;
--         uint32_t s1, s2, s3, s4;
--         uint32_t h0, h1, h2, h3, h4;
--         uint8_t buf[16];
--         size_t buf_used;
--         uint8_t key[16];
--       };
--
--   Its first 56 bytes are thus fourteen little-endian 32-bit fields: `r0`–`r4` at offsets 0–16, `s1`–`s4` at 20–32, `h0`–`h4` at 36–52. `u32At bs off` is the little-endian 32-bit word at byte `off`; `rLimb st i`, `sLimb st i`, `hLimb st i` are those fields of the bytes `st`; `limbVal f` is $f_0 + 2^{26} f_1 + 2^{52} f_2 + 2^{78} f_3 + 2^{104} f_4$.
--
--   `StateOk st` says that `st` has 56 bytes and
--   - $r_0 \le$ `0x3ffffff`, $r_1 \le$ `0x3ffff03`, $r_2 \le$ `0x3ffc0ff`, $r_3 \le$ `0x3f03fff`, $r_4 \le$ `0x00fffff` (the masks of poly1305.cc, lines 169–180);
--   - $s_i = 5 r_i$ for $i = 1, \dots, 4$;
--   - $h_0 < 2^{31} + 2^{29} + 2^{27}$ and $h_1, \dots, h_4 < 2^{26}$.
--
--   It is an invariant of our choosing, not BoringSSL's: the code relies on bounds of this kind for its 32- and 64-bit arithmetic to be exact, and the bound on $h_0$ is the one the block routine preserves.
--
--   **The internal block routine** `poly1305_update(state, in, len)` (poly1305.cc, lines 56–148), documented on lines 53–55: “poly1305_blocks updates \`state\` given some amount of input data. This function may only be called with a \`len\` that is not a multiple of 16 at the end of the data. Otherwise the input must be buffered into 16 byte blocks.” `blocksSpec` has ghost value $(st, m)$. Before: `x0` points to the 56 owned bytes $st$ with `StateOk` $st$, the bytes $m$ are readable at `x1`, `x2` $= |m|$, and the caller lends the 16 bytes below the stack pointer. After: `x0` points to 56 bytes $st'$ with `StateOk` $st'$, the same first 36 bytes ($r$ and $s$), and `limbVal (hLimb st')` $\equiv$ `accumulate (limbVal (rLimb st)) (limbVal (hLimb st)) m` $\pmod p$; $m$ and the stack frame are handed back. `internalOk f spec` is `subroutineOk` for a function that is a symbol of the code block but need not be exported (the internal routine is not).
--
--   **The exported functions.** poly1305.h documents them (lines 30–33, 37–38 and 42–43): “CRYPTO_poly1305_init sets up \`state\` so that it can be used to calculate an authentication tag with the one-time key \`key\`. Note that \`key\` is a one-time key and therefore there is no \`reset' method because that would enable several messages to be authenticated with the same key.” “CRYPTO_poly1305_update processes \`in_len\` bytes from \`in\`. It can be called zero or more times after poly1305_init.” “CRYPTO_poly1305_finish completes the poly1305 calculation and writes a 16 byte authentication tag to \`mac\`.” A representation predicate $\mathrm{Rep}$ (of type `StateRep`) relates an address $a$, the 512 bytes at $a$, a key and the bytes absorbed so far.
--   - `initSpec Rep`, for `CRYPTO_poly1305_init(state, key)`, ghost $(st, key)$. Before: `state` owns 512 bytes $st$, and the 32 bytes $key$ are readable at `key`. After: `state` holds 512 bytes $st'$ with $\mathrm{Rep}(\mathtt{state}, st', key, [\,])$; $key$ is handed back. No stack is used.
--   - `updateSpec Rep`, for `CRYPTO_poly1305_update(state, in, in_len)`, ghost $(st, key, m, inp)$. Before: `state` owns 512 bytes $st$ with $\mathrm{Rep}(\mathtt{state}, st, key, m)$, the bytes $inp$ are readable at `in`, `in_len` $= |inp|$, and the caller lends the 64 bytes below the stack pointer. After: `state` holds 512 bytes $st'$ with $\mathrm{Rep}(\mathtt{state}, st', key, m \mathbin{+\!\!+} inp)$; $inp$ and the stack frame are handed back.
--   - `finishSpec Rep`, for `CRYPTO_poly1305_finish(state, mac)`, ghost $(st, key, m, mac)$. Before: `state` owns 512 bytes $st$ with $\mathrm{Rep}(\mathtt{state}, st, key, m)$, `mac` owns 16 bytes, and the caller lends the 48 bytes below the stack pointer. After: `state` holds some 512 bytes, `mac` holds `poly1305Mac m key` (RFC 8439's `poly1305_mac`, bundle `Poly1305Boringssl_Rfc8439`), and the stack frame is handed back.
--   - `initOk Rep`, `updateOk Rep`, `finishOk Rep` are `boringsslPoly1305Lib.subroutineOk` of the three functions with these contracts.
--
--   The separating conjunctions make the state buffer, the key, the input, the output and the stack frame pairwise disjoint. The stack sizes are each function's own use: `CRYPTO_poly1305_update` saves 48 bytes and calls the block routine, which uses 16; `CRYPTO_poly1305_finish` saves 32 and calls it too.
-- source:
--   BoringSSL commit f8b3e2347647a6ad8d26e2ce4cee34f792d5f880 (https://boringssl.googlesource.com/boringssl/+/f8b3e2347647a6ad8d26e2ce4cee34f792d5f880), include/openssl/poly1305.h lines 28–45 and crypto/poly1305/poly1305.cc lines 36–56

import Definitions.Def_Poly1305Boringssl_Rfc8439
import Definitions.Def_Poly1305Boringssl_PlacedObj
import Definitions.Def_Arm64_Spec_Placed

/-!
# Contracts of BoringSSL's Poly1305 (`crypto/poly1305/poly1305.cc`) on AArch64

The layout of the first 56 bytes of BoringSSL's
`struct poly1305_state_st` with an invariant on it, and contracts (`Arm64.Spec`) for the three
exported functions `CRYPTO_poly1305_init`, `CRYPTO_poly1305_update`, `CRYPTO_poly1305_finish`
and for the internal block routine `poly1305_update` of the placed library `boringsslPoly1305Lib`.

Registers follow AAPCS64: arguments in `x0`, `x1`, `x2`.
-/

namespace Poly1305Boringssl

open Arm64

/-! ## The state

The first 56 bytes of BoringSSL's `struct poly1305_state_st` are fourteen `uint32_t` fields:
`r0, r1, r2, r3, r4` (offsets 0-16), `s1, s2, s3, s4` (offsets 20-32), `h0, h1, h2, h3, h4`
(offsets 36-52). -/

/-- The 32-bit little-endian word at byte offset `off` of `bs`, as a natural number. -/
def u32At (bs : List (BitVec 8)) (off : Nat) : Nat :=
  leBytesToNum ((bs.drop off).take 4)

/-- Limb `r_i` (`i ≤ 4`) of the state bytes `st`. -/
def rLimb (st : List (BitVec 8)) (i : Nat) : Nat := u32At st (4 * i)

/-- Limb `s_i` (`1 ≤ i ≤ 4`) of the state bytes `st`. -/
def sLimb (st : List (BitVec 8)) (i : Nat) : Nat := u32At st (16 + 4 * i)

/-- Limb `h_i` (`i ≤ 4`) of the state bytes `st`. -/
def hLimb (st : List (BitVec 8)) (i : Nat) : Nat := u32At st (36 + 4 * i)

/-- The number with radix-`2^26` limbs `f 0, …, f 4`. -/
def limbVal (f : Nat → Nat) : Nat :=
  f 0 + 2 ^ 26 * f 1 + 2 ^ 52 * f 2 + 2 ^ 78 * f 3 + 2 ^ 104 * f 4

/-- An invariant of the first 56 bytes of the state: `r_i` at most the masks
`CRYPTO_poly1305_init` applies, `s_i = 5 r_i`, and the accumulator limbs bounded
(`h0 < 2^31 + 2^29 + 2^27`, `h1, …, h4 < 2^26`). -/
def StateOk (st : List (BitVec 8)) : Prop :=
  st.length = 56 ∧
  rLimb st 0 ≤ 0x3ffffff ∧ rLimb st 1 ≤ 0x3ffff03 ∧ rLimb st 2 ≤ 0x3ffc0ff ∧
  rLimb st 3 ≤ 0x3f03fff ∧ rLimb st 4 ≤ 0x00fffff ∧
  (∀ i, 1 ≤ i → i ≤ 4 → sLimb st i = 5 * rLimb st i) ∧
  hLimb st 0 < 2 ^ 31 + 2 ^ 29 + 2 ^ 27 ∧ (∀ i, 1 ≤ i → i ≤ 4 → hLimb st i < 2 ^ 26)

/-! ## The internal block routine -/

/-- Contract of the internal `poly1305_update(state, in, len)`: entered with `x0 = state` owning
the 56 state bytes `st` with `StateOk st`, `x1 = in` pointing at the readable message bytes `m`,
`x2 = len = m.length`, and a 16-byte stack frame below `sp`, it returns with new state bytes `st'`
that satisfy `StateOk`, keep `r` and `s` (the first 36 bytes), and whose accumulator is congruent
modulo `2^130 - 5` to `accumulate` run on `m` with `r` and the old accumulator. -/
def blocksSpec : Spec (List (BitVec 8) × List (BitVec 8)) where
  pre x s0 :=
    match x with
    | (st, m) =>
      ⌜StateOk st ∧ (s0.readReg64 Reg.x2).toNat = m.length⌝ ∗
        (s0.readReg64 Reg.x0 ↦ₛ st) ∗ (s0.readReg64 Reg.x1 ↦ᵣ m) ∗ stackFrame s0 16
  post x s0 sf :=
    match x with
    | (st, m) =>
      (∃∗ st' : List (BitVec 8), (s0.readReg64 Reg.x0 ↦ₛ st') ∗
          ⌜StateOk st' ∧ st'.take 36 = st.take 36 ∧
            limbVal (hLimb st') % p1305 =
              accumulate (limbVal (rLimb st)) (limbVal (hLimb st)) m % p1305⌝) ∗
        (s0.readReg64 Reg.x1 ↦ᵣ m) ∗ stackFrame sf 16

/-- `Obj.PlacedLib.subroutineOk` for a function of `boringsslPoly1305Lib` that need not be
exported: `fnName` is a symbol of the text block, and for every placement `pl` under which the
library is `Placeable`, `subroutine_ok` holds for the placed program at the address of `fnName`. -/
def internalOk {S α : Type} [ToBaseSpec S α] (fnName : String) (spec : Obj.Placement → S) : Prop :=
  fnName ∈ boringsslPoly1305Lib.text.symbols.map Prod.fst ∧
  ∀ pl : Obj.Placement, boringsslPoly1305Lib.Placeable pl →
    subroutine_ok (boringsslPoly1305Lib.program pl) (boringsslPoly1305Lib.fnAddr pl fnName)
      (ToBaseSpec.toSpec (spec pl) pl.base)

/-! ## The exported functions

A representation predicate `Rep a st key m` relates the address `a` of a `poly1305_state`
buffer, its 512 bytes `st`, a 32-byte key and the message bytes absorbed so far. -/

/-- Representation predicates: address, state bytes, key, message so far. -/
abbrev StateRep : Type :=
  BitVec 64 → List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Prop

/-- Contract of `CRYPTO_poly1305_init(state, key)` (`x0 = state`, `x1 = key`), ghost `(st, key)`:
entered owning the 512 bytes `st` at `state` and with the 32 bytes `key` readable at `key`, it
returns with 512 bytes `st'` at `state` such that `Rep state st' key []`, and `key` unchanged. -/
def initSpec (Rep : StateRep) : Spec (List (BitVec 8) × List (BitVec 8)) where
  pre g s0 :=
    match g with
    | (st, key) =>
      ⌜st.length = 512 ∧ key.length = 32⌝ ∗
        (s0.readReg64 Reg.x0 ↦ₛ st) ∗ (s0.readReg64 Reg.x1 ↦ᵣ key)
  post g s0 _ :=
    match g with
    | (_, key) =>
      (∃∗ st' : List (BitVec 8),
          ⌜st'.length = 512 ∧ Rep (s0.readReg64 Reg.x0) st' key []⌝ ∗
            (s0.readReg64 Reg.x0 ↦ₛ st')) ∗
        (s0.readReg64 Reg.x1 ↦ᵣ key)

/-- Contract of `CRYPTO_poly1305_update(state, in, in_len)` (`x0 = state`, `x1 = in`,
`x2 = in_len`), ghost `(st, key, m, inp)`: entered owning the 512 bytes `st` at `state` with
`Rep state st key m`, the bytes `inp` readable at `in`, `in_len = inp.length` and a 64-byte stack
frame below `sp`, it returns with 512 bytes `st'` at `state` such that
`Rep state st' key (m ++ inp)`, `inp` unchanged and the stack frame handed back. -/
def updateSpec (Rep : StateRep) :
    Spec (List (BitVec 8) × List (BitVec 8) × List (BitVec 8) × List (BitVec 8)) where
  pre g s0 :=
    match g with
    | (st, key, m, inp) =>
      ⌜st.length = 512 ∧ Rep (s0.readReg64 Reg.x0) st key m ∧
          (s0.readReg64 Reg.x2).toNat = inp.length⌝ ∗
        (s0.readReg64 Reg.x0 ↦ₛ st) ∗ (s0.readReg64 Reg.x1 ↦ᵣ inp) ∗ stackFrame s0 64
  post g s0 _ :=
    match g with
    | (_, key, m, inp) =>
      (∃∗ st' : List (BitVec 8),
          ⌜st'.length = 512 ∧ Rep (s0.readReg64 Reg.x0) st' key (m ++ inp)⌝ ∗
            (s0.readReg64 Reg.x0 ↦ₛ st')) ∗
        (s0.readReg64 Reg.x1 ↦ᵣ inp) ∗ stackFrame s0 64

/-- Contract of `CRYPTO_poly1305_finish(state, mac)` (`x0 = state`, `x1 = mac`), ghost
`(st, key, m, mac)`: entered owning the 512 bytes `st` at `state` with `Rep state st key m`, the
16 bytes `mac` at `mac` and a 48-byte stack frame below `sp`, it returns with some 512 bytes at
`state`, the 16 bytes `poly1305Mac m key` at `mac` and the stack frame handed back. -/
def finishSpec (Rep : StateRep) :
    Spec (List (BitVec 8) × List (BitVec 8) × List (BitVec 8) × List (BitVec 8)) where
  pre g s0 :=
    match g with
    | (st, key, m, mac) =>
      ⌜st.length = 512 ∧ Rep (s0.readReg64 Reg.x0) st key m ∧ mac.length = 16⌝ ∗
        (s0.readReg64 Reg.x0 ↦ₛ st) ∗ (s0.readReg64 Reg.x1 ↦ₛ mac) ∗ stackFrame s0 48
  post g s0 _ :=
    match g with
    | (_, key, m, _) =>
      (∃∗ st' : List (BitVec 8), ⌜st'.length = 512⌝ ∗ (s0.readReg64 Reg.x0 ↦ₛ st')) ∗
        (s0.readReg64 Reg.x1 ↦ₛ poly1305Mac m key) ∗ stackFrame s0 48

/-- `CRYPTO_poly1305_init` meets `initSpec Rep` under every placement. -/
def initOk (Rep : StateRep) : Prop :=
  boringsslPoly1305Lib.subroutineOk "CRYPTO_poly1305_init" (fun _ => initSpec Rep)

/-- `CRYPTO_poly1305_update` meets `updateSpec Rep` under every placement. -/
def updateOk (Rep : StateRep) : Prop :=
  boringsslPoly1305Lib.subroutineOk "CRYPTO_poly1305_update" (fun _ => updateSpec Rep)

/-- `CRYPTO_poly1305_finish` meets `finishSpec Rep` under every placement. -/
def finishOk (Rep : StateRep) : Prop :=
  boringsslPoly1305Lib.subroutineOk "CRYPTO_poly1305_finish" (fun _ => finishSpec Rep)

end Poly1305Boringssl


