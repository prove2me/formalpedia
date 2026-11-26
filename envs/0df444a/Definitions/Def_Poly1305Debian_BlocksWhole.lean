-- Prove2me | Definitions.Def_Poly1305Debian_BlocksWhole
-- name    : Poly1305Debian_BlocksWhole
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-25T21:17:48.75731+00:00
-- url     : https://prove2.me/theorems/3234225a-ebd9-5c43-b887-6be2a3138915
-- title:
--   The block routine of Debian's libsodium Poly1305 on whole blocks — blocksSpec with the length a multiple of 16
-- statement:
--   `blocksWholeSpec` is the contract `blocksSpec` of the bundle `Poly1305Debian_Spec` for `poly1305_blocks(st, m, bytes)`, with one more condition in the precondition: the message length $|m|$, which equals `bytes`, is a multiple of 16. With `blocksSpec`'s own condition $|m| \ge 16$, the length is a positive multiple of 16. The postcondition, the ghost value and the use of no stack are those of `blocksSpec`.
--
--   **Why.** `blocksSpec` allowed any length of at least 16, and the statement [`Poly1305Debian.internalOk_poly1305_blocks`](https://prove2.me/theorems/21f859ee-ba32-47a7-b548-1c650daee6d3) made with it is Disproved (submission 88a8159d). The source's loop, `poly1305_donna64.h` line 84, “while (bytes >= poly1305_block_size) {”, stops when fewer than 16 bytes remain. Debian's compiled code instead runs until the message pointer equals $m + $ `bytes`, so for a length that is not a multiple of 16 it reads past the message. Every call in the library passes a positive multiple of 16: `poly1305_donna.c`, line 36, “poly1305_blocks(st, st->buffer, poly1305_block_size);”, and lines 42 and 44, “unsigned long long want = (bytes & ~(poly1305_block_size - 1));” and “poly1305_blocks(st, m, want);” under “if (bytes >= poly1305_block_size) {” (line 41); and `poly1305_donna64.h`, line 153, the call on the padded last block.
-- source:
--   libsodium 1.0.22-RELEASE, commit 77e1ce5d6dee871c49ef211222ba18ef0c486bda (https://github.com/jedisct1/libsodium/tree/77e1ce5d6dee871c49ef211222ba18ef0c486bda), src/libsodium/crypto_onetimeauth/poly1305/donna/poly1305_donna64.h lines 61–133 (poly1305_blocks) and its callers, poly1305_donna.c lines 36 and 41–44 and poly1305_donna64.h line 153

import Definitions.Def_Poly1305Debian_Spec

/-!
# The block routine of Debian's libsodium Poly1305, on whole blocks

`blocksSpec` (bundle `Poly1305Debian_Spec`) asks only `bytes ≥ 16` of the message length. Debian's
compiled `poly1305_blocks` also needs `bytes` to be a multiple of 16, which every caller in the
library passes. `blocksWholeSpec` is `blocksSpec` with that condition added to the precondition.
-/

namespace Poly1305Debian

open Arm64

/-- `blocksSpec` with the message length also a multiple of 16: the precondition adds
`m.length % 16 = 0` for the ghost message `m`; the postcondition is unchanged. -/
def blocksWholeSpec : Spec (Bool × List (BitVec 8) × BitVec 8 × List (BitVec 8)) :=
  { blocksSpec with
    pre := fun g s0 =>
      match g with
      | (_, _, _, m) => ⌜m.length % 16 = 0⌝ ∗ blocksSpec.pre g s0 }

end Poly1305Debian


