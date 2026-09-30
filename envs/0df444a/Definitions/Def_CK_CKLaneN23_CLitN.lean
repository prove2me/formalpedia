-- Prove2me | Definitions.Def_CK_CKLaneN23_CLitN
-- name    : CK_CKLaneN23_CLitN
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T10:31:46.144625+00:00
-- url     : https://prove2.me/theorems/b9bbbf5a-cdb5-41e6-98a9-95207c371040
-- title:
--   Courtade–Kumar proof module `CKLaneN23.CLitN` (transplant)
-- statement:
--   Platform version of the Lean module `CKLaneN23.CLitN` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture). The source builds the corner-checker certificate literals of Lane N23b with a custom `n23lit` command, which this platform does not accept. Here each literal is an ordinary definition `decodeTM (natToks [...])`: the same source token list, packed as zigzag-encoded base-2^w digits of a few natural numbers and decoded by plain recursive functions (`CKLaneN23.CLitN`), giving the same `TMd` values. This packed form replaces an earlier string-based encoding whose `String.toList` evaluation exceeded the kernel's recursion limit. Everything else is the original source, with project imports redirected to their transplanted bundles `Definitions.Def_CK_*`.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, platform re-encoding of the certificate literals of module CKLaneN23.TChainData (browse copy: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN23/TChainData.lean)

import Definitions.Def_CK_CKLaneN23_CLit

/-!
# CKLaneN23.CLitN — kernel-friendly certificate literal encoding (platform addition)

The platform version of `CKLaneN23.CLit` decodes each certificate literal from a token string
(`decodeTM (parseInts "…")`), replacing the source's custom `n23lit` command. Evaluating
`String.toList` on the long literals exceeds the kernel's recursion limit, so the literals of
`CKLaneN23.TChainData` are instead written as a short list of natural numbers: each triple `(k, w, n)`
packs `k` tokens as base-`2^w` digits of `n` (least significant first), each token zigzag-encoded
(`z ↦ 2z` for `z ≥ 0`, `z ↦ -2z-1` for `z < 0`). `natToks` recovers exactly the source token list,
which `decodeTM` turns into the same `TMd` value the source command built.
-/

namespace CKLaneN23.CT

/-- inverse of the zigzag encoding -/
def unzigN (z : Nat) : Int := if z % 2 = 0 then Int.ofNat (z / 2) else Int.negSucc (z / 2)

/-- the `k` base-`b` digits of `n`, least significant first, zigzag-decoded -/
def unpackN (b : Nat) : Nat → Nat → List Int
  | 0, _ => []
  | k + 1, n => unzigN (n % b) :: unpackN b k (n / b)

/-- concatenated tokens of all packed chunks `(k, w, n)` (`k` digits of `w` bits each) -/
def natToks : List (Nat × Nat × Nat) → List Int
  | [] => []
  | (k, w, n) :: r => unpackN (2 ^ w) k n ++ natToks r

end CKLaneN23.CT


