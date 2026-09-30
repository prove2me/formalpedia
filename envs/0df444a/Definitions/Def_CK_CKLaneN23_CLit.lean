-- Prove2me | Definitions.Def_CK_CKLaneN23_CLit
-- name    : CK_CKLaneN23_CLit
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T06:48:29.71099+00:00
-- url     : https://prove2.me/theorems/579cf9c0-246d-4521-bee6-57e2bd3268e6
-- title:
--   Courtade–Kumar proof module `CKLaneN23.CLit` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN23.CLit` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN23.CLit` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN23.CLit (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN23/CLit.lean)

import Definitions.Def_CK_CKLaneN23_CQ

/-!
# CKLaneN23.CLit — certificate literals (Lane N23b), platform version

The source defines a custom command `n23lit NAME "tokens"` that builds each literal term
directly. Custom commands are not accepted on this platform, so this version provides an
ordinary decoding function instead: `decodeTM tokens` rebuilds the same `TMd` value from the same
token format, and each literal is written `noncomputable def NAME : TMd := decodeTM (parseInts "tokens")`.
The kernel evaluates `decodeTM` to exactly the structure the custom command produced (same constructors,
same `qq num den` rationals).

Token format (integers):
  TM    := nS SLOT^nS  rnum rden  n
  SLOT  := nM (i k nL (e num den)^nL)^nM          -- one `QPoly` (x-coefficient)
-/

namespace CKLaneN23.CT

/-- `(e num den)^k` -/
def decTerms : Nat → List Int → List (ℤ × ℚ) × List Int
  | 0, ts => ([], ts)
  | k + 1, e :: num :: den :: ts =>
    let r := decTerms k ts
    ((e, qq num den.toNat) :: r.1, r.2)
  | _ + 1, _ => ([], [])

/-- `(i k nL (e num den)^nL)^k` -/
def decMons : Nat → List Int → List ((ℕ × ℕ) × List (ℤ × ℚ)) × List Int
  | 0, ts => ([], ts)
  | k + 1, i :: j :: nL :: ts =>
    let t := decTerms nL.toNat ts
    let r := decMons k t.2
    (((i.toNat, j.toNat), t.1) :: r.1, r.2)
  | _ + 1, _ => ([], [])

/-- `(nM MON^nM)^k` -/
def decSlots : Nat → List Int → List (List ((ℕ × ℕ) × List (ℤ × ℚ))) × List Int
  | 0, ts => ([], ts)
  | k + 1, nM :: ts =>
    let m := decMons nM.toNat ts
    let r := decSlots k m.2
    (m.1 :: r.1, r.2)
  | _ + 1, [] => ([], [])

/-- Tokenizer state: accumulated tokens (reversed), current value, sign, inside-token flag. -/
def parseIntsAux : List Char → List Int → Nat → Bool → Bool → List Int
  | [], acc, cur, neg, inTok => (if inTok then (if neg then -(cur : Int) else (cur : Int)) :: acc else acc).reverse
  | c :: cs, acc, cur, neg, inTok =>
    if c = ' ' ∨ c = '\n' ∨ c = '\t' ∨ c = '\r' then
      parseIntsAux cs (if inTok then (if neg then -(cur : Int) else (cur : Int)) :: acc else acc) 0 false false
    else if c = '-' then parseIntsAux cs acc cur true true
    else parseIntsAux cs acc (cur * 10 + (c.toNat - '0'.toNat)) neg true

/-- whitespace-separated integers (optional leading `-`), as in the source's `n23lit` tokenizer -/
def parseInts (s : String) : List Int := parseIntsAux s.toList [] 0 false false

/-- Decode a certificate literal `nS SLOT^nS rnum rden n`. -/
def decodeTM : List Int → TMd
  | nS :: ts =>
    let s := decSlots nS.toNat ts
    match s.2 with
    | rn :: rd :: n :: _ => ⟨s.1, qq rn rd.toNat, n.toNat⟩
    | _ => ⟨s.1, 0, 0⟩
  | [] => ⟨[], 0, 0⟩

end CKLaneN23.CT


