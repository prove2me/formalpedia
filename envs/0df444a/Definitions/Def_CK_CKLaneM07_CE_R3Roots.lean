-- Prove2me | Definitions.Def_CK_CKLaneM07_CE_R3Roots
-- name    : CK_CKLaneM07_CE_R3Roots
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T00:49:35.145217+00:00
-- url     : https://prove2.me/theorems/64239868-cd01-4dba-8916-5001eb980fe5
-- title:
--   Courtade–Kumar proof module `CKLaneM07.CE.R3Roots` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM07.CE.R3Roots` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM07.CE.R3Roots` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM07.CE.R3Roots (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM07/CE/R3Roots.lean)

import Definitions.Def_CK_CKLaneN1_R3Leaf

-- ===== source module CKLaneM07.CE.R3Roots =====
section

/-! Lane M07 row-3 octave roots `[2^-k, 2^-(k-1)] × [0,1] × [0, Y<k>]` (Y<k> = r3tree Y_k). -/

namespace CKLaneM07.CE.R3Roots

open CKLaneN1

def Y17 : ℚ := 25735 / 268435456
def root17 : B3 := ⟨1 / 131072, 1 / 65536, 0, 1, 0, Y17⟩

def Y16 : ℚ := 170163 / 1073741824
def root16 : B3 := ⟨1 / 65536, 1 / 32768, 0, 1, 0, Y16⟩

def Y15 : ℚ := 283877 / 1073741824
def root15 : B3 := ⟨1 / 32768, 1 / 16384, 0, 1, 0, Y15⟩

def Y14 : ℚ := 476709 / 1073741824
def root14 : B3 := ⟨1 / 16384, 1 / 8192, 0, 1, 0, Y14⟩

def Y13 : ℚ := 401997 / 536870912
def root13 : B3 := ⟨1 / 8192, 1 / 4096, 0, 1, 0, Y13⟩

def Y12 : ℚ := 1359019 / 1073741824
def root12 : B3 := ⟨1 / 4096, 1 / 2048, 0, 1, 0, Y12⟩

def Y11 : ℚ := 2297681 / 1073741824
def root11 : B3 := ⟨1 / 2048, 1 / 1024, 0, 1, 0, Y11⟩

def Y10 : ℚ := 3877283 / 1073741824
def root10 : B3 := ⟨1 / 1024, 1 / 512, 0, 1, 0, Y10⟩

def Y9 : ℚ := 1628721 / 268435456
def root9 : B3 := ⟨1 / 512, 1 / 256, 0, 1, 0, Y9⟩

def Y8 : ℚ := 339643 / 33554432
def root8 : B3 := ⟨1 / 256, 1 / 128, 0, 1, 0, Y8⟩

def Y7 : ℚ := 8966729 / 536870912
def root7 : B3 := ⟨1 / 128, 1 / 64, 0, 1, 0, Y7⟩

end CKLaneM07.CE.R3Roots

end


