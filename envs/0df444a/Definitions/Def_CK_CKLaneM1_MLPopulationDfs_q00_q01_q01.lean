-- Prove2me | Definitions.Def_CK_CKLaneM1_MLPopulationDfs_q00_q01_q01
-- name    : CK_CKLaneM1_MLPopulationDfs_q00_q01_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T13:29:09.634969+00:00
-- url     : https://prove2.me/theorems/a8d585db-2018-4d44-b665-6c660c8fe2ef
-- title:
--   Courtade–Kumar proof module `CKLaneM1.MLPopulationDfs (piece 1 of 4) (piece 2 of 3) (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM1.MLPopulationDfs (piece 1 of 4) (piece 2 of 3) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM1.MLPopulationDfs (piece 1 of 4) (piece 2 of 3) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM1.MLPopulationDfs (piece 1 of 4) (piece 2 of 3) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM1/MLPopulationDfs (piece 1 of 4) (piece 2 of 3) (piece 2 of 4).lean)

import Definitions.Def_CK_CKLaneM1_MLPopulationDfs_q00_q01_q00

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneM1.ML.Population
open CKLaneM1.ML
theorem ix0752_lt : ∀ i ∈ ix0752, i < Pop.S0364.leaves.length := by decide +kernel
def r0752 : List (List ℕ) := ix0752.map fun i => (Pop.S0364.leaves.getD i dflt).1
theorem r0752_ok : ∀ p ∈ r0752, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0364.sem ix0752_lt

def ix0753 : List ℕ := [35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]
theorem ix0753_lt : ∀ i ∈ ix0753, i < Pop.S0368.leaves.length := by decide +kernel
def r0753 : List (List ℕ) := ix0753.map fun i => (Pop.S0368.leaves.getD i dflt).1
theorem r0753_ok : ∀ p ∈ r0753, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0368.sem ix0753_lt

def ix0754 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]
theorem ix0754_lt : ∀ i ∈ ix0754, i < Pop.S0369.leaves.length := by decide +kernel
def r0754 : List (List ℕ) := ix0754.map fun i => (Pop.S0369.leaves.getD i dflt).1
theorem r0754_ok : ∀ p ∈ r0754, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0369.sem ix0754_lt

def ix0755 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]
theorem ix0755_lt : ∀ i ∈ ix0755, i < Pop.S0370.leaves.length := by decide +kernel
def r0755 : List (List ℕ) := ix0755.map fun i => (Pop.S0370.leaves.getD i dflt).1
theorem r0755_ok : ∀ p ∈ r0755, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0370.sem ix0755_lt

def ix0756 : List ℕ := [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97]
theorem ix0756_lt : ∀ i ∈ ix0756, i < Pop.S0374.leaves.length := by decide +kernel
end CKLaneM1.ML.Population


