-- Prove2me | Definitions.Def_CK_CKLaneM1_MLPopulationDfs_q01_q100
-- name    : CK_CKLaneM1_MLPopulationDfs_q01_q100
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T16:33:47.489204+00:00
-- url     : https://prove2.me/theorems/b63d0615-5a3a-41f9-b434-8dbe0a4c369f
-- title:
--   Courtade–Kumar proof module `CKLaneM1.MLPopulationDfs (piece 2 of 4) (piece 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM1.MLPopulationDfs (piece 2 of 4) (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM1.MLPopulationDfs (piece 2 of 4) (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM1.MLPopulationDfs (piece 2 of 4) (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM1/MLPopulationDfs (piece 2 of 4) (piece 1 of 4).lean)

import Definitions.Def_CK_CKLaneM1_MLPopulationDfs_q01_q01


set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneM1.ML.Population
open CKLaneM1.ML
def ix0800 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]
theorem ix0800_lt : ∀ i ∈ ix0800, i < Pop.S0197.leaves.length := by decide +kernel
def r0800 : List (List ℕ) := ix0800.map fun i => (Pop.S0197.leaves.getD i dflt).1
theorem r0800_ok : ∀ p ∈ r0800, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0197.sem ix0800_lt

def ix0801 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104]
theorem ix0801_lt : ∀ i ∈ ix0801, i < Pop.S0198.leaves.length := by decide +kernel
def r0801 : List (List ℕ) := ix0801.map fun i => (Pop.S0198.leaves.getD i dflt).1
theorem r0801_ok : ∀ p ∈ r0801, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0198.sem ix0801_lt

def ix0802 : List ℕ := [145, 146, 147, 148, 149]
theorem ix0802_lt : ∀ i ∈ ix0802, i < Pop.S0201.leaves.length := by decide +kernel
def r0802 : List (List ℕ) := ix0802.map fun i => (Pop.S0201.leaves.getD i dflt).1
theorem r0802_ok : ∀ p ∈ r0802, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0201.sem ix0802_lt

def ix0803 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135]
theorem ix0803_lt : ∀ i ∈ ix0803, i < Pop.S0202.leaves.length := by decide +kernel
def r0803 : List (List ℕ) := ix0803.map fun i => (Pop.S0202.leaves.getD i dflt).1
theorem r0803_ok : ∀ p ∈ r0803, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0202.sem ix0803_lt

def ix0804 : List ℕ := [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]
end CKLaneM1.ML.Population


