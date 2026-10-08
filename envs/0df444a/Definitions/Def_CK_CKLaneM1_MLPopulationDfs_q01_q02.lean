-- Prove2me | Definitions.Def_CK_CKLaneM1_MLPopulationDfs_q01_q02
-- name    : CK_CKLaneM1_MLPopulationDfs_q01_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T16:47:36.609191+00:00
-- url     : https://prove2.me/theorems/28cf8837-82d4-49b2-bdc2-601ea0355bc8
-- title:
--   Courtade–Kumar proof module `CKLaneM1.MLPopulationDfs (piece 2 of 4) (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM1.MLPopulationDfs (piece 2 of 4) (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM1.MLPopulationDfs (piece 2 of 4) (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM1.MLPopulationDfs (piece 2 of 4) (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM1/MLPopulationDfs (piece 2 of 4) (piece 3 of 4).lean)

import Definitions.Def_CK_CKLaneM1_MLPopulationDfs_q01_q101

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneM1.ML.Population
open CKLaneM1.ML
def r0808 : List (List ℕ) := ix0808.map fun i => (Pop.S0190.leaves.getD i dflt).1
theorem r0808_ok : ∀ p ∈ r0808, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0190.sem ix0808_lt

def ix0809 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]
theorem ix0809_lt : ∀ i ∈ ix0809, i < Pop.S0191.leaves.length := by decide +kernel
def r0809 : List (List ℕ) := ix0809.map fun i => (Pop.S0191.leaves.getD i dflt).1
theorem r0809_ok : ∀ p ∈ r0809, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0191.sem ix0809_lt

def ix0810 : List ℕ := [46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
theorem ix0810_lt : ∀ i ∈ ix0810, i < Pop.S0195.leaves.length := by decide +kernel
def r0810 : List (List ℕ) := ix0810.map fun i => (Pop.S0195.leaves.getD i dflt).1
theorem r0810_ok : ∀ p ∈ r0810, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0195.sem ix0810_lt

def ix0811 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]
theorem ix0811_lt : ∀ i ∈ ix0811, i < Pop.S0196.leaves.length := by decide +kernel
def r0811 : List (List ℕ) := ix0811.map fun i => (Pop.S0196.leaves.getD i dflt).1
theorem r0811_ok : ∀ p ∈ r0811, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0196.sem ix0811_lt

def ix0812 : List ℕ := [40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94]
theorem ix0812_lt : ∀ i ∈ ix0812, i < Pop.S0197.leaves.length := by decide +kernel
def r0812 : List (List ℕ) := ix0812.map fun i => (Pop.S0197.leaves.getD i dflt).1
end CKLaneM1.ML.Population


