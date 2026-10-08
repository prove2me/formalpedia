-- Prove2me | Definitions.Def_CK_CKLaneM1_MLPopulationDfs_q00
-- name    : CK_CKLaneM1_MLPopulationDfs_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T15:27:24.02096+00:00
-- url     : https://prove2.me/theorems/6158a336-483e-42c4-9f21-34879bccc621
-- title:
--   Courtade–Kumar proof module `CKLaneM1.MLPopulationDfs (piece 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM1.MLPopulationDfs (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM1.MLPopulationDfs (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM1.MLPopulationDfs (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM1/MLPopulationDfs (piece 1 of 4).lean)

import Definitions.Def_CK_CKLaneM1_MLPopulationDfs_q00_q01

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneM1.ML.Population
open CKLaneM1.ML
def ix0761 : List ℕ := [30, 31, 32, 33, 34, 35, 36, 37]
theorem ix0761_lt : ∀ i ∈ ix0761, i < Pop.S0364.leaves.length := by decide +kernel
def r0761 : List (List ℕ) := ix0761.map fun i => (Pop.S0364.leaves.getD i dflt).1
theorem r0761_ok : ∀ p ∈ r0761, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0364.sem ix0761_lt

def ix0762 : List ℕ := [53, 54, 55, 56, 57, 58, 59, 60]
theorem ix0762_lt : ∀ i ∈ ix0762, i < Pop.S0371.leaves.length := by decide +kernel
def r0762 : List (List ℕ) := ix0762.map fun i => (Pop.S0371.leaves.getD i dflt).1
theorem r0762_ok : ∀ p ∈ r0762, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0371.sem ix0762_lt

def ix0763 : List ℕ := [25, 26, 27, 28, 29, 30, 31, 32, 33]
theorem ix0763_lt : ∀ i ∈ ix0763, i < Pop.S0372.leaves.length := by decide +kernel
def r0763 : List (List ℕ) := ix0763.map fun i => (Pop.S0372.leaves.getD i dflt).1
theorem r0763_ok : ∀ p ∈ r0763, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0372.sem ix0763_lt

def ix0764 : List ℕ := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]
theorem ix0764_lt : ∀ i ∈ ix0764, i < Pop.S0373.leaves.length := by decide +kernel
def r0764 : List (List ℕ) := ix0764.map fun i => (Pop.S0373.leaves.getD i dflt).1
theorem r0764_ok : ∀ p ∈ r0764, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0373.sem ix0764_lt

def ix0765 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41]
theorem ix0765_lt : ∀ i ∈ ix0765, i < Pop.S0374.leaves.length := by decide +kernel
def r0765 : List (List ℕ) := ix0765.map fun i => (Pop.S0374.leaves.getD i dflt).1
theorem r0765_ok : ∀ p ∈ r0765, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0374.sem ix0765_lt

def ix0766 : List ℕ := [91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]
theorem ix0766_lt : ∀ i ∈ ix0766, i < Pop.S0387.leaves.length := by decide +kernel
def r0766 : List (List ℕ) := ix0766.map fun i => (Pop.S0387.leaves.getD i dflt).1
theorem r0766_ok : ∀ p ∈ r0766, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0387.sem ix0766_lt

def ix0767 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]
theorem ix0767_lt : ∀ i ∈ ix0767, i < Pop.S0388.leaves.length := by decide +kernel
def r0767 : List (List ℕ) := ix0767.map fun i => (Pop.S0388.leaves.getD i dflt).1
theorem r0767_ok : ∀ p ∈ r0767, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0388.sem ix0767_lt

def ix0768 : List ℕ := [67, 68, 69, 70, 71, 72, 73]
theorem ix0768_lt : ∀ i ∈ ix0768, i < Pop.S0389.leaves.length := by decide +kernel
def r0768 : List (List ℕ) := ix0768.map fun i => (Pop.S0389.leaves.getD i dflt).1
theorem r0768_ok : ∀ p ∈ r0768, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0389.sem ix0768_lt

def ix0769 : List ℕ := [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 114, 115, 116]
theorem ix0769_lt : ∀ i ∈ ix0769, i < Pop.S0390.leaves.length := by decide +kernel
def r0769 : List (List ℕ) := ix0769.map fun i => (Pop.S0390.leaves.getD i dflt).1
theorem r0769_ok : ∀ p ∈ r0769, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0390.sem ix0769_lt

def ix0770 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54]
theorem ix0770_lt : ∀ i ∈ ix0770, i < Pop.S0391.leaves.length := by decide +kernel
def r0770 : List (List ℕ) := ix0770.map fun i => (Pop.S0391.leaves.getD i dflt).1
theorem r0770_ok : ∀ p ∈ r0770, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0391.sem ix0770_lt

def ix0771 : List ℕ := [87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]
theorem ix0771_lt : ∀ i ∈ ix0771, i < Pop.S0392.leaves.length := by decide +kernel
def r0771 : List (List ℕ) := ix0771.map fun i => (Pop.S0392.leaves.getD i dflt).1
theorem r0771_ok : ∀ p ∈ r0771, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0392.sem ix0771_lt

def ix0772 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58]
theorem ix0772_lt : ∀ i ∈ ix0772, i < Pop.S0393.leaves.length := by decide +kernel
def r0772 : List (List ℕ) := ix0772.map fun i => (Pop.S0393.leaves.getD i dflt).1
theorem r0772_ok : ∀ p ∈ r0772, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0393.sem ix0772_lt

def ix0773 : List ℕ := [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
theorem ix0773_lt : ∀ i ∈ ix0773, i < Pop.S0046.leaves.length := by decide +kernel
def r0773 : List (List ℕ) := ix0773.map fun i => (Pop.S0046.leaves.getD i dflt).1
theorem r0773_ok : ∀ p ∈ r0773, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0046.sem ix0773_lt

end CKLaneM1.ML.Population


