-- Prove2me | Definitions.Def_CK_CKLaneM1_MLPopulationDfs_q01_q01
-- name    : CK_CKLaneM1_MLPopulationDfs_q01_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T16:06:45.752996+00:00
-- url     : https://prove2.me/theorems/0bc813d4-0ff2-4a2b-9184-b6dbd5c6ae24
-- title:
--   Courtade–Kumar proof module `CKLaneM1.MLPopulationDfs (piece 2 of 4) (piece 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM1.MLPopulationDfs (piece 2 of 4) (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM1.MLPopulationDfs (piece 2 of 4) (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM1.MLPopulationDfs (piece 2 of 4) (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM1/MLPopulationDfs (piece 2 of 4) (piece 2 of 3).lean)

import Definitions.Def_CK_CKLaneM1_MLPopulationDfs_q01_q00

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneM1.ML.Population
open CKLaneM1.ML
def ix0787 : List ℕ := [0, 1, 2, 3, 4, 5, 6]
theorem ix0787_lt : ∀ i ∈ ix0787, i < Pop.S0172.leaves.length := by decide +kernel
def r0787 : List (List ℕ) := ix0787.map fun i => (Pop.S0172.leaves.getD i dflt).1
theorem r0787_ok : ∀ p ∈ r0787, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0172.sem ix0787_lt

def ix0788 : List ℕ := [30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]
theorem ix0788_lt : ∀ i ∈ ix0788, i < Pop.S0174.leaves.length := by decide +kernel
def r0788 : List (List ℕ) := ix0788.map fun i => (Pop.S0174.leaves.getD i dflt).1
theorem r0788_ok : ∀ p ∈ r0788, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0174.sem ix0788_lt

def ix0789 : List ℕ := [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]
theorem ix0789_lt : ∀ i ∈ ix0789, i < Pop.S0180.leaves.length := by decide +kernel
def r0789 : List (List ℕ) := ix0789.map fun i => (Pop.S0180.leaves.getD i dflt).1
theorem r0789_ok : ∀ p ∈ r0789, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0180.sem ix0789_lt

def ix0790 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51]
theorem ix0790_lt : ∀ i ∈ ix0790, i < Pop.S0181.leaves.length := by decide +kernel
def r0790 : List (List ℕ) := ix0790.map fun i => (Pop.S0181.leaves.getD i dflt).1
theorem r0790_ok : ∀ p ∈ r0790, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0181.sem ix0790_lt

def ix0791 : List ℕ := [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]
theorem ix0791_lt : ∀ i ∈ ix0791, i < Pop.S0182.leaves.length := by decide +kernel
def r0791 : List (List ℕ) := ix0791.map fun i => (Pop.S0182.leaves.getD i dflt).1
theorem r0791_ok : ∀ p ∈ r0791, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0182.sem ix0791_lt

def ix0792 : List ℕ := [52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
theorem ix0792_lt : ∀ i ∈ ix0792, i < Pop.S0181.leaves.length := by decide +kernel
def r0792 : List (List ℕ) := ix0792.map fun i => (Pop.S0181.leaves.getD i dflt).1
theorem r0792_ok : ∀ p ∈ r0792, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0181.sem ix0792_lt

def ix0793 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]
theorem ix0793_lt : ∀ i ∈ ix0793, i < Pop.S0182.leaves.length := by decide +kernel
def r0793 : List (List ℕ) := ix0793.map fun i => (Pop.S0182.leaves.getD i dflt).1
theorem r0793_ok : ∀ p ∈ r0793, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0182.sem ix0793_lt

def ix0794 : List ℕ := [113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
theorem ix0794_lt : ∀ i ∈ ix0794, i < Pop.S0184.leaves.length := by decide +kernel
def r0794 : List (List ℕ) := ix0794.map fun i => (Pop.S0184.leaves.getD i dflt).1
theorem r0794_ok : ∀ p ∈ r0794, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0184.sem ix0794_lt

def ix0795 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]
theorem ix0795_lt : ∀ i ∈ ix0795, i < Pop.S0185.leaves.length := by decide +kernel
def r0795 : List (List ℕ) := ix0795.map fun i => (Pop.S0185.leaves.getD i dflt).1
theorem r0795_ok : ∀ p ∈ r0795, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0185.sem ix0795_lt

def ix0796 : List ℕ := [134, 135, 136, 137, 138, 139, 140, 141]
theorem ix0796_lt : ∀ i ∈ ix0796, i < Pop.S0186.leaves.length := by decide +kernel
def r0796 : List (List ℕ) := ix0796.map fun i => (Pop.S0186.leaves.getD i dflt).1
theorem r0796_ok : ∀ p ∈ r0796, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0186.sem ix0796_lt

def ix0797 : List ℕ := [35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60]
theorem ix0797_lt : ∀ i ∈ ix0797, i < Pop.S0192.leaves.length := by decide +kernel
def r0797 : List (List ℕ) := ix0797.map fun i => (Pop.S0192.leaves.getD i dflt).1
theorem r0797_ok : ∀ p ∈ r0797, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0192.sem ix0797_lt

def ix0798 : List ℕ := [83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]
theorem ix0798_lt : ∀ i ∈ ix0798, i < Pop.S0193.leaves.length := by decide +kernel
def r0798 : List (List ℕ) := ix0798.map fun i => (Pop.S0193.leaves.getD i dflt).1
theorem r0798_ok : ∀ p ∈ r0798, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0193.sem ix0798_lt

def ix0799 : List ℕ := [116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]
theorem ix0799_lt : ∀ i ∈ ix0799, i < Pop.S0196.leaves.length := by decide +kernel
def r0799 : List (List ℕ) := ix0799.map fun i => (Pop.S0196.leaves.getD i dflt).1
theorem r0799_ok : ∀ p ∈ r0799, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0196.sem ix0799_lt

end CKLaneM1.ML.Population


