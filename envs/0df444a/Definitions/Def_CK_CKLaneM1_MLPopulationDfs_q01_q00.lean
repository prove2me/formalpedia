-- Prove2me | Definitions.Def_CK_CKLaneM1_MLPopulationDfs_q01_q00
-- name    : CK_CKLaneM1_MLPopulationDfs_q01_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T15:54:00.445146+00:00
-- url     : https://prove2.me/theorems/58a3fb6c-30e8-4803-96db-6515681c0df4
-- title:
--   Courtade–Kumar proof module `CKLaneM1.MLPopulationDfs (piece 2 of 4) (piece 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM1.MLPopulationDfs (piece 2 of 4) (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM1.MLPopulationDfs (piece 2 of 4) (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM1.MLPopulationDfs (piece 2 of 4) (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM1/MLPopulationDfs (piece 2 of 4) (piece 1 of 3).lean)

import Definitions.Def_CK_CKLaneM1_MLPopulationDfs_q00


set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneM1.ML.Population
open CKLaneM1.ML
def ix0774 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 85, 86]
theorem ix0774_lt : ∀ i ∈ ix0774, i < Pop.S0047.leaves.length := by decide +kernel
def r0774 : List (List ℕ) := ix0774.map fun i => (Pop.S0047.leaves.getD i dflt).1
theorem r0774_ok : ∀ p ∈ r0774, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0047.sem ix0774_lt

def ix0775 : List ℕ := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]
theorem ix0775_lt : ∀ i ∈ ix0775, i < Pop.S0048.leaves.length := by decide +kernel
def r0775 : List (List ℕ) := ix0775.map fun i => (Pop.S0048.leaves.getD i dflt).1
theorem r0775_ok : ∀ p ∈ r0775, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0048.sem ix0775_lt

def ix0776 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72]
theorem ix0776_lt : ∀ i ∈ ix0776, i < Pop.S0049.leaves.length := by decide +kernel
def r0776 : List (List ℕ) := ix0776.map fun i => (Pop.S0049.leaves.getD i dflt).1
theorem r0776_ok : ∀ p ∈ r0776, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0049.sem ix0776_lt

def ix0777 : List ℕ := [103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]
theorem ix0777_lt : ∀ i ∈ ix0777, i < Pop.S0051.leaves.length := by decide +kernel
def r0777 : List (List ℕ) := ix0777.map fun i => (Pop.S0051.leaves.getD i dflt).1
theorem r0777_ok : ∀ p ∈ r0777, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0051.sem ix0777_lt

def ix0778 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 135, 136, 137, 138, 139, 140]
theorem ix0778_lt : ∀ i ∈ ix0778, i < Pop.S0052.leaves.length := by decide +kernel
def r0778 : List (List ℕ) := ix0778.map fun i => (Pop.S0052.leaves.getD i dflt).1
theorem r0778_ok : ∀ p ∈ r0778, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0052.sem ix0778_lt

def ix0779 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45]
theorem ix0779_lt : ∀ i ∈ ix0779, i < Pop.S0053.leaves.length := by decide +kernel
def r0779 : List (List ℕ) := ix0779.map fun i => (Pop.S0053.leaves.getD i dflt).1
theorem r0779_ok : ∀ p ∈ r0779, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0053.sem ix0779_lt

def ix0780 : List ℕ := [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]
theorem ix0780_lt : ∀ i ∈ ix0780, i < Pop.S0054.leaves.length := by decide +kernel
def r0780 : List (List ℕ) := ix0780.map fun i => (Pop.S0054.leaves.getD i dflt).1
theorem r0780_ok : ∀ p ∈ r0780, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0054.sem ix0780_lt

def ix0781 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67]
theorem ix0781_lt : ∀ i ∈ ix0781, i < Pop.S0055.leaves.length := by decide +kernel
def r0781 : List (List ℕ) := ix0781.map fun i => (Pop.S0055.leaves.getD i dflt).1
theorem r0781_ok : ∀ p ∈ r0781, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0055.sem ix0781_lt

def ix0782 : List ℕ := [73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
theorem ix0782_lt : ∀ i ∈ ix0782, i < Pop.S0049.leaves.length := by decide +kernel
def r0782 : List (List ℕ) := ix0782.map fun i => (Pop.S0049.leaves.getD i dflt).1
theorem r0782_ok : ∀ p ∈ r0782, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0049.sem ix0782_lt

def ix0783 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]
theorem ix0783_lt : ∀ i ∈ ix0783, i < Pop.S0050.leaves.length := by decide +kernel
def r0783 : List (List ℕ) := ix0783.map fun i => (Pop.S0050.leaves.getD i dflt).1
theorem r0783_ok : ∀ p ∈ r0783, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0050.sem ix0783_lt

def ix0784 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100]
theorem ix0784_lt : ∀ i ∈ ix0784, i < Pop.S0051.leaves.length := by decide +kernel
def r0784 : List (List ℕ) := ix0784.map fun i => (Pop.S0051.leaves.getD i dflt).1
theorem r0784_ok : ∀ p ∈ r0784, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0051.sem ix0784_lt

def ix0785 : List ℕ := [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]
theorem ix0785_lt : ∀ i ∈ ix0785, i < Pop.S0170.leaves.length := by decide +kernel
def r0785 : List (List ℕ) := ix0785.map fun i => (Pop.S0170.leaves.getD i dflt).1
theorem r0785_ok : ∀ p ∈ r0785, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0170.sem ix0785_lt

def ix0786 : List ℕ := [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]
theorem ix0786_lt : ∀ i ∈ ix0786, i < Pop.S0171.leaves.length := by decide +kernel
def r0786 : List (List ℕ) := ix0786.map fun i => (Pop.S0171.leaves.getD i dflt).1
theorem r0786_ok : ∀ p ∈ r0786, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0171.sem ix0786_lt

end CKLaneM1.ML.Population


