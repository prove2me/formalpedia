-- Prove2me | Definitions.Def_CK_CKLaneM1_MLPopulationDfs_q00_q00
-- name    : CK_CKLaneM1_MLPopulationDfs_q00_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T09:51:15.665347+00:00
-- url     : https://prove2.me/theorems/02d52f81-ae71-43b7-89a6-bbe95a8d62c8
-- title:
--   Courtade–Kumar proof module `CKLaneM1.MLPopulationDfs (piece 1 of 4) (piece 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM1.MLPopulationDfs (piece 1 of 4) (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM1.MLPopulationDfs (piece 1 of 4) (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM1.MLPopulationDfs (piece 1 of 4) (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM1/MLPopulationDfs (piece 1 of 4) (piece 1 of 3).lean)

import Definitions.Def_CK_CKLaneM1_MLPopulationDfs_part00



/-!
# Lane M1: the archived mean_logsum paths in DFS order of the archived (S) tree

For `CKLaneG3.tconsume` / `label_family_of_consume` (linear DFS walk): `dfsList` lists all 50429 archived
mean_logsum paths in lexicographic (= DFS; children digits `2ax < 2ax+1`) order.  It is built from 851
runs, each a DFS-consecutive run inside ONE population shard, given as kernel-range-checked indices into that
shard's certified leaf list (`getD`), so no path comparison or sorting is evaluated here.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace CKLaneM1.ML.Population

open CKLaneM1.ML

def ix0735 : List ℕ := [0]
theorem ix0735_lt : ∀ i ∈ ix0735, i < Pop.S0373.leaves.length := by decide +kernel
def r0735 : List (List ℕ) := ix0735.map fun i => (Pop.S0373.leaves.getD i dflt).1
theorem r0735_ok : ∀ p ∈ r0735, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0373.sem ix0735_lt

def ix0736 : List ℕ := [98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]
theorem ix0736_lt : ∀ i ∈ ix0736, i < Pop.S0374.leaves.length := by decide +kernel
def r0736 : List (List ℕ) := ix0736.map fun i => (Pop.S0374.leaves.getD i dflt).1
theorem r0736_ok : ∀ p ∈ r0736, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0374.sem ix0736_lt

def ix0737 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]
theorem ix0737_lt : ∀ i ∈ ix0737, i < Pop.S0375.leaves.length := by decide +kernel
def r0737 : List (List ℕ) := ix0737.map fun i => (Pop.S0375.leaves.getD i dflt).1
theorem r0737_ok : ∀ p ∈ r0737, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0375.sem ix0737_lt

def ix0738 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65]
theorem ix0738_lt : ∀ i ∈ ix0738, i < Pop.S0376.leaves.length := by decide +kernel
def r0738 : List (List ℕ) := ix0738.map fun i => (Pop.S0376.leaves.getD i dflt).1
theorem r0738_ok : ∀ p ∈ r0738, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0376.sem ix0738_lt

def ix0739 : List ℕ := [28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59]
theorem ix0739_lt : ∀ i ∈ ix0739, i < Pop.S0378.leaves.length := by decide +kernel
def r0739 : List (List ℕ) := ix0739.map fun i => (Pop.S0378.leaves.getD i dflt).1
theorem r0739_ok : ∀ p ∈ r0739, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0378.sem ix0739_lt

def ix0740 : List ℕ := [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]
theorem ix0740_lt : ∀ i ∈ ix0740, i < Pop.S0376.leaves.length := by decide +kernel
def r0740 : List (List ℕ) := ix0740.map fun i => (Pop.S0376.leaves.getD i dflt).1
theorem r0740_ok : ∀ p ∈ r0740, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0376.sem ix0740_lt

def ix0741 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]
theorem ix0741_lt : ∀ i ∈ ix0741, i < Pop.S0377.leaves.length := by decide +kernel
def r0741 : List (List ℕ) := ix0741.map fun i => (Pop.S0377.leaves.getD i dflt).1
theorem r0741_ok : ∀ p ∈ r0741, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0377.sem ix0741_lt

def ix0742 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90]
theorem ix0742_lt : ∀ i ∈ ix0742, i < Pop.S0378.leaves.length := by decide +kernel
def r0742 : List (List ℕ) := ix0742.map fun i => (Pop.S0378.leaves.getD i dflt).1
theorem r0742_ok : ∀ p ∈ r0742, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0378.sem ix0742_lt

def ix0743 : List ℕ := [60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]
theorem ix0743_lt : ∀ i ∈ ix0743, i < Pop.S0381.leaves.length := by decide +kernel
def r0743 : List (List ℕ) := ix0743.map fun i => (Pop.S0381.leaves.getD i dflt).1
theorem r0743_ok : ∀ p ∈ r0743, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0381.sem ix0743_lt

def ix0744 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]
theorem ix0744_lt : ∀ i ∈ ix0744, i < Pop.S0382.leaves.length := by decide +kernel
def r0744 : List (List ℕ) := ix0744.map fun i => (Pop.S0382.leaves.getD i dflt).1
theorem r0744_ok : ∀ p ∈ r0744, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0382.sem ix0744_lt

def ix0745 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81]
theorem ix0745_lt : ∀ i ∈ ix0745, i < Pop.S0383.leaves.length := by decide +kernel
def r0745 : List (List ℕ) := ix0745.map fun i => (Pop.S0383.leaves.getD i dflt).1
theorem r0745_ok : ∀ p ∈ r0745, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0383.sem ix0745_lt

def ix0746 : List ℕ := [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]
theorem ix0746_lt : ∀ i ∈ ix0746, i < Pop.S0355.leaves.length := by decide +kernel
def r0746 : List (List ℕ) := ix0746.map fun i => (Pop.S0355.leaves.getD i dflt).1
theorem r0746_ok : ∀ p ∈ r0746, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0355.sem ix0746_lt

def ix0747 : List ℕ := [0, 1]
theorem ix0747_lt : ∀ i ∈ ix0747, i < Pop.S0356.leaves.length := by decide +kernel
def r0747 : List (List ℕ) := ix0747.map fun i => (Pop.S0356.leaves.getD i dflt).1
theorem r0747_ok : ∀ p ∈ r0747, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0356.sem ix0747_lt

end CKLaneM1.ML.Population


