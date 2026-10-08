-- Prove2me | Definitions.Def_CK_CKLaneM1_MLPopulationDfs_part00
-- name    : CK_CKLaneM1_MLPopulationDfs_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T00:53:38.954867+00:00
-- url     : https://prove2.me/theorems/de2df3f9-a2ee-4d43-8fc2-c953ca10633f
-- title:
--   Courtade–Kumar proof module `CKLaneM1.MLPopulationDfs (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM1.MLPopulationDfs (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM1.MLPopulationDfs (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM1.MLPopulationDfs (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM1/MLPopulationDfs (part 1 of 2).lean)

import Definitions.Def_CK_CKLaneM1_MLPopulation

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

/-- Default entry for `getD` (never reached: every index is kernel-checked in range). -/
def dflt : List ℕ × LeafCert := ([], { r1 := 0, r2 := 0, tree := MTree.leaf ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩ })

theorem getD_mem {α : Type} : ∀ (L : List α) (i : ℕ) (d : α), i < L.length → L.getD i d ∈ L
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _, _ => List.mem_cons_self ..
  | _ :: xs, i + 1, d, h => List.mem_cons_of_mem _ (getD_mem xs i d (Nat.lt_of_succ_lt_succ h))

theorem idx_ok {L : List (List ℕ × LeafCert)} (hL : ∀ x ∈ L, SemSS (ssBox x.1)) {I : List ℕ}
    (hI : ∀ i ∈ I, i < L.length) :
    ∀ p ∈ I.map (fun i => (L.getD i dflt).1), CKLaneG3.SLeafOK (CKLaneG3.sBox p) := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  exact sLeafOK_of_semSS (hL _ (getD_mem L i dflt (hI i hi)))

theorem ok_append {G₁ G₂ : List (List ℕ)} (h₁ : ∀ p ∈ G₁, CKLaneG3.SLeafOK (CKLaneG3.sBox p))
    (h₂ : ∀ p ∈ G₂, CKLaneG3.SLeafOK (CKLaneG3.sBox p)) :
    ∀ p ∈ G₁ ++ G₂, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact h₁ p h
  · exact h₂ p h

def ix0000 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
theorem ix0000_lt : ∀ i ∈ ix0000, i < Pop.S0000.leaves.length := by decide +kernel
def r0000 : List (List ℕ) := ix0000.map fun i => (Pop.S0000.leaves.getD i dflt).1
theorem r0000_ok : ∀ p ∈ r0000, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0000.sem ix0000_lt

def ix0001 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
theorem ix0001_lt : ∀ i ∈ ix0001, i < Pop.S0001.leaves.length := by decide +kernel
def r0001 : List (List ℕ) := ix0001.map fun i => (Pop.S0001.leaves.getD i dflt).1
theorem r0001_ok : ∀ p ∈ r0001, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0001.sem ix0001_lt

def ix0002 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
theorem ix0002_lt : ∀ i ∈ ix0002, i < Pop.S0002.leaves.length := by decide +kernel
def r0002 : List (List ℕ) := ix0002.map fun i => (Pop.S0002.leaves.getD i dflt).1
theorem r0002_ok : ∀ p ∈ r0002, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0002.sem ix0002_lt

def ix0003 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
theorem ix0003_lt : ∀ i ∈ ix0003, i < Pop.S0003.leaves.length := by decide +kernel
def r0003 : List (List ℕ) := ix0003.map fun i => (Pop.S0003.leaves.getD i dflt).1
theorem r0003_ok : ∀ p ∈ r0003, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0003.sem ix0003_lt

def ix0004 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
theorem ix0004_lt : ∀ i ∈ ix0004, i < Pop.S0004.leaves.length := by decide +kernel
def r0004 : List (List ℕ) := ix0004.map fun i => (Pop.S0004.leaves.getD i dflt).1
theorem r0004_ok : ∀ p ∈ r0004, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0004.sem ix0004_lt

def ix0005 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
theorem ix0005_lt : ∀ i ∈ ix0005, i < Pop.S0005.leaves.length := by decide +kernel
def r0005 : List (List ℕ) := ix0005.map fun i => (Pop.S0005.leaves.getD i dflt).1
theorem r0005_ok : ∀ p ∈ r0005, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0005.sem ix0005_lt

def ix0006 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
theorem ix0006_lt : ∀ i ∈ ix0006, i < Pop.S0006.leaves.length := by decide +kernel
def r0006 : List (List ℕ) := ix0006.map fun i => (Pop.S0006.leaves.getD i dflt).1
theorem r0006_ok : ∀ p ∈ r0006, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0006.sem ix0006_lt

def ix0007 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]
theorem ix0007_lt : ∀ i ∈ ix0007, i < Pop.S0007.leaves.length := by decide +kernel
def r0007 : List (List ℕ) := ix0007.map fun i => (Pop.S0007.leaves.getD i dflt).1
theorem r0007_ok : ∀ p ∈ r0007, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0007.sem ix0007_lt

def ix0008 : List ℕ := [14, 15, 16, 9, 10, 11, 12, 13, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]
theorem ix0008_lt : ∀ i ∈ ix0008, i < Pop.S0008.leaves.length := by decide +kernel
def r0008 : List (List ℕ) := ix0008.map fun i => (Pop.S0008.leaves.getD i dflt).1
theorem r0008_ok : ∀ p ∈ r0008, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0008.sem ix0008_lt

def ix0009 : List ℕ := [140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
theorem ix0009_lt : ∀ i ∈ ix0009, i < Pop.S0007.leaves.length := by decide +kernel
def r0009 : List (List ℕ) := ix0009.map fun i => (Pop.S0007.leaves.getD i dflt).1
theorem r0009_ok : ∀ p ∈ r0009, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0007.sem ix0009_lt

def ix0010 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
theorem ix0010_lt : ∀ i ∈ ix0010, i < Pop.S0008.leaves.length := by decide +kernel
def r0010 : List (List ℕ) := ix0010.map fun i => (Pop.S0008.leaves.getD i dflt).1
theorem r0010_ok : ∀ p ∈ r0010, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0008.sem ix0010_lt

def ix0011 : List ℕ := [48]
theorem ix0011_lt : ∀ i ∈ ix0011, i < Pop.S0011.leaves.length := by decide +kernel
def r0011 : List (List ℕ) := ix0011.map fun i => (Pop.S0011.leaves.getD i dflt).1
theorem r0011_ok : ∀ p ∈ r0011, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0011.sem ix0011_lt

def ix0012 : List ℕ := [96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
theorem ix0012_lt : ∀ i ∈ ix0012, i < Pop.S0008.leaves.length := by decide +kernel
def r0012 : List (List ℕ) := ix0012.map fun i => (Pop.S0008.leaves.getD i dflt).1
theorem r0012_ok : ∀ p ∈ r0012, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0008.sem ix0012_lt

def ix0013 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
theorem ix0013_lt : ∀ i ∈ ix0013, i < Pop.S0009.leaves.length := by decide +kernel
def r0013 : List (List ℕ) := ix0013.map fun i => (Pop.S0009.leaves.getD i dflt).1
theorem r0013_ok : ∀ p ∈ r0013, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0009.sem ix0013_lt

def ix0014 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
theorem ix0014_lt : ∀ i ∈ ix0014, i < Pop.S0010.leaves.length := by decide +kernel
def r0014 : List (List ℕ) := ix0014.map fun i => (Pop.S0010.leaves.getD i dflt).1
theorem r0014_ok : ∀ p ∈ r0014, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0010.sem ix0014_lt

def ix0015 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]
theorem ix0015_lt : ∀ i ∈ ix0015, i < Pop.S0011.leaves.length := by decide +kernel
def r0015 : List (List ℕ) := ix0015.map fun i => (Pop.S0011.leaves.getD i dflt).1
theorem r0015_ok : ∀ p ∈ r0015, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0011.sem ix0015_lt

def ix0016 : List ℕ := [26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60]
theorem ix0016_lt : ∀ i ∈ ix0016, i < Pop.S0010.leaves.length := by decide +kernel
def r0016 : List (List ℕ) := ix0016.map fun i => (Pop.S0010.leaves.getD i dflt).1
theorem r0016_ok : ∀ p ∈ r0016, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0010.sem ix0016_lt

def ix0017 : List ℕ := [49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70]
theorem ix0017_lt : ∀ i ∈ ix0017, i < Pop.S0011.leaves.length := by decide +kernel
def r0017 : List (List ℕ) := ix0017.map fun i => (Pop.S0011.leaves.getD i dflt).1
theorem r0017_ok : ∀ p ∈ r0017, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0011.sem ix0017_lt

def ix0018 : List ℕ := [31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112]
theorem ix0018_lt : ∀ i ∈ ix0018, i < Pop.S0021.leaves.length := by decide +kernel
def r0018 : List (List ℕ) := ix0018.map fun i => (Pop.S0021.leaves.getD i dflt).1
theorem r0018_ok : ∀ p ∈ r0018, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0021.sem ix0018_lt

def ix0019 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
theorem ix0019_lt : ∀ i ∈ ix0019, i < Pop.S0022.leaves.length := by decide +kernel
def r0019 : List (List ℕ) := ix0019.map fun i => (Pop.S0022.leaves.getD i dflt).1
theorem r0019_ok : ∀ p ∈ r0019, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0022.sem ix0019_lt

def ix0020 : List ℕ := [115, 116]
theorem ix0020_lt : ∀ i ∈ ix0020, i < Pop.S0399.leaves.length := by decide +kernel
def r0020 : List (List ℕ) := ix0020.map fun i => (Pop.S0399.leaves.getD i dflt).1
theorem r0020_ok : ∀ p ∈ r0020, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0399.sem ix0020_lt

def ix0021 : List ℕ := [31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44]
theorem ix0021_lt : ∀ i ∈ ix0021, i < Pop.S0403.leaves.length := by decide +kernel
def r0021 : List (List ℕ) := ix0021.map fun i => (Pop.S0403.leaves.getD i dflt).1
theorem r0021_ok : ∀ p ∈ r0021, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0403.sem ix0021_lt

def ix0022 : List ℕ := [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146]
theorem ix0022_lt : ∀ i ∈ ix0022, i < Pop.S0404.leaves.length := by decide +kernel
def r0022 : List (List ℕ) := ix0022.map fun i => (Pop.S0404.leaves.getD i dflt).1
theorem r0022_ok : ∀ p ∈ r0022, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0404.sem ix0022_lt

def ix0023 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
theorem ix0023_lt : ∀ i ∈ ix0023, i < Pop.S0405.leaves.length := by decide +kernel
def r0023 : List (List ℕ) := ix0023.map fun i => (Pop.S0405.leaves.getD i dflt).1
theorem r0023_ok : ∀ p ∈ r0023, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0405.sem ix0023_lt

def ix0024 : List ℕ := [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 132, 133, 134, 135, 136, 137, 138, 139, 140]
theorem ix0024_lt : ∀ i ∈ ix0024, i < Pop.S0408.leaves.length := by decide +kernel
def r0024 : List (List ℕ) := ix0024.map fun i => (Pop.S0408.leaves.getD i dflt).1
theorem r0024_ok : ∀ p ∈ r0024, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0408.sem ix0024_lt

def ix0025 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76]
theorem ix0025_lt : ∀ i ∈ ix0025, i < Pop.S0409.leaves.length := by decide +kernel
def r0025 : List (List ℕ) := ix0025.map fun i => (Pop.S0409.leaves.getD i dflt).1
theorem r0025_ok : ∀ p ∈ r0025, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0409.sem ix0025_lt

def ix0026 : List ℕ := [35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]
theorem ix0026_lt : ∀ i ∈ ix0026, i < Pop.S0410.leaves.length := by decide +kernel
def r0026 : List (List ℕ) := ix0026.map fun i => (Pop.S0410.leaves.getD i dflt).1
theorem r0026_ok : ∀ p ∈ r0026, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0410.sem ix0026_lt

def ix0027 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]
theorem ix0027_lt : ∀ i ∈ ix0027, i < Pop.S0411.leaves.length := by decide +kernel
def r0027 : List (List ℕ) := ix0027.map fun i => (Pop.S0411.leaves.getD i dflt).1
theorem r0027_ok : ∀ p ∈ r0027, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0411.sem ix0027_lt

def ix0028 : List ℕ := [22, 23, 24, 25, 26]
theorem ix0028_lt : ∀ i ∈ ix0028, i < Pop.S0412.leaves.length := by decide +kernel
def r0028 : List (List ℕ) := ix0028.map fun i => (Pop.S0412.leaves.getD i dflt).1
theorem r0028_ok : ∀ p ∈ r0028, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0412.sem ix0028_lt

def ix0029 : List ℕ := [31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]
theorem ix0029_lt : ∀ i ∈ ix0029, i < Pop.S0413.leaves.length := by decide +kernel
def r0029 : List (List ℕ) := ix0029.map fun i => (Pop.S0413.leaves.getD i dflt).1
theorem r0029_ok : ∀ p ∈ r0029, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0413.sem ix0029_lt

def ix0030 : List ℕ := [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]
theorem ix0030_lt : ∀ i ∈ ix0030, i < Pop.S0401.leaves.length := by decide +kernel
def r0030 : List (List ℕ) := ix0030.map fun i => (Pop.S0401.leaves.getD i dflt).1
theorem r0030_ok : ∀ p ∈ r0030, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0401.sem ix0030_lt

def ix0031 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
theorem ix0031_lt : ∀ i ∈ ix0031, i < Pop.S0402.leaves.length := by decide +kernel
def r0031 : List (List ℕ) := ix0031.map fun i => (Pop.S0402.leaves.getD i dflt).1
theorem r0031_ok : ∀ p ∈ r0031, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0402.sem ix0031_lt

def ix0032 : List ℕ := [45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88]
theorem ix0032_lt : ∀ i ∈ ix0032, i < Pop.S0403.leaves.length := by decide +kernel
def r0032 : List (List ℕ) := ix0032.map fun i => (Pop.S0403.leaves.getD i dflt).1
theorem r0032_ok : ∀ p ∈ r0032, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0403.sem ix0032_lt

def ix0033 : List ℕ := [37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
theorem ix0033_lt : ∀ i ∈ ix0033, i < Pop.S0417.leaves.length := by decide +kernel
def r0033 : List (List ℕ) := ix0033.map fun i => (Pop.S0417.leaves.getD i dflt).1
theorem r0033_ok : ∀ p ∈ r0033, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0417.sem ix0033_lt

def ix0034 : List ℕ := [71, 72, 73, 74, 75, 76, 77, 78, 79, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122]
theorem ix0034_lt : ∀ i ∈ ix0034, i < Pop.S0011.leaves.length := by decide +kernel
def r0034 : List (List ℕ) := ix0034.map fun i => (Pop.S0011.leaves.getD i dflt).1
theorem r0034_ok : ∀ p ∈ r0034, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0011.sem ix0034_lt

def ix0035 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100]
theorem ix0035_lt : ∀ i ∈ ix0035, i < Pop.S0012.leaves.length := by decide +kernel
def r0035 : List (List ℕ) := ix0035.map fun i => (Pop.S0012.leaves.getD i dflt).1
theorem r0035_ok : ∀ p ∈ r0035, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0012.sem ix0035_lt

def ix0036 : List ℕ := [140]
theorem ix0036_lt : ∀ i ∈ ix0036, i < Pop.S0047.leaves.length := by decide +kernel
def r0036 : List (List ℕ) := ix0036.map fun i => (Pop.S0047.leaves.getD i dflt).1
theorem r0036_ok : ∀ p ∈ r0036, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0047.sem ix0036_lt

def ix0037 : List ℕ := [0, 1]
theorem ix0037_lt : ∀ i ∈ ix0037, i < Pop.S0048.leaves.length := by decide +kernel
def r0037 : List (List ℕ) := ix0037.map fun i => (Pop.S0048.leaves.getD i dflt).1
theorem r0037_ok : ∀ p ∈ r0037, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0048.sem ix0037_lt

def ix0038 : List ℕ := [66, 67, 68, 69, 70, 71, 72, 73]
theorem ix0038_lt : ∀ i ∈ ix0038, i < Pop.S0050.leaves.length := by decide +kernel
def r0038 : List (List ℕ) := ix0038.map fun i => (Pop.S0050.leaves.getD i dflt).1
theorem r0038_ok : ∀ p ∈ r0038, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0050.sem ix0038_lt

def ix0039 : List ℕ := [101, 102]
theorem ix0039_lt : ∀ i ∈ ix0039, i < Pop.S0051.leaves.length := by decide +kernel
def r0039 : List (List ℕ) := ix0039.map fun i => (Pop.S0051.leaves.getD i dflt).1
theorem r0039_ok : ∀ p ∈ r0039, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0051.sem ix0039_lt

def ix0040 : List ℕ := [126, 127, 128, 129, 130, 131, 132, 133, 134]
theorem ix0040_lt : ∀ i ∈ ix0040, i < Pop.S0052.leaves.length := by decide +kernel
def r0040 : List (List ℕ) := ix0040.map fun i => (Pop.S0052.leaves.getD i dflt).1
theorem r0040_ok : ∀ p ∈ r0040, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0052.sem ix0040_lt

def ix0041 : List ℕ := [52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90]
theorem ix0041_lt : ∀ i ∈ ix0041, i < Pop.S0053.leaves.length := by decide +kernel
def r0041 : List (List ℕ) := ix0041.map fun i => (Pop.S0053.leaves.getD i dflt).1
theorem r0041_ok : ∀ p ∈ r0041, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0053.sem ix0041_lt

def ix0042 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
theorem ix0042_lt : ∀ i ∈ ix0042, i < Pop.S0054.leaves.length := by decide +kernel
def r0042 : List (List ℕ) := ix0042.map fun i => (Pop.S0054.leaves.getD i dflt).1
theorem r0042_ok : ∀ p ∈ r0042, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0054.sem ix0042_lt

def ix0043 : List ℕ := [68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 86, 87, 88, 89, 90, 91, 92]
theorem ix0043_lt : ∀ i ∈ ix0043, i < Pop.S0055.leaves.length := by decide +kernel
def r0043 : List (List ℕ) := ix0043.map fun i => (Pop.S0055.leaves.getD i dflt).1
theorem r0043_ok : ∀ p ∈ r0043, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0055.sem ix0043_lt

def ix0044 : List ℕ := [71, 72, 73, 74]
theorem ix0044_lt : ∀ i ∈ ix0044, i < Pop.S0056.leaves.length := by decide +kernel
def r0044 : List (List ℕ) := ix0044.map fun i => (Pop.S0056.leaves.getD i dflt).1
theorem r0044_ok : ∀ p ∈ r0044, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0056.sem ix0044_lt

def ix0045 : List ℕ := [0]
theorem ix0045_lt : ∀ i ∈ ix0045, i < Pop.S0057.leaves.length := by decide +kernel
def r0045 : List (List ℕ) := ix0045.map fun i => (Pop.S0057.leaves.getD i dflt).1
theorem r0045_ok : ∀ p ∈ r0045, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0057.sem ix0045_lt

def ix0046 : List ℕ := [46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72]
theorem ix0046_lt : ∀ i ∈ ix0046, i < Pop.S0060.leaves.length := by decide +kernel
def r0046 : List (List ℕ) := ix0046.map fun i => (Pop.S0060.leaves.getD i dflt).1
theorem r0046_ok : ∀ p ∈ r0046, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0060.sem ix0046_lt

def ix0047 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89]
theorem ix0047_lt : ∀ i ∈ ix0047, i < Pop.S0061.leaves.length := by decide +kernel
def r0047 : List (List ℕ) := ix0047.map fun i => (Pop.S0061.leaves.getD i dflt).1
theorem r0047_ok : ∀ p ∈ r0047, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0061.sem ix0047_lt

def ix0048 : List ℕ := [46, 47, 48, 49, 50, 51]
theorem ix0048_lt : ∀ i ∈ ix0048, i < Pop.S0053.leaves.length := by decide +kernel
def r0048 : List (List ℕ) := ix0048.map fun i => (Pop.S0053.leaves.getD i dflt).1
theorem r0048_ok : ∀ p ∈ r0048, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0053.sem ix0048_lt

def ix0049 : List ℕ := [80, 81, 82, 83, 84, 85, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103]
theorem ix0049_lt : ∀ i ∈ ix0049, i < Pop.S0055.leaves.length := by decide +kernel
def r0049 : List (List ℕ) := ix0049.map fun i => (Pop.S0055.leaves.getD i dflt).1
theorem r0049_ok : ∀ p ∈ r0049, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0055.sem ix0049_lt

def ix0050 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70]
theorem ix0050_lt : ∀ i ∈ ix0050, i < Pop.S0056.leaves.length := by decide +kernel
def r0050 : List (List ℕ) := ix0050.map fun i => (Pop.S0056.leaves.getD i dflt).1
theorem r0050_ok : ∀ p ∈ r0050, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0056.sem ix0050_lt

def ix0051 : List ℕ := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44]
theorem ix0051_lt : ∀ i ∈ ix0051, i < Pop.S0057.leaves.length := by decide +kernel
def r0051 : List (List ℕ) := ix0051.map fun i => (Pop.S0057.leaves.getD i dflt).1
theorem r0051_ok : ∀ p ∈ r0051, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0057.sem ix0051_lt

def ix0052 : List ℕ := [25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82]
theorem ix0052_lt : ∀ i ∈ ix0052, i < Pop.S0059.leaves.length := by decide +kernel
def r0052 : List (List ℕ) := ix0052.map fun i => (Pop.S0059.leaves.getD i dflt).1
theorem r0052_ok : ∀ p ∈ r0052, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0059.sem ix0052_lt

def ix0053 : List ℕ := [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45]
theorem ix0053_lt : ∀ i ∈ ix0053, i < Pop.S0060.leaves.length := by decide +kernel
def r0053 : List (List ℕ) := ix0053.map fun i => (Pop.S0060.leaves.getD i dflt).1
theorem r0053_ok : ∀ p ∈ r0053, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0060.sem ix0053_lt

def ix0054 : List ℕ := [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]
theorem ix0054_lt : ∀ i ∈ ix0054, i < Pop.S0061.leaves.length := by decide +kernel
def r0054 : List (List ℕ) := ix0054.map fun i => (Pop.S0061.leaves.getD i dflt).1
theorem r0054_ok : ∀ p ∈ r0054, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0061.sem ix0054_lt

def ix0055 : List ℕ := [62, 63]
theorem ix0055_lt : ∀ i ∈ ix0055, i < Pop.S0058.leaves.length := by decide +kernel
def r0055 : List (List ℕ) := ix0055.map fun i => (Pop.S0058.leaves.getD i dflt).1
theorem r0055_ok : ∀ p ∈ r0055, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0058.sem ix0055_lt

def ix0056 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]
theorem ix0056_lt : ∀ i ∈ ix0056, i < Pop.S0059.leaves.length := by decide +kernel
def r0056 : List (List ℕ) := ix0056.map fun i => (Pop.S0059.leaves.getD i dflt).1
theorem r0056_ok : ∀ p ∈ r0056, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0059.sem ix0056_lt

def ix0057 : List ℕ := [45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67]
theorem ix0057_lt : ∀ i ∈ ix0057, i < Pop.S0057.leaves.length := by decide +kernel
def r0057 : List (List ℕ) := ix0057.map fun i => (Pop.S0057.leaves.getD i dflt).1
theorem r0057_ok : ∀ p ∈ r0057, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0057.sem ix0057_lt

def ix0058 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61]
theorem ix0058_lt : ∀ i ∈ ix0058, i < Pop.S0058.leaves.length := by decide +kernel
def r0058 : List (List ℕ) := ix0058.map fun i => (Pop.S0058.leaves.getD i dflt).1
theorem r0058_ok : ∀ p ∈ r0058, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0058.sem ix0058_lt

def ix0059 : List ℕ := [83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98]
theorem ix0059_lt : ∀ i ∈ ix0059, i < Pop.S0059.leaves.length := by decide +kernel
def r0059 : List (List ℕ) := ix0059.map fun i => (Pop.S0059.leaves.getD i dflt).1
theorem r0059_ok : ∀ p ∈ r0059, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0059.sem ix0059_lt

def ix0060 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]
theorem ix0060_lt : ∀ i ∈ ix0060, i < Pop.S0060.leaves.length := by decide +kernel
def r0060 : List (List ℕ) := ix0060.map fun i => (Pop.S0060.leaves.getD i dflt).1
theorem r0060_ok : ∀ p ∈ r0060, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0060.sem ix0060_lt

def ix0061 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81]
theorem ix0061_lt : ∀ i ∈ ix0061, i < Pop.S0062.leaves.length := by decide +kernel
def r0061 : List (List ℕ) := ix0061.map fun i => (Pop.S0062.leaves.getD i dflt).1
theorem r0061_ok : ∀ p ∈ r0061, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0062.sem ix0061_lt

def ix0062 : List ℕ := [5, 6, 7, 8, 9, 10, 11, 12]
theorem ix0062_lt : ∀ i ∈ ix0062, i < Pop.S0063.leaves.length := by decide +kernel
def r0062 : List (List ℕ) := ix0062.map fun i => (Pop.S0063.leaves.getD i dflt).1
theorem r0062_ok : ∀ p ∈ r0062, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0063.sem ix0062_lt

def ix0063 : List ℕ := [23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83]
theorem ix0063_lt : ∀ i ∈ ix0063, i < Pop.S0104.leaves.length := by decide +kernel
def r0063 : List (List ℕ) := ix0063.map fun i => (Pop.S0104.leaves.getD i dflt).1
theorem r0063_ok : ∀ p ∈ r0063, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0104.sem ix0063_lt

def ix0064 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66]
theorem ix0064_lt : ∀ i ∈ ix0064, i < Pop.S0105.leaves.length := by decide +kernel
def r0064 : List (List ℕ) := ix0064.map fun i => (Pop.S0105.leaves.getD i dflt).1
theorem r0064_ok : ∀ p ∈ r0064, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0105.sem ix0064_lt

def ix0065 : List ℕ := [28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75]
theorem ix0065_lt : ∀ i ∈ ix0065, i < Pop.S0111.leaves.length := by decide +kernel
def r0065 : List (List ℕ) := ix0065.map fun i => (Pop.S0111.leaves.getD i dflt).1
theorem r0065_ok : ∀ p ∈ r0065, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0111.sem ix0065_lt

def ix0066 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71]
theorem ix0066_lt : ∀ i ∈ ix0066, i < Pop.S0112.leaves.length := by decide +kernel
def r0066 : List (List ℕ) := ix0066.map fun i => (Pop.S0112.leaves.getD i dflt).1
theorem r0066_ok : ∀ p ∈ r0066, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0112.sem ix0066_lt

def ix0067 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48]
theorem ix0067_lt : ∀ i ∈ ix0067, i < Pop.S0113.leaves.length := by decide +kernel
def r0067 : List (List ℕ) := ix0067.map fun i => (Pop.S0113.leaves.getD i dflt).1
theorem r0067_ok : ∀ p ∈ r0067, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0113.sem ix0067_lt

def ix0068 : List ℕ := [40, 41, 42]
theorem ix0068_lt : ∀ i ∈ ix0068, i < Pop.S0115.leaves.length := by decide +kernel
def r0068 : List (List ℕ) := ix0068.map fun i => (Pop.S0115.leaves.getD i dflt).1
theorem r0068_ok : ∀ p ∈ r0068, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0115.sem ix0068_lt

def ix0069 : List ℕ := [27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113]
theorem ix0069_lt : ∀ i ∈ ix0069, i < Pop.S0122.leaves.length := by decide +kernel
def r0069 : List (List ℕ) := ix0069.map fun i => (Pop.S0122.leaves.getD i dflt).1
theorem r0069_ok : ∀ p ∈ r0069, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0122.sem ix0069_lt

def ix0070 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]
theorem ix0070_lt : ∀ i ∈ ix0070, i < Pop.S0123.leaves.length := by decide +kernel
def r0070 : List (List ℕ) := ix0070.map fun i => (Pop.S0123.leaves.getD i dflt).1
theorem r0070_ok : ∀ p ∈ r0070, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0123.sem ix0070_lt

def ix0071 : List ℕ := [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103]
theorem ix0071_lt : ∀ i ∈ ix0071, i < Pop.S0124.leaves.length := by decide +kernel
def r0071 : List (List ℕ) := ix0071.map fun i => (Pop.S0124.leaves.getD i dflt).1
theorem r0071_ok : ∀ p ∈ r0071, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0124.sem ix0071_lt

def ix0072 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
theorem ix0072_lt : ∀ i ∈ ix0072, i < Pop.S0125.leaves.length := by decide +kernel
def r0072 : List (List ℕ) := ix0072.map fun i => (Pop.S0125.leaves.getD i dflt).1
theorem r0072_ok : ∀ p ∈ r0072, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0125.sem ix0072_lt

def ix0073 : List ℕ := [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76]
theorem ix0073_lt : ∀ i ∈ ix0073, i < Pop.S0159.leaves.length := by decide +kernel
def r0073 : List (List ℕ) := ix0073.map fun i => (Pop.S0159.leaves.getD i dflt).1
theorem r0073_ok : ∀ p ∈ r0073, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0159.sem ix0073_lt

def ix0074 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]
theorem ix0074_lt : ∀ i ∈ ix0074, i < Pop.S0160.leaves.length := by decide +kernel
def r0074 : List (List ℕ) := ix0074.map fun i => (Pop.S0160.leaves.getD i dflt).1
theorem r0074_ok : ∀ p ∈ r0074, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0160.sem ix0074_lt

def ix0075 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 18, 19, 20, 21, 22, 23, 24, 25]
theorem ix0075_lt : ∀ i ∈ ix0075, i < Pop.S0161.leaves.length := by decide +kernel
def r0075 : List (List ℕ) := ix0075.map fun i => (Pop.S0161.leaves.getD i dflt).1
theorem r0075_ok : ∀ p ∈ r0075, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0161.sem ix0075_lt

def ix0076 : List ℕ := [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77]
theorem ix0076_lt : ∀ i ∈ ix0076, i < Pop.S0162.leaves.length := by decide +kernel
def r0076 : List (List ℕ) := ix0076.map fun i => (Pop.S0162.leaves.getD i dflt).1
theorem r0076_ok : ∀ p ∈ r0076, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0162.sem ix0076_lt

def ix0077 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38]
theorem ix0077_lt : ∀ i ∈ ix0077, i < Pop.S0163.leaves.length := by decide +kernel
def r0077 : List (List ℕ) := ix0077.map fun i => (Pop.S0163.leaves.getD i dflt).1
theorem r0077_ok : ∀ p ∈ r0077, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0163.sem ix0077_lt

def ix0078 : List ℕ := [79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102]
theorem ix0078_lt : ∀ i ∈ ix0078, i < Pop.S0166.leaves.length := by decide +kernel
def r0078 : List (List ℕ) := ix0078.map fun i => (Pop.S0166.leaves.getD i dflt).1
theorem r0078_ok : ∀ p ∈ r0078, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0166.sem ix0078_lt

def ix0079 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87]
theorem ix0079_lt : ∀ i ∈ ix0079, i < Pop.S0167.leaves.length := by decide +kernel
def r0079 : List (List ℕ) := ix0079.map fun i => (Pop.S0167.leaves.getD i dflt).1
theorem r0079_ok : ∀ p ∈ r0079, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0167.sem ix0079_lt

def ix0080 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105]
theorem ix0080_lt : ∀ i ∈ ix0080, i < Pop.S0168.leaves.length := by decide +kernel
def r0080 : List (List ℕ) := ix0080.map fun i => (Pop.S0168.leaves.getD i dflt).1
theorem r0080_ok : ∀ p ∈ r0080, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0168.sem ix0080_lt

def ix0081 : List ℕ := [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73]
theorem ix0081_lt : ∀ i ∈ ix0081, i < Pop.S0172.leaves.length := by decide +kernel
def r0081 : List (List ℕ) := ix0081.map fun i => (Pop.S0172.leaves.getD i dflt).1
theorem r0081_ok : ∀ p ∈ r0081, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0172.sem ix0081_lt

def ix0082 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84]
theorem ix0082_lt : ∀ i ∈ ix0082, i < Pop.S0173.leaves.length := by decide +kernel
def r0082 : List (List ℕ) := ix0082.map fun i => (Pop.S0173.leaves.getD i dflt).1
theorem r0082_ok : ∀ p ∈ r0082, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0173.sem ix0082_lt

def ix0083 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 128, 129, 130, 131, 132, 133, 134, 135]
theorem ix0083_lt : ∀ i ∈ ix0083, i < Pop.S0174.leaves.length := by decide +kernel
def r0083 : List (List ℕ) := ix0083.map fun i => (Pop.S0174.leaves.getD i dflt).1
theorem r0083_ok : ∀ p ∈ r0083, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0174.sem ix0083_lt

def ix0084 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64]
theorem ix0084_lt : ∀ i ∈ ix0084, i < Pop.S0175.leaves.length := by decide +kernel
def r0084 : List (List ℕ) := ix0084.map fun i => (Pop.S0175.leaves.getD i dflt).1
theorem r0084_ok : ∀ p ∈ r0084, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0175.sem ix0084_lt

def ix0085 : List ℕ := [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97]
theorem ix0085_lt : ∀ i ∈ ix0085, i < Pop.S0062.leaves.length := by decide +kernel
def r0085 : List (List ℕ) := ix0085.map fun i => (Pop.S0062.leaves.getD i dflt).1
theorem r0085_ok : ∀ p ∈ r0085, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0062.sem ix0085_lt

def ix0086 : List ℕ := [0, 1, 2, 3, 4, 13]
theorem ix0086_lt : ∀ i ∈ ix0086, i < Pop.S0063.leaves.length := by decide +kernel
def r0086 : List (List ℕ) := ix0086.map fun i => (Pop.S0063.leaves.getD i dflt).1
theorem r0086_ok : ∀ p ∈ r0086, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0063.sem ix0086_lt

def ix0087 : List ℕ := [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]
theorem ix0087_lt : ∀ i ∈ ix0087, i < Pop.S0065.leaves.length := by decide +kernel
def r0087 : List (List ℕ) := ix0087.map fun i => (Pop.S0065.leaves.getD i dflt).1
theorem r0087_ok : ∀ p ∈ r0087, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0065.sem ix0087_lt

def ix0088 : List ℕ := [23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85]
theorem ix0088_lt : ∀ i ∈ ix0088, i < Pop.S0066.leaves.length := by decide +kernel
def r0088 : List (List ℕ) := ix0088.map fun i => (Pop.S0066.leaves.getD i dflt).1
theorem r0088_ok : ∀ p ∈ r0088, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0066.sem ix0088_lt

def ix0089 : List ℕ := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88]
theorem ix0089_lt : ∀ i ∈ ix0089, i < Pop.S0068.leaves.length := by decide +kernel
def r0089 : List (List ℕ) := ix0089.map fun i => (Pop.S0068.leaves.getD i dflt).1
theorem r0089_ok : ∀ p ∈ r0089, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0068.sem ix0089_lt

def ix0090 : List ℕ := [46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96]
theorem ix0090_lt : ∀ i ∈ ix0090, i < Pop.S0072.leaves.length := by decide +kernel
def r0090 : List (List ℕ) := ix0090.map fun i => (Pop.S0072.leaves.getD i dflt).1
theorem r0090_ok : ∀ p ∈ r0090, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0072.sem ix0090_lt

def ix0091 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84]
theorem ix0091_lt : ∀ i ∈ ix0091, i < Pop.S0073.leaves.length := by decide +kernel
def r0091 : List (List ℕ) := ix0091.map fun i => (Pop.S0073.leaves.getD i dflt).1
theorem r0091_ok : ∀ p ∈ r0091, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0073.sem ix0091_lt

def ix0092 : List ℕ := [0, 1]
theorem ix0092_lt : ∀ i ∈ ix0092, i < Pop.S0074.leaves.length := by decide +kernel
def r0092 : List (List ℕ) := ix0092.map fun i => (Pop.S0074.leaves.getD i dflt).1
theorem r0092_ok : ∀ p ∈ r0092, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0074.sem ix0092_lt

def ix0093 : List ℕ := [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102]
theorem ix0093_lt : ∀ i ∈ ix0093, i < Pop.S0067.leaves.length := by decide +kernel
def r0093 : List (List ℕ) := ix0093.map fun i => (Pop.S0067.leaves.getD i dflt).1
theorem r0093_ok : ∀ p ∈ r0093, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0067.sem ix0093_lt

def ix0094 : List ℕ := [0, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99]
theorem ix0094_lt : ∀ i ∈ ix0094, i < Pop.S0068.leaves.length := by decide +kernel
def r0094 : List (List ℕ) := ix0094.map fun i => (Pop.S0068.leaves.getD i dflt).1
theorem r0094_ok : ∀ p ∈ r0094, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0068.sem ix0094_lt

def ix0095 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
theorem ix0095_lt : ∀ i ∈ ix0095, i < Pop.S0069.leaves.length := by decide +kernel
def r0095 : List (List ℕ) := ix0095.map fun i => (Pop.S0069.leaves.getD i dflt).1
theorem r0095_ok : ∀ p ∈ r0095, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0069.sem ix0095_lt

def ix0096 : List ℕ := [46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]
theorem ix0096_lt : ∀ i ∈ ix0096, i < Pop.S0070.leaves.length := by decide +kernel
def r0096 : List (List ℕ) := ix0096.map fun i => (Pop.S0070.leaves.getD i dflt).1
theorem r0096_ok : ∀ p ∈ r0096, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0070.sem ix0096_lt

def ix0097 : List ℕ := [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97]
theorem ix0097_lt : ∀ i ∈ ix0097, i < Pop.S0102.leaves.length := by decide +kernel
def r0097 : List (List ℕ) := ix0097.map fun i => (Pop.S0102.leaves.getD i dflt).1
theorem r0097_ok : ∀ p ∈ r0097, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0102.sem ix0097_lt

def ix0098 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]
theorem ix0098_lt : ∀ i ∈ ix0098, i < Pop.S0103.leaves.length := by decide +kernel
def r0098 : List (List ℕ) := ix0098.map fun i => (Pop.S0103.leaves.getD i dflt).1
theorem r0098_ok : ∀ p ∈ r0098, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0103.sem ix0098_lt

def ix0099 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]
theorem ix0099_lt : ∀ i ∈ ix0099, i < Pop.S0104.leaves.length := by decide +kernel
def r0099 : List (List ℕ) := ix0099.map fun i => (Pop.S0104.leaves.getD i dflt).1
theorem r0099_ok : ∀ p ∈ r0099, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0104.sem ix0099_lt

def ix0100 : List ℕ := [72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97]
theorem ix0100_lt : ∀ i ∈ ix0100, i < Pop.S0109.leaves.length := by decide +kernel
def r0100 : List (List ℕ) := ix0100.map fun i => (Pop.S0109.leaves.getD i dflt).1
theorem r0100_ok : ∀ p ∈ r0100, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0109.sem ix0100_lt

def ix0101 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92]
theorem ix0101_lt : ∀ i ∈ ix0101, i < Pop.S0110.leaves.length := by decide +kernel
def r0101 : List (List ℕ) := ix0101.map fun i => (Pop.S0110.leaves.getD i dflt).1
theorem r0101_ok : ∀ p ∈ r0101, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0110.sem ix0101_lt

def ix0102 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
theorem ix0102_lt : ∀ i ∈ ix0102, i < Pop.S0111.leaves.length := by decide +kernel
def r0102 : List (List ℕ) := ix0102.map fun i => (Pop.S0111.leaves.getD i dflt).1
theorem r0102_ok : ∀ p ∈ r0102, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0111.sem ix0102_lt

def ix0103 : List ℕ := [97, 98, 99, 100, 101, 102, 103, 104, 105, 106]
theorem ix0103_lt : ∀ i ∈ ix0103, i < Pop.S0114.leaves.length := by decide +kernel
def r0103 : List (List ℕ) := ix0103.map fun i => (Pop.S0114.leaves.getD i dflt).1
theorem r0103_ok : ∀ p ∈ r0103, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0114.sem ix0103_lt

def ix0104 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]
theorem ix0104_lt : ∀ i ∈ ix0104, i < Pop.S0115.leaves.length := by decide +kernel
def r0104 : List (List ℕ) := ix0104.map fun i => (Pop.S0115.leaves.getD i dflt).1
theorem r0104_ok : ∀ p ∈ r0104, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0115.sem ix0104_lt

def ix0105 : List ℕ := [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120]
theorem ix0105_lt : ∀ i ∈ ix0105, i < Pop.S0125.leaves.length := by decide +kernel
def r0105 : List (List ℕ) := ix0105.map fun i => (Pop.S0125.leaves.getD i dflt).1
theorem r0105_ok : ∀ p ∈ r0105, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0125.sem ix0105_lt

def ix0106 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42]
theorem ix0106_lt : ∀ i ∈ ix0106, i < Pop.S0126.leaves.length := by decide +kernel
def r0106 : List (List ℕ) := ix0106.map fun i => (Pop.S0126.leaves.getD i dflt).1
theorem r0106_ok : ∀ p ∈ r0106, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0126.sem ix0106_lt

def ix0107 : List ℕ := [67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87]
theorem ix0107_lt : ∀ i ∈ ix0107, i < Pop.S0130.leaves.length := by decide +kernel
def r0107 : List (List ℕ) := ix0107.map fun i => (Pop.S0130.leaves.getD i dflt).1
theorem r0107_ok : ∀ p ∈ r0107, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0130.sem ix0107_lt

def ix0108 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]
theorem ix0108_lt : ∀ i ∈ ix0108, i < Pop.S0131.leaves.length := by decide +kernel
def r0108 : List (List ℕ) := ix0108.map fun i => (Pop.S0131.leaves.getD i dflt).1
theorem r0108_ok : ∀ p ∈ r0108, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0131.sem ix0108_lt

def ix0109 : List ℕ := [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82]
theorem ix0109_lt : ∀ i ∈ ix0109, i < Pop.S0133.leaves.length := by decide +kernel
def r0109 : List (List ℕ) := ix0109.map fun i => (Pop.S0133.leaves.getD i dflt).1
theorem r0109_ok : ∀ p ∈ r0109, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0133.sem ix0109_lt

def ix0110 : List ℕ := [62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108]
theorem ix0110_lt : ∀ i ∈ ix0110, i < Pop.S0138.leaves.length := by decide +kernel
def r0110 : List (List ℕ) := ix0110.map fun i => (Pop.S0138.leaves.getD i dflt).1
theorem r0110_ok : ∀ p ∈ r0110, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0138.sem ix0110_lt

def ix0111 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]
theorem ix0111_lt : ∀ i ∈ ix0111, i < Pop.S0139.leaves.length := by decide +kernel
def r0111 : List (List ℕ) := ix0111.map fun i => (Pop.S0139.leaves.getD i dflt).1
theorem r0111_ok : ∀ p ∈ r0111, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0139.sem ix0111_lt

def ix0112 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36]
theorem ix0112_lt : ∀ i ∈ ix0112, i < Pop.S0140.leaves.length := by decide +kernel
def r0112 : List (List ℕ) := ix0112.map fun i => (Pop.S0140.leaves.getD i dflt).1
theorem r0112_ok : ∀ p ∈ r0112, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0140.sem ix0112_lt

def ix0113 : List ℕ := [94, 95, 96]
theorem ix0113_lt : ∀ i ∈ ix0113, i < Pop.S0141.leaves.length := by decide +kernel
def r0113 : List (List ℕ) := ix0113.map fun i => (Pop.S0141.leaves.getD i dflt).1
theorem r0113_ok : ∀ p ∈ r0113, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0141.sem ix0113_lt

def ix0114 : List ℕ := [46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99]
theorem ix0114_lt : ∀ i ∈ ix0114, i < Pop.S0145.leaves.length := by decide +kernel
def r0114 : List (List ℕ) := ix0114.map fun i => (Pop.S0145.leaves.getD i dflt).1
theorem r0114_ok : ∀ p ∈ r0114, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0145.sem ix0114_lt

def ix0115 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125]
theorem ix0115_lt : ∀ i ∈ ix0115, i < Pop.S0146.leaves.length := by decide +kernel
def r0115 : List (List ℕ) := ix0115.map fun i => (Pop.S0146.leaves.getD i dflt).1
theorem r0115_ok : ∀ p ∈ r0115, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0146.sem ix0115_lt

def ix0116 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]
theorem ix0116_lt : ∀ i ∈ ix0116, i < Pop.S0147.leaves.length := by decide +kernel
def r0116 : List (List ℕ) := ix0116.map fun i => (Pop.S0147.leaves.getD i dflt).1
theorem r0116_ok : ∀ p ∈ r0116, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0147.sem ix0116_lt

def ix0117 : List ℕ := [24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38]
theorem ix0117_lt : ∀ i ∈ ix0117, i < Pop.S0149.leaves.length := by decide +kernel
def r0117 : List (List ℕ) := ix0117.map fun i => (Pop.S0149.leaves.getD i dflt).1
theorem r0117_ok : ∀ p ∈ r0117, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0149.sem ix0117_lt

def ix0118 : List ℕ := [48, 49, 50, 51, 52, 53, 54]
theorem ix0118_lt : ∀ i ∈ ix0118, i < Pop.S0150.leaves.length := by decide +kernel
def r0118 : List (List ℕ) := ix0118.map fun i => (Pop.S0150.leaves.getD i dflt).1
theorem r0118_ok : ∀ p ∈ r0118, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0150.sem ix0118_lt

def ix0119 : List ℕ := [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52]
theorem ix0119_lt : ∀ i ∈ ix0119, i < Pop.S0151.leaves.length := by decide +kernel
def r0119 : List (List ℕ) := ix0119.map fun i => (Pop.S0151.leaves.getD i dflt).1
theorem r0119_ok : ∀ p ∈ r0119, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0151.sem ix0119_lt

def ix0120 : List ℕ := [25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101]
theorem ix0120_lt : ∀ i ∈ ix0120, i < Pop.S0147.leaves.length := by decide +kernel
def r0120 : List (List ℕ) := ix0120.map fun i => (Pop.S0147.leaves.getD i dflt).1
theorem r0120_ok : ∀ p ∈ r0120, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0147.sem ix0120_lt

def ix0121 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104]
theorem ix0121_lt : ∀ i ∈ ix0121, i < Pop.S0148.leaves.length := by decide +kernel
def r0121 : List (List ℕ) := ix0121.map fun i => (Pop.S0148.leaves.getD i dflt).1
theorem r0121_ok : ∀ p ∈ r0121, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0148.sem ix0121_lt

def ix0122 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105]
theorem ix0122_lt : ∀ i ∈ ix0122, i < Pop.S0149.leaves.length := by decide +kernel
def r0122 : List (List ℕ) := ix0122.map fun i => (Pop.S0149.leaves.getD i dflt).1
theorem r0122_ok : ∀ p ∈ r0122, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0149.sem ix0122_lt

def ix0123 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]
theorem ix0123_lt : ∀ i ∈ ix0123, i < Pop.S0150.leaves.length := by decide +kernel
def r0123 : List (List ℕ) := ix0123.map fun i => (Pop.S0150.leaves.getD i dflt).1
theorem r0123_ok : ∀ p ∈ r0123, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0150.sem ix0123_lt

def ix0124 : List ℕ := [30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
theorem ix0124_lt : ∀ i ∈ ix0124, i < Pop.S0136.leaves.length := by decide +kernel
def r0124 : List (List ℕ) := ix0124.map fun i => (Pop.S0136.leaves.getD i dflt).1
theorem r0124_ok : ∀ p ∈ r0124, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0136.sem ix0124_lt

def ix0125 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94]
theorem ix0125_lt : ∀ i ∈ ix0125, i < Pop.S0137.leaves.length := by decide +kernel
def r0125 : List (List ℕ) := ix0125.map fun i => (Pop.S0137.leaves.getD i dflt).1
theorem r0125_ok : ∀ p ∈ r0125, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0137.sem ix0125_lt

def ix0126 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]
theorem ix0126_lt : ∀ i ∈ ix0126, i < Pop.S0138.leaves.length := by decide +kernel
def r0126 : List (List ℕ) := ix0126.map fun i => (Pop.S0138.leaves.getD i dflt).1
theorem r0126_ok : ∀ p ∈ r0126, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0138.sem ix0126_lt

def ix0127 : List ℕ := [69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96]
theorem ix0127_lt : ∀ i ∈ ix0127, i < Pop.S0140.leaves.length := by decide +kernel
def r0127 : List (List ℕ) := ix0127.map fun i => (Pop.S0140.leaves.getD i dflt).1
theorem r0127_ok : ∀ p ∈ r0127, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0140.sem ix0127_lt

def ix0128 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93]
theorem ix0128_lt : ∀ i ∈ ix0128, i < Pop.S0141.leaves.length := by decide +kernel
def r0128 : List (List ℕ) := ix0128.map fun i => (Pop.S0141.leaves.getD i dflt).1
theorem r0128_ok : ∀ p ∈ r0128, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0141.sem ix0128_lt

def ix0129 : List ℕ := [37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68]
theorem ix0129_lt : ∀ i ∈ ix0129, i < Pop.S0140.leaves.length := by decide +kernel
def r0129 : List (List ℕ) := ix0129.map fun i => (Pop.S0140.leaves.getD i dflt).1
theorem r0129_ok : ∀ p ∈ r0129, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0140.sem ix0129_lt

def ix0130 : List ℕ := [39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85]
theorem ix0130_lt : ∀ i ∈ ix0130, i < Pop.S0143.leaves.length := by decide +kernel
def r0130 : List (List ℕ) := ix0130.map fun i => (Pop.S0143.leaves.getD i dflt).1
theorem r0130_ok : ∀ p ∈ r0130, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0143.sem ix0130_lt

def ix0131 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90]
theorem ix0131_lt : ∀ i ∈ ix0131, i < Pop.S0144.leaves.length := by decide +kernel
def r0131 : List (List ℕ) := ix0131.map fun i => (Pop.S0144.leaves.getD i dflt).1
theorem r0131_ok : ∀ p ∈ r0131, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0144.sem ix0131_lt

def ix0132 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45]
theorem ix0132_lt : ∀ i ∈ ix0132, i < Pop.S0145.leaves.length := by decide +kernel
def r0132 : List (List ℕ) := ix0132.map fun i => (Pop.S0145.leaves.getD i dflt).1
theorem r0132_ok : ∀ p ∈ r0132, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0145.sem ix0132_lt

def ix0133 : List ℕ := [55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93]
theorem ix0133_lt : ∀ i ∈ ix0133, i < Pop.S0150.leaves.length := by decide +kernel
def r0133 : List (List ℕ) := ix0133.map fun i => (Pop.S0150.leaves.getD i dflt).1
theorem r0133_ok : ∀ p ∈ r0133, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0150.sem ix0133_lt

def ix0134 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]
theorem ix0134_lt : ∀ i ∈ ix0134, i < Pop.S0151.leaves.length := by decide +kernel
def r0134 : List (List ℕ) := ix0134.map fun i => (Pop.S0151.leaves.getD i dflt).1
theorem r0134_ok : ∀ p ∈ r0134, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0151.sem ix0134_lt

def ix0135 : List ℕ := [104, 105, 106]
theorem ix0135_lt : ∀ i ∈ ix0135, i < Pop.S0153.leaves.length := by decide +kernel
def r0135 : List (List ℕ) := ix0135.map fun i => (Pop.S0153.leaves.getD i dflt).1
theorem r0135_ok : ∀ p ∈ r0135, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0153.sem ix0135_lt

def ix0136 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91]
theorem ix0136_lt : ∀ i ∈ ix0136, i < Pop.S0154.leaves.length := by decide +kernel
def r0136 : List (List ℕ) := ix0136.map fun i => (Pop.S0154.leaves.getD i dflt).1
theorem r0136_ok : ∀ p ∈ r0136, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0154.sem ix0136_lt

def ix0137 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102]
theorem ix0137_lt : ∀ i ∈ ix0137, i < Pop.S0155.leaves.length := by decide +kernel
def r0137 : List (List ℕ) := ix0137.map fun i => (Pop.S0155.leaves.getD i dflt).1
theorem r0137_ok : ∀ p ∈ r0137, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0155.sem ix0137_lt

def ix0138 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7]
theorem ix0138_lt : ∀ i ∈ ix0138, i < Pop.S0156.leaves.length := by decide +kernel
def r0138 : List (List ℕ) := ix0138.map fun i => (Pop.S0156.leaves.getD i dflt).1
theorem r0138_ok : ∀ p ∈ r0138, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0156.sem ix0138_lt

def ix0139 : List ℕ := [30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45]
theorem ix0139_lt : ∀ i ∈ ix0139, i < Pop.S0159.leaves.length := by decide +kernel
def r0139 : List (List ℕ) := ix0139.map fun i => (Pop.S0159.leaves.getD i dflt).1
theorem r0139_ok : ∀ p ∈ r0139, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0159.sem ix0139_lt

def ix0140 : List ℕ := [11, 12, 13, 14, 15, 16, 17]
theorem ix0140_lt : ∀ i ∈ ix0140, i < Pop.S0161.leaves.length := by decide +kernel
def r0140 : List (List ℕ) := ix0140.map fun i => (Pop.S0161.leaves.getD i dflt).1
theorem r0140_ok : ∀ p ∈ r0140, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0161.sem ix0140_lt

def ix0141 : List ℕ := [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77]
theorem ix0141_lt : ∀ i ∈ ix0141, i < Pop.S0063.leaves.length := by decide +kernel
def r0141 : List (List ℕ) := ix0141.map fun i => (Pop.S0063.leaves.getD i dflt).1
theorem r0141_ok : ∀ p ∈ r0141, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0063.sem ix0141_lt

def ix0142 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89]
theorem ix0142_lt : ∀ i ∈ ix0142, i < Pop.S0064.leaves.length := by decide +kernel
def r0142 : List (List ℕ) := ix0142.map fun i => (Pop.S0064.leaves.getD i dflt).1
theorem r0142_ok : ∀ p ∈ r0142, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0064.sem ix0142_lt

def ix0143 : List ℕ := [0, 1, 2, 3, 4, 5, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87]
theorem ix0143_lt : ∀ i ∈ ix0143, i < Pop.S0065.leaves.length := by decide +kernel
def r0143 : List (List ℕ) := ix0143.map fun i => (Pop.S0065.leaves.getD i dflt).1
theorem r0143_ok : ∀ p ∈ r0143, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0065.sem ix0143_lt

def ix0144 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107]
theorem ix0144_lt : ∀ i ∈ ix0144, i < Pop.S0066.leaves.length := by decide +kernel
def r0144 : List (List ℕ) := ix0144.map fun i => (Pop.S0066.leaves.getD i dflt).1
theorem r0144_ok : ∀ p ∈ r0144, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0066.sem ix0144_lt

def ix0145 : List ℕ := [0, 1, 2, 3]
theorem ix0145_lt : ∀ i ∈ ix0145, i < Pop.S0067.leaves.length := by decide +kernel
def r0145 : List (List ℕ) := ix0145.map fun i => (Pop.S0067.leaves.getD i dflt).1
theorem r0145_ok : ∀ p ∈ r0145, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0067.sem ix0145_lt

def ix0146 : List ℕ := [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91]
theorem ix0146_lt : ∀ i ∈ ix0146, i < Pop.S0069.leaves.length := by decide +kernel
def r0146 : List (List ℕ) := ix0146.map fun i => (Pop.S0069.leaves.getD i dflt).1
theorem r0146_ok : ∀ p ∈ r0146, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0069.sem ix0146_lt

def ix0147 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 112, 113, 114, 115, 116]
theorem ix0147_lt : ∀ i ∈ ix0147, i < Pop.S0070.leaves.length := by decide +kernel
def r0147 : List (List ℕ) := ix0147.map fun i => (Pop.S0070.leaves.getD i dflt).1
theorem r0147_ok : ∀ p ∈ r0147, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0070.sem ix0147_lt

def ix0148 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110]
theorem ix0148_lt : ∀ i ∈ ix0148, i < Pop.S0071.leaves.length := by decide +kernel
def r0148 : List (List ℕ) := ix0148.map fun i => (Pop.S0071.leaves.getD i dflt).1
theorem r0148_ok : ∀ p ∈ r0148, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0071.sem ix0148_lt

def ix0149 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45]
theorem ix0149_lt : ∀ i ∈ ix0149, i < Pop.S0072.leaves.length := by decide +kernel
def r0149 : List (List ℕ) := ix0149.map fun i => (Pop.S0072.leaves.getD i dflt).1
theorem r0149_ok : ∀ p ∈ r0149, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0072.sem ix0149_lt

def ix0150 : List ℕ := [82, 83, 84, 85, 86, 87, 88, 89, 90, 91]
theorem ix0150_lt : ∀ i ∈ ix0150, i < Pop.S0075.leaves.length := by decide +kernel
def r0150 : List (List ℕ) := ix0150.map fun i => (Pop.S0075.leaves.getD i dflt).1
theorem r0150_ok : ∀ p ∈ r0150, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0075.sem ix0150_lt

def ix0151 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91]
theorem ix0151_lt : ∀ i ∈ ix0151, i < Pop.S0076.leaves.length := by decide +kernel
def r0151 : List (List ℕ) := ix0151.map fun i => (Pop.S0076.leaves.getD i dflt).1
theorem r0151_ok : ∀ p ∈ r0151, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0076.sem ix0151_lt

def ix0152 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 102, 103, 104, 105, 106, 107]
theorem ix0152_lt : ∀ i ∈ ix0152, i < Pop.S0077.leaves.length := by decide +kernel
def r0152 : List (List ℕ) := ix0152.map fun i => (Pop.S0077.leaves.getD i dflt).1
theorem r0152_ok : ∀ p ∈ r0152, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0077.sem ix0152_lt

def ix0153 : List ℕ := [89, 90, 91, 92, 93, 94, 95, 96]
theorem ix0153_lt : ∀ i ∈ ix0153, i < Pop.S0079.leaves.length := by decide +kernel
def r0153 : List (List ℕ) := ix0153.map fun i => (Pop.S0079.leaves.getD i dflt).1
theorem r0153_ok : ∀ p ∈ r0153, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0079.sem ix0153_lt

def ix0154 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52]
theorem ix0154_lt : ∀ i ∈ ix0154, i < Pop.S0080.leaves.length := by decide +kernel
def r0154 : List (List ℕ) := ix0154.map fun i => (Pop.S0080.leaves.getD i dflt).1
theorem r0154_ok : ∀ p ∈ r0154, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0080.sem ix0154_lt

def ix0155 : List ℕ := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126]
theorem ix0155_lt : ∀ i ∈ ix0155, i < Pop.S0074.leaves.length := by decide +kernel
def r0155 : List (List ℕ) := ix0155.map fun i => (Pop.S0074.leaves.getD i dflt).1
theorem r0155_ok : ∀ p ∈ r0155, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0074.sem ix0155_lt

def ix0156 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81]
theorem ix0156_lt : ∀ i ∈ ix0156, i < Pop.S0075.leaves.length := by decide +kernel
def r0156 : List (List ℕ) := ix0156.map fun i => (Pop.S0075.leaves.getD i dflt).1
theorem r0156_ok : ∀ p ∈ r0156, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0075.sem ix0156_lt

def ix0157 : List ℕ := [96, 97, 98, 99, 100, 101]
theorem ix0157_lt : ∀ i ∈ ix0157, i < Pop.S0077.leaves.length := by decide +kernel
def r0157 : List (List ℕ) := ix0157.map fun i => (Pop.S0077.leaves.getD i dflt).1
theorem r0157_ok : ∀ p ∈ r0157, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0077.sem ix0157_lt

def ix0158 : List ℕ := [0, 1, 2, 3]
theorem ix0158_lt : ∀ i ∈ ix0158, i < Pop.S0078.leaves.length := by decide +kernel
def r0158 : List (List ℕ) := ix0158.map fun i => (Pop.S0078.leaves.getD i dflt).1
theorem r0158_ok : ∀ p ∈ r0158, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0078.sem ix0158_lt

def ix0159 : List ℕ := [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88]
theorem ix0159_lt : ∀ i ∈ ix0159, i < Pop.S0079.leaves.length := by decide +kernel
def r0159 : List (List ℕ) := ix0159.map fun i => (Pop.S0079.leaves.getD i dflt).1
theorem r0159_ok : ∀ p ∈ r0159, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0079.sem ix0159_lt

def ix0160 : List ℕ := [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]
theorem ix0160_lt : ∀ i ∈ ix0160, i < Pop.S0085.leaves.length := by decide +kernel
def r0160 : List (List ℕ) := ix0160.map fun i => (Pop.S0085.leaves.getD i dflt).1
theorem r0160_ok : ∀ p ∈ r0160, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0085.sem ix0160_lt

def ix0161 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98]
theorem ix0161_lt : ∀ i ∈ ix0161, i < Pop.S0086.leaves.length := by decide +kernel
def r0161 : List (List ℕ) := ix0161.map fun i => (Pop.S0086.leaves.getD i dflt).1
theorem r0161_ok : ∀ p ∈ r0161, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0086.sem ix0161_lt

def ix0162 : List ℕ := [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58]
theorem ix0162_lt : ∀ i ∈ ix0162, i < Pop.S0088.leaves.length := by decide +kernel
def r0162 : List (List ℕ) := ix0162.map fun i => (Pop.S0088.leaves.getD i dflt).1
theorem r0162_ok : ∀ p ∈ r0162, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0088.sem ix0162_lt

def ix0163 : List ℕ := [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87]
theorem ix0163_lt : ∀ i ∈ ix0163, i < Pop.S0078.leaves.length := by decide +kernel
def r0163 : List (List ℕ) := ix0163.map fun i => (Pop.S0078.leaves.getD i dflt).1
theorem r0163_ok : ∀ p ∈ r0163, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0078.sem ix0163_lt

def ix0164 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]
theorem ix0164_lt : ∀ i ∈ ix0164, i < Pop.S0079.leaves.length := by decide +kernel
def r0164 : List (List ℕ) := ix0164.map fun i => (Pop.S0079.leaves.getD i dflt).1
theorem r0164_ok : ∀ p ∈ r0164, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0079.sem ix0164_lt

def ix0165 : List ℕ := [53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84]
theorem ix0165_lt : ∀ i ∈ ix0165, i < Pop.S0080.leaves.length := by decide +kernel
def r0165 : List (List ℕ) := ix0165.map fun i => (Pop.S0080.leaves.getD i dflt).1
theorem r0165_ok : ∀ p ∈ r0165, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0080.sem ix0165_lt

def ix0166 : List ℕ := [34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108]
theorem ix0166_lt : ∀ i ∈ ix0166, i < Pop.S0082.leaves.length := by decide +kernel
def r0166 : List (List ℕ) := ix0166.map fun i => (Pop.S0082.leaves.getD i dflt).1
theorem r0166_ok : ∀ p ∈ r0166, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0082.sem ix0166_lt

def ix0167 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107]
theorem ix0167_lt : ∀ i ∈ ix0167, i < Pop.S0083.leaves.length := by decide +kernel
def r0167 : List (List ℕ) := ix0167.map fun i => (Pop.S0083.leaves.getD i dflt).1
theorem r0167_ok : ∀ p ∈ r0167, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0083.sem ix0167_lt

def ix0168 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101]
theorem ix0168_lt : ∀ i ∈ ix0168, i < Pop.S0084.leaves.length := by decide +kernel
def r0168 : List (List ℕ) := ix0168.map fun i => (Pop.S0084.leaves.getD i dflt).1
theorem r0168_ok : ∀ p ∈ r0168, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0084.sem ix0168_lt

def ix0169 : List ℕ := [0, 1, 2, 3, 4]
theorem ix0169_lt : ∀ i ∈ ix0169, i < Pop.S0085.leaves.length := by decide +kernel
def r0169 : List (List ℕ) := ix0169.map fun i => (Pop.S0085.leaves.getD i dflt).1
theorem r0169_ok : ∀ p ∈ r0169, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0085.sem ix0169_lt

def ix0170 : List ℕ := [90, 91]
theorem ix0170_lt : ∀ i ∈ ix0170, i < Pop.S0088.leaves.length := by decide +kernel
def r0170 : List (List ℕ) := ix0170.map fun i => (Pop.S0088.leaves.getD i dflt).1
theorem r0170_ok : ∀ p ∈ r0170, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0088.sem ix0170_lt

def ix0171 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94]
theorem ix0171_lt : ∀ i ∈ ix0171, i < Pop.S0089.leaves.length := by decide +kernel
def r0171 : List (List ℕ) := ix0171.map fun i => (Pop.S0089.leaves.getD i dflt).1
theorem r0171_ok : ∀ p ∈ r0171, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0089.sem ix0171_lt

def ix0172 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101]
theorem ix0172_lt : ∀ i ∈ ix0172, i < Pop.S0090.leaves.length := by decide +kernel
def r0172 : List (List ℕ) := ix0172.map fun i => (Pop.S0090.leaves.getD i dflt).1
theorem r0172_ok : ∀ p ∈ r0172, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0090.sem ix0172_lt

def ix0173 : List ℕ := [85, 86, 87, 88, 89, 90, 91, 92, 93, 94]
theorem ix0173_lt : ∀ i ∈ ix0173, i < Pop.S0080.leaves.length := by decide +kernel
def r0173 : List (List ℕ) := ix0173.map fun i => (Pop.S0080.leaves.getD i dflt).1
theorem r0173_ok : ∀ p ∈ r0173, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0080.sem ix0173_lt

def ix0174 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91]
theorem ix0174_lt : ∀ i ∈ ix0174, i < Pop.S0081.leaves.length := by decide +kernel
def r0174 : List (List ℕ) := ix0174.map fun i => (Pop.S0081.leaves.getD i dflt).1
theorem r0174_ok : ∀ p ∈ r0174, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0081.sem ix0174_lt

def ix0175 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]
theorem ix0175_lt : ∀ i ∈ ix0175, i < Pop.S0082.leaves.length := by decide +kernel
def r0175 : List (List ℕ) := ix0175.map fun i => (Pop.S0082.leaves.getD i dflt).1
theorem r0175_ok : ∀ p ∈ r0175, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0082.sem ix0175_lt

def ix0176 : List ℕ := [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71]
theorem ix0176_lt : ∀ i ∈ ix0176, i < Pop.S0084.leaves.length := by decide +kernel
def r0176 : List (List ℕ) := ix0176.map fun i => (Pop.S0084.leaves.getD i dflt).1
theorem r0176_ok : ∀ p ∈ r0176, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0084.sem ix0176_lt

def ix0177 : List ℕ := [68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91]
theorem ix0177_lt : ∀ i ∈ ix0177, i < Pop.S0087.leaves.length := by decide +kernel
def r0177 : List (List ℕ) := ix0177.map fun i => (Pop.S0087.leaves.getD i dflt).1
theorem r0177_ok : ∀ p ∈ r0177, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0087.sem ix0177_lt

def ix0178 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]
theorem ix0178_lt : ∀ i ∈ ix0178, i < Pop.S0088.leaves.length := by decide +kernel
def r0178 : List (List ℕ) := ix0178.map fun i => (Pop.S0088.leaves.getD i dflt).1
theorem r0178_ok : ∀ p ∈ r0178, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0088.sem ix0178_lt

def ix0179 : List ℕ := [88, 89, 90, 91, 92, 93, 94, 95]
theorem ix0179_lt : ∀ i ∈ ix0179, i < Pop.S0093.leaves.length := by decide +kernel
def r0179 : List (List ℕ) := ix0179.map fun i => (Pop.S0093.leaves.getD i dflt).1
theorem r0179_ok : ∀ p ∈ r0179, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0093.sem ix0179_lt

def ix0180 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99]
theorem ix0180_lt : ∀ i ∈ ix0180, i < Pop.S0094.leaves.length := by decide +kernel
def r0180 : List (List ℕ) := ix0180.map fun i => (Pop.S0094.leaves.getD i dflt).1
theorem r0180_ok : ∀ p ∈ r0180, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0094.sem ix0180_lt

def ix0181 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]
theorem ix0181_lt : ∀ i ∈ ix0181, i < Pop.S0095.leaves.length := by decide +kernel
def r0181 : List (List ℕ) := ix0181.map fun i => (Pop.S0095.leaves.getD i dflt).1
theorem r0181_ok : ∀ p ∈ r0181, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0095.sem ix0181_lt

def ix0182 : List ℕ := [76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107]
theorem ix0182_lt : ∀ i ∈ ix0182, i < Pop.S0096.leaves.length := by decide +kernel
def r0182 : List (List ℕ) := ix0182.map fun i => (Pop.S0096.leaves.getD i dflt).1
theorem r0182_ok : ∀ p ∈ r0182, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0096.sem ix0182_lt

def ix0183 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98]
theorem ix0183_lt : ∀ i ∈ ix0183, i < Pop.S0097.leaves.length := by decide +kernel
def r0183 : List (List ℕ) := ix0183.map fun i => (Pop.S0097.leaves.getD i dflt).1
theorem r0183_ok : ∀ p ∈ r0183, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0097.sem ix0183_lt

def ix0184 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73]
theorem ix0184_lt : ∀ i ∈ ix0184, i < Pop.S0098.leaves.length := by decide +kernel
def r0184 : List (List ℕ) := ix0184.map fun i => (Pop.S0098.leaves.getD i dflt).1
theorem r0184_ok : ∀ p ∈ r0184, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0098.sem ix0184_lt

def ix0185 : List ℕ := [31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113]
theorem ix0185_lt : ∀ i ∈ ix0185, i < Pop.S0100.leaves.length := by decide +kernel
def r0185 : List (List ℕ) := ix0185.map fun i => (Pop.S0100.leaves.getD i dflt).1
theorem r0185_ok : ∀ p ∈ r0185, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0100.sem ix0185_lt

def ix0186 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]
theorem ix0186_lt : ∀ i ∈ ix0186, i < Pop.S0101.leaves.length := by decide +kernel
def r0186 : List (List ℕ) := ix0186.map fun i => (Pop.S0101.leaves.getD i dflt).1
theorem r0186_ok : ∀ p ∈ r0186, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0101.sem ix0186_lt

def ix0187 : List ℕ := [58, 59, 60, 61, 62, 63]
theorem ix0187_lt : ∀ i ∈ ix0187, i < Pop.S0102.leaves.length := by decide +kernel
def r0187 : List (List ℕ) := ix0187.map fun i => (Pop.S0102.leaves.getD i dflt).1
theorem r0187_ok : ∀ p ∈ r0187, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0102.sem ix0187_lt

def ix0188 : List ℕ := [47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
theorem ix0188_lt : ∀ i ∈ ix0188, i < Pop.S0142.leaves.length := by decide +kernel
def r0188 : List (List ℕ) := ix0188.map fun i => (Pop.S0142.leaves.getD i dflt).1
theorem r0188_ok : ∀ p ∈ r0188, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0142.sem ix0188_lt

def ix0189 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38]
theorem ix0189_lt : ∀ i ∈ ix0189, i < Pop.S0143.leaves.length := by decide +kernel
def r0189 : List (List ℕ) := ix0189.map fun i => (Pop.S0143.leaves.getD i dflt).1
theorem r0189_ok : ∀ p ∈ r0189, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0143.sem ix0189_lt

def ix0190 : List ℕ := [53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108]
theorem ix0190_lt : ∀ i ∈ ix0190, i < Pop.S0151.leaves.length := by decide +kernel
def r0190 : List (List ℕ) := ix0190.map fun i => (Pop.S0151.leaves.getD i dflt).1
theorem r0190_ok : ∀ p ∈ r0190, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0151.sem ix0190_lt

def ix0191 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102]
theorem ix0191_lt : ∀ i ∈ ix0191, i < Pop.S0152.leaves.length := by decide +kernel
def r0191 : List (List ℕ) := ix0191.map fun i => (Pop.S0152.leaves.getD i dflt).1
theorem r0191_ok : ∀ p ∈ r0191, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0152.sem ix0191_lt

def ix0192 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38]
theorem ix0192_lt : ∀ i ∈ ix0192, i < Pop.S0153.leaves.length := by decide +kernel
def r0192 : List (List ℕ) := ix0192.map fun i => (Pop.S0153.leaves.getD i dflt).1
theorem r0192_ok : ∀ p ∈ r0192, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0153.sem ix0192_lt

def ix0193 : List ℕ := [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84]
theorem ix0193_lt : ∀ i ∈ ix0193, i < Pop.S0156.leaves.length := by decide +kernel
def r0193 : List (List ℕ) := ix0193.map fun i => (Pop.S0156.leaves.getD i dflt).1
theorem r0193_ok : ∀ p ∈ r0193, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0156.sem ix0193_lt

def ix0194 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98]
theorem ix0194_lt : ∀ i ∈ ix0194, i < Pop.S0157.leaves.length := by decide +kernel
def r0194 : List (List ℕ) := ix0194.map fun i => (Pop.S0157.leaves.getD i dflt).1
theorem r0194_ok : ∀ p ∈ r0194, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0157.sem ix0194_lt

def ix0195 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]
theorem ix0195_lt : ∀ i ∈ ix0195, i < Pop.S0158.leaves.length := by decide +kernel
def r0195 : List (List ℕ) := ix0195.map fun i => (Pop.S0158.leaves.getD i dflt).1
theorem r0195_ok : ∀ p ∈ r0195, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0158.sem ix0195_lt

def ix0196 : List ℕ := [46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60]
theorem ix0196_lt : ∀ i ∈ ix0196, i < Pop.S0159.leaves.length := by decide +kernel
def r0196 : List (List ℕ) := ix0196.map fun i => (Pop.S0159.leaves.getD i dflt).1
theorem r0196_ok : ∀ p ∈ r0196, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0159.sem ix0196_lt

def ix0197 : List ℕ := [26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89]
theorem ix0197_lt : ∀ i ∈ ix0197, i < Pop.S0161.leaves.length := by decide +kernel
def r0197 : List (List ℕ) := ix0197.map fun i => (Pop.S0161.leaves.getD i dflt).1
theorem r0197_ok : ∀ p ∈ r0197, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0161.sem ix0197_lt

def ix0198 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]
theorem ix0198_lt : ∀ i ∈ ix0198, i < Pop.S0162.leaves.length := by decide +kernel
def r0198 : List (List ℕ) := ix0198.map fun i => (Pop.S0162.leaves.getD i dflt).1
theorem r0198_ok : ∀ p ∈ r0198, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0162.sem ix0198_lt

def ix0199 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67]
theorem ix0199_lt : ∀ i ∈ ix0199, i < Pop.S0087.leaves.length := by decide +kernel
def r0199 : List (List ℕ) := ix0199.map fun i => (Pop.S0087.leaves.getD i dflt).1
theorem r0199_ok : ∀ p ∈ r0199, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0087.sem ix0199_lt

def ix0200 : List ℕ := [60, 59, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89]
theorem ix0200_lt : ∀ i ∈ ix0200, i < Pop.S0088.leaves.length := by decide +kernel
def r0200 : List (List ℕ) := ix0200.map fun i => (Pop.S0088.leaves.getD i dflt).1
theorem r0200_ok : ∀ p ∈ r0200, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0088.sem ix0200_lt

def ix0201 : List ℕ := [102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118]
theorem ix0201_lt : ∀ i ∈ ix0201, i < Pop.S0090.leaves.length := by decide +kernel
def r0201 : List (List ℕ) := ix0201.map fun i => (Pop.S0090.leaves.getD i dflt).1
theorem r0201_ok : ∀ p ∈ r0201, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0090.sem ix0201_lt

def ix0202 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102]
theorem ix0202_lt : ∀ i ∈ ix0202, i < Pop.S0091.leaves.length := by decide +kernel
def r0202 : List (List ℕ) := ix0202.map fun i => (Pop.S0091.leaves.getD i dflt).1
theorem r0202_ok : ∀ p ∈ r0202, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0091.sem ix0202_lt

def ix0203 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]
theorem ix0203_lt : ∀ i ∈ ix0203, i < Pop.S0092.leaves.length := by decide +kernel
def r0203 : List (List ℕ) := ix0203.map fun i => (Pop.S0092.leaves.getD i dflt).1
theorem r0203_ok : ∀ p ∈ r0203, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0092.sem ix0203_lt

def ix0204 : List ℕ := [59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83]
theorem ix0204_lt : ∀ i ∈ ix0204, i < Pop.S0093.leaves.length := by decide +kernel
def r0204 : List (List ℕ) := ix0204.map fun i => (Pop.S0093.leaves.getD i dflt).1
theorem r0204_ok : ∀ p ∈ r0204, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0093.sem ix0204_lt

def ix0205 : List ℕ := [80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93]
theorem ix0205_lt : ∀ i ∈ ix0205, i < Pop.S0095.leaves.length := by decide +kernel
def r0205 : List (List ℕ) := ix0205.map fun i => (Pop.S0095.leaves.getD i dflt).1
theorem r0205_ok : ∀ p ∈ r0205, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0095.sem ix0205_lt

def ix0206 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
theorem ix0206_lt : ∀ i ∈ ix0206, i < Pop.S0096.leaves.length := by decide +kernel
def r0206 : List (List ℕ) := ix0206.map fun i => (Pop.S0096.leaves.getD i dflt).1
theorem r0206_ok : ∀ p ∈ r0206, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0096.sem ix0206_lt

def ix0207 : List ℕ := [74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99]
theorem ix0207_lt : ∀ i ∈ ix0207, i < Pop.S0098.leaves.length := by decide +kernel
def r0207 : List (List ℕ) := ix0207.map fun i => (Pop.S0098.leaves.getD i dflt).1
theorem r0207_ok : ∀ p ∈ r0207, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0098.sem ix0207_lt

def ix0208 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93]
theorem ix0208_lt : ∀ i ∈ ix0208, i < Pop.S0099.leaves.length := by decide +kernel
def r0208 : List (List ℕ) := ix0208.map fun i => (Pop.S0099.leaves.getD i dflt).1
theorem r0208_ok : ∀ p ∈ r0208, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0099.sem ix0208_lt

def ix0209 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]
theorem ix0209_lt : ∀ i ∈ ix0209, i < Pop.S0100.leaves.length := by decide +kernel
def r0209 : List (List ℕ) := ix0209.map fun i => (Pop.S0100.leaves.getD i dflt).1
theorem r0209_ok : ∀ p ∈ r0209, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0100.sem ix0209_lt

def ix0210 : List ℕ := [27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
theorem ix0210_lt : ∀ i ∈ ix0210, i < Pop.S0092.leaves.length := by decide +kernel
def r0210 : List (List ℕ) := ix0210.map fun i => (Pop.S0092.leaves.getD i dflt).1
theorem r0210_ok : ∀ p ∈ r0210, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0092.sem ix0210_lt

def ix0211 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 84, 85, 86, 87]
theorem ix0211_lt : ∀ i ∈ ix0211, i < Pop.S0093.leaves.length := by decide +kernel
def r0211 : List (List ℕ) := ix0211.map fun i => (Pop.S0093.leaves.getD i dflt).1
theorem r0211_ok : ∀ p ∈ r0211, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0093.sem ix0211_lt

def ix0212 : List ℕ := [24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75]
theorem ix0212_lt : ∀ i ∈ ix0212, i < Pop.S0096.leaves.length := by decide +kernel
def r0212 : List (List ℕ) := ix0212.map fun i => (Pop.S0096.leaves.getD i dflt).1
theorem r0212_ok : ∀ p ∈ r0212, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0096.sem ix0212_lt

def ix0213 : List ℕ := [25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90]
theorem ix0213_lt : ∀ i ∈ ix0213, i < Pop.S0101.leaves.length := by decide +kernel
def r0213 : List (List ℕ) := ix0213.map fun i => (Pop.S0101.leaves.getD i dflt).1
theorem r0213_ok : ∀ p ∈ r0213, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0101.sem ix0213_lt

def ix0214 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57]
theorem ix0214_lt : ∀ i ∈ ix0214, i < Pop.S0102.leaves.length := by decide +kernel
def r0214 : List (List ℕ) := ix0214.map fun i => (Pop.S0102.leaves.getD i dflt).1
theorem r0214_ok : ∀ p ∈ r0214, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0102.sem ix0214_lt

def ix0215 : List ℕ := [87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101]
theorem ix0215_lt : ∀ i ∈ ix0215, i < Pop.S0107.leaves.length := by decide +kernel
def r0215 : List (List ℕ) := ix0215.map fun i => (Pop.S0107.leaves.getD i dflt).1
theorem r0215_ok : ∀ p ∈ r0215, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0107.sem ix0215_lt

def ix0216 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117]
theorem ix0216_lt : ∀ i ∈ ix0216, i < Pop.S0108.leaves.length := by decide +kernel
def r0216 : List (List ℕ) := ix0216.map fun i => (Pop.S0108.leaves.getD i dflt).1
theorem r0216_ok : ∀ p ∈ r0216, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0108.sem ix0216_lt

def ix0217 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43]
theorem ix0217_lt : ∀ i ∈ ix0217, i < Pop.S0109.leaves.length := by decide +kernel
def r0217 : List (List ℕ) := ix0217.map fun i => (Pop.S0109.leaves.getD i dflt).1
theorem r0217_ok : ∀ p ∈ r0217, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0109.sem ix0217_lt

def ix0218 : List ℕ := [49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84]
theorem ix0218_lt : ∀ i ∈ ix0218, i < Pop.S0113.leaves.length := by decide +kernel
def r0218 : List (List ℕ) := ix0218.map fun i => (Pop.S0113.leaves.getD i dflt).1
theorem r0218_ok : ∀ p ∈ r0218, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0113.sem ix0218_lt

def ix0219 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96]
theorem ix0219_lt : ∀ i ∈ ix0219, i < Pop.S0114.leaves.length := by decide +kernel
def r0219 : List (List ℕ) := ix0219.map fun i => (Pop.S0114.leaves.getD i dflt).1
theorem r0219_ok : ∀ p ∈ r0219, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0114.sem ix0219_lt

def ix0220 : List ℕ := [43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93]
theorem ix0220_lt : ∀ i ∈ ix0220, i < Pop.S0115.leaves.length := by decide +kernel
def r0220 : List (List ℕ) := ix0220.map fun i => (Pop.S0115.leaves.getD i dflt).1
theorem r0220_ok : ∀ p ∈ r0220, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0115.sem ix0220_lt

def ix0221 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98]
theorem ix0221_lt : ∀ i ∈ ix0221, i < Pop.S0116.leaves.length := by decide +kernel
def r0221 : List (List ℕ) := ix0221.map fun i => (Pop.S0116.leaves.getD i dflt).1
theorem r0221_ok : ∀ p ∈ r0221, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0116.sem ix0221_lt

def ix0222 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109]
theorem ix0222_lt : ∀ i ∈ ix0222, i < Pop.S0117.leaves.length := by decide +kernel
def r0222 : List (List ℕ) := ix0222.map fun i => (Pop.S0117.leaves.getD i dflt).1
theorem r0222_ok : ∀ p ∈ r0222, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0117.sem ix0222_lt

def ix0223 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92]
theorem ix0223_lt : ∀ i ∈ ix0223, i < Pop.S0118.leaves.length := by decide +kernel
def r0223 : List (List ℕ) := ix0223.map fun i => (Pop.S0118.leaves.getD i dflt).1
theorem r0223_ok : ∀ p ∈ r0223, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0118.sem ix0223_lt

def ix0224 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50]
theorem ix0224_lt : ∀ i ∈ ix0224, i < Pop.S0119.leaves.length := by decide +kernel
def r0224 : List (List ℕ) := ix0224.map fun i => (Pop.S0119.leaves.getD i dflt).1
theorem r0224_ok : ∀ p ∈ r0224, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0119.sem ix0224_lt

def ix0225 : List ℕ := [97]
theorem ix0225_lt : ∀ i ∈ ix0225, i < Pop.S0121.leaves.length := by decide +kernel
def r0225 : List (List ℕ) := ix0225.map fun i => (Pop.S0121.leaves.getD i dflt).1
theorem r0225_ok : ∀ p ∈ r0225, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0121.sem ix0225_lt

def ix0226 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]
theorem ix0226_lt : ∀ i ∈ ix0226, i < Pop.S0122.leaves.length := by decide +kernel
def r0226 : List (List ℕ) := ix0226.map fun i => (Pop.S0122.leaves.getD i dflt).1
theorem r0226_ok : ∀ p ∈ r0226, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0122.sem ix0226_lt

def ix0227 : List ℕ := [97, 98, 99, 100, 101, 102]
theorem ix0227_lt : ∀ i ∈ ix0227, i < Pop.S0127.leaves.length := by decide +kernel
def r0227 : List (List ℕ) := ix0227.map fun i => (Pop.S0127.leaves.getD i dflt).1
theorem r0227_ok : ∀ p ∈ r0227, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0127.sem ix0227_lt

def ix0228 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57]
theorem ix0228_lt : ∀ i ∈ ix0228, i < Pop.S0128.leaves.length := by decide +kernel
def r0228 : List (List ℕ) := ix0228.map fun i => (Pop.S0128.leaves.getD i dflt).1
theorem r0228_ok : ∀ p ∈ r0228, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0128.sem ix0228_lt

def ix0229 : List ℕ := [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87]
theorem ix0229_lt : ∀ i ∈ ix0229, i < Pop.S0131.leaves.length := by decide +kernel
def r0229 : List (List ℕ) := ix0229.map fun i => (Pop.S0131.leaves.getD i dflt).1
theorem r0229_ok : ∀ p ∈ r0229, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0131.sem ix0229_lt

def ix0230 : List ℕ := [67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87]
theorem ix0230_lt : ∀ i ∈ ix0230, i < Pop.S0105.leaves.length := by decide +kernel
def r0230 : List (List ℕ) := ix0230.map fun i => (Pop.S0105.leaves.getD i dflt).1
theorem r0230_ok : ∀ p ∈ r0230, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0105.sem ix0230_lt

def ix0231 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100]
theorem ix0231_lt : ∀ i ∈ ix0231, i < Pop.S0106.leaves.length := by decide +kernel
def r0231 : List (List ℕ) := ix0231.map fun i => (Pop.S0106.leaves.getD i dflt).1
theorem r0231_ok : ∀ p ∈ r0231, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0106.sem ix0231_lt

def ix0232 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86]
theorem ix0232_lt : ∀ i ∈ ix0232, i < Pop.S0107.leaves.length := by decide +kernel
def r0232 : List (List ℕ) := ix0232.map fun i => (Pop.S0107.leaves.getD i dflt).1
theorem r0232_ok : ∀ p ∈ r0232, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0107.sem ix0232_lt

def ix0233 : List ℕ := [44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71]
theorem ix0233_lt : ∀ i ∈ ix0233, i < Pop.S0109.leaves.length := by decide +kernel
def r0233 : List (List ℕ) := ix0233.map fun i => (Pop.S0109.leaves.getD i dflt).1
theorem r0233_ok : ∀ p ∈ r0233, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0109.sem ix0233_lt

def ix0234 : List ℕ := [35, 36, 37, 38, 39]
theorem ix0234_lt : ∀ i ∈ ix0234, i < Pop.S0115.leaves.length := by decide +kernel
def r0234 : List (List ℕ) := ix0234.map fun i => (Pop.S0115.leaves.getD i dflt).1
theorem r0234_ok : ∀ p ∈ r0234, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0115.sem ix0234_lt

def ix0235 : List ℕ := [51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97]
theorem ix0235_lt : ∀ i ∈ ix0235, i < Pop.S0119.leaves.length := by decide +kernel
def r0235 : List (List ℕ) := ix0235.map fun i => (Pop.S0119.leaves.getD i dflt).1
theorem r0235_ok : ∀ p ∈ r0235, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0119.sem ix0235_lt

def ix0236 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99]
theorem ix0236_lt : ∀ i ∈ ix0236, i < Pop.S0120.leaves.length := by decide +kernel
def r0236 : List (List ℕ) := ix0236.map fun i => (Pop.S0120.leaves.getD i dflt).1
theorem r0236_ok : ∀ p ∈ r0236, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0120.sem ix0236_lt

def ix0237 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96]
theorem ix0237_lt : ∀ i ∈ ix0237, i < Pop.S0121.leaves.length := by decide +kernel
def r0237 : List (List ℕ) := ix0237.map fun i => (Pop.S0121.leaves.getD i dflt).1
theorem r0237_ok : ∀ p ∈ r0237, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0121.sem ix0237_lt

def ix0238 : List ℕ := [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
theorem ix0238_lt : ∀ i ∈ ix0238, i < Pop.S0123.leaves.length := by decide +kernel
def r0238 : List (List ℕ) := ix0238.map fun i => (Pop.S0123.leaves.getD i dflt).1
theorem r0238_ok : ∀ p ∈ r0238, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0123.sem ix0238_lt

def ix0239 : List ℕ := [0, 1, 2, 3, 4, 5]
theorem ix0239_lt : ∀ i ∈ ix0239, i < Pop.S0124.leaves.length := by decide +kernel
def r0239 : List (List ℕ) := ix0239.map fun i => (Pop.S0124.leaves.getD i dflt).1
theorem r0239_ok : ∀ p ∈ r0239, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0124.sem ix0239_lt

def ix0240 : List ℕ := [43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99]
theorem ix0240_lt : ∀ i ∈ ix0240, i < Pop.S0126.leaves.length := by decide +kernel
def r0240 : List (List ℕ) := ix0240.map fun i => (Pop.S0126.leaves.getD i dflt).1
theorem r0240_ok : ∀ p ∈ r0240, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0126.sem ix0240_lt

def ix0241 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96]
theorem ix0241_lt : ∀ i ∈ ix0241, i < Pop.S0127.leaves.length := by decide +kernel
def r0241 : List (List ℕ) := ix0241.map fun i => (Pop.S0127.leaves.getD i dflt).1
theorem r0241_ok : ∀ p ∈ r0241, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0127.sem ix0241_lt

def ix0242 : List ℕ := [28, 29, 30, 31]
theorem ix0242_lt : ∀ i ∈ ix0242, i < Pop.S0125.leaves.length := by decide +kernel
def r0242 : List (List ℕ) := ix0242.map fun i => (Pop.S0125.leaves.getD i dflt).1
theorem r0242_ok : ∀ p ∈ r0242, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0125.sem ix0242_lt

def ix0243 : List ℕ := [58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110]
theorem ix0243_lt : ∀ i ∈ ix0243, i < Pop.S0128.leaves.length := by decide +kernel
def r0243 : List (List ℕ) := ix0243.map fun i => (Pop.S0128.leaves.getD i dflt).1
theorem r0243_ok : ∀ p ∈ r0243, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0128.sem ix0243_lt

def ix0244 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107]
theorem ix0244_lt : ∀ i ∈ ix0244, i < Pop.S0129.leaves.length := by decide +kernel
def r0244 : List (List ℕ) := ix0244.map fun i => (Pop.S0129.leaves.getD i dflt).1
theorem r0244_ok : ∀ p ∈ r0244, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0129.sem ix0244_lt

def ix0245 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66]
theorem ix0245_lt : ∀ i ∈ ix0245, i < Pop.S0130.leaves.length := by decide +kernel
def r0245 : List (List ℕ) := ix0245.map fun i => (Pop.S0130.leaves.getD i dflt).1
theorem r0245_ok : ∀ p ∈ r0245, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0130.sem ix0245_lt

def ix0246 : List ℕ := [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]
theorem ix0246_lt : ∀ i ∈ ix0246, i < Pop.S0131.leaves.length := by decide +kernel
def r0246 : List (List ℕ) := ix0246.map fun i => (Pop.S0131.leaves.getD i dflt).1
theorem r0246_ok : ∀ p ∈ r0246, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0131.sem ix0246_lt

def ix0247 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62]
theorem ix0247_lt : ∀ i ∈ ix0247, i < Pop.S0132.leaves.length := by decide +kernel
def r0247 : List (List ℕ) := ix0247.map fun i => (Pop.S0132.leaves.getD i dflt).1
theorem r0247_ok : ∀ p ∈ r0247, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0132.sem ix0247_lt

def ix0248 : List ℕ := [83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114]
theorem ix0248_lt : ∀ i ∈ ix0248, i < Pop.S0133.leaves.length := by decide +kernel
def r0248 : List (List ℕ) := ix0248.map fun i => (Pop.S0133.leaves.getD i dflt).1
theorem r0248_ok : ∀ p ∈ r0248, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0133.sem ix0248_lt

def ix0249 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94]
theorem ix0249_lt : ∀ i ∈ ix0249, i < Pop.S0134.leaves.length := by decide +kernel
def r0249 : List (List ℕ) := ix0249.map fun i => (Pop.S0134.leaves.getD i dflt).1
theorem r0249_ok : ∀ p ∈ r0249, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0134.sem ix0249_lt

def ix0250 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114]
theorem ix0250_lt : ∀ i ∈ ix0250, i < Pop.S0135.leaves.length := by decide +kernel
def r0250 : List (List ℕ) := ix0250.map fun i => (Pop.S0135.leaves.getD i dflt).1
theorem r0250_ok : ∀ p ∈ r0250, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0135.sem ix0250_lt

def ix0251 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]
theorem ix0251_lt : ∀ i ∈ ix0251, i < Pop.S0136.leaves.length := by decide +kernel
def r0251 : List (List ℕ) := ix0251.map fun i => (Pop.S0136.leaves.getD i dflt).1
theorem r0251_ok : ∀ p ∈ r0251, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0136.sem ix0251_lt

def ix0252 : List ℕ := [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61]
theorem ix0252_lt : ∀ i ∈ ix0252, i < Pop.S0138.leaves.length := by decide +kernel
def r0252 : List (List ℕ) := ix0252.map fun i => (Pop.S0138.leaves.getD i dflt).1
theorem r0252_ok : ∀ p ∈ r0252, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0138.sem ix0252_lt

def ix0253 : List ℕ := [97, 98, 99, 100, 101, 102]
theorem ix0253_lt : ∀ i ∈ ix0253, i < Pop.S0141.leaves.length := by decide +kernel
def r0253 : List (List ℕ) := ix0253.map fun i => (Pop.S0141.leaves.getD i dflt).1
theorem r0253_ok : ∀ p ∈ r0253, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0141.sem ix0253_lt

def ix0254 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46]
theorem ix0254_lt : ∀ i ∈ ix0254, i < Pop.S0142.leaves.length := by decide +kernel
def r0254 : List (List ℕ) := ix0254.map fun i => (Pop.S0142.leaves.getD i dflt).1
theorem r0254_ok : ∀ p ∈ r0254, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0142.sem ix0254_lt

def ix0255 : List ℕ := [63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104]
theorem ix0255_lt : ∀ i ∈ ix0255, i < Pop.S0132.leaves.length := by decide +kernel
def r0255 : List (List ℕ) := ix0255.map fun i => (Pop.S0132.leaves.getD i dflt).1
theorem r0255_ok : ∀ p ∈ r0255, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0132.sem ix0255_lt

def ix0256 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
theorem ix0256_lt : ∀ i ∈ ix0256, i < Pop.S0133.leaves.length := by decide +kernel
def r0256 : List (List ℕ) := ix0256.map fun i => (Pop.S0133.leaves.getD i dflt).1
theorem r0256_ok : ∀ p ∈ r0256, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0133.sem ix0256_lt

def ix0257 : List ℕ := [87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]
theorem ix0257_lt : ∀ i ∈ ix0257, i < Pop.S0047.leaves.length := by decide +kernel
def r0257 : List (List ℕ) := ix0257.map fun i => (Pop.S0047.leaves.getD i dflt).1
theorem r0257_ok : ∀ p ∈ r0257, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0047.sem ix0257_lt

def ix0258 : List ℕ := [39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103]
theorem ix0258_lt : ∀ i ∈ ix0258, i < Pop.S0153.leaves.length := by decide +kernel
def r0258 : List (List ℕ) := ix0258.map fun i => (Pop.S0153.leaves.getD i dflt).1
theorem r0258_ok : ∀ p ∈ r0258, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0153.sem ix0258_lt

def ix0259 : List ℕ := [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106]
theorem ix0259_lt : ∀ i ∈ ix0259, i < Pop.S0158.leaves.length := by decide +kernel
def r0259 : List (List ℕ) := ix0259.map fun i => (Pop.S0158.leaves.getD i dflt).1
theorem r0259_ok : ∀ p ∈ r0259, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0158.sem ix0259_lt

def ix0260 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]
theorem ix0260_lt : ∀ i ∈ ix0260, i < Pop.S0159.leaves.length := by decide +kernel
def r0260 : List (List ℕ) := ix0260.map fun i => (Pop.S0159.leaves.getD i dflt).1
theorem r0260_ok : ∀ p ∈ r0260, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0159.sem ix0260_lt

def ix0261 : List ℕ := [39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104]
theorem ix0261_lt : ∀ i ∈ ix0261, i < Pop.S0163.leaves.length := by decide +kernel
def r0261 : List (List ℕ) := ix0261.map fun i => (Pop.S0163.leaves.getD i dflt).1
theorem r0261_ok : ∀ p ∈ r0261, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0163.sem ix0261_lt

def ix0262 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99]
theorem ix0262_lt : ∀ i ∈ ix0262, i < Pop.S0164.leaves.length := by decide +kernel
def r0262 : List (List ℕ) := ix0262.map fun i => (Pop.S0164.leaves.getD i dflt).1
theorem r0262_ok : ∀ p ∈ r0262, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0164.sem ix0262_lt

def ix0263 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89]
theorem ix0263_lt : ∀ i ∈ ix0263, i < Pop.S0165.leaves.length := by decide +kernel
def r0263 : List (List ℕ) := ix0263.map fun i => (Pop.S0165.leaves.getD i dflt).1
theorem r0263_ok : ∀ p ∈ r0263, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0165.sem ix0263_lt

def ix0264 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
theorem ix0264_lt : ∀ i ∈ ix0264, i < Pop.S0166.leaves.length := by decide +kernel
def r0264 : List (List ℕ) := ix0264.map fun i => (Pop.S0166.leaves.getD i dflt).1
theorem r0264_ok : ∀ p ∈ r0264, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0166.sem ix0264_lt

def ix0265 : List ℕ := [49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74]
theorem ix0265_lt : ∀ i ∈ ix0265, i < Pop.S0164.leaves.length := by decide +kernel
def r0265 : List (List ℕ) := ix0265.map fun i => (Pop.S0164.leaves.getD i dflt).1
theorem r0265_ok : ∀ p ∈ r0265, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0164.sem ix0265_lt

def ix0266 : List ℕ := [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78]
theorem ix0266_lt : ∀ i ∈ ix0266, i < Pop.S0166.leaves.length := by decide +kernel
def r0266 : List (List ℕ) := ix0266.map fun i => (Pop.S0166.leaves.getD i dflt).1
theorem r0266_ok : ∀ p ∈ r0266, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0166.sem ix0266_lt

def ix0267 : List ℕ := [25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97]
theorem ix0267_lt : ∀ i ∈ ix0267, i < Pop.S0013.leaves.length := by decide +kernel
def r0267 : List (List ℕ) := ix0267.map fun i => (Pop.S0013.leaves.getD i dflt).1
theorem r0267_ok : ∀ p ∈ r0267, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0013.sem ix0267_lt

def ix0268 : List ℕ := [39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97]
theorem ix0268_lt : ∀ i ∈ ix0268, i < Pop.S0015.leaves.length := by decide +kernel
def r0268 : List (List ℕ) := ix0268.map fun i => (Pop.S0015.leaves.getD i dflt).1
theorem r0268_ok : ∀ p ∈ r0268, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0015.sem ix0268_lt

def ix0269 : List ℕ := [71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135]
theorem ix0269_lt : ∀ i ∈ ix0269, i < Pop.S0022.leaves.length := by decide +kernel
def r0269 : List (List ℕ) := ix0269.map fun i => (Pop.S0022.leaves.getD i dflt).1
theorem r0269_ok : ∀ p ∈ r0269, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0022.sem ix0269_lt

def ix0270 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]
theorem ix0270_lt : ∀ i ∈ ix0270, i < Pop.S0023.leaves.length := by decide +kernel
def r0270 : List (List ℕ) := ix0270.map fun i => (Pop.S0023.leaves.getD i dflt).1
theorem r0270_ok : ∀ p ∈ r0270, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0023.sem ix0270_lt

def ix0271 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81]
theorem ix0271_lt : ∀ i ∈ ix0271, i < Pop.S0024.leaves.length := by decide +kernel
def r0271 : List (List ℕ) := ix0271.map fun i => (Pop.S0024.leaves.getD i dflt).1
theorem r0271_ok : ∀ p ∈ r0271, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0024.sem ix0271_lt

def ix0272 : List ℕ := [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140]
theorem ix0272_lt : ∀ i ∈ ix0272, i < Pop.S0025.leaves.length := by decide +kernel
def r0272 : List (List ℕ) := ix0272.map fun i => (Pop.S0025.leaves.getD i dflt).1
theorem r0272_ok : ∀ p ∈ r0272, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0025.sem ix0272_lt

def ix0273 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]
theorem ix0273_lt : ∀ i ∈ ix0273, i < Pop.S0026.leaves.length := by decide +kernel
def r0273 : List (List ℕ) := ix0273.map fun i => (Pop.S0026.leaves.getD i dflt).1
theorem r0273_ok : ∀ p ∈ r0273, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0026.sem ix0273_lt

def ix0274 : List ℕ := [43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114]
theorem ix0274_lt : ∀ i ∈ ix0274, i < Pop.S0028.leaves.length := by decide +kernel
def r0274 : List (List ℕ) := ix0274.map fun i => (Pop.S0028.leaves.getD i dflt).1
theorem r0274_ok : ∀ p ∈ r0274, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0028.sem ix0274_lt

def ix0275 : List ℕ := [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]
theorem ix0275_lt : ∀ i ∈ ix0275, i < Pop.S0024.leaves.length := by decide +kernel
def r0275 : List (List ℕ) := ix0275.map fun i => (Pop.S0024.leaves.getD i dflt).1
theorem r0275_ok : ∀ p ∈ r0275, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0024.sem ix0275_lt

def ix0276 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
theorem ix0276_lt : ∀ i ∈ ix0276, i < Pop.S0025.leaves.length := by decide +kernel
def r0276 : List (List ℕ) := ix0276.map fun i => (Pop.S0025.leaves.getD i dflt).1
theorem r0276_ok : ∀ p ∈ r0276, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0025.sem ix0276_lt

def ix0277 : List ℕ := [54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]
theorem ix0277_lt : ∀ i ∈ ix0277, i < Pop.S0027.leaves.length := by decide +kernel
def r0277 : List (List ℕ) := ix0277.map fun i => (Pop.S0027.leaves.getD i dflt).1
theorem r0277_ok : ∀ p ∈ r0277, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0027.sem ix0277_lt

def ix0278 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135]
theorem ix0278_lt : ∀ i ∈ ix0278, i < Pop.S0028.leaves.length := by decide +kernel
def r0278 : List (List ℕ) := ix0278.map fun i => (Pop.S0028.leaves.getD i dflt).1
theorem r0278_ok : ∀ p ∈ r0278, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0028.sem ix0278_lt

def ix0279 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56]
theorem ix0279_lt : ∀ i ∈ ix0279, i < Pop.S0029.leaves.length := by decide +kernel
def r0279 : List (List ℕ) := ix0279.map fun i => (Pop.S0029.leaves.getD i dflt).1
theorem r0279_ok : ∀ p ∈ r0279, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0029.sem ix0279_lt

def ix0280 : List ℕ := [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117]
theorem ix0280_lt : ∀ i ∈ ix0280, i < Pop.S0025.leaves.length := by decide +kernel
def r0280 : List (List ℕ) := ix0280.map fun i => (Pop.S0025.leaves.getD i dflt).1
theorem r0280_ok : ∀ p ∈ r0280, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0025.sem ix0280_lt

def ix0281 : List ℕ := [35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146]
theorem ix0281_lt : ∀ i ∈ ix0281, i < Pop.S0026.leaves.length := by decide +kernel
def r0281 : List (List ℕ) := ix0281.map fun i => (Pop.S0026.leaves.getD i dflt).1
theorem r0281_ok : ∀ p ∈ r0281, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0026.sem ix0281_lt

def ix0282 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53]
theorem ix0282_lt : ∀ i ∈ ix0282, i < Pop.S0027.leaves.length := by decide +kernel
def r0282 : List (List ℕ) := ix0282.map fun i => (Pop.S0027.leaves.getD i dflt).1
theorem r0282_ok : ∀ p ∈ r0282, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0027.sem ix0282_lt

def ix0283 : List ℕ := [57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]
theorem ix0283_lt : ∀ i ∈ ix0283, i < Pop.S0029.leaves.length := by decide +kernel
def r0283 : List (List ℕ) := ix0283.map fun i => (Pop.S0029.leaves.getD i dflt).1
theorem r0283_ok : ∀ p ∈ r0283, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0029.sem ix0283_lt

def ix0284 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41]
theorem ix0284_lt : ∀ i ∈ ix0284, i < Pop.S0030.leaves.length := by decide +kernel
def r0284 : List (List ℕ) := ix0284.map fun i => (Pop.S0030.leaves.getD i dflt).1
theorem r0284_ok : ∀ p ∈ r0284, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0030.sem ix0284_lt

def ix0285 : List ℕ := [149]
theorem ix0285_lt : ∀ i ∈ ix0285, i < Pop.S0041.leaves.length := by decide +kernel
def r0285 : List (List ℕ) := ix0285.map fun i => (Pop.S0041.leaves.getD i dflt).1
theorem r0285_ok : ∀ p ∈ r0285, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0041.sem ix0285_lt

def ix0286 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]
theorem ix0286_lt : ∀ i ∈ ix0286, i < Pop.S0042.leaves.length := by decide +kernel
def r0286 : List (List ℕ) := ix0286.map fun i => (Pop.S0042.leaves.getD i dflt).1
theorem r0286_ok : ∀ p ∈ r0286, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0042.sem ix0286_lt

def ix0287 : List ℕ := [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
theorem ix0287_lt : ∀ i ∈ ix0287, i < Pop.S0044.leaves.length := by decide +kernel
def r0287 : List (List ℕ) := ix0287.map fun i => (Pop.S0044.leaves.getD i dflt).1
theorem r0287_ok : ∀ p ∈ r0287, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0044.sem ix0287_lt

def ix0288 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
theorem ix0288_lt : ∀ i ∈ ix0288, i < Pop.S0045.leaves.length := by decide +kernel
def r0288 : List (List ℕ) := ix0288.map fun i => (Pop.S0045.leaves.getD i dflt).1
theorem r0288_ok : ∀ p ∈ r0288, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0045.sem ix0288_lt

def ix0289 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76]
theorem ix0289_lt : ∀ i ∈ ix0289, i < Pop.S0046.leaves.length := by decide +kernel
def r0289 : List (List ℕ) := ix0289.map fun i => (Pop.S0046.leaves.getD i dflt).1
theorem r0289_ok : ∀ p ∈ r0289, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0046.sem ix0289_lt

def ix0290 : List ℕ := [23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]
theorem ix0290_lt : ∀ i ∈ ix0290, i < Pop.S0026.leaves.length := by decide +kernel
def r0290 : List (List ℕ) := ix0290.map fun i => (Pop.S0026.leaves.getD i dflt).1
theorem r0290_ok : ∀ p ∈ r0290, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0026.sem ix0290_lt

def ix0291 : List ℕ := [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126]
theorem ix0291_lt : ∀ i ∈ ix0291, i < Pop.S0030.leaves.length := by decide +kernel
def r0291 : List (List ℕ) := ix0291.map fun i => (Pop.S0030.leaves.getD i dflt).1
theorem r0291_ok : ∀ p ∈ r0291, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0030.sem ix0291_lt

def ix0292 : List ℕ := [77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]
theorem ix0292_lt : ∀ i ∈ ix0292, i < Pop.S0031.leaves.length := by decide +kernel
def r0292 : List (List ℕ) := ix0292.map fun i => (Pop.S0031.leaves.getD i dflt).1
theorem r0292_ok : ∀ p ∈ r0292, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0031.sem ix0292_lt

def ix0293 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61]
theorem ix0293_lt : ∀ i ∈ ix0293, i < Pop.S0032.leaves.length := by decide +kernel
def r0293 : List (List ℕ) := ix0293.map fun i => (Pop.S0032.leaves.getD i dflt).1
theorem r0293_ok : ∀ p ∈ r0293, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0032.sem ix0293_lt

def ix0294 : List ℕ := [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]
theorem ix0294_lt : ∀ i ∈ ix0294, i < Pop.S0030.leaves.length := by decide +kernel
def r0294 : List (List ℕ) := ix0294.map fun i => (Pop.S0030.leaves.getD i dflt).1
theorem r0294_ok : ∀ p ∈ r0294, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0030.sem ix0294_lt

def ix0295 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76]
theorem ix0295_lt : ∀ i ∈ ix0295, i < Pop.S0031.leaves.length := by decide +kernel
def r0295 : List (List ℕ) := ix0295.map fun i => (Pop.S0031.leaves.getD i dflt).1
theorem r0295_ok : ∀ p ∈ r0295, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0031.sem ix0295_lt

def ix0296 : List ℕ := [62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]
theorem ix0296_lt : ∀ i ∈ ix0296, i < Pop.S0032.leaves.length := by decide +kernel
def r0296 : List (List ℕ) := ix0296.map fun i => (Pop.S0032.leaves.getD i dflt).1
theorem r0296_ok : ∀ p ∈ r0296, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0032.sem ix0296_lt

def ix0297 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
theorem ix0297_lt : ∀ i ∈ ix0297, i < Pop.S0033.leaves.length := by decide +kernel
def r0297 : List (List ℕ) := ix0297.map fun i => (Pop.S0033.leaves.getD i dflt).1
theorem r0297_ok : ∀ p ∈ r0297, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0033.sem ix0297_lt

def ix0298 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78]
theorem ix0298_lt : ∀ i ∈ ix0298, i < Pop.S0034.leaves.length := by decide +kernel
def r0298 : List (List ℕ) := ix0298.map fun i => (Pop.S0034.leaves.getD i dflt).1
theorem r0298_ok : ∀ p ∈ r0298, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0034.sem ix0298_lt

def ix0299 : List ℕ := [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]
theorem ix0299_lt : ∀ i ∈ ix0299, i < Pop.S0035.leaves.length := by decide +kernel
def r0299 : List (List ℕ) := ix0299.map fun i => (Pop.S0035.leaves.getD i dflt).1
theorem r0299_ok : ∀ p ∈ r0299, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0035.sem ix0299_lt

def ix0300 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]
theorem ix0300_lt : ∀ i ∈ ix0300, i < Pop.S0036.leaves.length := by decide +kernel
def r0300 : List (List ℕ) := ix0300.map fun i => (Pop.S0036.leaves.getD i dflt).1
theorem r0300_ok : ∀ p ∈ r0300, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0036.sem ix0300_lt

def ix0301 : List ℕ := [79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
theorem ix0301_lt : ∀ i ∈ ix0301, i < Pop.S0034.leaves.length := by decide +kernel
def r0301 : List (List ℕ) := ix0301.map fun i => (Pop.S0034.leaves.getD i dflt).1
theorem r0301_ok : ∀ p ∈ r0301, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0034.sem ix0301_lt

def ix0302 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96]
theorem ix0302_lt : ∀ i ∈ ix0302, i < Pop.S0035.leaves.length := by decide +kernel
def r0302 : List (List ℕ) := ix0302.map fun i => (Pop.S0035.leaves.getD i dflt).1
theorem r0302_ok : ∀ p ∈ r0302, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0035.sem ix0302_lt

def ix0303 : List ℕ := [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
theorem ix0303_lt : ∀ i ∈ ix0303, i < Pop.S0036.leaves.length := by decide +kernel
def r0303 : List (List ℕ) := ix0303.map fun i => (Pop.S0036.leaves.getD i dflt).1
theorem r0303_ok : ∀ p ∈ r0303, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0036.sem ix0303_lt

def ix0304 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59]
theorem ix0304_lt : ∀ i ∈ ix0304, i < Pop.S0037.leaves.length := by decide +kernel
def r0304 : List (List ℕ) := ix0304.map fun i => (Pop.S0037.leaves.getD i dflt).1
theorem r0304_ok : ∀ p ∈ r0304, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0037.sem ix0304_lt

def ix0305 : List ℕ := [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]
theorem ix0305_lt : ∀ i ∈ ix0305, i < Pop.S0036.leaves.length := by decide +kernel
def r0305 : List (List ℕ) := ix0305.map fun i => (Pop.S0036.leaves.getD i dflt).1
theorem r0305_ok : ∀ p ∈ r0305, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0036.sem ix0305_lt

def ix0306 : List ℕ := [69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
theorem ix0306_lt : ∀ i ∈ ix0306, i < Pop.S0037.leaves.length := by decide +kernel
def r0306 : List (List ℕ) := ix0306.map fun i => (Pop.S0037.leaves.getD i dflt).1
theorem r0306_ok : ∀ p ∈ r0306, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0037.sem ix0306_lt

def ix0307 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72]
theorem ix0307_lt : ∀ i ∈ ix0307, i < Pop.S0038.leaves.length := by decide +kernel
def r0307 : List (List ℕ) := ix0307.map fun i => (Pop.S0038.leaves.getD i dflt).1
theorem r0307_ok : ∀ p ∈ r0307, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0038.sem ix0307_lt

def ix0308 : List ℕ := [31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]
theorem ix0308_lt : ∀ i ∈ ix0308, i < Pop.S0039.leaves.length := by decide +kernel
def r0308 : List (List ℕ) := ix0308.map fun i => (Pop.S0039.leaves.getD i dflt).1
theorem r0308_ok : ∀ p ∈ r0308, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0039.sem ix0308_lt

def ix0309 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
theorem ix0309_lt : ∀ i ∈ ix0309, i < Pop.S0040.leaves.length := by decide +kernel
def r0309 : List (List ℕ) := ix0309.map fun i => (Pop.S0040.leaves.getD i dflt).1
theorem r0309_ok : ∀ p ∈ r0309, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0040.sem ix0309_lt

def ix0310 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]
theorem ix0310_lt : ∀ i ∈ ix0310, i < Pop.S0041.leaves.length := by decide +kernel
def r0310 : List (List ℕ) := ix0310.map fun i => (Pop.S0041.leaves.getD i dflt).1
theorem r0310_ok : ∀ p ∈ r0310, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0041.sem ix0310_lt

def ix0311 : List ℕ := [73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
theorem ix0311_lt : ∀ i ∈ ix0311, i < Pop.S0038.leaves.length := by decide +kernel
def r0311 : List (List ℕ) := ix0311.map fun i => (Pop.S0038.leaves.getD i dflt).1
theorem r0311_ok : ∀ p ∈ r0311, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0038.sem ix0311_lt

def ix0312 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]
theorem ix0312_lt : ∀ i ∈ ix0312, i < Pop.S0039.leaves.length := by decide +kernel
def r0312 : List (List ℕ) := ix0312.map fun i => (Pop.S0039.leaves.getD i dflt).1
theorem r0312_ok : ∀ p ∈ r0312, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0039.sem ix0312_lt

def ix0313 : List ℕ := [25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]
theorem ix0313_lt : ∀ i ∈ ix0313, i < Pop.S0040.leaves.length := by decide +kernel
def r0313 : List (List ℕ) := ix0313.map fun i => (Pop.S0040.leaves.getD i dflt).1
theorem r0313_ok : ∀ p ∈ r0313, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0040.sem ix0313_lt

def ix0314 : List ℕ := [140, 141, 142, 143, 144, 145, 146, 147]
theorem ix0314_lt : ∀ i ∈ ix0314, i < Pop.S0042.leaves.length := by decide +kernel
def r0314 : List (List ℕ) := ix0314.map fun i => (Pop.S0042.leaves.getD i dflt).1
theorem r0314_ok : ∀ p ∈ r0314, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0042.sem ix0314_lt

def ix0315 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
theorem ix0315_lt : ∀ i ∈ ix0315, i < Pop.S0043.leaves.length := by decide +kernel
def r0315 : List (List ℕ) := ix0315.map fun i => (Pop.S0043.leaves.getD i dflt).1
theorem r0315_ok : ∀ p ∈ r0315, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0043.sem ix0315_lt

def ix0316 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120]
theorem ix0316_lt : ∀ i ∈ ix0316, i < Pop.S0044.leaves.length := by decide +kernel
def r0316 : List (List ℕ) := ix0316.map fun i => (Pop.S0044.leaves.getD i dflt).1
theorem r0316_ok : ∀ p ∈ r0316, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0044.sem ix0316_lt

def ix0317 : List ℕ := [39, 40, 41]
theorem ix0317_lt : ∀ i ∈ ix0317, i < Pop.S0033.leaves.length := by decide +kernel
def r0317 : List (List ℕ) := ix0317.map fun i => (Pop.S0033.leaves.getD i dflt).1
theorem r0317_ok : ∀ p ∈ r0317, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0033.sem ix0317_lt

def ix0318 : List ℕ := [97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109]
theorem ix0318_lt : ∀ i ∈ ix0318, i < Pop.S0035.leaves.length := by decide +kernel
def r0318 : List (List ℕ) := ix0318.map fun i => (Pop.S0035.leaves.getD i dflt).1
theorem r0318_ok : ∀ p ∈ r0318, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0035.sem ix0318_lt

def ix0319 : List ℕ := [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]
theorem ix0319_lt : ∀ i ∈ ix0319, i < Pop.S0036.leaves.length := by decide +kernel
def r0319 : List (List ℕ) := ix0319.map fun i => (Pop.S0036.leaves.getD i dflt).1
theorem r0319_ok : ∀ p ∈ r0319, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0036.sem ix0319_lt

def ix0320 : List ℕ := [60, 61, 62, 63, 64, 65, 66, 67, 68]
theorem ix0320_lt : ∀ i ∈ ix0320, i < Pop.S0037.leaves.length := by decide +kernel
def r0320 : List (List ℕ) := ix0320.map fun i => (Pop.S0037.leaves.getD i dflt).1
theorem r0320_ok : ∀ p ∈ r0320, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0037.sem ix0320_lt

def ix0321 : List ℕ := [30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]
theorem ix0321_lt : ∀ i ∈ ix0321, i < Pop.S0041.leaves.length := by decide +kernel
def r0321 : List (List ℕ) := ix0321.map fun i => (Pop.S0041.leaves.getD i dflt).1
theorem r0321_ok : ∀ p ∈ r0321, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0041.sem ix0321_lt

def ix0322 : List ℕ := [26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]
theorem ix0322_lt : ∀ i ∈ ix0322, i < Pop.S0042.leaves.length := by decide +kernel
def r0322 : List (List ℕ) := ix0322.map fun i => (Pop.S0042.leaves.getD i dflt).1
theorem r0322_ok : ∀ p ∈ r0322, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0042.sem ix0322_lt

def ix0323 : List ℕ := [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106]
theorem ix0323_lt : ∀ i ∈ ix0323, i < Pop.S0045.leaves.length := by decide +kernel
def r0323 : List (List ℕ) := ix0323.map fun i => (Pop.S0045.leaves.getD i dflt).1
theorem r0323_ok : ∀ p ∈ r0323, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0045.sem ix0323_lt

def ix0324 : List ℕ := [56, 57, 58]
theorem ix0324_lt : ∀ i ∈ ix0324, i < Pop.S0044.leaves.length := by decide +kernel
def r0324 : List (List ℕ) := ix0324.map fun i => (Pop.S0044.leaves.getD i dflt).1
theorem r0324_ok : ∀ p ∈ r0324, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0044.sem ix0324_lt

def ix0325 : List ℕ := [77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]
theorem ix0325_lt : ∀ i ∈ ix0325, i < Pop.S0046.leaves.length := by decide +kernel
def r0325 : List (List ℕ) := ix0325.map fun i => (Pop.S0046.leaves.getD i dflt).1
theorem r0325_ok : ∀ p ∈ r0325, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0046.sem ix0325_lt

def ix0326 : List ℕ := [73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84]
theorem ix0326_lt : ∀ i ∈ ix0326, i < Pop.S0047.leaves.length := by decide +kernel
def r0326 : List (List ℕ) := ix0326.map fun i => (Pop.S0047.leaves.getD i dflt).1
theorem r0326_ok : ∀ p ∈ r0326, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0047.sem ix0326_lt

def ix0327 : List ℕ := [29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130]
theorem ix0327_lt : ∀ i ∈ ix0327, i < Pop.S0170.leaves.length := by decide +kernel
def r0327 : List (List ℕ) := ix0327.map fun i => (Pop.S0170.leaves.getD i dflt).1
theorem r0327_ok : ∀ p ∈ r0327, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0170.sem ix0327_lt

def ix0328 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84]
theorem ix0328_lt : ∀ i ∈ ix0328, i < Pop.S0171.leaves.length := by decide +kernel
def r0328 : List (List ℕ) := ix0328.map fun i => (Pop.S0171.leaves.getD i dflt).1
theorem r0328_ok : ∀ p ∈ r0328, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0171.sem ix0328_lt

def ix0329 : List ℕ := [65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]
theorem ix0329_lt : ∀ i ∈ ix0329, i < Pop.S0175.leaves.length := by decide +kernel
def r0329 : List (List ℕ) := ix0329.map fun i => (Pop.S0175.leaves.getD i dflt).1
theorem r0329_ok : ∀ p ∈ r0329, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0175.sem ix0329_lt

def ix0330 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114]
theorem ix0330_lt : ∀ i ∈ ix0330, i < Pop.S0176.leaves.length := by decide +kernel
def r0330 : List (List ℕ) := ix0330.map fun i => (Pop.S0176.leaves.getD i dflt).1
theorem r0330_ok : ∀ p ∈ r0330, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0176.sem ix0330_lt

def ix0331 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]
theorem ix0331_lt : ∀ i ∈ ix0331, i < Pop.S0177.leaves.length := by decide +kernel
def r0331 : List (List ℕ) := ix0331.map fun i => (Pop.S0177.leaves.getD i dflt).1
theorem r0331_ok : ∀ p ∈ r0331, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0177.sem ix0331_lt

def ix0332 : List ℕ := [97, 98, 99, 100, 101, 102, 103, 104]
theorem ix0332_lt : ∀ i ∈ ix0332, i < Pop.S0178.leaves.length := by decide +kernel
def r0332 : List (List ℕ) := ix0332.map fun i => (Pop.S0178.leaves.getD i dflt).1
theorem r0332_ok : ∀ p ∈ r0332, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0178.sem ix0332_lt

def ix0333 : List ℕ := [79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141]
theorem ix0333_lt : ∀ i ∈ ix0333, i < Pop.S0179.leaves.length := by decide +kernel
def r0333 : List (List ℕ) := ix0333.map fun i => (Pop.S0179.leaves.getD i dflt).1
theorem r0333_ok : ∀ p ∈ r0333, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0179.sem ix0333_lt

def ix0334 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
theorem ix0334_lt : ∀ i ∈ ix0334, i < Pop.S0180.leaves.length := by decide +kernel
def r0334 : List (List ℕ) := ix0334.map fun i => (Pop.S0180.leaves.getD i dflt).1
theorem r0334_ok : ∀ p ∈ r0334, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0180.sem ix0334_lt

def ix0335 : List ℕ := [30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]
theorem ix0335_lt : ∀ i ∈ ix0335, i < Pop.S0177.leaves.length := by decide +kernel
def r0335 : List (List ℕ) := ix0335.map fun i => (Pop.S0177.leaves.getD i dflt).1
theorem r0335_ok : ∀ p ∈ r0335, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0177.sem ix0335_lt

def ix0336 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]
theorem ix0336_lt : ∀ i ∈ ix0336, i < Pop.S0178.leaves.length := by decide +kernel
def r0336 : List (List ℕ) := ix0336.map fun i => (Pop.S0178.leaves.getD i dflt).1
theorem r0336_ok : ∀ p ∈ r0336, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0178.sem ix0336_lt

def ix0337 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78]
theorem ix0337_lt : ∀ i ∈ ix0337, i < Pop.S0179.leaves.length := by decide +kernel
def r0337 : List (List ℕ) := ix0337.map fun i => (Pop.S0179.leaves.getD i dflt).1
theorem r0337_ok : ∀ p ∈ r0337, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0179.sem ix0337_lt

def ix0338 : List ℕ := [31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115]
theorem ix0338_lt : ∀ i ∈ ix0338, i < Pop.S0196.leaves.length := by decide +kernel
def r0338 : List (List ℕ) := ix0338.map fun i => (Pop.S0196.leaves.getD i dflt).1
theorem r0338_ok : ∀ p ∈ r0338, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0196.sem ix0338_lt

def ix0339 : List ℕ := [148]
theorem ix0339_lt : ∀ i ∈ ix0339, i < Pop.S0199.leaves.length := by decide +kernel
def r0339 : List (List ℕ) := ix0339.map fun i => (Pop.S0199.leaves.getD i dflt).1
theorem r0339_ok : ∀ p ∈ r0339, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0199.sem ix0339_lt

def ix0340 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89]
theorem ix0340_lt : ∀ i ∈ ix0340, i < Pop.S0200.leaves.length := by decide +kernel
def r0340 : List (List ℕ) := ix0340.map fun i => (Pop.S0200.leaves.getD i dflt).1
theorem r0340_ok : ∀ p ∈ r0340, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0200.sem ix0340_lt

def ix0341 : List ℕ := [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]
theorem ix0341_lt : ∀ i ∈ ix0341, i < Pop.S0201.leaves.length := by decide +kernel
def r0341 : List (List ℕ) := ix0341.map fun i => (Pop.S0201.leaves.getD i dflt).1
theorem r0341_ok : ∀ p ∈ r0341, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0201.sem ix0341_lt

def ix0342 : List ℕ := [93, 94, 95, 96]
theorem ix0342_lt : ∀ i ∈ ix0342, i < Pop.S0204.leaves.length := by decide +kernel
def r0342 : List (List ℕ) := ix0342.map fun i => (Pop.S0204.leaves.getD i dflt).1
theorem r0342_ok : ∀ p ∈ r0342, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0204.sem ix0342_lt

def ix0343 : List ℕ := [51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94]
theorem ix0343_lt : ∀ i ∈ ix0343, i < Pop.S0332.leaves.length := by decide +kernel
def r0343 : List (List ℕ) := ix0343.map fun i => (Pop.S0332.leaves.getD i dflt).1
theorem r0343_ok : ∀ p ∈ r0343, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0332.sem ix0343_lt

def ix0344 : List ℕ := [35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91]
theorem ix0344_lt : ∀ i ∈ ix0344, i < Pop.S0334.leaves.length := by decide +kernel
def r0344 : List (List ℕ) := ix0344.map fun i => (Pop.S0334.leaves.getD i dflt).1
theorem r0344_ok : ∀ p ∈ r0344, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0334.sem ix0344_lt

def ix0345 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66]
theorem ix0345_lt : ∀ i ∈ ix0345, i < Pop.S0389.leaves.length := by decide +kernel
def r0345 : List (List ℕ) := ix0345.map fun i => (Pop.S0389.leaves.getD i dflt).1
theorem r0345_ok : ∀ p ∈ r0345, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0389.sem ix0345_lt

def ix0346 : List ℕ := [60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113]
theorem ix0346_lt : ∀ i ∈ ix0346, i < Pop.S0390.leaves.length := by decide +kernel
def r0346 : List (List ℕ) := ix0346.map fun i => (Pop.S0390.leaves.getD i dflt).1
theorem r0346_ok : ∀ p ∈ r0346, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0390.sem ix0346_lt

def ix0347 : List ℕ := [55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]
theorem ix0347_lt : ∀ i ∈ ix0347, i < Pop.S0391.leaves.length := by decide +kernel
def r0347 : List (List ℕ) := ix0347.map fun i => (Pop.S0391.leaves.getD i dflt).1
theorem r0347_ok : ∀ p ∈ r0347, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0391.sem ix0347_lt

def ix0348 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
theorem ix0348_lt : ∀ i ∈ ix0348, i < Pop.S0392.leaves.length := by decide +kernel
def r0348 : List (List ℕ) := ix0348.map fun i => (Pop.S0392.leaves.getD i dflt).1
theorem r0348_ok : ∀ p ∈ r0348, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0392.sem ix0348_lt

def ix0349 : List ℕ := [83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]
theorem ix0349_lt : ∀ i ∈ ix0349, i < Pop.S0393.leaves.length := by decide +kernel
def r0349 : List (List ℕ) := ix0349.map fun i => (Pop.S0393.leaves.getD i dflt).1
theorem r0349_ok : ∀ p ∈ r0349, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0393.sem ix0349_lt

def ix0350 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]
theorem ix0350_lt : ∀ i ∈ ix0350, i < Pop.S0394.leaves.length := by decide +kernel
def r0350 : List (List ℕ) := ix0350.map fun i => (Pop.S0394.leaves.getD i dflt).1
theorem r0350_ok : ∀ p ∈ r0350, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0394.sem ix0350_lt

def ix0351 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40]
theorem ix0351_lt : ∀ i ∈ ix0351, i < Pop.S0395.leaves.length := by decide +kernel
def r0351 : List (List ℕ) := ix0351.map fun i => (Pop.S0395.leaves.getD i dflt).1
theorem r0351_ok : ∀ p ∈ r0351, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0395.sem ix0351_lt

def ix0352 : List ℕ := [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]
theorem ix0352_lt : ∀ i ∈ ix0352, i < Pop.S0398.leaves.length := by decide +kernel
def r0352 : List (List ℕ) := ix0352.map fun i => (Pop.S0398.leaves.getD i dflt).1
theorem r0352_ok : ∀ p ∈ r0352, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0398.sem ix0352_lt

def ix0353 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]
theorem ix0353_lt : ∀ i ∈ ix0353, i < Pop.S0399.leaves.length := by decide +kernel
def r0353 : List (List ℕ) := ix0353.map fun i => (Pop.S0399.leaves.getD i dflt).1
theorem r0353_ok : ∀ p ∈ r0353, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0399.sem ix0353_lt

def ix0354 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54]
theorem ix0354_lt : ∀ i ∈ ix0354, i < Pop.S0400.leaves.length := by decide +kernel
def r0354 : List (List ℕ) := ix0354.map fun i => (Pop.S0400.leaves.getD i dflt).1
theorem r0354_ok : ∀ p ∈ r0354, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0400.sem ix0354_lt

def ix0355 : List ℕ := [59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82]
theorem ix0355_lt : ∀ i ∈ ix0355, i < Pop.S0393.leaves.length := by decide +kernel
def r0355 : List (List ℕ) := ix0355.map fun i => (Pop.S0393.leaves.getD i dflt).1
theorem r0355_ok : ∀ p ∈ r0355, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0393.sem ix0355_lt

def ix0356 : List ℕ := [41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90]
theorem ix0356_lt : ∀ i ∈ ix0356, i < Pop.S0395.leaves.length := by decide +kernel
def r0356 : List (List ℕ) := ix0356.map fun i => (Pop.S0395.leaves.getD i dflt).1
theorem r0356_ok : ∀ p ∈ r0356, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0395.sem ix0356_lt

def ix0357 : List ℕ := [51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62]
theorem ix0357_lt : ∀ i ∈ ix0357, i < Pop.S0397.leaves.length := by decide +kernel
def r0357 : List (List ℕ) := ix0357.map fun i => (Pop.S0397.leaves.getD i dflt).1
theorem r0357_ok : ∀ p ∈ r0357, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0397.sem ix0357_lt

def ix0358 : List ℕ := [55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97]
theorem ix0358_lt : ∀ i ∈ ix0358, i < Pop.S0400.leaves.length := by decide +kernel
def r0358 : List (List ℕ) := ix0358.map fun i => (Pop.S0400.leaves.getD i dflt).1
theorem r0358_ok : ∀ p ∈ r0358, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0400.sem ix0358_lt

def ix0359 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]
theorem ix0359_lt : ∀ i ∈ ix0359, i < Pop.S0401.leaves.length := by decide +kernel
def r0359 : List (List ℕ) := ix0359.map fun i => (Pop.S0401.leaves.getD i dflt).1
theorem r0359_ok : ∀ p ∈ r0359, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0401.sem ix0359_lt

def ix0360 : List ℕ := [77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]
theorem ix0360_lt : ∀ i ∈ ix0360, i < Pop.S0409.leaves.length := by decide +kernel
def r0360 : List (List ℕ) := ix0360.map fun i => (Pop.S0409.leaves.getD i dflt).1
theorem r0360_ok : ∀ p ∈ r0360, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0409.sem ix0360_lt

def ix0361 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]
theorem ix0361_lt : ∀ i ∈ ix0361, i < Pop.S0410.leaves.length := by decide +kernel
def r0361 : List (List ℕ) := ix0361.map fun i => (Pop.S0410.leaves.getD i dflt).1
theorem r0361_ok : ∀ p ∈ r0361, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0410.sem ix0361_lt

def ix0362 : List ℕ := [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93]
theorem ix0362_lt : ∀ i ∈ ix0362, i < Pop.S0411.leaves.length := by decide +kernel
def r0362 : List (List ℕ) := ix0362.map fun i => (Pop.S0411.leaves.getD i dflt).1
theorem r0362_ok : ∀ p ∈ r0362, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0411.sem ix0362_lt

def ix0363 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]
theorem ix0363_lt : ∀ i ∈ ix0363, i < Pop.S0412.leaves.length := by decide +kernel
def r0363 : List (List ℕ) := ix0363.map fun i => (Pop.S0412.leaves.getD i dflt).1
theorem r0363_ok : ∀ p ∈ r0363, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0412.sem ix0363_lt

def ix0364 : List ℕ := [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88]
theorem ix0364_lt : ∀ i ∈ ix0364, i < Pop.S0416.leaves.length := by decide +kernel
def r0364 : List (List ℕ) := ix0364.map fun i => (Pop.S0416.leaves.getD i dflt).1
theorem r0364_ok : ∀ p ∈ r0364, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0416.sem ix0364_lt

def ix0365 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36]
theorem ix0365_lt : ∀ i ∈ ix0365, i < Pop.S0417.leaves.length := by decide +kernel
def r0365 : List (List ℕ) := ix0365.map fun i => (Pop.S0417.leaves.getD i dflt).1
theorem r0365_ok : ∀ p ∈ r0365, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0417.sem ix0365_lt

def ix0366 : List ℕ := [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87]
theorem ix0366_lt : ∀ i ∈ ix0366, i < Pop.S0412.leaves.length := by decide +kernel
def r0366 : List (List ℕ) := ix0366.map fun i => (Pop.S0412.leaves.getD i dflt).1
theorem r0366_ok : ∀ p ∈ r0366, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0412.sem ix0366_lt

def ix0367 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]
theorem ix0367_lt : ∀ i ∈ ix0367, i < Pop.S0413.leaves.length := by decide +kernel
def r0367 : List (List ℕ) := ix0367.map fun i => (Pop.S0413.leaves.getD i dflt).1
theorem r0367_ok : ∀ p ∈ r0367, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0413.sem ix0367_lt

def ix0368 : List ℕ := [99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109]
theorem ix0368_lt : ∀ i ∈ ix0368, i < Pop.S0414.leaves.length := by decide +kernel
def r0368 : List (List ℕ) := ix0368.map fun i => (Pop.S0414.leaves.getD i dflt).1
theorem r0368_ok : ∀ p ∈ r0368, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0414.sem ix0368_lt

def ix0369 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
theorem ix0369_lt : ∀ i ∈ ix0369, i < Pop.S0415.leaves.length := by decide +kernel
def r0369 : List (List ℕ) := ix0369.map fun i => (Pop.S0415.leaves.getD i dflt).1
theorem r0369_ok : ∀ p ∈ r0369, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0415.sem ix0369_lt

def ix0370 : List ℕ := [96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]
theorem ix0370_lt : ∀ i ∈ ix0370, i < Pop.S0417.leaves.length := by decide +kernel
def r0370 : List (List ℕ) := ix0370.map fun i => (Pop.S0417.leaves.getD i dflt).1
theorem r0370_ok : ∀ p ∈ r0370, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0417.sem ix0370_lt

def ix0371 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]
theorem ix0371_lt : ∀ i ∈ ix0371, i < Pop.S0418.leaves.length := by decide +kernel
def r0371 : List (List ℕ) := ix0371.map fun i => (Pop.S0418.leaves.getD i dflt).1
theorem r0371_ok : ∀ p ∈ r0371, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0418.sem ix0371_lt

def ix0372 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51]
theorem ix0372_lt : ∀ i ∈ ix0372, i < Pop.S0419.leaves.length := by decide +kernel
def r0372 : List (List ℕ) := ix0372.map fun i => (Pop.S0419.leaves.getD i dflt).1
theorem r0372_ok : ∀ p ∈ r0372, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0419.sem ix0372_lt

def ix0373 : List ℕ := [45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112]
theorem ix0373_lt : ∀ i ∈ ix0373, i < Pop.S0420.leaves.length := by decide +kernel
def r0373 : List (List ℕ) := ix0373.map fun i => (Pop.S0420.leaves.getD i dflt).1
theorem r0373_ok : ∀ p ∈ r0373, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0420.sem ix0373_lt

def ix0374 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]
theorem ix0374_lt : ∀ i ∈ ix0374, i < Pop.S0421.leaves.length := by decide +kernel
def r0374 : List (List ℕ) := ix0374.map fun i => (Pop.S0421.leaves.getD i dflt).1
theorem r0374_ok : ∀ p ∈ r0374, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0421.sem ix0374_lt

def ix0375 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]
theorem ix0375_lt : ∀ i ∈ ix0375, i < Pop.S0422.leaves.length := by decide +kernel
def r0375 : List (List ℕ) := ix0375.map fun i => (Pop.S0422.leaves.getD i dflt).1
theorem r0375_ok : ∀ p ∈ r0375, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0422.sem ix0375_lt

def ix0376 : List ℕ := [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]
theorem ix0376_lt : ∀ i ∈ ix0376, i < Pop.S0413.leaves.length := by decide +kernel
def r0376 : List (List ℕ) := ix0376.map fun i => (Pop.S0413.leaves.getD i dflt).1
theorem r0376_ok : ∀ p ∈ r0376, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0413.sem ix0376_lt

def ix0377 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98]
theorem ix0377_lt : ∀ i ∈ ix0377, i < Pop.S0414.leaves.length := by decide +kernel
def r0377 : List (List ℕ) := ix0377.map fun i => (Pop.S0414.leaves.getD i dflt).1
theorem r0377_ok : ∀ p ∈ r0377, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0414.sem ix0377_lt

def ix0378 : List ℕ := [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121]
theorem ix0378_lt : ∀ i ∈ ix0378, i < Pop.S0415.leaves.length := by decide +kernel
def r0378 : List (List ℕ) := ix0378.map fun i => (Pop.S0415.leaves.getD i dflt).1
theorem r0378_ok : ∀ p ∈ r0378, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0415.sem ix0378_lt

def ix0379 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
theorem ix0379_lt : ∀ i ∈ ix0379, i < Pop.S0416.leaves.length := by decide +kernel
def r0379 : List (List ℕ) := ix0379.map fun i => (Pop.S0416.leaves.getD i dflt).1
theorem r0379_ok : ∀ p ∈ r0379, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0416.sem ix0379_lt

def ix0380 : List ℕ := [53, 54, 55]
theorem ix0380_lt : ∀ i ∈ ix0380, i < Pop.S0415.leaves.length := by decide +kernel
def r0380 : List (List ℕ) := ix0380.map fun i => (Pop.S0415.leaves.getD i dflt).1
theorem r0380_ok : ∀ p ∈ r0380, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0415.sem ix0380_lt

def ix0381 : List ℕ := [52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119]
theorem ix0381_lt : ∀ i ∈ ix0381, i < Pop.S0419.leaves.length := by decide +kernel
def r0381 : List (List ℕ) := ix0381.map fun i => (Pop.S0419.leaves.getD i dflt).1
theorem r0381_ok : ∀ p ∈ r0381, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0419.sem ix0381_lt

def ix0382 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44]
theorem ix0382_lt : ∀ i ∈ ix0382, i < Pop.S0420.leaves.length := by decide +kernel
def r0382 : List (List ℕ) := ix0382.map fun i => (Pop.S0420.leaves.getD i dflt).1
theorem r0382_ok : ∀ p ∈ r0382, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0420.sem ix0382_lt

def ix0383 : List ℕ := [91, 92, 93, 94]
theorem ix0383_lt : ∀ i ∈ ix0383, i < Pop.S0395.leaves.length := by decide +kernel
def r0383 : List (List ℕ) := ix0383.map fun i => (Pop.S0395.leaves.getD i dflt).1
theorem r0383_ok : ∀ p ∈ r0383, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0395.sem ix0383_lt

def ix0384 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]
theorem ix0384_lt : ∀ i ∈ ix0384, i < Pop.S0396.leaves.length := by decide +kernel
def r0384 : List (List ℕ) := ix0384.map fun i => (Pop.S0396.leaves.getD i dflt).1
theorem r0384_ok : ∀ p ∈ r0384, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0396.sem ix0384_lt

def ix0385 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]
theorem ix0385_lt : ∀ i ∈ ix0385, i < Pop.S0397.leaves.length := by decide +kernel
def r0385 : List (List ℕ) := ix0385.map fun i => (Pop.S0397.leaves.getD i dflt).1
theorem r0385_ok : ∀ p ∈ r0385, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0397.sem ix0385_lt

def ix0386 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]
theorem ix0386_lt : ∀ i ∈ ix0386, i < Pop.S0398.leaves.length := by decide +kernel
def r0386 : List (List ℕ) := ix0386.map fun i => (Pop.S0398.leaves.getD i dflt).1
theorem r0386_ok : ∀ p ∈ r0386, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0398.sem ix0386_lt

def ix0387 : List ℕ := [104, 105]
theorem ix0387_lt : ∀ i ∈ ix0387, i < Pop.S0397.leaves.length := by decide +kernel
def r0387 : List (List ℕ) := ix0387.map fun i => (Pop.S0397.leaves.getD i dflt).1
theorem r0387_ok : ∀ p ∈ r0387, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0397.sem ix0387_lt

def ix0388 : List ℕ := [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]
theorem ix0388_lt : ∀ i ∈ ix0388, i < Pop.S0402.leaves.length := by decide +kernel
def r0388 : List (List ℕ) := ix0388.map fun i => (Pop.S0402.leaves.getD i dflt).1
theorem r0388_ok : ∀ p ∈ r0388, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0402.sem ix0388_lt

def ix0389 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141]
theorem ix0389_lt : ∀ i ∈ ix0389, i < Pop.S0403.leaves.length := by decide +kernel
def r0389 : List (List ℕ) := ix0389.map fun i => (Pop.S0403.leaves.getD i dflt).1
theorem r0389_ok : ∀ p ∈ r0389, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0403.sem ix0389_lt

def ix0390 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114]
theorem ix0390_lt : ∀ i ∈ ix0390, i < Pop.S0404.leaves.length := by decide +kernel
def r0390 : List (List ℕ) := ix0390.map fun i => (Pop.S0404.leaves.getD i dflt).1
theorem r0390_ok : ∀ p ∈ r0390, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0404.sem ix0390_lt

def ix0391 : List ℕ := [77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140]
theorem ix0391_lt : ∀ i ∈ ix0391, i < Pop.S0405.leaves.length := by decide +kernel
def r0391 : List (List ℕ) := ix0391.map fun i => (Pop.S0405.leaves.getD i dflt).1
theorem r0391_ok : ∀ p ∈ r0391, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0405.sem ix0391_lt

def ix0392 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]
theorem ix0392_lt : ∀ i ∈ ix0392, i < Pop.S0406.leaves.length := by decide +kernel
def r0392 : List (List ℕ) := ix0392.map fun i => (Pop.S0406.leaves.getD i dflt).1
theorem r0392_ok : ∀ p ∈ r0392, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0406.sem ix0392_lt

def ix0393 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130]
theorem ix0393_lt : ∀ i ∈ ix0393, i < Pop.S0407.leaves.length := by decide +kernel
def r0393 : List (List ℕ) := ix0393.map fun i => (Pop.S0407.leaves.getD i dflt).1
theorem r0393_ok : ∀ p ∈ r0393, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0407.sem ix0393_lt

def ix0394 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]
theorem ix0394_lt : ∀ i ∈ ix0394, i < Pop.S0408.leaves.length := by decide +kernel
def r0394 : List (List ℕ) := ix0394.map fun i => (Pop.S0408.leaves.getD i dflt).1
theorem r0394_ok : ∀ p ∈ r0394, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0408.sem ix0394_lt

def ix0395 : List ℕ := [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76]
theorem ix0395_lt : ∀ i ∈ ix0395, i < Pop.S0405.leaves.length := by decide +kernel
def r0395 : List (List ℕ) := ix0395.map fun i => (Pop.S0405.leaves.getD i dflt).1
theorem r0395_ok : ∀ p ∈ r0395, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0405.sem ix0395_lt

def ix0396 : List ℕ := [90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114]
theorem ix0396_lt : ∀ i ∈ ix0396, i < Pop.S0200.leaves.length := by decide +kernel
def r0396 : List (List ℕ) := ix0396.map fun i => (Pop.S0200.leaves.getD i dflt).1
theorem r0396_ok : ∀ p ∈ r0396, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0200.sem ix0396_lt

def ix0397 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 137, 138, 139, 140, 141, 142, 143, 144]
theorem ix0397_lt : ∀ i ∈ ix0397, i < Pop.S0201.leaves.length := by decide +kernel
def r0397 : List (List ℕ) := ix0397.map fun i => (Pop.S0201.leaves.getD i dflt).1
theorem r0397_ok : ∀ p ∈ r0397, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0201.sem ix0397_lt

def ix0398 : List ℕ := [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
theorem ix0398_lt : ∀ i ∈ ix0398, i < Pop.S0202.leaves.length := by decide +kernel
def r0398 : List (List ℕ) := ix0398.map fun i => (Pop.S0202.leaves.getD i dflt).1
theorem r0398_ok : ∀ p ∈ r0398, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0202.sem ix0398_lt

def ix0399 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89]
theorem ix0399_lt : ∀ i ∈ ix0399, i < Pop.S0203.leaves.length := by decide +kernel
def r0399 : List (List ℕ) := ix0399.map fun i => (Pop.S0203.leaves.getD i dflt).1
theorem r0399_ok : ∀ p ∈ r0399, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0203.sem ix0399_lt

def ix0400 : List ℕ := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]
theorem ix0400_lt : ∀ i ∈ ix0400, i < Pop.S0204.leaves.length := by decide +kernel
def r0400 : List (List ℕ) := ix0400.map fun i => (Pop.S0204.leaves.getD i dflt).1
theorem r0400_ok : ∀ p ∈ r0400, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0204.sem ix0400_lt

def ix0401 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66]
theorem ix0401_lt : ∀ i ∈ ix0401, i < Pop.S0205.leaves.length := by decide +kernel
def r0401 : List (List ℕ) := ix0401.map fun i => (Pop.S0205.leaves.getD i dflt).1
theorem r0401_ok : ∀ p ∈ r0401, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0205.sem ix0401_lt

def ix0402 : List ℕ := [68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81]
theorem ix0402_lt : ∀ i ∈ ix0402, i < Pop.S0204.leaves.length := by decide +kernel
def r0402 : List (List ℕ) := ix0402.map fun i => (Pop.S0204.leaves.getD i dflt).1
theorem r0402_ok : ∀ p ∈ r0402, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0204.sem ix0402_lt

def ix0403 : List ℕ := [67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
theorem ix0403_lt : ∀ i ∈ ix0403, i < Pop.S0205.leaves.length := by decide +kernel
def r0403 : List (List ℕ) := ix0403.map fun i => (Pop.S0205.leaves.getD i dflt).1
theorem r0403_ok : ∀ p ∈ r0403, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0205.sem ix0403_lt

def ix0404 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
theorem ix0404_lt : ∀ i ∈ ix0404, i < Pop.S0206.leaves.length := by decide +kernel
def r0404 : List (List ℕ) := ix0404.map fun i => (Pop.S0206.leaves.getD i dflt).1
theorem r0404_ok : ∀ p ∈ r0404, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0206.sem ix0404_lt

def ix0405 : List ℕ := [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92]
theorem ix0405_lt : ∀ i ∈ ix0405, i < Pop.S0204.leaves.length := by decide +kernel
def r0405 : List (List ℕ) := ix0405.map fun i => (Pop.S0204.leaves.getD i dflt).1
theorem r0405_ok : ∀ p ∈ r0405, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0204.sem ix0405_lt

def ix0406 : List ℕ := [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81]
theorem ix0406_lt : ∀ i ∈ ix0406, i < Pop.S0206.leaves.length := by decide +kernel
def r0406 : List (List ℕ) := ix0406.map fun i => (Pop.S0206.leaves.getD i dflt).1
theorem r0406_ok : ∀ p ∈ r0406, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0206.sem ix0406_lt

def ix0407 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88]
theorem ix0407_lt : ∀ i ∈ ix0407, i < Pop.S0207.leaves.length := by decide +kernel
def r0407 : List (List ℕ) := ix0407.map fun i => (Pop.S0207.leaves.getD i dflt).1
theorem r0407_ok : ∀ p ∈ r0407, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0207.sem ix0407_lt

def ix0408 : List ℕ := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52]
theorem ix0408_lt : ∀ i ∈ ix0408, i < Pop.S0208.leaves.length := by decide +kernel
def r0408 : List (List ℕ) := ix0408.map fun i => (Pop.S0208.leaves.getD i dflt).1
theorem r0408_ok : ∀ p ∈ r0408, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0208.sem ix0408_lt

def ix0409 : List ℕ := [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120]
theorem ix0409_lt : ∀ i ∈ ix0409, i < Pop.S0258.leaves.length := by decide +kernel
def r0409 : List (List ℕ) := ix0409.map fun i => (Pop.S0258.leaves.getD i dflt).1
theorem r0409_ok : ∀ p ∈ r0409, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0258.sem ix0409_lt

def ix0410 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91]
theorem ix0410_lt : ∀ i ∈ ix0410, i < Pop.S0259.leaves.length := by decide +kernel
def r0410 : List (List ℕ) := ix0410.map fun i => (Pop.S0259.leaves.getD i dflt).1
theorem r0410_ok : ∀ p ∈ r0410, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0259.sem ix0410_lt

def ix0411 : List ℕ := [108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118]
theorem ix0411_lt : ∀ i ∈ ix0411, i < Pop.S0264.leaves.length := by decide +kernel
def r0411 : List (List ℕ) := ix0411.map fun i => (Pop.S0264.leaves.getD i dflt).1
theorem r0411_ok : ∀ p ∈ r0411, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0264.sem ix0411_lt

def ix0412 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58]
theorem ix0412_lt : ∀ i ∈ ix0412, i < Pop.S0265.leaves.length := by decide +kernel
def r0412 : List (List ℕ) := ix0412.map fun i => (Pop.S0265.leaves.getD i dflt).1
theorem r0412_ok : ∀ p ∈ r0412, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0265.sem ix0412_lt

def ix0413 : List ℕ := [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86]
theorem ix0413_lt : ∀ i ∈ ix0413, i < Pop.S0273.leaves.length := by decide +kernel
def r0413 : List (List ℕ) := ix0413.map fun i => (Pop.S0273.leaves.getD i dflt).1
theorem r0413_ok : ∀ p ∈ r0413, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0273.sem ix0413_lt

def ix0414 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7]
theorem ix0414_lt : ∀ i ∈ ix0414, i < Pop.S0274.leaves.length := by decide +kernel
def r0414 : List (List ℕ) := ix0414.map fun i => (Pop.S0274.leaves.getD i dflt).1
theorem r0414_ok : ∀ p ∈ r0414, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0274.sem ix0414_lt

def ix0415 : List ℕ := [0]
theorem ix0415_lt : ∀ i ∈ ix0415, i < Pop.S0208.leaves.length := by decide +kernel
def r0415 : List (List ℕ) := ix0415.map fun i => (Pop.S0208.leaves.getD i dflt).1
theorem r0415_ok : ∀ p ∈ r0415, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0208.sem ix0415_lt

def ix0416 : List ℕ := [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56]
theorem ix0416_lt : ∀ i ∈ ix0416, i < Pop.S0211.leaves.length := by decide +kernel
def r0416 : List (List ℕ) := ix0416.map fun i => (Pop.S0211.leaves.getD i dflt).1
theorem r0416_ok : ∀ p ∈ r0416, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0211.sem ix0416_lt

def ix0417 : List ℕ := [53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]
theorem ix0417_lt : ∀ i ∈ ix0417, i < Pop.S0208.leaves.length := by decide +kernel
def r0417 : List (List ℕ) := ix0417.map fun i => (Pop.S0208.leaves.getD i dflt).1
theorem r0417_ok : ∀ p ∈ r0417, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0208.sem ix0417_lt

def ix0418 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82]
theorem ix0418_lt : ∀ i ∈ ix0418, i < Pop.S0209.leaves.length := by decide +kernel
def r0418 : List (List ℕ) := ix0418.map fun i => (Pop.S0209.leaves.getD i dflt).1
theorem r0418_ok : ∀ p ∈ r0418, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0209.sem ix0418_lt

def ix0419 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]
theorem ix0419_lt : ∀ i ∈ ix0419, i < Pop.S0210.leaves.length := by decide +kernel
def r0419 : List (List ℕ) := ix0419.map fun i => (Pop.S0210.leaves.getD i dflt).1
theorem r0419_ok : ∀ p ∈ r0419, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0210.sem ix0419_lt

def ix0420 : List ℕ := [6, 7, 8, 9, 10, 11, 12, 13, 97, 98, 99, 100]
theorem ix0420_lt : ∀ i ∈ ix0420, i < Pop.S0211.leaves.length := by decide +kernel
def r0420 : List (List ℕ) := ix0420.map fun i => (Pop.S0211.leaves.getD i dflt).1
theorem r0420_ok : ∀ p ∈ r0420, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0211.sem ix0420_lt

def ix0421 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45]
theorem ix0421_lt : ∀ i ∈ ix0421, i < Pop.S0212.leaves.length := by decide +kernel
def r0421 : List (List ℕ) := ix0421.map fun i => (Pop.S0212.leaves.getD i dflt).1
theorem r0421_ok : ∀ p ∈ r0421, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0212.sem ix0421_lt

def ix0422 : List ℕ := [53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112]
theorem ix0422_lt : ∀ i ∈ ix0422, i < Pop.S0236.leaves.length := by decide +kernel
def r0422 : List (List ℕ) := ix0422.map fun i => (Pop.S0236.leaves.getD i dflt).1
theorem r0422_ok : ∀ p ∈ r0422, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0236.sem ix0422_lt

def ix0423 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113]
theorem ix0423_lt : ∀ i ∈ ix0423, i < Pop.S0237.leaves.length := by decide +kernel
def r0423 : List (List ℕ) := ix0423.map fun i => (Pop.S0237.leaves.getD i dflt).1
theorem r0423_ok : ∀ p ∈ r0423, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0237.sem ix0423_lt

def ix0424 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]
theorem ix0424_lt : ∀ i ∈ ix0424, i < Pop.S0238.leaves.length := by decide +kernel
def r0424 : List (List ℕ) := ix0424.map fun i => (Pop.S0238.leaves.getD i dflt).1
theorem r0424_ok : ∀ p ∈ r0424, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0238.sem ix0424_lt

def ix0425 : List ℕ := [80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135]
theorem ix0425_lt : ∀ i ∈ ix0425, i < Pop.S0240.leaves.length := by decide +kernel
def r0425 : List (List ℕ) := ix0425.map fun i => (Pop.S0240.leaves.getD i dflt).1
theorem r0425_ok : ∀ p ∈ r0425, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0240.sem ix0425_lt

def ix0426 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36]
theorem ix0426_lt : ∀ i ∈ ix0426, i < Pop.S0241.leaves.length := by decide +kernel
def r0426 : List (List ℕ) := ix0426.map fun i => (Pop.S0241.leaves.getD i dflt).1
theorem r0426_ok : ∀ p ∈ r0426, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0241.sem ix0426_lt

def ix0427 : List ℕ := [71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105]
theorem ix0427_lt : ∀ i ∈ ix0427, i < Pop.S0243.leaves.length := by decide +kernel
def r0427 : List (List ℕ) := ix0427.map fun i => (Pop.S0243.leaves.getD i dflt).1
theorem r0427_ok : ∀ p ∈ r0427, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0243.sem ix0427_lt

def ix0428 : List ℕ := [30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88]
theorem ix0428_lt : ∀ i ∈ ix0428, i < Pop.S0254.leaves.length := by decide +kernel
def r0428 : List (List ℕ) := ix0428.map fun i => (Pop.S0254.leaves.getD i dflt).1
theorem r0428_ok : ∀ p ∈ r0428, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0254.sem ix0428_lt

def ix0429 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39]
theorem ix0429_lt : ∀ i ∈ ix0429, i < Pop.S0255.leaves.length := by decide +kernel
def r0429 : List (List ℕ) := ix0429.map fun i => (Pop.S0255.leaves.getD i dflt).1
theorem r0429_ok : ∀ p ∈ r0429, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0255.sem ix0429_lt

def ix0430 : List ℕ := [39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85]
theorem ix0430_lt : ∀ i ∈ ix0430, i < Pop.S0256.leaves.length := by decide +kernel
def r0430 : List (List ℕ) := ix0430.map fun i => (Pop.S0256.leaves.getD i dflt).1
theorem r0430_ok : ∀ p ∈ r0430, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0256.sem ix0430_lt

def ix0431 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]
theorem ix0431_lt : ∀ i ∈ ix0431, i < Pop.S0257.leaves.length := by decide +kernel
def r0431 : List (List ℕ) := ix0431.map fun i => (Pop.S0257.leaves.getD i dflt).1
theorem r0431_ok : ∀ p ∈ r0431, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0257.sem ix0431_lt

def ix0432 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]
theorem ix0432_lt : ∀ i ∈ ix0432, i < Pop.S0258.leaves.length := by decide +kernel
def r0432 : List (List ℕ) := ix0432.map fun i => (Pop.S0258.leaves.getD i dflt).1
theorem r0432_ok : ∀ p ∈ r0432, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0258.sem ix0432_lt

def ix0433 : List ℕ := [92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]
theorem ix0433_lt : ∀ i ∈ ix0433, i < Pop.S0259.leaves.length := by decide +kernel
def r0433 : List (List ℕ) := ix0433.map fun i => (Pop.S0259.leaves.getD i dflt).1
theorem r0433_ok : ∀ p ∈ r0433, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0259.sem ix0433_lt

def ix0434 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]
theorem ix0434_lt : ∀ i ∈ ix0434, i < Pop.S0260.leaves.length := by decide +kernel
def r0434 : List (List ℕ) := ix0434.map fun i => (Pop.S0260.leaves.getD i dflt).1
theorem r0434_ok : ∀ p ∈ r0434, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0260.sem ix0434_lt

def ix0435 : List ℕ := [30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140]
theorem ix0435_lt : ∀ i ∈ ix0435, i < Pop.S0239.leaves.length := by decide +kernel
def r0435 : List (List ℕ) := ix0435.map fun i => (Pop.S0239.leaves.getD i dflt).1
theorem r0435_ok : ∀ p ∈ r0435, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0239.sem ix0435_lt

def ix0436 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]
theorem ix0436_lt : ∀ i ∈ ix0436, i < Pop.S0240.leaves.length := by decide +kernel
def r0436 : List (List ℕ) := ix0436.map fun i => (Pop.S0240.leaves.getD i dflt).1
theorem r0436_ok : ∀ p ∈ r0436, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0240.sem ix0436_lt

def ix0437 : List ℕ := [111, 112, 113, 114, 115, 116, 117]
theorem ix0437_lt : ∀ i ∈ ix0437, i < Pop.S0243.leaves.length := by decide +kernel
def r0437 : List (List ℕ) := ix0437.map fun i => (Pop.S0243.leaves.getD i dflt).1
theorem r0437_ok : ∀ p ∈ r0437, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0243.sem ix0437_lt

def ix0438 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85]
theorem ix0438_lt : ∀ i ∈ ix0438, i < Pop.S0244.leaves.length := by decide +kernel
def r0438 : List (List ℕ) := ix0438.map fun i => (Pop.S0244.leaves.getD i dflt).1
theorem r0438_ok : ∀ p ∈ r0438, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0244.sem ix0438_lt

def ix0439 : List ℕ := [37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122]
theorem ix0439_lt : ∀ i ∈ ix0439, i < Pop.S0241.leaves.length := by decide +kernel
def r0439 : List (List ℕ) := ix0439.map fun i => (Pop.S0241.leaves.getD i dflt).1
theorem r0439_ok : ∀ p ∈ r0439, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0241.sem ix0439_lt

def ix0440 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135]
theorem ix0440_lt : ∀ i ∈ ix0440, i < Pop.S0242.leaves.length := by decide +kernel
def r0440 : List (List ℕ) := ix0440.map fun i => (Pop.S0242.leaves.getD i dflt).1
theorem r0440_ok : ∀ p ∈ r0440, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0242.sem ix0440_lt

def ix0441 : List ℕ := [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]
theorem ix0441_lt : ∀ i ∈ ix0441, i < Pop.S0244.leaves.length := by decide +kernel
def r0441 : List (List ℕ) := ix0441.map fun i => (Pop.S0244.leaves.getD i dflt).1
theorem r0441_ok : ∀ p ∈ r0441, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0244.sem ix0441_lt

def ix0442 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
theorem ix0442_lt : ∀ i ∈ ix0442, i < Pop.S0245.leaves.length := by decide +kernel
def r0442 : List (List ℕ) := ix0442.map fun i => (Pop.S0245.leaves.getD i dflt).1
theorem r0442_ok : ∀ p ∈ r0442, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0245.sem ix0442_lt

def ix0443 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]
theorem ix0443_lt : ∀ i ∈ ix0443, i < Pop.S0246.leaves.length := by decide +kernel
def r0443 : List (List ℕ) := ix0443.map fun i => (Pop.S0246.leaves.getD i dflt).1
theorem r0443_ok : ∀ p ∈ r0443, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0246.sem ix0443_lt

def ix0444 : List ℕ := [68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130]
theorem ix0444_lt : ∀ i ∈ ix0444, i < Pop.S0249.leaves.length := by decide +kernel
def r0444 : List (List ℕ) := ix0444.map fun i => (Pop.S0249.leaves.getD i dflt).1
theorem r0444_ok : ∀ p ∈ r0444, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0249.sem ix0444_lt

def ix0445 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94]
theorem ix0445_lt : ∀ i ∈ ix0445, i < Pop.S0250.leaves.length := by decide +kernel
def r0445 : List (List ℕ) := ix0445.map fun i => (Pop.S0250.leaves.getD i dflt).1
theorem r0445_ok : ∀ p ∈ r0445, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0250.sem ix0445_lt

def ix0446 : List ℕ := [93, 94, 95, 96, 97, 98]
theorem ix0446_lt : ∀ i ∈ ix0446, i < Pop.S0248.leaves.length := by decide +kernel
def r0446 : List (List ℕ) := ix0446.map fun i => (Pop.S0248.leaves.getD i dflt).1
theorem r0446_ok : ∀ p ∈ r0446, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0248.sem ix0446_lt

def ix0447 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67]
theorem ix0447_lt : ∀ i ∈ ix0447, i < Pop.S0249.leaves.length := by decide +kernel
def r0447 : List (List ℕ) := ix0447.map fun i => (Pop.S0249.leaves.getD i dflt).1
theorem r0447_ok : ∀ p ∈ r0447, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0249.sem ix0447_lt

def ix0448 : List ℕ := [136]
theorem ix0448_lt : ∀ i ∈ ix0448, i < Pop.S0242.leaves.length := by decide +kernel
def r0448 : List (List ℕ) := ix0448.map fun i => (Pop.S0242.leaves.getD i dflt).1
theorem r0448_ok : ∀ p ∈ r0448, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0242.sem ix0448_lt

def ix0449 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 106, 107, 108, 109, 110]
theorem ix0449_lt : ∀ i ∈ ix0449, i < Pop.S0243.leaves.length := by decide +kernel
def r0449 : List (List ℕ) := ix0449.map fun i => (Pop.S0243.leaves.getD i dflt).1
theorem r0449_ok : ∀ p ∈ r0449, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0243.sem ix0449_lt

def ix0450 : List ℕ := [86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114]
theorem ix0450_lt : ∀ i ∈ ix0450, i < Pop.S0244.leaves.length := by decide +kernel
def r0450 : List (List ℕ) := ix0450.map fun i => (Pop.S0244.leaves.getD i dflt).1
theorem r0450_ok : ∀ p ∈ r0450, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0244.sem ix0450_lt

def ix0451 : List ℕ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]
theorem ix0451_lt : ∀ i ∈ ix0451, i < Pop.S0246.leaves.length := by decide +kernel
def r0451 : List (List ℕ) := ix0451.map fun i => (Pop.S0246.leaves.getD i dflt).1
theorem r0451_ok : ∀ p ∈ r0451, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0246.sem ix0451_lt

def ix0452 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85]
theorem ix0452_lt : ∀ i ∈ ix0452, i < Pop.S0247.leaves.length := by decide +kernel
def r0452 : List (List ℕ) := ix0452.map fun i => (Pop.S0247.leaves.getD i dflt).1
theorem r0452_ok : ∀ p ∈ r0452, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0247.sem ix0452_lt

def ix0453 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92]
theorem ix0453_lt : ∀ i ∈ ix0453, i < Pop.S0248.leaves.length := by decide +kernel
def r0453 : List (List ℕ) := ix0453.map fun i => (Pop.S0248.leaves.getD i dflt).1
theorem r0453_ok : ∀ p ∈ r0453, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0248.sem ix0453_lt

def ix0454 : List ℕ := [95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]
theorem ix0454_lt : ∀ i ∈ ix0454, i < Pop.S0250.leaves.length := by decide +kernel
def r0454 : List (List ℕ) := ix0454.map fun i => (Pop.S0250.leaves.getD i dflt).1
theorem r0454_ok : ∀ p ∈ r0454, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0250.sem ix0454_lt

def ix0455 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]
theorem ix0455_lt : ∀ i ∈ ix0455, i < Pop.S0251.leaves.length := by decide +kernel
def r0455 : List (List ℕ) := ix0455.map fun i => (Pop.S0251.leaves.getD i dflt).1
theorem r0455_ok : ∀ p ∈ r0455, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0251.sem ix0455_lt

def ix0456 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113]
theorem ix0456_lt : ∀ i ∈ ix0456, i < Pop.S0252.leaves.length := by decide +kernel
def r0456 : List (List ℕ) := ix0456.map fun i => (Pop.S0252.leaves.getD i dflt).1
theorem r0456_ok : ∀ p ∈ r0456, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0252.sem ix0456_lt

def ix0457 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75]
theorem ix0457_lt : ∀ i ∈ ix0457, i < Pop.S0253.leaves.length := by decide +kernel
def r0457 : List (List ℕ) := ix0457.map fun i => (Pop.S0253.leaves.getD i dflt).1
theorem r0457_ok : ∀ p ∈ r0457, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0253.sem ix0457_lt

def ix0458 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]
theorem ix0458_lt : ∀ i ∈ ix0458, i < Pop.S0254.leaves.length := by decide +kernel
def r0458 : List (List ℕ) := ix0458.map fun i => (Pop.S0254.leaves.getD i dflt).1
theorem r0458_ok : ∀ p ∈ r0458, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0254.sem ix0458_lt

def ix0459 : List ℕ := [40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91]
theorem ix0459_lt : ∀ i ∈ ix0459, i < Pop.S0255.leaves.length := by decide +kernel
def r0459 : List (List ℕ) := ix0459.map fun i => (Pop.S0255.leaves.getD i dflt).1
theorem r0459_ok : ∀ p ∈ r0459, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0255.sem ix0459_lt

def ix0460 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38]
theorem ix0460_lt : ∀ i ∈ ix0460, i < Pop.S0256.leaves.length := by decide +kernel
def r0460 : List (List ℕ) := ix0460.map fun i => (Pop.S0256.leaves.getD i dflt).1
theorem r0460_ok : ∀ p ∈ r0460, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0256.sem ix0460_lt

def ix0461 : List ℕ := [33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101]
theorem ix0461_lt : ∀ i ∈ ix0461, i < Pop.S0260.leaves.length := by decide +kernel
def r0461 : List (List ℕ) := ix0461.map fun i => (Pop.S0260.leaves.getD i dflt).1
theorem r0461_ok : ∀ p ∈ r0461, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0260.sem ix0461_lt

def ix0462 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108]
theorem ix0462_lt : ∀ i ∈ ix0462, i < Pop.S0261.leaves.length := by decide +kernel
def r0462 : List (List ℕ) := ix0462.map fun i => (Pop.S0261.leaves.getD i dflt).1
theorem r0462_ok : ∀ p ∈ r0462, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0261.sem ix0462_lt

def ix0463 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105]
theorem ix0463_lt : ∀ i ∈ ix0463, i < Pop.S0262.leaves.length := by decide +kernel
def r0463 : List (List ℕ) := ix0463.map fun i => (Pop.S0262.leaves.getD i dflt).1
theorem r0463_ok : ∀ p ∈ r0463, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0262.sem ix0463_lt

def ix0464 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
theorem ix0464_lt : ∀ i ∈ ix0464, i < Pop.S0263.leaves.length := by decide +kernel
def r0464 : List (List ℕ) := ix0464.map fun i => (Pop.S0263.leaves.getD i dflt).1
theorem r0464_ok : ∀ p ∈ r0464, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0263.sem ix0464_lt

def ix0465 : List ℕ := [102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]
theorem ix0465_lt : ∀ i ∈ ix0465, i < Pop.S0266.leaves.length := by decide +kernel
def r0465 : List (List ℕ) := ix0465.map fun i => (Pop.S0266.leaves.getD i dflt).1
theorem r0465_ok : ∀ p ∈ r0465, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0266.sem ix0465_lt

def ix0466 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80]
theorem ix0466_lt : ∀ i ∈ ix0466, i < Pop.S0267.leaves.length := by decide +kernel
def r0466 : List (List ℕ) := ix0466.map fun i => (Pop.S0267.leaves.getD i dflt).1
theorem r0466_ok : ∀ p ∈ r0466, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0267.sem ix0466_lt

def ix0467 : List ℕ := [92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106]
theorem ix0467_lt : ∀ i ∈ ix0467, i < Pop.S0297.leaves.length := by decide +kernel
def r0467 : List (List ℕ) := ix0467.map fun i => (Pop.S0297.leaves.getD i dflt).1
theorem r0467_ok : ∀ p ∈ r0467, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0297.sem ix0467_lt

def ix0468 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78]
theorem ix0468_lt : ∀ i ∈ ix0468, i < Pop.S0298.leaves.length := by decide +kernel
def r0468 : List (List ℕ) := ix0468.map fun i => (Pop.S0298.leaves.getD i dflt).1
theorem r0468_ok : ∀ p ∈ r0468, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0298.sem ix0468_lt

def ix0469 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43]
theorem ix0469_lt : ∀ i ∈ ix0469, i < Pop.S0299.leaves.length := by decide +kernel
def r0469 : List (List ℕ) := ix0469.map fun i => (Pop.S0299.leaves.getD i dflt).1
theorem r0469_ok : ∀ p ∈ r0469, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0299.sem ix0469_lt

def ix0470 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59]
theorem ix0470_lt : ∀ i ∈ ix0470, i < Pop.S0300.leaves.length := by decide +kernel
def r0470 : List (List ℕ) := ix0470.map fun i => (Pop.S0300.leaves.getD i dflt).1
theorem r0470_ok : ∀ p ∈ r0470, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0300.sem ix0470_lt

def ix0471 : List ℕ := [28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]
theorem ix0471_lt : ∀ i ∈ ix0471, i < Pop.S0263.leaves.length := by decide +kernel
def r0471 : List (List ℕ) := ix0471.map fun i => (Pop.S0263.leaves.getD i dflt).1
theorem r0471_ok : ∀ p ∈ r0471, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0263.sem ix0471_lt

def ix0472 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107]
theorem ix0472_lt : ∀ i ∈ ix0472, i < Pop.S0264.leaves.length := by decide +kernel
def r0472 : List (List ℕ) := ix0472.map fun i => (Pop.S0264.leaves.getD i dflt).1
theorem r0472_ok : ∀ p ∈ r0472, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0264.sem ix0472_lt

def ix0473 : List ℕ := [80, 81, 82, 83, 84, 85]
theorem ix0473_lt : ∀ i ∈ ix0473, i < Pop.S0265.leaves.length := by decide +kernel
def r0473 : List (List ℕ) := ix0473.map fun i => (Pop.S0265.leaves.getD i dflt).1
theorem r0473_ok : ∀ p ∈ r0473, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0265.sem ix0473_lt

def ix0474 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52]
theorem ix0474_lt : ∀ i ∈ ix0474, i < Pop.S0266.leaves.length := by decide +kernel
def r0474 : List (List ℕ) := ix0474.map fun i => (Pop.S0266.leaves.getD i dflt).1
theorem r0474_ok : ∀ p ∈ r0474, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0266.sem ix0474_lt

def ix0475 : List ℕ := [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108]
theorem ix0475_lt : ∀ i ∈ ix0475, i < Pop.S0276.leaves.length := by decide +kernel
def r0475 : List (List ℕ) := ix0475.map fun i => (Pop.S0276.leaves.getD i dflt).1
theorem r0475_ok : ∀ p ∈ r0475, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0276.sem ix0475_lt

def ix0476 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125]
theorem ix0476_lt : ∀ i ∈ ix0476, i < Pop.S0277.leaves.length := by decide +kernel
def r0476 : List (List ℕ) := ix0476.map fun i => (Pop.S0277.leaves.getD i dflt).1
theorem r0476_ok : ∀ p ∈ r0476, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0277.sem ix0476_lt

def ix0477 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
theorem ix0477_lt : ∀ i ∈ ix0477, i < Pop.S0278.leaves.length := by decide +kernel
def r0477 : List (List ℕ) := ix0477.map fun i => (Pop.S0278.leaves.getD i dflt).1
theorem r0477_ok : ∀ p ∈ r0477, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0278.sem ix0477_lt

def ix0478 : List ℕ := [34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112]
theorem ix0478_lt : ∀ i ∈ ix0478, i < Pop.S0210.leaves.length := by decide +kernel
def r0478 : List (List ℕ) := ix0478.map fun i => (Pop.S0210.leaves.getD i dflt).1
theorem r0478_ok : ∀ p ∈ r0478, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0210.sem ix0478_lt

def ix0479 : List ℕ := [0, 1, 2, 3, 4, 5, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96]
theorem ix0479_lt : ∀ i ∈ ix0479, i < Pop.S0211.leaves.length := by decide +kernel
def r0479 : List (List ℕ) := ix0479.map fun i => (Pop.S0211.leaves.getD i dflt).1
theorem r0479_ok : ∀ p ∈ r0479, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0211.sem ix0479_lt

def ix0480 : List ℕ := [46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109]
theorem ix0480_lt : ∀ i ∈ ix0480, i < Pop.S0212.leaves.length := by decide +kernel
def r0480 : List (List ℕ) := ix0480.map fun i => (Pop.S0212.leaves.getD i dflt).1
theorem r0480_ok : ∀ p ∈ r0480, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0212.sem ix0480_lt

def ix0481 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]
theorem ix0481_lt : ∀ i ∈ ix0481, i < Pop.S0213.leaves.length := by decide +kernel
def r0481 : List (List ℕ) := ix0481.map fun i => (Pop.S0213.leaves.getD i dflt).1
theorem r0481_ok : ∀ p ∈ r0481, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0213.sem ix0481_lt

def ix0482 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120]
theorem ix0482_lt : ∀ i ∈ ix0482, i < Pop.S0214.leaves.length := by decide +kernel
def r0482 : List (List ℕ) := ix0482.map fun i => (Pop.S0214.leaves.getD i dflt).1
theorem r0482_ok : ∀ p ∈ r0482, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0214.sem ix0482_lt

def ix0483 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80]
theorem ix0483_lt : ∀ i ∈ ix0483, i < Pop.S0215.leaves.length := by decide +kernel
def r0483 : List (List ℕ) := ix0483.map fun i => (Pop.S0215.leaves.getD i dflt).1
theorem r0483_ok : ∀ p ∈ r0483, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0215.sem ix0483_lt

def ix0484 : List ℕ := [76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107]
theorem ix0484_lt : ∀ i ∈ ix0484, i < Pop.S0216.leaves.length := by decide +kernel
def r0484 : List (List ℕ) := ix0484.map fun i => (Pop.S0216.leaves.getD i dflt).1
theorem r0484_ok : ∀ p ∈ r0484, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0216.sem ix0484_lt

def ix0485 : List ℕ := [33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72]
theorem ix0485_lt : ∀ i ∈ ix0485, i < Pop.S0223.leaves.length := by decide +kernel
def r0485 : List (List ℕ) := ix0485.map fun i => (Pop.S0223.leaves.getD i dflt).1
theorem r0485_ok : ∀ p ∈ r0485, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0223.sem ix0485_lt

def ix0486 : List ℕ := [45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121]
theorem ix0486_lt : ∀ i ∈ ix0486, i < Pop.S0225.leaves.length := by decide +kernel
def r0486 : List (List ℕ) := ix0486.map fun i => (Pop.S0225.leaves.getD i dflt).1
theorem r0486_ok : ∀ p ∈ r0486, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0225.sem ix0486_lt

def ix0487 : List ℕ := [81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130]
theorem ix0487_lt : ∀ i ∈ ix0487, i < Pop.S0215.leaves.length := by decide +kernel
def r0487 : List (List ℕ) := ix0487.map fun i => (Pop.S0215.leaves.getD i dflt).1
theorem r0487_ok : ∀ p ∈ r0487, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0215.sem ix0487_lt

def ix0488 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 108, 109, 110, 111]
theorem ix0488_lt : ∀ i ∈ ix0488, i < Pop.S0216.leaves.length := by decide +kernel
def r0488 : List (List ℕ) := ix0488.map fun i => (Pop.S0216.leaves.getD i dflt).1
theorem r0488_ok : ∀ p ∈ r0488, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0216.sem ix0488_lt

def ix0489 : List ℕ := [126, 127, 128, 129, 130, 131, 132, 133, 134]
theorem ix0489_lt : ∀ i ∈ ix0489, i < Pop.S0218.leaves.length := by decide +kernel
def r0489 : List (List ℕ) := ix0489.map fun i => (Pop.S0218.leaves.getD i dflt).1
theorem r0489_ok : ∀ p ∈ r0489, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0218.sem ix0489_lt

def ix0490 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44]
theorem ix0490_lt : ∀ i ∈ ix0490, i < Pop.S0219.leaves.length := by decide +kernel
def r0490 : List (List ℕ) := ix0490.map fun i => (Pop.S0219.leaves.getD i dflt).1
theorem r0490_ok : ∀ p ∈ r0490, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0219.sem ix0490_lt

def ix0491 : List ℕ := [58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]
theorem ix0491_lt : ∀ i ∈ ix0491, i < Pop.S0220.leaves.length := by decide +kernel
def r0491 : List (List ℕ) := ix0491.map fun i => (Pop.S0220.leaves.getD i dflt).1
theorem r0491_ok : ∀ p ∈ r0491, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0220.sem ix0491_lt

def ix0492 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140]
theorem ix0492_lt : ∀ i ∈ ix0492, i < Pop.S0221.leaves.length := by decide +kernel
def r0492 : List (List ℕ) := ix0492.map fun i => (Pop.S0221.leaves.getD i dflt).1
theorem r0492_ok : ∀ p ∈ r0492, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0221.sem ix0492_lt

def ix0493 : List ℕ := [0, 1, 2, 3, 4]
theorem ix0493_lt : ∀ i ∈ ix0493, i < Pop.S0222.leaves.length := by decide +kernel
def r0493 : List (List ℕ) := ix0493.map fun i => (Pop.S0222.leaves.getD i dflt).1
theorem r0493_ok : ∀ p ∈ r0493, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0222.sem ix0493_lt

def ix0494 : List ℕ := [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]
theorem ix0494_lt : ∀ i ∈ ix0494, i < Pop.S0223.leaves.length := by decide +kernel
def r0494 : List (List ℕ) := ix0494.map fun i => (Pop.S0223.leaves.getD i dflt).1
theorem r0494_ok : ∀ p ∈ r0494, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0223.sem ix0494_lt

def ix0495 : List ℕ := [143, 144, 145, 146]
theorem ix0495_lt : ∀ i ∈ ix0495, i < Pop.S0222.leaves.length := by decide +kernel
def r0495 : List (List ℕ) := ix0495.map fun i => (Pop.S0222.leaves.getD i dflt).1
theorem r0495_ok : ∀ p ∈ r0495, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0222.sem ix0495_lt

def ix0496 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
theorem ix0496_lt : ∀ i ∈ ix0496, i < Pop.S0223.leaves.length := by decide +kernel
def r0496 : List (List ℕ) := ix0496.map fun i => (Pop.S0223.leaves.getD i dflt).1
theorem r0496_ok : ∀ p ∈ r0496, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0223.sem ix0496_lt

def ix0497 : List ℕ := [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]
theorem ix0497_lt : ∀ i ∈ ix0497, i < Pop.S0216.leaves.length := by decide +kernel
def r0497 : List (List ℕ) := ix0497.map fun i => (Pop.S0216.leaves.getD i dflt).1
theorem r0497_ok : ∀ p ∈ r0497, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0216.sem ix0497_lt

def ix0498 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46]
theorem ix0498_lt : ∀ i ∈ ix0498, i < Pop.S0217.leaves.length := by decide +kernel
def r0498 : List (List ℕ) := ix0498.map fun i => (Pop.S0217.leaves.getD i dflt).1
theorem r0498_ok : ∀ p ∈ r0498, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0217.sem ix0498_lt

def ix0499 : List ℕ := [62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130]
theorem ix0499_lt : ∀ i ∈ ix0499, i < Pop.S0219.leaves.length := by decide +kernel
def r0499 : List (List ℕ) := ix0499.map fun i => (Pop.S0219.leaves.getD i dflt).1
theorem r0499_ok : ∀ p ∈ r0499, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0219.sem ix0499_lt

def ix0500 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57]
theorem ix0500_lt : ∀ i ∈ ix0500, i < Pop.S0220.leaves.length := by decide +kernel
def r0500 : List (List ℕ) := ix0500.map fun i => (Pop.S0220.leaves.getD i dflt).1
theorem r0500_ok : ∀ p ∈ r0500, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0220.sem ix0500_lt

def ix0501 : List ℕ := [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]
theorem ix0501_lt : ∀ i ∈ ix0501, i < Pop.S0225.leaves.length := by decide +kernel
def r0501 : List (List ℕ) := ix0501.map fun i => (Pop.S0225.leaves.getD i dflt).1
theorem r0501_ok : ∀ p ∈ r0501, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0225.sem ix0501_lt

def ix0502 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39]
theorem ix0502_lt : ∀ i ∈ ix0502, i < Pop.S0226.leaves.length := by decide +kernel
def r0502 : List (List ℕ) := ix0502.map fun i => (Pop.S0226.leaves.getD i dflt).1
theorem r0502_ok : ∀ p ∈ r0502, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0226.sem ix0502_lt

def ix0503 : List ℕ := [29, 30, 31, 32, 33, 34, 35]
theorem ix0503_lt : ∀ i ∈ ix0503, i < Pop.S0227.leaves.length := by decide +kernel
def r0503 : List (List ℕ) := ix0503.map fun i => (Pop.S0227.leaves.getD i dflt).1
theorem r0503_ok : ∀ p ∈ r0503, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0227.sem ix0503_lt

def ix0504 : List ℕ := [40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106]
theorem ix0504_lt : ∀ i ∈ ix0504, i < Pop.S0226.leaves.length := by decide +kernel
def r0504 : List (List ℕ) := ix0504.map fun i => (Pop.S0226.leaves.getD i dflt).1
theorem r0504_ok : ∀ p ∈ r0504, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0226.sem ix0504_lt

def ix0505 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115]
theorem ix0505_lt : ∀ i ∈ ix0505, i < Pop.S0227.leaves.length := by decide +kernel
def r0505 : List (List ℕ) := ix0505.map fun i => (Pop.S0227.leaves.getD i dflt).1
theorem r0505_ok : ∀ p ∈ r0505, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0227.sem ix0505_lt

def ix0506 : List ℕ := [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]
theorem ix0506_lt : ∀ i ∈ ix0506, i < Pop.S0231.leaves.length := by decide +kernel
def r0506 : List (List ℕ) := ix0506.map fun i => (Pop.S0231.leaves.getD i dflt).1
theorem r0506_ok : ∀ p ∈ r0506, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0231.sem ix0506_lt

def ix0507 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115]
theorem ix0507_lt : ∀ i ∈ ix0507, i < Pop.S0232.leaves.length := by decide +kernel
def r0507 : List (List ℕ) := ix0507.map fun i => (Pop.S0232.leaves.getD i dflt).1
theorem r0507_ok : ∀ p ∈ r0507, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0232.sem ix0507_lt

def ix0508 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36]
theorem ix0508_lt : ∀ i ∈ ix0508, i < Pop.S0233.leaves.length := by decide +kernel
def r0508 : List (List ℕ) := ix0508.map fun i => (Pop.S0233.leaves.getD i dflt).1
theorem r0508_ok : ∀ p ∈ r0508, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0233.sem ix0508_lt

def ix0509 : List ℕ := [17, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52]
theorem ix0509_lt : ∀ i ∈ ix0509, i < Pop.S0236.leaves.length := by decide +kernel
def r0509 : List (List ℕ) := ix0509.map fun i => (Pop.S0236.leaves.getD i dflt).1
theorem r0509_ok : ∀ p ∈ r0509, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0236.sem ix0509_lt

def ix0510 : List ℕ := [81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]
theorem ix0510_lt : ∀ i ∈ ix0510, i < Pop.S0238.leaves.length := by decide +kernel
def r0510 : List (List ℕ) := ix0510.map fun i => (Pop.S0238.leaves.getD i dflt).1
theorem r0510_ok : ∀ p ∈ r0510, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0238.sem ix0510_lt

def ix0511 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]
theorem ix0511_lt : ∀ i ∈ ix0511, i < Pop.S0239.leaves.length := by decide +kernel
def r0511 : List (List ℕ) := ix0511.map fun i => (Pop.S0239.leaves.getD i dflt).1
theorem r0511_ok : ∀ p ∈ r0511, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0239.sem ix0511_lt

def ix0512 : List ℕ := [47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]
theorem ix0512_lt : ∀ i ∈ ix0512, i < Pop.S0217.leaves.length := by decide +kernel
def r0512 : List (List ℕ) := ix0512.map fun i => (Pop.S0217.leaves.getD i dflt).1
theorem r0512_ok : ∀ p ∈ r0512, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0217.sem ix0512_lt

def ix0513 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125]
theorem ix0513_lt : ∀ i ∈ ix0513, i < Pop.S0218.leaves.length := by decide +kernel
def r0513 : List (List ℕ) := ix0513.map fun i => (Pop.S0218.leaves.getD i dflt).1
theorem r0513_ok : ∀ p ∈ r0513, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0218.sem ix0513_lt

def ix0514 : List ℕ := [45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61]
theorem ix0514_lt : ∀ i ∈ ix0514, i < Pop.S0219.leaves.length := by decide +kernel
def r0514 : List (List ℕ) := ix0514.map fun i => (Pop.S0219.leaves.getD i dflt).1
theorem r0514_ok : ∀ p ∈ r0514, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0219.sem ix0514_lt

def ix0515 : List ℕ := [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]
theorem ix0515_lt : ∀ i ∈ ix0515, i < Pop.S0222.leaves.length := by decide +kernel
def r0515 : List (List ℕ) := ix0515.map fun i => (Pop.S0222.leaves.getD i dflt).1
theorem r0515_ok : ∀ p ∈ r0515, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0222.sem ix0515_lt

def ix0516 : List ℕ := [73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]
theorem ix0516_lt : ∀ i ∈ ix0516, i < Pop.S0223.leaves.length := by decide +kernel
def r0516 : List (List ℕ) := ix0516.map fun i => (Pop.S0223.leaves.getD i dflt).1
theorem r0516_ok : ∀ p ∈ r0516, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0223.sem ix0516_lt

def ix0517 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130]
theorem ix0517_lt : ∀ i ∈ ix0517, i < Pop.S0224.leaves.length := by decide +kernel
def r0517 : List (List ℕ) := ix0517.map fun i => (Pop.S0224.leaves.getD i dflt).1
theorem r0517_ok : ∀ p ∈ r0517, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0224.sem ix0517_lt

def ix0518 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44]
theorem ix0518_lt : ∀ i ∈ ix0518, i < Pop.S0225.leaves.length := by decide +kernel
def r0518 : List (List ℕ) := ix0518.map fun i => (Pop.S0225.leaves.getD i dflt).1
theorem r0518_ok : ∀ p ∈ r0518, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0225.sem ix0518_lt

def ix0519 : List ℕ := [120, 121, 122, 123, 124, 125, 126, 127]
theorem ix0519_lt : ∀ i ∈ ix0519, i < Pop.S0228.leaves.length := by decide +kernel
def r0519 : List (List ℕ) := ix0519.map fun i => (Pop.S0228.leaves.getD i dflt).1
theorem r0519_ok : ∀ p ∈ r0519, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0228.sem ix0519_lt

def ix0520 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88]
theorem ix0520_lt : ∀ i ∈ ix0520, i < Pop.S0229.leaves.length := by decide +kernel
def r0520 : List (List ℕ) := ix0520.map fun i => (Pop.S0229.leaves.getD i dflt).1
theorem r0520_ok : ∀ p ∈ r0520, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0229.sem ix0520_lt

def ix0521 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]
theorem ix0521_lt : ∀ i ∈ ix0521, i < Pop.S0230.leaves.length := by decide +kernel
def r0521 : List (List ℕ) := ix0521.map fun i => (Pop.S0230.leaves.getD i dflt).1
theorem r0521_ok : ∀ p ∈ r0521, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0230.sem ix0521_lt

def ix0522 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
theorem ix0522_lt : ∀ i ∈ ix0522, i < Pop.S0231.leaves.length := by decide +kernel
def r0522 : List (List ℕ) := ix0522.map fun i => (Pop.S0231.leaves.getD i dflt).1
theorem r0522_ok : ∀ p ∈ r0522, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0231.sem ix0522_lt

def ix0523 : List ℕ := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]
theorem ix0523_lt : ∀ i ∈ ix0523, i < Pop.S0234.leaves.length := by decide +kernel
def r0523 : List (List ℕ) := ix0523.map fun i => (Pop.S0234.leaves.getD i dflt).1
theorem r0523_ok : ∀ p ∈ r0523, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0234.sem ix0523_lt

def ix0524 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]
theorem ix0524_lt : ∀ i ∈ ix0524, i < Pop.S0235.leaves.length := by decide +kernel
def r0524 : List (List ℕ) := ix0524.map fun i => (Pop.S0235.leaves.getD i dflt).1
theorem r0524_ok : ∀ p ∈ r0524, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0235.sem ix0524_lt

def ix0525 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
theorem ix0525_lt : ∀ i ∈ ix0525, i < Pop.S0236.leaves.length := by decide +kernel
def r0525 : List (List ℕ) := ix0525.map fun i => (Pop.S0236.leaves.getD i dflt).1
theorem r0525_ok : ∀ p ∈ r0525, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0236.sem ix0525_lt

def ix0526 : List ℕ := [116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]
theorem ix0526_lt : ∀ i ∈ ix0526, i < Pop.S0227.leaves.length := by decide +kernel
def r0526 : List (List ℕ) := ix0526.map fun i => (Pop.S0227.leaves.getD i dflt).1
theorem r0526_ok : ∀ p ∈ r0526, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0227.sem ix0526_lt

def ix0527 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119]
theorem ix0527_lt : ∀ i ∈ ix0527, i < Pop.S0228.leaves.length := by decide +kernel
def r0527 : List (List ℕ) := ix0527.map fun i => (Pop.S0228.leaves.getD i dflt).1
theorem r0527_ok : ∀ p ∈ r0527, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0228.sem ix0527_lt

def ix0528 : List ℕ := [37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]
theorem ix0528_lt : ∀ i ∈ ix0528, i < Pop.S0233.leaves.length := by decide +kernel
def r0528 : List (List ℕ) := ix0528.map fun i => (Pop.S0233.leaves.getD i dflt).1
theorem r0528_ok : ∀ p ∈ r0528, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0233.sem ix0528_lt

def ix0529 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119]
theorem ix0529_lt : ∀ i ∈ ix0529, i < Pop.S0234.leaves.length := by decide +kernel
def r0529 : List (List ℕ) := ix0529.map fun i => (Pop.S0234.leaves.getD i dflt).1
theorem r0529_ok : ∀ p ∈ r0529, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0234.sem ix0529_lt

def ix0530 : List ℕ := [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38]
theorem ix0530_lt : ∀ i ∈ ix0530, i < Pop.S0236.leaves.length := by decide +kernel
def r0530 : List (List ℕ) := ix0530.map fun i => (Pop.S0236.leaves.getD i dflt).1
theorem r0530_ok : ∀ p ∈ r0530, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0236.sem ix0530_lt

def ix0531 : List ℕ := [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80]
theorem ix0531_lt : ∀ i ∈ ix0531, i < Pop.S0238.leaves.length := by decide +kernel
def r0531 : List (List ℕ) := ix0531.map fun i => (Pop.S0238.leaves.getD i dflt).1
theorem r0531_ok : ∀ p ∈ r0531, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0238.sem ix0531_lt

def ix0532 : List ℕ := [59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]
theorem ix0532_lt : ∀ i ∈ ix0532, i < Pop.S0265.leaves.length := by decide +kernel
def r0532 : List (List ℕ) := ix0532.map fun i => (Pop.S0265.leaves.getD i dflt).1
theorem r0532_ok : ∀ p ∈ r0532, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0265.sem ix0532_lt

def ix0533 : List ℕ := [53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83]
theorem ix0533_lt : ∀ i ∈ ix0533, i < Pop.S0266.leaves.length := by decide +kernel
def r0533 : List (List ℕ) := ix0533.map fun i => (Pop.S0266.leaves.getD i dflt).1
theorem r0533_ok : ∀ p ∈ r0533, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0266.sem ix0533_lt

def ix0534 : List ℕ := [81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97]
theorem ix0534_lt : ∀ i ∈ ix0534, i < Pop.S0267.leaves.length := by decide +kernel
def r0534 : List (List ℕ) := ix0534.map fun i => (Pop.S0267.leaves.getD i dflt).1
theorem r0534_ok : ∀ p ∈ r0534, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0267.sem ix0534_lt

def ix0535 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93]
theorem ix0535_lt : ∀ i ∈ ix0535, i < Pop.S0268.leaves.length := by decide +kernel
def r0535 : List (List ℕ) := ix0535.map fun i => (Pop.S0268.leaves.getD i dflt).1
theorem r0535_ok : ∀ p ∈ r0535, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0268.sem ix0535_lt

def ix0536 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 100, 101, 102, 103, 104, 105, 106]
theorem ix0536_lt : ∀ i ∈ ix0536, i < Pop.S0269.leaves.length := by decide +kernel
def r0536 : List (List ℕ) := ix0536.map fun i => (Pop.S0269.leaves.getD i dflt).1
theorem r0536_ok : ∀ p ∈ r0536, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0269.sem ix0536_lt

def ix0537 : List ℕ := [74, 75, 76, 77, 78, 79, 80]
theorem ix0537_lt : ∀ i ∈ ix0537, i < Pop.S0272.leaves.length := by decide +kernel
def r0537 : List (List ℕ) := ix0537.map fun i => (Pop.S0272.leaves.getD i dflt).1
theorem r0537_ok : ∀ p ∈ r0537, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0272.sem ix0537_lt

def ix0538 : List ℕ := [108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]
theorem ix0538_lt : ∀ i ∈ ix0538, i < Pop.S0275.leaves.length := by decide +kernel
def r0538 : List (List ℕ) := ix0538.map fun i => (Pop.S0275.leaves.getD i dflt).1
theorem r0538_ok : ∀ p ∈ r0538, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0275.sem ix0538_lt

def ix0539 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57]
theorem ix0539_lt : ∀ i ∈ ix0539, i < Pop.S0276.leaves.length := by decide +kernel
def r0539 : List (List ℕ) := ix0539.map fun i => (Pop.S0276.leaves.getD i dflt).1
theorem r0539_ok : ∀ p ∈ r0539, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0276.sem ix0539_lt

def ix0540 : List ℕ := [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99]
theorem ix0540_lt : ∀ i ∈ ix0540, i < Pop.S0269.leaves.length := by decide +kernel
def r0540 : List (List ℕ) := ix0540.map fun i => (Pop.S0269.leaves.getD i dflt).1
theorem r0540_ok : ∀ p ∈ r0540, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0269.sem ix0540_lt

def ix0541 : List ℕ := [80, 81, 82, 83, 84]
theorem ix0541_lt : ∀ i ∈ ix0541, i < Pop.S0271.leaves.length := by decide +kernel
def r0541 : List (List ℕ) := ix0541.map fun i => (Pop.S0271.leaves.getD i dflt).1
theorem r0541_ok : ∀ p ∈ r0541, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0271.sem ix0541_lt

def ix0542 : List ℕ := [81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]
theorem ix0542_lt : ∀ i ∈ ix0542, i < Pop.S0272.leaves.length := by decide +kernel
def r0542 : List (List ℕ) := ix0542.map fun i => (Pop.S0272.leaves.getD i dflt).1
theorem r0542_ok : ∀ p ∈ r0542, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0272.sem ix0542_lt

def ix0543 : List ℕ := [0, 1, 2, 3]
theorem ix0543_lt : ∀ i ∈ ix0543, i < Pop.S0273.leaves.length := by decide +kernel
def r0543 : List (List ℕ) := ix0543.map fun i => (Pop.S0273.leaves.getD i dflt).1
theorem r0543_ok : ∀ p ∈ r0543, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0273.sem ix0543_lt

def ix0544 : List ℕ := [107, 108, 109, 110, 111]
theorem ix0544_lt : ∀ i ∈ ix0544, i < Pop.S0269.leaves.length := by decide +kernel
def r0544 : List (List ℕ) := ix0544.map fun i => (Pop.S0269.leaves.getD i dflt).1
theorem r0544_ok : ∀ p ∈ r0544, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0269.sem ix0544_lt

def ix0545 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]
theorem ix0545_lt : ∀ i ∈ ix0545, i < Pop.S0270.leaves.length := by decide +kernel
def r0545 : List (List ℕ) := ix0545.map fun i => (Pop.S0270.leaves.getD i dflt).1
theorem r0545_ok : ∀ p ∈ r0545, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0270.sem ix0545_lt

def ix0546 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113]
theorem ix0546_lt : ∀ i ∈ ix0546, i < Pop.S0271.leaves.length := by decide +kernel
def r0546 : List (List ℕ) := ix0546.map fun i => (Pop.S0271.leaves.getD i dflt).1
theorem r0546_ok : ∀ p ∈ r0546, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0271.sem ix0546_lt

def ix0547 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73]
theorem ix0547_lt : ∀ i ∈ ix0547, i < Pop.S0272.leaves.length := by decide +kernel
def r0547 : List (List ℕ) := ix0547.map fun i => (Pop.S0272.leaves.getD i dflt).1
theorem r0547_ok : ∀ p ∈ r0547, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0272.sem ix0547_lt

def ix0548 : List ℕ := [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84]
theorem ix0548_lt : ∀ i ∈ ix0548, i < Pop.S0274.leaves.length := by decide +kernel
def r0548 : List (List ℕ) := ix0548.map fun i => (Pop.S0274.leaves.getD i dflt).1
theorem r0548_ok : ∀ p ∈ r0548, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0274.sem ix0548_lt

def ix0549 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107]
theorem ix0549_lt : ∀ i ∈ ix0549, i < Pop.S0275.leaves.length := by decide +kernel
def r0549 : List (List ℕ) := ix0549.map fun i => (Pop.S0275.leaves.getD i dflt).1
theorem r0549_ok : ∀ p ∈ r0549, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0275.sem ix0549_lt

def ix0550 : List ℕ := [58, 59, 60, 61, 62, 63, 64, 65]
theorem ix0550_lt : ∀ i ∈ ix0550, i < Pop.S0276.leaves.length := by decide +kernel
def r0550 : List (List ℕ) := ix0550.map fun i => (Pop.S0276.leaves.getD i dflt).1
theorem r0550_ok : ∀ p ∈ r0550, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0276.sem ix0550_lt

def ix0551 : List ℕ := [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52]
theorem ix0551_lt : ∀ i ∈ ix0551, i < Pop.S0268.leaves.length := by decide +kernel
def r0551 : List (List ℕ) := ix0551.map fun i => (Pop.S0268.leaves.getD i dflt).1
theorem r0551_ok : ∀ p ∈ r0551, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0268.sem ix0551_lt

def ix0552 : List ℕ := [4, 5, 6, 7]
theorem ix0552_lt : ∀ i ∈ ix0552, i < Pop.S0273.leaves.length := by decide +kernel
def r0552 : List (List ℕ) := ix0552.map fun i => (Pop.S0273.leaves.getD i dflt).1
theorem r0552_ok : ∀ p ∈ r0552, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0273.sem ix0552_lt

def ix0553 : List ℕ := [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45]
theorem ix0553_lt : ∀ i ∈ ix0553, i < Pop.S0277.leaves.length := by decide +kernel
def r0553 : List (List ℕ) := ix0553.map fun i => (Pop.S0277.leaves.getD i dflt).1
theorem r0553_ok : ∀ p ∈ r0553, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0277.sem ix0553_lt

def ix0554 : List ℕ := [24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70]
theorem ix0554_lt : ∀ i ∈ ix0554, i < Pop.S0278.leaves.length := by decide +kernel
def r0554 : List (List ℕ) := ix0554.map fun i => (Pop.S0278.leaves.getD i dflt).1
theorem r0554_ok : ∀ p ∈ r0554, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0278.sem ix0554_lt

def ix0555 : List ℕ := [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96]
theorem ix0555_lt : ∀ i ∈ ix0555, i < Pop.S0279.leaves.length := by decide +kernel
def r0555 : List (List ℕ) := ix0555.map fun i => (Pop.S0279.leaves.getD i dflt).1
theorem r0555_ok : ∀ p ∈ r0555, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0279.sem ix0555_lt

def ix0556 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 81, 82, 83, 84, 85, 86, 87, 88]
theorem ix0556_lt : ∀ i ∈ ix0556, i < Pop.S0280.leaves.length := by decide +kernel
def r0556 : List (List ℕ) := ix0556.map fun i => (Pop.S0280.leaves.getD i dflt).1
theorem r0556_ok : ∀ p ∈ r0556, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0280.sem ix0556_lt

def ix0557 : List ℕ := [39]
theorem ix0557_lt : ∀ i ∈ ix0557, i < Pop.S0294.leaves.length := by decide +kernel
def r0557 : List (List ℕ) := ix0557.map fun i => (Pop.S0294.leaves.getD i dflt).1
theorem r0557_ok : ∀ p ∈ r0557, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0294.sem ix0557_lt

def ix0558 : List ℕ := [71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105]
theorem ix0558_lt : ∀ i ∈ ix0558, i < Pop.S0278.leaves.length := by decide +kernel
def r0558 : List (List ℕ) := ix0558.map fun i => (Pop.S0278.leaves.getD i dflt).1
theorem r0558_ok : ∀ p ∈ r0558, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0278.sem ix0558_lt

def ix0559 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81]
theorem ix0559_lt : ∀ i ∈ ix0559, i < Pop.S0279.leaves.length := by decide +kernel
def r0559 : List (List ℕ) := ix0559.map fun i => (Pop.S0279.leaves.getD i dflt).1
theorem r0559_ok : ∀ p ∈ r0559, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0279.sem ix0559_lt

def ix0560 : List ℕ := [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 89, 90]
theorem ix0560_lt : ∀ i ∈ ix0560, i < Pop.S0280.leaves.length := by decide +kernel
def r0560 : List (List ℕ) := ix0560.map fun i => (Pop.S0280.leaves.getD i dflt).1
theorem r0560_ok : ∀ p ∈ r0560, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0280.sem ix0560_lt

def ix0561 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86]
theorem ix0561_lt : ∀ i ∈ ix0561, i < Pop.S0281.leaves.length := by decide +kernel
def r0561 : List (List ℕ) := ix0561.map fun i => (Pop.S0281.leaves.getD i dflt).1
theorem r0561_ok : ∀ p ∈ r0561, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0281.sem ix0561_lt

def ix0562 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105]
theorem ix0562_lt : ∀ i ∈ ix0562, i < Pop.S0282.leaves.length := by decide +kernel
def r0562 : List (List ℕ) := ix0562.map fun i => (Pop.S0282.leaves.getD i dflt).1
theorem r0562_ok : ∀ p ∈ r0562, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0282.sem ix0562_lt

def ix0563 : List ℕ := [55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84]
theorem ix0563_lt : ∀ i ∈ ix0563, i < Pop.S0283.leaves.length := by decide +kernel
def r0563 : List (List ℕ) := ix0563.map fun i => (Pop.S0283.leaves.getD i dflt).1
theorem r0563_ok : ∀ p ∈ r0563, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0283.sem ix0563_lt

def ix0564 : List ℕ := [106, 107, 108, 109, 110, 111, 112]
theorem ix0564_lt : ∀ i ∈ ix0564, i < Pop.S0282.leaves.length := by decide +kernel
def r0564 : List (List ℕ) := ix0564.map fun i => (Pop.S0282.leaves.getD i dflt).1
theorem r0564_ok : ∀ p ∈ r0564, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0282.sem ix0564_lt

def ix0565 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 85, 86]
theorem ix0565_lt : ∀ i ∈ ix0565, i < Pop.S0283.leaves.length := by decide +kernel
def r0565 : List (List ℕ) := ix0565.map fun i => (Pop.S0283.leaves.getD i dflt).1
theorem r0565_ok : ∀ p ∈ r0565, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0283.sem ix0565_lt

def ix0566 : List ℕ := [68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110]
theorem ix0566_lt : ∀ i ∈ ix0566, i < Pop.S0285.leaves.length := by decide +kernel
def r0566 : List (List ℕ) := ix0566.map fun i => (Pop.S0285.leaves.getD i dflt).1
theorem r0566_ok : ∀ p ∈ r0566, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0285.sem ix0566_lt

def ix0567 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
theorem ix0567_lt : ∀ i ∈ ix0567, i < Pop.S0286.leaves.length := by decide +kernel
def r0567 : List (List ℕ) := ix0567.map fun i => (Pop.S0286.leaves.getD i dflt).1
theorem r0567_ok : ∀ p ∈ r0567, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0286.sem ix0567_lt

def ix0568 : List ℕ := [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94]
theorem ix0568_lt : ∀ i ∈ ix0568, i < Pop.S0291.leaves.length := by decide +kernel
def r0568 : List (List ℕ) := ix0568.map fun i => (Pop.S0291.leaves.getD i dflt).1
theorem r0568_ok : ∀ p ∈ r0568, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0291.sem ix0568_lt

def ix0569 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56]
theorem ix0569_lt : ∀ i ∈ ix0569, i < Pop.S0292.leaves.length := by decide +kernel
def r0569 : List (List ℕ) := ix0569.map fun i => (Pop.S0292.leaves.getD i dflt).1
theorem r0569_ok : ∀ p ∈ r0569, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0292.sem ix0569_lt

def ix0570 : List ℕ := [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109]
theorem ix0570_lt : ∀ i ∈ ix0570, i < Pop.S0294.leaves.length := by decide +kernel
def r0570 : List (List ℕ) := ix0570.map fun i => (Pop.S0294.leaves.getD i dflt).1
theorem r0570_ok : ∀ p ∈ r0570, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0294.sem ix0570_lt

def ix0571 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
theorem ix0571_lt : ∀ i ∈ ix0571, i < Pop.S0295.leaves.length := by decide +kernel
def r0571 : List (List ℕ) := ix0571.map fun i => (Pop.S0295.leaves.getD i dflt).1
theorem r0571_ok : ∀ p ∈ r0571, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0295.sem ix0571_lt

def ix0572 : List ℕ := [87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101]
theorem ix0572_lt : ∀ i ∈ ix0572, i < Pop.S0283.leaves.length := by decide +kernel
def r0572 : List (List ℕ) := ix0572.map fun i => (Pop.S0283.leaves.getD i dflt).1
theorem r0572_ok : ∀ p ∈ r0572, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0283.sem ix0572_lt

def ix0573 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]
theorem ix0573_lt : ∀ i ∈ ix0573, i < Pop.S0284.leaves.length := by decide +kernel
def r0573 : List (List ℕ) := ix0573.map fun i => (Pop.S0284.leaves.getD i dflt).1
theorem r0573_ok : ∀ p ∈ r0573, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0284.sem ix0573_lt

def ix0574 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67]
theorem ix0574_lt : ∀ i ∈ ix0574, i < Pop.S0285.leaves.length := by decide +kernel
def r0574 : List (List ℕ) := ix0574.map fun i => (Pop.S0285.leaves.getD i dflt).1
theorem r0574_ok : ∀ p ∈ r0574, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0285.sem ix0574_lt

def ix0575 : List ℕ := [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77]
theorem ix0575_lt : ∀ i ∈ ix0575, i < Pop.S0286.leaves.length := by decide +kernel
def r0575 : List (List ℕ) := ix0575.map fun i => (Pop.S0286.leaves.getD i dflt).1
theorem r0575_ok : ∀ p ∈ r0575, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0286.sem ix0575_lt

def ix0576 : List ℕ := [69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]
theorem ix0576_lt : ∀ i ∈ ix0576, i < Pop.S0288.leaves.length := by decide +kernel
def r0576 : List (List ℕ) := ix0576.map fun i => (Pop.S0288.leaves.getD i dflt).1
theorem r0576_ok : ∀ p ∈ r0576, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0288.sem ix0576_lt

def ix0577 : List ℕ := [46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140]
theorem ix0577_lt : ∀ i ∈ ix0577, i < Pop.S0289.leaves.length := by decide +kernel
def r0577 : List (List ℕ) := ix0577.map fun i => (Pop.S0289.leaves.getD i dflt).1
theorem r0577_ok : ∀ p ∈ r0577, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0289.sem ix0577_lt

def ix0578 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]
theorem ix0578_lt : ∀ i ∈ ix0578, i < Pop.S0290.leaves.length := by decide +kernel
def r0578 : List (List ℕ) := ix0578.map fun i => (Pop.S0290.leaves.getD i dflt).1
theorem r0578_ok : ∀ p ∈ r0578, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0290.sem ix0578_lt

def ix0579 : List ℕ := [78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96]
theorem ix0579_lt : ∀ i ∈ ix0579, i < Pop.S0286.leaves.length := by decide +kernel
def r0579 : List (List ℕ) := ix0579.map fun i => (Pop.S0286.leaves.getD i dflt).1
theorem r0579_ok : ∀ p ∈ r0579, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0286.sem ix0579_lt

def ix0580 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]
theorem ix0580_lt : ∀ i ∈ ix0580, i < Pop.S0287.leaves.length := by decide +kernel
def r0580 : List (List ℕ) := ix0580.map fun i => (Pop.S0287.leaves.getD i dflt).1
theorem r0580_ok : ∀ p ∈ r0580, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0287.sem ix0580_lt

def ix0581 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 133, 134, 135, 136, 137, 138, 139]
theorem ix0581_lt : ∀ i ∈ ix0581, i < Pop.S0288.leaves.length := by decide +kernel
def r0581 : List (List ℕ) := ix0581.map fun i => (Pop.S0288.leaves.getD i dflt).1
theorem r0581_ok : ∀ p ∈ r0581, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0288.sem ix0581_lt

def ix0582 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45]
theorem ix0582_lt : ∀ i ∈ ix0582, i < Pop.S0289.leaves.length := by decide +kernel
def r0582 : List (List ℕ) := ix0582.map fun i => (Pop.S0289.leaves.getD i dflt).1
theorem r0582_ok : ∀ p ∈ r0582, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0289.sem ix0582_lt

def ix0583 : List ℕ := [57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91]
theorem ix0583_lt : ∀ i ∈ ix0583, i < Pop.S0292.leaves.length := by decide +kernel
def r0583 : List (List ℕ) := ix0583.map fun i => (Pop.S0292.leaves.getD i dflt).1
theorem r0583_ok : ∀ p ∈ r0583, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0292.sem ix0583_lt

def ix0584 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98]
theorem ix0584_lt : ∀ i ∈ ix0584, i < Pop.S0293.leaves.length := by decide +kernel
def r0584 : List (List ℕ) := ix0584.map fun i => (Pop.S0293.leaves.getD i dflt).1
theorem r0584_ok : ∀ p ∈ r0584, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0293.sem ix0584_lt

def ix0585 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 40, 41, 42, 43, 44, 45, 46, 47, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93]
theorem ix0585_lt : ∀ i ∈ ix0585, i < Pop.S0294.leaves.length := by decide +kernel
def r0585 : List (List ℕ) := ix0585.map fun i => (Pop.S0294.leaves.getD i dflt).1
theorem r0585_ok : ∀ p ∈ r0585, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0294.sem ix0585_lt

def ix0586 : List ℕ := [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109]
theorem ix0586_lt : ∀ i ∈ ix0586, i < Pop.S0296.leaves.length := by decide +kernel
def r0586 : List (List ℕ) := ix0586.map fun i => (Pop.S0296.leaves.getD i dflt).1
theorem r0586_ok : ∀ p ∈ r0586, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0296.sem ix0586_lt

def ix0587 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68]
theorem ix0587_lt : ∀ i ∈ ix0587, i < Pop.S0297.leaves.length := by decide +kernel
def r0587 : List (List ℕ) := ix0587.map fun i => (Pop.S0297.leaves.getD i dflt).1
theorem r0587_ok : ∀ p ∈ r0587, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0297.sem ix0587_lt

def ix0588 : List ℕ := [26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]
theorem ix0588_lt : ∀ i ∈ ix0588, i < Pop.S0290.leaves.length := by decide +kernel
def r0588 : List (List ℕ) := ix0588.map fun i => (Pop.S0290.leaves.getD i dflt).1
theorem r0588_ok : ∀ p ∈ r0588, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0290.sem ix0588_lt

def ix0589 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]
theorem ix0589_lt : ∀ i ∈ ix0589, i < Pop.S0291.leaves.length := by decide +kernel
def r0589 : List (List ℕ) := ix0589.map fun i => (Pop.S0291.leaves.getD i dflt).1
theorem r0589_ok : ∀ p ∈ r0589, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0291.sem ix0589_lt

def ix0590 : List ℕ := [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78]
theorem ix0590_lt : ∀ i ∈ ix0590, i < Pop.S0295.leaves.length := by decide +kernel
def r0590 : List (List ℕ) := ix0590.map fun i => (Pop.S0295.leaves.getD i dflt).1
theorem r0590_ok : ∀ p ∈ r0590, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0295.sem ix0590_lt

def ix0591 : List ℕ := [0, 1, 2, 3, 4, 5, 6]
theorem ix0591_lt : ∀ i ∈ ix0591, i < Pop.S0296.leaves.length := by decide +kernel
def r0591 : List (List ℕ) := ix0591.map fun i => (Pop.S0296.leaves.getD i dflt).1
theorem r0591_ok : ∀ p ∈ r0591, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0296.sem ix0591_lt

def ix0592 : List ℕ := [69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91]
theorem ix0592_lt : ∀ i ∈ ix0592, i < Pop.S0297.leaves.length := by decide +kernel
def r0592 : List (List ℕ) := ix0592.map fun i => (Pop.S0297.leaves.getD i dflt).1
theorem r0592_ok : ∀ p ∈ r0592, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0297.sem ix0592_lt

def ix0593 : List ℕ := [60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86]
theorem ix0593_lt : ∀ i ∈ ix0593, i < Pop.S0300.leaves.length := by decide +kernel
def r0593 : List (List ℕ) := ix0593.map fun i => (Pop.S0300.leaves.getD i dflt).1
theorem r0593_ok : ∀ p ∈ r0593, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0300.sem ix0593_lt

def ix0594 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
theorem ix0594_lt : ∀ i ∈ ix0594, i < Pop.S0301.leaves.length := by decide +kernel
def r0594 : List (List ℕ) := ix0594.map fun i => (Pop.S0301.leaves.getD i dflt).1
theorem r0594_ok : ∀ p ∈ r0594, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0301.sem ix0594_lt

def ix0595 : List ℕ := [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]
theorem ix0595_lt : ∀ i ∈ ix0595, i < Pop.S0303.leaves.length := by decide +kernel
def r0595 : List (List ℕ) := ix0595.map fun i => (Pop.S0303.leaves.getD i dflt).1
theorem r0595_ok : ∀ p ∈ r0595, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0303.sem ix0595_lt

def ix0596 : List ℕ := [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]
theorem ix0596_lt : ∀ i ∈ ix0596, i < Pop.S0324.leaves.length := by decide +kernel
def r0596 : List (List ℕ) := ix0596.map fun i => (Pop.S0324.leaves.getD i dflt).1
theorem r0596_ok : ∀ p ∈ r0596, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0324.sem ix0596_lt

def ix0597 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
theorem ix0597_lt : ∀ i ∈ ix0597, i < Pop.S0325.leaves.length := by decide +kernel
def r0597 : List (List ℕ) := ix0597.map fun i => (Pop.S0325.leaves.getD i dflt).1
theorem r0597_ok : ∀ p ∈ r0597, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0325.sem ix0597_lt

def ix0598 : List ℕ := [140, 141, 142, 143]
theorem ix0598_lt : ∀ i ∈ ix0598, i < Pop.S0329.leaves.length := by decide +kernel
def r0598 : List (List ℕ) := ix0598.map fun i => (Pop.S0329.leaves.getD i dflt).1
theorem r0598_ok : ∀ p ∈ r0598, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0329.sem ix0598_lt

def ix0599 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38]
theorem ix0599_lt : ∀ i ∈ ix0599, i < Pop.S0330.leaves.length := by decide +kernel
def r0599 : List (List ℕ) := ix0599.map fun i => (Pop.S0330.leaves.getD i dflt).1
theorem r0599_ok : ∀ p ∈ r0599, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0330.sem ix0599_lt

def ix0600 : List ℕ := [32, 33, 34, 35]
theorem ix0600_lt : ∀ i ∈ ix0600, i < Pop.S0332.leaves.length := by decide +kernel
def r0600 : List (List ℕ) := ix0600.map fun i => (Pop.S0332.leaves.getD i dflt).1
theorem r0600_ok : ∀ p ∈ r0600, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0332.sem ix0600_lt

def ix0601 : List ℕ := [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87]
theorem ix0601_lt : ∀ i ∈ ix0601, i < Pop.S0301.leaves.length := by decide +kernel
def r0601 : List (List ℕ) := ix0601.map fun i => (Pop.S0301.leaves.getD i dflt).1
theorem r0601_ok : ∀ p ∈ r0601, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0301.sem ix0601_lt

def ix0602 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98]
theorem ix0602_lt : ∀ i ∈ ix0602, i < Pop.S0302.leaves.length := by decide +kernel
def r0602 : List (List ℕ) := ix0602.map fun i => (Pop.S0302.leaves.getD i dflt).1
theorem r0602_ok : ∀ p ∈ r0602, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0302.sem ix0602_lt

def ix0603 : List ℕ := [0, 1, 2, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70]
theorem ix0603_lt : ∀ i ∈ ix0603, i < Pop.S0303.leaves.length := by decide +kernel
def r0603 : List (List ℕ) := ix0603.map fun i => (Pop.S0303.leaves.getD i dflt).1
theorem r0603_ok : ∀ p ∈ r0603, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0303.sem ix0603_lt

def ix0604 : List ℕ := [92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]
theorem ix0604_lt : ∀ i ∈ ix0604, i < Pop.S0305.leaves.length := by decide +kernel
def r0604 : List (List ℕ) := ix0604.map fun i => (Pop.S0305.leaves.getD i dflt).1
theorem r0604_ok : ∀ p ∈ r0604, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0305.sem ix0604_lt

def ix0605 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130]
theorem ix0605_lt : ∀ i ∈ ix0605, i < Pop.S0306.leaves.length := by decide +kernel
def r0605 : List (List ℕ) := ix0605.map fun i => (Pop.S0306.leaves.getD i dflt).1
theorem r0605_ok : ∀ p ∈ r0605, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0306.sem ix0605_lt

def ix0606 : List ℕ := [116, 117, 118, 119, 120, 121, 122]
theorem ix0606_lt : ∀ i ∈ ix0606, i < Pop.S0307.leaves.length := by decide +kernel
def r0606 : List (List ℕ) := ix0606.map fun i => (Pop.S0307.leaves.getD i dflt).1
theorem r0606_ok : ∀ p ∈ r0606, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0307.sem ix0606_lt

def ix0607 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84]
theorem ix0607_lt : ∀ i ∈ ix0607, i < Pop.S0308.leaves.length := by decide +kernel
def r0607 : List (List ℕ) := ix0607.map fun i => (Pop.S0308.leaves.getD i dflt).1
theorem r0607_ok : ∀ p ∈ r0607, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0308.sem ix0607_lt

def ix0608 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61]
theorem ix0608_lt : ∀ i ∈ ix0608, i < Pop.S0309.leaves.length := by decide +kernel
def r0608 : List (List ℕ) := ix0608.map fun i => (Pop.S0309.leaves.getD i dflt).1
theorem r0608_ok : ∀ p ∈ r0608, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0309.sem ix0608_lt

def ix0609 : List ℕ := [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112]
theorem ix0609_lt : ∀ i ∈ ix0609, i < Pop.S0325.leaves.length := by decide +kernel
def r0609 : List (List ℕ) := ix0609.map fun i => (Pop.S0325.leaves.getD i dflt).1
theorem r0609_ok : ∀ p ∈ r0609, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0325.sem ix0609_lt

def ix0610 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]
theorem ix0610_lt : ∀ i ∈ ix0610, i < Pop.S0326.leaves.length := by decide +kernel
def r0610 : List (List ℕ) := ix0610.map fun i => (Pop.S0326.leaves.getD i dflt).1
theorem r0610_ok : ∀ p ∈ r0610, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0326.sem ix0610_lt

def ix0611 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38]
theorem ix0611_lt : ∀ i ∈ ix0611, i < Pop.S0327.leaves.length := by decide +kernel
def r0611 : List (List ℕ) := ix0611.map fun i => (Pop.S0327.leaves.getD i dflt).1
theorem r0611_ok : ∀ p ∈ r0611, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0327.sem ix0611_lt

def ix0612 : List ℕ := [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]
theorem ix0612_lt : ∀ i ∈ ix0612, i < Pop.S0328.leaves.length := by decide +kernel
def r0612 : List (List ℕ) := ix0612.map fun i => (Pop.S0328.leaves.getD i dflt).1
theorem r0612_ok : ∀ p ∈ r0612, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0328.sem ix0612_lt

def ix0613 : List ℕ := [90, 91, 92, 93, 94, 95, 96, 97, 98]
theorem ix0613_lt : ∀ i ∈ ix0613, i < Pop.S0330.leaves.length := by decide +kernel
def r0613 : List (List ℕ) := ix0613.map fun i => (Pop.S0330.leaves.getD i dflt).1
theorem r0613_ok : ∀ p ∈ r0613, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0330.sem ix0613_lt

def ix0614 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89]
theorem ix0614_lt : ∀ i ∈ ix0614, i < Pop.S0331.leaves.length := by decide +kernel
def r0614 : List (List ℕ) := ix0614.map fun i => (Pop.S0331.leaves.getD i dflt).1
theorem r0614_ok : ∀ p ∈ r0614, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0331.sem ix0614_lt

def ix0615 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50]
theorem ix0615_lt : ∀ i ∈ ix0615, i < Pop.S0332.leaves.length := by decide +kernel
def r0615 : List (List ℕ) := ix0615.map fun i => (Pop.S0332.leaves.getD i dflt).1
theorem r0615_ok : ∀ p ∈ r0615, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0332.sem ix0615_lt

def ix0616 : List ℕ := [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96]
theorem ix0616_lt : ∀ i ∈ ix0616, i < Pop.S0335.leaves.length := by decide +kernel
def r0616 : List (List ℕ) := ix0616.map fun i => (Pop.S0335.leaves.getD i dflt).1
theorem r0616_ok : ∀ p ∈ r0616, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0335.sem ix0616_lt

def ix0617 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109]
theorem ix0617_lt : ∀ i ∈ ix0617, i < Pop.S0336.leaves.length := by decide +kernel
def r0617 : List (List ℕ) := ix0617.map fun i => (Pop.S0336.leaves.getD i dflt).1
theorem r0617_ok : ∀ p ∈ r0617, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0336.sem ix0617_lt

def ix0618 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]
theorem ix0618_lt : ∀ i ∈ ix0618, i < Pop.S0337.leaves.length := by decide +kernel
def r0618 : List (List ℕ) := ix0618.map fun i => (Pop.S0337.leaves.getD i dflt).1
theorem r0618_ok : ∀ p ∈ r0618, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0337.sem ix0618_lt

def ix0619 : List ℕ := [87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109]
theorem ix0619_lt : ∀ i ∈ ix0619, i < Pop.S0304.leaves.length := by decide +kernel
def r0619 : List (List ℕ) := ix0619.map fun i => (Pop.S0304.leaves.getD i dflt).1
theorem r0619_ok : ∀ p ∈ r0619, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0304.sem ix0619_lt

def ix0620 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91]
theorem ix0620_lt : ∀ i ∈ ix0620, i < Pop.S0305.leaves.length := by decide +kernel
def r0620 : List (List ℕ) := ix0620.map fun i => (Pop.S0305.leaves.getD i dflt).1
theorem r0620_ok : ∀ p ∈ r0620, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0305.sem ix0620_lt

def ix0621 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115]
theorem ix0621_lt : ∀ i ∈ ix0621, i < Pop.S0307.leaves.length := by decide +kernel
def r0621 : List (List ℕ) := ix0621.map fun i => (Pop.S0307.leaves.getD i dflt).1
theorem r0621_ok : ∀ p ∈ r0621, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0307.sem ix0621_lt

def ix0622 : List ℕ := [98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119]
theorem ix0622_lt : ∀ i ∈ ix0622, i < Pop.S0309.leaves.length := by decide +kernel
def r0622 : List (List ℕ) := ix0622.map fun i => (Pop.S0309.leaves.getD i dflt).1
theorem r0622_ok : ∀ p ∈ r0622, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0309.sem ix0622_lt

def ix0623 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]
theorem ix0623_lt : ∀ i ∈ ix0623, i < Pop.S0310.leaves.length := by decide +kernel
def r0623 : List (List ℕ) := ix0623.map fun i => (Pop.S0310.leaves.getD i dflt).1
theorem r0623_ok : ∀ p ∈ r0623, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0310.sem ix0623_lt

def ix0624 : List ℕ := [98, 99, 100, 101, 102, 103, 104, 105, 106]
theorem ix0624_lt : ∀ i ∈ ix0624, i < Pop.S0315.leaves.length := by decide +kernel
def r0624 : List (List ℕ) := ix0624.map fun i => (Pop.S0315.leaves.getD i dflt).1
theorem r0624_ok : ∀ p ∈ r0624, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0315.sem ix0624_lt

def ix0625 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43]
theorem ix0625_lt : ∀ i ∈ ix0625, i < Pop.S0316.leaves.length := by decide +kernel
def r0625 : List (List ℕ) := ix0625.map fun i => (Pop.S0316.leaves.getD i dflt).1
theorem r0625_ok : ∀ p ∈ r0625, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0316.sem ix0625_lt

def ix0626 : List ℕ := [26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86]
theorem ix0626_lt : ∀ i ∈ ix0626, i < Pop.S0310.leaves.length := by decide +kernel
def r0626 : List (List ℕ) := ix0626.map fun i => (Pop.S0310.leaves.getD i dflt).1
theorem r0626_ok : ∀ p ∈ r0626, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0310.sem ix0626_lt

def ix0627 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84]
theorem ix0627_lt : ∀ i ∈ ix0627, i < Pop.S0311.leaves.length := by decide +kernel
def r0627 : List (List ℕ) := ix0627.map fun i => (Pop.S0311.leaves.getD i dflt).1
theorem r0627_ok : ∀ p ∈ r0627, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0311.sem ix0627_lt

def ix0628 : List ℕ := [31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65]
theorem ix0628_lt : ∀ i ∈ ix0628, i < Pop.S0312.leaves.length := by decide +kernel
def r0628 : List (List ℕ) := ix0628.map fun i => (Pop.S0312.leaves.getD i dflt).1
theorem r0628_ok : ∀ p ∈ r0628, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0312.sem ix0628_lt

def ix0629 : List ℕ := [33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]
theorem ix0629_lt : ∀ i ∈ ix0629, i < Pop.S0314.leaves.length := by decide +kernel
def r0629 : List (List ℕ) := ix0629.map fun i => (Pop.S0314.leaves.getD i dflt).1
theorem r0629_ok : ∀ p ∈ r0629, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0314.sem ix0629_lt

def ix0630 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]
theorem ix0630_lt : ∀ i ∈ ix0630, i < Pop.S0315.leaves.length := by decide +kernel
def r0630 : List (List ℕ) := ix0630.map fun i => (Pop.S0315.leaves.getD i dflt).1
theorem r0630_ok : ∀ p ∈ r0630, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0315.sem ix0630_lt

def ix0631 : List ℕ := [65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110]
theorem ix0631_lt : ∀ i ∈ ix0631, i < Pop.S0320.leaves.length := by decide +kernel
def r0631 : List (List ℕ) := ix0631.map fun i => (Pop.S0320.leaves.getD i dflt).1
theorem r0631_ok : ∀ p ∈ r0631, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0320.sem ix0631_lt

def ix0632 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]
theorem ix0632_lt : ∀ i ∈ ix0632, i < Pop.S0321.leaves.length := by decide +kernel
def r0632 : List (List ℕ) := ix0632.map fun i => (Pop.S0321.leaves.getD i dflt).1
theorem r0632_ok : ∀ p ∈ r0632, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0321.sem ix0632_lt

def ix0633 : List ℕ := [36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109]
theorem ix0633_lt : ∀ i ∈ ix0633, i < Pop.S0323.leaves.length := by decide +kernel
def r0633 : List (List ℕ) := ix0633.map fun i => (Pop.S0323.leaves.getD i dflt).1
theorem r0633_ok : ∀ p ∈ r0633, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0323.sem ix0633_lt

def ix0634 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]
theorem ix0634_lt : ∀ i ∈ ix0634, i < Pop.S0324.leaves.length := by decide +kernel
def r0634 : List (List ℕ) := ix0634.map fun i => (Pop.S0324.leaves.getD i dflt).1
theorem r0634_ok : ∀ p ∈ r0634, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0324.sem ix0634_lt

def ix0635 : List ℕ := [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]
theorem ix0635_lt : ∀ i ∈ ix0635, i < Pop.S0312.leaves.length := by decide +kernel
def r0635 : List (List ℕ) := ix0635.map fun i => (Pop.S0312.leaves.getD i dflt).1
theorem r0635_ok : ∀ p ∈ r0635, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0312.sem ix0635_lt

def ix0636 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113]
theorem ix0636_lt : ∀ i ∈ ix0636, i < Pop.S0313.leaves.length := by decide +kernel
def r0636 : List (List ℕ) := ix0636.map fun i => (Pop.S0313.leaves.getD i dflt).1
theorem r0636_ok : ∀ p ∈ r0636, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0313.sem ix0636_lt

def ix0637 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]
theorem ix0637_lt : ∀ i ∈ ix0637, i < Pop.S0314.leaves.length := by decide +kernel
def r0637 : List (List ℕ) := ix0637.map fun i => (Pop.S0314.leaves.getD i dflt).1
theorem r0637_ok : ∀ p ∈ r0637, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0314.sem ix0637_lt

def ix0638 : List ℕ := [36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97]
theorem ix0638_lt : ∀ i ∈ ix0638, i < Pop.S0315.leaves.length := by decide +kernel
def r0638 : List (List ℕ) := ix0638.map fun i => (Pop.S0315.leaves.getD i dflt).1
theorem r0638_ok : ∀ p ∈ r0638, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0315.sem ix0638_lt

def ix0639 : List ℕ := [44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105]
theorem ix0639_lt : ∀ i ∈ ix0639, i < Pop.S0316.leaves.length := by decide +kernel
def r0639 : List (List ℕ) := ix0639.map fun i => (Pop.S0316.leaves.getD i dflt).1
theorem r0639_ok : ∀ p ∈ r0639, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0316.sem ix0639_lt

def ix0640 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121]
theorem ix0640_lt : ∀ i ∈ ix0640, i < Pop.S0317.leaves.length := by decide +kernel
def r0640 : List (List ℕ) := ix0640.map fun i => (Pop.S0317.leaves.getD i dflt).1
theorem r0640_ok : ∀ p ∈ r0640, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0317.sem ix0640_lt

def ix0641 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130]
theorem ix0641_lt : ∀ i ∈ ix0641, i < Pop.S0318.leaves.length := by decide +kernel
def r0641 : List (List ℕ) := ix0641.map fun i => (Pop.S0318.leaves.getD i dflt).1
theorem r0641_ok : ∀ p ∈ r0641, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0318.sem ix0641_lt

def ix0642 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130]
theorem ix0642_lt : ∀ i ∈ ix0642, i < Pop.S0319.leaves.length := by decide +kernel
def r0642 : List (List ℕ) := ix0642.map fun i => (Pop.S0319.leaves.getD i dflt).1
theorem r0642_ok : ∀ p ∈ r0642, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0319.sem ix0642_lt

def ix0643 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64]
theorem ix0643_lt : ∀ i ∈ ix0643, i < Pop.S0320.leaves.length := by decide +kernel
def r0643 : List (List ℕ) := ix0643.map fun i => (Pop.S0320.leaves.getD i dflt).1
theorem r0643_ok : ∀ p ∈ r0643, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0320.sem ix0643_lt

def ix0644 : List ℕ := [36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]
theorem ix0644_lt : ∀ i ∈ ix0644, i < Pop.S0321.leaves.length := by decide +kernel
def r0644 : List (List ℕ) := ix0644.map fun i => (Pop.S0321.leaves.getD i dflt).1
theorem r0644_ok : ∀ p ∈ r0644, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0321.sem ix0644_lt

def ix0645 : List ℕ := [44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126]
theorem ix0645_lt : ∀ i ∈ ix0645, i < Pop.S0299.leaves.length := by decide +kernel
def r0645 : List (List ℕ) := ix0645.map fun i => (Pop.S0299.leaves.getD i dflt).1
theorem r0645_ok : ∀ p ∈ r0645, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0299.sem ix0645_lt

def ix0646 : List ℕ := [71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92]
theorem ix0646_lt : ∀ i ∈ ix0646, i < Pop.S0303.leaves.length := by decide +kernel
def r0646 : List (List ℕ) := ix0646.map fun i => (Pop.S0303.leaves.getD i dflt).1
theorem r0646_ok : ∀ p ∈ r0646, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0303.sem ix0646_lt

def ix0647 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86]
theorem ix0647_lt : ∀ i ∈ ix0647, i < Pop.S0304.leaves.length := by decide +kernel
def r0647 : List (List ℕ) := ix0647.map fun i => (Pop.S0304.leaves.getD i dflt).1
theorem r0647_ok : ∀ p ∈ r0647, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0304.sem ix0647_lt

def ix0648 : List ℕ := [62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97]
theorem ix0648_lt : ∀ i ∈ ix0648, i < Pop.S0309.leaves.length := by decide +kernel
def r0648 : List (List ℕ) := ix0648.map fun i => (Pop.S0309.leaves.getD i dflt).1
theorem r0648_ok : ∀ p ∈ r0648, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0309.sem ix0648_lt

def ix0649 : List ℕ := [85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115]
theorem ix0649_lt : ∀ i ∈ ix0649, i < Pop.S0311.leaves.length := by decide +kernel
def r0649 : List (List ℕ) := ix0649.map fun i => (Pop.S0311.leaves.getD i dflt).1
theorem r0649_ok : ∀ p ∈ r0649, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0311.sem ix0649_lt

def ix0650 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]
theorem ix0650_lt : ∀ i ∈ ix0650, i < Pop.S0312.leaves.length := by decide +kernel
def r0650 : List (List ℕ) := ix0650.map fun i => (Pop.S0312.leaves.getD i dflt).1
theorem r0650_ok : ∀ p ∈ r0650, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0312.sem ix0650_lt

def ix0651 : List ℕ := [51, 52, 53, 54, 55, 56, 57, 58]
theorem ix0651_lt : ∀ i ∈ ix0651, i < Pop.S0317.leaves.length := by decide +kernel
def r0651 : List (List ℕ) := ix0651.map fun i => (Pop.S0317.leaves.getD i dflt).1
theorem r0651_ok : ∀ p ∈ r0651, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0317.sem ix0651_lt

def ix0652 : List ℕ := [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]
theorem ix0652_lt : ∀ i ∈ ix0652, i < Pop.S0318.leaves.length := by decide +kernel
def r0652 : List (List ℕ) := ix0652.map fun i => (Pop.S0318.leaves.getD i dflt).1
theorem r0652_ok : ∀ p ∈ r0652, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0318.sem ix0652_lt

def ix0653 : List ℕ := [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101]
theorem ix0653_lt : ∀ i ∈ ix0653, i < Pop.S0321.leaves.length := by decide +kernel
def r0653 : List (List ℕ) := ix0653.map fun i => (Pop.S0321.leaves.getD i dflt).1
theorem r0653_ok : ∀ p ∈ r0653, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0321.sem ix0653_lt

def ix0654 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121]
theorem ix0654_lt : ∀ i ∈ ix0654, i < Pop.S0322.leaves.length := by decide +kernel
def r0654 : List (List ℕ) := ix0654.map fun i => (Pop.S0322.leaves.getD i dflt).1
theorem r0654_ok : ∀ p ∈ r0654, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0322.sem ix0654_lt

def ix0655 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]
theorem ix0655_lt : ∀ i ∈ ix0655, i < Pop.S0323.leaves.length := by decide +kernel
def r0655 : List (List ℕ) := ix0655.map fun i => (Pop.S0323.leaves.getD i dflt).1
theorem r0655_ok : ∀ p ∈ r0655, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0323.sem ix0655_lt

def ix0656 : List ℕ := [33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]
theorem ix0656_lt : ∀ i ∈ ix0656, i < Pop.S0324.leaves.length := by decide +kernel
def r0656 : List (List ℕ) := ix0656.map fun i => (Pop.S0324.leaves.getD i dflt).1
theorem r0656_ok : ∀ p ∈ r0656, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0324.sem ix0656_lt

def ix0657 : List ℕ := [39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]
theorem ix0657_lt : ∀ i ∈ ix0657, i < Pop.S0327.leaves.length := by decide +kernel
def r0657 : List (List ℕ) := ix0657.map fun i => (Pop.S0327.leaves.getD i dflt).1
theorem r0657_ok : ∀ p ∈ r0657, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0327.sem ix0657_lt

def ix0658 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]
theorem ix0658_lt : ∀ i ∈ ix0658, i < Pop.S0328.leaves.length := by decide +kernel
def r0658 : List (List ℕ) := ix0658.map fun i => (Pop.S0328.leaves.getD i dflt).1
theorem r0658_ok : ∀ p ∈ r0658, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0328.sem ix0658_lt

def ix0659 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]
theorem ix0659_lt : ∀ i ∈ ix0659, i < Pop.S0329.leaves.length := by decide +kernel
def r0659 : List (List ℕ) := ix0659.map fun i => (Pop.S0329.leaves.getD i dflt).1
theorem r0659_ok : ∀ p ∈ r0659, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0329.sem ix0659_lt

def ix0660 : List ℕ := [39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89]
theorem ix0660_lt : ∀ i ∈ ix0660, i < Pop.S0330.leaves.length := by decide +kernel
def r0660 : List (List ℕ) := ix0660.map fun i => (Pop.S0330.leaves.getD i dflt).1
theorem r0660_ok : ∀ p ∈ r0660, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0330.sem ix0660_lt

def ix0661 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130]
theorem ix0661_lt : ∀ i ∈ ix0661, i < Pop.S0333.leaves.length := by decide +kernel
def r0661 : List (List ℕ) := ix0661.map fun i => (Pop.S0333.leaves.getD i dflt).1
theorem r0661_ok : ∀ p ∈ r0661, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0333.sem ix0661_lt

def ix0662 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]
theorem ix0662_lt : ∀ i ∈ ix0662, i < Pop.S0334.leaves.length := by decide +kernel
def r0662 : List (List ℕ) := ix0662.map fun i => (Pop.S0334.leaves.getD i dflt).1
theorem r0662_ok : ∀ p ∈ r0662, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0334.sem ix0662_lt

def ix0663 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
theorem ix0663_lt : ∀ i ∈ ix0663, i < Pop.S0335.leaves.length := by decide +kernel
def r0663 : List (List ℕ) := ix0663.map fun i => (Pop.S0335.leaves.getD i dflt).1
theorem r0663_ok : ∀ p ∈ r0663, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0335.sem ix0663_lt

def ix0664 : List ℕ := [130, 131, 132, 133, 134, 135, 136, 137]
theorem ix0664_lt : ∀ i ∈ ix0664, i < Pop.S0337.leaves.length := by decide +kernel
def r0664 : List (List ℕ) := ix0664.map fun i => (Pop.S0337.leaves.getD i dflt).1
theorem r0664_ok : ∀ p ∈ r0664, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0337.sem ix0664_lt

def ix0665 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146]
theorem ix0665_lt : ∀ i ∈ ix0665, i < Pop.S0338.leaves.length := by decide +kernel
def r0665 : List (List ℕ) := ix0665.map fun i => (Pop.S0338.leaves.getD i dflt).1
theorem r0665_ok : ∀ p ∈ r0665, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0338.sem ix0665_lt

def ix0666 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100]
theorem ix0666_lt : ∀ i ∈ ix0666, i < Pop.S0339.leaves.length := by decide +kernel
def r0666 : List (List ℕ) := ix0666.map fun i => (Pop.S0339.leaves.getD i dflt).1
theorem r0666_ok : ∀ p ∈ r0666, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0339.sem ix0666_lt

def ix0667 : List ℕ := [59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]
theorem ix0667_lt : ∀ i ∈ ix0667, i < Pop.S0345.leaves.length := by decide +kernel
def r0667 : List (List ℕ) := ix0667.map fun i => (Pop.S0345.leaves.getD i dflt).1
theorem r0667_ok : ∀ p ∈ r0667, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0345.sem ix0667_lt

def ix0668 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]
theorem ix0668_lt : ∀ i ∈ ix0668, i < Pop.S0346.leaves.length := by decide +kernel
def r0668 : List (List ℕ) := ix0668.map fun i => (Pop.S0346.leaves.getD i dflt).1
theorem r0668_ok : ∀ p ∈ r0668, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0346.sem ix0668_lt

def ix0669 : List ℕ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]
theorem ix0669_lt : ∀ i ∈ ix0669, i < Pop.S0347.leaves.length := by decide +kernel
def r0669 : List (List ℕ) := ix0669.map fun i => (Pop.S0347.leaves.getD i dflt).1
theorem r0669_ok : ∀ p ∈ r0669, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0347.sem ix0669_lt

def ix0670 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]
theorem ix0670_lt : ∀ i ∈ ix0670, i < Pop.S0348.leaves.length := by decide +kernel
def r0670 : List (List ℕ) := ix0670.map fun i => (Pop.S0348.leaves.getD i dflt).1
theorem r0670_ok : ∀ p ∈ r0670, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0348.sem ix0670_lt

def ix0671 : List ℕ := [104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]
theorem ix0671_lt : ∀ i ∈ ix0671, i < Pop.S0386.leaves.length := by decide +kernel
def r0671 : List (List ℕ) := ix0671.map fun i => (Pop.S0386.leaves.getD i dflt).1
theorem r0671_ok : ∀ p ∈ r0671, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0386.sem ix0671_lt

def ix0672 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90]
theorem ix0672_lt : ∀ i ∈ ix0672, i < Pop.S0387.leaves.length := by decide +kernel
def r0672 : List (List ℕ) := ix0672.map fun i => (Pop.S0387.leaves.getD i dflt).1
theorem r0672_ok : ∀ p ∈ r0672, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0387.sem ix0672_lt

def ix0673 : List ℕ := [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130]
theorem ix0673_lt : ∀ i ∈ ix0673, i < Pop.S0388.leaves.length := by decide +kernel
def r0673 : List (List ℕ) := ix0673.map fun i => (Pop.S0388.leaves.getD i dflt).1
theorem r0673_ok : ∀ p ∈ r0673, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0388.sem ix0673_lt

def ix0674 : List ℕ := [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86]
theorem ix0674_lt : ∀ i ∈ ix0674, i < Pop.S0392.leaves.length := by decide +kernel
def r0674 : List (List ℕ) := ix0674.map fun i => (Pop.S0392.leaves.getD i dflt).1
theorem r0674_ok : ∀ p ∈ r0674, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0392.sem ix0674_lt

def ix0675 : List ℕ := [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141]
theorem ix0675_lt : ∀ i ∈ ix0675, i < Pop.S0339.leaves.length := by decide +kernel
def r0675 : List (List ℕ) := ix0675.map fun i => (Pop.S0339.leaves.getD i dflt).1
theorem r0675_ok : ∀ p ∈ r0675, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0339.sem ix0675_lt

def ix0676 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]
theorem ix0676_lt : ∀ i ∈ ix0676, i < Pop.S0340.leaves.length := by decide +kernel
def r0676 : List (List ℕ) := ix0676.map fun i => (Pop.S0340.leaves.getD i dflt).1
theorem r0676_ok : ∀ p ∈ r0676, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0340.sem ix0676_lt

def ix0677 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]
theorem ix0677_lt : ∀ i ∈ ix0677, i < Pop.S0341.leaves.length := by decide +kernel
def r0677 : List (List ℕ) := ix0677.map fun i => (Pop.S0341.leaves.getD i dflt).1
theorem r0677_ok : ∀ p ∈ r0677, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0341.sem ix0677_lt

def ix0678 : List ℕ := [89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]
theorem ix0678_lt : ∀ i ∈ ix0678, i < Pop.S0342.leaves.length := by decide +kernel
def r0678 : List (List ℕ) := ix0678.map fun i => (Pop.S0342.leaves.getD i dflt).1
theorem r0678_ok : ∀ p ∈ r0678, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0342.sem ix0678_lt

def ix0679 : List ℕ := [130, 131]
theorem ix0679_lt : ∀ i ∈ ix0679, i < Pop.S0384.leaves.length := by decide +kernel
def r0679 : List (List ℕ) := ix0679.map fun i => (Pop.S0384.leaves.getD i dflt).1
theorem r0679_ok : ∀ p ∈ r0679, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0384.sem ix0679_lt

def ix0680 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65]
theorem ix0680_lt : ∀ i ∈ ix0680, i < Pop.S0385.leaves.length := by decide +kernel
def r0680 : List (List ℕ) := ix0680.map fun i => (Pop.S0385.leaves.getD i dflt).1
theorem r0680_ok : ∀ p ∈ r0680, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0385.sem ix0680_lt

def ix0681 : List ℕ := [23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]
theorem ix0681_lt : ∀ i ∈ ix0681, i < Pop.S0341.leaves.length := by decide +kernel
def r0681 : List (List ℕ) := ix0681.map fun i => (Pop.S0341.leaves.getD i dflt).1
theorem r0681_ok : ∀ p ∈ r0681, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0341.sem ix0681_lt

def ix0682 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 137, 138, 139, 140, 141, 142, 143, 144, 145]
theorem ix0682_lt : ∀ i ∈ ix0682, i < Pop.S0342.leaves.length := by decide +kernel
def r0682 : List (List ℕ) := ix0682.map fun i => (Pop.S0342.leaves.getD i dflt).1
theorem r0682_ok : ∀ p ∈ r0682, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0342.sem ix0682_lt

def ix0683 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
theorem ix0683_lt : ∀ i ∈ ix0683, i < Pop.S0343.leaves.length := by decide +kernel
def r0683 : List (List ℕ) := ix0683.map fun i => (Pop.S0343.leaves.getD i dflt).1
theorem r0683_ok : ∀ p ∈ r0683, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0343.sem ix0683_lt

def ix0684 : List ℕ := [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
theorem ix0684_lt : ∀ i ∈ ix0684, i < Pop.S0344.leaves.length := by decide +kernel
def r0684 : List (List ℕ) := ix0684.map fun i => (Pop.S0344.leaves.getD i dflt).1
theorem r0684_ok : ∀ p ∈ r0684, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0344.sem ix0684_lt

def ix0685 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]
theorem ix0685_lt : ∀ i ∈ ix0685, i < Pop.S0345.leaves.length := by decide +kernel
def r0685 : List (List ℕ) := ix0685.map fun i => (Pop.S0345.leaves.getD i dflt).1
theorem r0685_ok : ∀ p ∈ r0685, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0345.sem ix0685_lt

def ix0686 : List ℕ := [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
theorem ix0686_lt : ∀ i ∈ ix0686, i < Pop.S0383.leaves.length := by decide +kernel
def r0686 : List (List ℕ) := ix0686.map fun i => (Pop.S0383.leaves.getD i dflt).1
theorem r0686_ok : ∀ p ∈ r0686, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0383.sem ix0686_lt

def ix0687 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]
theorem ix0687_lt : ∀ i ∈ ix0687, i < Pop.S0384.leaves.length := by decide +kernel
def r0687 : List (List ℕ) := ix0687.map fun i => (Pop.S0384.leaves.getD i dflt).1
theorem r0687_ok : ∀ p ∈ r0687, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0384.sem ix0687_lt

def ix0688 : List ℕ := [24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]
theorem ix0688_lt : ∀ i ∈ ix0688, i < Pop.S0343.leaves.length := by decide +kernel
def r0688 : List (List ℕ) := ix0688.map fun i => (Pop.S0343.leaves.getD i dflt).1
theorem r0688_ok : ∀ p ∈ r0688, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0343.sem ix0688_lt

def ix0689 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
theorem ix0689_lt : ∀ i ∈ ix0689, i < Pop.S0344.leaves.length := by decide +kernel
def r0689 : List (List ℕ) := ix0689.map fun i => (Pop.S0344.leaves.getD i dflt).1
theorem r0689_ok : ∀ p ∈ r0689, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0344.sem ix0689_lt

def ix0690 : List ℕ := [30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58]
theorem ix0690_lt : ∀ i ∈ ix0690, i < Pop.S0345.leaves.length := by decide +kernel
def r0690 : List (List ℕ) := ix0690.map fun i => (Pop.S0345.leaves.getD i dflt).1
theorem r0690_ok : ∀ p ∈ r0690, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0345.sem ix0690_lt

def ix0691 : List ℕ := [137, 138, 139, 140, 141, 142]
theorem ix0691_lt : ∀ i ∈ ix0691, i < Pop.S0346.leaves.length := by decide +kernel
def r0691 : List (List ℕ) := ix0691.map fun i => (Pop.S0346.leaves.getD i dflt).1
theorem r0691_ok : ∀ p ∈ r0691, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0346.sem ix0691_lt

def ix0692 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104]
theorem ix0692_lt : ∀ i ∈ ix0692, i < Pop.S0347.leaves.length := by decide +kernel
def r0692 : List (List ℕ) := ix0692.map fun i => (Pop.S0347.leaves.getD i dflt).1
theorem r0692_ok : ∀ p ∈ r0692, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0347.sem ix0692_lt

def ix0693 : List ℕ := [31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115]
theorem ix0693_lt : ∀ i ∈ ix0693, i < Pop.S0348.leaves.length := by decide +kernel
def r0693 : List (List ℕ) := ix0693.map fun i => (Pop.S0348.leaves.getD i dflt).1
theorem r0693_ok : ∀ p ∈ r0693, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0348.sem ix0693_lt

def ix0694 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 125, 126, 127, 128, 129]
theorem ix0694_lt : ∀ i ∈ ix0694, i < Pop.S0349.leaves.length := by decide +kernel
def r0694 : List (List ℕ) := ix0694.map fun i => (Pop.S0349.leaves.getD i dflt).1
theorem r0694_ok : ∀ p ∈ r0694, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0349.sem ix0694_lt

def ix0695 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50]
theorem ix0695_lt : ∀ i ∈ ix0695, i < Pop.S0350.leaves.length := by decide +kernel
def r0695 : List (List ℕ) := ix0695.map fun i => (Pop.S0350.leaves.getD i dflt).1
theorem r0695_ok : ∀ p ∈ r0695, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0350.sem ix0695_lt

def ix0696 : List ℕ := [53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]
theorem ix0696_lt : ∀ i ∈ ix0696, i < Pop.S0349.leaves.length := by decide +kernel
def r0696 : List (List ℕ) := ix0696.map fun i => (Pop.S0349.leaves.getD i dflt).1
theorem r0696_ok : ∀ p ∈ r0696, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0349.sem ix0696_lt

def ix0697 : List ℕ := [51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101]
theorem ix0697_lt : ∀ i ∈ ix0697, i < Pop.S0350.leaves.length := by decide +kernel
def r0697 : List (List ℕ) := ix0697.map fun i => (Pop.S0350.leaves.getD i dflt).1
theorem r0697_ok : ∀ p ∈ r0697, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0350.sem ix0697_lt

def ix0698 : List ℕ := [126, 127, 128, 129, 130, 131, 132]
theorem ix0698_lt : ∀ i ∈ ix0698, i < Pop.S0352.leaves.length := by decide +kernel
def r0698 : List (List ℕ) := ix0698.map fun i => (Pop.S0352.leaves.getD i dflt).1
theorem r0698_ok : ∀ p ∈ r0698, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0352.sem ix0698_lt

def ix0699 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]
theorem ix0699_lt : ∀ i ∈ ix0699, i < Pop.S0353.leaves.length := by decide +kernel
def r0699 : List (List ℕ) := ix0699.map fun i => (Pop.S0353.leaves.getD i dflt).1
theorem r0699_ok : ∀ p ∈ r0699, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0353.sem ix0699_lt

def ix0700 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 142, 143, 141]
theorem ix0700_lt : ∀ i ∈ ix0700, i < Pop.S0354.leaves.length := by decide +kernel
def r0700 : List (List ℕ) := ix0700.map fun i => (Pop.S0354.leaves.getD i dflt).1
theorem r0700_ok : ∀ p ∈ r0700, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0354.sem ix0700_lt

def ix0701 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7]
theorem ix0701_lt : ∀ i ∈ ix0701, i < Pop.S0355.leaves.length := by decide +kernel
def r0701 : List (List ℕ) := ix0701.map fun i => (Pop.S0355.leaves.getD i dflt).1
theorem r0701_ok : ∀ p ∈ r0701, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0355.sem ix0701_lt

def ix0702 : List ℕ := [102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]
theorem ix0702_lt : ∀ i ∈ ix0702, i < Pop.S0350.leaves.length := by decide +kernel
def r0702 : List (List ℕ) := ix0702.map fun i => (Pop.S0350.leaves.getD i dflt).1
theorem r0702_ok : ∀ p ∈ r0702, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0350.sem ix0702_lt

def ix0703 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
theorem ix0703_lt : ∀ i ∈ ix0703, i < Pop.S0351.leaves.length := by decide +kernel
def r0703 : List (List ℕ) := ix0703.map fun i => (Pop.S0351.leaves.getD i dflt).1
theorem r0703_ok : ∀ p ∈ r0703, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0351.sem ix0703_lt

def ix0704 : List ℕ := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135]
theorem ix0704_lt : ∀ i ∈ ix0704, i < Pop.S0356.leaves.length := by decide +kernel
def r0704 : List (List ℕ) := ix0704.map fun i => (Pop.S0356.leaves.getD i dflt).1
theorem r0704_ok : ∀ p ∈ r0704, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0356.sem ix0704_lt

def ix0705 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]
theorem ix0705_lt : ∀ i ∈ ix0705, i < Pop.S0357.leaves.length := by decide +kernel
def r0705 : List (List ℕ) := ix0705.map fun i => (Pop.S0357.leaves.getD i dflt).1
theorem r0705_ok : ∀ p ∈ r0705, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0357.sem ix0705_lt

def ix0706 : List ℕ := [91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130]
theorem ix0706_lt : ∀ i ∈ ix0706, i < Pop.S0378.leaves.length := by decide +kernel
def r0706 : List (List ℕ) := ix0706.map fun i => (Pop.S0378.leaves.getD i dflt).1
theorem r0706_ok : ∀ p ∈ r0706, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0378.sem ix0706_lt

def ix0707 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46]
theorem ix0707_lt : ∀ i ∈ ix0707, i < Pop.S0379.leaves.length := by decide +kernel
def r0707 : List (List ℕ) := ix0707.map fun i => (Pop.S0379.leaves.getD i dflt).1
theorem r0707_ok : ∀ p ∈ r0707, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0379.sem ix0707_lt

def ix0708 : List ℕ := [137, 138, 139, 140, 141, 142, 143, 144]
theorem ix0708_lt : ∀ i ∈ ix0708, i < Pop.S0380.leaves.length := by decide +kernel
def r0708 : List (List ℕ) := ix0708.map fun i => (Pop.S0380.leaves.getD i dflt).1
theorem r0708_ok : ∀ p ∈ r0708, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0380.sem ix0708_lt

def ix0709 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59]
theorem ix0709_lt : ∀ i ∈ ix0709, i < Pop.S0381.leaves.length := by decide +kernel
def r0709 : List (List ℕ) := ix0709.map fun i => (Pop.S0381.leaves.getD i dflt).1
theorem r0709_ok : ∀ p ∈ r0709, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0381.sem ix0709_lt

def ix0710 : List ℕ := [26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]
theorem ix0710_lt : ∀ i ∈ ix0710, i < Pop.S0384.leaves.length := by decide +kernel
def r0710 : List (List ℕ) := ix0710.map fun i => (Pop.S0384.leaves.getD i dflt).1
theorem r0710_ok : ∀ p ∈ r0710, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0384.sem ix0710_lt

def ix0711 : List ℕ := [66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]
theorem ix0711_lt : ∀ i ∈ ix0711, i < Pop.S0385.leaves.length := by decide +kernel
def r0711 : List (List ℕ) := ix0711.map fun i => (Pop.S0385.leaves.getD i dflt).1
theorem r0711_ok : ∀ p ∈ r0711, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0385.sem ix0711_lt

def ix0712 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103]
theorem ix0712_lt : ∀ i ∈ ix0712, i < Pop.S0386.leaves.length := by decide +kernel
def r0712 : List (List ℕ) := ix0712.map fun i => (Pop.S0386.leaves.getD i dflt).1
theorem r0712_ok : ∀ p ∈ r0712, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0386.sem ix0712_lt

def ix0713 : List ℕ := [74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]
theorem ix0713_lt : ∀ i ∈ ix0713, i < Pop.S0389.leaves.length := by decide +kernel
def r0713 : List (List ℕ) := ix0713.map fun i => (Pop.S0389.leaves.getD i dflt).1
theorem r0713_ok : ∀ p ∈ r0713, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0389.sem ix0713_lt

def ix0714 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]
theorem ix0714_lt : ∀ i ∈ ix0714, i < Pop.S0390.leaves.length := by decide +kernel
def r0714 : List (List ℕ) := ix0714.map fun i => (Pop.S0390.leaves.getD i dflt).1
theorem r0714_ok : ∀ p ∈ r0714, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0390.sem ix0714_lt

def ix0715 : List ℕ := [24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126]
theorem ix0715_lt : ∀ i ∈ ix0715, i < Pop.S0351.leaves.length := by decide +kernel
def r0715 : List (List ℕ) := ix0715.map fun i => (Pop.S0351.leaves.getD i dflt).1
theorem r0715_ok : ∀ p ∈ r0715, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0351.sem ix0715_lt

def ix0716 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125]
theorem ix0716_lt : ∀ i ∈ ix0716, i < Pop.S0352.leaves.length := by decide +kernel
def r0716 : List (List ℕ) := ix0716.map fun i => (Pop.S0352.leaves.getD i dflt).1
theorem r0716_ok : ∀ p ∈ r0716, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0352.sem ix0716_lt

def ix0717 : List ℕ := [34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140]
theorem ix0717_lt : ∀ i ∈ ix0717, i < Pop.S0354.leaves.length := by decide +kernel
def r0717 : List (List ℕ) := ix0717.map fun i => (Pop.S0354.leaves.getD i dflt).1
theorem r0717_ok : ∀ p ∈ r0717, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0354.sem ix0717_lt

def ix0718 : List ℕ := [90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]
theorem ix0718_lt : ∀ i ∈ ix0718, i < Pop.S0357.leaves.length := by decide +kernel
def r0718 : List (List ℕ) := ix0718.map fun i => (Pop.S0357.leaves.getD i dflt).1
theorem r0718_ok : ∀ p ∈ r0718, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0357.sem ix0718_lt

def ix0719 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141]
theorem ix0719_lt : ∀ i ∈ ix0719, i < Pop.S0358.leaves.length := by decide +kernel
def r0719 : List (List ℕ) := ix0719.map fun i => (Pop.S0358.leaves.getD i dflt).1
theorem r0719_ok : ∀ p ∈ r0719, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0358.sem ix0719_lt

def ix0720 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]
theorem ix0720_lt : ∀ i ∈ ix0720, i < Pop.S0359.leaves.length := by decide +kernel
def r0720 : List (List ℕ) := ix0720.map fun i => (Pop.S0359.leaves.getD i dflt).1
theorem r0720_ok : ∀ p ∈ r0720, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0359.sem ix0720_lt

def ix0721 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118]
theorem ix0721_lt : ∀ i ∈ ix0721, i < Pop.S0360.leaves.length := by decide +kernel
def r0721 : List (List ℕ) := ix0721.map fun i => (Pop.S0360.leaves.getD i dflt).1
theorem r0721_ok : ∀ p ∈ r0721, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0360.sem ix0721_lt

def ix0722 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]
theorem ix0722_lt : ∀ i ∈ ix0722, i < Pop.S0361.leaves.length := by decide +kernel
def r0722 : List (List ℕ) := ix0722.map fun i => (Pop.S0361.leaves.getD i dflt).1
theorem r0722_ok : ∀ p ∈ r0722, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0361.sem ix0722_lt

def ix0723 : List ℕ := [79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104]
theorem ix0723_lt : ∀ i ∈ ix0723, i < Pop.S0364.leaves.length := by decide +kernel
def r0723 : List (List ℕ) := ix0723.map fun i => (Pop.S0364.leaves.getD i dflt).1
theorem r0723_ok : ∀ p ∈ r0723, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0364.sem ix0723_lt

def ix0724 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114]
theorem ix0724_lt : ∀ i ∈ ix0724, i < Pop.S0365.leaves.length := by decide +kernel
def r0724 : List (List ℕ) := ix0724.map fun i => (Pop.S0365.leaves.getD i dflt).1
theorem r0724_ok : ∀ p ∈ r0724, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0365.sem ix0724_lt

def ix0725 : List ℕ := [0]
theorem ix0725_lt : ∀ i ∈ ix0725, i < Pop.S0366.leaves.length := by decide +kernel
def r0725 : List (List ℕ) := ix0725.map fun i => (Pop.S0366.leaves.getD i dflt).1
theorem r0725_ok : ∀ p ∈ r0725, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0366.sem ix0725_lt

def ix0726 : List ℕ := [91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115]
theorem ix0726_lt : ∀ i ∈ ix0726, i < Pop.S0367.leaves.length := by decide +kernel
def r0726 : List (List ℕ) := ix0726.map fun i => (Pop.S0367.leaves.getD i dflt).1
theorem r0726_ok : ∀ p ∈ r0726, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0367.sem ix0726_lt

def ix0727 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]
theorem ix0727_lt : ∀ i ∈ ix0727, i < Pop.S0368.leaves.length := by decide +kernel
def r0727 : List (List ℕ) := ix0727.map fun i => (Pop.S0368.leaves.getD i dflt).1
theorem r0727_ok : ∀ p ∈ r0727, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0368.sem ix0727_lt

def ix0728 : List ℕ := [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]
theorem ix0728_lt : ∀ i ∈ ix0728, i < Pop.S0371.leaves.length := by decide +kernel
def r0728 : List (List ℕ) := ix0728.map fun i => (Pop.S0371.leaves.getD i dflt).1
theorem r0728_ok : ∀ p ∈ r0728, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0371.sem ix0728_lt

def ix0729 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]
theorem ix0729_lt : ∀ i ∈ ix0729, i < Pop.S0372.leaves.length := by decide +kernel
def r0729 : List (List ℕ) := ix0729.map fun i => (Pop.S0372.leaves.getD i dflt).1
theorem r0729_ok : ∀ p ∈ r0729, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0372.sem ix0729_lt

def ix0730 : List ℕ := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]
theorem ix0730_lt : ∀ i ∈ ix0730, i < Pop.S0366.leaves.length := by decide +kernel
def r0730 : List (List ℕ) := ix0730.map fun i => (Pop.S0366.leaves.getD i dflt).1
theorem r0730_ok : ∀ p ∈ r0730, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0366.sem ix0730_lt

def ix0731 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90]
theorem ix0731_lt : ∀ i ∈ ix0731, i < Pop.S0367.leaves.length := by decide +kernel
def r0731 : List (List ℕ) := ix0731.map fun i => (Pop.S0367.leaves.getD i dflt).1
theorem r0731_ok : ∀ p ∈ r0731, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0367.sem ix0731_lt

def ix0732 : List ℕ := [26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119]
theorem ix0732_lt : ∀ i ∈ ix0732, i < Pop.S0370.leaves.length := by decide +kernel
def r0732 : List (List ℕ) := ix0732.map fun i => (Pop.S0370.leaves.getD i dflt).1
theorem r0732_ok : ∀ p ∈ r0732, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0370.sem ix0732_lt

def ix0733 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52]
theorem ix0733_lt : ∀ i ∈ ix0733, i < Pop.S0371.leaves.length := by decide +kernel
def r0733 : List (List ℕ) := ix0733.map fun i => (Pop.S0371.leaves.getD i dflt).1
theorem r0733_ok : ∀ p ∈ r0733, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0371.sem ix0733_lt

def ix0734 : List ℕ := [34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]
theorem ix0734_lt : ∀ i ∈ ix0734, i < Pop.S0372.leaves.length := by decide +kernel
def r0734 : List (List ℕ) := ix0734.map fun i => (Pop.S0372.leaves.getD i dflt).1
theorem r0734_ok : ∀ p ∈ r0734, CKLaneG3.SLeafOK (CKLaneG3.sBox p) := idx_ok Pop.S0372.sem ix0734_lt


end CKLaneM1.ML.Population


