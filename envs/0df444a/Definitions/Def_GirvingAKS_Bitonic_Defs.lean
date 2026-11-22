-- Prove2me | Definitions.Def_GirvingAKS_Bitonic_Defs
-- name    : GirvingAKS_Bitonic_Defs
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:30:31.691582+00:00
-- url     : https://prove2.me/theorems/3d68099e-d933-4570-9251-7724e8f0f0b8
-- title:
--   AKS sorting networks (Seiferas port) — Bitonic Sort — Core Definitions
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Bitonic/Defs.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Batcher's (1968) bitonic sorting network for 2^k wires.
--
--   Definitions:
--
--   - `bitonicCompareLayer k` — one parallel layer comparing (i, i+2^k)
--   - `ComparatorNetwork.flip` — reverse wire order via `Fin.rev`
--   - `bitonicCrossLayer k` — cross compare layer pairing (i, 2^(k+1)-1-i)
--   - `bitonicMerge k` — recursive bitonic merge on 2^k wires
--   - `bitonicSort k` — recursive bitonic sort on 2^k wires
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Bitonic/Defs.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Sort_Defs

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Bitonic/Defs.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Bitonic Sort — Core Definitions

  Batcher's (1968) bitonic sorting network for 2^k wires.

  Definitions:
  - `bitonicCompareLayer k` — one parallel layer comparing (i, i+2^k)
  - `ComparatorNetwork.flip` — reverse wire order via `Fin.rev`
  - `bitonicCrossLayer k` — cross compare layer pairing (i, 2^(k+1)-1-i)
  - `bitonicMerge k` — recursive bitonic merge on 2^k wires
  - `bitonicSort k` — recursive bitonic sort on 2^k wires
-/


section

/-! **Bitonic Compare Layer** -/

/-- One parallel layer of `2^k` comparators on `2^(k+1)` wires.
    Compares position `i` with `i + 2^k` for all `i < 2^k`. -/
def bitonicCompareLayer (k : Nat) : ComparatorNetwork (2^(k+1)) :=
  { comparators := (List.finRange (2^k)).map fun i ↦
      { i := ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩
        j := ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩
        h := by simp only [Fin.lt_def]; omega } }

@[simp] theorem bitonicCompareLayer_size (k : Nat) :
    (bitonicCompareLayer k).size = 2^k := by
  simp [bitonicCompareLayer, ComparatorNetwork.size, List.length_map, List.length_finRange]

/-! **Wire Reversal (Flip)** -/

/-- Reverse the wire order of a comparator network via `Fin.rev`.
    Maps each comparator `(i, j)` to `(j.rev, i.rev)`, preserving the
    `i < j` invariant since `i < j ↔ j.rev < i.rev`. -/
def ComparatorNetwork.flip {n : Nat} (net : ComparatorNetwork n) : ComparatorNetwork n :=
  { comparators := net.comparators.map fun c ↦
      { i := c.j.rev
        j := c.i.rev
        h := Fin.rev_lt_rev.mpr c.h } }

@[simp] theorem ComparatorNetwork.flip_size {n : Nat} (net : ComparatorNetwork n) :
    net.flip.size = net.size := by
  simp [flip, size, List.length_map]

/-! **Bitonic Merge** -/

/-- Bitonic merge on `2^k` wires: recursively applies a compare layer
    then merges both halves independently.
    - k=0: empty (1 wire, nothing to do)
    - k+1: compare layer at distance `2^k`, then merge both halves -/
def bitonicMerge : (k : Nat) → ComparatorNetwork (2^k)
  | 0 => ⟨[]⟩
  | k + 1 =>
    have h0 : 0 + 2^k ≤ 2^(k+1) := by rw [Nat.pow_succ]; omega
    have h1 : 2^k + 2^k ≤ 2^(k+1) := by rw [Nat.pow_succ]; omega
    let layer := bitonicCompareLayer k
    let left := (bitonicMerge k).shiftEmbed (2^(k+1)) 0 h0
    let right := (bitonicMerge k).shiftEmbed (2^(k+1)) (2^k) h1
    ⟨layer.comparators ++ left.comparators ++ right.comparators⟩

/-! **Cross Compare Layer** -/

/-- Cross compare layer: pairs position `i` with `2^(k+1) - 1 - i` for
    all `i < 2^k`. After two ascending halves, this creates bitonic halves
    with left ≤ right, enabling standard `bitonicMerge` on each half. -/
def bitonicCrossLayer (k : Nat) : ComparatorNetwork (2^(k+1)) :=
  { comparators := (List.finRange (2^k)).map fun i ↦
      { i := ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩
        j := ⟨2^(k+1) - 1 - i.val, by rw [Nat.pow_succ]; omega⟩
        h := by simp only [Fin.lt_def]; have := i.isLt; rw [Nat.pow_succ]; omega } }

@[simp] theorem bitonicCrossLayer_size (k : Nat) :
    (bitonicCrossLayer k).size = 2^k := by
  simp [bitonicCrossLayer, ComparatorNetwork.size, List.length_map, List.length_finRange]

/-! **Bitonic Sort** -/

/-- Bitonic sort on `2^k` wires: recursively sort both halves ascending,
    apply a cross compare layer to create bitonic halves, then merge each
    half with `bitonicMerge`.
    - k=0: empty (1 wire, already sorted)
    - k+1: sort both halves, cross layer, merge both halves -/
def bitonicSort : (k : Nat) → ComparatorNetwork (2^k)
  | 0 => ⟨[]⟩
  | k + 1 =>
    have h0 : 0 + 2^k ≤ 2^(k+1) := by rw [Nat.pow_succ]; omega
    have h1 : 2^k + 2^k ≤ 2^(k+1) := by rw [Nat.pow_succ]; omega
    let sortLeft := (bitonicSort k).shiftEmbed (2^(k+1)) 0 h0
    let sortRight := (bitonicSort k).shiftEmbed (2^(k+1)) (2^k) h1
    let cross := bitonicCrossLayer k
    let mergeLeft := (bitonicMerge k).shiftEmbed (2^(k+1)) 0 h0
    let mergeRight := (bitonicMerge k).shiftEmbed (2^(k+1)) (2^k) h1
    ⟨sortLeft.comparators ++ sortRight.comparators ++
     cross.comparators ++ mergeLeft.comparators ++ mergeRight.comparators⟩

end


