-- Prove2me | Definitions.Def_GirvingAKS_Bitonic_Shrink
-- name    : GirvingAKS_Bitonic_Shrink
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:34:02.460481+00:00
-- url     : https://prove2.me/theorems/b0cd8edb-93c9-4185-8b6f-8505db290752
-- title:
--   AKS sorting networks (Seiferas port) — Bitonic Sort for Arbitrary n
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Bitonic/Shrink.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Restricts `bitonicSort k` (which operates on `2^k` wires) to arbitrary `n` wires via `restrictWires`, using `k = ⌈log₂ n⌉`.
--
--   Main results:
--
--   - `bitonicNetwork`          : computable sorting network for any n
--   - `bitonicNetwork_sorts`    : it sorts
--   - `bitonicNetwork_depth_le` : depth ≤ (⌈log₂ n⌉)²
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Bitonic/Shrink.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Bitonic_Correctness
import Definitions.Def_GirvingAKS_Bitonic_Depth
import Definitions.Def_GirvingAKS_Sort_Shrink

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Bitonic/Shrink.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Bitonic Sort for Arbitrary n

  Restricts `bitonicSort k` (which operates on `2^k` wires) to arbitrary `n`
  wires via `restrictWires`, using `k = ⌈log₂ n⌉`.

  Main results:
  - `bitonicNetwork`          : computable sorting network for any n
  - `bitonicNetwork_sorts`    : it sorts
  - `bitonicNetwork_depth_le` : depth ≤ (⌈log₂ n⌉)²
-/


section

/-- Bitonic sorting network for arbitrary `n`, by restricting `bitonicSort ⌈log₂ n⌉`
    from `2^⌈log₂ n⌉` wires down to `n`. -/
def bitonicNetwork (n : ℕ) : ComparatorNetwork n :=
  (bitonicSort (Nat.clog 2 n)).restrictWires n (Nat.le_pow_clog (by omega) n)

/-- `bitonicNetwork` sorts all inputs. -/
theorem bitonicNetwork_sorts (n : ℕ) : (bitonicNetwork n).Sorts := by
  unfold bitonicNetwork
  exact restrictWires_sorts _ _ _ (fun v ↦ bitonicSort_sorts _ Bool v)

/-- `bitonicNetwork n` has depth at most `(⌈log₂ n⌉)²`. -/
theorem bitonicNetwork_depth_le (n : ℕ) :
    (bitonicNetwork n).depth ≤ (Nat.clog 2 n) ^ 2 := by
  unfold bitonicNetwork
  exact (restrictWires_depth_le _ _ _).trans (bitonicSort_depth_le _)

end


