-- Prove2me | Definitions.Def_GirvingAKS_Seiferas
-- name    : GirvingAKS_Seiferas
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T19:38:20.761789+00:00
-- url     : https://prove2.me/theorems/23ddce90-1163-4895-a1cd-df5d9b1cf6dd
-- title:
--   AKS sorting networks (Seiferas port) — Main Theorem: O(log n)-Depth Sorting Networks
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Seiferas.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Assembles the Seiferas (2009) separator-based sorting network construction into a single `network n : ComparatorNetwork n` for all `n`.
--
--   For `n ≥ 1024` (i.e., `10 ≤ ⌈log₂ n⌉`), uses `seiferasNetwork` at power-of-2 size `2^⌈log₂ n⌉`, then `restrictWires` down to `n`. For `n < 1024`, uses `bitonicNetwork` (Batcher's bitonic sort).
--
--   Three results:
--
--   1. `network_sorts`: the network sorts all inputs
--   2. `network_depth_le`: `depth = 141 * 10 ^ 62 * ⌈log₂ n⌉`  (O(log n))
--   3. `network_size_le`: `size ≤ 705 * 10 ^ 61 * n * ⌈log₂ n⌉`  (O(n log n))
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Seiferas.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Bags_Depth
import Definitions.Def_GirvingAKS_Sort_ZeroOne

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Seiferas.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Main Theorem: O(log n)-Depth Sorting Networks

  Assembles the Seiferas (2009) separator-based sorting network construction
  into a single `network n : ComparatorNetwork n` for all `n`.

  For `n ≥ 1024` (i.e., `10 ≤ ⌈log₂ n⌉`), uses `seiferasNetwork` at
  power-of-2 size `2^⌈log₂ n⌉`, then `restrictWires` down to `n`.
  For `n < 1024`, uses `bitonicNetwork` (Batcher's bitonic sort).

  Three results:
  1. `network_sorts`: the network sorts all inputs
  2. `network_depth_le`: `depth = 141 * 10 ^ 62 * ⌈log₂ n⌉`  (O(log n))
  3. `network_size_le`: `size ≤ 705 * 10 ^ 61 * n * ⌈log₂ n⌉`  (O(n log n))
-/


/-! **Definition** -/

/-- O(log n)-depth sorting network for any `n`.
    Uses Seiferas's separator-based construction for `n ≥ 1024`,
    Batcher's bitonic sort for smaller inputs. -/
def network (n : ℕ) : ComparatorNetwork n :=
  if h : 1024 ≤ n then
    (seiferasNetwork seiferasParams (Nat.clog 2 n)).restrictWires n
      (Nat.le_pow_clog (by omega) n)
  else
    bitonicNetwork n

/-! **Correctness** -/

theorem network_sorts (n : ℕ) : (network n).Sorts := by
  unfold network; split
  case isTrue h =>
    have hk : 10 ≤ Nat.clog 2 n :=
      (show (10 : ℕ) = Nat.clog 2 1024 by decide +kernel) ▸ Nat.clog_mono_right 2 h
    exact restrictWires_sorts _ _ _ (fun v ↦ (seiferasNetwork_sorts _ _ hk) _ v)
  case isFalse => exact bitonicNetwork_sorts n

/-! **Depth** -/

theorem network_depth_le (n : ℕ) :
    (network n).depth ≤ 141 * 10 ^ 62 * Nat.clog 2 n := by
  set C := 141 * 10 ^ 62
  unfold network; split
  case isTrue h =>
    have hk : 10 ≤ Nat.clog 2 n :=
      (show (10 : ℕ) = Nat.clog 2 1024 by decide +kernel) ▸ Nat.clog_mono_right 2 h
    exact (restrictWires_depth_le _ _ _).trans
      ((seiferasNetwork_depth_le _ _ hk).trans
        (Nat.mul_le_mul_right _ seiferasParams_depth_le))
  case isFalse h =>
    set k := Nat.clog 2 n
    calc (bitonicNetwork n).depth
        ≤ k ^ 2 := bitonicNetwork_depth_le n
      _ = k * k := by ring
      _ ≤ C * k := by
          apply Nat.mul_le_mul_right
          calc k ≤ Nat.clog 2 1023 := Nat.clog_mono_right 2 (by omega)
            _ ≤ C := by decide +kernel

/-! **Size** -/

theorem network_size_le (n : ℕ) :
    (network n).size ≤ 705 * 10 ^ 61 * n * Nat.clog 2 n := by
  have h := (size_le_half_n_mul_depth (network n)).trans
    (Nat.mul_le_mul_left _ (network_depth_le n))
  set k := Nat.clog 2 n
  have h2 : n * (141 * 10 ^ 62 * k) = 2 * (705 * 10 ^ 61 * n * k) := by ring
  linarith

/-! **Existential version for `comparator` purposes** -/

/-- A pure theorem (no defs) for use with https://github.com/leanprover/comparator -/
theorem networks_exist (n : ℕ) : ∃ net : ComparatorNetwork n, net.Sorts ∧
    net.depth ≤ 141 * 10 ^ 62 * Nat.clog 2 n ∧
    net.size ≤ 705 * 10 ^ 61 * n * Nat.clog 2 n :=
  ⟨network n, network_sorts n, network_depth_le n, network_size_le n⟩


