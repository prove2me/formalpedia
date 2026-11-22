-- Prove2me | Definitions.Def_GirvingAKS_Separator_Family
-- name    : GirvingAKS_Separator_Family
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:31:12.271627+00:00
-- url     : https://prove2.me/theorems/6d7f7131-bf9b-4910-a932-26d014b0fe47
-- title:
--   AKS sorting networks (Seiferas port) — Separator Family
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Separator/Family.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Families of (γ, ε)-separator networks with bounded depth, analogous to `HalverFamily` in `Halver/Defs.lean`.
--
--   Key definitions:
--
--   - `SeparatorFamily` — structure bundling computable networks + proofs
--   - `SeparatorFamily.twice_size_le` — size bound derived from depth bound
--   - `SeparatorFamily.forWireCount` — bridge to arbitrary wire-count consumers
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Separator/Family.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Separator_Defs
import Definitions.Def_GirvingAKS_Sort_Depth
import Definitions.Def_GirvingAKS_Halver_Defs

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Separator/Family.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Separator Family

  Families of (γ, ε)-separator networks with bounded depth, analogous
  to `HalverFamily` in `Halver/Defs.lean`.

  Key definitions:
  • `SeparatorFamily` — structure bundling computable networks + proofs
  • `SeparatorFamily.twice_size_le` — size bound derived from depth bound
  • `SeparatorFamily.forWireCount` — bridge to arbitrary wire-count consumers
-/


section


open Finset BigOperators


/-! **Separator Family** -/

/-- A family of (γ, ε)-separator networks at all even sizes, with bounded
    depth. Mirrors `HalverFamily`: `net m` operates on `2 * m` wires.

    The type encodes which sizes exist: `net m` always operates on `2 * m`
    wires — no junk values, no validity threading. The depth bound is
    fundamental: `2 * (net m).size ≤ (2 * m) * depth` follows from
    `size_le_half_n_mul_depth`. -/
structure SeparatorFamily (γ ε : ℚ) where
  /-- Uniform depth bound for all networks in the family. -/
  depth : ℕ
  /-- The separator network for each index `m`. Operates on `2 * m` wires. -/
  net : (m : ℕ) → ComparatorNetwork (2 * m)
  /-- Each network is a (γ, ε)-separator. -/
  isSeparator : ∀ m, IsSeparator (net m) ↑γ ↑ε
  /-- Each network is an ε-halver (halving property).
      The separator is built from halvers, so it halves at the midpoint
      as well as separating at the γ-boundary. Used for the source-3
      halving error bound in `Bags/Strange.lean` (Seiferas 2009, Section 5). -/
  isHalver : ∀ m, IsEpsilonHalver (net m) ↑ε
  /-- Each network has depth at most `depth`. -/
  depth_le : ∀ m, (net m).depth ≤ depth

/-- Size bound derived from depth: `2 * size ≤ (2 * m) * sep.depth`. -/
theorem SeparatorFamily.twice_size_le {γ ε : ℚ}
    (family : SeparatorFamily γ ε) (m : ℕ) :
    2 * (family.net m).size ≤ (2 * m) * family.depth :=
  calc 2 * (family.net m).size
      ≤ (2 * m) * (family.net m).depth := size_le_half_n_mul_depth (family.net m)
    _ ≤ (2 * m) * family.depth := Nat.mul_le_mul_left _ (family.depth_le m)


/-! **Wire Count Bridge** -/

/-- Bridge a `SeparatorFamily` to an arbitrary wire count `n`.
    If `n` is even (`2 * (n / 2) = n`), uses `sep.net (n / 2)` cast to `n` wires.
    Otherwise returns the empty network. -/
def SeparatorFamily.forWireCount {γ ε : ℚ}
    (sep : SeparatorFamily γ ε) (n : ℕ) :
    ComparatorNetwork n :=
  if h : 2 * (n / 2) = n
  then (sep.net (n / 2)).cast h
  else ⟨[]⟩

/-- `forWireCount` has depth at most `sep.depth`. -/
theorem SeparatorFamily.forWireCount_depth_le {γ ε : ℚ}
    (sep : SeparatorFamily γ ε) (n : ℕ) :
    (sep.forWireCount n).depth ≤ sep.depth := by
  unfold forWireCount; split
  · simp [ComparatorNetwork.cast_depth, sep.depth_le]
  · simp [ComparatorNetwork.depth]

end


