-- Prove2me | Definitions.Def_GirvingAKS_Halver_Empty
-- name    : GirvingAKS_Halver_Empty
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:31:15.708838+00:00
-- url     : https://prove2.me/theorems/98e35984-4dbe-4c66-8195-408599912413
-- title:
--   AKS sorting networks (Seiferas port) — Empty Network is a Perfect Halver
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Halver/Empty.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** The empty comparator network on 0 wires is trivially an ε-halver for any ε: with 0 wires, `0/2 = 0` makes all `∀ k ≤ 0` conditions vacuous.
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Halver/Empty.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Halver_Defs

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Halver/Empty.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Empty Network is a Perfect Halver

  The empty comparator network on 0 wires is trivially an ε-halver
  for any ε: with 0 wires, `0/2 = 0` makes all `∀ k ≤ 0` conditions vacuous.
-/


section


/-- The empty network on 0 wires is an ε-halver for any ε. -/
theorem emptyNet_isEpsilonHalver (ε : ℝ) :
    IsEpsilonHalver (⟨[]⟩ : ComparatorNetwork 0) ε := by
  intro v
  constructor
  · intro k hk
    simp only [Fintype.card_fin, show 0 / 2 = 0 from rfl] at hk
    have : k = 0 := by omega
    subst this; simp
  · intro k hk
    simp only [Fintype.card_orderDual, Fintype.card_fin, show 0 / 2 = 0 from rfl] at hk
    have : k = 0 := by omega
    subst this; simp

/-- The empty network on 0 wires has depth 0. -/
theorem emptyNet_depth : (⟨[]⟩ : ComparatorNetwork 0).depth = 0 := by
  simp [ComparatorNetwork.depth]

end


