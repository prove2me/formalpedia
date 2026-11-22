-- Prove2me | Definitions.Def_GirvingAKS_Misc_Floor
-- name    : GirvingAKS_Misc_Floor
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:29:38.920506+00:00
-- url     : https://prove2.me/theorems/dbdff677-1be0-4f95-9b9e-7aad3be24215
-- title:
--   AKS sorting networks (Seiferas port) — ℚ/ℝ Floor Bridge
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Misc/Floor.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Lemmas bridging `⌊·⌋₊` between `ℚ` and `ℝ`.
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Misc/Floor.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Mathlib.Data.Real.Archimedean

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Misc/Floor.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # ℚ/ℝ Floor Bridge

  Lemmas bridging `⌊·⌋₊` between `ℚ` and `ℝ`.
-/


section

lemma floor_rat_real_eq (q : ℚ) (hq : 0 ≤ q) : ⌊(q : ℝ)⌋₊ = ⌊q⌋₊ := by
  have h1 : (⌊q⌋₊ : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.floor_le hq
  have h2 : (q : ℝ) < (⌊q⌋₊ : ℝ) + 1 := by exact_mod_cast Nat.lt_floor_add_one q
  exact (Nat.floor_eq_iff (by exact_mod_cast hq : (0 : ℝ) ≤ ↑q)).mpr ⟨h1, h2⟩

lemma floor_rat_real_mul_nat (γ : ℚ) (n : ℕ) (hγ : 0 ≤ γ) :
    ⌊(γ : ℝ) * ↑n⌋₊ = ⌊(γ : ℚ) * ↑n⌋₊ := by
  rw [show (γ : ℝ) * ↑n = ↑((γ : ℚ) * ↑n) from by push_cast; ring]
  exact floor_rat_real_eq _ (mul_nonneg hγ (Nat.cast_nonneg _))

end


