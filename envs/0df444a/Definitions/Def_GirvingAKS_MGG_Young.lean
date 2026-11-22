-- Prove2me | Definitions.Def_GirvingAKS_MGG_Young
-- name    : GirvingAKS_MGG_Young
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:37:13.0047+00:00
-- url     : https://prove2.me/theorems/02611f7f-cff0-48d5-8f6a-4e83801d8b47
-- title:
--   AKS sorting networks (Seiferas port) — Young's Inequality: Diamond Geometry
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/MGG/Young.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Diamond and outside-diamond case analysis for the pointwise condition. Depends on `YoungDefs.lean` for definitions and helper lemmas.
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/MGG/Young.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_MGG_YoungDefs

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/MGG/Young.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Young's Inequality: Diamond Geometry

  Diamond and outside-diamond case analysis for the pointwise condition.
  Depends on `YoungDefs.lean` for definitions and helper lemmas.
-/


section

open Matrix BigOperators Finset Real
open scoped Real

/-- Inside the diamond, both S₂ neighbors cannot simultaneously be strictly closer.
    Numerically verified for `n ≤ 300`. -/
theorem diamond_no_both_S2_closer (n α₁ α₂ : ℕ) (hn : 3 ≤ n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n)
    (hdiam : zmodDist n α₁ + zmodDist n α₂ ≤ n / 2) :
    ¬(zmodDist n (shearS2 n α₁ α₂).2 < zmodDist n α₂ ∧
      zmodDist n (shearS2Inv n α₁ α₂).2 < zmodDist n α₂) := by
  intro ⟨hs2, hs2i⟩
  rw [zd_S2 n α₁ α₂ hα₁ hα₂ (by omega)] at hs2
  rw [zd_S2I n α₁ α₂ hα₁ hα₂ (by omega)] at hs2i
  unfold zmodDist at hdiam hs2 hs2i
  by_cases h1 : 2 * α₁ < n
  · simp only [double_mod_lo n α₁ h1] at hs2 hs2i
    simp only [Nat.min_def] at hs2 hs2i hdiam; split_ifs at hdiam hs2 hs2i <;> omega
  · simp only [double_mod_hi n α₁ hα₁ h1] at hs2 hs2i
    simp only [Nat.min_def] at hs2 hs2i hdiam; split_ifs at hdiam hs2 hs2i <;> omega

/-- Inside the diamond, both S₁ neighbors cannot simultaneously be strictly closer.
    Symmetric version of `diamond_no_both_S2_closer`. -/
theorem diamond_no_both_S1_closer (n α₁ α₂ : ℕ) (hn : 3 ≤ n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n)
    (hdiam : zmodDist n α₁ + zmodDist n α₂ ≤ n / 2) :
    ¬(zmodDist n (shearS1 n α₁ α₂).1 < zmodDist n α₁ ∧
      zmodDist n (shearS1Inv n α₁ α₂).1 < zmodDist n α₁) := by
  intro ⟨hs1, hs1i⟩
  rw [zd_S1 n α₁ α₂ hα₁ hα₂ (by omega)] at hs1
  rw [zd_S1I n α₁ α₂ hα₁ hα₂ (by omega)] at hs1i
  unfold zmodDist at hdiam hs1 hs1i
  by_cases h2 : 2 * α₂ < n
  · simp only [double_mod_lo n α₂ h2] at hs1 hs1i
    simp only [Nat.min_def] at hs1 hs1i hdiam; split_ifs at hdiam hs1 hs1i <;> omega
  · simp only [double_mod_hi n α₂ hα₂ h2] at hs1 hs1i
    simp only [Nat.min_def] at hs1 hs1i hdiam; split_ifs at hdiam hs1 hs1i <;> omega

/-- In the strict diamond (`2(d₁+d₂) < n`), if S₂ is closer then the other 3
    neighbors are strictly farther. -/
theorem strict_diamond_closer_S2_all_farther (n α₁ α₂ : ℕ) (hn : 3 ≤ n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n)
    (hstrict : 2 * (zmodDist n α₁ + zmodDist n α₂) + 1 ≤ n)
    (hs2 : zmodDist n (shearS2 n α₁ α₂).2 < zmodDist n α₂) :
    zmodDist n α₂ < zmodDist n (shearS2Inv n α₁ α₂).2 ∧
    zmodDist n α₁ < zmodDist n (shearS1 n α₁ α₂).1 ∧
    zmodDist n α₁ < zmodDist n (shearS1Inv n α₁ α₂).1 := by
  rw [zd_S2 n α₁ α₂ hα₁ hα₂ (by omega)] at hs2
  rw [zd_S2I n α₁ α₂ hα₁ hα₂ (by omega),
      zd_S1 n α₁ α₂ hα₁ hα₂ (by omega),
      zd_S1I n α₁ α₂ hα₁ hα₂ (by omega)]
  unfold zmodDist at hstrict hs2 ⊢
  by_cases h1 : 2 * α₁ < n <;> by_cases h2 : 2 * α₂ < n
  · simp only [double_mod_lo n α₁ h1, double_mod_lo n α₂ h2,
      Nat.min_eq_left (by omega : α₁ ≤ n - α₁),
      Nat.min_eq_left (by omega : α₂ ≤ n - α₂)] at hstrict hs2 ⊢
    simp only [Nat.min_def] at hs2 ⊢; split_ifs at hs2 <;> (refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega)
  · simp only [double_mod_lo n α₁ h1, double_mod_hi n α₂ hα₂ h2,
      Nat.min_eq_left (by omega : α₁ ≤ n - α₁),
      Nat.min_eq_right (by omega : n - α₂ ≤ α₂)] at hstrict hs2 ⊢
    simp only [Nat.min_def] at hs2 ⊢; split_ifs at hs2 <;> (refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega)
  · simp only [double_mod_hi n α₁ hα₁ h1, double_mod_lo n α₂ h2,
      Nat.min_eq_right (by omega : n - α₁ ≤ α₁),
      Nat.min_eq_left (by omega : α₂ ≤ n - α₂)] at hstrict hs2 ⊢
    simp only [Nat.min_def] at hs2 ⊢; split_ifs at hs2 <;> (refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega)
  · simp only [double_mod_hi n α₁ hα₁ h1, double_mod_hi n α₂ hα₂ h2,
      Nat.min_eq_right (by omega : n - α₁ ≤ α₁),
      Nat.min_eq_right (by omega : n - α₂ ≤ α₂)] at hstrict hs2 ⊢
    simp only [Nat.min_def] at hs2 ⊢; split_ifs at hs2 <;> (refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega)

/-- Symmetric: if S₂⁻¹ closer in strict diamond, all other 3 are farther. -/
theorem strict_diamond_closer_S2Inv_all_farther (n α₁ α₂ : ℕ) (hn : 3 ≤ n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n)
    (hstrict : 2 * (zmodDist n α₁ + zmodDist n α₂) + 1 ≤ n)
    (hs2i : zmodDist n (shearS2Inv n α₁ α₂).2 < zmodDist n α₂) :
    zmodDist n α₂ < zmodDist n (shearS2 n α₁ α₂).2 ∧
    zmodDist n α₁ < zmodDist n (shearS1 n α₁ α₂).1 ∧
    zmodDist n α₁ < zmodDist n (shearS1Inv n α₁ α₂).1 := by
  rw [zd_S2I n α₁ α₂ hα₁ hα₂ (by omega)] at hs2i
  rw [zd_S2 n α₁ α₂ hα₁ hα₂ (by omega),
      zd_S1 n α₁ α₂ hα₁ hα₂ (by omega),
      zd_S1I n α₁ α₂ hα₁ hα₂ (by omega)]
  unfold zmodDist at hstrict hs2i ⊢
  by_cases h1 : 2 * α₁ < n <;> by_cases h2 : 2 * α₂ < n
  · simp only [double_mod_lo n α₁ h1, double_mod_lo n α₂ h2,
      Nat.min_eq_left (by omega : α₁ ≤ n - α₁),
      Nat.min_eq_left (by omega : α₂ ≤ n - α₂)] at hstrict hs2i ⊢
    simp only [Nat.min_def] at hs2i ⊢; split_ifs at hs2i <;> (refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega)
  · simp only [double_mod_lo n α₁ h1, double_mod_hi n α₂ hα₂ h2,
      Nat.min_eq_left (by omega : α₁ ≤ n - α₁),
      Nat.min_eq_right (by omega : n - α₂ ≤ α₂)] at hstrict hs2i ⊢
    simp only [Nat.min_def] at hs2i ⊢; split_ifs at hs2i <;> (refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega)
  · simp only [double_mod_hi n α₁ hα₁ h1, double_mod_lo n α₂ h2,
      Nat.min_eq_right (by omega : n - α₁ ≤ α₁),
      Nat.min_eq_left (by omega : α₂ ≤ n - α₂)] at hstrict hs2i ⊢
    simp only [Nat.min_def] at hs2i ⊢; split_ifs at hs2i <;> (refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega)
  · simp only [double_mod_hi n α₁ hα₁ h1, double_mod_hi n α₂ hα₂ h2,
      Nat.min_eq_right (by omega : n - α₁ ≤ α₁),
      Nat.min_eq_right (by omega : n - α₂ ≤ α₂)] at hstrict hs2i ⊢
    simp only [Nat.min_def] at hs2i ⊢; split_ifs at hs2i <;> (refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega)

/-- In strict diamond, S₂ pair both E implies S₁ pair both farther.
    Verified numerically for `n ≤ 200`. -/
theorem strict_diamond_S2_both_eq_implies_S1_farther (n α₁ α₂ : ℕ) (hn : 3 ≤ n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n) (hne : ¬(α₁ = 0 ∧ α₂ = 0))
    (hstrict : 2 * (zmodDist n α₁ + zmodDist n α₂) + 1 ≤ n)
    (hs2_eq : zmodDist n (shearS2 n α₁ α₂).2 = zmodDist n α₂)
    (hs2i_eq : zmodDist n (shearS2Inv n α₁ α₂).2 = zmodDist n α₂) :
    zmodDist n α₁ < zmodDist n (shearS1 n α₁ α₂).1 ∧
    zmodDist n α₁ < zmodDist n (shearS1Inv n α₁ α₂).1 := by
  rw [zd_S2 n α₁ α₂ hα₁ hα₂ (by omega)] at hs2_eq
  rw [zd_S2I n α₁ α₂ hα₁ hα₂ (by omega)] at hs2i_eq
  rw [zd_S1 n α₁ α₂ hα₁ hα₂ (by omega),
      zd_S1I n α₁ α₂ hα₁ hα₂ (by omega)]
  unfold zmodDist at hstrict hs2_eq hs2i_eq ⊢
  by_cases h1 : 2 * α₁ < n <;> by_cases h2 : 2 * α₂ < n
  · simp only [double_mod_lo n α₁ h1, double_mod_lo n α₂ h2,
      Nat.min_eq_left (by omega : α₁ ≤ n - α₁),
      Nat.min_eq_left (by omega : α₂ ≤ n - α₂)] at hstrict hs2_eq hs2i_eq ⊢
    simp only [Nat.min_def] at hs2_eq hs2i_eq ⊢
    split_ifs at hs2_eq <;> (try omega) <;> split_ifs at hs2i_eq <;> (try omega);
      constructor <;> split_ifs <;> omega
  · simp only [double_mod_lo n α₁ h1, double_mod_hi n α₂ hα₂ h2,
      Nat.min_eq_left (by omega : α₁ ≤ n - α₁),
      Nat.min_eq_right (by omega : n - α₂ ≤ α₂)] at hstrict hs2_eq hs2i_eq ⊢
    simp only [Nat.min_def] at hs2_eq hs2i_eq ⊢
    split_ifs at hs2_eq <;> (try omega); split_ifs at hs2i_eq <;> (try omega);
      constructor <;> split_ifs <;> omega
  · simp only [double_mod_hi n α₁ hα₁ h1, double_mod_lo n α₂ h2,
      Nat.min_eq_right (by omega : n - α₁ ≤ α₁),
      Nat.min_eq_left (by omega : α₂ ≤ n - α₂)] at hstrict hs2_eq hs2i_eq ⊢
    simp only [Nat.min_def] at hs2_eq hs2i_eq ⊢
    split_ifs at hs2_eq <;> omega
  · simp only [double_mod_hi n α₁ hα₁ h1, double_mod_hi n α₂ hα₂ h2,
      Nat.min_eq_right (by omega : n - α₁ ≤ α₁),
      Nat.min_eq_right (by omega : n - α₂ ≤ α₂)] at hstrict hs2_eq hs2i_eq ⊢
    simp only [Nat.min_def] at hs2_eq hs2i_eq ⊢
    split_ifs at hs2_eq <;> (try omega); split_ifs at hs2i_eq <;> omega

/-- Symmetric: S₁ pair both E implies S₂ pair both farther. -/
theorem strict_diamond_S1_both_eq_implies_S2_farther (n α₁ α₂ : ℕ) (hn : 3 ≤ n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n) (hne : ¬(α₁ = 0 ∧ α₂ = 0))
    (hstrict : 2 * (zmodDist n α₁ + zmodDist n α₂) + 1 ≤ n)
    (hs1_eq : zmodDist n (shearS1 n α₁ α₂).1 = zmodDist n α₁)
    (hs1i_eq : zmodDist n (shearS1Inv n α₁ α₂).1 = zmodDist n α₁) :
    zmodDist n α₂ < zmodDist n (shearS2 n α₁ α₂).2 ∧
    zmodDist n α₂ < zmodDist n (shearS2Inv n α₁ α₂).2 := by
  rw [zd_S1 n α₁ α₂ hα₁ hα₂ (by omega)] at hs1_eq
  rw [zd_S1I n α₁ α₂ hα₁ hα₂ (by omega)] at hs1i_eq
  rw [zd_S2 n α₁ α₂ hα₁ hα₂ (by omega),
      zd_S2I n α₁ α₂ hα₁ hα₂ (by omega)]
  unfold zmodDist at hstrict hs1_eq hs1i_eq ⊢
  by_cases h1 : 2 * α₁ < n <;> by_cases h2 : 2 * α₂ < n
  · simp only [double_mod_lo n α₁ h1, double_mod_lo n α₂ h2,
      Nat.min_eq_left (by omega : α₁ ≤ n - α₁),
      Nat.min_eq_left (by omega : α₂ ≤ n - α₂)] at hstrict hs1_eq hs1i_eq ⊢
    simp only [Nat.min_def] at hs1_eq hs1i_eq ⊢
    split_ifs at hs1_eq <;> (try omega) <;> split_ifs at hs1i_eq <;> (try omega);
      constructor <;> split_ifs <;> omega
  · simp only [double_mod_lo n α₁ h1, double_mod_hi n α₂ hα₂ h2,
      Nat.min_eq_left (by omega : α₁ ≤ n - α₁),
      Nat.min_eq_right (by omega : n - α₂ ≤ α₂)] at hstrict hs1_eq hs1i_eq ⊢
    simp only [Nat.min_def] at hs1_eq hs1i_eq ⊢
    split_ifs at hs1_eq <;> omega
  · simp only [double_mod_hi n α₁ hα₁ h1, double_mod_lo n α₂ h2,
      Nat.min_eq_right (by omega : n - α₁ ≤ α₁),
      Nat.min_eq_left (by omega : α₂ ≤ n - α₂)] at hstrict hs1_eq hs1i_eq ⊢
    simp only [Nat.min_def] at hs1_eq hs1i_eq ⊢
    split_ifs at hs1_eq <;> (try omega); split_ifs at hs1i_eq <;> (try omega);
      constructor <;> split_ifs <;> omega
  · simp only [double_mod_hi n α₁ hα₁ h1, double_mod_hi n α₂ hα₂ h2,
      Nat.min_eq_right (by omega : n - α₁ ≤ α₁),
      Nat.min_eq_right (by omega : n - α₂ ≤ α₂)] at hstrict hs1_eq hs1i_eq ⊢
    simp only [Nat.min_def] at hs1_eq hs1i_eq ⊢
    split_ifs at hs1_eq <;> (try omega); split_ifs at hs1i_eq <;> omega

/-- In the strict diamond, if S₁ is closer then the other 3 neighbors are strictly farther.
    Mirrors `strict_diamond_closer_S2_all_farther` with S₁/S₂ roles swapped. -/
theorem strict_diamond_closer_S1_all_farther (n α₁ α₂ : ℕ) (hn : 3 ≤ n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n)
    (hstrict : 2 * (zmodDist n α₁ + zmodDist n α₂) + 1 ≤ n)
    (hs1 : zmodDist n (shearS1 n α₁ α₂).1 < zmodDist n α₁) :
    zmodDist n α₁ < zmodDist n (shearS1Inv n α₁ α₂).1 ∧
    zmodDist n α₂ < zmodDist n (shearS2 n α₁ α₂).2 ∧
    zmodDist n α₂ < zmodDist n (shearS2Inv n α₁ α₂).2 := by
  rw [zd_S1 n α₁ α₂ hα₁ hα₂ (by omega)] at hs1
  rw [zd_S1I n α₁ α₂ hα₁ hα₂ (by omega),
      zd_S2 n α₁ α₂ hα₁ hα₂ (by omega),
      zd_S2I n α₁ α₂ hα₁ hα₂ (by omega)]
  unfold zmodDist at hstrict hs1 ⊢
  by_cases h1 : 2 * α₁ < n <;> by_cases h2 : 2 * α₂ < n
  · simp only [double_mod_lo n α₁ h1, double_mod_lo n α₂ h2,
      Nat.min_eq_left (by omega : α₁ ≤ n - α₁),
      Nat.min_eq_left (by omega : α₂ ≤ n - α₂)] at hstrict hs1 ⊢
    simp only [Nat.min_def] at hs1 ⊢; split_ifs at hs1 <;> (refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega)
  · simp only [double_mod_lo n α₁ h1, double_mod_hi n α₂ hα₂ h2,
      Nat.min_eq_left (by omega : α₁ ≤ n - α₁),
      Nat.min_eq_right (by omega : n - α₂ ≤ α₂)] at hstrict hs1 ⊢
    simp only [Nat.min_def] at hs1 ⊢; split_ifs at hs1 <;> (refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega)
  · simp only [double_mod_hi n α₁ hα₁ h1, double_mod_lo n α₂ h2,
      Nat.min_eq_right (by omega : n - α₁ ≤ α₁),
      Nat.min_eq_left (by omega : α₂ ≤ n - α₂)] at hstrict hs1 ⊢
    simp only [Nat.min_def] at hs1 ⊢; split_ifs at hs1 <;> (refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega)
  · simp only [double_mod_hi n α₁ hα₁ h1, double_mod_hi n α₂ hα₂ h2,
      Nat.min_eq_right (by omega : n - α₁ ≤ α₁),
      Nat.min_eq_right (by omega : n - α₂ ≤ α₂)] at hstrict hs1 ⊢
    simp only [Nat.min_def] at hs1 ⊢; split_ifs at hs1 <;> (refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega)

/-- Symmetric: if S₁⁻¹ closer in strict diamond, all other 3 are farther. -/
theorem strict_diamond_closer_S1Inv_all_farther (n α₁ α₂ : ℕ) (hn : 3 ≤ n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n)
    (hstrict : 2 * (zmodDist n α₁ + zmodDist n α₂) + 1 ≤ n)
    (hs1i : zmodDist n (shearS1Inv n α₁ α₂).1 < zmodDist n α₁) :
    zmodDist n α₁ < zmodDist n (shearS1 n α₁ α₂).1 ∧
    zmodDist n α₂ < zmodDist n (shearS2 n α₁ α₂).2 ∧
    zmodDist n α₂ < zmodDist n (shearS2Inv n α₁ α₂).2 := by
  rw [zd_S1I n α₁ α₂ hα₁ hα₂ (by omega)] at hs1i
  rw [zd_S1 n α₁ α₂ hα₁ hα₂ (by omega),
      zd_S2 n α₁ α₂ hα₁ hα₂ (by omega),
      zd_S2I n α₁ α₂ hα₁ hα₂ (by omega)]
  unfold zmodDist at hstrict hs1i ⊢
  by_cases h1 : 2 * α₁ < n <;> by_cases h2 : 2 * α₂ < n
  · simp only [double_mod_lo n α₁ h1, double_mod_lo n α₂ h2,
      Nat.min_eq_left (by omega : α₁ ≤ n - α₁),
      Nat.min_eq_left (by omega : α₂ ≤ n - α₂)] at hstrict hs1i ⊢
    simp only [Nat.min_def] at hs1i ⊢; split_ifs at hs1i <;> (refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega)
  · simp only [double_mod_lo n α₁ h1, double_mod_hi n α₂ hα₂ h2,
      Nat.min_eq_left (by omega : α₁ ≤ n - α₁),
      Nat.min_eq_right (by omega : n - α₂ ≤ α₂)] at hstrict hs1i ⊢
    simp only [Nat.min_def] at hs1i ⊢; split_ifs at hs1i <;> (refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega)
  · simp only [double_mod_hi n α₁ hα₁ h1, double_mod_lo n α₂ h2,
      Nat.min_eq_right (by omega : n - α₁ ≤ α₁),
      Nat.min_eq_left (by omega : α₂ ≤ n - α₂)] at hstrict hs1i ⊢
    simp only [Nat.min_def] at hs1i ⊢; split_ifs at hs1i <;> (refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega)
  · simp only [double_mod_hi n α₁ hα₁ h1, double_mod_hi n α₂ hα₂ h2,
      Nat.min_eq_right (by omega : n - α₁ ≤ α₁),
      Nat.min_eq_right (by omega : n - α₂ ≤ α₂)] at hstrict hs1i ⊢
    simp only [Nat.min_def] at hs1i ⊢; split_ifs at hs1i <;> (refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega)

/-- When `2(d₁+d₂) < n`, the ψ pair sum is at most `5√2/2` inside the diamond.
    Verified for `n ≤ 200`. The tight case is CFFF (one closer, three farther):
    `√2 + 3·(√2/2) = 5√2/2`.

    Proof uses three structural facts about the strict diamond:
    1. If any neighbor is closer, all other 3 are farther (`*_all_farther`).
    2. If S₂ pair both E, S₁ pair both F (`S2_both_eq_implies_S1_farther`).
    3. Symmetric for S₁. -/
theorem strict_diamond_pair_sum_le (n α₁ α₂ : ℕ) (hn : 3 ≤ n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n) (hne : ¬(α₁ = 0 ∧ α₂ = 0))
    (hstrict : 2 * (zmodDist n α₁ + zmodDist n α₂) + 1 ≤ n) :
    (psiWeight n α₁ α₂ (shearS2 n α₁ α₂).1 (shearS2 n α₁ α₂).2 +
     psiWeight n α₁ α₂ (shearS2Inv n α₁ α₂).1 (shearS2Inv n α₁ α₂).2) +
    (psiWeight n α₁ α₂ (shearS1 n α₁ α₂).1 (shearS1 n α₁ α₂).2 +
     psiWeight n α₁ α₂ (shearS1Inv n α₁ α₂).1 (shearS1Inv n α₁ α₂).2) ≤ 5 * √2 / 2 := by
  -- Abbreviations
  set s2 := shearS2 n α₁ α₂; set s2i := shearS2Inv n α₁ α₂
  set s1 := shearS1 n α₁ α₂; set s1i := shearS1Inv n α₁ α₂
  -- Coordinate preservation
  have hs2_fst : s2.1 = α₁ := shearS2_fst n α₁ α₂
  have hs2i_fst : s2i.1 = α₁ := shearS2Inv_fst n α₁ α₂
  have hs1_snd : s1.2 = α₂ := shearS1_snd n α₁ α₂
  have hs1i_snd : s1i.2 = α₂ := shearS1Inv_snd n α₁ α₂
  -- zmodDistGt reductions
  have hgt_s2 : zmodDistGt n α₁ α₂ s2.1 s2.2 = decide (zmodDist n s2.2 < zmodDist n α₂) := by
    rw [hs2_fst]; exact zmodDistGt_of_fst_eq n α₁ α₂ s2.2
  have hgt_s2i : zmodDistGt n α₁ α₂ s2i.1 s2i.2 = decide (zmodDist n s2i.2 < zmodDist n α₂) := by
    rw [hs2i_fst]; exact zmodDistGt_of_fst_eq n α₁ α₂ s2i.2
  have hgt_s1 : zmodDistGt n α₁ α₂ s1.1 s1.2 = decide (zmodDist n s1.1 < zmodDist n α₁) := by
    rw [hs1_snd]; exact zmodDistGt_of_snd_eq n α₁ α₂ s1.1
  have hgt_s1i : zmodDistGt n α₁ α₂ s1i.1 s1i.2 = decide (zmodDist n s1i.1 < zmodDist n α₁) := by
    rw [hs1i_snd]; exact zmodDistGt_of_snd_eq n α₁ α₂ s1i.1
  -- Reverse zmodDistGt
  have hgt_s2_r : zmodDistGt n s2.1 s2.2 α₁ α₂ = decide (zmodDist n α₂ < zmodDist n s2.2) := by
    rw [hs2_fst]; exact zmodDistGt_of_fst_eq n α₁ s2.2 α₂
  have hgt_s2i_r : zmodDistGt n s2i.1 s2i.2 α₁ α₂ = decide (zmodDist n α₂ < zmodDist n s2i.2) := by
    rw [hs2i_fst]; exact zmodDistGt_of_fst_eq n α₁ s2i.2 α₂
  have hgt_s1_r : zmodDistGt n s1.1 s1.2 α₁ α₂ = decide (zmodDist n α₁ < zmodDist n s1.1) := by
    rw [hs1_snd]; exact zmodDistGt_of_snd_eq n s1.1 α₂ α₁
  have hgt_s1i_r : zmodDistGt n s1i.1 s1i.2 α₁ α₂ = decide (zmodDist n α₁ < zmodDist n s1i.1) := by
    rw [hs1i_snd]; exact zmodDistGt_of_snd_eq n s1i.1 α₂ α₁
  -- √2 facts
  have hsq : (√2 : ℝ) ^ 2 = 2 := sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hpos : (0:ℝ) < √2 := sqrt_pos.mpr (by norm_num)
  -- Case split: is any S₂ neighbor closer?
  by_cases h_s2_closer : zmodDist n s2.2 < zmodDist n α₂
  · -- S₂ closer: all other 3 are farther
    have h_all := strict_diamond_closer_S2_all_farther n α₁ α₂ hn hα₁ hα₂ hstrict h_s2_closer
    have h_s2i_f : zmodDist n α₂ < zmodDist n s2i.2 := h_all.1
    have h_s1_f : zmodDist n α₁ < zmodDist n s1.1 := h_all.2.1
    have h_s1i_f : zmodDist n α₁ < zmodDist n s1i.1 := h_all.2.2
    rw [psiWeight_eq_sqrt2_of_gt n α₁ α₂ s2.1 s2.2 (by rw [hgt_s2]; simp [h_s2_closer]),
        psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s2i.1 s2i.2
          (by rw [hgt_s2i]; simp [not_lt.mpr h_s2i_f.le])
          (by rw [hgt_s2i_r]; simp [h_s2i_f]),
        psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s1.1 s1.2
          (by rw [hgt_s1]; simp [not_lt.mpr h_s1_f.le])
          (by rw [hgt_s1_r]; simp [h_s1_f]),
        psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s1i.1 s1i.2
          (by rw [hgt_s1i]; simp [not_lt.mpr h_s1i_f.le])
          (by rw [hgt_s1i_r]; simp [h_s1i_f])]
    nlinarith [sq_nonneg (√2 - 1)]
  · by_cases h_s2i_closer : zmodDist n s2i.2 < zmodDist n α₂
    · -- S₂⁻¹ closer: all other 3 are farther
      have h_all := strict_diamond_closer_S2Inv_all_farther n α₁ α₂ hn hα₁ hα₂ hstrict h_s2i_closer
      have h_s2_f : zmodDist n α₂ < zmodDist n s2.2 := h_all.1
      have h_s1_f : zmodDist n α₁ < zmodDist n s1.1 := h_all.2.1
      have h_s1i_f : zmodDist n α₁ < zmodDist n s1i.1 := h_all.2.2
      rw [psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s2.1 s2.2
            (by rw [hgt_s2]; simp [not_lt.mpr h_s2_f.le])
            (by rw [hgt_s2_r]; simp [h_s2_f]),
          psiWeight_eq_sqrt2_of_gt n α₁ α₂ s2i.1 s2i.2 (by rw [hgt_s2i]; simp [h_s2i_closer]),
          psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s1.1 s1.2
            (by rw [hgt_s1]; simp [not_lt.mpr h_s1_f.le])
            (by rw [hgt_s1_r]; simp [h_s1_f]),
          psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s1i.1 s1i.2
            (by rw [hgt_s1i]; simp [not_lt.mpr h_s1i_f.le])
            (by rw [hgt_s1i_r]; simp [h_s1i_f])]
      nlinarith [sq_nonneg (√2 - 1)]
    · -- No S₂ closer. Check S₁.
      by_cases h_s1_closer : zmodDist n s1.1 < zmodDist n α₁
      · -- S₁ closer: all other 3 are farther
        have h_all := strict_diamond_closer_S1_all_farther n α₁ α₂ hn hα₁ hα₂ hstrict h_s1_closer
        have h_s1i_f : zmodDist n α₁ < zmodDist n s1i.1 := h_all.1
        have h_s2_f : zmodDist n α₂ < zmodDist n s2.2 := h_all.2.1
        have h_s2i_f : zmodDist n α₂ < zmodDist n s2i.2 := h_all.2.2
        rw [psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s2.1 s2.2
              (by rw [hgt_s2]; simp [not_lt.mpr h_s2_f.le])
              (by rw [hgt_s2_r]; simp [h_s2_f]),
            psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s2i.1 s2i.2
              (by rw [hgt_s2i]; simp [not_lt.mpr h_s2i_f.le])
              (by rw [hgt_s2i_r]; simp [h_s2i_f]),
            psiWeight_eq_sqrt2_of_gt n α₁ α₂ s1.1 s1.2 (by rw [hgt_s1]; simp [h_s1_closer]),
            psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s1i.1 s1i.2
              (by rw [hgt_s1i]; simp [not_lt.mpr h_s1i_f.le])
              (by rw [hgt_s1i_r]; simp [h_s1i_f])]
        nlinarith [sq_nonneg (√2 - 1)]
      · by_cases h_s1i_closer : zmodDist n s1i.1 < zmodDist n α₁
        · -- S₁⁻¹ closer: all other 3 are farther
          have h_all := strict_diamond_closer_S1Inv_all_farther n α₁ α₂ hn hα₁ hα₂ hstrict h_s1i_closer
          have h_s1_f : zmodDist n α₁ < zmodDist n s1.1 := h_all.1
          have h_s2_f : zmodDist n α₂ < zmodDist n s2.2 := h_all.2.1
          have h_s2i_f : zmodDist n α₂ < zmodDist n s2i.2 := h_all.2.2
          rw [psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s2.1 s2.2
                (by rw [hgt_s2]; simp [not_lt.mpr h_s2_f.le])
                (by rw [hgt_s2_r]; simp [h_s2_f]),
              psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s2i.1 s2i.2
                (by rw [hgt_s2i]; simp [not_lt.mpr h_s2i_f.le])
                (by rw [hgt_s2i_r]; simp [h_s2i_f]),
              psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s1.1 s1.2
                (by rw [hgt_s1]; simp [not_lt.mpr h_s1_f.le])
                (by rw [hgt_s1_r]; simp [h_s1_f]),
              psiWeight_eq_sqrt2_of_gt n α₁ α₂ s1i.1 s1i.2 (by rw [hgt_s1i]; simp [h_s1i_closer])]
          nlinarith [sq_nonneg (√2 - 1)]
        · -- No closer at all. Each ψ ≤ 1.
          by_cases h_s2_eq : zmodDist n s2.2 = zmodDist n α₂ ∧ zmodDist n s2i.2 = zmodDist n α₂
          · -- S₂ pair both E → S₁ pair both F
            obtain ⟨hs2e, hs2ie⟩ := h_s2_eq
            have h_all := strict_diamond_S2_both_eq_implies_S1_farther
              n α₁ α₂ hn hα₁ hα₂ hne hstrict hs2e hs2ie
            have h_s1_f : zmodDist n α₁ < zmodDist n s1.1 := h_all.1
            have h_s1i_f : zmodDist n α₁ < zmodDist n s1i.1 := h_all.2
            have hψ_s2 : psiWeight n α₁ α₂ s2.1 s2.2 = 1 := by
              have h1 : zmodDistGt n α₁ α₂ s2.1 s2.2 = false := by
                rw [hgt_s2]; exact decide_eq_false (not_lt.mpr (le_of_eq hs2e.symm))
              have h2 : zmodDistGt n s2.1 s2.2 α₁ α₂ = false := by
                rw [hgt_s2_r]; exact decide_eq_false (not_lt.mpr (le_of_eq hs2e))
              simp only [psiWeight, h1, h2, Bool.false_eq_true, ↓reduceIte]
            have hψ_s2i : psiWeight n α₁ α₂ s2i.1 s2i.2 = 1 := by
              have h1 : zmodDistGt n α₁ α₂ s2i.1 s2i.2 = false := by
                rw [hgt_s2i]; exact decide_eq_false (not_lt.mpr (le_of_eq hs2ie.symm))
              have h2 : zmodDistGt n s2i.1 s2i.2 α₁ α₂ = false := by
                rw [hgt_s2i_r]; exact decide_eq_false (not_lt.mpr (le_of_eq hs2ie))
              simp only [psiWeight, h1, h2, Bool.false_eq_true, ↓reduceIte]
            rw [hψ_s2, hψ_s2i,
                psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s1.1 s1.2
                  (by rw [hgt_s1]; simp [not_lt.mpr h_s1_f.le])
                  (by rw [hgt_s1_r]; simp [h_s1_f]),
                psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s1i.1 s1i.2
                  (by rw [hgt_s1i]; simp [not_lt.mpr h_s1i_f.le])
                  (by rw [hgt_s1i_r]; simp [h_s1i_f])]
            nlinarith [sq_nonneg (3 * √2 - 4)]
          · -- S₂ pair NOT both E → at least one S₂ is farther
            push_neg at h_s2_eq
            by_cases h_s1_eq : zmodDist n s1.1 = zmodDist n α₁ ∧ zmodDist n s1i.1 = zmodDist n α₁
            · -- S₁ pair both E → S₂ pair both F
              obtain ⟨hs1e, hs1ie⟩ := h_s1_eq
              have h_all := strict_diamond_S1_both_eq_implies_S2_farther
                n α₁ α₂ hn hα₁ hα₂ hne hstrict hs1e hs1ie
              have h_s2_f : zmodDist n α₂ < zmodDist n s2.2 := h_all.1
              have h_s2i_f : zmodDist n α₂ < zmodDist n s2i.2 := h_all.2
              have hψ_s1 : psiWeight n α₁ α₂ s1.1 s1.2 = 1 := by
                have h1 : zmodDistGt n α₁ α₂ s1.1 s1.2 = false := by
                  rw [hgt_s1]; exact decide_eq_false (not_lt.mpr (le_of_eq hs1e.symm))
                have h2 : zmodDistGt n s1.1 s1.2 α₁ α₂ = false := by
                  rw [hgt_s1_r]; exact decide_eq_false (not_lt.mpr (le_of_eq hs1e))
                simp only [psiWeight, h1, h2, Bool.false_eq_true, ↓reduceIte]
              have hψ_s1i : psiWeight n α₁ α₂ s1i.1 s1i.2 = 1 := by
                have h1 : zmodDistGt n α₁ α₂ s1i.1 s1i.2 = false := by
                  rw [hgt_s1i]; exact decide_eq_false (not_lt.mpr (le_of_eq hs1ie.symm))
                have h2 : zmodDistGt n s1i.1 s1i.2 α₁ α₂ = false := by
                  rw [hgt_s1i_r]; exact decide_eq_false (not_lt.mpr (le_of_eq hs1ie))
                simp only [psiWeight, h1, h2, Bool.false_eq_true, ↓reduceIte]
              rw [hψ_s1, hψ_s1i,
                  psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s2.1 s2.2
                    (by rw [hgt_s2]; simp [not_lt.mpr h_s2_f.le])
                    (by rw [hgt_s2_r]; simp [h_s2_f]),
                  psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s2i.1 s2i.2
                    (by rw [hgt_s2i]; simp [not_lt.mpr h_s2i_f.le])
                    (by rw [hgt_s2i_r]; simp [h_s2i_f])]
              nlinarith [sq_nonneg (3 * √2 - 4)]
            · -- Neither pair both E. Each pair has at most 1 E (so at least 1 F).
              push_neg at h_s1_eq
              -- S₂ pair: not both E, no closer → at least one F. pair ≤ 1 + √2/2.
              have hp1 : psiWeight n α₁ α₂ s2.1 s2.2 + psiWeight n α₁ α₂ s2i.1 s2i.2
                  ≤ 1 + √2 / 2 := by
                have hle1 := psiWeight_le_one_of_not_gt n α₁ α₂ s2.1 s2.2
                  (by rw [hgt_s2]; exact decide_eq_false h_s2_closer)
                have hle2 := psiWeight_le_one_of_not_gt n α₁ α₂ s2i.1 s2i.2
                  (by rw [hgt_s2i]; exact decide_eq_false h_s2i_closer)
                -- Case split: is s2 equal (E) or farther (F)?
                rcases eq_or_lt_of_le (Nat.le_of_not_lt h_s2_closer) with hs2_eq | hs2_lt
                · -- s2 is E → by h_s2_eq, s2i is not E → s2i is F
                  have h_s2i_ne := h_s2_eq hs2_eq.symm
                  have h_s2i_f : zmodDist n α₂ < zmodDist n s2i.2 :=
                    lt_of_le_of_ne (Nat.le_of_not_lt h_s2i_closer) (Ne.symm h_s2i_ne)
                  rw [psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s2i.1 s2i.2
                    (by rw [hgt_s2i]; simp [not_lt.mpr h_s2i_f.le])
                    (by rw [hgt_s2i_r]; simp [h_s2i_f])]
                  linarith
                · -- s2 is F
                  rw [psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s2.1 s2.2
                    (by rw [hgt_s2]; simp [not_lt.mpr hs2_lt.le])
                    (by rw [hgt_s2_r]; simp [hs2_lt])]
                  linarith
              -- S₁ pair: similarly, ≤ 1 + √2/2.
              have hp2 : psiWeight n α₁ α₂ s1.1 s1.2 + psiWeight n α₁ α₂ s1i.1 s1i.2
                  ≤ 1 + √2 / 2 := by
                have hle1 := psiWeight_le_one_of_not_gt n α₁ α₂ s1.1 s1.2
                  (by rw [hgt_s1]; exact decide_eq_false h_s1_closer)
                have hle2 := psiWeight_le_one_of_not_gt n α₁ α₂ s1i.1 s1i.2
                  (by rw [hgt_s1i]; exact decide_eq_false h_s1i_closer)
                -- Case split: is s1 equal (E) or farther (F)?
                rcases eq_or_lt_of_le (Nat.le_of_not_lt h_s1_closer) with hs1_eq | hs1_lt
                · -- s1 is E → by h_s1_eq, s1i is not E → s1i is F
                  have h_s1i_ne := h_s1_eq hs1_eq.symm
                  have h_s1i_f : zmodDist n α₁ < zmodDist n s1i.1 :=
                    lt_of_le_of_ne (Nat.le_of_not_lt h_s1i_closer) (Ne.symm h_s1i_ne)
                  rw [psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s1i.1 s1i.2
                    (by rw [hgt_s1i]; simp [not_lt.mpr h_s1i_f.le])
                    (by rw [hgt_s1i_r]; simp [h_s1i_f])]
                  linarith
                · -- s1 is F
                  rw [psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s1.1 s1.2
                    (by rw [hgt_s1]; simp [not_lt.mpr hs1_lt.le])
                    (by rw [hgt_s1_r]; simp [hs1_lt])]
                  linarith
              calc (psiWeight n α₁ α₂ s2.1 s2.2 + psiWeight n α₁ α₂ s2i.1 s2i.2) +
                  (psiWeight n α₁ α₂ s1.1 s1.2 + psiWeight n α₁ α₂ s1i.1 s1i.2)
                  ≤ (1 + √2 / 2) + (1 + √2 / 2) := add_le_add hp1 hp2
                _ = 2 + √2 := by ring
                _ ≤ 5 * √2 / 2 := by nlinarith [sq_nonneg (3 * √2 - 4)]

/-- When `2(d₁+d₂) = n` (even `n`, `d₁+d₂ = n/2` exactly): `cos²(πd₁/n) + cos²(πd₂/n) = 1`.
    Follows from `d₂ = n/2 - d₁`, giving `cos(πd₂/n) = sin(πd₁/n)`. -/
theorem cos_sq_sum_eq_one_of_double_eq (n α₁ α₂ : ℕ) (hn : 0 < n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n)
    (hdb : 2 * (zmodDist n α₁ + zmodDist n α₂) = n) :
    |cos (↑π * ↑α₁ / ↑n)| ^ 2 + |cos (↑π * ↑α₂ / ↑n)| ^ 2 = 1 := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [abs_cos_eq_cos_zmodDist n α₁ hα₁ hn, abs_cos_eq_cos_zmodDist n α₂ hα₂ hn]
  set d₁ := zmodDist n α₁
  set d₂ := zmodDist n α₂
  -- d₂ = n/2 - d₁, so πd₂/n = π/2 - πd₁/n
  have hd₂_eq : (d₂ : ℝ) = n / 2 - d₁ := by
    have : (2 : ℝ) * (↑d₁ + ↑d₂) = ↑n := by exact_mod_cast hdb
    linarith
  rw [show π * (d₂ : ℝ) / n = π / 2 - π * d₁ / n from by
    rw [hd₂_eq]; field_simp]
  rw [cos_pi_div_two_sub, add_comm]
  exact sin_sq_add_cos_sq _

/-- Inside the diamond, when pair sums exceed `5√2/2`, the cosine squared sum is at most 1.
    Proof: excess contradicts `strict_diamond_pair_sum_le`, so `2(d₁+d₂) = n`,
    and then `cos_sq_sum_eq_one_of_double_eq` gives `cos² = 1 ≤ 1`. -/
theorem diamond_excess_cos_sq_le_one (n α₁ α₂ : ℕ) (hn : 3 ≤ n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n) (hne : ¬(α₁ = 0 ∧ α₂ = 0))
    (hdiam : zmodDist n α₁ + zmodDist n α₂ ≤ n / 2)
    (hexcess : 5 * √2 / 2 <
      (psiWeight n α₁ α₂ (shearS2 n α₁ α₂).1 (shearS2 n α₁ α₂).2 +
       psiWeight n α₁ α₂ (shearS2Inv n α₁ α₂).1 (shearS2Inv n α₁ α₂).2) +
      (psiWeight n α₁ α₂ (shearS1 n α₁ α₂).1 (shearS1 n α₁ α₂).2 +
       psiWeight n α₁ α₂ (shearS1Inv n α₁ α₂).1 (shearS1Inv n α₁ α₂).2)) :
    |cos (↑π * ↑α₁ / ↑n)| ^ 2 + |cos (↑π * ↑α₂ / ↑n)| ^ 2 ≤ 1 := by
  -- 2(d₁+d₂) ≥ n, since otherwise strict_diamond_pair_sum_le contradicts excess
  have h2d : ¬ (2 * (zmodDist n α₁ + zmodDist n α₂) + 1 ≤ n) := by
    intro hstrict
    have hle := strict_diamond_pair_sum_le n α₁ α₂ hn hα₁ hα₂ hne hstrict
    linarith
  -- 2(d₁+d₂) ≤ n from diamond: d₁+d₂ ≤ n/2 → 2(d₁+d₂) ≤ 2(n/2) ≤ n
  have h2d_le : 2 * (zmodDist n α₁ + zmodDist n α₂) ≤ n := by
    have hd₁ := zmodDist_le_half n α₁ hα₁
    have hd₂ := zmodDist_le_half n α₂ hα₂
    omega
  -- So 2(d₁+d₂) = n
  have h2d_eq : 2 * (zmodDist n α₁ + zmodDist n α₂) = n := by omega
  rw [cos_sq_sum_eq_one_of_double_eq n α₁ α₂ (by omega) hα₁ hα₂ h2d_eq]

/-- Inside the diamond, the pointwise condition (*) holds.
    Proof structure:
    1. No CC inside diamond (each pair ≤ `1+√2`).
    2. If pair_sum ≤ `5√2/2`: direct bound using `|cos| ≤ 1`.
    3. If pair_sum > `5√2/2`: Cauchy-Schwarz with `cos² ≤ 1` and
       `pair² ≤ 2(1+√2)² = 6+4√2 < 25/2`. -/
theorem diamond_psi_bound (n α₁ α₂ : ℕ) (hn : 3 ≤ n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n) (hne : ¬(α₁ = 0 ∧ α₂ = 0))
    (hdiam : zmodDist n α₁ + zmodDist n α₂ ≤ n / 2) :
    pointwiseCondition n α₁ α₂ := by
  unfold pointwiseCondition
  simp only
  set s1 := shearS1 n α₁ α₂
  set s1i := shearS1Inv n α₁ α₂
  set s2 := shearS2 n α₁ α₂
  set s2i := shearS2Inv n α₁ α₂
  set pair₁ := psiWeight n α₁ α₂ s2.1 s2.2 + psiWeight n α₁ α₂ s2i.1 s2i.2
  set pair₂ := psiWeight n α₁ α₂ s1.1 s1.2 + psiWeight n α₁ α₂ s1i.1 s1i.2
  set c₁ := |cos (↑π * ↑α₁ / ↑n)|
  set c₂ := |cos (↑π * ↑α₂ / ↑n)|
  have hc₁_le : c₁ ≤ 1 := abs_cos_le_one _
  have hc₂_le : c₂ ≤ 1 := abs_cos_le_one _
  have hc₁ : 0 ≤ c₁ := abs_nonneg _
  have hc₂ : 0 ≤ c₂ := abs_nonneg _
  have hp₁ : 0 ≤ pair₁ := add_nonneg (psiWeight_pos n α₁ α₂ s2.1 s2.2).le
    (psiWeight_pos n α₁ α₂ s2i.1 s2i.2).le
  have hp₂ : 0 ≤ pair₂ := add_nonneg (psiWeight_pos n α₁ α₂ s1.1 s1.2).le
    (psiWeight_pos n α₁ α₂ s1i.1 s1i.2).le
  -- √2 facts
  have hsq2 : (√2 : ℝ) ^ 2 = 2 := sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hpos : (0:ℝ) < √2 := sqrt_pos.mpr (by norm_num)
  -- S₂ preserves first coordinate, S₁ preserves second
  have hs1_snd : s1.2 = α₂ := shearS1_snd n α₁ α₂
  have hs1i_snd : s1i.2 = α₂ := shearS1Inv_snd n α₁ α₂
  have hs2_fst : s2.1 = α₁ := shearS2_fst n α₁ α₂
  have hs2i_fst : s2i.1 = α₁ := shearS2Inv_fst n α₁ α₂
  -- Rewrite zmodDistGt using coordinate preservation
  have hgt_s2 : zmodDistGt n α₁ α₂ s2.1 s2.2 = decide (zmodDist n s2.2 < zmodDist n α₂) := by
    rw [hs2_fst]; exact zmodDistGt_of_fst_eq n α₁ α₂ s2.2
  have hgt_s2i : zmodDistGt n α₁ α₂ s2i.1 s2i.2 = decide (zmodDist n s2i.2 < zmodDist n α₂) := by
    rw [hs2i_fst]; exact zmodDistGt_of_fst_eq n α₁ α₂ s2i.2
  have hgt_s1 : zmodDistGt n α₁ α₂ s1.1 s1.2 = decide (zmodDist n s1.1 < zmodDist n α₁) := by
    rw [hs1_snd]; exact zmodDistGt_of_snd_eq n α₁ α₂ s1.1
  have hgt_s1i : zmodDistGt n α₁ α₂ s1i.1 s1i.2 = decide (zmodDist n s1i.1 < zmodDist n α₁) := by
    rw [hs1i_snd]; exact zmodDistGt_of_snd_eq n α₁ α₂ s1i.1
  -- No CC inside diamond: at most one S₂ neighbor is closer
  have h_no_cc_s2 := diamond_no_both_S2_closer n α₁ α₂ hn hα₁ hα₂ hdiam
  have h_no_cc_s1 := diamond_no_both_S1_closer n α₁ α₂ hn hα₁ hα₂ hdiam
  -- Each pair ≤ 1 + √2 (at least one ψ ≤ 1 per pair, since no CC)
  have hpair₁_le : pair₁ ≤ 1 + √2 := by
    rcases not_and_or.mp h_no_cc_s2 with h | h
    · have := psiWeight_le_one_of_not_gt n α₁ α₂ s2.1 s2.2
        (by rw [hgt_s2]; exact decide_eq_false h)
      linarith [psiWeight_le_sqrt2 n α₁ α₂ s2i.1 s2i.2]
    · have := psiWeight_le_one_of_not_gt n α₁ α₂ s2i.1 s2i.2
        (by rw [hgt_s2i]; exact decide_eq_false h)
      linarith [psiWeight_le_sqrt2 n α₁ α₂ s2.1 s2.2]
  have hpair₂_le : pair₂ ≤ 1 + √2 := by
    rcases not_and_or.mp h_no_cc_s1 with h | h
    · have := psiWeight_le_one_of_not_gt n α₁ α₂ s1.1 s1.2
        (by rw [hgt_s1]; exact decide_eq_false h)
      linarith [psiWeight_le_sqrt2 n α₁ α₂ s1i.1 s1i.2]
    · have := psiWeight_le_one_of_not_gt n α₁ α₂ s1i.1 s1i.2
        (by rw [hgt_s1i]; exact decide_eq_false h)
      linarith [psiWeight_le_sqrt2 n α₁ α₂ s1.1 s1.2]
  -- Split on pair sum
  by_cases hsum : pair₁ + pair₂ ≤ 5 * √2 / 2
  · -- Direct bound: LHS ≤ 1·pair₁ + 1·pair₂ = pair_sum ≤ 5√2/2
    calc c₁ * pair₁ + c₂ * pair₂
        ≤ 1 * pair₁ + 1 * pair₂ := by nlinarith
      _ = pair₁ + pair₂ := by ring
      _ ≤ 5 * √2 / 2 := hsum
  · -- Cauchy-Schwarz case: pair_sum > 5√2/2
    push_neg at hsum
    -- cos² ≤ 1 for excess cases
    have hcos_sq : c₁ ^ 2 + c₂ ^ 2 ≤ 1 :=
      diamond_excess_cos_sq_le_one n α₁ α₂ hn hα₁ hα₂ hne hdiam (by linarith)
    -- pair₁² + pair₂² ≤ 2(1+√2)² = 6+4√2 < 25/2
    have hpair_sq : pair₁ ^ 2 + pair₂ ^ 2 ≤ 25 / 2 := by
      have h1 : pair₁ ^ 2 ≤ (1 + √2) ^ 2 := by nlinarith [sq_nonneg (pair₁ - (1 + √2))]
      have h2 : pair₂ ^ 2 ≤ (1 + √2) ^ 2 := by nlinarith [sq_nonneg (pair₂ - (1 + √2))]
      nlinarith [sq_nonneg (√2 * 8 - 13)]
    -- CS: c₁p₁ + c₂p₂ ≤ √(c²) · √(p²) ≤ √1 · √(25/2) = 5√2/2
    have hCS := cauchy_schwarz_two c₁ c₂ pair₁ pair₂ hc₁ hc₂ hp₁ hp₂
    have hn' : 0 < n := by omega
    have h25 : √(25 / 2 : ℝ) = 5 * √2 / 2 := by
      rw [show (25 : ℝ) / 2 = (5 * √2 / 2) ^ 2 from by nlinarith]
      exact sqrt_sq (by positivity)
    calc c₁ * pair₁ + c₂ * pair₂
        ≤ √(c₁ ^ 2 + c₂ ^ 2) * √(pair₁ ^ 2 + pair₂ ^ 2) := hCS
      _ ≤ √1 * √(25 / 2) := by
          apply mul_le_mul (Real.sqrt_le_sqrt hcos_sq) (Real.sqrt_le_sqrt hpair_sq)
            (sqrt_nonneg _) (sqrt_nonneg _)
      _ = 5 * √2 / 2 := by rw [sqrt_one, one_mul, h25]

/-- Outside the diamond, the pointwise condition (*) holds.
    Uses Cauchy-Schwarz on ℝ²: `cos₁·p₁ + cos₂·p₂ ≤ √(cos₁²+cos₂²)·√(p₁²+p₂²) ≤ 1·5√2/2`.
    Relies on `cos_sq_sum_le_one` (cos₁²+cos₂² ≤ 1) and `pair_sq_sum_le_outside` (p₁²+p₂² ≤ 25/2). -/
theorem outside_diamond_psi_bound (n α₁ α₂ : ℕ) (hn : 3 ≤ n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n)
    (hout : n / 2 < zmodDist n α₁ + zmodDist n α₂) :
    pointwiseCondition n α₁ α₂ := by
  unfold pointwiseCondition
  simp only
  -- Name the pair sums
  set s1 := shearS1 n α₁ α₂
  set s1i := shearS1Inv n α₁ α₂
  set s2 := shearS2 n α₁ α₂
  set s2i := shearS2Inv n α₁ α₂
  set pair₁ := psiWeight n α₁ α₂ s2.1 s2.2 + psiWeight n α₁ α₂ s2i.1 s2i.2
  set pair₂ := psiWeight n α₁ α₂ s1.1 s1.2 + psiWeight n α₁ α₂ s1i.1 s1i.2
  set c₁ := |cos (↑π * ↑α₁ / ↑n)|
  set c₂ := |cos (↑π * ↑α₂ / ↑n)|
  have hc₁ : 0 ≤ c₁ := abs_nonneg _
  have hc₂ : 0 ≤ c₂ := abs_nonneg _
  have hp₁ : 0 ≤ pair₁ := add_nonneg (psiWeight_pos n α₁ α₂ s2.1 s2.2).le
    (psiWeight_pos n α₁ α₂ s2i.1 s2i.2).le
  have hp₂ : 0 ≤ pair₂ := add_nonneg (psiWeight_pos n α₁ α₂ s1.1 s1.2).le
    (psiWeight_pos n α₁ α₂ s1i.1 s1i.2).le
  have hn' : 0 < n := by omega
  -- Cauchy-Schwarz: c₁·p₁ + c₂·p₂ ≤ √(c₁²+c₂²) · √(p₁²+p₂²)
  have hCS := cauchy_schwarz_two c₁ c₂ pair₁ pair₂ hc₁ hc₂ hp₁ hp₂
  have hcos_sq := cos_sq_sum_le_one n α₁ α₂ hn' hα₁ hα₂ hout
  have hpair_sq := pair_sq_sum_le_outside n α₁ α₂ hn hα₁ hα₂
  -- √(c²) ≤ √1 = 1 and √(p²) ≤ √(25/2) = 5√2/2
  have hsq2 : (0 : ℝ) < √2 := sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)
  have hsq2_sq : (√2 : ℝ) ^ 2 = 2 := sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  -- √(25/2) = 5/(√2) = 5√2/2
  have h25 : √(25 / 2 : ℝ) = 5 * √2 / 2 := by
    rw [show (25 : ℝ) / 2 = (5 * √2 / 2) ^ 2 from by nlinarith]
    exact sqrt_sq (by positivity)
  calc c₁ * pair₁ + c₂ * pair₂
      ≤ √(c₁ ^ 2 + c₂ ^ 2) * √(pair₁ ^ 2 + pair₂ ^ 2) := hCS
    _ ≤ √1 * √(25 / 2) := by
        apply mul_le_mul (Real.sqrt_le_sqrt hcos_sq) (Real.sqrt_le_sqrt hpair_sq)
          (sqrt_nonneg _) (sqrt_nonneg _)
    _ = 5 * √2 / 2 := by rw [sqrt_one, one_mul, h25]


/-! **Step 6b: Combined Pointwise Condition** -/

/-- The pointwise condition holds for all nonzero `α ∈ (Z/nZ)²`.
    Combines `diamond_psi_bound` (inside) and `outside_diamond_psi_bound` (outside). -/
theorem pointwiseCondition_forall (n α₁ α₂ : ℕ) (hn : 3 ≤ n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n) (hne : ¬(α₁ = 0 ∧ α₂ = 0)) :
    pointwiseCondition n α₁ α₂ := by
  by_cases hdiam : zmodDist n α₁ + zmodDist n α₂ ≤ n / 2
  · exact diamond_psi_bound n α₁ α₂ hn hα₁ hα₂ hne hdiam
  · exact outside_diamond_psi_bound n α₁ α₂ hn hα₁ hα₂ (by omega)


end


