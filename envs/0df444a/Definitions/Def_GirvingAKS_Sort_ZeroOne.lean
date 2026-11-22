-- Prove2me | Definitions.Def_GirvingAKS_Sort_ZeroOne
-- name    : GirvingAKS_Sort_ZeroOne
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:30:48.326701+00:00
-- url     : https://prove2.me/theorems/f9cdf0da-045d-4b92-8edf-20677aad9d51
-- title:
--   AKS sorting networks (Seiferas port) — The 0-1 Principle
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Sort/ZeroOne.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** A comparator network sorts all inputs iff it sorts all Boolean (0-1) inputs. This is the key reduction that makes correctness proofs tractable.
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Sort/ZeroOne.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Sort_Monotone

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Sort/ZeroOne.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # The 0-1 Principle

  A comparator network sorts all inputs iff it sorts all Boolean (0-1) inputs.
  This is the key reduction that makes correctness proofs tractable.
-/


section


open Finset BigOperators


/-- The 0-1 Principle: A comparator network sorts all inputs iff it
    sorts all Boolean (0-1) inputs. This is the key reduction that
    makes correctness proofs tractable. -/
theorem zero_one_principle {n : ℕ} (net : ComparatorNetwork n) :
    (∀ (v : Fin n → Bool), Monotone (net.exec v)) →
    net.Sorts := by
  intro h_bool
  unfold ComparatorNetwork.Sorts
  intro α _ v
  -- By contradiction: if net.exec v isn't sorted, construct a
  -- Boolean witness via a threshold function.
  by_contra h_not_mono
  simp only [Monotone, not_forall, not_le] at h_not_mono
  obtain ⟨i, j, hij, hlt⟩ := h_not_mono
  -- hlt : (net.exec v) j < (net.exec v) i, with hij : i ≤ j
  -- Threshold function: true iff strictly above (net.exec v) j
  let f : α → Bool := fun x ↦ decide ((net.exec v) j < x)
  have hf : Monotone f := by
    intro a b hab
    show decide ((net.exec v) j < a) ≤ decide ((net.exec v) j < b)
    by_cases ha : (net.exec v) j < a
    · have hb : (net.exec v) j < b := lt_of_lt_of_le ha hab
      simp [ha, hb]
    · simp [ha]
  -- By exec_comp_monotone: net.exec (f ∘ v) = f ∘ (net.exec v)
  have hcomm := (net.exec_comp_monotone (f := f) hf v).symm
  -- The Boolean input f ∘ v is not sorted by the network
  have h_sorted := (h_bool (f ∘ v)) hij
  rw [hcomm, show (f ∘ net.exec v) i = true from decide_eq_true_eq.mpr hlt,
      show (f ∘ net.exec v) j = false from decide_eq_false_iff_not.mpr (lt_irrefl _)] at h_sorted
  exact absurd h_sorted (by decide)

end


