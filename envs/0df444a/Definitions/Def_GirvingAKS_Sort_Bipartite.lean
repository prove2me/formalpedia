-- Prove2me | Definitions.Def_GirvingAKS_Sort_Bipartite
-- name    : GirvingAKS_Sort_Bipartite
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:30:22.414041+00:00
-- url     : https://prove2.me/theorems/e5b249d1-3d5c-409a-9a8e-0a0c1b054507
-- title:
--   AKS sorting networks (Seiferas port) — Bipartite Comparator Lemmas
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Sort/Bipartite.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Monotonicity and ordering lemmas for bipartite comparator networks: comparators whose top wire `c.i.val < m` and bottom wire `m ≤ c.j.val`.
--
--   Main results:
--
--   - `foldl_member_order`: after executing a bipartite list, each comparator's
--
--   wires satisfy `output[c.i] ≤ output[c.j]`
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Sort/Bipartite.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Sort_Defs

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Sort/Bipartite.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Bipartite Comparator Lemmas

  Monotonicity and ordering lemmas for bipartite comparator networks:
  comparators whose top wire `c.i.val < m` and bottom wire `m ≤ c.j.val`.

  Main results:
  • `foldl_member_order`: after executing a bipartite list, each comparator's
    wires satisfy `output[c.i] ≤ output[c.j]`
-/


section


open Finset BigOperators


/-! **Bipartite Comparator Monotonicity** -/

/-- Applying a bipartite comparator: top values can only decrease. -/
lemma bipartite_apply_top_le {n m : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n)
    (hcj : m ≤ c.j.val)
    (w : Fin n → α) (k : Fin n) (hk : k.val < m) :
    c.apply w k ≤ w k := by
  have hkj : k ≠ c.j := fun h => absurd (h ▸ hk) (by omega)
  by_cases hki : k = c.i
  · subst hki; unfold Comparator.apply; rw [if_pos rfl]; exact min_le_left _ _
  · unfold Comparator.apply; rw [if_neg hki, if_neg hkj]

/-- Applying a bipartite comparator: bottom values can only increase. -/
lemma bipartite_apply_bot_ge {n m : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n)
    (hci : c.i.val < m)
    (w : Fin n → α) (k : Fin n) (hk : m ≤ k.val) :
    w k ≤ c.apply w k := by
  have hki : k ≠ c.i := fun h => absurd (h ▸ hk) (by omega)
  by_cases hkj : k = c.j
  · subst hkj; unfold Comparator.apply; rw [if_neg hki, if_pos rfl]; exact le_max_right _ _
  · unfold Comparator.apply; rw [if_neg hki, if_neg hkj]

/-- A comparator establishes order between its two wires: output[i] ≤ output[j]. -/
lemma comparator_apply_order {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) (w : Fin n → α) :
    c.apply w c.i ≤ c.apply w c.j := by
  have hij : c.j ≠ c.i := c.h.ne'
  unfold Comparator.apply
  rw [if_pos rfl, if_neg hij, if_pos rfl]
  exact le_trans (min_le_left _ _) (le_max_left _ _)

/-- Executing a list of bipartite comparators preserves ordering between
    a top wire and a bottom wire. -/
lemma foldl_bipartite_preserves_le {n m : ℕ} {α : Type*} [LinearOrder α]
    (cs : List (Comparator n))
    (hcs : ∀ c ∈ cs, c.i.val < m ∧ m ≤ c.j.val)
    (w : Fin n → α) (top bot : Fin n) (htop : top.val < m) (hbot : m ≤ bot.val)
    (h : w top ≤ w bot) :
    (cs.foldl (fun acc c ↦ c.apply acc) w) top ≤
    (cs.foldl (fun acc c ↦ c.apply acc) w) bot := by
  induction cs generalizing w with
  | nil => exact h
  | cons c rest ih =>
    simp only [List.foldl_cons]
    apply ih (fun c' hc' => hcs c' (.tail c hc'))
    have ⟨hci, hcj⟩ := hcs c (.head rest)
    exact le_trans (bipartite_apply_top_le c hcj w top htop)
      (le_trans h (bipartite_apply_bot_ge c hci w bot hbot))

/-- If a comparator c₀ is in a list of bipartite comparators, then after
    executing the list, output[c₀.i] ≤ output[c₀.j]. -/
lemma foldl_member_order {n m : ℕ} {α : Type*} [LinearOrder α]
    (cs : List (Comparator n))
    (c₀ : Comparator n) (hc₀ : c₀ ∈ cs)
    (hall : ∀ c' ∈ cs, c'.i.val < m ∧ m ≤ c'.j.val)
    (w : Fin n → α) :
    (cs.foldl (fun acc c ↦ c.apply acc) w) c₀.i ≤
    (cs.foldl (fun acc c ↦ c.apply acc) w) c₀.j := by
  induction cs generalizing w with
  | nil => nomatch hc₀
  | cons c rest ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hc₀ with rfl | h_rest
    · have ⟨hci, hcj⟩ := hall c₀ (.head rest)
      exact foldl_bipartite_preserves_le rest
        (fun c' hc' => hall c' (.tail c₀ hc'))
        (c₀.apply w) c₀.i c₀.j hci hcj (comparator_apply_order c₀ w)
    · exact ih h_rest
        (fun c' hc' => hall c' (.tail c hc'))
        (c.apply w)

end


