-- Prove2me | Definitions.Def_TwoChoicesSuffice_KOut_Coloring
-- name    : TwoChoicesSuffice_KOut_Coloring
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:35:56.446584+00:00
-- url     : https://prove2.me/theorems/03c2a8b0-49f9-46a4-aeca-d0d4e609ecfd
-- title:
--   Proper colourings $Z_q$ and directed cycles of the first-choice map
-- statement:
--   For a graph $J$ on $V$ and an integer $q\ge1$, a **proper $q$-colouring** is a map $c:V\to\{0,\dots,q-1\}$ with $c(u)\ne c(w)$ for every edge $uw$ of $J$, and $Z_q(J)$ is the number of proper $q$-colourings (labelled colours).
--
--   When every vertex has a neighbour, the first-choice graph $H^1_G(\sigma)$ is the undirected graph of the map $v\mapsto s_1(v)$. Its **directed cycles** are the periodic orbits $\{v,s_1(v),\dots,s_1^{\ell-1}(v)\}$ of this map, each counted once (up to rotation), with length $\ell$ the minimal period; two opposite arcs $v\to w\to v$ form a directed cycle of length two even though they give one undirected edge.
--
--   Every graph whose edges all have the form $\{u,f(u)\}$ for a map $f$ has a proper $10$-colouring, so the uniform proper colouring used in §7 is well defined.
--
--   **Formalization Note** `properColorings q J` is the finset of proper colourings (the elements of Mathlib's `J.Coloring (Fin q)` as functions), `numColorings q J` its cardinality. `directedCycles f` is the image of `cycleOf f` over the periodic points of `f`, so a cycle's length is its cardinality. The file proves `properColorings_prefixOne_nonempty`: $Z_{10}(H^1_G(\sigma))>0$ for every outcome.
-- source:
--   Yanyu Chen, Yu Chen, STOC 2027 submission #372 (October 2026), §7.3 (Z_q, eq. (7)) and Lemma 14, printed p. 18, PDF p. 19; PDF p. 19; Appendix A, PDF pp. 26–27

import Mathlib
import Definitions.Def_TwoChoicesSuffice_KOut_Sampling

open scoped Classical

namespace TwoChoicesSuffice.KOut

variable {V : Type*} [Fintype V]

/-- The proper vertex colourings `c : V → {0, …, q-1}` of `J` (labelled colours). This is
the finite set underlying Mathlib's `J.Coloring (Fin q)`. -/
noncomputable def properColorings (q : ℕ) (J : SimpleGraph V) : Finset (V → Fin q) :=
  Finset.univ.filter fun c => ∀ u w, J.Adj u w → c u ≠ c w

/-- `Z_q(J)`: the number of proper `q`-colourings of `J`. Source: §7.3, PDF p. 19. -/
noncomputable def numColorings (q : ℕ) (J : SimpleGraph V) : ℕ :=
  (properColorings q J).card

/-- The directed cycle of the map `f` through a periodic point `v`, as a vertex set: the
orbit `{v, f v, …, f^[p-1] v}` with `p` the minimal period. Its cardinality is the length
`ℓ` of the cycle; two opposite arcs `v → w → v` form a cycle of length two. -/
noncomputable def cycleOf (f : V → V) (v : V) : Finset V :=
  (Finset.range (Function.minimalPeriod f v)).image fun m => f^[m] v

/-- The directed cycles of the functional graph of `f : V → V`, each counted once (up to
cyclic rotation) as the vertex set of a periodic orbit. -/
noncomputable def directedCycles (f : V → V) : Finset (Finset V) :=
  (Finset.univ.filter fun v => v ∈ Function.periodicPts f).image (cycleOf f)

/-- Structural fact: a graph each of whose edges is `{u, f u}` for some map `f` (a
subgraph of a functional graph) has a proper 10-colouring. Proof: some vertex has at most
one `f`-preimage, hence at most two neighbours; colour greedily. -/
lemma exists_coloring_of_subFunctional (J : SimpleGraph V) (f : V → V)
    (hJ : ∀ u w, J.Adj u w → f u = w ∨ f w = u) :
    ∃ c : V → Fin 10, ∀ u w, J.Adj u w → c u ≠ c w := by
  suffices h : ∀ s : Finset V, ∃ c : V → Fin 10, ∀ u ∈ s, ∀ w ∈ s, J.Adj u w → c u ≠ c w by
    obtain ⟨c, hc⟩ := h Finset.univ
    exact ⟨c, fun u w h => hc u (Finset.mem_univ _) w (Finset.mem_univ _) h⟩
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨fun _ => 0, by simp⟩
    have hsum : ∑ v ∈ s, (s.filter (fun u => f u = v)).card ≤ ∑ _v ∈ s, 1 := by
      rw [← Finset.card_eq_sum_ones]
      calc ∑ v ∈ s, (s.filter (fun u => f u = v)).card
          = ∑ b ∈ s, ((s.filter (fun u => f u ∈ s)).filter (fun u => f u = b)).card := by
            refine Finset.sum_congr rfl fun b hb => ?_
            congr 1
            ext u
            simp only [Finset.mem_filter]
            constructor
            · rintro ⟨hu, hub⟩; exact ⟨⟨hu, hub ▸ hb⟩, hub⟩
            · rintro ⟨⟨hu, _⟩, hub⟩; exact ⟨hu, hub⟩
        _ = (s.filter (fun u => f u ∈ s)).card :=
            (Finset.card_eq_sum_card_fiberwise (f := f) (t := s)
              (fun x hx => (Finset.mem_filter.1 hx).2)).symm
        _ ≤ s.card := Finset.card_filter_le _ _
    obtain ⟨v, hv, hvle⟩ := Finset.exists_le_of_sum_le hs hsum
    obtain ⟨c, hc⟩ := ih (s.erase v) (Finset.erase_ssubset hv)
    have hF : (insert (c (f v)) ((s.filter (fun u => f u = v)).image c)).card < 10 := by
      calc (insert (c (f v)) ((s.filter (fun u => f u = v)).image c)).card
          ≤ ((s.filter (fun u => f u = v)).image c).card + 1 := Finset.card_insert_le _ _
        _ ≤ (s.filter (fun u => f u = v)).card + 1 := by
            gcongr; exact Finset.card_image_le
        _ ≤ 1 + 1 := by gcongr
        _ < 10 := by norm_num
    obtain ⟨x, hx⟩ : ∃ x, x ∉ insert (c (f v)) ((s.filter (fun u => f u = v)).image c) := by
      by_contra h
      push Not at h
      have h' : (Finset.univ : Finset (Fin 10)) ⊆
          insert (c (f v)) ((s.filter (fun u => f u = v)).image c) := fun x _ => h x
      have := Finset.card_le_card h'
      simp only [Finset.card_univ, Fintype.card_fin] at this
      omega
    refine ⟨Function.update c v x, ?_⟩
    intro u hu w hw huw
    by_cases huv : u = v
    · subst huv
      have hwu : w ≠ u := (J.ne_of_adj huw).symm
      rw [Function.update_self, Function.update_of_ne hwu]
      intro hxw
      rcases hJ _ _ huw with h | h
      · exact hx (by rw [hxw, ← h]; exact Finset.mem_insert_self _ _)
      · exact hx (Finset.mem_insert_of_mem
          (Finset.mem_image.2 ⟨w, Finset.mem_filter.2 ⟨hw, h⟩, hxw.symm⟩))
    · by_cases hwv : w = v
      · subst hwv
        rw [Function.update_self, Function.update_of_ne huv]
        intro hcx
        rcases hJ _ _ huw with h | h
        · exact hx (Finset.mem_insert_of_mem
            (Finset.mem_image.2 ⟨u, Finset.mem_filter.2 ⟨hu, h⟩, hcx⟩))
        · exact hx (by rw [← hcx, ← h]; exact Finset.mem_insert_self _ _)
      · rw [Function.update_of_ne huv, Function.update_of_ne hwv]
        exact hc u (Finset.mem_erase.2 ⟨huv, hu⟩) w (Finset.mem_erase.2 ⟨hwv, hw⟩) huw

/-- Every first-choice graph `H^1_G(σ)` has a proper 10-colouring, so the uniform
colouring law of §7.2 is well defined (`Z_10(H^1_G(σ)) > 0`). -/
lemma properColorings_prefixOne_nonempty (G : SimpleGraph V) {k : ℕ} (σ : V → Fin k → V) :
    (properColorings 10 (prefixGraph G σ 1)).Nonempty := by
  by_cases hk : 0 < k
  · obtain ⟨c, hc⟩ := exists_coloring_of_subFunctional (prefixGraph G σ 1)
      (fun v => σ v ⟨0, hk⟩) (by
        rintro u w ⟨_, ⟨i, hi, h⟩ | ⟨i, hi, h⟩⟩
        · have : i = ⟨0, hk⟩ := Fin.ext (by simp only; omega)
          exact Or.inl (this ▸ h)
        · have : i = ⟨0, hk⟩ := Fin.ext (by simp only; omega)
          exact Or.inr (this ▸ h))
    exact ⟨c, Finset.mem_filter.2 ⟨Finset.mem_univ _, hc⟩⟩
  · refine ⟨fun _ => 0, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
    rintro u w ⟨_, ⟨i, _, _⟩ | ⟨i, _, _⟩⟩ <;> exact absurd i.pos hk

end TwoChoicesSuffice.KOut


