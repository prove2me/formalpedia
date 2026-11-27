-- Prove2me | solution 1 for AlonMilman.PropertyT.Supplement.theorem_3_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:05:56.382682+00:00
-- url     : https://prove2.me/submissions/dc8901b3-e958-4295-8fcd-a513271e21ac

import Mathlib
import Definitions.Def_AlonMilman_PropertyT_Supplement_concentrationFun
import Definitions.Def_AlonMilman_PropertyT_Supplement_IsConcentrated
import Definitions.Def_AlonMilman_PropertyT_Supplement_oddGraph

open AlonMilman
open AlonMilman.PropertyT
open AlonMilman.PropertyT.Supplement

/-- Theorem 3.4 (Alon–Milman 1985, p. 81).
(i) For every choice of finite sets `S_k` with `|S_k| = 2k − 1` (`k ≥ 1`), the family of odd
graphs `{O_k}_{k ≥ 1}` on `S_k` is concentrated (`O_1` is the one-vertex graph).
(ii) If `{G_i}` is a concentrated family of finite simple graphs, each of them regular, then the
family `{L(G_i)}` of their line graphs is concentrated.
In particular the family `{L(O_k)}_{k ≥ 1}` is concentrated. -/
theorem solution :
    (∀ (S : ℕ+ → Type) [∀ k, Fintype (S k)] [∀ k, DecidableEq (S k)],
        (∀ k, Fintype.card (S k) = 2 * (k : ℕ) - 1) →
        IsConcentrated (fun k => {A : Finset (S k) // A.card = (k : ℕ) - 1})
          (fun k => oddGraph (S k) (k : ℕ))) ∧
    (∀ (V : ℕ → Type) [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
        (G : ∀ i, SimpleGraph (V i)) [∀ i, DecidableRel (G i).Adj],
        (∀ i, ∃ d : ℕ, (G i).IsRegularOfDegree d) → IsConcentrated V G →
        IsConcentrated (fun i => (G i).edgeSet) (fun i => (G i).lineGraph)) ∧
    (∀ (S : ℕ+ → Type) [∀ k, Fintype (S k)] [∀ k, DecidableEq (S k)],
        (∀ k, Fintype.card (S k) = 2 * (k : ℕ) - 1) →
        IsConcentrated (fun k => (oddGraph (S k) (k : ℕ)).edgeSet)
          (fun k => (oddGraph (S k) (k : ℕ)).lineGraph)) := by
            open SimpleGraph in
            · have hle1 : ∀ {W : Type} (H : SimpleGraph W) (x y : W), (x = y ∨ H.Adj x y) → H.edist x y ≤ 1 := by
                intro W H x y h
                rcases h with rfl | h
                · simp
                · exact (edist_eq_one_iff_adj.2 h).le
              have hedge : ∀ {V : Type} (G : SimpleGraph V) (e : G.edgeSet) (x y : V), x ∈ (e : Sym2 V) → y ∈ (e : Sym2 V) → G.edist x y ≤ 1 := by
                intro V G e x y hx hy
                obtain ⟨e, he⟩ := e
                induction e using Sym2.ind with
                | h u v =>
                  simp only [Sym2.mem_iff] at hx hy
                  have hadj : G.Adj u v := he
                  apply hle1
                  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
                  · exact Or.inl rfl
                  · exact Or.inr hadj
                  · exact Or.inr hadj.symm
                  · exact Or.inl rfl
              have hline1 : ∀ {V : Type} (G : SimpleGraph V) (b e : G.edgeSet) (a : V), a ∈ (b : Sym2 V) → a ∈ (e : Sym2 V) → G.lineGraph.edist b e ≤ 1 := by
                intro V G b e a hb he
                apply hle1
                by_cases h : b = e
                · exact Or.inl h
                · exact Or.inr (lineGraph_adj_iff_exists.2 ⟨h, a, hb, he⟩)
              -- lifting G-walks to line graph walks
              have W1 : ∀ {V : Type} (G : SimpleGraph V) (a x : V) (p : G.Walk a x) (b e : G.edgeSet),
                  a ∈ (b : Sym2 V) → x ∈ (e : Sym2 V) → G.lineGraph.edist b e ≤ p.length + 1 := by
                intro V G a x p
                induction p with
                | nil => intro b e hb he; simpa using hline1 G b e _ hb he
                | @cons a w x hadj p ih =>
                  intro b e hb he
                  let g : G.edgeSet := ⟨s(a, w), hadj⟩
                  have h1 : G.lineGraph.edist b g ≤ 1 := hline1 G b g a hb (by simp [g])
                  have h2 := ih g e (by simp [g]) he
                  calc G.lineGraph.edist b e ≤ G.lineGraph.edist b g + G.lineGraph.edist g e := SimpleGraph.edist_triangle
                    _ ≤ 1 + (p.length + 1) := add_le_add h1 h2
                    _ = ((Walk.cons hadj p).length : ℕ∞) + 1 := by simp; ring
              have W2 : ∀ {V : Type} (G : SimpleGraph V) (e f : G.edgeSet) (q : G.lineGraph.Walk e f) (x y : V),
                  x ∈ (e : Sym2 V) → y ∈ (f : Sym2 V) → G.edist x y ≤ q.length + 1 := by
                intro V G e f q
                induction q with
                | nil => intro x y hx hy; simpa using hedge G _ x y hx hy
                | @cons e g f hadj q ih =>
                  intro x y hx hy
                  obtain ⟨_, z, hz1, hz2⟩ := lineGraph_adj_iff_exists.1 hadj
                  have h1 : G.edist x z ≤ 1 := hedge G e x z hx hz1
                  have h2 := ih z y hz2 hy
                  calc G.edist x y ≤ G.edist x z + G.edist z y := SimpleGraph.edist_triangle
                    _ ≤ 1 + (q.length + 1) := add_le_add h1 h2
                    _ = ((Walk.cons hadj q).length : ℕ∞) + 1 := by simp; ring
              have M : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
                  (d : ℕ), G.IsRegularOfDegree d → 1 ≤ d → ∀ ρ : ℝ, 1 ≤ ρ → Fintype.card G.edgeSet ≠ 0 →
                  concentrationFun G.lineGraph ρ ≤ 2 * concentrationFun G (ρ - 1) := by
                intro V _ _ G _ d hreg hd ρ hρ hE
                have hV : Fintype.card V ≠ 0 := by
                  intro h0
                  apply hE
                  rw [Fintype.card_eq_zero_iff] at h0 ⊢
                  exact ⟨fun e => by
                    obtain ⟨e, he⟩ := e
                    induction e using Sym2.ind with
                    | h u v => exact h0.elim u⟩
                have hhs : 2 * Fintype.card G.edgeSet = d * Fintype.card V := by
                  rw [← edgeFinset_card, ← sum_degrees_eq_twice_card_edges]
                  simp [hreg.degree_eq, mul_comm]
                unfold concentrationFun
                rw [if_neg hE, if_neg hV]
                apply Finset.sup'_le
                intro B hB
                rw [Finset.mem_filter] at hB
                classical
                set A : Finset V := Finset.univ.filter (fun v => ∃ b ∈ B, v ∈ (b : Sym2 V)) with hAdef
                -- double counting
                have hBA : 2 * B.card ≤ d * A.card := by
                  have h1 := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
                    (fun (b : G.edgeSet) (v : V) => v ∈ (b : Sym2 V)) (s := B) (t := Finset.univ)
                  have h2 : ∀ b : G.edgeSet, (Finset.bipartiteAbove (fun (b : G.edgeSet) (v : V) => v ∈ (b : Sym2 V)) Finset.univ b).card = 2 := by
                    intro b
                    have : (Finset.bipartiteAbove (fun (b : G.edgeSet) (v : V) => v ∈ (b : Sym2 V)) Finset.univ b) = (b : Sym2 V).toFinset := by
                      ext v; simp [Finset.bipartiteAbove]
                    rw [this]
                    exact Sym2.card_toFinset_of_not_isDiag _ (G.not_isDiag_of_mem_edgeSet b.2)
                  simp only [h2, Finset.sum_const, smul_eq_mul] at h1
                  rw [mul_comm, h1]
                  calc ∑ v, (Finset.bipartiteBelow (fun (b : G.edgeSet) (v : V) => v ∈ (b : Sym2 V)) B v).card
                      = ∑ v ∈ A, (Finset.bipartiteBelow (fun (b : G.edgeSet) (v : V) => v ∈ (b : Sym2 V)) B v).card := by
                        symm
                        apply Finset.sum_subset (Finset.subset_univ _)
                        intro v _ hv
                        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
                        intro b hb
                        simp only [Finset.bipartiteBelow, Finset.mem_filter] at hb
                        exact hv (by rw [hAdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, b, hb.1, hb.2⟩)
                    _ ≤ ∑ v ∈ A, d := by
                        apply Finset.sum_le_sum
                        intro v _
                        rw [← hreg.degree_eq v, ← card_incidenceFinset_eq_degree]
                        rw [← Finset.card_map ⟨Subtype.val, Subtype.val_injective⟩]
                        apply Finset.card_le_card
                        intro e he
                        simp only [Finset.mem_map, Finset.bipartiteBelow, Finset.mem_filter] at he
                        obtain ⟨b, ⟨_, hb⟩, rfl⟩ := he
                        rw [mem_incidenceFinset]
                        exact ⟨b.2, hb⟩
                    _ = d * A.card := by simp [mul_comm]
                have hA : (Fintype.card V : ℝ) ≤ 2 * (A.card : ℝ) := by
                  have h1 : (2 * Fintype.card G.edgeSet : ℝ) = d * Fintype.card V := by exact_mod_cast hhs
                  have h2 : (2 * B.card : ℝ) ≤ d * A.card := by exact_mod_cast hBA
                  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
                  have h3 := hB.2
                  nlinarith
                set A' := enlargement G A (ρ - 1) with hA'def
                have claim1 : ∀ e : G.edgeSet, e ∉ enlargement G.lineGraph B ρ → ∀ x ∈ (e : Sym2 V), x ∉ A' := by
                  intro e he x hx hxA
                  apply he
                  simp only [hA'def, enlargement, Finset.mem_filter] at hxA
                  obtain ⟨_, a, ha, hreach, hdist⟩ := hxA
                  rw [hAdef, Finset.mem_filter] at ha
                  obtain ⟨_, b, hb, hab⟩ := ha
                  obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
                  have hw := W1 G a x p b e hab hx
                  have hr : G.lineGraph.Reachable b e := by
                    rw [← edist_ne_top_iff_reachable]
                    intro htop; rw [htop] at hw; simp at hw
                  simp only [enlargement, Finset.mem_filter]
                  refine ⟨Finset.mem_univ _, b, hb, hr, ?_⟩
                  have : G.lineGraph.dist b e ≤ p.length + 1 := by
                    have := hr.coe_dist_eq_edist
                    rw [← this] at hw
                    exact_mod_cast hw
                  have h2 : ((G.lineGraph.dist b e : ℕ) : ℝ) ≤ (p.length : ℝ) + 1 := by exact_mod_cast this
                  rw [hp] at h2
                  linarith
                set C : Finset V := Finset.univ \ A' with hCdef
                set E' : Finset G.edgeSet := Finset.univ \ enlargement G.lineGraph B ρ with hE'def
                have claim2 : E'.card ≤ d * C.card := by
                  calc E'.card = (E'.map ⟨Subtype.val, Subtype.val_injective⟩).card := (Finset.card_map _).symm
                    _ ≤ (C.biUnion (fun v => G.incidenceFinset v)).card := by
                      apply Finset.card_le_card
                      intro e he
                      simp only [Finset.mem_map, hE'def, Finset.mem_sdiff, Finset.mem_univ, true_and] at he
                      obtain ⟨e, he, rfl⟩ := he
                      obtain ⟨e', he'⟩ := e
                      induction e' using Sym2.ind with
                      | h u v =>
                        rw [Finset.mem_biUnion]
                        refine ⟨u, ?_, ?_⟩
                        · rw [hCdef, Finset.mem_sdiff]
                          exact ⟨Finset.mem_univ _, claim1 _ he u (Sym2.mem_mk_left u v)⟩
                        · rw [mem_incidenceFinset]
                          exact ⟨he', Sym2.mem_mk_left u v⟩
                    _ ≤ ∑ v ∈ C, (G.incidenceFinset v).card := Finset.card_biUnion_le
                    _ = d * C.card := by
                      simp [card_incidenceFinset_eq_degree, hreg.degree_eq, mul_comm]
                have hE'c : (E'.card : ℝ) = Fintype.card G.edgeSet - (enlargement G.lineGraph B ρ).card := by
                  rw [hE'def, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
                  rw [Nat.cast_sub (by rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _))]
                have hCc : (C.card : ℝ) = Fintype.card V - A'.card := by
                  rw [hCdef, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
                  rw [Nat.cast_sub (by rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _))]
                have hmem : A ∈ (Finset.univ : Finset (Finset V)).filter
                    (fun A => (Fintype.card V : ℝ) ≤ 2 * (A.card : ℝ)) := Finset.mem_filter.2 ⟨Finset.mem_univ _, hA⟩
                have hle := Finset.le_sup' (fun A => 1 - ((enlargement G A (ρ - 1)).card : ℝ) / (Fintype.card V : ℝ)) hmem
                refine le_trans ?_ (mul_le_mul_of_nonneg_left hle (by norm_num))
                have hEpos : (0 : ℝ) < Fintype.card G.edgeSet := by exact_mod_cast Nat.pos_of_ne_zero hE
                have hVpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast Nat.pos_of_ne_zero hV
                have h1 : (2 * Fintype.card G.edgeSet : ℝ) = d * Fintype.card V := by exact_mod_cast hhs
                have h2 : (E'.card : ℝ) ≤ d * C.card := by exact_mod_cast claim2
                rw [← hA'def]
                have e1 : 1 - ((enlargement G.lineGraph B ρ).card : ℝ) / Fintype.card G.edgeSet = E'.card / Fintype.card G.edgeSet := by
                  rw [hE'c, sub_div, div_self hEpos.ne']
                have e2 : 1 - (A'.card : ℝ) / Fintype.card V = C.card / Fintype.card V := by
                  rw [hCc, sub_div, div_self hVpos.ne']
                rw [e1, e2, div_le_iff₀ hEpos]
                have hd' : (0 : ℝ) < d := by exact_mod_cast hd
                calc (E'.card : ℝ) ≤ d * C.card := h2
                  _ = d * (C.card / Fintype.card V * Fintype.card V) := by rw [div_mul_cancel₀ _ hVpos.ne']
                  _ = C.card / Fintype.card V * (d * Fintype.card V) := by ring
                  _ = _ := by rw [← h1]; ring
              have F1 : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (ρ : ℝ), 0 ≤ ρ →
                  concentrationFun G ρ ≤ 1 / 2 := by
                intro V _ _ G ρ hρ
                unfold concentrationFun
                split_ifs with hV
                · norm_num
                apply Finset.sup'_le
                intro A hA
                rw [Finset.mem_filter] at hA
                have hsub : A ⊆ enlargement G A ρ := by
                  intro a ha
                  simp only [enlargement, Finset.mem_filter]
                  exact ⟨Finset.mem_univ _, a, ha, Reachable.refl a, by simp [hρ]⟩
                have h1 : (A.card : ℝ) ≤ (enlargement G A ρ).card := by exact_mod_cast Finset.card_le_card hsub
                have hVpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast Nat.pos_of_ne_zero hV
                rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hVpos]
                linarith [hA.2]
              have D : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
                  (∀ v, ∃ w, G.Adj v w) → G.lineGraph.diam ≠ 0 → 1 ≤ G.diam ∧ G.diam ≤ G.lineGraph.diam + 1 := by
                intro V _ _ G _ hadj hL
                have hLtop : G.lineGraph.ediam ≠ ⊤ := by
                  intro h; apply hL; simp [SimpleGraph.diam, h]
                have hle : G.ediam ≤ G.lineGraph.ediam + 1 := by
                  rw [ediam_le_iff]
                  intro u v
                  obtain ⟨u', hu⟩ := hadj u
                  obtain ⟨v', hv⟩ := hadj v
                  let e : G.edgeSet := ⟨s(u, u'), hu⟩
                  let f : G.edgeSet := ⟨s(v, v'), hv⟩
                  by_cases hr : G.lineGraph.Reachable e f
                  · obtain ⟨q, hq⟩ := hr.exists_walk_length_eq_dist
                    have := W2 G e f q u v (by simp [e]) (by simp [f])
                    rw [hq, hr.coe_dist_eq_edist] at this
                    exact this.trans (by gcongr; exact edist_le_ediam)
                  · exfalso; apply hLtop
                    have : G.lineGraph.edist e f = ⊤ := by
                      by_contra h; exact hr (edist_ne_top_iff_reachable.1 h)
                    rw [eq_top_iff, ← this]; exact edist_le_ediam
                have hGtop : G.ediam ≠ ⊤ := by
                  intro h; rw [h, top_le_iff] at hle
                  exact hLtop (by simpa using hle)
                constructor
                · by_cases hVne : Nonempty V
                  · obtain ⟨v⟩ := hVne
                    obtain ⟨w, hvw⟩ := hadj v
                    have h1 : (1 : ℕ∞) ≤ G.ediam := by
                      rw [← edist_eq_one_iff_adj.2 hvw]; exact edist_le_ediam
                    have := ENat.toNat_le_toNat h1 hGtop
                    simpa [SimpleGraph.diam] using this
                  · exfalso; apply hL
                    rw [not_nonempty_iff] at hVne
                    have : Subsingleton G.edgeSet := ⟨fun a _ => hVne.elim (Quot.out a.1).1⟩
                    have h0 : G.lineGraph.ediam = 0 := ediam_eq_zero_iff_subsingleton.2 this
                    simp [SimpleGraph.diam, h0]
                · have h2 : G.ediam ≤ ((G.lineGraph.diam + 1 : ℕ) : ℕ∞) := by
                    rw [Nat.cast_add, SimpleGraph.diam, ENat.coe_toNat hLtop]; simpa using hle
                  exact ENat.toNat_le_of_le_coe h2
              have hII : ∀ {ι : Type} (V : ι → Type) [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
                  (G : ∀ i, SimpleGraph (V i)) [∀ i, DecidableRel (G i).Adj],
                  (∀ i, ∃ d : ℕ, (G i).IsRegularOfDegree d) → IsConcentrated V G →
                  IsConcentrated (fun i => (G i).edgeSet) (fun i => (G i).lineGraph) := by
                intro ι V _ _ G _ hreg hconc
                obtain ⟨c, h, hc, hh, hb⟩ := hconc
                refine ⟨2 * c + 1, min (h / 4) (1 / 2), by linarith, lt_min (by linarith) (by norm_num), ?_⟩
                intro i ρ hρ
                obtain ⟨d, hd⟩ := hreg i
                have hc' : (0 : ℝ) < 2 * c + 1 := by linarith
                by_cases hE : Fintype.card (G i).edgeSet = 0
                · unfold concentrationFun
                  rw [if_pos hE]; positivity
                have hd1 : 1 ≤ d := by
                  rw [Fintype.card_eq_zero_iff, not_isEmpty_iff] at hE
                  obtain ⟨⟨e, he⟩⟩ := hE
                  revert he
                  induction e using Sym2.ind with
                  | h u v =>
                    intro he
                    have := ((G i).degree_pos_iff_exists_adj u).2 ⟨v, he⟩
                    rw [hd.degree_eq] at this; omega
                have hadj : ∀ v, ∃ w, (G i).Adj v w := by
                  intro v
                  apply ((G i).degree_pos_iff_exists_adj v).1
                  rw [hd.degree_eq]; omega
                have hF := F1 (G i).lineGraph ρ hρ.le
                by_cases hL : (G i).lineGraph.diam = 0
                · rw [hL]; simp; linarith
                have hLpos : (1 : ℝ) ≤ ((G i).lineGraph.diam : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hL
                have hsL : 1 ≤ Real.sqrt ((G i).lineGraph.diam : ℝ) := by
                  rw [Real.one_le_sqrt]; exact hLpos
                have hmin1 : min (h / 4) (1 / 2) ≤ h / 4 := min_le_left _ _
                have hmin2 : min (h / 4) (1 / 2) ≤ 1 / 2 := min_le_right _ _
                have hmin0 : 0 < min (h / 4) (1 / 2) := lt_min (by linarith) (by norm_num)
                by_cases hρ2 : ρ < 2
                · have hfl : ⌊min (h / 4) (1 / 2) * ρ / Real.sqrt ((G i).lineGraph.diam : ℝ)⌋₊ = 0 := by
                    rw [Nat.floor_eq_zero, div_lt_one (by linarith)]
                    nlinarith
                  rw [hfl]; simp; linarith
                push Not at hρ2
                obtain ⟨hG1, hGL⟩ := D (G i) hadj hL
                have hM := M (G i) d hd hd1 ρ (by linarith) hE
                have hbG := hb i (ρ - 1) (by linarith)
                have hGpos : (1 : ℝ) ≤ ((G i).diam : ℝ) := by exact_mod_cast hG1
                have hGL' : ((G i).diam : ℝ) ≤ (G i).lineGraph.diam + 1 := by exact_mod_cast hGL
                set s := Real.sqrt ((G i).diam : ℝ) with hs
                set t := Real.sqrt ((G i).lineGraph.diam : ℝ) with ht
                have hs1 : 1 ≤ s := by rw [hs, Real.one_le_sqrt]; exact hGpos
                have hs2 : s ^ 2 = (G i).diam := Real.sq_sqrt (by linarith)
                have ht2 : t ^ 2 = (G i).lineGraph.diam := Real.sq_sqrt (by linarith)
                have hst : s ≤ 2 * t := by
                  have h3 : s ^ 2 ≤ (2 * t) ^ 2 := by
                    rw [hs2, mul_pow, ht2]; linarith only [hGL', hLpos]
                  exact abs_le_of_sq_le_sq' h3 (by linarith only [hsL]) |>.2
                have hineq : min (h / 4) (1 / 2) * ρ / t ≤ h * (ρ - 1) / s := by
                  rw [div_le_div_iff₀ (by linarith) (by linarith)]
                  have : min (h / 4) (1 / 2) * ρ * s ≤ h / 4 * ρ * (2 * t) := by
                    apply mul_le_mul (mul_le_mul_of_nonneg_right hmin1 (by linarith)) hst (by linarith) (by positivity)
                  have h2 : h * t * (ρ / 2) ≤ h * t * (ρ - 1) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
                  linarith
                have hfl := Nat.floor_le_floor hineq
                have hexp : Real.exp (-(⌊h * (ρ - 1) / s⌋₊ : ℝ)) ≤ Real.exp (-(⌊min (h / 4) (1 / 2) * ρ / t⌋₊ : ℝ)) := by
                  apply Real.exp_le_exp.2
                  have : (⌊min (h / 4) (1 / 2) * ρ / t⌋₊ : ℝ) ≤ (⌊h * (ρ - 1) / s⌋₊ : ℝ) := by exact_mod_cast hfl
                  linarith
                have hpos := Real.exp_pos (-(⌊min (h / 4) (1 / 2) * ρ / t⌋₊ : ℝ))
                calc concentrationFun (G i).lineGraph ρ ≤ 2 * concentrationFun (G i) (ρ - 1) := hM
                  _ ≤ 2 * (c * Real.exp (-(⌊h * (ρ - 1) / s⌋₊ : ℝ))) := mul_le_mul_of_nonneg_left hbG zero_le_two
                  _ ≤ 2 * (c * Real.exp (-(⌊min (h / 4) (1 / 2) * ρ / t⌋₊ : ℝ))) :=
                    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hc.le) zero_le_two
                  _ ≤ (2 * c + 1) * Real.exp (-(⌊min (h / 4) (1 / 2) * ρ / t⌋₊ : ℝ)) := by
                    rw [add_mul, one_mul, mul_assoc]; exact le_add_of_nonneg_right hpos.le
              have REG : ∀ (S : Type) [Fintype S] [DecidableEq S] (k : ℕ), 1 ≤ k → Fintype.card S = 2 * k - 1 →
                  ∃ d : ℕ, (oddGraph S k).IsRegularOfDegree d := by
                intro S _ _ k hk hS
                rcases Nat.lt_or_ge k 2 with hk2 | hk2
                · refine ⟨0, fun A => ?_⟩
                  rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
                  intro B hB
                  rw [mem_neighborFinset] at hB
                  apply hB.1
                  apply Subtype.ext
                  have h0 : k - 1 = 0 := by omega
                  have hA : A.1.card = 0 := A.2.trans h0
                  have hB' : B.1.card = 0 := B.2.trans h0
                  rw [Finset.card_eq_zero.1 hA, Finset.card_eq_zero.1 hB']
                · refine ⟨k, fun A => ?_⟩
                  rw [← SimpleGraph.card_neighborFinset_eq_degree]
                  have hc : ((A.1)ᶜ.powersetCard (k - 1)).card = k := by
                    rw [Finset.card_powersetCard, Finset.card_compl, hS, A.2]
                    have : 2 * k - 1 - (k - 1) = k := by omega
                    rw [this, ← Nat.choose_symm (by omega : k - 1 ≤ k)]
                    have : k - (k - 1) = 1 := by omega
                    rw [this, Nat.choose_one_right]
                  refine Eq.trans ?_ hc
                  apply Finset.card_bij (fun B _ => B.1)
                  · intro B hB
                    rw [mem_neighborFinset] at hB
                    rw [Finset.mem_powersetCard]
                    exact ⟨fun x hx => Finset.mem_compl.2 (fun hxA => Finset.disjoint_left.1 hB.2 hxA hx), B.2⟩
                  · intro B _ C _ h; exact Subtype.ext h
                  · intro T hT
                    rw [Finset.mem_powersetCard] at hT
                    refine ⟨⟨T, hT.2⟩, ?_, rfl⟩
                    rw [mem_neighborFinset]
                    have hdisj : Disjoint A.1 T := by
                      rw [Finset.disjoint_right]; intro x hx; exact Finset.mem_compl.1 (hT.1 hx)
                    refine ⟨?_, hdisj⟩
                    intro hAT
                    have : A.1 = T := congrArg Subtype.val hAT
                    rw [this, disjoint_self, Finset.bot_eq_empty] at hdisj
                    have := hT.2; rw [hdisj] at this; simp at this; omega
              have TP : ∀ (p q a b t : ℝ), 0 ≤ p → 0 ≤ q → p + q = 1 → |a - b| ≤ 1 → |t| ≤ 1 →
                  p * Real.exp (t * a) + q * Real.exp (t * b) ≤ Real.exp (t * (p * a + q * b) + t ^ 2) := by
                intro p q a b t hp hq hpq hab ht
                have hq1 : q ≤ 1 := by linarith
                have hp1 : p ≤ 1 := by linarith
                have key : ∀ u : ℝ, |u| ≤ 1 → Real.exp u ≤ 1 + u + u ^ 2 := by
                  intro u hu
                  have := (abs_le.1 (Real.abs_exp_sub_one_sub_id_le hu)).2
                  linarith
                have h1 : |t * (q * (a - b))| ≤ |t| := by
                  rw [abs_mul, abs_mul, abs_of_nonneg hq]
                  have : q * |a - b| ≤ 1 := by nlinarith [abs_nonneg (a - b)]
                  nlinarith [abs_nonneg t]
                have h2 : |t * (-(p * (a - b)))| ≤ |t| := by
                  rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg hp]
                  have : p * |a - b| ≤ 1 := by nlinarith [abs_nonneg (a - b)]
                  nlinarith [abs_nonneg t]
                have e1 : t * a = t * (p * a + q * b) + t * (q * (a - b)) := by
                  have : p = 1 - q := by linarith
                  subst this; ring
                have e2 : t * b = t * (p * a + q * b) + t * (-(p * (a - b))) := by
                  have : q = 1 - p := by linarith
                  subst this; ring
                have k1 := key _ (h1.trans ht)
                have k2 := key _ (h2.trans ht)
                have s1 : (t * (q * (a - b))) ^ 2 ≤ t ^ 2 := sq_le_sq.2 h1
                have s2 : (t * (-(p * (a - b)))) ^ 2 ≤ t ^ 2 := sq_le_sq.2 h2
                have hfin : p * Real.exp (t * (q * (a - b))) + q * Real.exp (t * (-(p * (a - b)))) ≤ Real.exp (t ^ 2) := by
                  have h3 := Real.add_one_le_exp (t ^ 2)
                  have h4 : p * Real.exp (t * (q * (a - b))) ≤ p * (1 + t * (q * (a - b)) + t ^ 2) :=
                    mul_le_mul_of_nonneg_left (by linarith) hp
                  have h5 : q * Real.exp (t * (-(p * (a - b)))) ≤ q * (1 + t * (-(p * (a - b))) + t ^ 2) :=
                    mul_le_mul_of_nonneg_left (by linarith) hq
                  have h6 : p * (1 + t * (q * (a - b)) + t ^ 2) + q * (1 + t * (-(p * (a - b))) + t ^ 2) = (p + q) * (1 + t ^ 2) := by ring
                  rw [hpq] at h6
                  linarith
                rw [Real.exp_add, e1, e2, Real.exp_add, Real.exp_add]
                have := mul_le_mul_of_nonneg_left hfin (Real.exp_pos (t * (p * a + q * b))).le
                linarith
              -- double counting
              have DC : ∀ {α : Type} [DecidableEq α] (s : Finset α) (m : ℕ) (f : Finset α → ℝ),
                  ∑ A ∈ s.powersetCard m, ∑ y ∈ s \ A, f (insert y A) = (m + 1) * ∑ B ∈ s.powersetCard (m + 1), f B := by
                intro α _ s m f
                have h1 : (m + 1 : ℝ) * ∑ B ∈ s.powersetCard (m + 1), f B = ∑ B ∈ s.powersetCard (m + 1), ∑ y ∈ B, f B := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro B hB
                  rw [Finset.sum_const, (Finset.mem_powersetCard.1 hB).2]; simp
                rw [h1, Finset.sum_sigma', Finset.sum_sigma']
                apply Finset.sum_bij' (fun (x : (_ : Finset α) × α) _ => (⟨insert x.2 x.1, x.2⟩ : (_ : Finset α) × α))
                  (fun (x : (_ : Finset α) × α) _ => (⟨x.1.erase x.2, x.2⟩ : (_ : Finset α) × α))
                · rintro ⟨A, y⟩ h
                  simp only [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_sdiff] at h ⊢
                  refine ⟨⟨Finset.insert_subset h.2.1 h.1.1, ?_⟩, Finset.mem_insert_self _ _⟩
                  rw [Finset.card_insert_of_notMem h.2.2, h.1.2]
                · rintro ⟨B, y⟩ h
                  simp only [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_sdiff] at h ⊢
                  refine ⟨⟨(Finset.erase_subset _ _).trans h.1.1, ?_⟩, h.1.1 h.2, Finset.notMem_erase _ _⟩
                  rw [Finset.card_erase_of_mem h.2, h.1.2]; simp
                · rintro ⟨A, y⟩ h
                  simp only [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_sdiff] at h
                  simp [Finset.erase_insert h.2.2]
                · rintro ⟨B, y⟩ h
                  simp only [Finset.mem_sigma, Finset.mem_powersetCard] at h
                  simp [Finset.insert_erase h.2]
                · rintro ⟨A, y⟩ h
                  rfl
              have LAP : ∀ {α : Type} [DecidableEq α] (t : ℝ), |t| ≤ 1 → ∀ (s : Finset α) (m : ℕ) (f : Finset α → ℝ),
                  (∀ B x, f B - 1 ≤ f (insert x B) ∧ f (insert x B) ≤ f B) →
                  ∑ A ∈ s.powersetCard m, Real.exp (t * f A) ≤
                    ((s.powersetCard m).card : ℝ) * Real.exp (t * ((∑ A ∈ s.powersetCard m, f A) / ((s.powersetCard m).card : ℝ)) + s.card * t ^ 2) := by
                intro α _ t ht s
                induction s using Finset.induction_on with
                | empty =>
                  intro m f hf
                  rcases m with _ | m
                  · simp
                  · have h0 : (∅ : Finset α).powersetCard (m + 1) = ∅ := Finset.powersetCard_eq_empty.2 (by simp)
                    rw [h0]; simp
                | @insert x s hx ih =>
                  intro m f hf
                  rcases m with _ | m
                  · simp; positivity
                  have hsum : ∀ g : Finset α → ℝ, ∑ A ∈ (insert x s).powersetCard (m + 1), g A =
                      ∑ A ∈ s.powersetCard (m + 1), g A + ∑ A ∈ s.powersetCard m, g (insert x A) := by
                    intro g
                    rw [Finset.powersetCard_succ_insert hx, Finset.sum_union, Finset.sum_image]
                    · intro A hA B hB hAB
                      have hA' : x ∉ A := fun h => hx ((Finset.mem_powersetCard.1 hA).1 h)
                      have hB' : x ∉ B := fun h => hx ((Finset.mem_powersetCard.1 hB).1 h)
                      rw [← Finset.erase_insert hA', ← Finset.erase_insert hB']
                      exact congrArg (fun C => Finset.erase C x) hAB
                    · rw [Finset.disjoint_left]
                      intro A hA hA2
                      obtain ⟨B, _, rfl⟩ := Finset.mem_image.1 hA2
                      exact hx ((Finset.mem_powersetCard.1 hA).1 (Finset.mem_insert_self _ _))
                  have hcard : (((insert x s).powersetCard (m + 1)).card : ℝ) = ((s.powersetCard (m + 1)).card : ℝ) + ((s.powersetCard m).card : ℝ) := by
                    have := hsum (fun _ => 1)
                    simpa using this
                  have I0 := ih (m + 1) f hf
                  have I1 := ih m (fun A => f (insert x A)) (by
                    intro B y
                    have := hf (insert x B) y
                    rw [Finset.insert_comm]; exact this)
                  rw [hsum, hsum, hcard, Finset.card_insert_of_notMem hx]
                  have hN0 : ((s.powersetCard (m + 1)).card : ℝ) = (s.card.choose (m + 1) : ℕ) := by rw [Finset.card_powersetCard]
                  have hN1 : ((s.powersetCard m).card : ℝ) = (s.card.choose m : ℕ) := by rw [Finset.card_powersetCard]
                  set N0 : ℝ := ((s.powersetCard (m + 1)).card : ℝ) with hN0d
                  set N1 : ℝ := ((s.powersetCard m).card : ℝ) with hN1d
                  set F0 : ℝ := ∑ A ∈ s.powersetCard (m + 1), f A with hF0
                  set F1 : ℝ := ∑ A ∈ s.powersetCard m, f (insert x A) with hF1
                  have hn : (0 : ℝ) ≤ t ^ 2 := by positivity
                  push_cast
                  rcases Nat.lt_or_ge s.card m with hlt | hge
                  · have z0 : s.powersetCard (m + 1) = ∅ := Finset.powersetCard_eq_empty.2 (by omega)
                    have z1 : s.powersetCard m = ∅ := Finset.powersetCard_eq_empty.2 (by omega)
                    rw [hN0d, hN1d, z0, z1]; simp
                  have hN1pos : 0 < N1 := by
                    rw [hN1]; exact_mod_cast Nat.choose_pos hge
                  rcases Nat.lt_or_ge s.card (m + 1) with hlt | hge'
                  · have z0 : s.powersetCard (m + 1) = ∅ := Finset.powersetCard_eq_empty.2 (by omega)
                    have n0 : N0 = 0 := by rw [hN0d, z0]; simp
                    have f0 : F0 = 0 := by rw [hF0, z0]; simp
                    rw [n0, f0, z0]
                    simp only [Finset.sum_empty, zero_add]
                    refine I1.trans ?_
                    apply mul_le_mul_of_nonneg_left _ hN1pos.le
                    apply Real.exp_le_exp.2
                    linarith
                  have hN0pos : 0 < N0 := by
                    rw [hN0]; exact_mod_cast Nat.choose_pos hge'
                  have hnm : (0 : ℝ) < (s.card : ℝ) - m := by
                    have : ((m + 1 : ℕ) : ℝ) ≤ s.card := by exact_mod_cast hge'
                    push_cast at this; linarith
                  have hcs : ∀ A ∈ s.powersetCard m, ((s \ A).card : ℝ) = (s.card : ℝ) - m := by
                    intro A hA
                    rw [Finset.mem_powersetCard] at hA
                    rw [Finset.card_sdiff_of_subset hA.1, hA.2, Nat.cast_sub hge]
                  have hT : ((s.card : ℝ) - m) * N1 = (m + 1) * N0 := by
                    have := DC s m (fun _ => 1)
                    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at this
                    rw [← this, Finset.sum_congr rfl hcs]
                    simp [hN1d]; ring
                  have hdiff : ∑ A ∈ s.powersetCard m, ∑ y ∈ s \ A, (f (insert x A) - f (insert y A)) = ((s.card : ℝ) - m) * F1 - (m + 1) * F0 := by
                    simp only [Finset.sum_sub_distrib]
                    rw [DC s m f]
                    congr 1
                    rw [hF1, Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro A hA
                    rw [Finset.sum_const, nsmul_eq_mul, hcs A hA]
                  have hab : |F0 / N0 - F1 / N1| ≤ 1 := by
                    have hb : |((s.card : ℝ) - m) * F1 - (m + 1) * F0| ≤ ((s.card : ℝ) - m) * N1 := by
                      rw [← hdiff]
                      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
                      calc ∑ A ∈ s.powersetCard m, |∑ y ∈ s \ A, (f (insert x A) - f (insert y A))|
                          ≤ ∑ A ∈ s.powersetCard m, ((s.card : ℝ) - m) := by
                            apply Finset.sum_le_sum
                            intro A hA
                            refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
                            rw [← hcs A hA]
                            calc ∑ y ∈ s \ A, |f (insert x A) - f (insert y A)| ≤ ∑ y ∈ s \ A, (1 : ℝ) := by
                                  apply Finset.sum_le_sum
                                  intro y _
                                  have := hf A x
                                  have := hf A y
                                  rw [abs_le]; constructor <;> linarith
                              _ = _ := by simp
                        _ = _ := by simp [hN1d]; ring
                    have he : F0 / N0 - F1 / N1 = -((((s.card : ℝ) - m) * F1 - (m + 1) * F0) / (((s.card : ℝ) - m) * N1)) := by
                      have : F0 / N0 = (m + 1) * F0 / ((m + 1) * N0) := by
                        have : (m + 1 : ℝ) ≠ 0 := by positivity
                        field_simp
                      rw [this, ← hT]
                      field_simp
                      ring
                    rw [he, abs_neg, abs_div, abs_of_pos (mul_pos hnm hN1pos)]
                    exact div_le_one_of_le₀ hb (mul_pos hnm hN1pos).le
                  have hN : 0 < N0 + N1 := by linarith
                  have tp := TP (N0 / (N0 + N1)) (N1 / (N0 + N1)) (F0 / N0) (F1 / N1) t (div_nonneg hN0pos.le hN.le) (div_nonneg hN1pos.le hN.le) (by rw [← add_div]; exact div_self hN.ne') hab ht
                  have e3 : N0 / (N0 + N1) * (F0 / N0) + N1 / (N0 + N1) * (F1 / N1) = (F0 + F1) / (N0 + N1) := by
                    field_simp
                  rw [e3] at tp
                  have tp2 := mul_le_mul_of_nonneg_left tp (mul_pos hN (Real.exp_pos (s.card * t ^ 2))).le
                  calc _ ≤ N0 * Real.exp (t * (F0 / N0) + s.card * t ^ 2) + N1 * Real.exp (t * (F1 / N1) + s.card * t ^ 2) := add_le_add I0 I1
                    _ = (N0 + N1) * Real.exp (s.card * t ^ 2) * (N0 / (N0 + N1) * Real.exp (t * (F0 / N0)) + N1 / (N0 + N1) * Real.exp (t * (F1 / N1))) := by
                      rw [Real.exp_add, Real.exp_add]; field_simp
                    _ ≤ _ := tp2
                    _ = _ := by
                      rw [mul_assoc, ← Real.exp_add]; ring_nf
              have UP : ∀ (S : Type) [Fintype S] [DecidableEq S] (k : ℕ), 1 ≤ k → Fintype.card S = 2 * k - 1 →
                  ∀ (j : ℕ) (A B : {A : Finset S // A.card = k - 1}), (A.1 \ B.1).card = j →
                    (oddGraph S k).edist A B ≤ ((2 * j : ℕ) : ℕ∞) := by
                intro S _ _ k hk hS j
                induction j with
                | zero =>
                  intro A B h
                  rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at h
                  have : A = B := Subtype.ext (Finset.eq_of_subset_of_card_le h (by rw [A.2, B.2]))
                  subst this; simp
                | succ j ih =>
                  intro A B h
                  have hBA : (B.1 \ A.1).card = j + 1 := by
                    rw [← h]; exact Finset.card_sdiff_comm (B.2.trans A.2.symm)
                  obtain ⟨x, hx⟩ := Finset.card_pos.1 (by omega : 0 < (A.1 \ B.1).card)
                  obtain ⟨y, hy⟩ := Finset.card_pos.1 (by omega : 0 < (B.1 \ A.1).card)
                  rw [Finset.mem_sdiff] at hx hy
                  have hApos : 1 ≤ A.1.card := Finset.card_pos.2 ⟨x, hx.1⟩
                  have hk2 : 2 ≤ k := by have := A.2; omega
                  have hye : y ∉ A.1.erase x := fun h' => hy.2 (Finset.mem_of_mem_erase h')
                  have hA'c : (insert y (A.1.erase x)).card = k - 1 := by
                    rw [Finset.card_insert_of_notMem hye, Finset.card_erase_of_mem hx.1, A.2]; omega
                  have hCc : ((insert y A.1)ᶜ).card = k - 1 := by
                    rw [Finset.card_compl, Finset.card_insert_of_notMem hy.2, A.2, hS]; omega
                  have hne : ∀ (P Q : {A : Finset S // A.card = k - 1}), Disjoint P.1 Q.1 → P ≠ Q := by
                    intro P Q hd hPQ
                    rw [hPQ, disjoint_self, Finset.bot_eq_empty] at hd
                    have := Q.2; rw [hd] at this; simp at this; omega
                  have hd1 : Disjoint A.1 (insert y A.1)ᶜ := by
                    rw [Finset.disjoint_left]; intro z hz hz'
                    exact Finset.mem_compl.1 hz' (Finset.mem_insert_of_mem hz)
                  have hd2 : Disjoint (insert y A.1)ᶜ (insert y (A.1.erase x)) := by
                    rw [Finset.disjoint_right]; intro z hz hz'
                    exact Finset.mem_compl.1 hz' (Finset.insert_subset_insert _ (Finset.erase_subset _ _) hz)
                  let C : {A : Finset S // A.card = k - 1} := ⟨_, hCc⟩
                  let A' : {A : Finset S // A.card = k - 1} := ⟨_, hA'c⟩
                  have a1 : (oddGraph S k).Adj A C := ⟨hne A C hd1, hd1⟩
                  have a2 : (oddGraph S k).Adj C A' := ⟨hne C A' hd2, hd2⟩
                  have hj : (A'.1 \ B.1).card = j := by
                    have : A'.1 \ B.1 = (A.1 \ B.1).erase x := by
                      ext z
                      simp only [A', Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
                      constructor
                      · rintro ⟨rfl | h1, h2⟩
                        · exact absurd hy.1 h2
                        · exact ⟨h1.1, h1.2, h2⟩
                      · rintro ⟨h1, h2, h3⟩
                        exact ⟨Or.inr ⟨h1, h2⟩, h3⟩
                    rw [this, Finset.card_erase_of_mem (Finset.mem_sdiff.2 hx), h]; simp
                  have hih := ih A' B hj
                  calc (oddGraph S k).edist A B ≤ (oddGraph S k).edist A A' + (oddGraph S k).edist A' B := SimpleGraph.edist_triangle
                    _ ≤ ((oddGraph S k).edist A C + (oddGraph S k).edist C A') + (oddGraph S k).edist A' B := by
                      gcongr; exact SimpleGraph.edist_triangle
                    _ ≤ (1 + 1) + ((2 * j : ℕ) : ℕ∞) := by
                      rw [edist_eq_one_iff_adj.2 a1, edist_eq_one_iff_adj.2 a2]; gcongr
                    _ = ((2 * (j + 1) : ℕ) : ℕ∞) := by push_cast; ring
              have LOW : ∀ (S : Type) [Fintype S] [DecidableEq S] (k : ℕ), 1 ≤ k → Fintype.card S = 2 * k - 1 →
                  ∀ (A B : {A : Finset S // A.card = k - 1}) (p : (oddGraph S k).Walk A B),
                    ∀ (D : Finset S), ∀ r : ℕ, ((D \ A.1).card ≤ r ∨ (D ∩ A.1).card ≤ r) → 
                      ((D \ B.1).card ≤ r + p.length ∨ (D ∩ B.1).card ≤ r + p.length) := by
                intro S _ _ k hk hS A B p
                induction p with
                | nil => intro D r h; simpa using h
                | @cons A C B hadj p ih =>
                  intro D r h
                  have hstep : (D \ C.1).card ≤ r + 1 ∨ (D ∩ C.1).card ≤ r + 1 := by
                    have hd : Disjoint A.1 C.1 := hadj.2
                    rcases h with h | h
                    · right
                      have : (D ∩ C.1).card ≤ (D \ A.1).card := by
                        apply Finset.card_le_card
                        intro z hz
                        rw [Finset.mem_inter] at hz
                        exact Finset.mem_sdiff.2 ⟨hz.1, fun h' => Finset.disjoint_left.1 hd h' hz.2⟩
                      omega
                    · left
                      have h1 : ((A.1 ∪ C.1)ᶜ).card ≤ 1 := by
                        rw [Finset.card_compl, Finset.card_union_of_disjoint hd, A.2, C.2, hS]; omega
                      have : (D \ C.1) ⊆ (D ∩ A.1) ∪ (A.1 ∪ C.1)ᶜ := by
                        intro z hz
                        rw [Finset.mem_sdiff] at hz
                        by_cases hzA : z ∈ A.1
                        · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hz.1, hzA⟩)
                        · refine Finset.mem_union_right _ (Finset.mem_compl.2 fun h => ?_)
                          exact (Finset.mem_union.1 h).elim hzA hz.2
                      have h2 := (Finset.card_le_card this).trans (Finset.card_union_le _ _)
                      omega
                  have := ih D (r + 1) hstep
                  rw [Walk.length_cons]
                  have e : r + (p.length + 1) = r + 1 + p.length := by ring
                  rw [e]; exact this
              have ETOP : ∀ (S : Type) [Fintype S] [DecidableEq S] (k : ℕ), 1 ≤ k → Fintype.card S = 2 * k - 1 →
                  (oddGraph S k).ediam ≠ ⊤ := by
                intro S _ _ k hk hS htop
                have : (oddGraph S k).ediam ≤ ((2 * Fintype.card S : ℕ) : ℕ∞) := by
                  rw [ediam_le_iff]
                  intro A B
                  refine (UP S k hk hS _ A B rfl).trans ?_
                  exact_mod_cast Nat.mul_le_mul_left 2 (Finset.card_le_univ _)
                rw [htop, top_le_iff] at this
                exact ENat.coe_ne_top _ this
              have DIAM : ∀ (S : Type) [Fintype S] [DecidableEq S] (k : ℕ), 1 ≤ k → Fintype.card S = 2 * k - 1 →
                  (k - 1) / 2 ≤ (oddGraph S k).diam := by
                intro S _ _ k hk hS
                obtain ⟨A, -, hA⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset S)) (n := k - 1) (by rw [Finset.card_univ, hS]; omega)
                obtain ⟨A1, hA1, hA1c⟩ := Finset.exists_subset_card_eq (s := A) (n := (k - 1) - (k - 1) / 2) (by omega)
                obtain ⟨E, hE, hEc⟩ := Finset.exists_subset_card_eq (s := Aᶜ) (n := (k - 1) / 2) (by rw [Finset.card_compl, hS]; omega)
                have hdis : ∀ z ∈ E, z ∉ A := fun z hz => Finset.mem_compl.1 (hE hz)
                have hBc : (A1 ∪ E).card = k - 1 := by
                  rw [Finset.card_union_of_disjoint, hA1c, hEc]
                  · omega
                  · rw [Finset.disjoint_right]; intro z hz hz'; exact hdis z hz (hA1 hz')
                let A0 : {A : Finset S // A.card = k - 1} := ⟨A, hA⟩
                let B0 : {A : Finset S // A.card = k - 1} := ⟨A1 ∪ E, hBc⟩
                have hr : (oddGraph S k).Reachable A0 B0 := by
                  rw [← edist_ne_top_iff_reachable]
                  intro htop
                  have := UP S k hk hS _ A0 B0 rfl
                  rw [htop, top_le_iff] at this
                  exact ENat.coe_ne_top _ this
                obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
                have h0 := LOW S k hk hS A0 B0 p A 0 (Or.inl (by simp [A0]))
                have i1 : A ∩ (A1 ∪ E) = A1 := by
                  ext z; simp only [Finset.mem_inter, Finset.mem_union]
                  constructor
                  · rintro ⟨h1, h2 | h2⟩
                    · exact h2
                    · exact absurd h1 (hdis z h2)
                  · intro h; exact ⟨hA1 h, Or.inl h⟩
                have i2 : A \ (A1 ∪ E) = A \ A1 := by
                  ext z; simp only [Finset.mem_sdiff, Finset.mem_union]
                  constructor
                  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 (Or.inl h)⟩
                  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h.elim h2 (fun h => hdis z h h1)⟩
                have i3 : (A \ A1).card = (k - 1) / 2 := by
                  rw [Finset.card_sdiff_of_subset hA1, hA, hA1c]; omega
                have hlen : (k - 1) / 2 ≤ p.length := by
                  simp only [B0] at h0
                  rw [i1, i2, i3, hA1c] at h0
                  omega
                have hdd : (oddGraph S k).dist A0 B0 ≤ (oddGraph S k).diam := dist_le_diam (ETOP S k hk hS)
                omega
              have CONC : ∀ (S : Type) [Fintype S] [DecidableEq S] (k : ℕ), 1 ≤ k → Fintype.card S = 2 * k - 1 →
                  ∀ ρ : ℝ, 0 < ρ → concentrationFun (oddGraph S k) ρ ≤
                    2 * Real.exp (2 - ρ / (2 * Real.sqrt ((2 * k - 1 : ℕ) : ℝ))) := by
                intro S _ _ k hk hS ρ hρ
                unfold concentrationFun
                split_ifs with hV
                · positivity
                apply Finset.sup'_le
                intro 𝒜 h𝒜
                rw [Finset.mem_filter] at h𝒜
                have hVpos : (0 : ℝ) < Fintype.card {A : Finset S // A.card = k - 1} := by exact_mod_cast Nat.pos_of_ne_zero hV
                have hne : 𝒜.Nonempty := by
                  rw [← Finset.card_pos]
                  have : (0 : ℝ) < 𝒜.card := by linarith [h𝒜.2]
                  exact_mod_cast this
                let f : Finset S → ℝ := fun B => 𝒜.inf' hne (fun a => ((a.1 \ B).card : ℝ))
                have hf : ∀ B x, f B - 1 ≤ f (insert x B) ∧ f (insert x B) ≤ f B := by
                  intro B x
                  constructor
                  · apply Finset.le_inf'
                    intro a ha
                    have h1 : f B ≤ ((a.1 \ B).card : ℝ) := Finset.inf'_le _ ha
                    have h2 : (a.1 \ B).card ≤ (a.1 \ insert x B).card + 1 := by
                      have : a.1 \ B ⊆ insert x (a.1 \ insert x B) := by
                        intro z hz
                        rw [Finset.mem_sdiff] at hz
                        by_cases hzx : z = x
                        · rw [hzx]; exact Finset.mem_insert_self _ _
                        · refine Finset.mem_insert_of_mem (Finset.mem_sdiff.2 ⟨hz.1, fun h => ?_⟩)
                          exact (Finset.mem_insert.1 h).elim hzx hz.2
                      exact (Finset.card_le_card this).trans (Finset.card_insert_le _ _)
                    have h3 : ((a.1 \ B).card : ℝ) ≤ (a.1 \ insert x B).card + 1 := by exact_mod_cast h2
                    linarith
                  · apply Finset.le_inf'
                    intro a ha
                    refine (Finset.inf'_le _ ha).trans ?_
                    exact_mod_cast Finset.card_le_card (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) (Finset.subset_insert _ _))
                set s : Finset (Finset S) := (Finset.univ : Finset S).powersetCard (k - 1) with hs
                have hsub : ∀ g : Finset S → ℝ, ∑ A ∈ s, g A = ∑ v : {A : Finset S // A.card = k - 1}, g v.1 := by
                  intro g
                  symm
                  apply Finset.sum_bij (fun v _ => v.1)
                  · intro v _; rw [hs, Finset.mem_powersetCard]; exact ⟨Finset.subset_univ _, v.2⟩
                  · intro a _ b _ h; exact Subtype.ext h
                  · intro b hb; rw [hs, Finset.mem_powersetCard] at hb; exact ⟨⟨b, hb.2⟩, Finset.mem_univ _, rfl⟩
                  · intro a _; rfl
                have hcard : (s.card : ℝ) = Fintype.card {A : Finset S // A.card = k - 1} := by
                  have := hsub (fun _ => 1)
                  simpa using this
                set N : ℝ := (Fintype.card {A : Finset S // A.card = k - 1} : ℝ) with hN
                set n : ℝ := ((2 * k - 1 : ℕ) : ℝ) with hn
                have hn1 : 1 ≤ n := by rw [hn]; exact_mod_cast (by omega : 1 ≤ 2 * k - 1)
                set q := Real.sqrt n with hq
                have hq1 : 1 ≤ q := by rw [hq, Real.one_le_sqrt]; exact hn1
                have hq2 : q ^ 2 = n := Real.sq_sqrt (by linarith)
                set t : ℝ := 1 / q with ht
                have ht0 : 0 < t := by positivity
                have ht1 : |t| ≤ 1 := by rw [abs_of_pos ht0, ht]; exact (div_le_one (by linarith)).2 hq1
                have hnt : n * t ^ 2 = 1 := by rw [ht, ← hq2]; field_simp
                have hcs : ((Finset.univ : Finset S).card : ℝ) = n := by rw [Finset.card_univ, hS]
                have L1 := LAP t ht1 Finset.univ (k - 1) f hf
                have L2 := LAP (-t) (by rwa [abs_neg]) Finset.univ (k - 1) f hf
                rw [← hs, hcard, hcs, hsub, neg_sq, hnt] at L2
                rw [← hs, hcard, hcs, hsub, hnt] at L1
                set E : ℝ := (∑ A ∈ s, f A) / N with hEd
                have f0 : ∀ a ∈ 𝒜, f a.1 ≤ 0 := by
                  intro a ha
                  have : f a.1 ≤ ((a.1 \ a.1).card : ℝ) := Finset.inf'_le _ ha
                  simpa using this
                have hlow : (𝒜.card : ℝ) ≤ ∑ v : {A : Finset S // A.card = k - 1}, Real.exp (-t * f v.1) := by
                  calc (𝒜.card : ℝ) = ∑ v ∈ 𝒜, (1 : ℝ) := by simp
                    _ ≤ ∑ v ∈ 𝒜, Real.exp (-t * f v.1) := by
                      apply Finset.sum_le_sum
                      intro v hv
                      apply Real.one_le_exp
                      exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.2 ht0.le) (f0 v hv)
                    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => (Real.exp_pos _).le)
                have hEe : Real.exp (t * E) ≤ 2 * Real.exp 1 := by
                  have h1 : N ≤ 2 * (N * Real.exp (-t * E + 1)) := by
                    linarith only [h𝒜.2, hlow, L2]
                  have h2 : 1 ≤ 2 * Real.exp (-t * E + 1) := by
                    have h1' : N * 1 ≤ N * (2 * Real.exp (-t * E + 1)) := by linarith only [h1]
                    exact le_of_mul_le_mul_left h1' hVpos
                  have h3 : Real.exp (-t * E + 1) * Real.exp (t * E) = Real.exp 1 := by
                    rw [← Real.exp_add]; congr 1; ring
                  calc Real.exp (t * E) = 1 * Real.exp (t * E) := (one_mul _).symm
                    _ ≤ 2 * Real.exp (-t * E + 1) * Real.exp (t * E) := mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
                    _ = 2 * (Real.exp (-t * E + 1) * Real.exp (t * E)) := mul_assoc _ _ _
                    _ = 2 * Real.exp 1 := by rw [h3]
                set X := enlargement (oddGraph S k) 𝒜 ρ with hX
                have hbad : ∀ v, v ∉ X → ρ / 2 ≤ f v.1 := by
                  intro v hv
                  by_contra hcon
                  push Not at hcon
                  obtain ⟨a, ha, hfa⟩ := Finset.exists_mem_eq_inf' hne (fun a => ((a.1 \ v.1).card : ℝ))
                  have hfa' : f v.1 = ((a.1 \ v.1).card : ℝ) := hfa
                  apply hv
                  simp only [hX, enlargement, Finset.mem_filter]
                  have hup := UP S k hk hS _ a v rfl
                  have hr : (oddGraph S k).Reachable a v := by
                    rw [← edist_ne_top_iff_reachable]
                    intro htop
                    rw [htop, top_le_iff] at hup
                    exact ENat.coe_ne_top _ hup
                  refine ⟨Finset.mem_univ _, a, ha, hr, ?_⟩
                  rw [← hr.coe_dist_eq_edist] at hup
                  have h1 : (oddGraph S k).dist a v ≤ 2 * (a.1 \ v.1).card := by exact_mod_cast hup
                  have h2 : ((oddGraph S k).dist a v : ℝ) ≤ 2 * ((a.1 \ v.1).card : ℝ) := by exact_mod_cast h1
                  linarith
                classical
                have hcomp : ((Finset.univ \ X).card : ℝ) = N - X.card := by
                  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
                  rw [Nat.cast_sub (by rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _))]
                have hmark : ((Finset.univ \ X).card : ℝ) * Real.exp (t * (ρ / 2)) ≤ N * Real.exp (t * E + 1) := by
                  refine le_trans ?_ L1
                  calc ((Finset.univ \ X).card : ℝ) * Real.exp (t * (ρ / 2)) = ∑ v ∈ Finset.univ \ X, Real.exp (t * (ρ / 2)) := by simp
                    _ ≤ ∑ v ∈ Finset.univ \ X, Real.exp (t * f v.1) := by
                      apply Finset.sum_le_sum
                      intro v hv
                      apply Real.exp_le_exp.2
                      exact mul_le_mul_of_nonneg_left (hbad v (Finset.mem_sdiff.1 hv).2) ht0.le
                    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => (Real.exp_pos _).le)
                have e1 : 1 - (X.card : ℝ) / N = ((Finset.univ \ X).card : ℝ) / N := by
                  rw [hcomp, sub_div, div_self hVpos.ne']
                rw [e1, div_le_iff₀ hVpos]
                have e2 : Real.exp (2 - ρ / (2 * q)) = Real.exp 1 * Real.exp 1 * Real.exp (-(t * (ρ / 2))) := by
                  rw [← Real.exp_add, ← Real.exp_add]; congr 1; rw [ht]; field_simp; ring
                have e3 : Real.exp (t * (ρ / 2)) * Real.exp (-(t * (ρ / 2))) = 1 := by
                  rw [← Real.exp_add]; simp
                have hpe := Real.exp_pos (-(t * (ρ / 2)))
                rw [e2]
                rw [Real.exp_add] at hmark
                have h5 : N * (Real.exp (t * E) * Real.exp 1) ≤ N * (2 * Real.exp 1 * Real.exp 1) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hEe (Real.exp_pos 1).le) hVpos.le
                have h6 := mul_le_mul_of_nonneg_right (hmark.trans h5) hpe.le
                rw [mul_assoc, e3] at h6
                linarith
              have hI : ∀ (S : ℕ+ → Type) [∀ k, Fintype (S k)] [∀ k, DecidableEq (S k)],
                    (∀ k, Fintype.card (S k) = 2 * (k : ℕ) - 1) →
                    IsConcentrated (fun k => {A : Finset (S k) // A.card = (k : ℕ) - 1})
                      (fun k => oddGraph (S k) (k : ℕ)) := by
                intro S _ _ hS
                refine ⟨2 * Real.exp 2, 1 / 6, mul_pos two_pos (Real.exp_pos 2), by norm_num, ?_⟩
                intro k ρ hρ
                have hk : 1 ≤ (k : ℕ) := k.pos
                by_cases hd : (oddGraph (S k) (k : ℕ)).diam = 0
                · rw [hd]
                  have := F1 (oddGraph (S k) (k : ℕ)) ρ hρ.le
                  have h2 := Real.add_one_le_exp (2 : ℝ)
                  rw [Nat.cast_zero, Real.sqrt_zero, div_zero, Nat.floor_zero, Nat.cast_zero, neg_zero, Real.exp_zero, mul_one]
                  linarith only [this, h2]
                have hD := DIAM (S k) k hk (hS k)
                have hC := CONC (S k) k hk (hS k) ρ hρ
                refine hC.trans ?_
                rw [mul_assoc, ← Real.exp_add]
                apply mul_le_mul_of_nonneg_left _ (by norm_num)
                apply Real.exp_le_exp.2
                have h7 : 2 * (k : ℕ) - 1 ≤ 9 * (oddGraph (S k) (k : ℕ)).diam := by omega
                have h7' : ((2 * (k : ℕ) - 1 : ℕ) : ℝ) ≤ 9 * ((oddGraph (S k) (k : ℕ)).diam : ℝ) := by exact_mod_cast h7
                set q := Real.sqrt ((2 * (k : ℕ) - 1 : ℕ) : ℝ) with hq
                set r := Real.sqrt ((oddGraph (S k) (k : ℕ)).diam : ℝ) with hr
                have hq0 : 0 < q := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < 2 * (k : ℕ) - 1))
                have hr0 : 0 < r := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hd)
                have hqr : q ≤ 3 * r := by
                  rw [hq, Real.sqrt_le_left (by positivity), mul_pow, hr, Real.sq_sqrt (Nat.cast_nonneg _)]
                  linarith
                have hfl : (⌊1 / 6 * ρ / r⌋₊ : ℝ) ≤ 1 / 6 * ρ / r := Nat.floor_le (by positivity)
                have hle : 1 / 6 * ρ / r ≤ ρ / (2 * q) := by
                  rw [div_le_div_iff₀ hr0 (mul_pos two_pos hq0)]
                  have h8 : ρ * q ≤ ρ * (3 * r) := mul_le_mul_of_nonneg_left hqr hρ.le
                  linarith only [h8]
                linarith only [hfl, hle]
              refine ⟨hI, fun V _ _ G _ hreg hc => hII V G hreg hc, ?_⟩
              intro S _ _ hS
              exact hII _ _ (fun k => REG (S k) (k : ℕ) k.pos (hS k)) (hI S hS)
