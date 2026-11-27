-- Prove2me | solution 1 for AtomicDynRouting.ResidenceTime.Supplement.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:17:57.807786+00:00
-- url     : https://prove2.me/submissions/a152ddc7-810d-4766-ab13-dd30645ed72f

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Supplement_Equilibrium

open AtomicDynRouting
open AtomicDynRouting.ResidenceTime
open AtomicDynRouting.ResidenceTime.Supplement

open AtomicDynRouting.ResidenceTime

theorem solution {ι V E : Type} [Fintype V] [Fintype E] (G : Game ι V E) (hN : G.N.Acyclic) (hG : G.Standing) (p : ι → List E) (hp : G.IsEquilibrium p) :
    (∀ i j v, G.preempts p i j v → G.arrTime p i G.d ≤ G.arrTime p j G.d) ∧
    (∀ (T : ℕ) (q : ι → List E), G.IsProfile q → (∀ i ∈ G.batchesUpTo p T, q i = p i) →
      (∀ i ∈ G.batchesUpTo p T, ∀ j ∉ G.batchesUpTo p T, ∀ v,
          G.passes q i v → G.passes q j v → G.preempts q i j v) ∧
      (∀ i ∈ G.batchesUpTo p T, ∀ v, G.arrTime q i v = G.arrTime p i v)) := by
        classical
        -- a path from `u` through the edge `e` has a nonempty prefix from `u` to `head e`
        have hpfx : ∀ (P : List E) (u w : V), G.N.IsPathFrom u w P → ∀ e ∈ P,
            ∃ P1 : List E, G.N.IsPathFrom u (G.N.head e) P1 ∧ P1 ≠ [] := by
          intro P
          induction P with
          | nil => intro u w _ e he; simp at he
          | cons e' P' ih =>
            intro u w hP e he
            rcases hP with ⟨h1, h2⟩
            rcases List.mem_cons.1 he with rfl | he'
            · exact ⟨[e], ⟨h1, rfl⟩, by simp⟩
            · obtain ⟨P1, hP1, -⟩ := ih _ _ h2 e he'
              exact ⟨e' :: P1, ⟨h1, hP1⟩, by simp⟩
        -- in an acyclic network, a path enters each vertex through at most one edge
        have uniqIn : ∀ (P : List E) (u w : V), G.N.IsPathFrom u w P → ∀ e1 ∈ P, ∀ e2 ∈ P,
            G.N.head e1 = G.N.head e2 → e1 = e2 := by
          intro P
          induction P with
          | nil => intro u w _ e1 he1; simp at he1
          | cons e' P' ih =>
            intro u w hP e1 he1 e2 he2 hh
            rcases hP with ⟨h1, h2⟩
            rcases List.mem_cons.1 he1 with rfl | he1' <;> rcases List.mem_cons.1 he2 with rfl | he2'
            · rfl
            · obtain ⟨P1, hP1, hne⟩ := hpfx P' _ _ h2 e2 he2'
              rw [← hh] at hP1
              exact absurd (hN _ _ hP1) hne
            · obtain ⟨P1, hP1, hne⟩ := hpfx P' _ _ h2 e1 he1'
              rw [hh] at hP1
              exact absurd (hN _ _ hP1) hne
            · exact ih _ _ h2 e1 he1' e2 he2' hh
        have hprof : G.IsProfile p := by
          unfold Game.IsEquilibrium at hp
          split at hp
          · exact hp.1
          · exact hp.1
          · exact hp.1
        -- preemption is asymmetric for profiles
        have asymm : ∀ (q : ι → List E), G.IsProfile q → ∀ i j v,
            G.preempts q i j v → G.preempts q j i v → False := by
          intro q hq i j v h1 h2
          have hv := hG.2
          unfold Game.preempts at h1 h2
          obtain ⟨-, -, h1⟩ := h1
          obtain ⟨-, -, h2⟩ := h2
          rcases h1 with h1 | ⟨h1e, h1⟩ <;> rcases h2 with h2 | ⟨h2e, h2⟩
          · exact absurd (h1.trans h2) (lt_irrefl _)
          · rw [h2e] at h1; exact lt_irrefl _ h1
          · rw [h1e] at h2; exact lt_irrefl _ h2
          · unfold Game.RuleValid at hv
            revert h1 h2 hv
            cases G.rule with
            | r1 hp' =>
              intro hv h1 h2
              have := hv.1; exact _root_.asymm h1 h2
            | r2 hp' =>
              intro hv h1 h2
              have := hv.1; exact _root_.asymm h1 h2
            | r3 ep op =>
              intro hv h1 h2
              rcases h1 with ⟨hvo, ei, ej, hei, hej, hep⟩ | ⟨hvo, hop⟩ <;>
                rcases h2 with ⟨hvo', ej', ei', hej', hei', hep'⟩ | ⟨hvo', hop'⟩
              · have e1 : ei = ei' := uniqIn _ _ _ (hq i).1 _ hei.1 _ hei'.1 (hei.2.trans hei'.2.symm)
                have e2 : ej = ej' := uniqIn _ _ _ (hq j).1 _ hej.1 _ hej'.1 (hej.2.trans hej'.2.symm)
                subst e1 e2
                have := (hv.1 v); exact _root_.asymm hep hep'
              · exact hvo hvo'
              · exact hvo' hvo
              · have := hv.2; exact _root_.asymm hop hop'
        classical
        have hsel : ∀ X t i, G.selected X t (G.state X t) i →
            G.state X (t+1) i = ⟨(G.state X t i).pos + 1, t + 1⟩ := by
          intro X t i h
          simp [Game.state, h]
        have hnsel : ∀ X t i, ¬ G.selected X t (G.state X t) i →
            G.state X (t+1) i = G.state X t i := by
          intro X t i h
          simp [Game.state, h]
        have hpos1 : ∀ X t i, (G.state X t i).pos ≤ (G.state X (t+1) i).pos ∧
            (G.state X (t+1) i).pos ≤ (G.state X t i).pos + 1 := by
          intro X t i
          by_cases h : G.selected X t (G.state X t) i
          · rw [hsel X t i h]; simp
          · rw [hnsel X t i h]; simp
        have hmono : ∀ X i t t', t ≤ t' → (G.state X t i).pos ≤ (G.state X t' i).pos := by
          intro X i t t' h
          induction h with
          | refl => exact le_rfl
          | step _ ih => exact ih.trans (hpos1 X _ i).1
        have hleave_unf : ∀ X i m, G.leave X i m =
            if h : ∃ t, m < (G.state X (t + 1) i).pos then ((Nat.find h : ℕ) : ℕ∞) else ⊤ := by
          intro X i m; unfold Game.leave; rfl
        have hleave_eq : ∀ X i s, G.selected X s (G.state X s) i →
            G.leave X i (G.state X s i).pos = s := by
          intro X i s h
          rw [hleave_unf]
          have hex : ∃ t, (G.state X s i).pos < (G.state X (t + 1) i).pos :=
            ⟨s, by rw [hsel X s i h]; simp⟩
          rw [dif_pos hex]
          congr 1
          apply le_antisymm
          · exact Nat.find_le (by rw [hsel X s i h]; simp)
          · by_contra hlt
            push Not at hlt
            have := Nat.find_spec hex
            have := hmono X i (Nat.find hex + 1) s (by omega)
            omega
        have hleave_spec : ∀ X i m (s : ℕ), G.leave X i m = (s : ℕ∞) →
            (G.state X s i).pos = m ∧ G.selected X s (G.state X s) i := by
          intro X i m s h
          rw [hleave_unf] at h
          split_ifs at h with hex
          · have hs : Nat.find hex = s := by exact_mod_cast h
            have h1 := Nat.find_spec hex
            rw [hs] at h1
            have h2 : (G.state X s i).pos ≤ m := by
              rcases Nat.eq_zero_or_pos s with h0 | h0
              · subst h0; simp [Game.state]
              · have := Nat.find_min hex (show s - 1 < Nat.find hex by omega)
                push Not at this
                rwa [show s - 1 + 1 = s by omega] at this
            have h3 := hpos1 X s i
            have hpm : (G.state X s i).pos = m := by omega
            refine ⟨hpm, ?_⟩
            by_contra hn
            rw [hnsel X s i hn] at h1
            omega
          · exact absurd h.symm (ENat.natCast_ne_top s)
        have hsince : ∀ X t i, ((G.state X t i).since : ℕ∞) = G.reach X i (G.state X t i).pos := by
          intro X t i
          induction t with
          | zero => simp [Game.state, Game.reach]
          | succ t ih =>
            by_cases h : G.selected X t (G.state X t) i
            · rw [hsel X t i h]
              simp only [Game.reach, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
              rw [hleave_eq X i t h]; push_cast; rfl
            · rw [hnsel X t i h]; exact ih
        have hsince_bd : ∀ X t i, G.entry i ≤ (G.state X t i).since ∧
            (G.state X t i).since ≤ max (G.entry i) t := by
          intro X t i
          induction t with
          | zero => simp [Game.state]
          | succ t ih =>
            by_cases h : G.selected X t (G.state X t) i
            · rw [hsel X t i h]
              have := h.1
              simp; omega
            · rw [hnsel X t i h]; omega
        have hreach_le : ∀ X i m (s : ℕ), G.reach X i m ≤ (s : ℕ∞) → m ≤ (G.state X s i).pos := by
          intro X i m s h
          rcases m with _ | m
          · omega
          · simp only [Game.reach, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at h
            obtain ⟨s', hs'⟩ : ∃ s' : ℕ, G.leave X i m = (s' : ℕ∞) := by
              cases hl : G.leave X i m with
              | top => rw [hl] at h; simp at h
              | coe a => exact ⟨a, rfl⟩
            rw [hs'] at h
            have hss : s' + 1 ≤ s := by exact_mod_cast h
            obtain ⟨h1, h2⟩ := hleave_spec X i m s' hs'
            have := hsel X s' i h2
            have h4 := hmono X i (s'+1) s hss
            rw [this] at h4
            simp at h4; omega
        have hpos_eq : ∀ X i m (s : ℕ), G.reach X i m ≤ (s : ℕ∞) → ¬ G.leave X i m ≤ (s : ℕ∞) →
            (G.state X s i).pos = m := by
          intro X i m s h1 h2
          have := hreach_le X i m s h1
          by_contra hne
          apply h2
          rw [hleave_unf]
          have hex : ∃ t, m < (G.state X (t + 1) i).pos := ⟨s, by have := (hpos1 X s i).1; omega⟩
          rw [dif_pos hex]
          have : Nat.find hex ≤ s := Nat.find_le (by have := (hpos1 X s i).1; omega)
          exact_mod_cast this
        have hpath_app : ∀ (L1 L2 : List E) u w, G.N.IsPathFrom u w (L1 ++ L2) ↔
            ∃ x, G.N.IsPathFrom u x L1 ∧ G.N.IsPathFrom x w L2 := by
          intro L1 L2
          induction L1 with
          | nil => intro u w; simp [Network.IsPathFrom]
          | cons e L ih =>
            intro u w
            simp only [List.cons_append, Network.IsPathFrom, ih]
            constructor
            · rintro ⟨h1, x, h2, h3⟩; exact ⟨x, ⟨h1, h2⟩, h3⟩
            · rintro ⟨x, ⟨h1, h2⟩, h3⟩; exact ⟨h1, x, h2, h3⟩
        have hconsec : ∀ (L : List E) u w, G.N.IsPathFrom u w L → ∀ m e e', L[m]? = some e →
            L[m+1]? = some e' → G.N.head e = G.N.tail e' := by
          intro L
          induction L with
          | nil => intro u w _ m e e' h; simp at h
          | cons a L ih =>
            intro u w hP m e e' h1 h2
            simp only [Network.IsPathFrom] at hP
            rcases m with _ | m
            · simp at h1 h2; subst h1
              cases L with
              | nil => simp at h2
              | cons b L => simp at h2; subst h2; exact hP.2.1.symm
            · simp at h1 h2
              exact ih _ _ hP.2 m e e' h1 h2
        have hfirst : ∀ (L : List E) u w e, G.N.IsPathFrom u w L → L[0]? = some e → G.N.tail e = u := by
          intro L u w e hP h
          cases L with
          | nil => simp at h
          | cons a L => simp at h; subst h; exact hP.1
        have hend : ∀ (L : List E) u w, G.N.IsPathFrom u w L → ∀ n e, L[n]? = some e →
            n + 1 = L.length → G.N.head e = w := by
          intro L
          induction L with
          | nil => intro u w _ n e h; simp at h
          | cons a L ih =>
            intro u w hP n e h1 h2
            simp only [Network.IsPathFrom] at hP
            rcases n with _ | n
            · simp at h1; subst h1
              rcases L with _ | ⟨b, L⟩
              · exact hP.2
              · simp at h2
            · simp at h1 h2
              exact ih _ _ hP.2 n e h1 (by omega)
        have hvtx : ∀ (L : List E) w, G.N.IsPathFrom G.o w L → ∀ m e, L[m]? = some e →
            G.vtxAt L m = some (G.N.tail e) := by
          intro L w hP m e h
          rcases m with _ | m
          · simp [Game.vtxAt, hfirst L G.o w e hP h]
          · obtain ⟨e0, he0⟩ : ∃ e0, L[m]? = some e0 := by
              have := (List.getElem?_eq_some_iff.mp h).1
              exact ⟨L[m], List.getElem?_eq_getElem (by omega)⟩
            simp [Game.vtxAt, he0, hconsec L G.o w hP m e0 e he0 h]
        have hsplit : ∀ (L : List E) w, G.N.IsPathFrom G.o w L → ∀ m x, m ≤ L.length →
            G.vtxAt L m = some x → G.N.IsPathFrom G.o x (L.take m) ∧ G.N.IsPathFrom x w (L.drop m) := by
          intro L w hP m x hm hx
          have h := hP
          rw [← List.take_append_drop m L, hpath_app] at h
          obtain ⟨y, h1, h2⟩ := h
          have hy : y = x := by
            rcases m with _ | m
            · simp [Game.vtxAt] at hx; simp [Network.IsPathFrom] at h1; rw [← h1, hx]
            · obtain ⟨e0, he0⟩ : ∃ e0, L[m]? = some e0 := ⟨L[m], by simp <;> omega⟩
              simp [Game.vtxAt, he0] at hx
              have := hend (L.take (m+1)) G.o y h1 m e0 (by rw [List.getElem?_take_of_lt (by omega)]; exact he0)
                (by rw [List.length_take]; omega)
              rw [← this, hx]
          subst hy; exact ⟨h1, h2⟩
        have hbetC : ∀ (Y1 Y2 : ι → List E) i a k b, (Y1 i)[AState.pos a - 1]? = (Y2 i)[AState.pos a - 1]? →
            (Y1 k)[AState.pos b - 1]? = (Y2 k)[AState.pos b - 1]? →
            (G.better Y1 i a k b ↔ G.better Y2 i a k b) := by
          intro Y1 Y2 i a k b h1 h2
          unfold Game.better
          cases G.rule with
          | r1 _ => exact Iff.rfl
          | r2 _ => exact Iff.rfl
          | r3 ep op => simp only [h1, h2]
        have hcaus : ∀ (Y1 Y2 : ι → List E) l i, (∀ c, c ≠ l → Y1 c = Y2 c) →
            (Y1 l).take i = (Y2 l).take i → ∀ t, (∀ t' < t, (G.state Y1 t' l).pos < i) →
            G.state Y1 t = G.state Y2 t := by
          intro Y1 Y2 l i hY hT t
          induction t with
          | zero => intro _; rfl
          | succ t ih =>
            intro ht
            have ih' := ih (fun t' h => ht t' (by omega))
            have hlook : ∀ k, (Y1 k)[(G.state Y1 t k).pos]? = (Y2 k)[(G.state Y1 t k).pos]? := by
              intro k
              by_cases hk : k = l
              · subst hk
                have hlt := ht t (by omega)
                rw [← List.getElem?_take_of_lt hlt, hT, List.getElem?_take_of_lt hlt]
              · rw [hY k hk]
            have hlook1 : ∀ k, (Y1 k)[(G.state Y1 t k).pos - 1]? = (Y2 k)[(G.state Y1 t k).pos - 1]? := by
              intro k
              by_cases hk : k = l
              · subst hk
                have hlt : (G.state Y1 t k).pos - 1 < i := by have := ht t (by omega); omega
                rw [← List.getElem?_take_of_lt hlt, hT, List.getElem?_take_of_lt hlt]
              · rw [hY k hk]
            have hiff : ∀ c, G.selected Y1 t (G.state Y1 t) c ↔ G.selected Y2 t (G.state Y2 t) c := by
              intro c
              rw [← ih']
              have hb : ∀ k, G.better Y1 c (G.state Y1 t c) k (G.state Y1 t k) ↔
                  G.better Y2 c (G.state Y1 t c) k (G.state Y1 t k) := fun k =>
                hbetC _ _ _ _ _ _ (hlook1 c) (hlook1 k)
              simp only [Game.selected, hlook, hb]
            funext c
            by_cases h1 : G.selected Y1 t (G.state Y1 t) c
            · rw [hsel _ _ _ h1, hsel _ _ _ ((hiff c).mp h1), ih']
            · rw [hnsel _ _ _ h1, hnsel _ _ _ (fun h => h1 ((hiff c).mpr h)), ih']
        have hcaus_reach : ∀ (Y1 Y2 : ι → List E) l i, (∀ c, c ≠ l → Y1 c = Y2 c) →
            (Y1 l).take i = (Y2 l).take i → G.reach Y1 l i = G.reach Y2 l i := by
          intro Y1 Y2 l i hY hT
          rcases i with _ | i
          · simp [Game.reach]
          · simp only [Game.reach, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
            have key : ∀ (Z1 Z2 : ι → List E), (∀ c, c ≠ l → Z1 c = Z2 c) →
                (Z1 l).take (i+1) = (Z2 l).take (i+1) → ∀ t,
                (G.state Z1 (t+1) l).pos ≤ i → (G.state Z2 (t+1) l).pos ≤ i := by
              intro Z1 Z2 hZ hZT t h
              have := hcaus Z1 Z2 l (i+1) hZ hZT (t+1) (fun t' ht' => by
                have := hmono Z1 l t' (t+1) (by omega); omega)
              rw [← this]; exact h
            have hP : ∀ t, i < (G.state Y1 (t+1) l).pos ↔ i < (G.state Y2 (t+1) l).pos := by
              intro t
              constructor
              · intro h; by_contra h'; push Not at h'
                have := key Y2 Y1 (fun c hc => (hY c hc).symm) hT.symm t h'; omega
              · intro h; by_contra h'; push Not at h'
                have := key Y1 Y2 hY hT t h'; omega
            rw [hleave_unf, hleave_unf]
            simp only [hP]
        have huniq : ∀ (L : List E) w, G.N.IsPathFrom G.o w L → ∀ i i' x, i ≤ L.length → i' ≤ L.length →
            G.vtxAt L i = some x → G.vtxAt L i' = some x → i = i' := by
          have one : ∀ (L : List E) w, G.N.IsPathFrom G.o w L → ∀ i i' x, i < i' → i' ≤ L.length →
              G.vtxAt L i = some x → G.vtxAt L i' = some x → False := by
            intro L w hP i i' x hlt hi' hx hx'
            obtain ⟨h1, -⟩ := hsplit L w hP i' x hi' hx'
            have hx2 : G.vtxAt (L.take i') i = some x := by
              rw [← hx]
              rcases i with _ | i
              · simp [Game.vtxAt]
              · simp only [Game.vtxAt, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
                rw [List.getElem?_take_of_lt (by omega)]
            obtain ⟨-, h2⟩ := hsplit (L.take i') x h1 i x (by rw [List.length_take]; omega) hx2
            have := hN x _ h2
            have := congrArg List.length this
            simp [List.length_drop, List.length_take] at this
            omega
          intro L w hP i i' x hi hi' hx hx'
          rcases lt_trichotomy i i' with h | h | h
          · exact (one L w hP i i' x h hi' hx hx').elim
          · exact h
          · exact (one L w hP i' i x h hi hx' hx).elim
        have core12 : ∀ hp : ι → ι → Prop, (G.rule = .r1 hp ∨ G.rule = .r2 hp) → G.IsUFR p →
          ∀ (T : ℕ) (q : ι → List E), G.IsProfile q → (∀ i ∈ G.batchesUpTo p T, q i = p i) →
            (∀ i ∈ G.batchesUpTo p T, ∀ j ∉ G.batchesUpTo p T, ∀ v,
                G.passes q i v → G.passes q j v → G.preempts q i j v) ∧
            (∀ i ∈ G.batchesUpTo p T, ∀ v, G.arrTime q i v = G.arrTime p i v) := by
          intro hp hrule hpU
          have hbet : ∀ (Y1 Y2 : ι → List E) a b c d, G.better Y1 a b c d ↔ G.better Y2 a b c d := by
            intro Y1 Y2 a b c d
            rcases hrule with hr | hr <;> simp [Game.better, hr]
          obtain ⟨hsto, hentry⟩ : IsStrictTotalOrder ι hp ∧ ∀ i j, G.entry i < G.entry j → hp i j := by
            have := hG.2
            rcases hrule with hr | hr <;> simpa [Game.RuleValid, hr] using this
          have hirr : ∀ a, ¬ hp a a := fun a => irrefl a
          have htrans : ∀ a b c, hp a b → hp b c → hp a c := fun _ _ _ => _root_.trans
          have htri : ∀ a b, hp a b ∨ a = b ∨ hp b a := fun a b => trichotomous a b
          set μ : ι → V → ℕ∞ := fun l w => ⨅ (P : List E) (_ : G.IsODPath P), G.arrTime (deviate p l P) l w
            with hμ
          have hM : ∀ t, (∀ h X, G.IsProfile X → (∀ c, (hp c h ∨ c = h) → X c = p c) →
                G.state X t h = G.state p t h) ∧
              (∀ l X, G.IsProfile X → (∀ c, hp c l → X c = p c) → ∀ k, ¬ hp k l → ∀ m w,
                m ≤ (X k).length → G.vtxAt (X k) m = some w → G.reach X k m ≤ t → μ l w ≤ G.reach X k m) := by
            have harr : ∀ h w i, i ≤ (p h).length → G.vtxAt (p h) i = some w →
                G.arrTime p h w = G.reach p h i := by
              intro h w i hi hw
              apply le_antisymm
              · exact iInf₂_le i ⟨hi, hw⟩
              · refine le_iInf₂ fun k hk => ?_
                have := huniq (p h) G.d (hpU.1 h).1 i k w hi hk.1 hw hk.2
                subst this; exact le_rfl
            have hlen : ∀ (L : List E) n e, L[n]? = some e → n < L.length := fun L n e h =>
              (List.getElem?_eq_some_iff.mp h).1
            intro t
            induction t using Nat.strong_induction_on with
            | _ t IH =>
            have hInvS : ∀ t', t' ≤ t → (∀ t'', t'' < t' → (∀ h X, G.IsProfile X →
                (∀ c, (hp c h ∨ c = h) → X c = p c) → G.state X t'' h = G.state p t'' h) ∧
                (∀ l X, G.IsProfile X → (∀ c, hp c l → X c = p c) → ∀ k, ¬ hp k l → ∀ m w,
                m ≤ (X k).length → G.vtxAt (X k) m = some w → G.reach X k m ≤ t'' →
                μ l w ≤ G.reach X k m)) → ∀ h X, G.IsProfile X →
                (∀ c, (hp c h ∨ c = h) → X c = p c) → G.state X t' h = G.state p t' h := by
              intro t' _ IH' h X hX hag
              rcases t' with _ | t'
              · rfl
              obtain ⟨Inv', F'⟩ := IH' t' (by omega)
              have hahead : ∀ Y, G.IsProfile Y → (∀ c, (hp c h ∨ c = h) → Y c = p c) → ∀ c e,
                  hp h c → G.entry c ≤ t' → (Y c)[(G.state Y t' c).pos]? = some e →
                  (Y h)[(G.state Y t' h).pos]? = some e →
                  (G.state Y t' h).since ≤ (G.state Y t' c).since := by
                intro Y hY hagY c e hhc hen hce hhe
                by_contra hlt; push Not at hlt
                have hvc := hvtx (Y c) G.d (hY c).1 _ e hce
                have h1 := F' h Y hY (fun c' hc' => hagY c' (Or.inl hc')) c
                  (fun h' => hirr _ (htrans _ _ _ h' hhc)) _ _ (le_of_lt (hlen _ _ _ hce)) hvc
                  (by rw [← hsince]; have := (hsince_bd Y t' c).2; exact_mod_cast (by omega : (G.state Y t' c).since ≤ t'))
                rw [← hsince] at h1
                have hYh : Y h = p h := hagY h (Or.inr rfl)
                have hsh : G.state Y t' h = G.state p t' h := Inv' h Y hY hagY
                rw [hYh, hsh] at hhe
                have hvh := hvtx (p h) G.d (hpU.1 h).1 _ e hhe
                have hpass : G.passes p h (G.N.tail e) := ⟨_, le_of_lt (hlen _ _ _ hhe), hvh⟩
                have h2 : G.arrTime p h (G.N.tail e) ≤ μ h (G.N.tail e) :=
                  le_iInf₂ fun P hP => not_lt.mp (hpU.2 h _ hpass P hP)
                rw [harr h _ _ (le_of_lt (hlen _ _ _ hhe)) hvh, ← hsince, ← hsh] at h2
                have := h2.trans h1
                have : (G.state Y t' h).since ≤ (G.state Y t' c).since := by exact_mod_cast this
                omega
              have hselY : ∀ Y, G.IsProfile Y → (∀ c, (hp c h ∨ c = h) → Y c = p c) →
                  (G.selected Y t' (G.state Y t') h ↔ G.selected p t' (G.state p t') h) := by
                intro Y hY hagY
                have hYh : Y h = p h := hagY h (Or.inr rfl)
                have hsh : G.state Y t' h = G.state p t' h := Inv' h Y hY hagY
                have hdown : ∀ c, hp c h → (∀ c', (hp c' c ∨ c' = c) → Y c' = p c') := by
                  intro c hc c' hc'
                  rcases hc' with hc' | rfl
                  · exact hagY c' (Or.inl (htrans _ _ _ hc' hc))
                  · exact hagY c' (Or.inl hc)
                have hlow : ∀ (Z : ι → List E), G.IsProfile Z → (∀ c, (hp c h ∨ c = h) → Z c = p c) →
                    ∀ c e, c ≠ h → ¬ hp c h → G.entry c ≤ t' → (Z c)[(G.state Z t' c).pos]? = some e →
                    (Z h)[(G.state Z t' h).pos]? = some e →
                    G.better Z h (G.state Z t' h) c (G.state Z t' c) := by
                  intro Z hZ hagZ c e hne hnh hen hce hhe
                  have hhc : hp h c := by
                    rcases htri h c with h' | h' | h'
                    · exact h'
                    · exact absurd h'.symm hne
                    · exact absurd h' hnh
                  have := hahead Z hZ hagZ c e hhc hen hce hhe
                  rcases hrule with hr | hr
                  · simp only [Game.better, hr]; exact hhc
                  · simp only [Game.better, hr]
                    rcases lt_or_eq_of_le this with h' | h'
                    · exact Or.inl h'
                    · exact Or.inr ⟨h', hhc⟩
                constructor
                · rintro ⟨hen, e, he, hall⟩
                  refine ⟨hen, e, by rw [← hYh, ← hsh]; exact he, fun c hc hen' hce => ?_⟩
                  by_cases hch : hp c h
                  · have hsc := Inv' c Y hY (hdown c hch)
                    have := hall c hc hen' (by rw [hdown c hch c (Or.inr rfl), hsc]; exact hce)
                    rw [hsh, hsc, hbet Y p] at this; exact this
                  · exact hlow p hpU.1 (fun _ _ => rfl) c e hc hch hen' hce (by rw [← hYh, ← hsh]; exact he)
                · rintro ⟨hen, e, he, hall⟩
                  refine ⟨hen, e, by rw [hYh, hsh]; exact he, fun c hc hen' hce => ?_⟩
                  by_cases hch : hp c h
                  · have hsc := Inv' c Y hY (hdown c hch)
                    have := hall c hc hen' (by rw [← hdown c hch c (Or.inr rfl), ← hsc]; exact hce)
                    rw [← hsh, ← hsc, hbet p Y] at this; exact this
                  · exact hlow Y hY hagY c e hc hch hen' hce (by rw [hYh, hsh]; exact he)
              have hsh : G.state X t' h = G.state p t' h := Inv' h X hX hag
              by_cases hs : G.selected p t' (G.state p t') h
              · rw [hsel _ _ _ hs, hsel _ _ _ ((hselY X hX hag).mpr hs), hsh]
              · rw [hnsel _ _ _ hs, hnsel _ _ _ (fun h' => hs ((hselY X hX hag).mp h')), hsh]
            refine ⟨hInvS t le_rfl IH, ?_⟩
            intro l X hX hag k hk m w hm hw hreach
            have hlk : G.entry l ≤ G.entry k := by
              by_contra h'; exact hk (hentry _ _ (by omega))
            rcases m with _ | m
            · simp [Game.vtxAt] at hw
              subst hw
              have hdp : deviate p l (p l) = p := by unfold deviate; exact Function.update_eq_self l p
              have : μ l G.o ≤ G.arrTime p l G.o := by
                have := iInf₂_le (f := fun (P : List E) (_ : G.IsODPath P) =>
                  G.arrTime (deviate p l P) l G.o) (p l) (hpU.1 l)
                rw [hdp] at this; exact this
              refine this.trans ((iInf₂_le 0 ⟨Nat.zero_le _, by simp [Game.vtxAt]⟩).trans ?_)
              simp [Game.reach]; exact_mod_cast hlk
            · simp only [Game.reach, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at hreach ⊢
              obtain ⟨s, hs⟩ : ∃ s : ℕ, G.leave X k m = (s : ℕ∞) := by
                cases hl : G.leave X k m with
                | top => rw [hl] at hreach; simp at hreach
                | coe a => exact ⟨a, rfl⟩
              rw [hs] at hreach ⊢
              have hst : s + 1 ≤ t := by exact_mod_cast hreach
              obtain ⟨hposk, hselk⟩ := hleave_spec X k m s hs
              obtain ⟨henk, e, he, hall⟩ := hselk
              rw [hposk] at he
              have hw' : w = G.N.head e := by simp [Game.vtxAt, he] at hw; exact hw.symm
              subst hw'
              have hvk := hvtx (X k) G.d (hX k).1 m e he
              have hmlt := hlen _ _ _ he
              have hsk : ((G.state X s k).since : ℕ∞) = G.reach X k m := by rw [hsince, hposk]
              have hsk_le : (G.state X s k).since ≤ s := by have := (hsince_bd X s k).2; omega
              have hμw' : μ l (G.N.tail e) ≤ G.reach X k m :=
                (IH (G.state X s k).since (by omega)).2 l X hX hag k hk m _ (by omega) hvk (by rw [← hsk])
              obtain ⟨Pw, hPw⟩ := ENat.exists_eq_iInf
                (fun P : List E => ⨅ (_ : G.IsODPath P), G.arrTime (deviate p l P) l (G.N.tail e))
              have hfin : μ l (G.N.tail e) ≠ ⊤ :=
                ne_top_of_le_ne_top (by rw [← hsk]; exact ENat.natCast_ne_top _) hμw'
              have hPwOD : G.IsODPath Pw := by
                by_contra hn; apply hfin; rw [hμ]; simp only; rw [← hPw]; simp [hn]
              have hPw' : G.arrTime (deviate p l Pw) l (G.N.tail e) = μ l (G.N.tail e) := by
                rw [hμ]; simp only; rw [← hPw]; simp [hPwOD]
              have hdPw : deviate p l Pw l = Pw := by unfold deviate; simp
              obtain ⟨i, hi⟩ := ENat.exists_eq_iInf (fun i => ⨅ (_ : i ≤ (deviate p l Pw l).length ∧
                G.vtxAt (deviate p l Pw l) i = some (G.N.tail e)), G.reach (deviate p l Pw) l i)
              have hi2 : G.arrTime (deviate p l Pw) l (G.N.tail e) = ⨅ (_ : i ≤ (deviate p l Pw l).length ∧
                  G.vtxAt (deviate p l Pw l) i = some (G.N.tail e)), G.reach (deviate p l Pw) l i := by
                unfold Game.arrTime; exact hi.symm
              have hci : i ≤ (deviate p l Pw l).length ∧ G.vtxAt (deviate p l Pw l) i = some (G.N.tail e) := by
                by_contra hn; rw [iInf_neg hn] at hi2; exact hfin (hPw' ▸ hi2)
              have hreach_i : G.reach (deviate p l Pw) l i = μ l (G.N.tail e) := by
                rw [← hPw', hi2, iInf_pos hci]
              rw [hdPw] at hci
              set P := Pw.take i ++ (X k).drop m with hP
              have htk : (Pw.take i).length = i := by simp; omega
              have hPOD : G.IsODPath P := by
                refine ⟨?_, ?_⟩
                · rw [hpath_app]
                  exact ⟨_, (hsplit Pw G.d hPwOD.1 i _ hci.1 hci.2).1,
                    (hsplit (X k) G.d (hX k).1 m _ (by omega) hvk).2⟩
                · intro h; rw [hP, List.append_eq_nil_iff] at h
                  have := congrArg List.length h.2; simp at this; omega
              set A := deviate p l P with hAdef
              have hAl : A l = P := by simp [A, deviate]
              have hAc : ∀ c, c ≠ l → A c = p c := fun c hc => by
                simp [A, deviate, Function.update_of_ne hc]
              have hreachA : G.reach A l i = μ l (G.N.tail e) := by
                rw [← hreach_i]; apply hcaus_reach
                · intro c hc; simp [A, deviate, Function.update_of_ne hc]
                · rw [hAl, hdPw, List.take_left' htk]
              have hPi : P[i]? = some e := by
                rw [hP, List.getElem?_append_right (by omega), htk]; simp [he]
              have hlenP := hlen _ _ _ hPi
              have hμw : μ l (G.N.head e) ≤ G.reach A l (i+1) := by
                refine (iInf₂_le P hPOD).trans ?_
                exact iInf₂_le (i+1) ⟨by simp only [deviate, Function.update_self]; omega,
                  by simp only [deviate, Function.update_self]; simp [Game.vtxAt, hPi]⟩
              refine hμw.trans ?_
              simp only [Game.reach, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
              suffices hsuf : G.leave A l i ≤ (s : ℕ∞) by exact add_le_add hsuf le_rfl
              by_contra hgt
              have hAprof : G.IsProfile A := fun c => by
                by_cases hc : c = l
                · subst hc; rw [hAl]; exact hPOD
                · rw [hAc c hc]; exact hpU.1 c
              have hagA : ∀ c, hp c l → A c = p c := fun c hc => hAc c (fun h => hirr _ (h ▸ hc))
              have hri : G.reach A l i ≤ (s : ℕ∞) := by
                rw [hreachA]; exact hμw'.trans (by rw [← hsk]; exact_mod_cast hsk_le)
              have hposA := hpos_eq A l i s hri hgt
              have hsinceA : ((G.state A s l).since : ℕ∞) = μ l (G.N.tail e) := by
                rw [hsince, hposA, hreachA]
              have henl : G.entry l ≤ s := by omega
              have hAle : (A l)[(G.state A s l).pos]? = some e := by rw [hposA, hAl, hPi]
              have hn2 : ¬ ∀ c, c ≠ l → G.entry c ≤ s → (A c)[(G.state A s c).pos]? = some e →
                  G.better A l (G.state A s l) c (G.state A s c) := fun hh =>
                hgt (by rw [← hposA, hleave_eq A l s ⟨henl, e, hAle, hh⟩])
              push Not at hn2
              obtain ⟨c, hcl, henc, hce, hnb⟩ := hn2
              have hsl_le_k : (G.state A s l).since ≤ (G.state X s k).since := by
                have : ((G.state A s l).since : ℕ∞) ≤ (G.state X s k).since := by
                  rw [hsinceA, hsk]; exact hμw'
                exact_mod_cast this
              by_cases hcH : hp c l
              · have hInvs := hInvS s (by omega) (fun t'' h => IH t'' (by omega))
                have hAc' := hInvs c A hAprof (fun c' hc' => hagA c'
                  (hc'.elim (fun h => htrans _ _ _ h hcH) (fun h => h ▸ hcH)))
                have hXc' := hInvs c X hX (fun c' hc' => hag c'
                  (hc'.elim (fun h => htrans _ _ _ h hcH) (fun h => h ▸ hcH)))
                have hck : c ≠ k := fun h => hk (h ▸ hcH)
                have hb := hall c hck henc (by rw [hag c hcH, hXc', ← hAc', ← hagA c hcH]; exact hce)
                rcases hrule with hr | hr
                · simp only [Game.better, hr] at hb; exact hk (htrans _ _ _ hb hcH)
                · simp only [Game.better, hr] at hb hnb
                  rcases hb with hb | ⟨_, hb⟩
                  · apply hnb; left; rw [hAc', ← hXc']; omega
                  · exact hk (htrans _ _ _ hb hcH)
              · have hlc : hp l c := by
                  rcases htri l c with h | h | h
                  · exact h
                  · exact absurd h.symm hcl
                  · exact absurd h hcH
                rcases hrule with hr | hr
                · simp only [Game.better, hr] at hnb; exact hnb hlc
                · simp only [Game.better, hr] at hnb
                  have hlt : (G.state A s c).since < (G.state A s l).since := by
                    by_contra h'; push Not at h'; apply hnb
                    rcases lt_or_eq_of_le h' with h'' | h''
                    · exact Or.inl h''
                    · exact Or.inr ⟨h'', hlc⟩
                  have hvc := hvtx (A c) G.d (hAprof c).1 _ e hce
                  have hsc_le : (G.state A s c).since ≤ s := by have := (hsince_bd A s c).2; omega
                  have h4 := (IH (G.state A s c).since (by omega)).2 l A hAprof hagA c hcH _ _
                    (le_of_lt (hlen _ _ _ hce)) hvc (by rw [← hsince])
                  rw [← hsince] at h4
                  have h3 : μ l (G.N.tail e) < μ l (G.N.tail e) := by
                    calc μ l (G.N.tail e) ≤ _ := h4
                      _ < ((G.state A s l).since : ℕ∞) := by exact_mod_cast hlt
                      _ = μ l (G.N.tail e) := hsinceA
                  exact lt_irrefl _ h3
          have hInv : ∀ h X, G.IsProfile X → (∀ c, (hp c h ∨ c = h) → X c = p c) → ∀ t,
              G.state X t h = G.state p t h := fun h X hX hag t => (hM t).1 h X hX hag
          have hF : ∀ l X, G.IsProfile X → (∀ c, hp c l → X c = p c) → ∀ k, ¬ hp k l → ∀ m w,
              m ≤ (X k).length → G.vtxAt (X k) m = some w → μ l w ≤ G.reach X k m := by
            intro l X hX hag k hk m w hm hw
            cases hr : G.reach X k m with
            | top => exact le_top
            | coe a => rw [← hr]; exact (hM a).2 l X hX hag k hk m w hm hw (by rw [hr])
          have h2 : ∀ l q, G.IsProfile q → (∀ k, hp k l → q k = p k) → q l = p l →
              ∀ j, hp l j → ∀ v, ¬ G.preempts q j l v := by
            intro l q hq hH hql j hlj v ⟨hpj, hpl, hcase⟩
            have hlt : G.arrTime q j v < G.arrTime q l v := by
              rcases hrule with hr | hr <;> simp only [hr] at hcase <;>
                rcases hcase with h | ⟨_, h⟩
              · exact h
              · exact absurd (htrans _ _ _ h hlj) (hirr _)
              · exact h
              · exact absurd (htrans _ _ _ h hlj) (hirr _)
            have hst : ∀ t, G.state q t l = G.state p t l :=
              hInv l q hq (fun c hc => hc.elim (hH c) (fun h => h ▸ hql))
            have e1 : G.arrTime q l v = G.arrTime p l v := by
              simp only [Game.arrTime, Game.reach, Game.leave, hst, hql]
            have hpl' : G.passes p l v := by
              obtain ⟨k, hk, hv⟩ := hpl; exact ⟨k, by rw [← hql]; exact hk, by rw [← hql]; exact hv⟩
            have e2 : G.arrTime p l v ≤ μ l v :=
              le_iInf₂ fun P hP => not_lt.mp (hpU.2 l v hpl' P hP)
            have e3 : μ l v ≤ G.arrTime q j v :=
              le_iInf₂ fun m hm => hF l q hq hH j (fun h => hirr _ (htrans _ _ _ h hlj)) m v hm.1 hm.2
            rw [e1] at hlt
            exact absurd (lt_of_lt_of_le hlt (e2.trans e3)) (lt_irrefl _)
          have hArr : ∀ (X : ι → List E), G.IsProfile X → ∀ h w i, i ≤ (X h).length →
              G.vtxAt (X h) i = some w → G.arrTime X h w = G.reach X h i := by
            intro X hX h w i hi hw
            apply le_antisymm
            · exact iInf₂_le i ⟨hi, hw⟩
            · refine le_iInf₂ fun k hk => ?_
              have := huniq (X h) G.d (hX h).1 i k w hi hk.1 hw hk.2
              subst this; exact le_rfl
          have hpassd : ∀ i, G.passes p i G.d := by
            intro i
            obtain ⟨hP, hne⟩ := hpU.1 i
            have hl : 0 < (p i).length := List.length_pos_iff.2 hne
            refine ⟨(p i).length, le_rfl, ?_⟩
            have he : (p i)[(p i).length - 1]? = some ((p i)[(p i).length - 1]'(by omega)) :=
              List.getElem?_eq_getElem (by omega)
            have := hend (p i) G.o G.d hP ((p i).length - 1) _ he (by omega)
            unfold Game.vtxAt
            rw [if_neg (by omega), he, Option.map_some, this]
          have htotP : ∀ q i j v, hp i j → G.passes q i v → G.passes q j v → ¬ G.preempts q j i v →
              G.preempts q i j v := by
            intro q i j v hij hi hj hn
            refine ⟨hi, hj, ?_⟩
            rcases lt_trichotomy (G.arrTime q i v) (G.arrTime q j v) with h | h | h
            · exact Or.inl h
            · right; refine ⟨h, ?_⟩
              rcases hrule with hr | hr <;> simp only [hr] <;> exact hij
            · exact absurd ⟨hj, hi, Or.inl h⟩ hn
          have hle : ∀ i j, hp i j → G.arrTime p i G.d ≤ G.arrTime p j G.d := by
            intro i j hij
            by_contra hlt
            push Not at hlt
            exact h2 i p hpU.1 (fun _ _ => rfl) rfl j hij G.d ⟨hpassd j, hpassd i, Or.inl hlt⟩
          intro T q hq hqp
          have hdown : ∀ i ∈ G.batchesUpTo p T, ∀ k, hp k i → k ∈ G.batchesUpTo p T := by
            intro i hi k hk
            exact (hle k i hk).trans hi
          refine ⟨?_, ?_⟩
          · intro i hi j hj v hiv hjv
            have hij : hp i j := by
              rcases htri i j with h | h | h
              · exact h
              · exact absurd (h ▸ hi) hj
              · exact absurd (hdown i hi j h) hj
            exact htotP q i j v hij hiv hjv
              (h2 i q hq (fun k hk => hqp k (hdown i hi k hk)) (hqp i hi) j hij v)
          · intro i hi v
            have hst : ∀ t, G.state q t i = G.state p t i :=
              hInv i q hq (fun c hc => hc.elim (fun h => hqp c (hdown i hi c h)) (fun h => h ▸ hqp i hi))
            simp only [Game.arrTime, Game.reach, Game.leave, hst, hqp i hi]
        have core3 : ∀ (ep : V → E → E → Prop) (op : ι → ι → Prop), G.rule = .r3 ep op → G.IsNE p →
          ∀ (T : ℕ) (q : ι → List E), G.IsProfile q → (∀ i ∈ G.batchesUpTo p T, q i = p i) →
            (∀ i ∈ G.batchesUpTo p T, ∀ j ∉ G.batchesUpTo p T, ∀ v,
                G.passes q i v → G.passes q j v → G.preempts q i j v) ∧
            (∀ i ∈ G.batchesUpTo p T, ∀ v, G.arrTime q i v = G.arrTime p i v) := by
          intro ep op hr hNE T
          set H := G.batchesUpTo p T with hHdef
          obtain ⟨hepO, hopO⟩ : (∀ v, IsStrictTotalOrder E (ep v)) ∧ IsStrictTotalOrder ι op := by
            simpa only [Game.RuleValid, hr] using hG.2
          have hfinE : ∀ r : ℕ, {i | G.entry i = r}.Finite := hG.1
          have hlen : ∀ (L : List E) n e, L[n]? = some e → n < L.length := fun L n e h =>
            (List.getElem?_eq_some_iff.mp h).1
          have hArr : ∀ (X : ι → List E), G.IsProfile X → ∀ h w i, i ≤ (X h).length →
              G.vtxAt (X h) i = some w → G.arrTime X h w = G.reach X h i := by
            intro X hX h w i hi hw
            apply le_antisymm
            · exact iInf₂_le i ⟨hi, hw⟩
            · refine le_iInf₂ fun k hk => ?_
              have := huniq (X h) G.d (hX h).1 i k w hi hk.1 hw hk.2
              subst this; exact le_rfl
          -- keys
          let key : List E → ℕ → ι → ι ⊕ E := fun P m c =>
            if m = 0 then Sum.inl c else (P[m-1]?).elim (Sum.inl c) Sum.inr
          let vx : ι ⊕ E → V := Sum.elim (fun _ => G.o) G.N.head
          let klt : V → ι ⊕ E → ι ⊕ E → Prop := fun v => Sum.Lex op (ep v)
          have key0 : ∀ P c, key P 0 c = Sum.inl c := fun P c => by simp [key]
          have keyS : ∀ (P : List E) m c e, P[m]? = some e → key P (m+1) c = Sum.inr e := fun P m c e h => by
            simp [key, h]
          have keyc : ∀ (P Q : List E) m c, P.take m = Q.take m → key P m c = key Q m c := by
            intro P Q m c h
            rcases m with _ | m
            · rw [key0, key0]
            · have : P[m]? = Q[m]? := by
                rw [← List.getElem?_take_of_lt (show m < m+1 by omega), h,
                  List.getElem?_take_of_lt (by omega)]
              simp [key, this]
          have hvkey : ∀ (P : List E) m c, m ≤ P.length → G.vtxAt P m = some (vx (key P m c)) := by
            intro P m c hm
            rcases m with _ | m
            · rw [key0]; simp [Game.vtxAt, vx]
            · have he : P[m]? = some (P[m]'(by omega)) := List.getElem?_eq_getElem (by omega)
              rw [keyS P m c _ he]; simp [Game.vtxAt, vx, he]
          have kltTri : ∀ v a b, klt v a b ∨ a = b ∨ klt v b a := by
            intro v a b
            haveI := hepO v
            rcases a with a | a <;> rcases b with b | b
            · rcases trichotomous_of op a b with h | h | h
              · exact Or.inl (Sum.Lex.inl h)
              · exact Or.inr (Or.inl (by rw [h]))
              · exact Or.inr (Or.inr (Sum.Lex.inl h))
            · exact Or.inl (Sum.Lex.sep _ _)
            · exact Or.inr (Or.inr (Sum.Lex.sep _ _))
            · rcases trichotomous_of (ep v) a b with h | h | h
              · exact Or.inl (Sum.Lex.inr h)
              · exact Or.inr (Or.inl (by rw [h]))
              · exact Or.inr (Or.inr (Sum.Lex.inr h))
          have kltTrans : ∀ v a b c, klt v a b → klt v b c → klt v a c := by
            intro v a b c h1 h2
            haveI := hepO v
            rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2
            · exact Sum.Lex.inl (_root_.trans h1 h2)
            · exact Sum.Lex.sep _ _
            · exact Sum.Lex.inr (_root_.trans h1 h2)
            · exact Sum.Lex.sep _ _
          have kltIrr : ∀ v a, ¬ klt v a a := by
            intro v a h
            haveI := hepO v
            rcases h with h | h | h
            · exact irrefl_of op _ h
            · exact irrefl_of (ep v) _ h
          -- weak order of tags
          let tle : V → ℕ → ι ⊕ E → ℕ → ι ⊕ E → Prop := fun v n k n' k' =>
            n < n' ∨ (n = n' ∧ (klt v k k' ∨ k = k'))
          have tleRefl : ∀ v n k, tle v n k n k := fun v n k => Or.inr ⟨rfl, Or.inr rfl⟩
          have tleTrans : ∀ v n k n' k' n'' k'', tle v n k n' k' → tle v n' k' n'' k'' →
              tle v n k n'' k'' := by
            intro v n k n' k' n'' k'' h1 h2
            rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
            · exact Or.inl (by omega)
            · exact Or.inl (by omega)
            · exact Or.inl (by omega)
            · refine Or.inr ⟨by omega, ?_⟩
              rcases h1' with h1' | rfl
              · rcases h2' with h2' | rfl
                · exact Or.inl (kltTrans _ _ _ _ h1' h2')
                · exact Or.inl h1'
              · exact h2'
          have tleAnti : ∀ v n k n' k', tle v n k n' k' → tle v n' k' n k → n = n' ∧ k = k' := by
            intro v n k n' k' h1 h2
            rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
            · omega
            · omega
            · omega
            · refine ⟨h1, ?_⟩
              rcases h1' with h1' | h1'
              · rcases h2' with h2' | h2'
                · exact absurd (kltTrans _ _ _ _ h1' h2') (kltIrr _ _)
                · exact h2'.symm
              · exact h1'
          have tleTot : ∀ v n k n' k', tle v n k n' k' ∨ tle v n' k' n k := by
            intro v n k n' k'
            rcases lt_trichotomy n n' with h | h | h
            · exact Or.inl (Or.inl h)
            · rcases kltTri v k k' with h' | h' | h'
              · exact Or.inl (Or.inr ⟨h, Or.inl h'⟩)
              · exact Or.inl (Or.inr ⟨h, Or.inr h'⟩)
              · exact Or.inr (Or.inr ⟨h.symm, Or.inl h'⟩)
            · exact Or.inr (Or.inl h)
          -- witnesses: unilateral deviations of later-batch agents
          let Wit : ι → List E → ℕ → ℕ → ι ⊕ E → Prop := fun l P m n k =>
            l ∉ H ∧ G.IsODPath P ∧ m ≤ P.length ∧ G.reach (deviate p l P) l m = (n : ℕ∞) ∧ key P m l = k
          let Dom : ℕ → ι ⊕ E → Prop := fun n k => ∃ l P m n' k', Wit l P m n' k' ∧ vx k' = vx k ∧
            tle (vx k) n' k' n k
          have domMono : ∀ n k n' k', Dom n k → vx k' = vx k → tle (vx k) n k n' k' → Dom n' k' := by
            rintro n k n' k' ⟨l, P, m, n0, k0, hW, hv, ht⟩ hv' ht'
            exact ⟨l, P, m, n0, k0, hW, hv.trans hv'.symm, by rw [hv']; exact tleTrans _ _ _ _ _ _ _ ht ht'⟩
          have domMin : ∀ n k, Dom n k → ∃ l P m n0 k0, Wit l P m n0 k0 ∧ vx k0 = vx k ∧
              ∀ n' k', vx k' = vx k → Dom n' k' → tle (vx k) n0 k0 n' k' := by
            rintro n k ⟨l, P, m, n1, k1, hW, hv, -⟩
            have hex : ∃ n, ∃ k', vx k' = vx k ∧ ∃ l P m, Wit l P m n k' := ⟨n1, k1, hv, l, P, m, hW⟩
            set n0 := Nat.find hex with hn0
            have hS := Nat.find_spec hex
            rw [← hn0] at hS
            let Ks : Set (ι ⊕ E) := {k' | vx k' = vx k ∧ ∃ l P m, Wit l P m n0 k'}
            have hKfin : Ks.Finite := by
              refine Set.Finite.subset (((hfinE n0).image Sum.inl).union
                (Set.finite_range (Sum.inr : E → ι ⊕ E))) ?_
              rintro k' ⟨-, l', P', m', hW'⟩
              rcases k' with c | e
              · left
                obtain ⟨-, -, hm', hre, hk⟩ := hW'
                rcases m' with _ | m'
                · rw [key0] at hk
                  have hlc : l' = c := by simpa using hk
                  subst hlc
                  simp only [Game.reach, if_true] at hre
                  exact ⟨l', by exact_mod_cast hre, rfl⟩
                · have he : P'[m']? = some (P'[m']'(by omega)) := List.getElem?_eq_getElem (by omega)
                  rw [keyS P' m' l' _ he] at hk
                  exact absurd hk (by simp)
              · right; exact ⟨e, rfl⟩
            have hKne : Ks.Nonempty := hS
            have hmin : ∀ (S : Set (ι ⊕ E)), S.Finite → S.Nonempty →
                ∃ a ∈ S, ∀ b ∈ S, klt (vx k) a b ∨ a = b := by
              intro S hSf
              refine Set.Finite.induction_on (motive := fun S _ => S.Nonempty →
                ∃ a ∈ S, ∀ b ∈ S, klt (vx k) a b ∨ a = b) S hSf ?_ ?_
              · intro h; exact absurd h Set.not_nonempty_empty
              · intro a S _ _ ih _
                by_cases hne : S.Nonempty
                · obtain ⟨b, hb, hbm⟩ := ih hne
                  rcases kltTri (vx k) a b with h | h | h
                  · refine ⟨a, Set.mem_insert _ _, ?_⟩
                    rintro c (rfl | hc)
                    · exact Or.inr rfl
                    · rcases hbm c hc with h' | rfl
                      · exact Or.inl (kltTrans _ _ _ _ h h')
                      · exact Or.inl h
                  · refine ⟨a, Set.mem_insert _ _, ?_⟩
                    rintro c (rfl | hc)
                    · exact Or.inr rfl
                    · rw [h]; exact hbm c hc
                  · refine ⟨b, Set.mem_insert_of_mem _ hb, ?_⟩
                    rintro c (rfl | hc)
                    · exact Or.inl h
                    · exact hbm c hc
                · refine ⟨a, Set.mem_insert _ _, ?_⟩
                  rintro c (rfl | hc)
                  · exact Or.inr rfl
                  · exact absurd ⟨c, hc⟩ hne
            obtain ⟨k0, ⟨hk0v, l0, P0, m0, hW0⟩, hk0m⟩ := hmin Ks hKfin hKne
            refine ⟨l0, P0, m0, n0, k0, hW0, hk0v, ?_⟩
            rintro n' k' hv' ⟨l2, P2, m2, n2, k2, hW2, hv2, ht2⟩
            rw [hv'] at ht2
            refine tleTrans _ _ _ n2 k2 _ _ ?_ ht2
            have hle : n0 ≤ n2 := Nat.find_le ⟨k2, hv2.trans hv', l2, P2, m2, hW2⟩
            rcases lt_or_eq_of_le hle with h | h
            · exact Or.inl h
            · refine Or.inr ⟨h, hk0m k2 ⟨hv2.trans hv', l2, P2, m2, ?_⟩⟩
              rw [h]; exact hW2
          -- tags of agents in a buffer
          have hposle : ∀ X t i, (G.state X t i).pos ≤ (X i).length := by
            intro X t i
            induction t with
            | zero => simp [Game.state]
            | succ t ih =>
              by_cases h : G.selected X t (G.state X t) i
              · rw [hsel X t i h]
                obtain ⟨-, e, he, -⟩ := h
                have := hlen _ _ _ he
                simpa using this
              · rw [hnsel X t i h]; exact ih
          have hvst : ∀ X, G.IsProfile X → ∀ c m e, (X c)[m]? = some e → vx (key (X c) m c) = G.N.tail e := by
            intro X hX c m e he
            have h1 := hvtx (X c) G.d (hX c).1 m e he
            rw [hvkey (X c) m c (le_of_lt (hlen _ _ _ he))] at h1
            simpa using h1
          have hpos0 : ∀ X, G.IsProfile X → ∀ c m e, (X c)[m]? = some e → (m = 0 ↔ G.N.tail e = G.o) := by
            intro X hX c m e he
            have h1 := hvtx (X c) G.d (hX c).1 m e he
            constructor
            · rintro rfl; simp [Game.vtxAt] at h1; exact h1.symm
            · intro h
              rw [h] at h1
              exact huniq (X c) G.d (hX c).1 m 0 G.o (le_of_lt (hlen _ _ _ he)) (Nat.zero_le _) h1
                (by simp [Game.vtxAt])
          have hbl : ∀ X, G.IsProfile X → ∀ i k a b e, (X i)[AState.pos a]? = some e →
              (X k)[AState.pos b]? = some e → (G.better X i a k b ↔ (a.since < b.since ∨
                (a.since = b.since ∧ klt (G.N.tail e) (key (X i) a.pos i) (key (X k) b.pos k)))) := by
            intro X hX i k a b e hi hk
            have h0i := hpos0 X hX i _ e hi
            have h0k := hpos0 X hX k _ e hk
            simp only [Game.better, hr]
            refine or_congr Iff.rfl (and_congr Iff.rfl ?_)
            by_cases ho : G.N.tail e = G.o
            · have ha := h0i.2 ho
              have hb := h0k.2 ho
              rw [ha, hb, key0, key0]
              simp [klt]
            · have ha : a.pos ≠ 0 := fun h => ho (h0i.1 h)
              have hb : b.pos ≠ 0 := fun h => ho (h0k.1 h)
              obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero ha
              obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero hb
              have hli := hlen _ _ _ hi
              have hlk := hlen _ _ _ hk
              have hei : (X i)[m]? = some ((X i)[m]'(by omega)) := List.getElem?_eq_getElem (by omega)
              have hek : (X k)[m']? = some ((X k)[m']'(by omega)) := List.getElem?_eq_getElem (by omega)
              have hhd : G.N.head ((X i)[m]'(by omega)) = G.N.tail e :=
                hconsec (X i) _ _ (hX i).1 m _ e hei (by rw [← Nat.succ_eq_add_one, ← hm]; exact hi)
              rw [hm, hm', Nat.succ_eq_add_one, Nat.succ_eq_add_one, keyS _ _ _ _ hei, keyS _ _ _ _ hek]
              simp only [Nat.add_sub_cancel, hei, hek]
              constructor
              · rintro (h | ⟨-, -, x, y, hx, hy, h⟩)
                · omega
                · simp only [Option.some.injEq] at hx hy
                  rw [← hx, ← hy, hhd] at h
                  exact Sum.Lex.inr h
              · intro h
                right
                refine ⟨by omega, by omega, _, _, rfl, rfl, ?_⟩
                rw [hhd]
                simpa [klt] using h
          have hhist : ∀ X t i, 0 < (G.state X t i).pos → ∃ r, r < t ∧ G.selected X r (G.state X r) i ∧
              (G.state X r i).pos + 1 = (G.state X t i).pos ∧ (G.state X t i).since = r + 1 := by
            intro X t i
            induction t with
            | zero => intro h; simp [Game.state] at h
            | succ t ih =>
              intro h
              by_cases hs : G.selected X t (G.state X t) i
              · refine ⟨t, by omega, hs, ?_, ?_⟩ <;> rw [hsel X t i hs]
              · rw [hnsel X t i hs] at h ⊢
                obtain ⟨r, h1, h2, h3, h4⟩ := ih h
                exact ⟨r, by omega, h2, h3, h4⟩
          -- two agents in the same buffer carry different tags
          have hdist : ∀ X, G.IsProfile X → ∀ s i k e, i ≠ k → (X i)[(G.state X s i).pos]? = some e →
              (X k)[(G.state X s k).pos]? = some e → (G.state X s i).since = (G.state X s k).since →
              key (X i) (G.state X s i).pos i = key (X k) (G.state X s k).pos k → False := by
            intro X hX s i k e hik hi hk hsn hke
            have h0i := hpos0 X hX i _ e hi
            have h0k := hpos0 X hX k _ e hk
            by_cases ho : G.N.tail e = G.o
            · rw [h0i.2 ho, h0k.2 ho, key0, key0] at hke
              exact hik (by simpa using hke)
            · have ha : (G.state X s i).pos ≠ 0 := fun h => ho (h0i.1 h)
              have hb : (G.state X s k).pos ≠ 0 := fun h => ho (h0k.1 h)
              obtain ⟨r, hr1, hr2, hr3, hr4⟩ := hhist X s i (by omega)
              obtain ⟨r', hr1', hr2', hr3', hr4'⟩ := hhist X s k (by omega)
              have : r' = r := by omega
              subst this
              obtain ⟨en1, e1, he1, hb1⟩ := hr2
              obtain ⟨en2, e2, he2, hb2⟩ := hr2'
              rw [← hr3, ← hr3', keyS _ _ _ _ he1, keyS _ _ _ _ he2] at hke
              have hee : e1 = e2 := by simpa using hke
              subst hee
              have b1 := (hbl X hX i k _ _ e1 he1 he2).1 (hb1 k hik.symm en2 he2)
              have b2 := (hbl X hX k i _ _ e1 he2 he1).1 (hb2 i hik en1 he1)
              rcases b1 with b1 | ⟨b1, b1'⟩ <;> rcases b2 with b2 | ⟨b2, b2'⟩
              · omega
              · omega
              · omega
              · exact kltIrr _ _ (kltTrans _ _ _ _ b1' b2')
          let D : (ι → List E) → ℕ → ι → Prop := fun Y t c =>
            Dom (G.state Y t c).since (key (Y c) (G.state Y t c).pos c)
          let Agree : (ι → List E) → Prop := fun Y => G.IsProfile Y ∧ ∀ i ∈ H, Y i = p i
          have hAgp : Agree p := ⟨hprof, fun _ _ => rfl⟩
          let J : ℕ → Prop := fun t => ∀ Y, Agree Y → (∀ c, c ∉ H → D Y t c) ∧
            (∀ h, h ∈ H → G.state Y t h = G.state p t h ∨ (D Y t h ∧ D p t h))
          have persist : ∀ t, J t → ∀ Y, Agree Y → ∀ c, D Y t c → D Y (t+1) c := by
            intro t hJ Y hY c hD
            by_cases hs : G.selected Y t (G.state Y t) c
            swap
            · show Dom _ _; rw [hnsel Y t c hs]; exact hD
            obtain ⟨hen, e, he, hall⟩ := hs
            have hsc := hsel Y t c ⟨hen, e, he, hall⟩
            have hvc : vx (key (Y c) (G.state Y t c).pos c) = G.N.tail e := hvst Y hY.1 c _ e he
            obtain ⟨l, Pw, i, n0, k0, hW, hv0, hmin⟩ := domMin _ _ hD
            rw [hvc] at hv0 hmin
            obtain ⟨hl, hPw, hi, hre, hk0⟩ := hW
            have hwc := hmin _ _ hvc hD
            set m := (G.state Y t c).pos with hm
            have hmlt := hlen _ _ _ he
            set P := Pw.take i ++ (Y c).drop m with hP
            have htk : (Pw.take i).length = i := by simp; omega
            have hPwv : G.vtxAt Pw i = some (G.N.tail e) := by
              rw [hvkey Pw i l hi, hk0, hv0]
            have hPOD : G.IsODPath P := by
              refine ⟨?_, ?_⟩
              · rw [hpath_app]
                exact ⟨_, (hsplit Pw G.d hPw.1 i _ hi hPwv).1,
                  (hsplit (Y c) G.d (hY.1 c).1 m _ (by omega) (hvtx (Y c) G.d (hY.1 c).1 m e he)).2⟩
              · intro h; rw [hP, List.append_eq_nil_iff] at h
                have := congrArg List.length h.2; simp at this; omega
            have hdPw : deviate p l Pw l = Pw := by unfold deviate; simp
            set A := deviate p l P with hAdef
            have hAl : A l = P := by simp [A, deviate]
            have hAc : ∀ c, c ≠ l → A c = p c := fun c hc => by
              simp [A, deviate, Function.update_of_ne hc]
            have hPtk : P.take i = Pw.take i := List.take_left' htk
            have hreachA : G.reach A l i = (n0 : ℕ∞) := by
              rw [← hre]; apply hcaus_reach
              · intro c hc; simp [A, deviate, Function.update_of_ne hc]
              · rw [hAl, hdPw, hPtk]
            have hkeyA : key P i l = k0 := by rw [← hk0]; exact keyc _ _ _ _ hPtk
            have hPi : P[i]? = some e := by
              rw [hP, List.getElem?_append_right (by omega), htk]; simp [he]
            have hlenP := hlen _ _ _ hPi
            have hAprof : G.IsProfile A := fun c => by
              by_cases hc : c = l
              · subst hc; rw [hAl]; exact hPOD
              · rw [hAc c hc]; exact hprof c
            have hAgA : Agree A := ⟨hAprof, fun c hc => hAc c (fun h => hl (h ▸ hc))⟩
            have hscle : (G.state Y t c).since ≤ t := by have := (hsince_bd Y t c).2; omega
            have hn0t : n0 ≤ t := by rcases hwc with h | ⟨h, -⟩ <;> omega
            have hent_l : G.entry l ≤ t := by
              have hri : G.reach A l i ≤ (t : ℕ∞) := by rw [hreachA]; exact_mod_cast hn0t
              have := hreach_le A l i t hri
              rcases Nat.eq_zero_or_pos i with h0 | h0
              · rw [h0] at hreachA
                simp only [Game.reach, if_true] at hreachA
                have : G.entry l = n0 := by exact_mod_cast hreachA
                omega
              · obtain ⟨r, hr1, hr2, -, -⟩ := hhist A t l (by omega)
                have := hr2.1; omega
            -- key claim
            have hlv : G.leave A l i ≤ (t : ℕ∞) := by
              by_contra hgt
              have hri : G.reach A l i ≤ (t : ℕ∞) := by rw [hreachA]; exact_mod_cast hn0t
              have hposA := hpos_eq A l i t hri hgt
              have hsinceA : (G.state A t l).since = n0 := by
                have := hsince A t l
                rw [hposA, hreachA] at this
                exact_mod_cast this
              have hAle : (A l)[(G.state A t l).pos]? = some e := by rw [hposA, hAl, hPi]
              have hn2 : ¬ ∀ c', c' ≠ l → G.entry c' ≤ t → (A c')[(G.state A t c').pos]? = some e →
                  G.better A l (G.state A t l) c' (G.state A t c') := fun hh =>
                hgt (by rw [← hposA, hleave_eq A l t ⟨hent_l, e, hAle, hh⟩])
              push Not at hn2
              obtain ⟨c', hcl, henc, hce, hnb⟩ := hn2
              rw [hbl A hAprof l c' _ _ e hAle hce, hsinceA, hposA, hAl, hkeyA] at hnb
              have hvc' : vx (key (A c') (G.state A t c').pos c') = G.N.tail e := hvst A hAprof c' _ e hce
              have hnle : ¬ tle (G.N.tail e) n0 k0 (G.state A t c').since
                  (key (A c') (G.state A t c').pos c') := by
                rintro (h | ⟨h, h' | h'⟩)
                · exact hnb (Or.inl h)
                · exact hnb (Or.inr ⟨h, h'⟩)
                · refine hdist A hAprof t l c' e hcl.symm hAle hce (by rw [hsinceA, h]) ?_
                  rw [hposA, hAl, hkeyA, h']
              have hnD : ¬ D A t c' := fun h => hnle (hmin _ _ hvc' h)
              have hc'H : c' ∈ H := by
                by_contra hc'
                exact hnD ((hJ A hAgA).1 c' hc')
              have hA1 : G.state A t c' = G.state p t c' := by
                rcases (hJ A hAgA).2 c' hc'H with h | h
                · exact h
                · exact absurd h.1 hnD
              have hAp : A c' = p c' := hAc c' hcl
              have hY1 : G.state Y t c' = G.state p t c' := by
                rcases (hJ Y hY).2 c' hc'H with h | h
                · exact h
                · refine absurd ?_ hnD
                  show Dom _ _
                  rw [hA1, hAp]; exact h.2
              have hYp : Y c' = p c' := hY.2 c' hc'H
              rw [hA1, hAp] at hnle hce
              by_cases hcc : c' = c
              · subst hcc
                apply hnle
                rw [← hY1, ← hYp]
                exact hwc
              · have hcY : (Y c')[(G.state Y t c').pos]? = some e := by rw [hYp, hY1]; exact hce
                have hb := hall c' hcc henc hcY
                rw [hbl Y hY.1 c c' _ _ e he hcY, hYp, hY1] at hb
                apply hnle
                refine tleTrans _ _ _ _ _ _ _ hwc ?_
                rcases hb with h | ⟨h, h'⟩
                · exact Or.inl h
                · exact Or.inr ⟨h, Or.inl h'⟩
            show Dom _ _
            rw [hsc, keyS (Y c) _ c e he]
            obtain ⟨s, hs⟩ : ∃ s : ℕ, G.leave A l i = (s : ℕ∞) := by
              cases hl : G.leave A l i with
              | top => rw [hl] at hlv; simp at hlv
              | coe a => exact ⟨a, rfl⟩
            have hst : s ≤ t := by rw [hs] at hlv; exact_mod_cast hlv
            refine ⟨l, P, i+1, s+1, Sum.inr e, ⟨hl, hPOD, by omega, ?_, keyS P i l e hPi⟩, rfl, ?_⟩
            · simp only [Game.reach, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
              rw [← hAdef, hs]; push_cast; rfl
            · rcases lt_or_eq_of_le hst with h | h
              · exact Or.inl (by simpa using h)
              · exact Or.inr ⟨by simp [h], Or.inr rfl⟩
          have hJall : ∀ t, J t := by
            intro t
            induction t with
            | zero =>
              intro Y hY
              refine ⟨fun c hc => ?_, fun h _ => Or.inl rfl⟩
              show Dom _ _
              simp only [Game.state]
              rw [key0]
              refine ⟨c, p c, 0, G.entry c, Sum.inl c, ⟨hc, hprof c, Nat.zero_le _, ?_, key0 _ _⟩, rfl,
                tleRefl _ _ _⟩
              simp [Game.reach]
            | succ t hJ =>
              intro Y hY
              refine ⟨fun c hc => persist t hJ Y hY c ((hJ Y hY).1 c hc), fun h hh => ?_⟩
              rcases (hJ Y hY).2 h hh with heq | hd
              swap
              · exact Or.inr ⟨persist t hJ Y hY h hd.1, persist t hJ p hAgp h hd.2⟩
              by_cases hD : D Y t h
              · refine Or.inr ⟨persist t hJ Y hY h hD, persist t hJ p hAgp h ?_⟩
                show Dom _ _
                rw [← heq, ← hY.2 h hh]; exact hD
              left
              have one : ∀ Y1 Y2, Agree Y1 → Agree Y2 →
                  (∀ c ∈ H, G.state Y1 t c = G.state Y2 t c ∨ D Y2 t c) →
                  G.state Y1 t h = G.state Y2 t h → ¬ D Y2 t h →
                  G.selected Y1 t (G.state Y1 t) h → G.selected Y2 t (G.state Y2 t) h := by
                intro Y1 Y2 h1 h2 hst hsh hnD hsl
                obtain ⟨hen, e, he, hall⟩ := hsl
                have hY12 : ∀ c ∈ H, Y1 c = Y2 c := fun c hc => (h1.2 c hc).trans (h2.2 c hc).symm
                have he2 : (Y2 h)[(G.state Y2 t h).pos]? = some e := by rw [← hY12 h hh, ← hsh]; exact he
                refine ⟨hen, e, he2, fun k hk henk hke => ?_⟩
                by_contra hnb
                rw [hbl Y2 h2.1 h k _ _ e he2 hke] at hnb
                have hvh : vx (key (Y2 h) (G.state Y2 t h).pos h) = G.N.tail e := hvst Y2 h2.1 h _ e he2
                have hvk : vx (key (Y2 k) (G.state Y2 t k).pos k) = G.N.tail e := hvst Y2 h2.1 k _ e hke
                have hle : tle (G.N.tail e) (G.state Y2 t k).since (key (Y2 k) (G.state Y2 t k).pos k)
                    (G.state Y2 t h).since (key (Y2 h) (G.state Y2 t h).pos h) := by
                  rcases tleTot (G.N.tail e) (G.state Y2 t k).since (key (Y2 k) (G.state Y2 t k).pos k)
                    (G.state Y2 t h).since (key (Y2 h) (G.state Y2 t h).pos h) with h' | h'
                  · exact h'
                  · rcases h' with h' | ⟨h', h'' | h''⟩
                    · exact absurd (Or.inl h') hnb
                    · exact absurd (Or.inr ⟨h', h''⟩) hnb
                    · exact Or.inr ⟨h'.symm, Or.inr h''.symm⟩
                have hnDk : ¬ D Y2 t k := fun hDk =>
                  hnD (domMono _ _ _ _ hDk (hvh.trans hvk.symm) (by rw [hvk]; exact hle))
                have hkH : k ∈ H := by
                  by_contra hkH
                  exact hnDk ((hJ Y2 h2).1 k hkH)
                have hsk : G.state Y1 t k = G.state Y2 t k := (hst k hkH).resolve_right hnDk
                have hb := hall k hk henk (by rw [hY12 k hkH, hsk]; exact hke)
                rw [hbl Y1 h1.1 h k _ _ e he (by rw [hY12 k hkH, hsk]; exact hke), hY12 k hkH, hsk,
                  hY12 h hh, hsh] at hb
                exact hnb hb
              have hDp : ¬ D p t h := by
                intro hD'
                apply hD
                show Dom _ _
                rw [heq, hY.2 h hh]; exact hD'
              have hiff : G.selected Y t (G.state Y t) h ↔ G.selected p t (G.state p t) h := by
                constructor
                · exact one Y p hY hAgp (fun c hc => ((hJ Y hY).2 c hc).imp id And.right) heq hDp
                · exact one p Y hAgp hY (fun c hc => ((hJ Y hY).2 c hc).imp Eq.symm And.left) heq.symm hD
              by_cases hs : G.selected p t (G.state p t) h
              · rw [hsel _ _ _ hs, hsel _ _ _ (hiff.2 hs), heq]
              · rw [hnsel _ _ _ hs, hnsel _ _ _ (fun h' => hs (hiff.1 h')), heq]
          -- batch agents are never dominated
          have hlast : ∀ i, G.vtxAt (p i) (p i).length = some G.d := by
            intro i
            obtain ⟨hP, hne⟩ := hprof i
            have hl : 0 < (p i).length := List.length_pos_iff.2 hne
            have he : (p i)[(p i).length - 1]? = some ((p i)[(p i).length - 1]'(by omega)) :=
              List.getElem?_eq_getElem (by omega)
            have := hend (p i) G.o G.d hP ((p i).length - 1) _ he (by omega)
            unfold Game.vtxAt
            rw [if_neg (by omega), he, Option.map_some, this]
          have hHpos : ∀ i ∈ H, (G.state p T i).pos = (p i).length := by
            intro i hi
            have h1 : G.arrTime p i G.d ≤ (T : ℕ∞) := hi
            rw [hArr p hprof i G.d _ le_rfl (hlast i)] at h1
            exact le_antisymm (hposle _ _ _) (hreach_le p i _ T h1)
          have hnDp : ∀ h ∈ H, ∀ t, ¬ D p t h := by
            intro h hh t hD
            have hfw : ∀ t', t ≤ t' → D p t' h := by
              intro t' htt
              induction t', htt using Nat.le_induction with
              | base => exact hD
              | succ n _ ih => exact persist n (hJall n) p hAgp h ih
            have hDT := hfw (max t T) (le_max_left _ _)
            have hpl : (G.state p (max t T) h).pos = (p h).length :=
              le_antisymm (hposle _ _ _) ((hHpos h hh) ▸ hmono p h T _ (le_max_right _ _))
            have hsn : ((G.state p (max t T) h).since : ℕ∞) ≤ (T : ℕ∞) := by
              rw [hsince, hpl, ← hArr p hprof h G.d _ le_rfl (hlast h)]; exact hh
            obtain ⟨l, P, m, n', k', ⟨hl, hP, hm, hre, hk⟩, hv, ht⟩ := hDT
            have hvd : vx (key (p h) (G.state p (max t T) h).pos h) = G.d := by
              have := hvkey (p h) (p h).length h le_rfl
              rw [hlast h] at this
              rw [hpl]; simpa using this.symm
            rw [hvd] at hv
            have hPd : G.vtxAt P m = some G.d := by rw [hvkey P m l hm, hk, hv]
            have hdl : deviate p l P l = P := by unfold deviate; simp
            have h1 : G.arrTime (deviate p l P) l G.d ≤ (n' : ℕ∞) := by
              rw [← hre]; exact iInf₂_le m ⟨by rw [hdl]; exact hm, by rw [hdl]; exact hPd⟩
            have h2 : n' ≤ (G.state p (max t T) h).since := by
              rcases ht with h | ⟨h, -⟩ <;> omega
            apply hl
            show G.arrTime p l G.d ≤ (T : ℕ∞)
            exact (hNE.2 l P hP).trans (h1.trans ((Nat.cast_le.2 h2).trans hsn))
          have hstate : ∀ Y, Agree Y → ∀ h ∈ H, ∀ t, G.state Y t h = G.state p t h := by
            intro Y hY h hh t
            rcases (hJall t Y hY).2 h hh with h' | h'
            · exact h'
            · exact absurd h'.2 (hnDp h hh t)
          have hhit : ∀ X i t m, m ≤ (G.state X t i).pos → ∃ t', (G.state X t' i).pos = m := by
            intro X i t
            induction t with
            | zero => intro m hm; exact ⟨0, by simp [Game.state] at hm ⊢; omega⟩
            | succ t ih =>
              intro m hm
              by_cases h : m ≤ (G.state X t i).pos
              · exact ih m h
              · exact ⟨t+1, by have := (hpos1 X t i).2; omega⟩
          intro q hq hqp
          have hqA : Agree q := ⟨hq, hqp⟩
          refine ⟨?_, ?_⟩
          swap
          · intro i hi v
            simp only [Game.arrTime, Game.reach, Game.leave, hstate q hqA i hi, hqp i hi]
          intro i hi j hj v hiv hjv
          obtain ⟨ki, hki, hvi⟩ := hiv
          obtain ⟨kj, hkj, hvj⟩ := hjv
          have hij : i ≠ j := fun h => hj (h ▸ hi)
          have hai := hArr q hq i v ki hki hvi
          have haj := hArr q hq j v kj hkj hvj
          obtain ⟨ti, hti⟩ : ∃ t', (G.state q t' i).pos = ki := by
            apply hhit q i T
            rw [hstate q hqA i hi T, hHpos i hi, ← hqp i hi]; exact hki
          have hri : G.reach q i ki = ((G.state q ti i).since : ℕ∞) := by rw [hsince, hti]
          have hni : ¬ D q ti i := by
            intro hD
            apply hnDp i hi ti
            show Dom _ _
            rw [← hstate q hqA i hi ti, ← hqp i hi]; exact hD
          refine ⟨⟨ki, hki, hvi⟩, ⟨kj, hkj, hvj⟩, ?_⟩
          by_contra hnot
          push Not at hnot
          obtain ⟨hn1, hn2⟩ := hnot
          simp only [hr] at hn2
          rw [hai, haj, hri] at hn1 hn2
          obtain ⟨sj, hsj⟩ : ∃ s : ℕ, G.reach q j kj = (s : ℕ∞) := by
            cases hl : G.reach q j kj with
            | top => rw [hl] at hn1; simp at hn1
            | coe a => exact ⟨a, rfl⟩
          obtain ⟨tj, htj⟩ : ∃ t', (G.state q t' j).pos = kj :=
            hhit q j sj kj (hreach_le q j kj sj (by rw [hsj]))
          have hrj : G.reach q j kj = ((G.state q tj j).since : ℕ∞) := by rw [hsince, htj]
          rw [hrj] at hn1 hn2
          have hDj : D q tj j := (hJall tj q hqA).1 j hj
          have hki' : vx (key (q i) ki i) = v := by
            have := hvkey (q i) ki i hki
            rw [hvi] at this; simpa using this.symm
          have hkj' : vx (key (q j) kj j) = v := by
            have := hvkey (q j) kj j hkj
            rw [hvj] at this; simpa using this.symm
          apply hni
          show Dom _ _
          refine domMono _ _ _ _ hDj (by rw [hti, htj, hki', hkj']) ?_
          rw [hti, htj, hkj']
          have hn1' : (G.state q tj j).since ≤ (G.state q ti i).since := by exact_mod_cast hn1
          rcases lt_or_eq_of_le hn1' with hlt | heq
          · exact Or.inl hlt
          refine Or.inr ⟨heq, ?_⟩
          have hn2' := hn2 (by rw [heq])
          rcases kltTri v (key (q j) kj j) (key (q i) ki i) with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          exfalso
          by_cases hvo : v = G.o
          · have e1 : ki = 0 := huniq (q i) G.d (hq i).1 ki 0 v hki (Nat.zero_le _) hvi
              (by simp [Game.vtxAt, hvo])
            have e2 : kj = 0 := huniq (q j) G.d (hq j).1 kj 0 v hkj (Nat.zero_le _) hvj
              (by simp [Game.vtxAt, hvo])
            rw [e1, e2, key0, key0] at h
            exact hn2' (Or.inr ⟨hvo, by simpa [klt] using h⟩)
          · have e1 : ki ≠ 0 := by rintro rfl; simp [Game.vtxAt] at hvi; exact hvo hvi.symm
            have e2 : kj ≠ 0 := by rintro rfl; simp [Game.vtxAt] at hvj; exact hvo hvj.symm
            obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero e1
            obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero e2
            have hei : (q i)[m]? = some ((q i)[m]'(by omega)) := List.getElem?_eq_getElem (by omega)
            have hej : (q j)[m']? = some ((q j)[m']'(by omega)) := List.getElem?_eq_getElem (by omega)
            rw [keyS _ _ _ _ hei, keyS _ _ _ _ hej] at h
            rw [keyS _ _ _ _ hei] at hki'
            rw [keyS _ _ _ _ hej] at hkj'
            refine hn2' (Or.inl ⟨hvo, _, _, ⟨List.getElem_mem _, hki'⟩, ⟨List.getElem_mem _, hkj'⟩, ?_⟩)
            simpa [klt] using h
        have core : ∀ (T : ℕ) (q : ι → List E), G.IsProfile q → (∀ i ∈ G.batchesUpTo p T, q i = p i) →
            (∀ i ∈ G.batchesUpTo p T, ∀ j ∉ G.batchesUpTo p T, ∀ v,
                G.passes q i v → G.passes q j v → G.preempts q i j v) ∧
            (∀ i ∈ G.batchesUpTo p T, ∀ v, G.arrTime q i v = G.arrTime p i v) := by
          rcases hr : G.rule with hpr | hpr | ⟨ep, op⟩
          · exact core12 hpr (Or.inl hr) (by unfold Game.IsEquilibrium at hp; rw [hr] at hp; exact hp)
          · exact core12 hpr (Or.inr hr) (by unfold Game.IsEquilibrium at hp; rw [hr] at hp; exact hp)
          · exact core3 ep op hr (by unfold Game.IsEquilibrium at hp; rw [hr] at hp; exact hp)
        refine ⟨?_, core⟩
        intro i j v hpre
        by_contra hlt
        push Not at hlt
        have hfin : G.arrTime p j G.d ≠ ⊤ := ne_top_of_lt hlt
        obtain ⟨T, hT⟩ := ENat.ne_top_iff_exists.1 hfin
        have hj : j ∈ G.batchesUpTo p T := by
          show G.arrTime p j G.d ≤ (T : ℕ∞); rw [hT]
        have hi : i ∉ G.batchesUpTo p T := by
          intro hi
          have : G.arrTime p i G.d ≤ (T : ℕ∞) := hi
          rw [hT] at this
          exact absurd hlt (not_lt.2 this)
        have h2 := (core T p hprof (fun _ _ => rfl)).1 j hj i hi v hpre.2.1 hpre.1
        exact asymm p hprof i j v hpre h2
