-- Prove2me | solution 1 for AtomicDynRouting.ResidenceTime.Supplement.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:17:37.02737+00:00
-- url     : https://prove2.me/submissions/ef802d20-0770-4835-94af-31383ed4615f

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Supplement_Equilibrium

open AtomicDynRouting
open AtomicDynRouting.ResidenceTime
open AtomicDynRouting.ResidenceTime.Supplement

open AtomicDynRouting.ResidenceTime

theorem solution {ι V E : Type} [Fintype V] [Fintype E] (G : Game ι V E) (hN : G.N.Acyclic) (hG : G.Standing) (hp : ι → ι → Prop) (hrule : G.rule = .r1 hp ∨ G.rule = .r2 hp) (p : ι → List E) (hpU : G.IsUFR p) :
    (∀ i j, hp i j → ∀ v, ¬ G.preempts p j i v) ∧
    (∀ l : ι, ∃ P : List E, G.IsODPath P ∧
      ∀ q : ι → List E, G.IsProfile q → (∀ k, hp k l → q k = p k) → q l = P →
        ∀ j, hp l j → ∀ v, ¬ G.preempts q j l v) := by
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
              push_neg at hlt
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
                  push_neg at this
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
          have hbet : ∀ (Y1 Y2 : ι → List E) a b c d, G.better Y1 a b c d ↔ G.better Y2 a b c d := by
            intro Y1 Y2 a b c d
            rcases hrule with hr | hr <;> simp [Game.better, hr]
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
              have hiff : ∀ c, G.selected Y1 t (G.state Y1 t) c ↔ G.selected Y2 t (G.state Y2 t) c := by
                intro c
                rw [← ih']
                simp only [Game.selected, hlook, hbet Y1 Y2]
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
                · intro h; by_contra h'; push_neg at h'
                  have := key Y2 Y1 (fun c hc => (hY c hc).symm) hT.symm t h'; omega
                · intro h; by_contra h'; push_neg at h'
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
                by_contra hlt; push_neg at hlt
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
              push_neg at hn2
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
                    by_contra h'; push_neg at h'; apply hnb
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
          refine ⟨fun i j hij v => h2 i p hpU.1 (fun _ _ => rfl) rfl j hij v, fun l => ⟨p l, hpU.1 l, ?_⟩⟩
          intro q hq hH hql j hlj v
          exact h2 l q hq hH hql j hlj v
