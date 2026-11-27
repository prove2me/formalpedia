-- Prove2me | solution 1 for AssortOpt.HMF.Supplement.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:36:32.656929+00:00
-- url     : https://prove2.me/submissions/c4d5e843-c502-40c3-9068-efa8a0c02368

import Mathlib
import Definitions.Def_AssortOpt_HMF_Supplement_MarkovModel

open AssortOpt
open AssortOpt.HMF
open AssortOpt.HMF.Supplement

theorem solution {n : ℕ} (C : MarkovModel n) :
    HasHistoryMonotoneFutures (inducedDist C) := by
      classical
      -- list facts about first visits
      have hmem : ∀ (l : List (Fin n)) x, x ∈ (firstVisits l).val ↔ x ∈ l := by
        intro l x; simp [firstVisits]
      have hnd : ∀ (l : List (Fin n)), (firstVisits l).val.Nodup := fun l => (firstVisits l).property
      have hsnoc : ∀ (l : List (Fin n)) a, (firstVisits (l ++ [a])).val =
          if a ∈ l then (firstVisits l).val else (firstVisits l).val ++ [a] := by
        intro l a
        by_cases h : a ∈ l
        · have h' : a ∈ l.reverse := List.mem_reverse.mpr h
          simp [firstVisits, List.reverse_append, List.dedup_cons_of_mem h', h]
        · have h' : a ∉ l.reverse := by simpa using h
          simp [firstVisits, List.reverse_append, List.dedup_cons_of_notMem h', h]
      have hpre : ∀ (a b : List (Fin n)), (firstVisits a).val <+: (firstVisits (a ++ b)).val := by
        intro a b
        induction b using List.reverseRecOn with
        | nil => simp
        | append_singleton b x ih =>
          rw [← List.append_assoc, hsnoc]
          split_ifs
          · exact ih
          · exact ih.trans (List.prefix_append _ _)
      have hfind : ∀ (q : Fin n → Bool) (w : List (Fin n)),
          (firstVisits w).val.find? q = w.find? q := by
        intro q w
        induction w using List.reverseRecOn with
        | nil => simp [firstVisits]
        | append_singleton l a ih =>
          rw [hsnoc]
          split_ifs with h
          · rw [ih, List.find?_append]
            cases hl : l.find? q with
            | some x => simp
            | none =>
              rw [List.find?_eq_none] at hl
              have := hl a h
              simp [this]
          · rw [List.find?_append, ih, List.find?_append]
      have hPL : ∀ (L p ys : List (Fin n)) (e : Fin n), L.Nodup → p <+: L → p = ys ++ [e] →
          p = L.take (L.idxOf e + 1) := by
        intro L p ys e hL hp hpe
        obtain ⟨zs, rfl⟩ := hp
        subst hpe
        have hne : e ∉ ys := by
          intro h
          have := hL
          rw [List.append_assoc, List.nodup_append] at this
          exact this.2.2 e h e (by simp) rfl
        rw [List.append_assoc, List.idxOf_append_of_notMem hne]
        rw [show ys ++ ([e] ++ zs) = (ys ++ [e]) ++ zs by simp, List.take_left' (by simp)]
      have hKL : ∀ (ρ ys u v : List (Fin n)) (e : Fin n), ρ = ys ++ [e] → e ∉ u →
          (ρ <+: (firstVisits (u ++ e :: v)).val ↔ ρ = (firstVisits (u ++ [e])).val) := by
        intro ρ ys u v e hρ hu
        have hq : (firstVisits (u ++ [e])).val = (firstVisits u).val ++ [e] := by
          rw [hsnoc]; simp [hu]
        have hqL : (firstVisits (u ++ [e])).val <+: (firstVisits (u ++ e :: v)).val := by
          have := hpre (u ++ [e]) v
          simpa using this
        constructor
        · intro h
          rw [hPL _ _ _ e (hnd _) h hρ, hPL _ _ _ e (hnd _) hqL hq]
        · intro h; rw [h]; exact hqL

      have hsupp : (inducedDist C).supp =
          (allReports n).filter (fun ℓ => 0 < reportProb (listLaw C) ℓ) := rfl
      have hp : (inducedDist C).p = reportProb (listLaw C) := rfl
      have hsumQ : ∀ (Q : List (Fin n) → Prop) [DecidablePred Q],
          ∑ ℓ ∈ (inducedDist C).supp with Q ℓ, (inducedDist C).p ℓ =
            (∑' w, if Q (firstVisits w).val then C.walks w else 0).toReal := by
        intro Q _
        rw [hsupp, hp, Finset.filter_filter]
        have hnn : ∀ ℓ, 0 ≤ reportProb (listLaw C) ℓ := by
          intro ℓ; unfold reportProb; split <;> positivity
        have h1 : ∑ ℓ ∈ (allReports n).filter (fun ℓ => 0 < reportProb (listLaw C) ℓ ∧ Q ℓ),
            reportProb (listLaw C) ℓ = ∑ ℓ ∈ (allReports n).filter Q, reportProb (listLaw C) ℓ := by
          apply Finset.sum_subset
          · intro ℓ hℓ
            simp only [Finset.mem_filter] at hℓ ⊢
            exact ⟨hℓ.1, hℓ.2.2⟩
          · intro ℓ hℓ h
            simp only [Finset.mem_filter, not_and] at hℓ h
            exact le_antisymm (le_of_not_gt (fun hh => h hℓ.1 hh hℓ.2)) (hnn ℓ)
        rw [h1]
        unfold allReports
        rw [Finset.filter_image, Finset.sum_image (fun a _ b _ h => Subtype.ext h)]
        have h2 : ∀ a : Report n, reportProb (listLaw C) a.val = (listLaw C a).toReal := by
          intro a; simp [reportProb, a.property]
        simp_rw [h2]
        rw [← ENNReal.toReal_sum (fun a _ => (listLaw C).apply_ne_top a)]
        congr 1
        have h3 : ∑ a ∈ Finset.univ.filter (fun a : Report n => Q a.val), listLaw C a =
            (listLaw C).toOuterMeasure {a | Q a.val} := by
          rw [PMF.toOuterMeasure_apply, tsum_fintype, Finset.sum_filter]
          congr 1; funext a; simp [Set.indicator_apply]
        rw [h3, listLaw, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply]
        congr 1; funext w; simp [Set.indicator_apply]

      have hct : ∀ (e : Fin n) (u : List (Fin n)) (a : Fin n), ∃ c : ℝ, 0 ≤ c ∧
          ∀ v, walkTail C.chain a (u ++ e :: v) = c * walkTail C.chain e v := by
        intro e u
        induction u with
        | nil => intro a; exact ⟨C.chain.P (some a) (some e), C.chain.nonneg _ _, fun v => rfl⟩
        | cons b u ih =>
          intro a
          obtain ⟨c, hc0, hc⟩ := ih b
          refine ⟨C.chain.P (some a) (some b) * c, mul_nonneg (C.chain.nonneg _ _) hc0, ?_⟩
          intro v
          show C.chain.P (some a) (some b) * walkTail C.chain b (u ++ e :: v) = _
          rw [hc, mul_assoc]
      have hc : ∀ (e : Fin n) (u : List (Fin n)), ∃ c : ℝ, 0 ≤ c ∧
          ∀ v, walkWeight C.chain C.initial (u ++ e :: v) = c * walkTail C.chain e v := by
        intro e u
        cases u with
        | nil => exact ⟨C.initial (some e), C.initial_nonneg _, fun v => rfl⟩
        | cons a u =>
          obtain ⟨c, hc0, hc⟩ := hct e u a
          refine ⟨C.initial (some a) * c, mul_nonneg (C.initial_nonneg _) hc0, ?_⟩
          intro v
          show C.initial (some a) * walkTail C.chain a (u ++ e :: v) = _
          rw [hc, mul_assoc]
      choose c hc0 hcv using hc
      have hdec : ∀ (e : Fin n) (F : List (Fin n) → ENNReal), (∀ w, F w ≠ 0 → e ∈ w) →
          ∑' w, F w = ∑' (p : {u : List (Fin n) // e ∉ u} × List (Fin n)), F (p.1.1 ++ e :: p.2) := by
        intro e F hF
        symm
        apply Function.Injective.tsum_eq (g := fun p : {u : List (Fin n) // e ∉ u} × List (Fin n) =>
          p.1.1 ++ e :: p.2)
        · rintro ⟨⟨u1, h1⟩, v1⟩ ⟨⟨u2, h2⟩, v2⟩ h
          simp only at h
          have hl : u1.length = u2.length := by
            have := congrArg (List.idxOf e) h
            rw [List.idxOf_append_of_notMem h1, List.idxOf_append_of_notMem h2] at this
            simpa [List.idxOf_cons_self] using this
          obtain ⟨hu, hv⟩ := List.append_inj h hl
          subst hu
          simp at hv
          subst hv
          rfl
        · intro w hw
          have he := hF w hw
          obtain ⟨x, hx⟩ : ∃ x, w.find? (· == e) = some x :=
            Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨e, he, by simp⟩)
          obtain ⟨hxe, as, bs, rfl, has⟩ := List.find?_eq_some_iff_append.mp hx
          have hxe' : x = e := by simpa using hxe
          subst hxe'
          refine ⟨⟨⟨as, fun h => by simpa using has x h⟩, bs⟩, rfl⟩

      have hM : ∀ ρ ∈ prefixes (inducedDist C), ∀ (e : Fin n) (ys : List (Fin n)), ρ = ys ++ [e] →
          ∀ S : Finset (Fin n), Disjoint S ρ.toFinset → ∀ j,
          condChoiceProb (inducedDist C) S j ρ =
            (∑' v, if Chooses S v j then ENNReal.ofReal (walkTail C.chain e v) else 0).toReal /
            (∑' v, ENNReal.ofReal (walkTail C.chain e v)).toReal := by
        intro ρ hρmem e ys hρ S hS j
        have hpos : 0 < prefProb (inducedDist C) ρ := by
          unfold prefixes at hρmem
          simp only [Finset.mem_filter, Finset.mem_biUnion, List.mem_toFinset, List.mem_inits] at hρmem
          obtain ⟨⟨ℓ, hℓ, hpl⟩, _⟩ := hρmem
          unfold prefProb
          refine lt_of_lt_of_le ((inducedDist C).pos ℓ hℓ) ?_
          apply Finset.single_le_sum (f := (inducedDist C).p)
          · intro i hi
            exact le_of_lt ((inducedDist C).pos i (Finset.mem_filter.mp hi).1)
          · exact Finset.mem_filter.mpr ⟨hℓ, hpl⟩
        have heρ : e ∈ ρ := by simp [hρ]
        set X : ENNReal := ∑' u : {u : List (Fin n) // e ∉ u},
          if ρ = (firstVisits (u.1 ++ [e])).val then ENNReal.ofReal (c e u.1) else 0 with hX
        have hT : (∑' w, if ρ <+: (firstVisits w).val then C.walks w else 0) =
            X * ∑' v, ENNReal.ofReal (walkTail C.chain e v) := by
          rw [hdec e]
          · rw [ENNReal.tsum_prod (f := fun (a : {u : List (Fin n) // e ∉ u}) b =>
              if ρ <+: (firstVisits (a.1 ++ e :: b)).val then C.walks (a.1 ++ e :: b) else 0)]
            rw [hX, ← ENNReal.tsum_mul_right]
            congr 1; funext u
            rw [← ENNReal.tsum_mul_left]
            congr 1; funext v
            simp only [hKL ρ ys u.1 v e hρ u.2]
            rw [C.walks_eq, hcv, ENNReal.ofReal_mul (hc0 _ _)]
            split_ifs <;> simp
          · intro w hw
            by_contra hn
            apply hw
            rw [if_neg]
            intro h
            exact hn ((hmem w e).mp (h.subset heρ))
        have hN : (∑' w, if ρ <+: (firstVisits w).val ∧ Chooses S (firstVisits w).val j
              then C.walks w else 0) =
            X * ∑' v, (if Chooses S v j then ENNReal.ofReal (walkTail C.chain e v) else 0) := by
          rw [hdec e]
          · rw [ENNReal.tsum_prod (f := fun (a : {u : List (Fin n) // e ∉ u}) b =>
              if ρ <+: (firstVisits (a.1 ++ e :: b)).val ∧ Chooses S (firstVisits (a.1 ++ e :: b)).val j
              then C.walks (a.1 ++ e :: b) else 0)]
            rw [hX, ← ENNReal.tsum_mul_right]
            congr 1; funext u
            rw [← ENNReal.tsum_mul_left]
            congr 1; funext v
            simp only [hKL ρ ys u.1 v e hρ u.2]
            rw [C.walks_eq, hcv, ENNReal.ofReal_mul (hc0 _ _)]
            by_cases hq : ρ = (firstVisits (u.1 ++ [e])).val
            · have hch : Chooses S (firstVisits (u.1 ++ e :: v)).val j ↔ Chooses S v j := by
                unfold Chooses
                rw [hfind, List.find?_append, List.find?_cons]
                have hnotS : ∀ x ∈ u.1 ++ [e], x ∉ S := by
                  intro x hx hxS
                  have hxρ : x ∈ ρ := by rw [hq, hmem]; exact hx
                  exact Finset.disjoint_left.mp hS hxS (List.mem_toFinset.mpr hxρ)
                have hu : u.1.find? (fun i => decide (i ∈ S)) = none := by
                  rw [List.find?_eq_none]
                  intro x hx
                  simpa using hnotS x (by simp [hx])
                have he : ¬ e ∈ S := hnotS e (by simp)
                simp [hu, he]
              simp only [hq, true_and, hch]
              split_ifs <;> simp
            · simp [hq]
          · intro w hw
            by_contra hn
            apply hw
            rw [if_neg]
            intro h
            exact hn ((hmem w e).mp (h.1.subset heρ))
        have hpos' := hpos
        unfold prefProb at hpos'
        unfold condChoiceProb prefProb
        rw [hsumQ (fun ℓ => ρ <+: ℓ ∧ Chooses S ℓ j), hsumQ (fun ℓ => ρ <+: ℓ), hN, hT]
        rw [hsumQ (fun ℓ => ρ <+: ℓ), hT, ENNReal.toReal_mul] at hpos'
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
        exact mul_div_mul_left _ _ (left_ne_zero_of_mul (ne_of_gt hpos'))
      intro ρ hρ ρ' hρ' hlast _ S hS j _
      have hne : ρ ≠ [] := (Finset.mem_filter.mp hρ).2
      obtain ⟨e, he⟩ : ∃ e, ρ.getLast? = some e := by
        cases h : ρ.getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.mp h) hne
        | some e => exact ⟨e, rfl⟩
      have he' : ρ'.getLast? = some e := hlast ▸ he
      obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp he
      obtain ⟨ys', hys'⟩ := List.getLast?_eq_some_iff.mp he'
      rw [Finset.disjoint_union_right] at hS
      rw [hM ρ hρ e ys hys S hS.1 j, hM ρ' hρ' e ys' hys' S hS.2 j]
