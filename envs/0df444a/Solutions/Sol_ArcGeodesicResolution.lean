-- Prove2me | solution 1 for ArcGeodesicResolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:04:06.149932+00:00
-- url     : https://prove2.me/submissions/262e607b-e30c-4e00-ace9-534fbc44e5be

import Definitions.Def_Tablet_curveArc
import Definitions.Def_Tablet_IsGeodesicResolution
import Definitions.Def_Tablet_RestrictGeodesicResolutionTruncated
import Definitions.Def_Tablet_ConcatGeodesicResolution
import Definitions.Def_Tablet_ArcGeodesicResolution
import Theorems.Thm_ConcatGeodesicResolution
import Theorems.Thm_RestrictGeodesicResolutionTruncated


set_option autoImplicit false
open Set
theorem _root_.solution {E : Type*} [MetricSpace E] (γ : Curve E) (hcl : IsClosedCurve γ)
    (k : ℕ) (s : ℕ → ℝ) (hs : IsGeodesicResolution γ k s)
    (t t' : ℝ) (ht0 : 0 ≤ t) (htl : t ≤ γ.len) (ht'0 : 0 ≤ t') (ht'l : t' ≤ γ.len) :
    ∃ (kA : ℕ) (sA : ℕ → ℝ),
      1 ≤ kA ∧
      IsGeodesicResolution (curveArc γ hcl t t' ht0 htl ht'0 ht'l) kA sA ∧
      (t ≤ t' → ∃ j0 : ℕ,
        ∀ i : ℕ, 1 ≤ i → i ≤ kA - 1 → j0 + (i - 1) ≤ k ∧ sA i = s (j0 + (i - 1)) - t) ∧
      (t' < t → ∃ j0 m : ℕ,
        (∀ i : ℕ, 1 ≤ i → i ≤ m → j0 + (i - 1) ≤ k ∧ sA i = s (j0 + (i - 1)) - t) ∧
        (∀ i : ℕ, m < i → i ≤ kA - 1 → i - m ≤ k ∧
          sA i = (γ.len - t) + s (i - m)) ∧
        (1 ≤ m → s (j0 + (m - 1)) = γ.len)) := by
-- BODY
  classical
  obtain ⟨hmono, hs0, hsk, hedge⟩ := id hs
  by_cases hle : t ≤ t'
  · -- Ordinary case: the arc is the plain restriction `γ|_{[t,t']}`.
    have harc : curveArc γ hcl t t' ht0 htl ht'0 ht'l = curveRestrict γ t t' ht0 hle ht'l :=
      dif_pos hle
    rcases eq_or_lt_of_le hle with heq | hlt
    · -- Degenerate window `t = t'`: one trivial edge, both correspondence clauses vacuous.
      refine ⟨1, fun _ => 0, le_refl 1, ?_, ?_, ?_⟩
      · rw [harc]
        refine ⟨?_, rfl, ?_, ?_⟩
        · intro p _ q _ _; exact le_refl 0
        · show (0:ℝ) = t' - t
          rw [← heq]; ring
        · intro i _ u hu v hv
          have hu0 : u = 0 := le_antisymm hu.2 hu.1
          have hv0 : v = 0 := le_antisymm hv.2 hv.1
          rw [hu0, hv0]
          simp
      · intro _
        exact ⟨0, by intro i hi1 hi2; omega⟩
      · intro hc; exact absurd hle (not_le.mpr hc)
    · -- Nondegenerate window `t < t'`: canonical enclosing indices, then the truncated-end fact.
      set S : Finset ℕ := (Finset.range (k + 1)).filter (fun j => s j ≤ t) with hSdef
      have h0S : 0 ∈ S := by
        simp only [hSdef, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, by rw [hs0]; exact ht0⟩
      have hSne : S.Nonempty := ⟨0, h0S⟩
      set jA := S.max' hSne with hjAdef
      have hjAmem : jA ∈ S := S.max'_mem hSne
      have hjAprop : jA ≤ k ∧ s jA ≤ t := by
        have := hjAmem
        simp only [hSdef, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff] at this
        exact this
      have hsjA : s jA ≤ t := hjAprop.2
      have hjAk : jA < k := by
        rcases lt_or_eq_of_le hjAprop.1 with hlt' | heq'
        · exact hlt'
        · exfalso
          rw [heq', hsk] at hsjA
          linarith
      have hajA : t ≤ s (jA + 1) := by
        by_contra hcon
        have hcon' : s (jA + 1) < t := not_le.mp hcon
        have hmem : jA + 1 ∈ S := by
          simp only [hSdef, Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, le_of_lt hcon'⟩
        have hle' := S.le_max' _ hmem
        rw [← hjAdef] at hle'
        omega
      set T : Finset ℕ := (Finset.range (k + 1)).filter (fun j => t' ≤ s j) with hTdef
      have hkT : k ∈ T := by
        simp only [hTdef, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, by rw [hsk]; exact ht'l⟩
      have hTne : T.Nonempty := ⟨k, hkT⟩
      set jB := T.min' hTne with hjBdef
      have hjBmem : jB ∈ T := T.min'_mem hTne
      have hjBprop : jB ≤ k ∧ t' ≤ s jB := by
        have := hjBmem
        simp only [hTdef, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff] at this
        exact this
      have hjBk : jB ≤ k := hjBprop.1
      have hbjB : t' ≤ s jB := hjBprop.2
      have hjB1 : 1 ≤ jB := by
        rcases Nat.eq_zero_or_pos jB with hz | hp
        · exfalso
          rw [hz, hs0] at hbjB
          linarith
        · exact hp
      have hsjB : s (jB - 1) ≤ t' := by
        by_contra hcon
        have hcon' : t' < s (jB - 1) := not_le.mp hcon
        have hmem : jB - 1 ∈ T := by
          simp only [hTdef, Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, le_of_lt hcon'⟩
        have hle' := T.min'_le _ hmem
        rw [← hjBdef] at hle'
        omega
      have hjAB : jA < jB := by
        by_contra hcon
        have hcon' : jB ≤ jA := Nat.not_lt.mp hcon
        have : s jB ≤ s jA :=
          hmono (Set.mem_Icc.mpr ⟨Nat.zero_le _, hjBk⟩)
            (Set.mem_Icc.mpr ⟨Nat.zero_le _, le_of_lt hjAk⟩) hcon'
        linarith
      refine ⟨jB - jA,
        fun i => if i = 0 then 0 else if i = jB - jA then t' - t else s (jA + i) - t,
        by omega, ?_, ?_, ?_⟩
      · rw [harc]
        exact RestrictGeodesicResolutionTruncated γ k s hs t t' ht0 hlt ht'l jA jB hjAk hsjA
          hajA hjB1 hjBk hsjB hbjB
      · intro _
        refine ⟨jA + 1, ?_⟩
        intro i hi1 hi2
        have hidx : jA + 1 + (i - 1) = jA + i := by omega
        refine ⟨by omega, ?_⟩
        show (if i = 0 then (0:ℝ) else if i = jB - jA then t' - t else s (jA + i) - t)
            = s (jA + 1 + (i - 1)) - t
        rw [hidx, if_neg (by omega : ¬ (i = 0)), if_neg (by omega : ¬ (i = jB - jA))]
      · intro hc; exact absurd hle (not_le.mpr hc)
  · -- Wrap case: the arc is the concatenation of the tail `γ|_{[t,γ.len]}` with the head
    -- `γ|_{[0,t']}`.
    have ht't : t' < t := not_le.mp hle
    have hlenpos : 0 < γ.len := lt_of_le_of_lt ht'0 (lt_of_lt_of_le ht't htl)
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hk
      · exfalso; rw [hk0, hs0] at hsk; linarith
      · exact hk
    have hbl : t' ≤ γ.len := le_of_lt (lt_of_lt_of_le ht't htl)
    have hEnd : (curveRestrict γ t γ.len ht0 htl (le_refl γ.len)).toFun
          (curveRestrict γ t γ.len ht0 htl (le_refl γ.len)).len
        = (curveRestrict γ 0 t' (le_refl 0) ht'0 hbl).toFun 0 := by
      show γ.toFun (t + min (γ.len - t) (max 0 (γ.len - t)))
          = γ.toFun (0 + min (t' - 0) (max 0 0))
      have e1 : max (0:ℝ) (γ.len - t) = γ.len - t := max_eq_right (by linarith)
      have e2 : min (γ.len - t) (γ.len - t) = γ.len - t := min_self _
      have e3 : max (0:ℝ) (0:ℝ) = 0 := max_self 0
      have e4 : min (t' - 0) (0:ℝ) = 0 := by rw [sub_zero]; exact min_eq_right ht'0
      rw [e1, e2, e3, e4]
      have hzz : t + (γ.len - t) = γ.len := by ring
      rw [hzz, add_zero]
      exact hcl
    have harc2 : curveArc γ hcl t t' ht0 htl ht'0 ht'l
        = curveConcat (curveRestrict γ t γ.len ht0 htl (le_refl γ.len))
            (curveRestrict γ 0 t' (le_refl 0) ht'0 hbl) hEnd := by
      have h1 : curveArc γ hcl t t' ht0 htl ht'0 ht'l
          = curveWrapRestrict γ t t' hcl ht0 htl ht'0 (not_le.mp hle) := dif_neg hle
      rw [h1]
      rfl
    -- The tail `γ|_{[t,γ.len]}`, resolved with its breakpoints indexed from a single `j0`.
    obtain ⟨m, rt, j0, hrt, htail1, htail2⟩ :
        ∃ (m : ℕ) (rt : ℕ → ℝ) (j0 : ℕ),
          IsGeodesicResolution (curveRestrict γ t γ.len ht0 htl (le_refl γ.len)) m rt ∧
          (∀ i : ℕ, 1 ≤ i → i ≤ m → j0 + (i - 1) ≤ k ∧ rt i = s (j0 + (i - 1)) - t) ∧
          (1 ≤ m → s (j0 + (m - 1)) = γ.len) := by
      rcases eq_or_lt_of_le htl with hteq | htlt
      · refine ⟨0, fun _ => 0, 0, ⟨?_, rfl, ?_, ?_⟩, ?_, ?_⟩
        · intro p _ q _ _; exact le_refl 0
        · show (0:ℝ) = γ.len - t
          rw [← hteq]; ring
        · intro i hi; omega
        · intro i hi1 hi2; omega
        · intro hm; omega
      · set S : Finset ℕ := (Finset.range (k + 1)).filter (fun j => s j ≤ t) with hSdef
        have h0S : 0 ∈ S := by
          simp only [hSdef, Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, by rw [hs0]; exact ht0⟩
        have hSne : S.Nonempty := ⟨0, h0S⟩
        set jA := S.max' hSne with hjAdef
        have hjAmem : jA ∈ S := S.max'_mem hSne
        have hjAprop : jA ≤ k ∧ s jA ≤ t := by
          have hh := hjAmem
          simp only [hSdef, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff] at hh
          exact hh
        have hsjA : s jA ≤ t := hjAprop.2
        have hjAk : jA < k := by
          rcases lt_or_eq_of_le hjAprop.1 with hh | hh
          · exact hh
          · exfalso; rw [hh, hsk] at hsjA; linarith
        have hajA : t ≤ s (jA + 1) := by
          by_contra hcon
          have hcon' : s (jA + 1) < t := not_le.mp hcon
          have hmem : jA + 1 ∈ S := by
            simp only [hSdef, Finset.mem_filter, Finset.mem_range]
            exact ⟨by omega, le_of_lt hcon'⟩
          have hle2 := S.le_max' _ hmem
          rw [← hjAdef] at hle2
          omega
        have hsk1 : s (k - 1) ≤ γ.len := by
          rw [← hsk]
          exact hmono (Set.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩)
            (Set.mem_Icc.mpr ⟨Nat.zero_le _, le_rfl⟩) (by omega)
        refine ⟨k - jA,
          fun i => if i = 0 then 0 else if i = k - jA then γ.len - t else s (jA + i) - t,
          jA + 1, ?_, ?_, ?_⟩
        · exact RestrictGeodesicResolutionTruncated γ k s hs t γ.len ht0 htlt le_rfl jA k
            hjAk hsjA hajA hk1 le_rfl hsk1 hsk.ge
        · intro i hi1 hi2
          have hidx : jA + 1 + (i - 1) = jA + i := by omega
          refine ⟨by omega, ?_⟩
          show (if i = 0 then (0:ℝ) else if i = k - jA then γ.len - t else s (jA + i) - t)
              = s (jA + 1 + (i - 1)) - t
          rw [hidx, if_neg (by omega : ¬ (i = 0))]
          by_cases hik : i = k - jA
          · rw [if_pos hik]
            have he : jA + i = k := by omega
            rw [he, hsk]
          · rw [if_neg hik]
        · intro _
          have hidx : jA + 1 + (k - jA - 1) = k := by omega
          rw [hidx, hsk]
    -- The head `γ|_{[0,t']}`, resolved with its breakpoints being those of `s` unshifted.
    obtain ⟨Kh, rh, hrh, hhead1⟩ :
        ∃ (Kh : ℕ) (rh : ℕ → ℝ),
          IsGeodesicResolution (curveRestrict γ 0 t' (le_refl 0) ht'0 hbl) Kh rh ∧
          (∀ i : ℕ, 1 ≤ i → i ≤ Kh - 1 → i ≤ k ∧ rh i = s i) := by
      rcases eq_or_lt_of_le ht'0 with ht'eq | ht'pos
      · refine ⟨0, fun _ => 0, ⟨?_, rfl, ?_, ?_⟩, ?_⟩
        · intro p _ q _ _; exact le_refl 0
        · show (0:ℝ) = t' - 0
          rw [← ht'eq]; ring
        · intro i hi; omega
        · intro i hi1 hi2; omega
      · set T : Finset ℕ := (Finset.range (k + 1)).filter (fun j => t' ≤ s j) with hTdef
        have hkT : k ∈ T := by
          simp only [hTdef, Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, by rw [hsk]; exact hbl⟩
        have hTne : T.Nonempty := ⟨k, hkT⟩
        set jB := T.min' hTne with hjBdef
        have hjBmem : jB ∈ T := T.min'_mem hTne
        have hjBprop : jB ≤ k ∧ t' ≤ s jB := by
          have hh := hjBmem
          simp only [hTdef, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff] at hh
          exact hh
        have hjBk : jB ≤ k := hjBprop.1
        have hbjB : t' ≤ s jB := hjBprop.2
        have hjB1 : 1 ≤ jB := by
          rcases Nat.eq_zero_or_pos jB with hzz | hp
          · exfalso; rw [hzz, hs0] at hbjB; linarith
          · exact hp
        have hsjB : s (jB - 1) ≤ t' := by
          by_contra hcon
          have hcon' : t' < s (jB - 1) := not_le.mp hcon
          have hmem : jB - 1 ∈ T := by
            simp only [hTdef, Finset.mem_filter, Finset.mem_range]
            exact ⟨by omega, le_of_lt hcon'⟩
          have hle2 := T.min'_le _ hmem
          rw [← hjBdef] at hle2
          omega
        have hs1 : (0:ℝ) ≤ s (0 + 1) := by
          rw [Nat.zero_add, ← hs0]
          exact hmono (Set.mem_Icc.mpr ⟨Nat.zero_le _, Nat.zero_le _⟩)
            (Set.mem_Icc.mpr ⟨Nat.zero_le _, hk1⟩) (Nat.zero_le _)
        refine ⟨jB - 0,
          fun i => if i = 0 then 0 else if i = jB - 0 then t' - 0 else s (0 + i) - 0, ?_, ?_⟩
        · exact RestrictGeodesicResolutionTruncated γ k s hs 0 t' le_rfl ht'pos hbl 0 jB
            hk1 (le_of_eq hs0) hs1 hjB1 hjBk hsjB hbjB
        · intro i hi1 hi2
          refine ⟨by omega, ?_⟩
          show (if i = 0 then (0:ℝ) else if i = jB - 0 then t' - 0 else s (0 + i) - 0) = s i
          rw [if_neg (by omega : ¬ (i = 0)), if_neg (by omega : ¬ (i = jB - 0)),
            Nat.zero_add, sub_zero]
    -- Glue the two resolutions.
    by_cases hz : m + Kh = 0
    · have hm0 : m = 0 := by omega
      have hKh0 : Kh = 0 := by omega
      obtain ⟨-, hrt0, hrtm, -⟩ := hrt
      obtain ⟨-, hrh0, hrhK, -⟩ := hrh
      have hAlen : (curveRestrict γ t γ.len ht0 htl (le_refl γ.len)).len = 0 := by
        rw [← hrtm, hm0, hrt0]
      have hBlen : (curveRestrict γ 0 t' (le_refl 0) ht'0 hbl).len = 0 := by
        rw [← hrhK, hKh0, hrh0]
      refine ⟨1, fun _ => 0, le_refl 1, ?_, ?_, ?_⟩
      · rw [harc2]
        refine ⟨?_, rfl, ?_, ?_⟩
        · intro p _ q _ _; exact le_refl 0
        · show (0:ℝ) = (curveRestrict γ t γ.len ht0 htl (le_refl γ.len)).len
              + (curveRestrict γ 0 t' (le_refl 0) ht'0 hbl).len
          rw [hAlen, hBlen]; ring
        · intro i hi u hu v hv
          have hu0 : u = 0 := le_antisymm hu.2 hu.1
          have hv0 : v = 0 := le_antisymm hv.2 hv.1
          rw [hu0, hv0]
          simp
      · intro hc; exact absurd hc (not_le.mpr ht't)
      · intro _
        refine ⟨0, 0, ?_, ?_, ?_⟩
        · intro i hi1 hi2; omega
        · intro i hi1 hi2; omega
        · intro hi; omega
    · refine ⟨m + Kh, fun i => if i ≤ m then rt i else (γ.len - t) + rh (i - m),
        by omega, ?_, ?_, ?_⟩
      · rw [harc2]
        exact ConcatGeodesicResolution
          (curveRestrict γ t γ.len ht0 htl (le_refl γ.len))
          (curveRestrict γ 0 t' (le_refl 0) ht'0 hbl) hEnd m Kh rt rh hrt hrh
      · intro hc; exact absurd hc (not_le.mpr ht't)
      · intro _
        refine ⟨j0, m, ?_, ?_, ?_⟩
        · intro i hi1 hi2
          obtain ⟨hA, hB⟩ := htail1 i hi1 hi2
          refine ⟨hA, ?_⟩
          show (if i ≤ m then rt i else (γ.len - t) + rh (i - m)) = s (j0 + (i - 1)) - t
          rw [if_pos hi2]
          exact hB
        · intro i hi1 hi2
          have hi' : 1 ≤ i - m := by omega
          have hi'2 : i - m ≤ Kh - 1 := by omega
          obtain ⟨hA, hB⟩ := hhead1 (i - m) hi' hi'2
          refine ⟨hA, ?_⟩
          show (if i ≤ m then rt i else (γ.len - t) + rh (i - m)) = (γ.len - t) + s (i - m)
          rw [if_neg (by omega : ¬ (i ≤ m)), hB]
        · exact htail2
