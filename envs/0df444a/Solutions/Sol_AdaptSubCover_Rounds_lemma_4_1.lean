-- Prove2me | solution 1 for AdaptSubCover.Rounds.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T22:07:48.545505+00:00
-- url     : https://prove2.me/submissions/2389c64a-039a-4e15-ac10-5f47d8a20af6

import Mathlib
import Definitions.Def_AdaptSubCover_Rounds_Analysis

open AdaptSubCover.Rounds

namespace ASCL41

variable {U : Type} [DecidableEq U] {m : ℕ}

theorem go_prefix (stop : History m U → Bool) (ω : Fin m → U) :
    ∀ (L : List (Fin m)) (h : History m U), h <+: Round.go stop ω L h
  | [], h => by simp [Round.go]
  | i :: L, h => by
    simp only [Round.go]
    split_ifs with h1 h2
    · exact List.prefix_refl _
    · exact go_prefix stop ω L h
    · exact (List.prefix_append h _).trans (go_prefix stop ω L _)

theorem items_mono {h h' : History m U} (hp : h <+: h') : h.items ⊆ h'.items := by
  obtain ⟨t, rfl⟩ := hp
  intro x hx
  simp only [History.items, List.map_append, List.toFinset_append, Finset.mem_union] at hx ⊢
  exact Or.inl hx

theorem items_append (h : History m U) (x : Fin m × U) :
    (h ++ [x]).items = insert x.1 h.items := by
  ext y; simp [History.items, or_comm]

/-- If the stopping rule fires after the first `k` entries, only those entries are probed. -/
theorem go_items_sub (stop : History m U → Bool) (ω : Fin m → U) :
    ∀ (l : List (Fin m)) (h : History m U) (k : ℕ), l.Nodup → (∀ x ∈ l, x ∉ h.items) →
      stop (h ++ (l.take k).map (fun i => (i, ω i))) = true →
      (Round.go stop ω l h).items ⊆ h.items ∪ (l.take k).toFinset
  | [], h, k, _, _, _ => by simp [Round.go]
  | i :: l, h, k, hnd, hdis, hs => by
    by_cases hsh : stop h = true
    · simp [Round.go, hsh]
    · have hs' : stop h = false := by simpa using hsh
      have hi : i ∉ h.items := hdis i (by simp)
      have e : Round.go stop ω (i :: l) h = Round.go stop ω l (h ++ [(i, ω i)]) := by
        simp [Round.go, hs', hi]
      rw [e]
      cases k with
      | zero => simp at hs; exact absurd hs hsh
      | succ k =>
        have hnd' := (List.nodup_cons.mp hnd)
        have hdis' : ∀ x ∈ l, x ∉ (h ++ [(i, ω i)]).items := by
          intro x hx
          rw [items_append, Finset.mem_insert, not_or]
          exact ⟨fun hxi => hnd'.1 (by simp only at hxi; exact hxi ▸ hx), hdis x (by simp [hx])⟩
        have hs2 : stop ((h ++ [(i, ω i)]) ++ (l.take k).map (fun i => (i, ω i))) = true := by
          simpa using hs
        have := go_items_sub stop ω l _ k hnd'.2 hdis' hs2
        refine this.trans ?_
        rw [items_append]
        intro y hy
        simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset] at hy ⊢
        rcases hy with (rfl | hy) | hy
        · right; simp
        · left; exact hy
        · right; simp [hy]

/-- If the stopping rule never fires on the first `k+1` prefixes, the entry `l[k]` is probed. -/
theorem go_items_mem (stop : History m U → Bool) (ω : Fin m → U) :
    ∀ (l : List (Fin m)) (h : History m U) (k : ℕ) (hk : k < l.length), l.Nodup →
      (∀ x ∈ l, x ∉ h.items) →
      (∀ j ≤ k, stop (h ++ (l.take j).map (fun i => (i, ω i))) = false) →
      l[k] ∈ (Round.go stop ω l h).items
  | [], h, k, hk, _, _, _ => by simp at hk
  | i :: l, h, k, hk, hnd, hdis, hs => by
    have hs0 : stop h = false := by simpa using hs 0 (Nat.zero_le _)
    have hi : i ∉ h.items := hdis i (by simp)
    have e : Round.go stop ω (i :: l) h = Round.go stop ω l (h ++ [(i, ω i)]) := by
      simp [Round.go, hs0, hi]
    rw [e]
    cases k with
    | zero =>
      apply items_mono (go_prefix stop ω l _)
      simp [items_append]
    | succ k =>
      have hnd' := (List.nodup_cons.mp hnd)
      have hdis' : ∀ x ∈ l, x ∉ (h ++ [(i, ω i)]).items := by
        intro x hx
        rw [items_append, Finset.mem_insert, not_or]
        exact ⟨fun hxi => hnd'.1 (by simp only at hxi; exact hxi ▸ hx), hdis x (by simp [hx])⟩
      have := go_items_mem stop ω l (h ++ [(i, ω i)]) k (by simpa using hk) hnd'.2 hdis'
        (fun j hj => by simpa using hs (j + 1) (by omega))
      simpa using this

end ASCL41

namespace ASCL41

/-- Arithmetic core: for an integer value `F ≤ Q`, `τ < F` iff `F` is in a scale `j ≥ z` or
`F = Q`. -/
theorem scale_iff (Q F z : ℕ) (hQ : 0 < Q) (hFQ : F ≤ Q)
    (hτ : (F : ℝ) ≠ (Q : ℝ) * (1 - delta z)) :
    (Q : ℝ) * (1 - delta z) < F ↔
      ((∃ j : ℕ, z ≤ j ∧ j ≤ Nat.log 2 Q ∧ (2⁻¹ : ℝ) ^ j / 2 < ((Q : ℝ) - F) / Q ∧
        ((Q : ℝ) - F) / Q ≤ (2⁻¹ : ℝ) ^ j) ∨ F = Q) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hinv : ∀ j : ℕ, (2⁻¹ : ℝ) ^ j = 1 / 2 ^ j := by intro j; rw [inv_pow, one_div]
  constructor
  · intro hlt
    rcases eq_or_lt_of_le hFQ with hEq | hlt'
    · exact Or.inr hEq
    left
    set d := Q - F with hd
    have hd1 : 1 ≤ d := by omega
    have hdQ : d ≤ Q := by omega
    set j := Nat.log 2 (Q / d)
    have hqd : Q / d ≠ 0 := by
      have : 1 ≤ Q / d := (Nat.one_le_div_iff (by omega)).mpr hdQ
      omega
    have h1 : 2 ^ j * d ≤ Q := by
      have := Nat.pow_log_le_self 2 hqd
      calc 2 ^ j * d ≤ Q / d * d := Nat.mul_le_mul_right _ this
        _ ≤ Q := Nat.div_mul_le_self Q d
    have h2 : Q < 2 ^ (j + 1) * d := by
      have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (Q / d)
      exact (Nat.div_lt_iff_lt_mul (by omega)).mp this
    have hdr : ((Q : ℝ) - F) = (d : ℝ) := by
      rw [hd, Nat.cast_sub hFQ]
    have h1r : (2 : ℝ) ^ j * d ≤ Q := by exact_mod_cast h1
    have h2r : (Q : ℝ) < 2 ^ (j + 1) * d := by exact_mod_cast h2
    have hδ : delta z = 1 / 2 ^ z := by unfold delta; rw [hinv]
    refine ⟨j, ?_, ?_, ?_, ?_⟩
    · by_contra hjz
      push_neg at hjz
      have hpow : (2 : ℝ) ^ (j + 1) ≤ 2 ^ z := pow_le_pow_right₀ (by norm_num) (by omega)
      -- τ < F means d < Q / 2^z
      have : (d : ℝ) * 2 ^ z < Q := by
        rw [hδ] at hlt
        have h2z : (0 : ℝ) < 2 ^ z := by positivity
        have : (Q : ℝ) - F < Q / 2 ^ z := by
          have e : (Q : ℝ) * (1 - 1 / 2 ^ z) = Q - Q / 2 ^ z := by ring
          linarith
        rw [hdr, lt_div_iff₀ h2z] at this
        exact this
      have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
      nlinarith
    · apply Nat.log_mono_right
      exact Nat.div_le_self Q d
    · rw [hdr, hinv, lt_div_iff₀ hQr]
      rw [pow_succ] at h2r
      have h2j : (0 : ℝ) < 2 ^ j := by positivity
      rw [div_div, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      linarith
    · rw [hdr, hinv, div_le_iff₀ hQr]
      have h2j : (0 : ℝ) < 2 ^ j := by positivity
      rw [div_mul_eq_mul_div, le_div_iff₀ h2j]
      linarith
  · rintro (⟨j, hzj, -, -, hle⟩ | hEq)
    · have hδj : (2⁻¹ : ℝ) ^ j ≤ delta z := by
        unfold delta
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hzj
      have : ((Q : ℝ) - F) / Q ≤ delta z := hle.trans hδj
      rw [div_le_iff₀ hQr] at this
      have hge : (Q : ℝ) * (1 - delta z) ≤ F := by nlinarith
      exact lt_of_le_of_ne hge (Ne.symm hτ)
    · subst hEq
      have hδ : 0 < delta z := by unfold delta; positivity
      nlinarith

end ASCL41

open ASCL41 in
theorem solution {U : Type} [Fintype U] [DecidableEq U] {m : ℕ} (I : Instance U m) (hI : I.Standing) (hQ : 0 < I.Q)
    (z : ℕ) (hτ : ∀ n : ℕ, (n : ℝ) ≠ I.tau z)
    (L : List (Fin m)) (hL : I.IsGreedyList (fun A => (I.f A : ℝ)) I.Q (I.tau z) Finset.univ L)
    (t : ℝ) (ht0 : 0 ≤ t) (ht : t < (I.cumCost L L.length : ℝ)) (ω : Fin m → U) :
    I.NAStoppedBy (I.tau z) L t ω ↔
      ((∃ j : ℕ, z ≤ j ∧ I.InScale j (I.prefixAt L t) ω) ∨
        I.f ((I.prefixAt L t).image ω) = I.Q) := by
  obtain ⟨-, -, -, hmon, -⟩ := hI
  obtain ⟨hnd, -, -⟩ := hL
  set k := Nat.findGreatest (fun j => (I.cumCost L j : ℝ) ≤ t) L.length with hk
  have hpre : I.prefixAt L t = (L.take k).toFinset := rfl
  have hPk : (I.cumCost L k : ℝ) ≤ t := by
    have := Nat.findGreatest_spec (P := fun j => (I.cumCost L j : ℝ) ≤ t) (m := 0) (n := L.length)
      (Nat.zero_le _) (by simp [Instance.cumCost, ht0])
    exact this
  have hkle : k ≤ L.length := Nat.findGreatest_le _
  have hklt : k < L.length := by
    rcases eq_or_lt_of_le hkle with h | h
    · rw [h] at hPk; linarith
    · exact h
  set g : Fin m → Fin m × U := fun i => (i, ω i)
  set stop := (I.parcaRound (I.tau z) L).stop
  have hstop : ∀ h : History m U, stop h = decide (I.tau z < (I.f h.realized : ℝ)) := fun _ => rfl
  have hreal : ∀ j, History.realized (([] : History m U) ++ (L.take j).map g) =
      (L.take j).toFinset.image ω := by
    intro j
    ext u
    simp only [History.realized, g, List.nil_append, List.map_map, List.mem_toFinset,
      Finset.mem_image]
    rw [List.mem_map]
    simp
  have hNA : I.NA (I.tau z) L ω = Round.go stop ω L [] := rfl
  have hFQ : I.f ((L.take k).toFinset.image ω) ≤ I.Q := hmon (Finset.subset_univ _)
  -- the stopping characterization
  have hchar : I.NAStoppedBy (I.tau z) L t ω ↔
      I.tau z < (I.f ((L.take k).toFinset.image ω) : ℝ) := by
    unfold Instance.NAStoppedBy
    rw [hpre, hNA]
    constructor
    · intro hsub
      by_contra hcon
      push_neg at hcon
      have hmem := go_items_mem stop ω L [] k hklt hnd (by simp [History.items])
        (by
          intro j hj
          rw [hstop, hreal j, decide_eq_false_iff_not, not_lt]
          refine le_trans ?_ hcon
          have : (L.take j).toFinset.image ω ⊆ (L.take k).toFinset.image ω := by
            apply Finset.image_subset_image
            intro x hx
            simp only [List.mem_toFinset] at hx ⊢
            exact List.take_subset_take_left L hj hx
          exact_mod_cast hmon this)
      have := hsub hmem
      rw [List.mem_toFinset] at this
      have hnd' := hnd
      rw [← List.take_append_drop k L] at hnd'
      have hdrop : L[k] ∈ L.drop k := by
        rw [List.mem_iff_getElem]
        exact ⟨0, by simp; omega, by simp⟩
      exact List.disjoint_of_nodup_append hnd' this hdrop
    · intro hlt
      have := go_items_sub stop ω L [] k hnd (by simp [History.items])
        (by rw [hstop, hreal k]; simpa using hlt)
      simpa [History.items] using this
  rw [hchar]
  unfold Instance.tau
  rw [hpre]
  have hsi := scale_iff I.Q (I.f ((L.take k).toFinset.image ω)) z hQ hFQ (hτ _)
  rw [hsi]
  rfl
