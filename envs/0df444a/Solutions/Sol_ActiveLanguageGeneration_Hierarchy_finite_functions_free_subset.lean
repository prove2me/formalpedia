-- Prove2me | solution 1 for ActiveLanguageGeneration.Hierarchy.finite_functions_free_subset
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:20:29.68455+00:00
-- url     : https://prove2.me/submissions/2fab7499-8686-4289-8fac-5d93fd1602b1

import Mathlib
import Definitions.Def_ActiveLanguageGeneration_Hierarchy_DistinctTuple

section
set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy.Dev.Free

noncomputable section Ramsey
open Filter
open scoped Classical

variable {χ : Type*} [Finite χ]

lemma eventually_constant (U : Ultrafilter ℕ) (f : ℕ → χ) :
    ∃ b, ∀ᶠ m in U, f m = b :=
  U.eventually_exists_iff.mp (Eventually.of_forall (fun m => ⟨f m, rfl⟩))

noncomputable def limitColor (U : Ultrafilter ℕ) (c : Finset ℕ → χ) : ℕ → Finset ℕ → χ
  | 0, s => c s
  | k+1, s => (eventually_constant U (fun m => limitColor U c k (insert m s))).choose

lemma limitColor_eventually (U : Ultrafilter ℕ) (c : Finset ℕ → χ)
    (k : ℕ) (s : Finset ℕ) :
    ∀ᶠ m in U, limitColor U c k (insert m s) = limitColor U c (k+1) s :=
  (eventually_constant U (fun m => limitColor U c k (insert m s))).choose_spec

/-- The finite-set form of the infinite Ramsey theorem, proved by iterated
ultrafilter colors. Used only for the four-hit thinning in exact-pairs. -/
theorem homogeneous (n : ℕ) (c : Finset ℕ → χ) :
    ∃ (M : Set ℕ) (b : χ), M.Infinite ∧
      ∀ s : Finset ℕ, (↑s : Set ℕ) ⊆ M → s.card = n → c s = b := by
  let U := Ultrafilter.of (atTop : Filter ℕ)
  let b := limitColor U c n ∅
  let Good : Finset ℕ → Prop := fun S => ∀ s ⊆ S, s.card ≤ n → limitColor U c (n-s.card) s = b
  have hempty : Good ∅ := by
    intro s hs _
    have he : s = ∅ := Finset.subset_empty.mp hs
    subst s
    rfl
  have hstep (S : Finset ℕ) (hS : Good S) : ∃ m > S.sup id, Good (insert m S) := by
    have hev (s : Finset ℕ) (hs : s ⊆ S) : ∀ᶠ m in U,
        s.card < n → limitColor U c (n-s.card-1) (insert m s) = b := by
      by_cases hlt : s.card < n
      · have he : n-s.card-1+1 = n-s.card := by omega
        exact (limitColor_eventually U c (n-s.card-1) s).mono
          (fun _ h _ => h.trans (by rw [he]; exact hS s hs hlt.le))
      · exact Eventually.of_forall (fun _ h => (hlt h).elim)
    have hall : ∀ᶠ m in U, ∀ s ∈ S.powerset,
        s.card < n → limitColor U c (n-s.card-1) (insert m s) = b :=
      (eventually_all_finset S.powerset).mpr (fun s hs => hev s (Finset.mem_powerset.mp hs))
    have hlarge : ∀ᶠ m in U, S.sup id < m :=
      (eventually_gt_atTop (S.sup id)).filter_mono (Ultrafilter.of_le atTop)
    obtain ⟨m, hm, hall⟩ := (hlarge.and hall).exists
    have hmS : m ∉ S := by
      intro h
      exact (not_le_of_gt hm) (Finset.le_sup (f := id) h)
    refine ⟨m, hm, fun s hs hcard => ?_⟩
    by_cases hms : m ∈ s
    · let t := s.erase m
      have hts : t ⊆ S := by
        intro a ha
        have hh := Finset.mem_of_subset hs (Finset.mem_of_mem_erase ha)
        exact (Finset.mem_insert.mp hh).resolve_left (Finset.ne_of_mem_erase ha)
      have htc : t.card+1 = s.card := by
        exact Finset.card_erase_add_one hms
      have he : insert m t = s := Finset.insert_erase hms
      have hh := hall t (Finset.mem_powerset.mpr hts) (by omega)
      simpa only [he, show n-t.card-1 = n-s.card by omega] using hh
    · have hss : s ⊆ S := by
        intro a ha
        exact (Finset.mem_insert.mp (hs ha)).resolve_left (fun h => hms (h ▸ ha))
      exact hS s hss hcard
  let next (S : {S : Finset ℕ // Good S}) : ℕ := (hstep S.val S.property).choose
  have hn (S : {S : Finset ℕ // Good S}) : S.val.sup id < next S ∧ Good (insert (next S) S.val) :=
    (hstep S.val S.property).choose_spec
  let seq : ℕ → {S : Finset ℕ // Good S} := Nat.rec ⟨∅, hempty⟩
    (fun _ S => ⟨insert (next S) S.val, (hn S).2⟩)
  have hseq (i : ℕ) : (seq (i+1)).val = insert (next (seq i)) (seq i).val := rfl
  have hmono : Monotone (fun i => (seq i).val) := monotone_nat_of_le_succ
    (fun i => by rw [hseq]; exact Finset.subset_insert _ _)
  let v : ℕ → ℕ := fun i => next (seq i)
  have hvmem (i : ℕ) : v i ∈ (seq (i+1)).val := by rw [hseq]; exact Finset.mem_insert_self _ _
  have hv : StrictMono v := by
    apply strictMono_nat_of_lt_succ
    intro i
    exact (Finset.le_sup (f := id) (hvmem i)).trans_lt (hn (seq (i+1))).1
  let M : Set ℕ := ⋃ i, ↑(seq i).val
  have hM : M.Infinite := (Set.infinite_range_of_injective hv.injective).mono (by
    rintro _ ⟨i, rfl⟩
    exact Set.mem_iUnion.mpr ⟨i+1, hvmem i⟩)
  refine ⟨M, b, hM, fun s hs hcard => ?_⟩
  have hex : ∀ a : s, ∃ i, a.val ∈ (seq i).val :=
    fun a => Set.mem_iUnion.mp (hs a.property)
  choose k hk using hex
  let N := Finset.univ.sup k
  have hsub : s ⊆ (seq N).val := by
    intro a ha
    exact hmono (Finset.le_sup (f := k) (Finset.mem_univ ⟨a, ha⟩)) (hk ⟨a, ha⟩)
  have hh := (seq N).property s hsub hcard.le
  simpa only [hcard, Nat.sub_self, limitColor] using hh

/-- Relative version for any infinite subset of the natural numbers. -/
theorem homogeneous_subset (n : ℕ) (c : Finset ℕ → χ) (A : Set ℕ) (hA : A.Infinite) :
    ∃ (M : Set ℕ) (b : χ), M ⊆ A ∧ M.Infinite ∧
      ∀ s : Finset ℕ, (↑s : Set ℕ) ⊆ M → s.card = n → c s = b := by
  let f : ℕ → ℕ := Nat.nth (· ∈ A)
  have hf : StrictMono f := Nat.nth_strictMono hA
  obtain ⟨B, b, hB, hb⟩ := homogeneous n (fun s => c (s.image f))
  refine ⟨f '' B, b, ?_, hB.image hf.injective.injOn, ?_⟩
  · rintro _ ⟨i, _, rfl⟩
    exact Nat.nth_mem_of_infinite hA i
  · intro s hs hcard
    let t := s.preimage f (hf.injective.injOn)
    have him : t.image f = s := by
      ext a
      constructor
      · intro ha
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
        exact Finset.mem_preimage.mp hi
      · intro ha
        obtain ⟨i, _, rfl⟩ := hs ha
        exact Finset.mem_image.mpr ⟨i, Finset.mem_preimage.mpr ha, rfl⟩
    have hts : (↑t : Set ℕ) ⊆ B := by
      intro i hi
      have hfi : f i ∈ s := (Finset.mem_preimage.mp hi)
      obtain ⟨j, hj, he⟩ := hs hfi
      exact hf.injective he ▸ hj
    have htcard : t.card = n := by rw [← hcard, ← him, Finset.card_image_of_injective _ hf.injective]
    simpa only [him] using hb t hts htcard

end Ramsey

theorem ramsey_pnat {χ : Type} [Finite χ] (n : ℕ) (c : Finset ℕ+ → χ) (Z : Set ℕ+)
    (hZ : Z.Infinite) :
    ∃ (H : Set ℕ+) (b : χ), H ⊆ Z ∧ H.Infinite ∧
      ∀ s : Finset ℕ+, (↑s : Set ℕ+) ⊆ H → s.card = n → c s = b := by
  classical
  let A : Set ℕ := PNat.val '' Z
  have hA : A.Infinite := hZ.image PNat.coe_injective.injOn
  obtain ⟨M, b, hMA, hM, hb⟩ :=
    homogeneous_subset n (fun s : Finset ℕ => c (s.image Nat.toPNat')) A hA
  have hpos : ∀ m ∈ M, 0 < m := by
    intro m hm
    obtain ⟨p, _, rfl⟩ := hMA hm
    exact p.pos
  have hinj : Set.InjOn Nat.toPNat' M := by
    intro a ha a' ha' he
    have := congrArg PNat.val he
    rwa [PNat.toPNat'_coe (hpos a ha), PNat.toPNat'_coe (hpos a' ha')] at this
  refine ⟨Nat.toPNat' '' M, b, ?_, hM.image hinj, ?_⟩
  · rintro _ ⟨m, hm, rfl⟩
    obtain ⟨p, hp, rfl⟩ := hMA hm
    rwa [PNat.coe_toPNat']
  · intro s hs hcard
    have hcoe : ∀ x ∈ s, ((x : ℕ)) ∈ M := by
      intro x hx
      obtain ⟨m, hm, hmx⟩ := hs hx
      have : (m.toPNat' : ℕ) = m := PNat.toPNat'_coe (hpos m hm)
      rw [hmx] at this
      rw [this]; exact hm
    have hsimg : (s.image PNat.val).image Nat.toPNat' = s := by
      rw [Finset.image_image]
      have : (Nat.toPNat' ∘ PNat.val) = id := by
        funext x; exact PNat.coe_toPNat' x
      rw [this, Finset.image_id]
    have hc : (s.image PNat.val).card = n := by
      rw [Finset.card_image_of_injective _ PNat.coe_injective, hcard]
    have := hb (s.image PNat.val) (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      exact hcoe y hy) hc
    rwa [hsimg] at this

theorem exists_enum (H : Set ℕ+) (hH : H.Infinite) :
    ∃ h : ℕ → ℕ+, StrictMono h ∧ ∀ i, h i ∈ H := by
  let A : Set ℕ := PNat.val '' H
  have hA : A.Infinite := hH.image PNat.coe_injective.injOn
  have hf : StrictMono (Nat.nth (· ∈ A)) := Nat.nth_strictMono hA
  have hmem : ∀ i, Nat.nth (· ∈ A) i ∈ A := fun i => Nat.nth_mem_of_infinite hA i
  have hpos : ∀ i, 0 < Nat.nth (· ∈ A) i := by
    intro i
    obtain ⟨p, _, hp⟩ := hmem i
    rw [← hp]; exact p.pos
  refine ⟨fun i => Nat.toPNat' (Nat.nth (· ∈ A) i), ?_, ?_⟩
  · intro i j hij
    have := hf hij
    show (_ : ℕ+) < _
    rw [← PNat.coe_lt_coe, PNat.toPNat'_coe (hpos i), PNat.toPNat'_coe (hpos j)]
    exact this
  · intro i
    obtain ⟨p, hp, he⟩ := hmem i
    show Nat.toPNat' _ ∈ H
    rw [← he, PNat.coe_toPNat']
    exact hp

open ActiveLanguageGeneration.Hierarchy

/-- Colour of a finite set `S` of `ℕ+`: the set of positions `k` such that the `k`-th element of
`S` is the value of `g` on some ordering of the others. -/
def col (X : Set ℕ+) (q : ℕ) (g : DistinctTuple X q → ℕ+) (S : Finset ℕ+) : Fin (q+1) → Prop :=
  fun k => ∃ h : S.card = q+1, ∃ t : DistinctTuple X q,
    Set.range (fun j => (t j).val) = ↑(S.erase (S.orderEmbOfFin h k)) ∧
      g t = S.orderEmbOfFin h k

theorem no_color (X : Set ℕ+) (q : ℕ) (g : DistinctTuple X q → ℕ+) (H : Set ℕ+)
    (b : Fin (q+1) → Prop)
    (hhom : ∀ s : Finset ℕ+, (↑s : Set ℕ+) ⊆ H → s.card = q+1 → col X q g s = b)
    (h : ℕ → ℕ+) (hmono : StrictMono h) (hH : ∀ i, h i ∈ H) (k : Fin (q+1)) : ¬ b k := by
  classical
  intro hbk
  let M : ℕ := q^q+1
  let N : Finset ℕ := Finset.range k ∪ Finset.Ico (k+M) (q+M)
  let A : Finset ℕ+ := N.image h
  have hk : (k : ℕ) ≤ q := Nat.lt_succ_iff.mp k.isLt
  have hex : ∀ m : Fin M, ∃ t : DistinctTuple X q,
      Set.range (fun j => (t j).val) = (↑A : Set ℕ+) ∧ g t = h (k+m) := by
    intro m
    let w : Fin (q+1) → ℕ := fun j => if (j:ℕ) < k then j else if (j:ℕ) = k then k+m else j-1+M
    have hw : StrictMono w := by
      intro i j hij
      have : (i:ℕ) < j := hij
      have hm := m.isLt
      simp only [w]; split_ifs <;> omega
    let f : Fin (q+1) → ℕ+ := fun j => h (w j)
    have hf : StrictMono f := hmono.comp hw
    let S : Finset ℕ+ := Finset.univ.image f
    have hScard : S.card = q+1 := by
      rw [Finset.card_image_of_injective _ hf.injective]; simp
    have hfe : f = S.orderEmbOfFin hScard :=
      Finset.orderEmbOfFin_unique hScard
        (fun x => Finset.mem_image_of_mem _ (Finset.mem_univ x)) hf
    have hSH : (↑S : Set ℕ+) ⊆ H := by
      intro x hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      exact hH _
    have hcol : col X q g S k := by
      have := congrFun (hhom S hSH hScard) k
      rw [this]; exact hbk
    obtain ⟨h', t, ht1, ht2⟩ := hcol
    have hfe' : S.orderEmbOfFin h' = f := hfe.symm
    rw [hfe'] at ht1 ht2
    have hfk : f k = h (k+m) := by
      simp [f, w]
    have hAeq : S.erase (f k) = A := by
      ext x
      simp only [Finset.mem_erase, S, A, N, Finset.mem_image, Finset.mem_univ, true_and,
        Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
      have hm := m.isLt
      constructor
      · rintro ⟨hne, j, rfl⟩
        refine ⟨w j, ?_, rfl⟩
        have hj := j.isLt
        have : (j : ℕ) ≠ k := by
          intro he
          apply hne
          have : j = k := Fin.ext he
          rw [this]
        simp only [w]
        split_ifs <;> omega
      · rintro ⟨i, hi, rfl⟩
        refine ⟨?_, ?_⟩
        · rw [hfk]
          intro he
          have := hmono.injective he
          omega
        · by_cases hik : i < k
          · refine ⟨⟨i, by omega⟩, ?_⟩
            simp only [f, w]
            rw [if_pos (by simpa using hik)]
          · refine ⟨⟨i - M + 1, by omega⟩, ?_⟩
            simp only [f, w]
            have : ¬ (i - M + 1 < k) := by omega
            have h2 : ¬ (i - M + 1 = k) := by omega
            simp only [this, h2, if_false]
            congr 1
            omega
    refine ⟨t, ?_, ?_⟩
    · rw [ht1, hAeq]
    · rw [ht2, hfk]
  choose t ht1 ht2 using hex
  have hmem : ∀ m j, (t m j).val ∈ A := by
    intro m j
    have : (t m j).val ∈ Set.range (fun j => (t m j).val) := ⟨j, rfl⟩
    rw [ht1 m] at this
    exact_mod_cast this
  let Φ : Fin M → (Fin q → ↥A) := fun m j => ⟨(t m j).val, hmem m j⟩
  have hΦ : Function.Injective Φ := by
    intro m m' he
    have htt : t m = t m' := by
      ext j
      exact congrArg (fun F => (F j).val) he
    have h3 : h (k + m) = h (k + m') := by rw [← ht2 m, ← ht2 m', htt]
    have := hmono.injective h3
    exact Fin.ext (by omega)
  have hc := Fintype.card_le_of_injective Φ hΦ
  have hAcard : A.card ≤ q := by
    calc A.card ≤ N.card := Finset.card_image_le
      _ ≤ (Finset.range k).card + (Finset.Ico (k+M) (q+M)).card := Finset.card_union_le _ _
      _ ≤ q := by simp; omega
  simp only [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin] at hc
  have : A.card ^ q ≤ q ^ q := Nat.pow_le_pow_left hAcard q
  have hM : M = q^q+1 := rfl
  omega

theorem single_step (X : Set ℕ+) (q : ℕ) (g : DistinctTuple X q → ℕ+) (Z : Set ℕ+)
    (hZ : Z.Infinite) :
    ∃ Y : Set ℕ+, Y ⊆ Z ∧ Y.Infinite ∧
      ∀ a : DistinctTuple X q, tupleValues a ⊆ Y → g a ∉ Y \ tupleValues a := by
  classical
  obtain ⟨H, b, hHZ, hHinf, hhom⟩ := ramsey_pnat (q+1) (col X q g) Z hZ
  obtain ⟨h, hmono, hH⟩ := exists_enum H hHinf
  refine ⟨H, hHZ, hHinf, ?_⟩
  intro a ha hga
  obtain ⟨hgH, hgn⟩ := hga
  let S : Finset ℕ+ := insert (g a) (Finset.univ.image fun j => (a j).val)
  have hnot : g a ∉ (Finset.univ.image fun j => (a j).val) := by
    intro hm
    apply hgn
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm
    exact ⟨j, hj⟩
  have hScard : S.card = q+1 := by
    rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective]
    · simp
    · intro i j hij
      exact a.injective (Subtype.ext hij)
  have hSH : (↑S : Set ℕ+) ⊆ H := by
    intro x hx
    rcases Finset.mem_insert.mp (Finset.mem_coe.mp hx) with rfl | hx
    · exact hgH
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      exact ha ⟨j, rfl⟩
  have hcol := hhom S hSH hScard
  have hmemS : g a ∈ S := Finset.mem_insert_self _ _
  have hr := Finset.range_orderEmbOfFin S hScard
  have : g a ∈ Set.range (S.orderEmbOfFin hScard) := by rw [hr]; exact hmemS
  obtain ⟨k, hk⟩ := this
  have hbk : b k := by
    rw [← hcol]
    refine ⟨hScard, a, ?_, hk.symm⟩
    rw [hk]
    simp only [S, Finset.erase_insert hnot]
    ext x; simp
  exact no_color X q g H b hhom h hmono hH k hbk

end ActiveLanguageGeneration.Hierarchy.Dev.Free

namespace ActiveLanguageGeneration.Hierarchy

open Dev.Free in
theorem chk_finite_functions_free_subset
    (X : Set ℕ+) (hX : X.Infinite) {ι : Type} [Fintype ι]
    (r : ι → ℕ+) (g : (i : ι) → DistinctTuple X (r i : ℕ) → ℕ+) :
    ∃ Y : Set ℕ+, Y ⊆ X ∧ Y.Infinite ∧
      ∀ (i : ι) (a : DistinctTuple X (r i : ℕ)), tupleValues a ⊆ Y →
        g i a ∉ Y \ tupleValues a := by
  classical
  have key : ∀ s : Finset ι, ∃ Y : Set ℕ+, Y ⊆ X ∧ Y.Infinite ∧
      ∀ i ∈ s, ∀ a : DistinctTuple X (r i : ℕ), tupleValues a ⊆ Y →
        g i a ∉ Y \ tupleValues a := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨X, subset_rfl, hX, fun i hi => by simp at hi⟩
    | insert i s hi ih =>
      obtain ⟨Y, hYX, hYinf, hY⟩ := ih
      obtain ⟨Y', hY'Y, hY'inf, hY'⟩ := single_step X (r i : ℕ) (g i) Y hYinf
      refine ⟨Y', hY'Y.trans hYX, hY'inf, ?_⟩
      intro j hj a ha hmem
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hY' a ha hmem
      · exact hY j hj a (ha.trans hY'Y) ⟨hY'Y hmem.1, hmem.2⟩
  obtain ⟨Y, hYX, hYinf, hY⟩ := key Finset.univ
  exact ⟨Y, hYX, hYinf, fun i a ha => hY i (Finset.mem_univ i) a ha⟩

end ActiveLanguageGeneration.Hierarchy

end

theorem solution : type_of% @ActiveLanguageGeneration.Hierarchy.chk_finite_functions_free_subset := @ActiveLanguageGeneration.Hierarchy.chk_finite_functions_free_subset
