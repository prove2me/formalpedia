-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RegularLocalRegularSequence_RingKrullDimQuotientSpanSingletonAddOne
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RegularLocalRegularSequence_RingKrullDimQuotientSpanSingletonAddOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:41.955356+00:00
-- url     : https://prove2.me/theorems/6ee0b70a-d9fd-4e8a-a91f-77f67ecf0140
-- title:
--   Ring Krull Dim Quotient Span Singleton Add One
-- statement:
--   Definitions and structural lemmas for Ring Krull Dim Quotient Span Singleton Add One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RegularLocalRegularSequence/RingKrullDimQuotientSpanSingletonAddOne.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.UnitaryGroupMassFormula.RLRS
namespace IsRegularLocalRing
open IsLocalRing
universe u
theorem spanFinrank_span_finset_le {R : Type*} [CommRing R] (s : Finset R) :
    Submodule.spanFinrank (Ideal.span (s : Set R)) ≤ s.card := by
  exact (Submodule.spanFinrank_span_le_ncard_of_finite s.finite_toSet).trans_eq (Set.ncard_coe_finset s)
theorem exists_repr_ne_zero {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (b : Module.Basis ι K V) {v : V} (hv : v ≠ 0) : ∃ j, b.repr v j ≠ 0 := by
  by_contra h
  simp only [not_exists, ne_eq, not_not] at h
  exact hv (b.repr.map_eq_zero_iff.mp (Finsupp.ext fun j => by simpa using h j))
theorem span_insert_image_erase_eq_top {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {N : ℕ} (b : Module.Basis (Fin N) K V) (v : V) {j : Fin N}
    (hj : b.repr v j ≠ 0) :
    Submodule.span K (insert v (⇑b '' ↑(Finset.univ.erase j))) = ⊤ := by
  classical
  set W := Submodule.span K (insert v (⇑b '' ↑(Finset.univ.erase j))) with hW
  have hb : ∀ i, i ≠ j → b i ∈ W := fun i hi =>
    Submodule.subset_span (Set.mem_insert_of_mem _ ⟨i, by simp [hi], rfl⟩)
  have hvW : v ∈ W := Submodule.subset_span (Set.mem_insert _ _)
  have hbj : b j ∈ W := by
    have h1 : ∑ i, b.repr v i • b i = v := b.sum_repr v
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at h1
    have h2 : b.repr v j • b j ∈ W := by
      rw [eq_sub_of_add_eq h1]
      exact W.sub_mem hvW (W.sum_mem fun i hi => W.smul_mem _ (hb i (Finset.ne_of_mem_erase hi)))
    have h3 := W.smul_mem (b.repr v j)⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ hj, one_smul] at h3
  rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  by_cases hi : i = j
  · subst hi; exact hbj
  · exact hb i hi
theorem isLocalRing_quotient_span_singleton {R : Type*} [CommRing R] [IsLocalRing R]
    {x : R} (hx : x ∈ maximalIdeal R) : IsLocalRing (R ⧸ Ideal.span ({x} : Set R)) := by
  have hne : Ideal.span ({x} : Set R) ≠ ⊤ := fun h => by
    have hle : Ideal.span ({x} : Set R) ≤ maximalIdeal R :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)
    rw [h] at hle
    exact (inferInstance : (maximalIdeal R).IsMaximal).ne_top (top_le_iff.mp hle)
  have : Nontrivial (R ⧸ Ideal.span ({x} : Set R)) := Ideal.Quotient.nontrivial_iff.mpr hne
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
theorem spanFinrank_maximalIdeal_quotient_succ_le (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2)
    [IsLocalRing (R ⧸ Ideal.span ({x} : Set R))] :
    Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) + 1 ≤
      Module.finrank (ResidueField R) (CotangentSpace R) := by
  classical
  let b := Module.finBasis (ResidueField R) (CotangentSpace R)
  have hv : (maximalIdeal R).toCotangent ⟨x, hx⟩ ≠ 0 := by
    rw [Ne, Ideal.toCotangent_eq_zero]; exact hx2
  obtain ⟨j, hj⟩ := exists_repr_ne_zero b hv
  have htop := span_insert_image_erase_eq_top b _ hj
  choose y hy using fun i => (maximalIdeal R).toCotangent_surjective (b i)
  have hcot : Submodule.span (ResidueField R) ((maximalIdeal R).toCotangent ''
      (insert (⟨x, hx⟩ : maximalIdeal R) (y '' ↑(Finset.univ.erase j)))) = ⊤ := by
    refine Eq.trans ?_ htop
    congr 1
    simp only [Set.image_insert_eq, Set.image_image, hy]
  have hspan0 := IsLocalRing.CotangentSpace.span_image_eq_top_iff.mp hcot
  have hspan : Submodule.span R (Subtype.val ''
      (insert (⟨x, hx⟩ : maximalIdeal R) (y '' ↑(Finset.univ.erase j)))) = maximalIdeal R := by
    calc _ = Submodule.map (maximalIdeal R).subtype (Submodule.span R
          (insert (⟨x, hx⟩ : maximalIdeal R) (y '' ↑(Finset.univ.erase j)))) :=
          (Submodule.map_span _ _).symm
      _ = Submodule.map (maximalIdeal R).subtype ⊤ := by rw [hspan0]
      _ = maximalIdeal R := Submodule.map_subtype_top _
  obtain ⟨F, hF⟩ : ∃ F : Finset R, F = (Finset.univ.erase j).image (fun i => (y i : R)) := ⟨_, rfl⟩
  have hm : Ideal.span (insert x (F : Set R)) = maximalIdeal R := by
    refine Eq.trans ?_ hspan
    rw [hF, Finset.coe_image, Set.image_insert_eq, Set.image_image]
  have hcomap : Ideal.comap (Ideal.Quotient.mk (Ideal.span ({x} : Set R)))
      (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
  have hx0 : Ideal.Quotient.mk (Ideal.span ({x} : Set R)) x = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x)
  have hQ : maximalIdeal (R ⧸ Ideal.span ({x} : Set R)) =
      Ideal.span ((F.image (Ideal.Quotient.mk (Ideal.span ({x} : Set R))) : Finset _) :
        Set (R ⧸ Ideal.span ({x} : Set R))) := by
    rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective
      (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))), hcomap, ← hm, Ideal.map_span,
      Set.image_insert_eq, hx0, Ideal.span_insert, Ideal.span_singleton_eq_bot.mpr rfl, bot_sup_eq,
      Finset.coe_image]
  have hcard : (F.image (Ideal.Quotient.mk (Ideal.span ({x} : Set R)))).card ≤
      Module.finrank (ResidueField R) (CotangentSpace R) - 1 := by
    calc (F.image (Ideal.Quotient.mk (Ideal.span ({x} : Set R)))).card ≤ F.card := Finset.card_image_le
      _ ≤ (Finset.univ.erase j).card := by rw [hF]; exact Finset.card_image_le
      _ = _ := by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hpos : 0 < Module.finrank (ResidueField R) (CotangentSpace R) := Fin.pos j
  rw [hQ]
  have := spanFinrank_span_finset_le (F.image (Ideal.Quotient.mk (Ideal.span ({x} : Set R))))
  omega
theorem natCast_withBot_enat_le_iff {a b : ℕ} :
    ((a : ℕ) : WithBot ℕ∞) ≤ ((b : ℕ) : WithBot ℕ∞) ↔ a ≤ b := by
  exact Nat.cast_le
theorem eq_natCast_and_add_one_eq_of_le {a : WithBot ℕ∞} {d n : ℕ}
    (h1 : ((n : ℕ) : WithBot ℕ∞) ≤ a + 1) (h2 : a ≤ ((d : ℕ) : WithBot ℕ∞)) (h3 : d + 1 ≤ n) :
    a = ((d : ℕ) : WithBot ℕ∞) ∧ a + 1 = ((n : ℕ) : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot =>
    exfalso
    rw [WithBot.bot_add, le_bot_iff] at h1; exact WithBot.natCast_ne_bot n h1
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      exact ENat.natCast_ne_top d (top_le_iff.mp (WithBot.coe_le_coe.mp h2))
    | coe k =>
      have ek : (((k : ℕ) : ℕ∞) : WithBot ℕ∞) = ((k : ℕ) : WithBot ℕ∞) := rfl
      rw [ek] at h1 h2 ⊢
      rw [← Nat.cast_succ] at h1
      have h1' := natCast_withBot_enat_le_iff.mp h1
      have h2' := natCast_withBot_enat_le_iff.mp h2
      have hkd : k = d := by omega
      have hn : n = k + 1 := by omega
      subst hkd hn
      exact ⟨rfl, (Nat.cast_succ k).symm⟩
theorem spanFinrank_maximalIdeal_eq_ringKrullDim (R : Type*) [CommRing R] [IsRegularLocalRing R] :
    ((Submodule.spanFinrank (maximalIdeal R) : ℕ) : WithBot ℕ∞) = ringKrullDim R := by
  exact IsRegularLocalRing.spanFinrank_maximalIdeal
theorem finrank_cotangentSpace_le_spanFinrank (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    Module.finrank (ResidueField R) (CotangentSpace R) ≤ Submodule.spanFinrank (maximalIdeal R) := by
  exact (IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace R).ge
theorem ringKrullDim_le_quot_span_add_one {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {x : R} (hx : x ∈ maximalIdeal R) :
    ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 := by
  have h1 : Submodule.spanFinrank (Ideal.span ({x} : Set R)) ≤ 1 := by
    have := spanFinrank_span_finset_le ({x} : Finset R)
    simpa only [Finset.coe_singleton, Finset.card_singleton] using this
  have hle : Ideal.span ({x} : Set R) ≤ maximalIdeal R :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)
  have hjac : maximalIdeal R ≤ Ring.jacobson R := by
    rw [← Ideal.jacobson_bot]
    exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  have h := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank (Ideal.span ({x} : Set R)) (hle.trans hjac)
  refine h.trans ?_
  gcongr
  exact (natCast_withBot_enat_le_iff.mpr h1).trans_eq Nat.cast_one
theorem ringKrullDim_le_spanFinrank_maximalIdeal' (S : Type*) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] :
    ringKrullDim S ≤ ((Submodule.spanFinrank (maximalIdeal S) : ℕ) : WithBot ℕ∞) := by
  exact ringKrullDim_le_spanFinrank_maximalIdeal S
theorem spanFinrank_quotient_eq_and_ringKrullDim_add_one (R : Type*) [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ∈ maximalIdeal R)
    (hx2 : x ∉ maximalIdeal R ^ 2) [IsLocalRing (R ⧸ Ideal.span ({x} : Set R))] :
    ((Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) : ℕ) : WithBot ℕ∞)
        = ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) ∧
      ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 = ringKrullDim R := by
  have hreg := spanFinrank_maximalIdeal_eq_ringKrullDim R
  have h5 := spanFinrank_maximalIdeal_quotient_succ_le R hx hx2
  have hfr := finrank_cotangentSpace_le_spanFinrank R
  have hA := ringKrullDim_le_quot_span_add_one hx
  have hB := ringKrullDim_le_spanFinrank_maximalIdeal' (R ⧸ Ideal.span ({x} : Set R))
  obtain ⟨e1, e2⟩ := eq_natCast_and_add_one_eq_of_le (by rw [hreg]; exact hA) hB (by omega)
  exact ⟨e1.symm, e2.trans hreg⟩
theorem isPrime_of_mem_minimalPrimes {R : Type*} [CommRing R] {p : Ideal R}
    (hp : p ∈ minimalPrimes R) : p.IsPrime := by
  exact Ideal.IsMinimalPrime.isPrime hp
theorem le_of_le_of_mem_minimalPrimes {R : Type*} [CommRing R] {p q : Ideal R}
    (hp : p ∈ minimalPrimes R) (hq : q.IsPrime) (hle : q ≤ p) : p ≤ q := by
  exact hp.2 ⟨hq, bot_le⟩ hle
theorem isDomain_of_maximalIdeal_eq_bot (R : Type*) [CommRing R] [IsLocalRing R]
    (h : maximalIdeal R = ⊥) : IsDomain R := by
  have hu : ∀ a : R, a ≠ 0 → IsUnit a := fun a ha => by
    by_contra hna
    apply ha
    have hm : a ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal a).mpr hna
    rw [h] at hm
    exact (Ideal.mem_bot).mp hm
  have : NoZeroDivisors R := ⟨fun {a b} hab => by
    by_cases ha : a = 0
    · exact Or.inl ha
    · exact Or.inr ((hu a ha).mul_right_eq_zero.mp hab)⟩
  exact NoZeroDivisors.to_isDomain _
theorem maximalIdeal_eq_bot_of_le_sq (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (h : maximalIdeal R ≤ maximalIdeal R ^ 2) : maximalIdeal R = ⊥ := by
  apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (maximalIdeal R)
    (IsNoetherian.noetherian _)
  · rw [pow_two] at h
    exact h
  · exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
theorem exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes (R : Type*) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (hsq : ¬ maximalIdeal R ≤ maximalIdeal R ^ 2)
    (hmin : ¬ ∃ p ∈ minimalPrimes R, maximalIdeal R ≤ p) :
    ∃ x, x ∈ maximalIdeal R ∧ x ∉ maximalIdeal R ^ 2 ∧ ∀ p ∈ minimalPrimes R, x ∉ p := by
  classical
  have hfin : (minimalPrimes R).Finite := by
    exact minimalPrimes.finite_of_isNoetherianRing R
  have hprime : ∀ i ∈ insert (maximalIdeal R ^ 2) hfin.toFinset, i ≠ maximalIdeal R ^ 2 →
      i ≠ maximalIdeal R ^ 2 → (id i).IsPrime := by
    intro i hi hne _
    rw [Finset.mem_insert] at hi
    rcases hi with h | h
    · exact absurd h hne
    · exact isPrime_of_mem_minimalPrimes (hfin.mem_toFinset.mp h)
  have hiff : ((maximalIdeal R : Set R) ⊆ ⋃ i ∈ ((insert (maximalIdeal R ^ 2) hfin.toFinset : Finset (Ideal R)) : Set (Ideal R)), id i) ↔
      ∃ i ∈ insert (maximalIdeal R ^ 2) hfin.toFinset, maximalIdeal R ≤ id i := by
    exact Ideal.subset_union_prime (s := insert (maximalIdeal R ^ 2) hfin.toFinset) (f := id)
      (maximalIdeal R ^ 2) (maximalIdeal R ^ 2) hprime
  have key := hiff.not.mpr (by
      rintro ⟨i, hi, hle⟩
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | h
      · exact hsq hle
      · exact hmin ⟨i, hfin.mem_toFinset.mp h, hle⟩)
  rw [Set.not_subset] at key
  obtain ⟨x, hx, hxu⟩ := key
  simp only [Set.mem_iUnion, not_exists, id, SetLike.mem_coe] at hxu
  exact ⟨x, hx, fun h => hxu _ (Finset.mem_insert_self _ _) h,
    fun p hp h => hxu p (Finset.mem_insert_of_mem (hfin.mem_toFinset.mpr hp)) h⟩
theorem quotient_span_singleton {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hx2 : x ∉ IsLocalRing.maximalIdeal R ^ 2) :
    IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)) := by
  have := isLocalRing_quotient_span_singleton hx
  have h7 := spanFinrank_quotient_eq_and_ringKrullDim_add_one R hx hx2
  exact { spanFinrank_maximalIdeal := h7.1 }
theorem natCast_withBot_enat_eq_iff {a b : ℕ} :
    ((a : ℕ) : WithBot ℕ∞) = ((b : ℕ) : WithBot ℕ∞) ↔ a = b := by
  exact Nat.cast_inj
theorem isDomain_of_isPrime_bot {R : Type*} [CommRing R] [Nontrivial R]
    (h : (⊥ : Ideal R).IsPrime) : IsDomain R := by
  have : NoZeroDivisors R := ⟨fun {a b} hab => by
    have := h.mem_or_mem (show a * b ∈ (⊥ : Ideal R) from (Ideal.mem_bot).mpr hab)
    simpa only [Ideal.mem_bot] using this⟩
  exact NoZeroDivisors.to_isDomain _
theorem ringKrullDim_le_zero_of_maximalIdeal_minimal {R : Type*} [CommRing R] [IsLocalRing R]
    (h : maximalIdeal R ∈ minimalPrimes R) : ringKrullDim R ≤ 0 := by
  show Order.krullDim (PrimeSpectrum R) ≤ 0
  rw [Order.krullDim_nonpos_iff_forall_isMax]
  intro q r _
  have h1 : r.asIdeal ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal r.isPrime.ne_top
  have h2 : maximalIdeal R ≤ q.asIdeal :=
    le_of_le_of_mem_minimalPrimes h q.isPrime (IsLocalRing.le_maximalIdeal q.isPrime.ne_top)
  exact h1.trans h2
theorem isDomain_of_forall_spanFinrank_lt (R : Type u) [CommRing R]
    [IsRegularLocalRing R]
    (IH : ∀ (S : Type u) [CommRing S] [IsRegularLocalRing S],
      Submodule.spanFinrank (maximalIdeal S) < Submodule.spanFinrank (maximalIdeal R) →
        IsDomain S) :
    IsDomain R := by
  classical
  by_cases hsq : maximalIdeal R ≤ maximalIdeal R ^ 2
  · exact isDomain_of_maximalIdeal_eq_bot R (maximalIdeal_eq_bot_of_le_sq R hsq)
  obtain ⟨y, hy, hy2⟩ := SetLike.not_le_iff_exists.mp hsq
  have hdimR : ∃ d : ℕ, ((d + 1 : ℕ) : WithBot ℕ∞) = ringKrullDim R := by
    have := isLocalRing_quotient_span_singleton hy
    have h7 := spanFinrank_quotient_eq_and_ringKrullDim_add_one R hy hy2
    exact ⟨_, by rw [← h7.2, ← h7.1]; exact Nat.cast_succ _⟩
  by_cases hmin : ∃ p ∈ minimalPrimes R, maximalIdeal R ≤ p
  · exfalso
    obtain ⟨p, hp, hle⟩ := hmin
    have hpm : p = maximalIdeal R :=
      le_antisymm (IsLocalRing.le_maximalIdeal (isPrime_of_mem_minimalPrimes hp).ne_top) hle
    subst hpm
    have h0 := ringKrullDim_le_zero_of_maximalIdeal_minimal hp
    obtain ⟨d, hd⟩ := hdimR
    rw [← hd, ← Nat.cast_zero] at h0
    have := natCast_withBot_enat_le_iff.mp h0
    omega
  obtain ⟨x, hx, hx2, hxp⟩ := exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes R hsq hmin
  have := isLocalRing_quotient_span_singleton hx
  have h7 := spanFinrank_quotient_eq_and_ringKrullDim_add_one R hx hx2
  have := quotient_span_singleton hx hx2
  have hlt : Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) <
      Submodule.spanFinrank (maximalIdeal R) := by
    have e := h7.2
    rw [← h7.1, ← spanFinrank_maximalIdeal_eq_ringKrullDim R, ← Nat.cast_succ] at e
    have := natCast_withBot_enat_eq_iff.mp e
    omega
  have hQ : IsDomain (R ⧸ Ideal.span ({x} : Set R)) := IH _ hlt
  have hprime : (Ideal.span ({x} : Set R)).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp hQ
  obtain ⟨p, hp, hpx⟩ := Ideal.exists_minimalPrimes_le
    (show (⊥ : Ideal R) ≤ Ideal.span ({x} : Set R) from bot_le)
  have hpP := isPrime_of_mem_minimalPrimes hp
  have hxp' : x ∉ p := hxp p hp
  have hle : p ≤ Ideal.span ({x} : Set R) • p := by
    intro z hz
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp (hpx hz)
    have ha : a ∈ p := (hpP.mem_or_mem hz).resolve_right hxp'
    have hs : x * a ∈ Ideal.span ({x} : Set R) • p :=
      Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) ha
    rw [mul_comm a x]
    exact hs
  have hjac : Ideal.span ({x} : Set R) ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)
  have hbot : p = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ (IsNoetherian.noetherian p) hle hjac
  rw [hbot] at hpP
  exact isDomain_of_isPrime_bot hpP
theorem isDomain_of_spanFinrank_le :
    ∀ (n : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R],
      Submodule.spanFinrank (maximalIdeal R) ≤ n → IsDomain R := by
  intro n
  induction n with
  | zero =>
    intro R _ _ h
    exact isDomain_of_forall_spanFinrank_lt R (fun S _ _ hS => absurd hS (by omega))
  | succ n ih =>
    intro R _ _ h
    exact isDomain_of_forall_spanFinrank_lt R (fun S _ _ hS => ih S (by omega))
theorem isDomain (R : Type*) [CommRing R]
    [IsRegularLocalRing R] : IsDomain R := by
  exact isDomain_of_spanFinrank_le (Submodule.spanFinrank (maximalIdeal R)) R le_rfl
instance (priority := 100) instIsDomain {R : Type*} [CommRing R]
    [IsRegularLocalRing R] : IsDomain R :=
  IsRegularLocalRing.isDomain R
end IsRegularLocalRing
end PI.UnitaryGroupMassFormula.RLRS


