-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_RegularLocalRing
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_RegularLocalRing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:40.188206+00:00
-- url     : https://prove2.me/theorems/b33437fe-1e48-4c21-a333-46399ec32be3
-- title:
--   Regular Local Ring
-- statement:
--   Definitions and structural lemmas for Regular Local Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/RegularLocalRing.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace IsRegularLocalRing
open IsLocalRing
universe u
theorem spanFinrank_span_finset_le_card {R : Type*} [CommRing R] (s : Finset R) :
    Submodule.spanFinrank (Ideal.span (s : Set R)) ≤ s.card := by
  have h2 : (Ideal.span (s : Set R)).FG := Submodule.fg_span s.finite_toSet
  have h1 : (Ideal.span (s : Set R)).spanRank ≤ Cardinal.mk ((s : Set R)) :=
    Submodule.spanRank_span_le_card _
  rw [Submodule.FG.spanRank_eq_spanFinrank h2] at h1
  have h3 : Cardinal.mk ((s : Set R)) = (s.card : Cardinal) := by simp
  rw [h3] at h1
  exact_mod_cast h1
theorem exists_repr_ne_zero {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (b : Module.Basis ι K V) {v : V} (hv : v ≠ 0) : ∃ j, b.repr v j ≠ 0 := by
  by_contra h
  push Not at h
  have h0 : b.repr v = 0 := by
    ext j
    simp [h j]
  apply hv
  have h1 := congrArg (b.repr.symm) h0
  simpa using h1
theorem span_insert_image_erase_eq_top {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {N : ℕ} (b : Module.Basis (Fin N) K V) (v : V) {j : Fin N}
    (hj : b.repr v j ≠ 0) :
    Submodule.span K (insert v (⇑b '' ↑(Finset.univ.erase j))) = ⊤ := by
  rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  simp only [SetLike.mem_coe]
  by_cases hij : i = j
  · rw [hij]
    have hmem1 : v ∈ Submodule.span K (insert v (⇑b '' ↑(Finset.univ.erase j))) :=
      Submodule.subset_span (Set.mem_insert _ _)
    have hmem2 : ∑ l ∈ Finset.univ.erase j, b.repr v l • b l ∈
        Submodule.span K (insert v (⇑b '' ↑(Finset.univ.erase j))) := by
      refine Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ ?_
      exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨l, Finset.mem_coe.mpr hl, rfl⟩)
    have hsub : v - ∑ l ∈ Finset.univ.erase j, b.repr v l • b l = b.repr v j • b j := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ j), b.sum_repr v]
      abel
    have hkey : b.repr v j • b j ∈
        Submodule.span K (insert v (⇑b '' ↑(Finset.univ.erase j))) := by
      rw [← hsub]
      exact Submodule.sub_mem _ hmem1 hmem2
    have h2 := Submodule.smul_mem _ (b.repr v j)⁻¹ hkey
    rwa [smul_smul, inv_mul_cancel₀ hj, one_smul] at h2
  · exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨i, by simp [hij], rfl⟩)
theorem isLocalRing_quotient_span_singleton {R : Type*} [CommRing R] [IsLocalRing R]
    {x : R} (hx : x ∈ maximalIdeal R) : IsLocalRing (R ⧸ Ideal.span ({x} : Set R)) := by
  have hIle : Ideal.span ({x} : Set R) ≤ maximalIdeal R := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hx
  have hIne : Ideal.span ({x} : Set R) ≠ ⊤ := by
    intro h
    rw [h, top_le_iff] at hIle
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top hIle
  have hone : (1 : R ⧸ Ideal.span ({x} : Set R)) ≠ 0 := by
    intro h
    have h1 : (1 : R) ∈ Ideal.span ({x} : Set R) := by
      rwa [← Ideal.Quotient.eq_zero_iff_mem, map_one]
    exact hIne ((Ideal.eq_top_iff_one _).mpr h1)
  have : Nontrivial (R ⧸ Ideal.span ({x} : Set R)) := ⟨⟨1, 0, hone⟩⟩
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
theorem spanFinrank_maximalIdeal_quotient_add_one_le_finrank (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2)
    [IsLocalRing (R ⧸ Ideal.span ({x} : Set R))] :
    Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) + 1 ≤
      Module.finrank (ResidueField R) (CotangentSpace R) := by
  classical
  have hv0 : (maximalIdeal R).toCotangent ⟨x, hx⟩ ≠ 0 := by
    rw [Ne, Ideal.toCotangent_eq_zero]
    exact hx2
  obtain ⟨j, hj⟩ := exists_repr_ne_zero (Module.finBasis (ResidueField R) (CotangentSpace R)) hv0
  obtain ⟨z, hz⟩ : ∃ z : Fin (Module.finrank (ResidueField R) (CotangentSpace R)) →
      (maximalIdeal R), ∀ i, (maximalIdeal R).toCotangent (z i) =
        Module.finBasis (ResidueField R) (CotangentSpace R) i := by
    have hsurj : Function.Surjective (maximalIdeal R).toCotangent :=
      Ideal.toCotangent_surjective _
    choose z hz using fun i => hsurj (Module.finBasis (ResidueField R) (CotangentSpace R) i)
    exact ⟨z, hz⟩
  set s : Set (maximalIdeal R) :=
    insert (⟨x, hx⟩ : maximalIdeal R) (z '' ↑(Finset.univ.erase j)) with hsdef
  have htop : Submodule.span R s = ⊤ := by
    rw [← IsLocalRing.CotangentSpace.span_image_eq_top_iff]
    have himg : (maximalIdeal R).toCotangent '' s =
        insert ((maximalIdeal R).toCotangent ⟨x, hx⟩)
          (⇑(Module.finBasis (ResidueField R) (CotangentSpace R)) ''
            ↑(Finset.univ.erase j)) := by
      rw [hsdef, Set.image_insert_eq, Set.image_image]
      simp [hz]
    rw [himg]
    exact span_insert_image_erase_eq_top _ _ hj
  have hmspan : Ideal.span ((Subtype.val : maximalIdeal R → R) '' s) = maximalIdeal R := by
    have h := congrArg (Submodule.map (maximalIdeal R).subtype) htop
    rw [Submodule.map_span, Submodule.map_subtype_top] at h
    simpa using h
  have hIle : Ideal.span ({x} : Set R) ≤ maximalIdeal R := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hx
  have hmapS : maximalIdeal (R ⧸ Ideal.span ({x} : Set R)) =
      Ideal.map (Ideal.Quotient.mk (Ideal.span ({x} : Set R))) (maximalIdeal R) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
      refine Ideal.mem_map_of_mem _ ?_
      by_contra hr
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hr
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy
      exact hy (hr.map (Ideal.Quotient.mk (Ideal.span ({x} : Set R))))
    · refine IsLocalRing.le_maximalIdeal ?_
      intro h
      rw [Ideal.eq_top_iff_one, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at h
      obtain ⟨r, hrm, hr1⟩ := h
      have h2 : r - 1 ∈ Ideal.span ({x} : Set R) := by
        rw [← Ideal.Quotient.eq]
        simpa using hr1
      have h3 : (1 : R) ∈ maximalIdeal R := by
        have h4 := sub_mem hrm (hIle h2)
        simp at h4
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h3)
  have hx0 : Ideal.Quotient.mk (Ideal.span ({x} : Set R)) x = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x)
  have himg : (Ideal.Quotient.mk (Ideal.span ({x} : Set R))) ''
      ((Subtype.val : maximalIdeal R → R) '' s) =
      insert 0 ((fun i => Ideal.Quotient.mk (Ideal.span ({x} : Set R)) ((z i : R))) ''
        ↑(Finset.univ.erase j)) := by
    rw [hsdef, Set.image_image, Set.image_insert_eq, Set.image_image]
    simp [hx0]
  have hquot : maximalIdeal (R ⧸ Ideal.span ({x} : Set R)) =
      Ideal.span ((fun i => Ideal.Quotient.mk (Ideal.span ({x} : Set R)) ((z i : R))) ''
        ↑(Finset.univ.erase j)) := by
    rw [hmapS]
    conv_lhs => rw [← hmspan]
    rw [Ideal.map_span, himg]
    exact Submodule.span_insert_zero
  have hcard : Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) ≤
      (Finset.univ.erase j).card := by
    rw [hquot, ← Finset.coe_image]
    exact le_trans (spanFinrank_span_finset_le_card _) Finset.card_image_le
  have hjpos : 0 < Module.finrank (ResidueField R) (CotangentSpace R) := Fin.pos j
  have hcard2 : (Finset.univ.erase j).card =
      Module.finrank (ResidueField R) (CotangentSpace R) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  omega
theorem eq_natCast_and_add_one_eq_of_le {a : WithBot ℕ∞} {d n : ℕ}
    (h1 : ((n : ℕ) : WithBot ℕ∞) ≤ a + 1) (h2 : a ≤ ((d : ℕ) : WithBot ℕ∞)) (h3 : d + 1 ≤ n) :
    a = ((d : ℕ) : WithBot ℕ∞) ∧ a + 1 = ((n : ℕ) : WithBot ℕ∞) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, a = ((m : ℕ) : WithBot ℕ∞) := by
    induction a using WithBot.recBotCoe with
    | bot =>
      exfalso
      rw [WithBot.bot_add, le_bot_iff] at h1
      exact WithBot.natCast_ne_bot n h1
    | coe e =>
      induction e using ENat.recTopCoe with
      | top =>
        exfalso
        have h2' : (⊤ : ℕ∞) ≤ (d : ℕ∞) := by exact_mod_cast h2
        simp at h2'
      | coe m => exact ⟨m, by norm_cast⟩
  have hmd : m ≤ d := by exact_mod_cast h2
  have hnm : n ≤ m + 1 := by exact_mod_cast h1
  have hm : m = d := by omega
  have hn : n = m + 1 := by omega
  refine ⟨?_, ?_⟩
  · rw [hm]
  · rw [hn]
    norm_cast
theorem spanFinrank_quotient_eq_ringKrullDim_and_add_one_eq (R : Type*) [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ∈ maximalIdeal R)
    (hx2 : x ∉ maximalIdeal R ^ 2) [IsLocalRing (R ⧸ Ideal.span ({x} : Set R))] :
    ((Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) : ℕ) : WithBot ℕ∞)
        = ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) ∧
      ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 = ringKrullDim R := by
  have hdn := spanFinrank_maximalIdeal_quotient_add_one_le_finrank R hx hx2
  have hRdim : ((Module.finrank (ResidueField R) (CotangentSpace R) : ℕ) : WithBot ℕ∞)
      = ringKrullDim R := by
    rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
    exact_mod_cast IsRegularLocalRing.spanFinrank_maximalIdeal
  have hdimQuot : ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) ≤
      ((Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) : ℕ) :
        WithBot ℕ∞) := by
    exact_mod_cast ringKrullDim_le_spanFinrank_maximalIdeal (R ⧸ Ideal.span ({x} : Set R))
  have hIj : Ideal.span ({x} : Set R) ≤ Ring.jacobson R := by
    refine le_trans ?_ (IsLocalRing.ringJacobson_eq_maximalIdeal R).ge
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hx
  have hdimLe := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank
      (Ideal.span ({x} : Set R)) hIj
  have h1 : Submodule.spanFinrank (Ideal.span ({x} : Set R)) ≤ 1 := by
    have h := spanFinrank_span_finset_le_card ({x} : Finset R)
    simpa using h
  have hcast : ((Submodule.spanFinrank (Ideal.span ({x} : Set R)) : ℕ) : WithBot ℕ∞) ≤ 1 := by
    exact_mod_cast h1
  have hdimSucc : ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 :=
    hdimLe.trans (add_le_add le_rfl hcast)
  obtain ⟨hA, hB⟩ := eq_natCast_and_add_one_eq_of_le
    (d := Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))))
    (n := Module.finrank (ResidueField R) (CotangentSpace R))
    (by rw [hRdim]; exact hdimSucc) hdimQuot hdn
  refine ⟨hA.symm, ?_⟩
  rw [hB, hRdim]
theorem isPrime_of_mem_minimalPrimes {R : Type*} [CommRing R] {p : Ideal R}
    (hp : p ∈ minimalPrimes R) : p.IsPrime := hp.1.1
theorem le_of_le_of_mem_minimalPrimes {R : Type*} [CommRing R] {p q : Ideal R}
    (hp : p ∈ minimalPrimes R) (hq : q.IsPrime) (hle : q ≤ p) : p ≤ q :=
  hp.2 ⟨hq, bot_le⟩ hle
theorem isDomain_of_maximalIdeal_eq_bot (R : Type*) [CommRing R] [IsLocalRing R]
    (h : maximalIdeal R = ⊥) : IsDomain R := by
  have hp : (maximalIdeal R).IsPrime := (maximalIdeal.isMaximal R).isPrime
  rw [h] at hp
  have := hp
  exact IsDomain.of_bot_isPrime R
theorem maximalIdeal_eq_bot_of_le_sq (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (h : maximalIdeal R ≤ maximalIdeal R ^ 2) : maximalIdeal R = ⊥ := by
  refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (maximalIdeal R)
    (IsNoetherian.noetherian _) ?_ (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  show maximalIdeal R ≤ maximalIdeal R * maximalIdeal R
  rw [← pow_two]
  exact h
theorem exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes (R : Type*) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (hsq : ¬ maximalIdeal R ≤ maximalIdeal R ^ 2)
    (hmin : ¬ ∃ p ∈ minimalPrimes R, maximalIdeal R ≤ p) :
    ∃ x, x ∈ maximalIdeal R ∧ x ∉ maximalIdeal R ^ 2 ∧ ∀ p ∈ minimalPrimes R, x ∉ p := by
  classical
  obtain ⟨t, ht⟩ := (minimalPrimes.finite_of_isNoetherianRing R).exists_finset_coe
  by_contra hcon
  push Not at hcon
  have hsub : (maximalIdeal R : Set R) ⊆
      ⋃ i ∈ ((insert (maximalIdeal R ^ 2) t : Finset (Ideal R)) : Set (Ideal R)), (i : Set R) := by
    intro y hy
    rcases em (y ∈ maximalIdeal R ^ 2) with hm2 | hm2
    · exact Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_insert_self _ _)) hm2
    · obtain ⟨p, hp, hyp⟩ := hcon y hy hm2
      have hpt : p ∈ insert (maximalIdeal R ^ 2) t := by
        apply Finset.mem_insert_of_mem
        rw [← Finset.mem_coe, ht]
        exact hp
      exact Set.mem_biUnion (Finset.mem_coe.mpr hpt) hyp
  have hp : ∀ i ∈ (insert (maximalIdeal R ^ 2) t : Finset (Ideal R)),
      i ≠ maximalIdeal R ^ 2 → i ≠ maximalIdeal R ^ 2 → i.IsPrime := by
    intro i hi h1 _
    have hit : i ∈ t := by
      rcases Finset.mem_insert.mp hi with hh | hh
      · exact absurd hh h1
      · exact hh
    refine isPrime_of_mem_minimalPrimes ?_
    rw [← ht]
    exact Finset.mem_coe.mpr hit
  obtain ⟨i, hi, hle⟩ := (Ideal.subset_union_prime _ _ hp).mp hsub
  rcases Finset.mem_insert.mp hi with hh | hh
  · subst hh
    exact hsq hle
  · refine hmin ⟨i, ?_, hle⟩
    rw [← ht]
    exact Finset.mem_coe.mpr hh
theorem isRegularLocalRing_quotient_span_singleton {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hx2 : x ∉ IsLocalRing.maximalIdeal R ^ 2) :
    IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)) := by
  have := isLocalRing_quotient_span_singleton hx
  rw [isRegularLocalRing_iff]
  exact_mod_cast (spanFinrank_quotient_eq_ringKrullDim_and_add_one_eq R hx hx2).1
theorem isDomain_of_forall_spanFinrank_lt (R : Type u) [CommRing R]
    [IsRegularLocalRing R]
    (IH : ∀ (S : Type u) [CommRing S] [IsRegularLocalRing S],
      Submodule.spanFinrank (maximalIdeal S) < Submodule.spanFinrank (maximalIdeal R) →
        IsDomain S) :
    IsDomain R := by
  classical
  by_cases hsq : maximalIdeal R ≤ maximalIdeal R ^ 2
  · exact isDomain_of_maximalIdeal_eq_bot R (maximalIdeal_eq_bot_of_le_sq R hsq)
  by_cases hmin : ∃ p ∈ minimalPrimes R, maximalIdeal R ≤ p
  · exfalso
    obtain ⟨p, hp, hple⟩ := hmin
    have hpp : p.IsPrime := isPrime_of_mem_minimalPrimes hp
    have hpm : p = maximalIdeal R := le_antisymm (IsLocalRing.le_maximalIdeal hpp.ne_top) hple
    have hallideal : ∀ q : Ideal R, q.IsPrime → q = maximalIdeal R := by
      intro q hq
      refine le_antisymm (IsLocalRing.le_maximalIdeal hq.ne_top) ?_
      rw [← hpm]
      exact le_of_le_of_mem_minimalPrimes hp hq
        (by rw [hpm]; exact IsLocalRing.le_maximalIdeal hq.ne_top)
    have h2 : ringKrullDim R ≤ 0 := by
      have hPQ : ∀ P Q : PrimeSpectrum R, P = Q := by
        intro P Q
        apply PrimeSpectrum.ext
        rw [hallideal P.asIdeal P.isPrime, hallideal Q.asIdeal Q.isPrime]
      have : Subsingleton (PrimeSpectrum R) := ⟨hPQ⟩
      exact Order.krullDim_nonpos_of_subsingleton
    obtain ⟨x, hx, hx2⟩ : ∃ x, x ∈ maximalIdeal R ∧ x ∉ maximalIdeal R ^ 2 := by
      by_contra hc
      push Not at hc
      exact hsq fun y hy => hc y hy
    have := isLocalRing_quotient_span_singleton hx
    have hpos := spanFinrank_maximalIdeal_quotient_add_one_le_finrank R hx hx2
    have hdim : ringKrullDim R =
        (Module.finrank (ResidueField R) (CotangentSpace R) : WithBot ℕ∞) :=
      ((IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance).symm
    rw [hdim] at h2
    have hle0 : Module.finrank (ResidueField R) (CotangentSpace R) ≤ 0 := by exact_mod_cast h2
    omega
  · obtain ⟨x, hx, hx2, hxp⟩ :=
      exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes R hsq hmin
    have := isLocalRing_quotient_span_singleton hx
    have hrq : IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)) :=
      isRegularLocalRing_quotient_span_singleton hx hx2
    have hlt : Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) <
        Submodule.spanFinrank (maximalIdeal R) := by
      have h1 := spanFinrank_maximalIdeal_quotient_add_one_le_finrank R hx hx2
      have h2 : Submodule.spanFinrank (maximalIdeal R)
          = Module.finrank (ResidueField R) (CotangentSpace R) := by
        rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
      omega
    have hdom := IH (R ⧸ Ideal.span ({x} : Set R)) hlt
    have hprime : (Ideal.span ({x} : Set R)).IsPrime :=
      (Ideal.Quotient.isDomain_iff_prime _).mp hdom
    obtain ⟨p, hp, hple⟩ :=
      Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal R) ≤ Ideal.span ({x} : Set R))
    have hpp : p.IsPrime := isPrime_of_mem_minimalPrimes hp
    have hpbot : p = ⊥ := by
      refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) p
        (IsNoetherian.noetherian p) ?_ (IsLocalRing.maximalIdeal_le_jacobson ⊥)
      intro y hy
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp (hple hy)
      have ha : a ∈ p := by
        rcases hpp.mem_or_mem hy with hh | hh
        · exact absurd hh (hxp p hp)
        · exact hh
      exact Ideal.mul_mem_mul hx ha
    rw [hpbot] at hpp
    have := hpp
    exact IsDomain.of_bot_isPrime R
theorem isDomain_of_spanFinrank_le :
    ∀ (n : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R],
      Submodule.spanFinrank (maximalIdeal R) ≤ n → IsDomain R := by
  intro n
  induction n with
  | zero =>
    intro R _ _ h
    refine isDomain_of_forall_spanFinrank_lt R ?_
    intro S _ _ hS
    exact absurd (lt_of_lt_of_le hS h) (Nat.not_lt_zero _)
  | succ n IH =>
    intro R _ _ h
    refine isDomain_of_forall_spanFinrank_lt R ?_
    intro S _ _ hS
    exact IH S (by omega)
theorem _root_.P2M_RH_IsRegularLocalRing_isDomain_230c370e09fbca01 (R : Type*) [CommRing R]
    [IsRegularLocalRing R] : IsDomain R :=
  isDomain_of_spanFinrank_le (Submodule.spanFinrank (IsLocalRing.maximalIdeal R)) R le_rfl

alias isDomain := _root_.P2M_RH_IsRegularLocalRing_isDomain_230c370e09fbca01
instance (priority := 100) instIsDomain {R : Type*} [CommRing R]
    [IsRegularLocalRing R] : IsDomain R :=
  IsRegularLocalRing.isDomain R
end IsRegularLocalRing


