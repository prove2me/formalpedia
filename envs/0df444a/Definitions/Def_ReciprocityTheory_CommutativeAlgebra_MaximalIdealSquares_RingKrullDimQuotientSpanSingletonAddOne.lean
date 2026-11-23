-- Prove2me | Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
-- name    : ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:21.225538+00:00
-- url     : https://prove2.me/theorems/1fea5aab-05b6-474e-91d7-3d19a51a0d87
-- title:
--   Ring Krull Dim Quotient Span Singleton Add One
-- statement:
--   Definitions and structural lemmas for Ring Krull Dim Quotient Span Singleton Add One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/MaximalIdealSquares/RingKrullDimQuotientSpanSingletonAddOne.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.CA.AB.RegA
namespace IsRegularLocalRing
open IsLocalRing
universe u
theorem spanFinrank_span_finset_le {R : Type*} [CommRing R] (s : Finset R) :
    Submodule.spanFinrank (Ideal.span (s : Set R)) ≤ s.card := by
  calc Submodule.spanFinrank (Ideal.span (s : Set R)) ≤ (s : Set R).ncard :=
        Submodule.spanFinrank_span_le_ncard_of_finite s.finite_toSet
    _ = s.card := Set.ncard_coe_finset s
theorem exists_repr_ne_zero {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (b : Module.Basis ι K V) {v : V} (hv : v ≠ 0) : ∃ j, b.repr v j ≠ 0 := by
  by_contra h
  push_neg at h
  exact hv (b.repr.map_eq_zero_iff.mp (Finsupp.ext fun j => by simpa using h j))
theorem span_insert_image_erase_eq_top {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {N : ℕ} (b : Module.Basis (Fin N) K V) (v : V) {j : Fin N}
    (hj : b.repr v j ≠ 0) :
    Submodule.span K (insert v (⇑b '' ↑(Finset.univ.erase j))) = ⊤ := by
  classical
  set W := Submodule.span K (insert v (⇑b '' ↑(Finset.univ.erase j))) with hW
  have hbi : ∀ i, i ≠ j → b i ∈ W := fun i hi =>
    Submodule.subset_span (Set.mem_insert_of_mem _ ⟨i, by simp [hi], rfl⟩)
  have hvW : v ∈ W := Submodule.subset_span (Set.mem_insert _ _)
  have hbj : b j ∈ W := by
    have hsum := b.sum_repr v
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at hsum
    have h2 : (∑ i ∈ Finset.univ.erase j, b.repr v i • b i) ∈ W :=
      Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (hbi i (Finset.ne_of_mem_erase hi))
    have h3 : b.repr v j • b j ∈ W := by
      rw [eq_sub_of_add_eq hsum]
      exact Submodule.sub_mem _ hvW h2
    have h4 := Submodule.smul_mem W (b.repr v j)⁻¹ h3
    rwa [smul_smul, inv_mul_cancel₀ hj, one_smul] at h4
  rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  by_cases hi : i = j
  · rw [hi]; exact hbj
  · exact hbi i hi
theorem isLocalRing_quotient_span_singleton {R : Type*} [CommRing R] [IsLocalRing R]
    {x : R} (hx : x ∈ maximalIdeal R) : IsLocalRing (R ⧸ Ideal.span ({x} : Set R)) := by
  have hI : Ideal.span ({x} : Set R) ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact (IsLocalRing.mem_maximalIdeal x).mp hx
  have : Nontrivial (R ⧸ Ideal.span ({x} : Set R)) := by
    first
    | exact Ideal.Quotient.nontrivial_iff.mpr hI
    | exact ⟨⟨0, 1, fun h => hI ((Ideal.eq_top_iff_one _).mpr
        (Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_one]; exact h.symm)))⟩⟩
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
theorem spanFinrank_maximalIdeal_quotient_succ_le (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2)
    [IsLocalRing (R ⧸ Ideal.span ({x} : Set R))] :
    Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) + 1 ≤
      Module.finrank (ResidueField R) (CotangentSpace R) := by
  classical
  have hne : (maximalIdeal R).toCotangent ⟨x, hx⟩ ≠ 0 := fun h =>
    hx2 ((Ideal.toCotangent_eq_zero _ _).mp h)
  obtain ⟨j, hj⟩ := exists_repr_ne_zero (Module.finBasis (ResidueField R) (CotangentSpace R)) hne
  have hspan := span_insert_image_erase_eq_top
    (Module.finBasis (ResidueField R) (CotangentSpace R)) _ hj
  choose y hy using fun i => Ideal.toCotangent_surjective (maximalIdeal R)
    (Module.finBasis (ResidueField R) (CotangentSpace R) i)
  have htop : Submodule.span R
      (insert (⟨x, hx⟩ : maximalIdeal R) (y '' ↑(Finset.univ.erase j))) = ⊤ := by
    apply IsLocalRing.CotangentSpace.span_image_eq_top_iff.mp
    rw [Set.image_insert_eq, Set.image_image]
    simp only [hy]
    exact hspan
  have hm : Ideal.span (Subtype.val ''
      (insert (⟨x, hx⟩ : maximalIdeal R) (y '' ↑(Finset.univ.erase j)))) = maximalIdeal R := by
    have h1 := congrArg (Submodule.map (maximalIdeal R).subtype) htop
    first
    | rw [Submodule.map_span, Submodule.map_subtype_top] at h1
    | rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at h1
    first
    | exact h1
    | simpa using h1
  have hcomap : (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))).comap (Ideal.Quotient.mk (Ideal.span ({x} : Set R))) = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
  have hmax : maximalIdeal (R ⧸ Ideal.span ({x} : Set R)) = Ideal.map (Ideal.Quotient.mk (Ideal.span ({x} : Set R))) (Ideal.span (Subtype.val ''
      (insert (⟨x, hx⟩ : maximalIdeal R) (y '' ↑(Finset.univ.erase j))))) := by
    rw [hm, ← hcomap, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  have hx0 : Ideal.Quotient.mk (Ideal.span ({x} : Set R)) x = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x)
  have hset : (Ideal.Quotient.mk (Ideal.span ({x} : Set R))) '' (Subtype.val ''
      (insert (⟨x, hx⟩ : maximalIdeal R) (y '' ↑(Finset.univ.erase j)))) =
      insert 0 (↑((Finset.univ.erase j).image (fun i => Ideal.Quotient.mk (Ideal.span ({x} : Set R)) (y i : R))) : Set (R ⧸ Ideal.span ({x} : Set R))) := by
    simp only [Set.image_insert_eq, Set.image_image, Finset.coe_image, Subtype.coe_mk, hx0]
  rw [hmax, Ideal.map_span, hset]
  have hz : Ideal.span (insert (0 : (R ⧸ Ideal.span ({x} : Set R)))
      (↑((Finset.univ.erase j).image (fun i => Ideal.Quotient.mk (Ideal.span ({x} : Set R)) (y i : R))) : Set (R ⧸ Ideal.span ({x} : Set R)))) =
      Ideal.span (↑((Finset.univ.erase j).image (fun i => Ideal.Quotient.mk (Ideal.span ({x} : Set R)) (y i : R))) : Set (R ⧸ Ideal.span ({x} : Set R))) :=
    Submodule.span_insert_zero
  rw [hz]
  have h1 := spanFinrank_span_finset_le ((Finset.univ.erase j).image (fun i => Ideal.Quotient.mk (Ideal.span ({x} : Set R)) (y i : R)))
  have h2 := Finset.card_image_le (s := Finset.univ.erase j) (f := fun i => Ideal.Quotient.mk (Ideal.span ({x} : Set R)) (y i : R))
  have h3 := Finset.card_erase_of_mem (Finset.mem_univ j)
  rw [Finset.card_univ, Fintype.card_fin] at h3
  have h4 := j.pos
  omega
theorem eq_natCast_and_add_one_eq_of_le {a : WithBot ℕ∞} {d n : ℕ}
    (h1 : ((n : ℕ) : WithBot ℕ∞) ≤ a + 1) (h2 : a ≤ ((d : ℕ) : WithBot ℕ∞)) (h3 : d + 1 ≤ n) :
    a = ((d : ℕ) : WithBot ℕ∞) ∧ a + 1 = ((n : ℕ) : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot =>
    first
    | simp at h1
    | exact absurd h1 (by simp)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h2' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((d : ℕ∞) : WithBot ℕ∞) := h2
      exact absurd (WithBot.coe_le_coe.mp h2') (not_le.mpr (ENat.coe_lt_top d))
    | coe m =>
      have h1' : n ≤ m + 1 := by
        first
        | exact_mod_cast h1
        | (have h1'' := WithBot.coe_le_coe.mp h1; exact_mod_cast h1'')
      have h2' : m ≤ d := by
        first
        | exact_mod_cast h2
        | (have h2'' := WithBot.coe_le_coe.mp h2; exact_mod_cast h2'')
      have hm : m = d := by omega
      have hn : m + 1 = n := by omega
      subst hm
      constructor
      · first | rfl | norm_cast | simp
      · rw [← hn]
        first | rfl | norm_cast | simp
theorem spanFinrank_quotient_eq_and_ringKrullDim_add_one (R : Type*) [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ∈ maximalIdeal R)
    (hx2 : x ∉ maximalIdeal R ^ 2) [IsLocalRing (R ⧸ Ideal.span ({x} : Set R))] :
    ((Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) : ℕ) : WithBot ℕ∞)
        = ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) ∧
      ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 = ringKrullDim R := by
  have hreg : ((Submodule.spanFinrank (maximalIdeal R) : ℕ) : WithBot ℕ∞) = ringKrullDim R := by
    first
    | exact IsRegularLocalRing.spanFinrank_maximalIdeal
    | exact (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
  have hlink : Submodule.spanFinrank (maximalIdeal R) =
      Module.finrank (ResidueField R) (CotangentSpace R) := by
    first
    | exact IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace
    | exact IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := R)
    | exact (IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := R)).symm
  have h5 := spanFinrank_maximalIdeal_quotient_succ_le R hx hx2
  have hxj : (((({x} : Finset R)) : Set R)) ⊆ (Ring.jacobson R : Set R) := by
    intro z hz
    have hz' : z = x := by simpa using hz
    rw [hz']
    first
    | exact (Ideal.jacobson_bot (R := R)) ▸ IsLocalRing.maximalIdeal_le_jacobson ⊥ hx
    | exact IsLocalRing.maximalIdeal_le_jacobson ⊥ hx
    | (rw [← Ideal.jacobson_bot]; exact IsLocalRing.maximalIdeal_le_jacobson ⊥ hx)
    | (rw [← Ideal.jacobson_bot, IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]; exact hx)
  have hd := ringKrullDim_le_ringKrullDim_quotient_add_card ({x} : Finset R) hxj
  simp only [Finset.coe_singleton, Finset.card_singleton, Nat.cast_one] at hd
  have hle := ringKrullDim_le_spanFinrank_maximalIdeal (R ⧸ Ideal.span ({x} : Set R))
  obtain ⟨e1, e2⟩ := eq_natCast_and_add_one_eq_of_le (a := ringKrullDim (R ⧸ Ideal.span ({x} : Set R)))
    (d := Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))))
    (n := Submodule.spanFinrank (maximalIdeal R)) (by
      rw [hreg]
      first
      | exact hd
      | (rw [Finset.coe_singleton] at hd; exact hd)
      | (convert hd using 3 <;> simp)) hle (by omega)
  exact ⟨e1.symm, e2.trans hreg⟩
theorem isPrime_of_mem_minimalPrimes {R : Type*} [CommRing R] {p : Ideal R}
    (hp : p ∈ minimalPrimes R) : p.IsPrime := by
  first
  | exact Ideal.minimalPrimes_isPrime hp
  | exact hp.1.1
theorem le_of_le_of_mem_minimalPrimes {R : Type*} [CommRing R] {p q : Ideal R}
    (hp : p ∈ minimalPrimes R) (hq : q.IsPrime) (hle : q ≤ p) : p ≤ q := by
  first
  | exact hp.2 ⟨hq, bot_le⟩ hle
  | exact Minimal.le_of_le hp ⟨hq, bot_le⟩ hle
theorem isDomain_of_bot_isPrime {R : Type*} [CommRing R] [Nontrivial R]
    (h : (⊥ : Ideal R).IsPrime) : IsDomain R := by
  have : NoZeroDivisors R := ⟨fun {a b} hab => by
    have h2 : a * b ∈ (⊥ : Ideal R) := by rw [hab]; exact Submodule.zero_mem _
    rcases h.mem_or_mem h2 with h3 | h3
    · exact Or.inl (Ideal.mem_bot.mp h3)
    · exact Or.inr (Ideal.mem_bot.mp h3)⟩
  exact NoZeroDivisors.to_isDomain R
theorem isDomain_of_maximalIdeal_eq_bot (R : Type*) [CommRing R] [IsLocalRing R]
    (h : maximalIdeal R = ⊥) : IsDomain R := by
  have hbot : (⊥ : Ideal R).IsPrime := by
    rw [← h]
    infer_instance
  exact isDomain_of_bot_isPrime hbot
theorem maximalIdeal_eq_bot_of_le_sq (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (h : maximalIdeal R ≤ maximalIdeal R ^ 2) : maximalIdeal R = ⊥ := by
  have hfg : (maximalIdeal R).FG := IsNoetherian.noetherian _
  have hle : maximalIdeal R ≤ maximalIdeal R • maximalIdeal R := by
    rw [Ideal.smul_eq_mul, ← sq]
    exact h
  have hjac : maximalIdeal R ≤ Ideal.jacobson ⊥ := by
    first
    | exact IsLocalRing.maximalIdeal_le_jacobson ⊥
    | exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  exact Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg hle hjac
theorem exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes (R : Type*) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (hsq : ¬ maximalIdeal R ≤ maximalIdeal R ^ 2)
    (hmin : ¬ ∃ p ∈ minimalPrimes R, maximalIdeal R ≤ p) :
    ∃ x, x ∈ maximalIdeal R ∧ x ∉ maximalIdeal R ^ 2 ∧ ∀ p ∈ minimalPrimes R, x ∉ p := by
  classical
  have hfin : (minimalPrimes R).Finite := by
    first
    | exact minimalPrimes.finite_of_isNoetherianRing R
    | exact minimalPrimes.finite_of_isNoetherianRing (R := R)
  by_contra hcon
  push_neg at hcon
  have hsub : ((maximalIdeal R : Set R)) ⊆ ⋃ i ∈ (↑(insert (maximalIdeal R ^ 2) hfin.toFinset) :
      Set (Ideal R)), (i : Set R) := by
    intro z hz
    simp only [Set.mem_iUnion]
    by_cases h2 : z ∈ maximalIdeal R ^ 2
    · exact ⟨maximalIdeal R ^ 2, by simp, h2⟩
    · obtain ⟨p, hp, hzp⟩ := hcon z hz h2
      exact ⟨p, by simp [hp], hzp⟩
  obtain ⟨i, hi, hle⟩ := (Ideal.subset_union_prime (f := fun i : Ideal R => i)
    (maximalIdeal R ^ 2) (maximalIdeal R ^ 2) (by
      intro i hi hne _
      rw [Finset.mem_insert, Set.Finite.mem_toFinset] at hi
      exact isPrime_of_mem_minimalPrimes (hi.resolve_left hne))).mp hsub
  rw [Finset.mem_insert, Set.Finite.mem_toFinset] at hi
  rcases hi with rfl | hi
  · exact hsq hle
  · exact hmin ⟨i, hi, hle⟩
theorem quotient_span_singleton {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hx2 : x ∉ IsLocalRing.maximalIdeal R ^ 2) :
    IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)) := by
  haveI := isLocalRing_quotient_span_singleton hx
  have h := (spanFinrank_quotient_eq_and_ringKrullDim_add_one R hx hx2).1
  first
  | exact ⟨h⟩
  | exact { spanFinrank_maximalIdeal := h }
  | exact ⟨inferInstance, inferInstance, h⟩
  | constructor
theorem maximalIdeal_le_sq_of_finrank_cotangent_zero (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (h : Module.finrank (ResidueField R) (CotangentSpace R) = 0) :
    maximalIdeal R ≤ maximalIdeal R ^ 2 := by
  intro z hz
  by_contra hz2
  have hne : (maximalIdeal R).toCotangent ⟨z, hz⟩ ≠ 0 := fun h' =>
    hz2 ((Ideal.toCotangent_eq_zero _ _).mp h')
  obtain ⟨j, _⟩ := exists_repr_ne_zero (Module.finBasis (ResidueField R) (CotangentSpace R)) hne
  exact (Fin.cast h j).elim0
theorem isDomain_of_forall_spanFinrank_lt (R : Type u) [CommRing R]
    [IsRegularLocalRing R]
    (IH : ∀ (S : Type u) [CommRing S] [IsRegularLocalRing S],
      Submodule.spanFinrank (maximalIdeal S) < Submodule.spanFinrank (maximalIdeal R) →
        IsDomain S) :
    IsDomain R := by
  by_cases hsq : maximalIdeal R ≤ maximalIdeal R ^ 2
  · exact isDomain_of_maximalIdeal_eq_bot R (maximalIdeal_eq_bot_of_le_sq R hsq)
  have hreg : ((Submodule.spanFinrank (maximalIdeal R) : ℕ) : WithBot ℕ∞) = ringKrullDim R := by
    first
    | exact IsRegularLocalRing.spanFinrank_maximalIdeal
    | exact (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
  have hlink : Submodule.spanFinrank (maximalIdeal R) =
      Module.finrank (ResidueField R) (CotangentSpace R) := by
    first
    | exact IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace
    | exact IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := R)
    | exact (IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := R)).symm
  by_cases hmin : ∃ p ∈ minimalPrimes R, maximalIdeal R ≤ p
  · exfalso
    obtain ⟨p, hp, hle⟩ := hmin
    have hall : ∀ q : PrimeSpectrum R, q.asIdeal = maximalIdeal R := fun q => by
      have h1 : q.asIdeal ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal q.isPrime.ne_top
      have h2 : p ≤ q.asIdeal := le_of_le_of_mem_minimalPrimes hp q.isPrime (h1.trans hle)
      exact le_antisymm h1 (hle.trans h2)
    have hdim : ringKrullDim R ≤ 0 := by
      first
      | apply iSup_le
      | (unfold ringKrullDim Order.krullDim; apply iSup_le)
      intro l
      have hl : l.length = 0 := by
        by_contra hl
        have hpos : 0 < l.length := Nat.pos_of_ne_zero hl
        have hs := l.step ⟨0, hpos⟩
        have he : l.toFun (Fin.castSucc ⟨0, hpos⟩) = l.toFun (Fin.succ ⟨0, hpos⟩) :=
          PrimeSpectrum.ext ((hall _).trans (hall _).symm)
        exact (ne_of_lt hs) he
      simp [hl]
    have h0' : ((Submodule.spanFinrank (maximalIdeal R) : ℕ) : WithBot ℕ∞) ≤ 0 := by
      rw [hreg]; exact hdim
    have h0 : Submodule.spanFinrank (maximalIdeal R) = 0 := by
      first
      | exact Nat.le_zero.mp (by exact_mod_cast h0')
      | (norm_cast at h0'; omega)
      | simpa using h0'
    exact hsq (maximalIdeal_le_sq_of_finrank_cotangent_zero R (hlink.symm.trans h0))
  obtain ⟨x, hx, hx2, hxmin⟩ := exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes R hsq hmin
  haveI hR' : IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)) := quotient_span_singleton hx hx2
  have h7 := spanFinrank_quotient_eq_and_ringKrullDim_add_one R hx hx2
  have hlt : Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) < Submodule.spanFinrank (maximalIdeal R) := by
    have e : ((Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) : ℕ) : WithBot ℕ∞) + 1 =
        ((Submodule.spanFinrank (maximalIdeal R) : ℕ) : WithBot ℕ∞) := by
      rw [h7.1, h7.2, hreg]
    have e' : Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) + 1 =
        Submodule.spanFinrank (maximalIdeal R) := by
      exact_mod_cast e
    omega
  have hdom : IsDomain (R ⧸ Ideal.span ({x} : Set R)) := IH _ hlt
  have hprime : (Ideal.span ({x} : Set R)).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp hdom
  haveI := hprime
  obtain ⟨p, hp, hple⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := Ideal.span ({x} : Set R)) bot_le
  have hpp : p.IsPrime := isPrime_of_mem_minimalPrimes hp
  have hxp : x ∉ p := hxmin p hp
  have hle : p ≤ Ideal.span ({x} : Set R) • p := by
    intro z hz
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.mp (hple hz)
    have hw : w ∈ p := (hpp.mem_or_mem hz).resolve_right hxp
    rw [mul_comm]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) hw
  have hjac : Ideal.span ({x} : Set R) ≤ Ideal.jacobson ⊥ := by
    rw [Ideal.span_singleton_le_iff_mem]
    first
    | exact IsLocalRing.maximalIdeal_le_jacobson ⊥ hx
    | exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm ▸ hx
  have hbot : p = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ (IsNoetherian.noetherian p) hle hjac
  rw [hbot] at hpp
  exact isDomain_of_bot_isPrime hpp
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
    [IsRegularLocalRing R] : IsDomain R := isDomain_of_spanFinrank_le _ R le_rfl
instance (priority := 100) instIsDomain {R : Type*} [CommRing R]
    [IsRegularLocalRing R] : IsDomain R :=
  IsRegularLocalRing.isDomain R
end IsRegularLocalRing
end ReciprocityTheory.CA.AB.RegA


