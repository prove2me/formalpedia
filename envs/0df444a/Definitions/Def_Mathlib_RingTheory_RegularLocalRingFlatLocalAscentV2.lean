-- Prove2me | Definitions.Def_Mathlib_RingTheory_RegularLocalRingFlatLocalAscentV2
-- name    : Mathlib_RingTheory_RegularLocalRingFlatLocalAscentV2
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/5d4f9519-a057-5b66-9870-1c520d1f8a5b
-- title:
--   Regular local rings: flat local ascent, with inlined domain property
-- statement:
--   This module re-issues the flat local ascent development for regular local rings, adding a self-contained chain of auxiliary results whose endpoint is that a regular local ring is a domain. No new predicate or structure is introduced: all notions used are the existing ones — `IsRegularLocalRing`, the maximal ideal and cotangent space of a local ring, `Submodule.spanFinrank`, `ringKrullDim`, `QuotSMulTop`, and `Sequence.IsRegular`/`Sequence.IsWeaklyRegular` — and the module's own namespace contributes only the inlined lemmas, all of them private.
--
--   The inlined chain runs as follows. For a local ring of positive Krull dimension the maximal ideal is non-zero and is not a minimal prime; for $x$ in the maximal ideal the quotient $R/(x)$ is again local; a Noetherian local ring has Krull dimension equal to the cast of a natural number. Next, for a Noetherian local $R$ and $x \in \mathfrak m \setminus \mathfrak m^2$, there is a finite set $S \ni x$ with at most $\operatorname{spanFinrank} \mathfrak m$ elements spanning $\mathfrak m$, obtained by extending the image of $x$ in the cotangent space to a basis; and, by avoidance of the finitely many minimal primes together with $\mathfrak m^2$, such an $x$ can be chosen outside every minimal prime. For such an $x$ the dimension drops by exactly one, $\dim R/(x) + 1 = \dim R$, and $R/(x)$ is again regular local with $\operatorname{spanFinrank}$ of its maximal ideal one less than that of $\mathfrak m$. An induction on $\operatorname{spanFinrank} \mathfrak m$ then yields that a regular local ring is a domain: in the inductive step $(x)$ is prime, and any minimal prime contained in $(x)$ is killed by Nakayama, so $(0)$ is prime.
--
--   **Relation to Mathlib.** All notions involved are Mathlib's; the module defines nothing new, and its declarations are private auxiliary lemmas leading to the statement that a regular local ring is a domain.
--
--   **Where it is used.** Together with the imported modules on quotients by regular sequences and on flat local ascent, this supplies the commutative-algebra facts about regular local rings used in the ring-theoretic part of the modularity-lifting argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_RingTheory_RegularLocalRingFlatLocalAscentV2.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_RegularLocalRingQuotientRegular
import Definitions.Def_AlgebraicGeometry_RegularLocalRingRegularSequenceAscent
import Definitions.Def_Mathlib_RingTheory_RegularLocalRingFlatLocalAscent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

section InlinedTheorems

section LinkageInlined_d8d822bd

open IsLocalRing RingTheory
open scoped Pointwise

namespace W2RLR

universe u v

private theorem maximalIdeal_ne_bot_of_ringKrullDim_pos (R : Type u) [CommRing R] [IsLocalRing R] (hdim : 0 < ringKrullDim R) :
    maximalIdeal R ≠ ⊥ := by
  intro hbot
  rw [ringKrullDim_eq_zero_of_isField
    (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot)] at hdim
  exact hdim.false

namespace No4PatchingCore

section FromABFreeness
variable {R : Type u} [CommRing R]

private theorem isLocalRing_quotient_span_singleton [IsLocalRing R] {x : R}
    (hx : x ∈ maximalIdeal R) : IsLocalRing (R ⧸ Ideal.span {x}) := by
  have hne : Ideal.span {x} ≠ ⊤ := by
    intro h
    exact (maximalIdeal.isMaximal R).ne_top
      (top_le_iff.mp (h ▸ Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)))
  haveI : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

private theorem exists_ringKrullDim_eq_natCast (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] : ∃ d : ℕ, ringKrullDim R = (d : WithBot ℕ∞) := by
  have h1 : ringKrullDim R ≠ ⊤ := ringKrullDim_ne_top
  have h2 : ringKrullDim R ≠ ⊥ := ringKrullDim_ne_bot
  cases hd : ringKrullDim R with
  | bot => exact absurd hd h2
  | coe d =>
    cases d with
    | top => exact absurd hd (by simpa using h1)
    | coe d => exact ⟨d, rfl⟩

end FromABFreeness

section Exchange0
variable (R : Type u) [CommRing R]

private theorem exists_finite_span_eq_maximalIdeal_mem [IsLocalRing R] [IsNoetherianRing R]
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) :
    ∃ S : Set R, x ∈ S ∧ S.Finite ∧ S.ncard ≤ (maximalIdeal R).spanFinrank ∧
      Ideal.span S = maximalIdeal R := by
  classical

  set ξ : CotangentSpace R := (maximalIdeal R).toCotangent ⟨x, hx⟩ with hξdef
  have hξ0 : ξ ≠ 0 := by
    rw [hξdef, ne_eq, Ideal.toCotangent_eq_zero]
    exact hx2

  have hli : LinearIndepOn (ResidueField R) id ({ξ} : Set (CotangentSpace R)) := by
    refine LinearIndepOn.singleton' ?_
    intro r hr
    rcases smul_eq_zero.mp hr with h | h
    · exact h
    · exact absurd h hξ0

  obtain ⟨B, hξB, hBfin, hBcard, hBspan⟩ :
      ∃ B : Set (CotangentSpace R), ξ ∈ B ∧ B.Finite ∧
        B.ncard = (maximalIdeal R).spanFinrank ∧
        Submodule.span (ResidueField R) B = ⊤ := by
    refine ⟨hli.extend (Set.subset_univ _),
      hli.subset_extend _ (Set.mem_singleton ξ), ?_, ?_, ?_⟩
    · haveI : Finite (hli.extend (Set.subset_univ ({ξ} : Set (CotangentSpace R)))) :=
        Module.Finite.finite_basis (Module.Basis.extend hli)
      exact Set.toFinite _
    · haveI : Finite (hli.extend (Set.subset_univ ({ξ} : Set (CotangentSpace R)))) :=
        Module.Finite.finite_basis (Module.Basis.extend hli)
      haveI : Fintype (hli.extend (Set.subset_univ ({ξ} : Set (CotangentSpace R)))) :=
        Fintype.ofFinite _
      rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace R,
        Module.finrank_eq_card_basis (Module.Basis.extend hli),
        ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    · have h1 := (Module.Basis.extend hli).span_eq
      rwa [Module.Basis.range_extend] at h1

  choose lift hlift using (maximalIdeal R).toCotangent_surjective
  set S₀ : Set ↥(maximalIdeal R) := insert ⟨x, hx⟩ (lift '' (B \ {ξ})) with hS₀def

  have himg : (maximalIdeal R).toCotangent '' S₀ = B := by
    rw [hS₀def, Set.image_insert_eq, ← hξdef, ← Set.image_comp]
    have hcomp : ((maximalIdeal R).toCotangent ∘ lift) '' (B \ {ξ}) = B \ {ξ} := by
      have : ∀ v ∈ B \ {ξ}, ((maximalIdeal R).toCotangent ∘ lift) v = id v :=
        fun v _ => hlift v
      rw [Set.image_congr this, Set.image_id]
    rw [hcomp, Set.insert_diff_singleton, Set.insert_eq_self.mpr hξB]

  have hspanR : Submodule.span R S₀ = ⊤ := by
    apply IsLocalRing.CotangentSpace.span_image_eq_top_iff.mp
    rw [himg, hBspan]
  have hspan : Ideal.span ((↑) '' S₀ : Set R) = maximalIdeal R := by
    have hmap := congrArg (Submodule.map (maximalIdeal R).subtype) hspanR
    rwa [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at hmap

  refine ⟨(↑) '' S₀, ⟨⟨x, hx⟩, by rw [hS₀def]; exact Set.mem_insert _ _, rfl⟩, ?_, ?_, hspan⟩
  · rw [hS₀def]
    exact (((hBfin.diff).image _).insert _).image _
  ·
    have hfin₁ : (lift '' (B \ {ξ})).Finite := (hBfin.diff).image _
    have h1 : ((↑) '' S₀ : Set R).ncard ≤ S₀.ncard := by
      apply Set.ncard_image_le
      rw [hS₀def]; exact hfin₁.insert _
    have h2 : S₀.ncard ≤ (lift '' (B \ {ξ})).ncard + 1 := by
      rw [hS₀def]; exact Set.ncard_insert_le _ _
    have h3 : (lift '' (B \ {ξ})).ncard ≤ (B \ {ξ}).ncard :=
      Set.ncard_image_le hBfin.diff
    have h4 : (B \ {ξ}).ncard + 1 = B.ncard :=
      Set.ncard_diff_singleton_add_one hξB hBfin
    omega

end Exchange0

section PrimeAvoidance

private theorem maximalIdeal_notMem_minimalPrimes_of_ringKrullDim_pos
    (R : Type u) [CommRing R] [IsLocalRing R] (hdim : 0 < ringKrullDim R) :
    maximalIdeal R ∉ minimalPrimes R := by
  intro hmem

  have hall : ∀ p : PrimeSpectrum R, p.asIdeal = maximalIdeal R := fun p =>
    le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top)
      (hmem.2 ⟨p.isPrime, bot_le⟩ (IsLocalRing.le_maximalIdeal p.isPrime.ne_top))
  haveI : Subsingleton (PrimeSpectrum R) :=
    ⟨fun p q => PrimeSpectrum.ext ((hall p).trans (hall q).symm)⟩
  have heq : ringKrullDim R = 0 := by
    rw [ringKrullDim]
    haveI : Nonempty (PrimeSpectrum R) := ⟨⟨maximalIdeal R, inferInstance⟩⟩
    letI : Unique (PrimeSpectrum R) := uniqueOfSubsingleton (Classical.arbitrary _)
    exact Order.krullDim_eq_zero_of_unique
  rw [heq] at hdim
  exact hdim.false

private theorem exists_parameter_notMem_minimalPrimes
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : 0 < ringKrullDim R) :
    ∃ x ∈ maximalIdeal R, x ∉ (maximalIdeal R) ^ 2 ∧ ∀ p ∈ minimalPrimes R, x ∉ p := by
  classical
  have hbot : maximalIdeal R ≠ ⊥ :=
    W2RLR.maximalIdeal_ne_bot_of_ringKrullDim_pos R hdim

  have hfin : (insert ((maximalIdeal R) ^ 2) (minimalPrimes R)).Finite :=
    Set.Finite.insert _ (minimalPrimes.finite_of_isNoetherianRing R)

  have hnotle : ¬ ∃ I ∈ hfin.toFinset, maximalIdeal R ≤ I := by
    rintro ⟨I, hIs, hle⟩
    rw [Set.Finite.mem_toFinset, Set.mem_insert_iff] at hIs
    rcases hIs with rfl | hI
    ·
      refine hbot (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R)
        (maximalIdeal R) (IsNoetherian.noetherian _) ?_
        (IsLocalRing.maximalIdeal_le_jacobson _))
      rwa [Ideal.smul_eq_mul, ← pow_two]
    ·
      have hp_prime : I.IsPrime := Ideal.minimalPrimes_isPrime hI
      have heq : I = maximalIdeal R :=
        (IsLocalRing.le_maximalIdeal hp_prime.ne_top).antisymm hle
      rw [heq] at hI
      exact maximalIdeal_notMem_minimalPrimes_of_ringKrullDim_pos R hdim hI

  have havoid : ¬ ((maximalIdeal R : Set R) ⊆
      ⋃ I ∈ (hfin.toFinset : Set (Ideal R)), (I : Set R)) := by
    intro hsub
    refine hnotle ((Ideal.subset_union_prime (s := hfin.toFinset) (f := fun I => I)
      ((maximalIdeal R) ^ 2) ((maximalIdeal R) ^ 2) ?_).mp hsub)
    intro I hIs hI₁ _
    rw [Set.Finite.mem_toFinset, Set.mem_insert_iff] at hIs
    rcases hIs with rfl | hI
    · exact absurd rfl hI₁
    · exact Ideal.minimalPrimes_isPrime hI

  rw [hfin.coe_toFinset] at havoid
  obtain ⟨x, hxm, hxout⟩ := Set.not_subset.mp havoid
  refine ⟨x, hxm, ?_, ?_⟩
  ·
    intro hx2
    exact hxout (Set.mem_biUnion (Set.mem_insert _ _) hx2)
  ·
    intro p hp hxp
    exact hxout (Set.mem_biUnion (Set.mem_insert_of_mem _ hp) hxp)

end PrimeAvoidance

section DimensionDrop

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

private theorem annihilator_self_eq_bot (R : Type u) [CommRing R] : Module.annihilator R R = ⊥ := by
  rw [eq_bot_iff]
  intro r hr
  simpa using Module.mem_annihilator.mp hr 1

private theorem ringKrullDim_quotSMulTop_succ_eq_of_forall_notMem_minimalPrimes
    {x : R} (hx : x ∈ maximalIdeal R) (hxmin : ∀ p ∈ minimalPrimes R, x ∉ p) :
    ringKrullDim (QuotSMulTop x R) + 1 = ringKrullDim R := by
  rw [← Module.supportDim_quotient_eq_ringKrullDim, ← Module.supportDim_self_eq_ringKrullDim]
  refine Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
    ?_ hx
  intro p hp
  refine hxmin p ?_
  rwa [annihilator_self_eq_bot] at hp

private theorem ringKrullDim_quotient_span_singleton_succ_eq_of_forall_notMem_minimalPrimes
    {x : R} (hx : x ∈ maximalIdeal R) (hxmin : ∀ p ∈ minimalPrimes R, x ∉ p) :
    ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R := by
  have hkey : ringKrullDim (QuotSMulTop x R) + 1 = ringKrullDim R :=
    ringKrullDim_quotSMulTop_succ_eq_of_forall_notMem_minimalPrimes hx hxmin
  have hspan : Ideal.span {x} = x • (⊤ : Ideal R) := by
    simp [← Submodule.ideal_span_singleton_smul]
  rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquivAlgOfEq R hspan).toRingEquiv]
  exact hkey

end DimensionDrop

section QuotientRegularity

variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

private theorem isRegularLocalRing_quotient_span_singleton_of_forall_notMem_minimalPrimes
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2)
    (hxmin : ∀ p ∈ minimalPrimes R, x ∉ p) [IsLocalRing (R ⧸ Ideal.span {x})] :
    IsRegularLocalRing (R ⧸ Ideal.span {x}) ∧
      (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 =
        (maximalIdeal R).spanFinrank := by

  obtain ⟨S, hxS, hSfin, hScard, hSspan⟩ :=
    exists_finite_span_eq_maximalIdeal_mem R hx hx2

  have hmax' : (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {x})) =
      maximalIdeal (R ⧸ Ideal.span {x}) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hmkx : (Ideal.Quotient.mk (Ideal.span {x})) x = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  have hmap : (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {x})) =
      Ideal.span ((Ideal.Quotient.mk (Ideal.span {x})) '' (S \ {x})) := by
    rw [← hSspan, Ideal.map_span]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨y, hy, rfl⟩
      by_cases hyx : y = x
      · subst hyx
        rw [SetLike.mem_coe, hmkx]
        exact Submodule.zero_mem _
      · exact Ideal.subset_span ⟨y, ⟨hy, hyx⟩, rfl⟩
    · exact Ideal.span_mono (Set.image_mono Set.diff_subset)

  have hsf_le : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 ≤
      (maximalIdeal R).spanFinrank := by
    have h1 : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank ≤ (S \ {x}).ncard := by
      rw [← hmax', hmap]
      exact le_trans
        (Submodule.spanFinrank_span_le_ncard_of_finite ((hSfin.diff).image _))
        (Set.ncard_image_le hSfin.diff)
    have h2 : (S \ {x}).ncard + 1 = S.ncard :=
      Set.ncard_diff_singleton_add_one hxS hSfin
    omega

  have hkrull : ringKrullDim (R ⧸ Ideal.span {x}) ≤
      ((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞) :=
    ringKrullDim_le_spanFinrank_maximalIdeal _
  have hdrop : ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R :=
    ringKrullDim_quotient_span_singleton_succ_eq_of_forall_notMem_minimalPrimes hx hxmin
  have hregR : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
    IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)

  have hsqueeze : (maximalIdeal R).spanFinrank ≤
      (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 := by
    have hcalc : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤
        (((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 : ℕ) : WithBot ℕ∞) := by
      rw [hregR, ← hdrop]
      calc ringKrullDim (R ⧸ Ideal.span {x}) + 1
          ≤ ((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞) + 1 :=
            add_le_add hkrull le_rfl
        _ = (((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 : ℕ) : WithBot ℕ∞) := by
            push_cast
            ring
    exact_mod_cast hcalc
  have hkey : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 =
      (maximalIdeal R).spanFinrank := by omega

  obtain ⟨d, hd⟩ := exists_ringKrullDim_eq_natCast (R ⧸ Ideal.span {x})
  have hd1 : (d : ℕ) + 1 = (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 := by
    have hcast : ((d + 1 : ℕ) : WithBot ℕ∞) =
        (((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 : ℕ) : WithBot ℕ∞) := by
      have h5 : ringKrullDim (R ⧸ Ideal.span {x}) + 1 =
          (((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 : ℕ) : WithBot ℕ∞) := by
        rw [hdrop, ← hregR]
        exact_mod_cast congrArg (Nat.cast : ℕ → WithBot ℕ∞) hkey.symm
      rw [hd] at h5
      rw [← h5]
      push_cast
      ring
    exact_mod_cast hcast
  refine ⟨IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_, hkey⟩
  rw [hd]
  have : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank = d := by omega
  exact_mod_cast this.le

end QuotientRegularity

section MatsumuraDomain

private theorem isDomain_of_isRegularLocalRing_aux :
    ∀ (n : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R],
      (maximalIdeal R).spanFinrank = n → IsDomain R := by
  intro n
  induction n with
  | zero =>

    intro R _ _ hn
    have hbot : maximalIdeal R = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot
        ((maximalIdeal R).fg_of_isNoetherianRing)).mp hn
    haveI hprime : (⊥ : Ideal R).IsPrime := hbot ▸ (maximalIdeal.isMaximal R).isPrime
    exact IsDomain.of_bot_isPrime R
  | succ n IH =>
    intro R _ _ hn

    have hdim : ringKrullDim R = ((n + 1 : ℕ) : WithBot ℕ∞) := by
      rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R), hn]
    have hdim_pos : 0 < ringKrullDim R := by
      rw [hdim]
      exact_mod_cast Nat.succ_pos n

    obtain ⟨x, hx_mem, hx_sq, hx_min⟩ := exists_parameter_notMem_minimalPrimes R hdim_pos

    haveI hloc : IsLocalRing (R ⧸ Ideal.span {x}) :=
      isLocalRing_quotient_span_singleton hx_mem
    obtain ⟨hreg', hsf'⟩ :=
      isRegularLocalRing_quotient_span_singleton_of_forall_notMem_minimalPrimes R
        hx_mem hx_sq hx_min
    haveI := hreg'
    have hsf'n : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank = n := by
      rw [hn] at hsf'
      omega

    have hdom' : IsDomain (R ⧸ Ideal.span {x}) := IH (R ⧸ Ideal.span {x}) hsf'n
    have hprime : (Ideal.span {x}).IsPrime := by
      rw [← Ideal.Quotient.isDomain_iff_prime]
      exact hdom'

    haveI := hprime
    obtain ⟨p, hp_min, hp_le⟩ :=
      Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := Ideal.span {x}) bot_le
    have hp_prime : p.IsPrime := Ideal.minimalPrimes_isPrime hp_min
    have hxp : x ∉ p := hx_min p hp_min

    have hple : p ≤ (maximalIdeal R) • p := by
      intro a ha
      obtain ⟨r, hrx⟩ := Ideal.mem_span_singleton'.mp (hp_le ha)
      have hrp : r ∈ p := by
        have hmem : r * x ∈ p := by rw [hrx]; exact ha
        rcases hp_prime.mem_or_mem hmem with h | h
        · exact h
        · exact absurd h hxp
      rw [Ideal.smul_eq_mul, ← hrx, mul_comm r x]
      exact Ideal.mul_mem_mul hx_mem hrp

    have hp_bot : p = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) p
        (IsNoetherian.noetherian p) hple (IsLocalRing.maximalIdeal_le_jacobson _)

    haveI : (⊥ : Ideal R).IsPrime := hp_bot ▸ hp_prime
    exact IsDomain.of_bot_isPrime R

private theorem isDomain_of_isRegularLocalRing (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    IsDomain R :=
  isDomain_of_isRegularLocalRing_aux ((maximalIdeal R).spanFinrank) R rfl

end MatsumuraDomain

end No4PatchingCore

end W2RLR

open IsLocalRing

private theorem IsRegularLocalRing.isDomain_loc (R : Type*) [CommRing R] [IsRegularLocalRing R] :
    IsDomain R :=
  W2RLR.No4PatchingCore.isDomain_of_isRegularLocalRing R

end LinkageInlined_d8d822bd

end InlinedTheorems

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open IsLocalRing RingTheory
open scoped Pointwise

namespace RegularFlatLocalAscent

universe u v

end RegularFlatLocalAscent

end


