-- Prove2me | solution 1 for AlgebraicGeometry.universallyClosed_of_forall_isDiscreteValuationRing_finite_residueField_hasLift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/b5f35986-8069-58d6-be6f-ee393cddef71

import Mathlib
import Theorems.Thm_AlgebraicGeometry_universallyClosed_of_forall_finite_isClosedMap_pullback_snd_mvPolynomial
import Theorems.Thm_IsConstructible_isClosed_of_forall_specializes_mem_of_jacobsonSpace
import Theorems.Thm_IsLocalRing_exists_isPrime_not_mem_ringKrullDim_quotient_eq_one
import Theorems.Thm_AlgebraicGeometry_exists_valuativeCommSq_isDiscreteValuationRing_finite_residueField_of_specializes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_universallyClosed_of_forall_isDiscreteValuationRing_finite_residueField_hasLift

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace DVRValCritFin

open IsLocalRing Topology

theorem isJacobsonRing_int : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases hP0 : P = ⊥
  · subst hP0
    refine le_antisymm (fun x hx => ?_) Ideal.le_jacobson
    rw [Ideal.mem_bot]
    have h := (Ideal.mem_jacobson_bot.mp hx) x
    rcases Int.isUnit_iff.mp h with h1 | h1 <;> nlinarith [sq_nonneg x]
  · haveI := hP
    haveI := IsPrime.to_maximal_ideal (S := P) hP0
    exact Ideal.jacobson_eq_self_of_isMaximal

theorem finite_of_field_of_moduleFinite_int (F : Type u) [Field F] [Module.Finite ℤ F] : Finite F := by
  classical
  obtain ⟨p, hp⟩ := CharP.exists F
  rcases CharP.char_is_prime_or_zero F p with hpp | hp0
  · haveI : Fact p.Prime := ⟨hpp⟩
    letI : Algebra (ZMod p) F := ZMod.algebra F p
    haveI : Module.Finite (ZMod p) F := Module.Finite.of_restrictScalars_finite ℤ (ZMod p) F
    exact Module.finite_of_finite (ZMod p)
  · exfalso
    subst hp0
    haveI : CharZero F := CharP.charP_to_charZero F
    haveI : IsNoetherian ℤ F := isNoetherian_of_isNoetherianRing_of_finite ℤ F
    have h2 : (2 : F) ≠ 0 := two_ne_zero
    let N : ℕ → Submodule ℤ F := fun n => Submodule.span ℤ {((2 : F) ^ n)⁻¹}
    have hmono : ∀ n, N n < N (n + 1) := by
      intro n
      refine lt_of_le_of_ne ?_ ?_
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        refine Submodule.mem_span_singleton.mpr ⟨2, ?_⟩
        rw [zsmul_eq_mul, Int.cast_ofNat, pow_succ, mul_inv, ← mul_assoc, mul_comm (2 : F) _, mul_assoc,
          mul_inv_cancel₀ h2, mul_one]
      · intro h
        have hmem : ((2 : F) ^ (n + 1))⁻¹ ∈ N n := h ▸ Submodule.subset_span rfl
        obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hmem
        rw [zsmul_eq_mul] at hk
        have hk' : (k : F) * 2 = 1 := by
          have e := congrArg (fun y => y * (2 : F) ^ (n + 1)) hk
          rwa [inv_mul_cancel₀ (pow_ne_zero _ h2), pow_succ, ← mul_assoc, mul_assoc (k : F) _ _,
            inv_mul_cancel₀ (pow_ne_zero _ h2), mul_one] at e
        have : ((k * 2 : ℤ) : F) = ((1 : ℤ) : F) := by push_cast; exact hk'
        have := Int.cast_injective this
        omega
    obtain ⟨n, hn⟩ := (monotone_stabilizes_iff_noetherian.mpr ‹IsNoetherian ℤ F›)
      ⟨N, monotone_nat_of_le_succ fun n => (hmono n).le⟩
    exact (hmono n).ne (hn (n + 1) (Nat.le_succ n))

theorem finite_quotient_mvPolynomial_of_isMaximal {B : Type u} [CommRing B] [Algebra.FiniteType ℤ B]
    {ι : Type u} [Finite ι] (m : Ideal (MvPolynomial ι B)) [m.IsMaximal] : Finite (MvPolynomial ι B ⧸ m) := by
  classical
  haveI : IsJacobsonRing ℤ := isJacobsonRing_int
  letI : Field (MvPolynomial ι B ⧸ m) := Ideal.Quotient.field m

  have h := finite_of_finite_type_of_isJacobsonRing ℤ (MvPolynomial ι B ⧸ m)
  have key : ((Ring.toIntAlgebra (MvPolynomial ι B ⧸ m)).toModule : Module ℤ (MvPolynomial ι B ⧸ m)) =
      AddCommGroup.toIntModule _ := Subsingleton.elim _ _
  haveI : Module.Finite ℤ (MvPolynomial ι B ⧸ m) := by
    have e : @Module.Finite ℤ (MvPolynomial ι B ⧸ m) _ _ (Ring.toIntAlgebra _).toModule =
        @Module.Finite ℤ (MvPolynomial ι B ⧸ m) _ _ (AddCommGroup.toIntModule _) := by rw [key]
    exact e.mp h
  exact finite_of_field_of_moduleFinite_int _

theorem locallyOfFinitePresentation_of_isNoetherianRing {C : Type u} [CommRing C] [IsNoetherianRing C]
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of C)) [LocallyOfFiniteType g] :
    LocallyOfFinitePresentation g := by
  haveI : IsNoetherianRing ↑Γ(Spec (CommRingCat.of C), ⊤) :=
    isNoetherianRing_of_ringEquiv C (Scheme.ΓSpecIso (CommRingCat.of C)).symm.commRingCatIsoToRingEquiv
  refine HasRingHomProperty.of_source_openCover (P := @LocallyOfFinitePresentation) X.affineCover fun i => ?_
  have hft : ((X.affineCover.f i ≫ g).appTop).hom.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  exact RingHom.FinitePresentation.of_finiteType.mp hft

theorem hasLift_baseChange {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {iX : X' ⟶ X} {iY : Y' ⟶ Y}
    (hP : IsPullback iX f' f iY)
    (H : ∀ (S : ValuativeCommSq f) [IsDiscreteValuationRing S.R] [Finite (ResidueField S.R)], S.commSq.HasLift)
    (S : ValuativeCommSq f') [IsDiscreteValuationRing S.R] [Finite (ResidueField S.R)] : S.commSq.HasLift := by
  let S' : ValuativeCommSq f :=
    { R := S.R
      K := S.K
      i₁ := S.i₁ ≫ iX
      i₂ := S.i₂ ≫ iY
      commSq := ⟨by simp only [Category.assoc, hP.w, reassoc_of% S.commSq.w]⟩ }
  haveI : IsDiscreteValuationRing S'.R := ‹IsDiscreteValuationRing S.R›
  haveI : Finite (ResidueField S'.R) := ‹Finite (ResidueField S.R)›
  obtain ⟨l₀, hl₁, hl₂⟩ := (H S').exists_lift
  refine ⟨⟨⟨hP.lift l₀ S.i₂ (by simpa [S'] using hl₂), ?_, hP.lift_snd _ _ _⟩⟩⟩
  apply hP.hom_ext
  · simpa [S'] using hl₁
  · simp only [Category.assoc]
    rw [hP.lift_snd, S.commSq.w]

theorem exists_isOpen_inter_closure_subset {T : Type u} [TopologicalSpace T] {s : Set T} (hs : IsConstructible s) :
    ∀ x ∈ s, ∃ U : Set T, IsOpen U ∧ x ∈ U ∧ U ∩ closure {x} ⊆ s := by

  let Q : Set T → Prop := fun s => ∀ x ∈ s, ∃ U : Set T, IsOpen U ∧ x ∈ U ∧ U ∩ closure {x} ⊆ s
  have hQi : ∀ s t, Q s → Q t → Q (s ∩ t) := by
    intro s t hs ht x ⟨hxs, hxt⟩
    obtain ⟨U, hU, hxU, hUs⟩ := hs x hxs
    obtain ⟨V, hV, hxV, hVt⟩ := ht x hxt
    exact ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, fun y ⟨⟨hyU, hyV⟩, hy⟩ => ⟨hUs ⟨hyU, hy⟩, hVt ⟨hyV, hy⟩⟩⟩
  have hQu : ∀ s t, Q s → Q t → Q (s ∪ t) := by
    intro s t hs ht x hx
    rcases hx with hxs | hxt
    · obtain ⟨U, hU, hxU, hUs⟩ := hs x hxs
      exact ⟨U, hU, hxU, fun y hy => Or.inl (hUs hy)⟩
    · obtain ⟨V, hV, hxV, hVt⟩ := ht x hxt
      exact ⟨V, hV, hxV, fun y hy => Or.inr (hVt hy)⟩
  suffices h : Q s ∧ Q sᶜ from h.1
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
    refine ⟨fun x hx => ⟨U, hU, hx, fun y hy => hy.1⟩, fun x hx => ⟨Set.univ, isOpen_univ, trivial, ?_⟩⟩
    rintro y ⟨-, hy⟩
    exact (hU.isClosed_compl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hx)) hy
  | union s hs t ht ihs iht =>
    exact ⟨hQu _ _ ihs.1 iht.1, by rw [Set.compl_union]; exact hQi _ _ ihs.2 iht.2⟩
  | compl s hs ih => exact ⟨ih.2, by rw [compl_compl]; exact ih.1⟩

theorem eq_or_eq_maximalIdeal_of_ringKrullDim_quotient_eq_one {R : Type u} [CommRing R] [IsLocalRing R]
    (q : Ideal R) [q.IsPrime] (hq : ringKrullDim (R ⧸ q) = 1) (p : Ideal R) [p.IsPrime] (hqp : q ≤ p) :
    p = q ∨ p = maximalIdeal R := by
  classical
  haveI : Nontrivial (R ⧸ q) := Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsPrime.ne_top ‹_›)
  haveI : IsLocalRing (R ⧸ q) := IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  have h1 : (maximalIdeal (R ⧸ q)).height = 1 := by
    have := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R ⧸ q)
    rw [hq] at this
    exact_mod_cast this
  let pbar := p.map (Ideal.Quotient.mk q)
  haveI hpbar : pbar.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hqp
  have hcomap : pbar.comap (Ideal.Quotient.mk q) = p := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.mpr hqp]
  by_cases hpm : pbar = maximalIdeal (R ⧸ q)
  · right
    have : (maximalIdeal (R ⧸ q)).comap (Ideal.Quotient.mk q) = maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
    rw [← hcomap, hpm, this]
  · left
    have hlt : pbar < maximalIdeal (R ⧸ q) := lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hpbar.ne_top) hpm
    have h0 : pbar.height < (1 : ℕ) := (Ideal.height_le_iff (n := 1)).mp h1.le pbar hpbar hlt
    have h00 : pbar.height = 0 := by
      rw [Nat.cast_one] at h0
      exact ENat.lt_one_iff_eq_zero.mp h0
    have hb : pbar = ⊥ := by
      rw [Ideal.height_eq_zero_iff] at h00
      exact le_bot_iff.mp (h00.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le)
    rw [← hcomap, hb, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

theorem exists_coheightOne {C : Type u} [CommRing C] [IsNoetherianRing C] (𝔭 𝔪 : Ideal C) [𝔭.IsPrime] [𝔪.IsMaximal]
    (hpm : 𝔭 ≤ 𝔪) (hne : 𝔭 ≠ 𝔪) (s : C) (hs : s ∉ 𝔭) :
    ∃ 𝔮 : Ideal C, 𝔮.IsPrime ∧ 𝔭 ≤ 𝔮 ∧ 𝔮 ≤ 𝔪 ∧ 𝔮 ≠ 𝔪 ∧ s ∉ 𝔮 ∧
      ∀ p : Ideal C, p.IsPrime → 𝔮 ≤ p → p ≤ 𝔪 → p = 𝔮 ∨ p = 𝔪 := by
  classical

  let R₀ := Localization.AtPrime 𝔪
  have hdisj : ∀ {I : Ideal C}, I ≤ 𝔪 → Disjoint (𝔪.primeCompl : Set C) (I : Set C) := fun hI =>
    Set.disjoint_left.mpr fun x hx hxI => hx (hI hxI)
  let P : Ideal R₀ := 𝔭.map (algebraMap C R₀)
  haveI hP : P.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint 𝔪.primeCompl R₀ 𝔭 ‹_› (hdisj hpm)
  have hPu : P.comap (algebraMap C R₀) = 𝔭 := IsLocalization.under_map_of_isPrime_disjoint 𝔪.primeCompl R₀ ‹_› (hdisj hpm)
  have hMu : (maximalIdeal R₀).comap (algebraMap C R₀) = 𝔪 := Localization.AtPrime.under_maximalIdeal
  have hMm : 𝔪.map (algebraMap C R₀) = maximalIdeal R₀ := Localization.AtPrime.map_eq_maximalIdeal
  haveI : Nontrivial (R₀ ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr hP.ne_top
  haveI : IsLocalRing (R₀ ⧸ P) := IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  let φ : C →+* R₀ ⧸ P := (Ideal.Quotient.mk P).comp (algebraMap C R₀)
  have hφker : ∀ x, φ x = 0 ↔ x ∈ 𝔭 := fun x => by
    rw [← hPu, Ideal.mem_comap]; exact Ideal.Quotient.eq_zero_iff_mem

  have hnf : ¬ IsField (R₀ ⧸ P) := by
    intro hF
    have hPmax : P.IsMaximal := Ideal.Quotient.maximal_of_isField P hF
    apply hne
    rw [← hPu, IsLocalRing.eq_maximalIdeal hPmax, hMu]
  obtain ⟨qbar, hqbar, hsq, hdim⟩ :=
    IsLocalRing.exists_isPrime_not_mem_ringKrullDim_quotient_eq_one hnf (φ s) (fun h => hs ((hφker s).mp h))
  let Q : Ideal R₀ := qbar.comap (Ideal.Quotient.mk P)
  haveI hQ : Q.IsPrime := Ideal.IsPrime.comap _
  have hPQ : P ≤ Q := fun x hx => by
    show Ideal.Quotient.mk P x ∈ qbar
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]; exact qbar.zero_mem
  have hQmap : Q.map (Ideal.Quotient.mk P) = qbar := Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _
  refine ⟨Q.comap (algebraMap C R₀), Ideal.IsPrime.comap _, ?_, ?_, ?_, ?_, ?_⟩
  · exact hPu.ge.trans (Ideal.comap_mono hPQ)
  · exact (Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQ.ne_top)).trans hMu.le
  · intro hQm

    have hQM : Q = maximalIdeal R₀ := by
      have := IsLocalization.map_under 𝔪.primeCompl R₀ Q
      rw [Ideal.under, hQm, hMm] at this
      exact this.symm
    have hqM : qbar.IsMaximal := by
      rw [← hQmap, hQM]
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
        (I := maximalIdeal R₀) inferInstance with htop | hmax
      · exact absurd (hQmap.symm.trans (hQM ▸ htop) ▸ hqbar.ne_top) (fun h => h rfl)
      · exact hmax
    have h0 : ringKrullDim ((R₀ ⧸ P) ⧸ qbar) = 0 := by
      letI := Ideal.Quotient.field qbar
      exact ringKrullDim_eq_zero_of_field _
    rw [h0] at hdim
    exact zero_ne_one hdim
  · rwa [Ideal.mem_comap, Ideal.mem_comap]
  · intro p hp hQp hpM
    haveI := hp
    let p₀ : Ideal R₀ := p.map (algebraMap C R₀)
    haveI hp₀ : p₀.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint 𝔪.primeCompl R₀ p hp (hdisj hpM)
    have hp₀u : p₀.comap (algebraMap C R₀) = p := IsLocalization.under_map_of_isPrime_disjoint 𝔪.primeCompl R₀ hp (hdisj hpM)
    have hQp₀ : Q ≤ p₀ := by
      have := IsLocalization.map_under 𝔪.primeCompl R₀ Q
      rw [← this]
      exact Ideal.map_mono hQp
    haveI : (p₀.map (Ideal.Quotient.mk P)).IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime (hPQ.trans hQp₀)
    have key := eq_or_eq_maximalIdeal_of_ringKrullDim_quotient_eq_one qbar hdim (p₀.map (Ideal.Quotient.mk P))
      (by rw [← hQmap]; exact Ideal.map_mono hQp₀)
    have hback : (p₀.map (Ideal.Quotient.mk P)).comap (Ideal.Quotient.mk P) = p₀ := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
        sup_eq_left.mpr (hPQ.trans hQp₀)]
    rcases key with h | h
    · left
      rw [← hp₀u, ← hback, h]
    · right
      have : (maximalIdeal (R₀ ⧸ P)).comap (Ideal.Quotient.mk P) = maximalIdeal R₀ :=
        IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
      rw [← hp₀u, ← hback, h, this, hMu]

theorem mem_image_of_specializes_of_isClosed
    {C : Type u} [CommRing C] [IsNoetherianRing C] [IsJacobsonRing C]
    (hfin : ∀ (m : Ideal C) [m.IsMaximal], Finite (C ⧸ m))
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of C)) [QuasiCompact g] [LocallyOfFiniteType g]
    (H : ∀ (S : ValuativeCommSq g) [IsDiscreteValuationRing S.R] [Finite (ResidueField S.R)], S.commSq.HasLift)
    (Z : Set X) (hZ : IsClosed Z) (hZc : IsConstructible (g.base '' Z))
    {t' t : ↥(Spec (CommRingCat.of C))} (ht' : t' ∈ g.base '' Z) (h : t' ⤳ t)
    (ht : IsClosed ({t} : Set ↥(Spec (CommRingCat.of C)))) : t ∈ g.base '' Z := by
  classical
  by_cases htt : t' = t
  · exact htt ▸ ht'

  obtain ⟨U, hU, ht'U, hUZ⟩ := exists_isOpen_inter_closure_subset hZc t' ht'
  obtain ⟨_, ⟨_, ⟨s, rfl⟩, rfl⟩, hts, hsU⟩ := PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open ht'U hU

  haveI hmax : t.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal t).mp ht
  have hle : t'.asIdeal ≤ t.asIdeal := (PrimeSpectrum.le_iff_specializes t' t).mpr h
  have hne : t'.asIdeal ≠ t.asIdeal := fun e => htt (PrimeSpectrum.ext e)
  obtain ⟨𝔮, h𝔮, hp𝔮, h𝔮m, h𝔮ne, hs𝔮, hcov⟩ := exists_coheightOne t'.asIdeal t.asIdeal hle hne s hts
  let q : ↥(Spec (CommRingCat.of C)) := ⟨𝔮, h𝔮⟩
  have hqZ : q ∈ g.base '' Z := by
    refine hUZ ⟨hsU hs𝔮, ?_⟩
    exact (PrimeSpectrum.le_iff_mem_closure t' q).mp hp𝔮
  obtain ⟨z, hzZ, hz⟩ := hqZ

  have hzt : g.base z ⤳ t := by rw [hz]; exact (PrimeSpectrum.le_iff_specializes q t).mp h𝔮m
  have hznt : g.base z ≠ t := by rw [hz]; exact fun e => h𝔮ne (congrArg PrimeSpectrum.asIdeal e)
  obtain ⟨S, hR, hfinR, hi₂, hi₁⟩ :=
    AlgebraicGeometry.exists_valuativeCommSq_isDiscreteValuationRing_finite_residueField_of_specializes
      hfin g z t ht hzt hznt (by rw [hz]; exact hcov)
  haveI := hR
  haveI := hfinR
  obtain ⟨l, hl₁, hl₂⟩ := (H S).exists_lift
  refine ⟨l.base (closedPoint S.R), ?_, ?_⟩
  ·
    have hgen : l.base ((Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))).base (closedPoint S.K)) ∈ closure {z} := by
      apply hi₁
      refine ⟨closedPoint S.K, ?_⟩
      rw [← hl₁]
      exact Scheme.Hom.comp_apply _ _ _
    have hsp : (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))).base (closedPoint S.K) ⤳ closedPoint S.R :=
      IsLocalRing.specializes_closedPoint _
    have h1 := (hsp.map l.continuous).mem_closure
    have h2 : closure {l.base ((Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))).base (closedPoint S.K))} ⊆
        closure {z} := isClosed_closure.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hgen)
    have h3 : closure {z} ⊆ Z := hZ.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hzZ)
    exact h3 (h2 h1)
  · rw [← Scheme.Hom.comp_apply, hl₂, hi₂]

end DVRValCritFin

theorem solution
    {B : Type u} [CommRing B] [Algebra.FiniteType ℤ B]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [QuasiCompact f] [LocallyOfFiniteType f]
    (H : ∀ (S : ValuativeCommSq f) [IsDiscreteValuationRing S.R] [Finite (IsLocalRing.ResidueField S.R)], S.commSq.HasLift) :
    UniversallyClosed f := by
  classical

  apply AlgebraicGeometry.universallyClosed_of_forall_finite_isClosedMap_pullback_snd_mvPolynomial f
  intro ι _

  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
  haveI : IsJacobsonRing ℤ := DVRValCritFin.isJacobsonRing_int
  haveI : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := ℤ)
  have hfinC : ∀ (m : Ideal (MvPolynomial ι B)) [m.IsMaximal], Finite (MvPolynomial ι B ⧸ m) := fun m _ =>
    DVRValCritFin.finite_quotient_mvPolynomial_of_isMaximal m
  have HC : ∀ (S : ValuativeCommSq (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap B (MvPolynomial ι B))))))
      [IsDiscreteValuationRing S.R] [Finite (IsLocalRing.ResidueField S.R)], S.commSq.HasLift := fun S _ _ =>
    DVRValCritFin.hasLift_baseChange
      (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap B (MvPolynomial ι B))))) H S

  intro Z hZ

  haveI : IsLocallyNoetherian (pullback f (Spec.map (CommRingCat.ofHom (algebraMap B (MvPolynomial ι B))))) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap B (MvPolynomial ι B)))))
  haveI : CompactSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap B (MvPolynomial ι B))))) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap B (MvPolynomial ι B)))))
  haveI : IsNoetherian (pullback f (Spec.map (CommRingCat.ofHom (algebraMap B (MvPolynomial ι B))))) := {}
  have hZc : Topology.IsConstructible Z :=
    Topology.IsConstructible.of_compl ((TopologicalSpace.NoetherianSpace.isCompact Zᶜ).isConstructible hZ.isOpen_compl)
  haveI := DVRValCritFin.locallyOfFinitePresentation_of_isNoetherianRing
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap B (MvPolynomial ι B)))))
  have himg := Scheme.Hom.isConstructible_image
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap B (MvPolynomial ι B))))) hZc
  apply IsConstructible.isClosed_of_forall_specializes_mem_of_jacobsonSpace himg
  intro t' ht' t hst htc
  exact DVRValCritFin.mem_image_of_specializes_of_isClosed hfinC _ HC Z hZ himg ht' hst htc

end S_AlgebraicGeometry_universallyClosed_of_forall_isDiscreteValuationRing_finite_residueField_hasLift
end P2MW
export P2MW.S_AlgebraicGeometry_universallyClosed_of_forall_isDiscreteValuationRing_finite_residueField_hasLift (solution)
