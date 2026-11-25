-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFD
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFD
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:13:39.256837+00:00
-- url     : https://prove2.me/theorems/3faf96ad-ebcd-41e1-91ba-fe8f70642ba0
-- title:
--   Regular UFD
-- statement:
--   Definitions and structural lemmas for Regular UFD, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularUFD.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDLocalization
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsRegularLocalRing_isDomain
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsRegularLocalRing_localization_atPrime
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_hasProjectiveDimensionLT_of_isRegularLocalRing
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isRegularLocalRing_quotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.SchemeCoh
open IsLocalRing Ideal Module
universe u
section Cofactor
variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {n : ℕ}
noncomputable def cofactorLinear (bN : Module.Basis (Fin n) R N) :
    M × N →ₗ[R] (M × N) [⋀^Fin n]→ₗ[R] M where
  toFun x := (bN.det.compLinearMap (LinearMap.snd R M N)).smulRight x.1
  map_add' x y := AlternatingMap.ext fun _ ↦ by simp
  map_smul' c x := AlternatingMap.ext fun _ ↦ by simp [smul_smul, mul_comm]
noncomputable def cofactorToLeft (bN : Module.Basis (Fin n) R N) :
    ⋀[R]^(n + 1) (M × N) →ₗ[R] M :=
  exteriorPower.alternatingMapLinearEquiv (AlternatingMap.alternatizeUncurryFin (cofactorLinear bN))
theorem cofactorToLeft_ιMulti_cons (bN : Module.Basis (Fin n) R N) (m : M) :
    cofactorToLeft bN (exteriorPower.ιMulti R (n + 1) (Fin.cons (m, 0) fun i ↦ (0, bN i))) = m := by
  simp [cofactorToLeft, cofactorLinear, AlternatingMap.alternatizeUncurryFin_apply,
    Fin.sum_univ_succ, Module.Basis.det_self]
end Cofactor
theorem isPrincipal_of_isStablyFree {D : Type u} [CommRing D] [IsDomain D] [IsNoetherianRing D]
    (P : Ideal D)
    (hP : P ≠ ⊥) [IsStablyFree D P] : P.IsPrincipal := by
  obtain ⟨N, _, _, _, _, hfree⟩ := IsStablyFree.exist_free_prod D P
  let n := Module.finrank D N

  let 𝔭 : PrimeSpectrum D := ⟨⊥, Ideal.bot_prime⟩
  have h1 : rankAtStalk P 𝔭 = 1 := by
    let Dp := Localization.AtPrime 𝔭.asIdeal
    let pc := 𝔭.asIdeal.primeCompl
    let f := Algebra.linearMap D Dp
    let g := P.toLocalized' Dp pc f
    have htop : P.localized' Dp pc f = ⊤ := by
      rw [Ideal.localized'_eq_map]
      obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
      exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ ha)
        (IsLocalization.map_units Dp (⟨a, fun h ↦ ha0 h⟩ : pc))
    let e := ((IsLocalizedModule.linearEquiv pc (LocalizedModule.mkLinearMap pc P) g
      ).extendScalarsOfIsLocalization pc Dp).trans
      ((LinearEquiv.ofEq _ _ htop).trans (Submodule.topEquiv))
    change Module.finrank Dp (LocalizedModule pc P) = 1
    rw [e.finrank_eq, Module.finrank_self]
  have hp : Module.finrank D (P × N) = n + 1 := by
    have heq := congr($(rankAtStalk_prod P N) 𝔭)
    simp only [rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Pi.add_apply, h1] at heq
    grind
  let e : D ≃ₗ[D] ⋀[D]^(n + 1) (P × N) :=
    (Module.nonempty_linearEquiv_of_finrank_eq_one <| by simp [exteriorPower.finrank_eq, hp]).some
  let bN : Module.Basis (Fin n) D N := Module.finBasis D N
  let f : D →ₗ[D] P := cofactorToLeft bN ∘ₗ e
  have hf : Function.Surjective f := fun x ↦
    ⟨e.symm (exteriorPower.ιMulti D (n + 1) (Fin.cons (x, 0) fun i ↦ (0, bN i))), by
      simp [f, cofactorToLeft_ιMulti_cons]⟩
  refine ⟨(f 1 : D), ?_⟩
  apply le_antisymm
  · intro y hy
    obtain ⟨r, hr⟩ := hf ⟨y, hy⟩
    have : y = r * (f 1 : D) := by
      rw [← smul_eq_mul, ← Submodule.coe_smul, ← map_smul, smul_eq_mul, mul_one, hr]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact (f 1).2
open CategoryTheory in

theorem isStablyFree_localizedModule {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (T : Submonoid R) (k : ℕ) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : HasProjectiveDimensionLT (ModuleCat.of R M) (k + 1))
    (hproj : Module.Projective (Localization T) (LocalizedModule T M)) :
    IsStablyFree (Localization T) (LocalizedModule T M) := by
  induction k generalizing M with
  | zero =>
    rw [zero_add, ← projective_iff_hasProjectiveDimensionLT_one, ← IsProjective.iff_projective]
      at hM
    have : Module.Free R M := Module.free_of_flat_of_isLocalRing
    have := Module.free_of_isLocalizedModule (Rₛ := Localization T) T
      (LocalizedModule.mkLinearMap T M)
    infer_instance
  | succ k ih =>
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
    let K := LinearMap.ker π
    have hS := LinearMap.shortExact_shortComplexKer hπ
    have hprojF : Projective (π.shortComplexKer).X₂ := by
      rw [← IsProjective.iff_projective]; infer_instance
    have hK : HasProjectiveDimensionLT (ModuleCat.of R K) (k + 1) :=
      (hS.hasProjectiveDimensionLT_X₃_iff k hprojF).mp hM
    let A := Localization T
    let mkK := LocalizedModule.mkLinearMap T K
    let mkF := LocalizedModule.mkLinearMap T (Fin n → R)
    let mkM := LocalizedModule.mkLinearMap T M
    let φ₁ := (IsLocalizedModule.map T mkK mkF K.subtype).extendScalarsOfIsLocalization T A
    let φ₂ := (IsLocalizedModule.map T mkF mkM π).extendScalarsOfIsLocalization T A
    have hex0 : Function.Exact K.subtype π := fun y ↦
      ⟨fun h ↦ ⟨⟨y, h⟩, rfl⟩, by rintro ⟨k, rfl⟩; exact k.2⟩
    have ex : Function.Exact φ₁ φ₂ := LocalizedModule.map_exact T K.subtype π hex0
    have inj : Function.Injective φ₁ :=
      IsLocalizedModule.map_injective T mkK mkF K.subtype K.injective_subtype
    have surj : Function.Surjective φ₂ := IsLocalizedModule.map_surjective T mkF mkM π hπ
    obtain ⟨h, hh⟩ := Module.projective_lifting_property φ₂ LinearMap.id surj
    let e := (Function.Exact.splitSurjectiveEquiv (R := A) (M := LocalizedModule T K)
      (N := LocalizedModule T (Fin n → R)) (P := LocalizedModule T M) (f := φ₁) (g := φ₂) ex inj
      ⟨h, hh⟩).1
    have hFfree : Module.Free A (LocalizedModule T (Fin n → R)) :=
      Module.free_of_isLocalizedModule T mkF
    have : Module.Free A (LocalizedModule T K × LocalizedModule T M) := Module.Free.of_equiv e
    have hKproj : Module.Projective A (LocalizedModule T K) :=
      Module.Projective.of_split (LinearMap.inl A _ (LocalizedModule T M))
        (LinearMap.fst A _ _) (LinearMap.ext fun _ ↦ rfl)
    have hKsf := ih K hK hKproj
    obtain ⟨N, _, _, _, _, hNfree⟩ := IsStablyFree.exist_free_prod A (LocalizedModule T K)
    have : Module.Finite R K := inferInstance
    have : Module.Finite A (LocalizedModule T K) := inferInstance
    have : Module.Free A (LocalizedModule T M × (LocalizedModule T K × N)) := by
      exact Module.Free.of_equiv ((LinearEquiv.prodAssoc A (LocalizedModule T M)
        (LocalizedModule T K) N).symm.trans
          (((LinearEquiv.prodComm A _ _).trans e.symm).prodCongr (LinearEquiv.refl A N))).symm
    exact IsStablyFree.of_free_prod A (LocalizedModule T M) (LocalizedModule T K × N)
instance (priority := 100) IsRegularLocalRing.toIsDomain {R : Type u} [CommRing R]
    [IsRegularLocalRing R] : IsDomain R :=
  IsRegularLocalRing.isDomain
theorem isRegularLocalRing_localization_away_atPrime {S : Type u} [CommRing S]
    [IsRegularLocalRing S] {x : S} (hx : x ∈ maximalIdeal S)
    (q : Ideal (Localization.Away x)) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) ∧
      (maximalIdeal (Localization.AtPrime q)).spanFinrank < (maximalIdeal S).spanFinrank := by
  let A := Localization.Away x
  let Aq := Localization.AtPrime q
  let Q' := q.comap (algebraMap S A)
  have hQ' : Q'.IsPrime := Ideal.comap_isPrime _ _
  have : IsLocalization.AtPrime Aq Q' :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (Submonoid.powers x) Aq q
  have := IsRegularLocalRing.localization_atPrime Q'
  let e : Aq ≃ₐ[S] Localization.AtPrime Q' := IsLocalization.algEquiv Q'.primeCompl _ _
  have hreg : IsRegularLocalRing Aq := IsRegularLocalRing.of_ringEquiv e.symm.toRingEquiv
  refine ⟨hreg, ?_⟩
  have hxQ : x ∉ Q' := fun h ↦ hQ'.ne_top' (by
    have hu := IsLocalization.Away.algebraMap_isUnit (S := A) x
    exact (Ideal.comap_eq_top_iff).mpr (q.eq_top_of_isUnit_mem h hu))
  have hlt : Q' < maximalIdeal S :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hQ'.ne_top) (fun h ↦ hxQ (h ▸ hx))
  have h1 : ((maximalIdeal Aq).spanFinrank : WithBot ℕ∞) = (Q'.height : WithBot ℕ∞) := by
    rw [(isRegularLocalRing_iff Aq).mp hreg, IsLocalization.AtPrime.ringKrullDim_eq_height Q' Aq]
  have h2 : Q'.height + 1 ≤ (maximalIdeal S).height := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h3 : ((maximalIdeal S).height : WithBot ℕ∞) = ((maximalIdeal S).spanFinrank : WithBot ℕ∞) := by
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, (isRegularLocalRing_iff S).mp inferInstance]
  have h1' : Q'.height = ((maximalIdeal Aq).spanFinrank : ℕ∞) := by exact_mod_cast h1.symm
  have h3' : (maximalIdeal S).height = ((maximalIdeal S).spanFinrank : ℕ∞) := by exact_mod_cast h3
  rw [h1', h3'] at h2
  have : (maximalIdeal Aq).spanFinrank + 1 ≤ (maximalIdeal S).spanFinrank := by exact_mod_cast h2
  change (maximalIdeal Aq).spanFinrank < _
  omega
theorem IsRegularLocalRing.uniqueFactorizationMonoid (R : Type u) [CommRing R]
    [IsRegularLocalRing R] : UniqueFactorizationMonoid R := by
  suffices H : ∀ n : ℕ, ∀ (S : Type u) [CommRing S] [IsRegularLocalRing S],
      (maximalIdeal S).spanFinrank = n → UniqueFactorizationMonoid S from H _ R rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S _ _ hn
  have hd : ringKrullDim S = (n : WithBot ℕ∞) := by
    rw [← hn]; exact ((isRegularLocalRing_iff S).mp inferInstance).symm
  have hfg : (maximalIdeal S).FG := (maximalIdeal S).fg_of_isNoetherianRing
  by_cases h0 : n = 0
  · apply UniqueFactorizationMonoid.of_forall_isPrincipal_of_height_eq_one
    intro p hp hp1
    exfalso
    have h := Ideal.height_le_ringKrullDim_of_ne_top hp.ne_top
    rw [hp1, hd, h0] at h
    have : (1 : ℕ) ≤ 0 := by exact_mod_cast h
    omega
  have hjac : maximalIdeal S ≤ jacobson ⊥ :=
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  have hsq : ¬ maximalIdeal S ≤ maximalIdeal S ^ 2 := by
    intro hle
    have : maximalIdeal S = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg
      (by simpa [pow_two, smul_eq_mul] using hle) hjac
    exact h0 (by rw [← hn, this]; simp)
  obtain ⟨x, hx, hx2⟩ := Set.not_subset.mp hsq
  have hx0 : x ≠ 0 := fun h ↦ hx2 (h ▸ zero_mem _)
  have hne : span {x} ≠ ⊤ := fun h ↦ (IsLocalRing.maximalIdeal.isMaximal S).ne_top
    (top_le_iff.mp (h ▸ (span_singleton_le_iff_mem _).mpr hx))
  have : Nontrivial (S ⧸ span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsLocalRing (S ⧸ span {x}) := .of_surjective' _ Ideal.Quotient.mk_surjective
  obtain ⟨hreg, -⟩ := isRegularLocalRing_quotient hx hx2
  have hprime : (span {x} : Ideal S).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
  have hxp : Prime x := (Ideal.span_singleton_prime hx0).mp hprime
  rw [UniqueFactorizationMonoid.iff_localizationAway_of_prime hxp]
  let A := Localization.Away x
  have : IsDomain A := Localization.Away.isDomain hx0
  apply UniqueFactorizationMonoid.of_forall_isPrincipal_of_height_eq_one
  intro P hP hP1
  have hP0 : P ≠ ⊥ := P.ne_bot_of_height_eq_one hP1
  have : Module.FinitePresentation A P := Module.finitePresentation_of_finite A P

  have hPproj : Module.Projective A P := by
    apply Module.projective_of_localization_maximal
    intro q hq
    obtain ⟨hregq, hltq⟩ := isRegularLocalRing_localization_away_atPrime hx q
    let Aq := Localization.AtPrime q
    have : UniqueFactorizationMonoid Aq := ih _ (hn ▸ hltq) Aq rfl
    have hPq : (P.map (algebraMap A Aq)).IsPrincipal := by
      by_cases hle : P ≤ q
      · have hdisj : Disjoint (q.primeCompl : Set A) (P : Set A) := by
          rw [Set.disjoint_left]
          intro a ha haP
          exact ha (hle haP)
        have : (P.map (algebraMap A Aq)).IsPrime :=
          IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl Aq P hP hdisj
        exact UniqueFactorizationMonoid.isPrincipal_of_height_eq_one
          (by rw [IsLocalization.height_map_of_disjoint q.primeCompl P hdisj, hP1])
      · obtain ⟨a, haP, haq⟩ := Set.not_subset.mp hle
        have htop : P.map (algebraMap A Aq) = ⊤ := Ideal.eq_top_of_isUnit_mem _
          (Ideal.mem_map_of_mem _ haP) (IsLocalization.map_units Aq (⟨a, haq⟩ : q.primeCompl))
        rw [htop]
        exact ⟨⟨1, Ideal.span_singleton_one.symm⟩⟩
    let f := Algebra.linearMap A Aq
    let g := P.toLocalized' Aq q.primeCompl f
    let e := ((IsLocalizedModule.linearEquiv q.primeCompl (LocalizedModule.mkLinearMap q.primeCompl P)
      g).extendScalarsOfIsLocalization q.primeCompl Aq).trans
      (LinearEquiv.ofEq _ _ (Ideal.localized'_eq_map Aq q.primeCompl P))
    obtain ⟨⟨c, hc⟩⟩ := hPq
    have hfree : Module.Free Aq (P.map (algebraMap A Aq)) := by
      by_cases hc0 : c = 0
      · have : Subsingleton (P.map (algebraMap A Aq)) := by
          rw [hc, hc0, Submodule.span_singleton_eq_bot.mpr rfl]
          infer_instance
        infer_instance
      · exact Module.Free.of_equiv ((LinearEquiv.toSpanNonzeroSingleton Aq Aq c hc0).trans
          (LinearEquiv.ofEq _ _ hc.symm))
    exact Module.Projective.of_equiv e.symm

  let Q := P.comap (algebraMap S A)
  have hQpd := hasProjectiveDimensionLT_of_isRegularLocalRing hd Q
  let T := Submonoid.powers x
  let f := Algebra.linearMap S A
  let gQ := Q.toLocalized' A T f
  have hloc : Q.localized' A T f = P := by
    rw [Ideal.localized'_eq_map]; exact IsLocalization.map_comap T A P
  let eQ : LocalizedModule T Q ≃ₗ[A] P :=
    ((IsLocalizedModule.linearEquiv T (LocalizedModule.mkLinearMap T Q) gQ
      ).extendScalarsOfIsLocalization T A).trans (LinearEquiv.ofEq _ _ hloc)
  have hproj' : Module.Projective A (LocalizedModule T Q) := Module.Projective.of_equiv eQ.symm
  have hsf := isStablyFree_localizedModule T n Q hQpd hproj'
  have : IsStablyFree A P := IsStablyFree.equiv eQ
  exact isPrincipal_of_isStablyFree P hP0
instance (priority := 100) IsRegularLocalRing.toUniqueFactorizationMonoid {R : Type u} [CommRing R]
    [IsRegularLocalRing R] : UniqueFactorizationMonoid R :=
  IsRegularLocalRing.uniqueFactorizationMonoid R
end GroundTheory.Arith.SchemeCoh


