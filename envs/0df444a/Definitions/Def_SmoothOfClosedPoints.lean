-- Prove2me | Definitions.Def_SmoothOfClosedPoints
-- name    : SmoothOfClosedPoints
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/afb5d3a4-84ed-5cb4-8871-a1c140d983c3
-- title:
--   Smoothness of relative dimension from closed points
-- statement:
--   This module is a piece of commutative algebra and algebraic geometry: a criterion deducing smoothness of a quasi-compact scheme over an algebraically closed field from data at its closed points, together with the local ingredients it needs.
--
--   The first group of results works over a field $k$. For $k$ algebraically closed, $S$ a $k$-algebra of finite type and $m \subset S$ maximal, `bijective_algebraMap_quotient` states that $k \to S/m$ is bijective, i.e. $m$ is a rational point. The `Localization` section fixes a $k$-algebra $S$, an ideal $m$, an element $g$, and a $k$- and $S$-algebra $T$ which is the localisation of $S$ away from $g$ (with the scalar tower $k \to S \to T$); assuming $m$ maximal and $g \notin m$ it records that $x \in S$ lies in $m^2$ as soon as its image lies in $(mT)^2$, that $mT$ contracts to $m$, and, when $k \to S/m$ is surjective, that every $t \in T$ differs from the image of a constant by an element of $mT$. The map `mapCotangent` is the $k$-linear map $m/m^2 \to (mT)/(mT)^2$ induced by $S \to T$ (Mathlib's `Ideal.mapCotangent` along the tower algebra map), `mapCotangent_toCotangent` identifies it on classes of elements, and `mapCotangent_bijective`, `mapCotangentEquiv` give it as a $k$-linear isomorphism under the same hypotheses. Next, `finrank_cotangent_ker_eq`: for a surjective $k$-algebra map $\psi : T \to \kappa$ onto a field $\kappa$ with $k \to \kappa$ bijective, $T$ nontrivial and formally smooth over $k$ with $\Omega_{T/k}$ free of finite rank, $\dim_k (\ker\psi)/(\ker\psi)^2 = \operatorname{rank}_T \Omega_{T/k}$; the proof passes through the cotangent complex of the associated extension.
--
--   Combining these, `exists_isStandardSmoothOfRelativeDimension_of_formallySmooth` shows: for $k$ algebraically closed, $S$ of finite type, $m$ maximal with $S_m$ formally smooth over $k$ and $\dim_k m/m^2 = r$, there is $g \notin m$ with $S[1/g]$ standard smooth of relative dimension $r$ over $k$. Finally `SmoothOfRelativeDimension.of_forall_isClosed` states: if $X$ is a quasi-compact scheme with structure morphism $f : X \to \operatorname{Spec} k$ and every closed point $z$ of $X$ lies in the image of an open immersion $\operatorname{Spec} S \to X$ over $k$, with $S$ of finite type, at a prime $p$ with $S_p$ formally smooth over $k$ and $\dim_k p/p^2 = r$, then $f$ is smooth of relative dimension $r$.
--
--   **Relation to Mathlib.** All notions used are Mathlib's (`Ideal.Cotangent`, `Ideal.mapCotangent`, `Algebra.Extension` and its cotangent complex, `Algebra.IsStandardSmoothOfRelativeDimension`, `AlgebraicGeometry.SmoothOfRelativeDimension`); the module adds no new definitions beyond the induced cotangent map `mapCotangent` and the equivalence `mapCotangentEquiv` for a localisation away from an element, and the two criteria.
--
--   **Where it is used.** The scheme-theoretic criterion is the tool used elsewhere in the development to verify that a quasi-compact scheme over an algebraically closed field is smooth of a given relative dimension, by checking formal smoothness of the local ring and the dimension of the cotangent space at each closed point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_SmoothOfClosedPoints.lean

import Mathlib.AlgebraicGeometry.Morphisms.Smooth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

namespace SmoothOfClosedPoints

section Nullstellensatz

variable (k : Type*) {S : Type*} [Field k] [IsAlgClosed k] [CommRing S] [Algebra k S]
  [Algebra.FiniteType k S] (m : Ideal S) [m.IsMaximal]

theorem bijective_algebraMap_quotient : Function.Bijective (algebraMap k (S ⧸ m)) := by
  letI := Ideal.Quotient.field m
  haveI : Algebra.FiniteType k (S ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k m) (Ideal.Quotient.mkₐ_surjective k m)
  haveI : Module.Finite k (S ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (S ⧸ m)
  haveI : Algebra.IsIntegral k (S ⧸ m) := Algebra.IsIntegral.of_finite k (S ⧸ m)
  exact IsAlgClosed.ringHom_bijective_of_isIntegral (algebraMap k (S ⧸ m))
    (algebraMap_isIntegral_iff.mpr inferInstance)

end Nullstellensatz

section Localization

variable {k : Type*} {S : Type*} [Field k] [CommRing S] [Algebra k S]
  (m : Ideal S) {g : S}
  (T : Type*) [CommRing T] [Algebra S T] [Algebra k T] [IsScalarTower k S T]
  [IsLocalization.Away g T]

theorem mem_sq_of_algebraMap_mem_sq [hm : m.IsMaximal] (hg : g ∉ m) {x : S}
    (hx : algebraMap S T x ∈ Ideal.map (algebraMap S T) m ^ 2) : x ∈ m ^ 2 := by
  rw [← Ideal.map_pow, IsLocalization.mem_map_algebraMap_iff (Submonoid.powers g) T] at hx
  obtain ⟨⟨⟨y, hy⟩, ⟨s, hs⟩⟩, e⟩ := hx
  simp only at e
  rw [← map_mul, IsLocalization.eq_iff_exists (Submonoid.powers g) T] at e
  obtain ⟨⟨c, hc⟩, e⟩ := e
  simp only at e

  have hprim : (m ^ 2).IsPrimary :=
    Ideal.isPrimary_of_isMaximal_radical (by rw [Ideal.radical_pow _ two_ne_zero, hm.isPrime.radical]; exact hm)
  have hmem : x * (c * s) ∈ m ^ 2 := by
    have : c * (x * s) ∈ m ^ 2 := e ▸ Ideal.mul_mem_left _ c hy
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  rcases (Ideal.isPrimary_iff.mp hprim).2 hmem with h | h
  · exact h
  · exfalso
    rw [Ideal.radical_pow _ two_ne_zero, hm.isPrime.radical] at h
    have hcs : c * s ∈ Submonoid.powers g := Submonoid.mul_mem _ hc hs
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp hcs
    rw [← hn] at h
    exact hg (hm.isPrime.mem_of_pow_mem n h)

theorem comap_map_eq [hm : m.IsMaximal] (hg : g ∉ m) : (Ideal.map (algebraMap S T) m).comap (algebraMap S T) = m :=
  IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) T hm.isPrime
    ((Ideal.disjoint_powers_iff_notMem g hm.isPrime.isRadical).mpr hg)

theorem exists_sub_algebraMap_mem [hm : m.IsMaximal] (hg : g ∉ m)
    (hk : Function.Surjective (algebraMap k (S ⧸ m))) (t : T) :
    ∃ c : k, t - algebraMap k T c ∈ Ideal.map (algebraMap S T) m := by
  set J := Ideal.map (algebraMap S T) m with hJ

  have hS : ∀ x : S, ∃ c : k, algebraMap S T x - algebraMap k T c ∈ J := by
    intro x
    obtain ⟨c, hc⟩ := hk (Ideal.Quotient.mk m x)
    refine ⟨c, ?_⟩
    rw [IsScalarTower.algebraMap_apply k S T, ← map_sub]
    apply Ideal.mem_map_of_mem
    rw [← Ideal.Quotient.eq, ← hc, ← Ideal.Quotient.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply k S (S ⧸ m)]
  obtain ⟨⟨x, ⟨s, hs⟩⟩, e⟩ := IsLocalization.surj (Submonoid.powers g) t
  simp only at e

  obtain ⟨cx, hcx⟩ := hS x
  obtain ⟨cs, hcs⟩ := hS s
  have hcs0 : cs ≠ 0 := by
    rintro rfl
    rw [map_zero, sub_zero] at hcs
    have : s ∈ J.comap (algebraMap S T) := hcs
    rw [comap_map_eq m T hg] at this
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hs
    exact hg (hm.isPrime.mem_of_pow_mem n this)
  refine ⟨cx * cs⁻¹, ?_⟩

  rw [← Ideal.Quotient.eq] at hcx hcs ⊢
  have hu : Ideal.Quotient.mk J (algebraMap S T s) * Ideal.Quotient.mk J (algebraMap k T cs⁻¹) = 1 := by
    rw [hcs, ← map_mul, ← map_mul, mul_inv_cancel₀ hcs0, map_one, map_one]
  calc Ideal.Quotient.mk J t
      = Ideal.Quotient.mk J t * (Ideal.Quotient.mk J (algebraMap S T s)
          * Ideal.Quotient.mk J (algebraMap k T cs⁻¹)) := by rw [hu, mul_one]
    _ = Ideal.Quotient.mk J (algebraMap S T x) * Ideal.Quotient.mk J (algebraMap k T cs⁻¹) := by
          rw [← mul_assoc, ← map_mul, e]
    _ = Ideal.Quotient.mk J (algebraMap k T (cx * cs⁻¹)) := by rw [hcx, ← map_mul, ← map_mul]

noncomputable def mapCotangent :
    m.Cotangent →ₗ[k] (Ideal.map (algebraMap S T) m).Cotangent :=
  Ideal.mapCotangent m (Ideal.map (algebraMap S T) m) (IsScalarTower.toAlgHom k S T)
    (fun _ hx => Ideal.mem_map_of_mem (algebraMap S T) hx)

theorem mapCotangent_toCotangent (x : m) :
    mapCotangent (k := k) m T (m.toCotangent x)
      = (Ideal.map (algebraMap S T) m).toCotangent
          ⟨algebraMap S T x, Ideal.mem_map_of_mem (algebraMap S T) x.2⟩ :=
  Ideal.mapCotangent_toCotangent _ _ _ _ x

theorem mapCotangent_bijective [hm : m.IsMaximal] (hg : g ∉ m)
    (hk : Function.Surjective (algebraMap k (S ⧸ m))) :
    Function.Bijective (mapCotangent (k := k) m T) := by
  set J := Ideal.map (algebraMap S T) m with hJ
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    obtain ⟨x, rfl⟩ := m.toCotangent_surjective v
    rw [mapCotangent_toCotangent, Ideal.toCotangent_eq_zero] at hv
    exact (Ideal.toCotangent_eq_zero m x).mpr (mem_sq_of_algebraMap_mem_sq m T hg hv)
  · intro w
    obtain ⟨⟨y, hy⟩, rfl⟩ := J.toCotangent_surjective w
    obtain ⟨⟨⟨x, hx⟩, ⟨s, hs⟩⟩, e⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers g) T).mp hy
    simp only at e

    obtain ⟨u, hu⟩ := IsLocalization.map_units T (⟨s, hs⟩ : Submonoid.powers g)
    simp only at hu
    obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem m T hg hk (↑u⁻¹ : T)
    refine ⟨c • m.toCotangent ⟨x, hx⟩, ?_⟩
    rw [LinearMap.map_smul, mapCotangent_toCotangent]
    have hxJ : algebraMap S T x ∈ J := Ideal.mem_map_of_mem _ hx
    rw [← LinearMap.map_smul_of_tower, Ideal.toCotangent_eq]

    have hy' : y = ↑u⁻¹ * algebraMap S T x := by
      rw [← e, ← hu, mul_comm y, ← mul_assoc, Units.inv_mul, one_mul]
    have : ((c • (⟨algebraMap S T x, hxJ⟩ : J) : J) : T) - y
        = -( (↑u⁻¹ - algebraMap k T c) * algebraMap S T x) := by
      rw [hy']
      change c • algebraMap S T x - _ = _
      rw [Algebra.smul_def, sub_mul]; ring
    rw [this, Ideal.neg_mem_iff, pow_two]
    exact Ideal.mul_mem_mul hc hxJ

noncomputable def mapCotangentEquiv [m.IsMaximal] (hg : g ∉ m)
    (hk : Function.Surjective (algebraMap k (S ⧸ m))) :
    m.Cotangent ≃ₗ[k] (Ideal.map (algebraMap S T) m).Cotangent :=
  LinearEquiv.ofBijective _ (mapCotangent_bijective m T hg hk)

end Localization

section Conormal

variable {k : Type*} [Field k] {T : Type*} [CommRing T] [Algebra k T]
  {κ : Type*} [Field κ] [Algebra k κ] (ψ : T →ₐ[k] κ) (hψ : Function.Surjective ψ)
  (hk : Function.Bijective (algebraMap k κ))

include hψ hk in

theorem finrank_cotangent_ker_eq [Nontrivial T] [Algebra.FormallySmooth k T]
    [Module.Free T Ω[T⁄k]] [Module.Finite T Ω[T⁄k]] :
    Module.finrank k (RingHom.ker (ψ : T →+* κ)).Cotangent = Module.finrank T Ω[T⁄k] := by
  letI : Algebra T κ := (ψ : T →+* κ).toAlgebra
  haveI : IsScalarTower k T κ := IsScalarTower.of_algebraMap_eq' ψ.comp_algebraMap.symm
  let P : Algebra.Extension k κ :=
    { Ring := T
      σ := fun x => (hψ x).choose
      algebraMap_σ := fun x => (hψ x).choose_spec }
  haveI : Algebra.FormallySmooth k P.Ring := ‹Algebra.FormallySmooth k T›

  have hκ : Algebra.FormallySmooth k κ :=
    .of_equiv (AlgEquiv.ofBijective (Algebra.ofId k κ) hk)
  haveI : Subsingleton Ω[κ⁄k] := KaehlerDifferential.subsingleton_of_surjective k κ hk.2

  obtain ⟨l, hl⟩ := P.formallySmooth_iff_split_injection.mp hκ
  have hinj : Function.Injective P.cotangentComplex := by
    intro a b hab
    have := LinearMap.congr_fun hl a
    have := LinearMap.congr_fun hl b
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at *
    rw [← ‹l (P.cotangentComplex a) = a›, ← ‹l (P.cotangentComplex b) = b›, hab]
  have hsurj : Function.Surjective P.cotangentComplex := fun y =>
    (P.exact_cotangentComplex_toKaehler y).mp (Subsingleton.elim _ _)
  let e₄ : P.Cotangent ≃ₗ[κ] P.CotangentSpace := LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩

  let bΩ := Module.Free.chooseBasis T Ω[T⁄k]
  let bC : Module.Basis _ κ P.CotangentSpace := Algebra.TensorProduct.basis κ bΩ
  have h2 : Module.finrank κ P.CotangentSpace = Module.finrank T Ω[T⁄k] := by
    rw [Module.finrank_eq_card_basis bC, Module.finrank_eq_card_chooseBasisIndex]

  have h1 : Module.finrank k κ = 1 := by
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap k κ) hk).finrank_eq, Module.finrank_self]
  have h3 : Module.finrank k P.Cotangent = Module.finrank κ P.Cotangent := by
    rw [← Module.finrank_mul_finrank k κ P.Cotangent, h1, one_mul]
  have h4 : Module.finrank k (RingHom.ker (ψ : T →+* κ)).Cotangent = Module.finrank k P.Cotangent :=
    (P.cotangentEquivCotangentKer.restrictScalars k).finrank_eq.symm
  rw [h4, h3, e₄.finrank_eq, h2]

end Conormal

theorem exists_isStandardSmoothOfRelativeDimension_of_formallySmooth
    (k : Type u) (S : Type u) [Field k] [IsAlgClosed k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (m : Ideal S) [hm : m.IsMaximal] (r : ℕ)
    (hfs : Algebra.FormallySmooth k (Localization.AtPrime m))
    (hr : Module.finrank k m.Cotangent = r) :
    ∃ g ∉ m, Algebra.IsStandardSmoothOfRelativeDimension r k (Localization.Away g) := by
  haveI : Algebra.FinitePresentation k S := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  haveI : Algebra.IsSmoothAt k m := hfs
  obtain ⟨g, hg, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth k m
  refine ⟨g, hg, ?_⟩
  haveI := hstd
  haveI : Algebra.FormallySmooth k (Localization.Away g) := Algebra.Smooth.formallySmooth

  letI := Ideal.Quotient.field m
  have hk := bijective_algebraMap_quotient k m

  set T := Localization.Away g with hT
  have hunit : IsUnit (Ideal.Quotient.mk m g) :=
    isUnit_iff_ne_zero.mpr (fun h => hg (Ideal.Quotient.eq_zero_iff_mem.mp h))
  let ψ₀ : T →+* S ⧸ m := IsLocalization.Away.lift g hunit
  have hψ₀ : ∀ x : S, ψ₀ (algebraMap S T x) = Ideal.Quotient.mk m x :=
    fun x => IsLocalization.Away.lift_eq g hunit x
  let ψ : T →ₐ[k] S ⧸ m :=
    { ψ₀ with
      commutes' := fun c => by
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
          MonoidHom.coe_coe]
        rw [IsScalarTower.algebraMap_apply k S T, hψ₀, ← Ideal.Quotient.algebraMap_eq,
          ← IsScalarTower.algebraMap_apply] }
  have hψ : Function.Surjective ψ := fun q => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨algebraMap S T x, hψ₀ x⟩

  have hker : RingHom.ker (ψ : T →+* S ⧸ m) = Ideal.map (algebraMap S T) m := by
    have hunder : (RingHom.ker (ψ : T →+* S ⧸ m)).comap (algebraMap S T) = m := by
      ext x
      rw [Ideal.mem_comap, RingHom.mem_ker]
      show ψ₀ (algebraMap S T x) = 0 ↔ x ∈ m
      rw [hψ₀, Ideal.Quotient.eq_zero_iff_mem]
    rw [← IsLocalization.map_under (Submonoid.powers g) T (RingHom.ker (ψ : T →+* S ⧸ m))]
    show Ideal.map (algebraMap S T) ((RingHom.ker (ψ : T →+* S ⧸ m)).comap (algebraMap S T)) = _
    rw [hunder]
  haveI : Nontrivial T := (ψ : T →+* S ⧸ m).domain_nontrivial

  have key := finrank_cotangent_ker_eq ψ hψ hk
  have hΩ : Module.finrank T Ω[T⁄k] = r := by
    rw [← key, ← hr]
    exact ((mapCotangentEquiv m T hg hk.2).trans
      ((Ideal.Cotangent.equivOfEq _ _ hker.symm).restrictScalars k)).finrank_eq.symm
  exact (Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth r).mpr
    (by rw [← Module.finrank_eq_rank, hΩ])

end SmoothOfClosedPoints

namespace AlgebraicGeometry

theorem SmoothOfRelativeDimension.of_forall_isClosed
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [CompactSpace X]
    (f : X ⟶ Spec (.of k)) (r : ℕ)
    (h : ∀ z : X, IsClosed ({z} : Set X) →
      ∃ (S : Type u) (_ : CommRing S) (_ : Algebra k S) (_ : Algebra.FiniteType k S)
        (ι : Spec (.of S) ⟶ X) (_ : IsOpenImmersion ι)
        (_ : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k S)))
        (p : PrimeSpectrum S), ι p = z ∧
          Algebra.FormallySmooth k (Localization.AtPrime p.asIdeal) ∧
          Module.finrank k p.asIdeal.Cotangent = r) :
    SmoothOfRelativeDimension r f := by

  have main : ∀ x : X, ∃ (R : CommRingCat.{u}) (φ : CommRingCat.of k ⟶ R) (j : Spec R ⟶ X)
      (_ : IsOpenImmersion j), x ∈ Set.range j ∧ j ≫ f = Spec.map φ ∧
        RingHom.IsStandardSmoothOfRelativeDimension r φ.hom := by
    intro x
    obtain ⟨z, hzx, hz⟩ := (isClosed_closure (s := ({x} : Set X))).exists_closed_singleton
      ⟨x, subset_closure rfl⟩
    obtain ⟨S, _, _, _, ι, _, hιf, p, hpz, hfs, hr⟩ := h z hz

    have hpcl : IsClosed ({p} : Set (PrimeSpectrum S)) := by
      have : ({p} : Set (PrimeSpectrum S)) = ι ⁻¹' {z} := by
        ext q
        simp only [Set.mem_singleton_iff]
        exact ⟨fun hq => hq ▸ hpz, fun hq => ι.isOpenEmbedding.injective (hq.trans hpz.symm)⟩
      rw [this]
      exact hz.preimage ι.continuous
    haveI : p.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp hpcl
    obtain ⟨g, hg, hT⟩ :=
      SmoothOfClosedPoints.exists_isStandardSmoothOfRelativeDimension_of_formallySmooth
        k S p.asIdeal r hfs hr
    refine ⟨CommRingCat.of (Localization.Away g), CommRingCat.ofHom (algebraMap k _),
      Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))) ≫ ι, inferInstance,
      ?_, ?_, (RingHom.isStandardSmoothOfRelativeDimension_algebraMap r).mpr hT⟩
    ·
      have hxι : x ∈ Set.range ι := by
        obtain ⟨y, hy, hy'⟩ := mem_closure_iff.mp hzx (Set.range ι)
          ι.isOpenEmbedding.isOpen_range ⟨p, hpz⟩
        rw [Set.mem_singleton_iff.mp hy'] at hy
        exact hy
      obtain ⟨y, rfl⟩ := hxι
      have hyp : y ⤳ p := by
        apply ι.isOpenEmbedding.isInducing.specializes_iff.mp
        rw [hpz]
        exact specializes_iff_mem_closure.mpr hzx
      have hgy : g ∉ y.asIdeal := fun hgy => hg ((PrimeSpectrum.le_iff_specializes y p).mpr hyp hgy)
      have hyr : y ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := by
        rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
        exact hgy
      obtain ⟨y', hy'⟩ := hyr
      exact ⟨y', by rw [Scheme.Hom.comp_apply]; exact congrArg ι hy'⟩
    · rw [Category.assoc, hιf, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← IsScalarTower.algebraMap_eq]
  choose R φ j hj hxj hjf hT using main
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers X (fun x => Spec (R x)) j
    (fun x => by obtain ⟨y, hy⟩ := hxj x; exact ⟨x, y, hy⟩) hj
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @SmoothOfRelativeDimension r) 𝒰]
  intro x
  show SmoothOfRelativeDimension r (j x ≫ f)
  rw [hjf x, HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension r)]
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ (hT x)

end AlgebraicGeometry

#print axioms SmoothOfClosedPoints.bijective_algebraMap_quotient
#print axioms SmoothOfClosedPoints.mapCotangentEquiv
#print axioms SmoothOfClosedPoints.finrank_cotangent_ker_eq
#print axioms SmoothOfClosedPoints.exists_isStandardSmoothOfRelativeDimension_of_formallySmooth
#print axioms AlgebraicGeometry.SmoothOfRelativeDimension.of_forall_isClosed


