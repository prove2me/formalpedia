-- Prove2me | solution 1 for Algebra.FormallySmooth.isDiscreteValuationRing_localizationAtPrime_of_krullDimLE_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/c8d18995-de1c-56f8-8fc8-0bebe3352169

import Mathlib
import Theorems.Thm_Algebra_IsStandardSmoothOfRelativeDimension_isDiscreteValuationRing_localization_atPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_FormallySmooth_isDiscreteValuationRing_localizationAtPrime_of_krullDimLE_one

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open Algebra IsLocalRing

namespace L1BE1

theorem isStandardSmoothOfRelativeDimension_mvPolynomial (k : Type) [CommRing k] (n : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension n k (MvPolynomial (Fin n) k) := by
  classical

  let v : PEmpty.{1} → MvPolynomial (Fin n) k := fun e => nomatch e
  let a : PEmpty.{1} → Fin n := fun e => nomatch e
  have ha : Function.Injective a := fun e => nomatch e
  let P₀ : Algebra.PreSubmersivePresentation k (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range v)) (Fin n) PEmpty.{1} :=
    Algebra.PreSubmersivePresentation.naive a ha
  have hjac : IsUnit P₀.jacobian := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    have : P₀.jacobiMatrix = 1 := by
      ext i j; exact nomatch i
    rw [this, Matrix.det_one, map_one]
    exact isUnit_one
  let P₁ : Algebra.SubmersivePresentation k (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range v)) (Fin n) PEmpty.{1} :=
    { toPreSubmersivePresentation := P₀, jacobian_isUnit := hjac }

  have hbot : Ideal.span (Set.range v) = (⊥ : Ideal (MvPolynomial (Fin n) k)) := by
    rw [Ideal.span_eq_bot]; rintro _ ⟨e, _⟩; exact nomatch e
  let e : (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range v)) ≃ₐ[k] MvPolynomial (Fin n) k :=
    (Ideal.quotientEquivAlgOfEq k hbot).trans (AlgEquiv.quotientBot k (MvPolynomial (Fin n) k))
  let P : Algebra.SubmersivePresentation k (MvPolynomial (Fin n) k) (Fin n) PEmpty.{1} := P₁.ofAlgEquiv e
  refine ⟨⟨Fin n, PEmpty.{1}, inferInstance, inferInstance, P, ?_⟩⟩

  simp [Algebra.Presentation.dimension]

end L1BE1

namespace L1BE1

theorem isDiscreteValuationRing_of_ringEquiv {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] (e : A ≃+* B) : IsDiscreteValuationRing B := by
  haveI : IsPrincipalIdealRing B := IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
  haveI : IsLocalRing B := IsLocalRing.of_surjective' e.toRingHom e.surjective
  refine { not_a_field' := ?_ }
  intro hbot
  apply IsDiscreteValuationRing.not_a_field A
  rw [eq_bot_iff] at hbot ⊢
  intro x hx
  have hx' : e x ∈ maximalIdeal B := by
    rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    exact fun hu => hx (by simpa using hu.map e.symm)
  have := hbot hx'
  rw [Ideal.mem_bot] at this ⊢
  exact e.injective (by rw [this, map_zero])

theorem exists_ltSeries_of_forall_X_sub_C_mem {k : Type} [Field k] (n : ℕ) (a : Fin n → k)
    (𝔮 : Ideal (MvPolynomial (Fin n) k)) [h𝔮p : 𝔮.IsPrime]
    (h𝔮 : ∀ i, MvPolynomial.X i - MvPolynomial.C (a i) ∈ 𝔮) :
    ∃ l : LTSeries (PrimeSpectrum (MvPolynomial (Fin n) k)), l.length = n ∧
      RelSeries.last l = ⟨𝔮, h𝔮p⟩ := by
  classical
  let φ : ℕ → (MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) k) := fun j =>
    MvPolynomial.aeval fun i : Fin n => if (i : ℕ) < j then MvPolynomial.C (a i) else MvPolynomial.X i
  have hφX : ∀ j (i : Fin n), φ j (MvPolynomial.X i) =
      if (i : ℕ) < j then MvPolynomial.C (a i) else MvPolynomial.X i := fun j i => MvPolynomial.aeval_X _ i
  have hφC : ∀ j (c : k), φ j (MvPolynomial.C c) = MvPolynomial.C c := fun j c => (φ j).commutes c
  let P : ℕ → Ideal (MvPolynomial (Fin n) k) := fun j => RingHom.ker (φ j).toRingHom
  have hPprime : ∀ j, (P j).IsPrime := fun j => RingHom.ker_isPrime (φ j).toRingHom
  have hmemP : ∀ j p, p ∈ P j ↔ φ j p = 0 := fun j p => RingHom.mem_ker
  have hcomp : ∀ j p, φ (j + 1) (φ j p) = φ (j + 1) p := by
    intro j p
    have : (φ (j + 1)).comp (φ j) = φ (j + 1) := by
      apply MvPolynomial.algHom_ext
      intro i
      rw [AlgHom.comp_apply, hφX j]
      split_ifs with h
      · rw [hφC, hφX, if_pos (Nat.lt_succ_of_lt h)]
      · rfl
    exact congrArg (fun g => g p) (congrArg DFunLike.coe this)
  have hmono : ∀ j, P j ≤ P (j + 1) := by
    intro j p hp
    rw [hmemP] at hp ⊢
    rw [← hcomp, hp, map_zero]
  have hmem_succ : ∀ (j : ℕ) (hj : j < n),
      MvPolynomial.X (⟨j, hj⟩ : Fin n) - MvPolynomial.C (a ⟨j, hj⟩) ∈ P (j + 1) := by
    intro j hj
    rw [hmemP, map_sub, hφX, hφC]
    simp
  have hnot_mem : ∀ (j : ℕ) (hj : j < n),
      MvPolynomial.X (⟨j, hj⟩ : Fin n) - MvPolynomial.C (a ⟨j, hj⟩) ∉ P j := by
    intro j hj h
    rw [hmemP, map_sub, hφX, hφC] at h
    simp only [lt_self_iff_false, if_false] at h
    have := congrArg (MvPolynomial.eval (Function.update (fun _ : Fin n => (0 : k)) ⟨j, hj⟩ (a ⟨j, hj⟩ + 1))) h
    simp [MvPolynomial.eval_X, MvPolynomial.eval_C, Function.update_self] at this
  have hPle : ∀ j, P j ≤ 𝔮 := by
    intro j p hp
    rw [hmemP] at hp
    have hagree : (Ideal.Quotient.mkₐ k 𝔮).comp (φ j) = Ideal.Quotient.mkₐ k 𝔮 := by
      apply MvPolynomial.algHom_ext
      intro i
      rw [AlgHom.comp_apply, hφX]
      split_ifs with h
      · exact ((Ideal.Quotient.eq).mpr (h𝔮 i)).symm
      · rfl
    have := congrArg (fun g => g p) (congrArg DFunLike.coe hagree)
    simp only [AlgHom.comp_apply, hp, map_zero] at this
    rw [Ideal.Quotient.mkₐ_eq_mk] at this
    exact Ideal.Quotient.eq_zero_iff_mem.mp this.symm
  let f : Fin (n + 1) → PrimeSpectrum (MvPolynomial (Fin n) k) := fun i =>
    if h : (i : ℕ) < n then ⟨P i, hPprime i⟩ else ⟨𝔮, h𝔮p⟩
  have hstep : ∀ i : Fin n, f (Fin.castSucc i) < f i.succ := by
    intro i
    have hi : (i : ℕ) < n := i.2
    simp only [f, Fin.val_castSucc, Fin.val_succ, dif_pos hi]
    by_cases h : (i : ℕ) + 1 < n
    · rw [dif_pos h]
      refine lt_of_le_of_ne (hmono i) fun heq => ?_
      have h1 := hmem_succ i hi
      have : P ((i : ℕ) + 1) = P i := (congrArg PrimeSpectrum.asIdeal heq).symm
      rw [this] at h1
      exact hnot_mem i hi h1
    · rw [dif_neg h]
      refine lt_of_le_of_ne (hPle i) fun heq => ?_
      have : 𝔮 = P i := (congrArg PrimeSpectrum.asIdeal heq).symm
      exact hnot_mem i hi (this ▸ h𝔮 ⟨i, hi⟩)
  refine ⟨LTSeries.mk n f (Fin.strictMono_iff_lt_succ.mpr hstep), rfl, ?_⟩
  show f (Fin.last n) = _
  simp only [f, Fin.val_last, lt_self_iff_false, dif_neg, not_false_eq_true]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem relDim_eq_one {k R : Type} [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    (hdim : Ring.KrullDimLE 1 R) (𝔫 : Ideal R) [𝔫.IsMaximal] (hne : 𝔫 ≠ ⊥)
    (hrat : Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap k R)))
    (f : R) (hf : f ∉ 𝔫) (n : ℕ)
    [Algebra (MvPolynomial (Fin n) k) (Localization.Away f)]
    [IsScalarTower k (MvPolynomial (Fin n) k) (Localization.Away f)]
    [Algebra.IsStandardEtale (MvPolynomial (Fin n) k) (Localization.Away f)] : n = 1 := by
  classical
  haveI h𝔫p : 𝔫.IsPrime := Ideal.IsMaximal.isPrime ‹_›
  have hfield : IsField (R ⧸ 𝔫) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient 𝔫).mp ‹_›
  have hf0 : f ≠ 0 := fun h => hf (h ▸ 𝔫.zero_mem)
  have hle : Submonoid.powers f ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hf0
  haveI : IsDomain (Localization.Away f) := IsLocalization.isDomain_localization hle
  have hinj : Function.Injective (algebraMap R (Localization.Away f)) := IsLocalization.injective _ hle
  have hdisj : Disjoint (↑(Submonoid.powers f) : Set R) (↑𝔫 : Set R) := by
    rw [Set.disjoint_left]
    rintro x ⟨m, rfl⟩ hx
    exact hf (Ideal.IsPrime.mem_of_pow_mem h𝔫p m hx)
  set 𝔫' : Ideal (Localization.Away f) := 𝔫.map (algebraMap R (Localization.Away f)) with h𝔫'
  haveI h𝔫'p : 𝔫'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) _ 𝔫 h𝔫p hdisj
  have hunder : 𝔫'.comap (algebraMap R (Localization.Away f)) = 𝔫 :=
    IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers f) (Localization.Away f) h𝔫p hdisj
  haveI hEt : Algebra.Etale (MvPolynomial (Fin n) k) (Localization.Away f) := inferInstance
  haveI hflat : Module.Flat (MvPolynomial (Fin n) k) (Localization.Away f) := inferInstance
  haveI hgd : Algebra.HasGoingDown (MvPolynomial (Fin n) k) (Localization.Away f) := Algebra.HasGoingDown.of_flat
  have halgk : ∀ c : k, algebraMap k (Localization.Away f) c =
      algebraMap (MvPolynomial (Fin n) k) (Localization.Away f) (MvPolynomial.C c) := fun c => by
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  have halgkR : ∀ c : k, algebraMap k (Localization.Away f) c =
      algebraMap R (Localization.Away f) (algebraMap k R c) := fun c => IsScalarTower.algebraMap_apply k R _ c

  have hrat' : ∀ z : Localization.Away f, ∃ c : k, z - algebraMap k (Localization.Away f) c ∈ 𝔫' := by
    intro z
    obtain ⟨⟨r, ⟨s, hs⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) z
    have hs𝔫 : s ∉ 𝔫 := Set.disjoint_left.mp hdisj hs
    have hs0 : Ideal.Quotient.mk 𝔫 s ≠ 0 := fun h => hs𝔫 (Ideal.Quotient.eq_zero_iff_mem.mp h)
    obtain ⟨t, ht⟩ := hfield.mul_inv_cancel hs0
    obtain ⟨s₂, rfl⟩ := Ideal.Quotient.mk_surjective t
    obtain ⟨c₁, hc₁⟩ := hrat (Ideal.Quotient.mk 𝔫 r)
    obtain ⟨c₂, hc₂⟩ := hrat (Ideal.Quotient.mk 𝔫 s₂)
    simp only [RingHom.comp_apply] at hc₁ hc₂
    refine ⟨c₁ * c₂, ?_⟩
    have hsu : IsUnit (algebraMap R (Localization.Away f) s) := IsLocalization.map_units _ ⟨s, hs⟩
    rw [← Ideal.unit_mul_mem_iff_mem 𝔫' hsu]
    have hkey : algebraMap R (Localization.Away f) s *
        (IsLocalization.mk' (Localization.Away f) r ⟨s, hs⟩ - algebraMap k (Localization.Away f) (c₁ * c₂)) =
        algebraMap R (Localization.Away f) (r - s * (algebraMap k R c₁ * algebraMap k R c₂)) := by
      rw [mul_sub, mul_comm, IsLocalization.mk'_spec, halgkR, map_sub, map_mul, map_mul, map_mul, map_mul]
    rw [hkey, h𝔫']
    apply Ideal.mem_map_of_mem
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_mul, hc₁, hc₂, sub_eq_zero]
    calc Ideal.Quotient.mk 𝔫 r = Ideal.Quotient.mk 𝔫 r * (Ideal.Quotient.mk 𝔫 s * Ideal.Quotient.mk 𝔫 s₂) := by
          rw [ht, mul_one]
      _ = Ideal.Quotient.mk 𝔫 s * (Ideal.Quotient.mk 𝔫 r * Ideal.Quotient.mk 𝔫 s₂) := by ring

  set 𝔮 : Ideal (MvPolynomial (Fin n) k) := 𝔫'.comap (algebraMap (MvPolynomial (Fin n) k) (Localization.Away f)) with h𝔮
  haveI h𝔮p : 𝔮.IsPrime := Ideal.comap_isPrime _ 𝔫'
  have hX : ∀ i : Fin n, ∃ a : k, MvPolynomial.X i - MvPolynomial.C a ∈ 𝔮 := by
    intro i
    obtain ⟨a, ha⟩ := hrat' (algebraMap (MvPolynomial (Fin n) k) (Localization.Away f) (MvPolynomial.X i))
    refine ⟨a, ?_⟩
    rw [h𝔮, Ideal.mem_comap, map_sub, ← halgk]
    exact ha
  choose a ha using hX

  have hn1 : n ≤ 1 := by
    obtain ⟨l, hl, hlast⟩ := exists_ltSeries_of_forall_X_sub_C_mem n a 𝔮 ha
    haveI : 𝔫'.LiesOver (RelSeries.last l).asIdeal := ⟨by rw [hlast]⟩
    obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l 𝔫'

    have hsm : StrictMono (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) :=
      Monotone.strictMono_of_injective (fun p q hpq => Ideal.comap_mono hpq)
        (PrimeSpectrum.localization_comap_injective (Localization.Away f) (Submonoid.powers f))
    let L' : LTSeries (PrimeSpectrum R) := L.map _ hsm
    have h1 : (L'.length : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum R) := Order.LTSeries.length_le_krullDim L'
    have h2 : Order.krullDim (PrimeSpectrum R) ≤ (1 : ℕ) := hdim.krullDim_le
    have h3 : L'.length = n := by rw [← hl, ← hL]; rfl
    rw [h3] at h1
    exact_mod_cast h1.trans h2

  have hn0 : n ≠ 0 := by
    intro hn
    subst hn

    haveI : Algebra.FormallyEtale k (MvPolynomial (Fin 0) k) :=
      Algebra.FormallyEtale.of_equiv (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).symm
    haveI : Algebra.FormallyUnramified k (MvPolynomial (Fin 0) k) := inferInstance
    haveI : Algebra.FormallyUnramified (MvPolynomial (Fin 0) k) (Localization.Away f) := inferInstance
    haveI : Algebra.EssFiniteType (MvPolynomial (Fin 0) k) (Localization.Away f) := inferInstance
    haveI : Algebra.FormallyUnramified k (Localization.Away f) :=
      Algebra.FormallyUnramified.comp k (MvPolynomial (Fin 0) k) (Localization.Away f)
    haveI : Algebra.EssFiniteType k (Localization.Away f) :=
      Algebra.EssFiniteType.comp k (MvPolynomial (Fin 0) k) (Localization.Away f)
    haveI : Module.Finite k (Localization.Away f) := Algebra.FormallyUnramified.finite_of_free k (Localization.Away f)
    haveI : Algebra.IsIntegral k (Localization.Away f) := Algebra.IsIntegral.of_finite k (Localization.Away f)
    have hF : IsField (Localization.Away f) := isField_of_isIntegral_of_isField' (Field.toIsField k)
    apply hne
    rw [← hunder]
    have h𝔫'bot : 𝔫' = ⊥ := by
      refine eq_bot_iff.mpr fun x hx => ?_
      by_contra hx0
      obtain ⟨y, hy⟩ := hF.mul_inv_cancel hx0
      exact h𝔫'p.ne_top (Ideal.eq_top_of_isUnit_mem _ hx (IsUnit.of_mul_eq_one (b := y) hy))
    rw [h𝔫'bot, Ideal.comap_bot_of_injective _ hinj]
  omega

end L1BE1

theorem solution
    {k : Type} [Field k] {R : Type} [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.FormallySmooth k R] [Algebra.FinitePresentation k R] (hdim : Ring.KrullDimLE 1 R)
    (𝔫 : Ideal R) [𝔫.IsMaximal] (hne : 𝔫 ≠ ⊥)
    (hrat : Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap k R))) :
    ∃ _ : IsDomain (Localization.AtPrime 𝔫), IsDiscreteValuationRing (Localization.AtPrime 𝔫) := by
  classical

  haveI : Algebra.IsSmoothAt k 𝔫 := by
    haveI : Algebra.FormallySmooth R (Localization.AtPrime 𝔫) :=
      Algebra.FormallySmooth.of_isLocalization 𝔫.primeCompl
    exact Algebra.FormallySmooth.comp k R (Localization.AtPrime 𝔫)
  obtain ⟨f, hf, n, alg, hst, hse⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (S := R) (p := 𝔫)
  letI := alg
  haveI := hst
  haveI := hse
  have hn : n = 1 := L1BE1.relDim_eq_one hdim 𝔫 hne hrat f hf n
  subst hn

  let Rf := Localization.Away f
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 (MvPolynomial (Fin 1) k) Rf :=
    (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero).mp inferInstance
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 1 k (MvPolynomial (Fin 1) k) :=
    L1BE1.isStandardSmoothOfRelativeDimension_mvPolynomial k 1
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 1 k Rf := by
    have := Algebra.IsStandardSmoothOfRelativeDimension.trans (n := 1) (m := 0)
      (R := k) (S := MvPolynomial (Fin 1) k) (T := Rf)
    simpa using this

  let 𝔫' : Ideal Rf := 𝔫.map (algebraMap R Rf)
  have hdisj : Disjoint (↑(Submonoid.powers f) : Set R) (↑𝔫 : Set R) :=
    (Ideal.disjoint_powers_iff_notMem _ ‹𝔫.IsMaximal›.isPrime.isRadical).mpr hf
  haveI h𝔫'p : 𝔫'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) Rf 𝔫 inferInstance hdisj
  have hcomap : 𝔫'.comap (algebraMap R Rf) = 𝔫 :=
    IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers f) Rf inferInstance hdisj
  haveI : 𝔫'.IsMaximal := by
    refine ⟨⟨h𝔫'p.ne_top, fun Q hQ => ?_⟩⟩
    by_contra hQtop
    have hle : 𝔫 ≤ Q.comap (algebraMap R Rf) := by
      rw [← hcomap]; exact Ideal.comap_mono hQ.le
    have hQ' : Q.comap (algebraMap R Rf) ≠ ⊤ := fun htop =>
      hQtop ((Ideal.eq_top_iff_one _).mpr (by
        have : (1 : R) ∈ Q.comap (algebraMap R Rf) := by rw [htop]; trivial
        simpa using this))
    have heq : Q.comap (algebraMap R Rf) = 𝔫 := (‹𝔫.IsMaximal›.eq_of_le hQ' hle).symm
    have hQeq : Q = 𝔫' := by
      have hmu : (Q.comap (algebraMap R Rf)).map (algebraMap R Rf) = Q :=
        IsLocalization.map_under (Submonoid.powers f) Rf Q
      rw [heq] at hmu
      exact hmu.symm
    exact absurd hQ (by rw [hQeq]; exact lt_irrefl _)

  obtain ⟨hdom', hdvr'⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.isDiscreteValuationRing_localization_atPrime
      (k := k) (A := Rf) 𝔫'
  haveI := hdom'
  haveI := hdvr'
  have hloc : IsLocalization.AtPrime (Localization.AtPrime 𝔫') (𝔫'.comap (algebraMap R Rf)) :=
    IsLocalization.isLocalization_atPrime_localization_atPrime (Submonoid.powers f) 𝔫'
  haveI : IsLocalization 𝔫.primeCompl (Localization.AtPrime 𝔫') := by
    have hsub : 𝔫.primeCompl = (𝔫'.comap (algebraMap R Rf)).primeCompl := by
      ext x
      show x ∈ (↑𝔫 : Set R)ᶜ ↔ x ∈ (↑(𝔫'.comap (algebraMap R Rf)) : Set R)ᶜ
      rw [hcomap]
    rw [hsub]; exact hloc
  haveI : IsDomain (Localization.AtPrime 𝔫) :=
    IsLocalization.isDomain_localization 𝔫.primeCompl_le_nonZeroDivisors
  let e : Localization.AtPrime 𝔫 ≃ₐ[R] Localization.AtPrime 𝔫' :=
    IsLocalization.algEquiv 𝔫.primeCompl (Localization.AtPrime 𝔫) (Localization.AtPrime 𝔫')
  exact ⟨inferInstance, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e.symm⟩

end S_Algebra_FormallySmooth_isDiscreteValuationRing_localizationAtPrime_of_krullDimLE_one
end P2MW
export P2MW.S_Algebra_FormallySmooth_isDiscreteValuationRing_localizationAtPrime_of_krullDimLE_one (solution)
