-- Prove2me | solution 1 for AlgebraicCurve.card_places_deg_one_eq_sum_divisors_of_constantFieldExtension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/68724a35-a07c-5100-a854-abd5138fb8e7

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_card_places_deg_one_eq_sum_divisors_of_constantFieldExtension

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial IsDedekindDomain IsLocalRing

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver IsCurveOver.finite_residueField IsCurveOver.finiteResidue Place Place.deg HasPrincipalDivisors HasPrincipalDivisors.exists_divisor Place.fiberEquiv"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField deg ord ord_inv ne_top' toValuationSubring mk mem_maximalIdeal_iff_ord_pos integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter toValuationSubring_eq_of_restrict_eq fiberEquiv restrict forgetConstants constantFieldEquiv restrictConstants restrictConstants_fiber_finite"
namespace ConstFieldExtCount
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

theorem ker_eq_maximalIdeal {R L : Type*} [CommRing R] [IsLocalRing R] [Field L] [Finite L]
    (ψ : R →+* L) : RingHom.ker ψ = maximalIdeal R := by
  haveI : Finite ψ.range := inferInstance
  have hf : IsField ψ.range := Finite.isField_of_domain ψ.range
  have hq : IsField (R ⧸ RingHom.ker ψ) :=
    MulEquiv.isField hf (RingHom.quotientKerEquivRange ψ).toMulEquiv
  exact IsLocalRing.eq_maximalIdeal (Ideal.Quotient.maximal_of_isField _ hq)

section Local

variable {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F']
  [Algebra F F'] [IsScalarTower k F F']
  {k' : Type*} [Field k'] [Algebra k k'] [Algebra k' F'] [IsScalarTower k k' F']

scoped instance isScalarTower_valuationSubring (v : Place k F) :
    IsScalarTower k v.toValuationSubring F' :=
  IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply k F F' a,
      IsScalarTower.algebraMap_apply k v.toValuationSubring F a,
      ← IsScalarTower.algebraMap_apply v.toValuationSubring F F']

variable [Algebra.IsIntegral k k']

def constHom (v : Place k F) : k' →+* integralClosureAt F' v :=
  (algebraMap k' F').codRestrict (integralClosure v.toValuationSubring F') fun a =>
    (mem_integralClosure_iff _ _).mpr
      (((Algebra.IsIntegral.isIntegral (R := k) a).map
        (IsScalarTower.toAlgHom k k' F')).tower_top)

@[scoped simp] theorem coe_constHom (v : Place k F) (a : k') :
    ((constHom (F' := F') v a : integralClosureAt F' v) : F') = algebraMap k' F' a := rfl

theorem algebraMap_constHom (v : Place k F) (a : k') :
    algebraMap (integralClosureAt F' v) F' (constHom v a) = algebraMap k' F' a := rfl

theorem algebraMap_algebraMap_eq_constHom (v : Place k F) (a : k) :
    algebraMap v.toValuationSubring (integralClosureAt F' v) (algebraMap k v.toValuationSubring a)
      = constHom v (algebraMap k k' a) := by
  apply Subtype.ext
  change algebraMap F F' (algebraMap k F a) = algebraMap k' F' (algebraMap k k' a)
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem constHom_comp_algebraMap (v : Place k F) :
    (constHom (F' := F') v).comp (algebraMap k k')
      = (algebraMap v.toValuationSubring (integralClosureAt F' v)).comp
          (algebraMap k v.toValuationSubring) := by
  refine RingHom.ext fun a => ?_
  simp only [RingHom.comp_apply, algebraMap_algebraMap_eq_constHom (k' := k')]

variable (k') in

def HomO (v : Place k F) : Type _ :=
  {ψ : v.toValuationSubring →+* k' //
    ∀ a : k, ψ (algebraMap k v.toValuationSubring a) = algebraMap k k' a}

def homOEquivAlgHom [Finite k'] (v : Place k F) :
    HomO k' v ≃ (v.ResidueField →ₐ[k] k') where
  toFun ψ :=
    { Ideal.Quotient.lift (maximalIdeal v.toValuationSubring) ψ.1
        (fun a ha => by rwa [← ker_eq_maximalIdeal ψ.1, RingHom.mem_ker] at ha) with
      commutes' := fun r => by
        change Ideal.Quotient.lift _ _ _
          (Ideal.Quotient.mk _ (algebraMap k v.toValuationSubring r)) = _
        rw [Ideal.Quotient.lift_mk]
        exact ψ.2 r }
  invFun χ :=
    ⟨χ.toRingHom.comp (residue v.toValuationSubring), fun a => by
      change χ (algebraMap k v.ResidueField a) = _
      exact χ.commutes a⟩
  left_inv ψ := by
    apply Subtype.ext
    ext x
    rfl
  right_inv χ := by
    apply AlgHom.ext
    intro x
    obtain ⟨y, rfl⟩ := residue_surjective x
    rfl

variable (k') in

def HomC (v : Place k F) : Type _ :=
  {φ : integralClosureAt F' v →+* k' // ∀ a : k', φ (constHom v a) = a}

def restrictHomC (v : Place k F) (φ : HomC k' (F' := F') v) : HomO k' v :=
  ⟨φ.1.comp (algebraMap v.toValuationSubring (integralClosureAt F' v)), fun a => by
    rw [RingHom.comp_apply, algebraMap_algebraMap_eq_constHom (k' := k'), φ.2]⟩

theorem eq_aeval_constHom (v : Place k F) (α : k') (c : integralClosureAt F' v)
    (p : (v.toValuationSubring)[X]) (hp : aeval (algebraMap k' F' α) p = (c : F')) :
    c = aeval (constHom v α) p := by
  apply Subtype.ext
  change (c : F') = (integralClosure (↥v.toValuationSubring) F').val (aeval (constHom v α) p)
  rw [← aeval_algHom_apply]
  exact hp.symm

theorem restrictHomC_bijective (v : Place k F) (α : k')
    (htop : Algebra.adjoin k {α} = ⊤)
    (hgen : ∀ c : integralClosureAt F' v, ∃ p : (v.toValuationSubring)[X],
      aeval (algebraMap k' F' α) p = (c : F'))
    (hdvd : ∀ p : (v.toValuationSubring)[X], aeval (algebraMap k' F' α) p = 0 →
      (minpoly k α).map (algebraMap k v.toValuationSubring) ∣ p) :
    Function.Bijective (restrictHomC (k' := k') (F' := F') v) := by
  classical
  set O := v.toValuationSubring
  set genC : integralClosureAt F' v := constHom v α with hgenC
  constructor
  ·
    rintro ⟨φ₁, h₁⟩ ⟨φ₂, h₂⟩ h
    have h' : φ₁.comp (algebraMap O (integralClosureAt F' v))
        = φ₂.comp (algebraMap O (integralClosureAt F' v)) := congrArg Subtype.val h
    apply Subtype.ext
    ext c
    obtain ⟨p, hp⟩ := hgen c
    have hc : c = aeval genC p := eq_aeval_constHom v α c p hp
    change φ₁ c = φ₂ c
    rw [hc, aeval_def, hom_eval₂, hom_eval₂, h', hgenC, h₁ α, h₂ α]
  ·
    rintro ⟨ψ, hψ⟩
    set f : O[X] →+* integralClosureAt F' v := (aeval genC).toRingHom with hf_def
    have hf : Function.Surjective f := by
      intro c
      obtain ⟨p, hp⟩ := hgen c
      exact ⟨p, (eq_aeval_constHom v α c p hp).symm⟩
    set φ₀ : O[X] →+* k' := eval₂RingHom ψ α with hφ₀_def
    have hψk : ψ.comp (algebraMap k O) = algebraMap k k' := RingHom.ext hψ
    have hker : RingHom.ker f ≤ RingHom.ker φ₀ := by
      intro p hp
      rw [RingHom.mem_ker] at hp ⊢
      have hp0 : aeval (algebraMap k' F' α) p = 0 := by
        have : ((f p : integralClosureAt F' v) : F') = 0 := by rw [hp]; rfl
        rw [hf_def] at this
        change ((integralClosure O F').val (aeval genC p)) = 0 at this
        rwa [← aeval_algHom_apply] at this
      obtain ⟨q, hq⟩ := hdvd p hp0
      rw [hq, map_mul, hφ₀_def]
      change eval₂ ψ α ((minpoly k α).map (algebraMap k O)) * _ = 0
      rw [eval₂_map, hψk]
      change aeval α (minpoly k α) * _ = 0
      rw [minpoly.aeval, zero_mul]
    let φ : integralClosureAt F' v →+* k' := f.liftOfSurjective hf ⟨φ₀, hker⟩
    have hφf : ∀ p, φ (f p) = φ₀ p := fun p => RingHom.liftOfSurjective_comp_apply f hf ⟨φ₀, hker⟩ p
    have hφO : ∀ x : O, φ (algebraMap O (integralClosureAt F' v) x) = ψ x := by
      intro x
      have hx : algebraMap O (integralClosureAt F' v) x = f (Polynomial.C x) := by
        rw [hf_def]; change _ = aeval genC (Polynomial.C x); rw [aeval_C]
      rw [hx, hφf, hφ₀_def]
      change eval₂ ψ α (Polynomial.C x) = ψ x
      rw [eval₂_C]
    refine ⟨⟨φ, fun a => ?_⟩, ?_⟩
    ·
      have ha : a ∈ Algebra.adjoin k {α} := by rw [htop]; exact Algebra.mem_top
      rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
      obtain ⟨r, rfl⟩ := ha
      change φ (constHom v (aeval α r)) = aeval α r
      rw [aeval_def, hom_eval₂, constHom_comp_algebraMap, ← hgenC, ← eval₂_map]
      change φ (aeval genC (r.map (algebraMap k O))) = _
      change φ (f (r.map (algebraMap k O))) = _
      rw [hφf, hφ₀_def]
      change eval₂ ψ α (r.map (algebraMap k O)) = _
      rw [eval₂_map, hψk]
    · apply Subtype.ext
      ext x
      exact hφO x

variable (k') in

def homCEquivHomO (v : Place k F) (α : k')
    (htop : Algebra.adjoin k {α} = ⊤)
    (hgen : ∀ c : integralClosureAt F' v, ∃ p : (v.toValuationSubring)[X],
      aeval (algebraMap k' F' α) p = (c : F'))
    (hdvd : ∀ p : (v.toValuationSubring)[X], aeval (algebraMap k' F' α) p = 0 →
      (minpoly k α).map (algebraMap k v.toValuationSubring) ∣ p) :
    HomC k' (F' := F') v ≃ HomO k' v :=
  Equiv.ofBijective _ (restrictHomC_bijective v α htop hgen hdvd)

variable [FiniteDimensional F F'] [Algebra.IsSeparable F F']

variable (k') in

def GoodPrime (v : Place k F) : Type _ :=
  {P : HeightOneSpectrum (integralClosureAt F' v) //
    ∀ c : integralClosureAt F' v, ∃ a : k', c - constHom v a ∈ P.asIdeal}

def goodPrimeOfHomC [Finite k'] (v : Place k F) (φ : HomC k' (F' := F') v) : GoodPrime k' (F' := F') v :=
  ⟨⟨RingHom.ker φ.1, RingHom.ker_isPrime _, by
      intro hbot
      obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (maximalIdeal_ne_bot v)
      have h1 : algebraMap v.toValuationSubring (integralClosureAt F' v) r ∈ RingHom.ker φ.1 := by
        rw [RingHom.mem_ker, ← RingHom.comp_apply, ← RingHom.mem_ker, ker_eq_maximalIdeal]
        exact hr
      rw [hbot, Ideal.mem_bot] at h1
      exact hr0 (algebraMap_integralClosureAt_injective v (by rw [h1, map_zero]))⟩,
    fun c => ⟨φ.1 c, by
      change c - constHom v (φ.1 c) ∈ RingHom.ker φ.1
      rw [RingHom.mem_ker, map_sub, φ.2, sub_self]⟩⟩

@[scoped simp] theorem goodPrimeOfHomC_asIdeal [Finite k'] (v : Place k F) (φ : HomC k' (F' := F') v) :
    (goodPrimeOfHomC v φ).1.asIdeal = RingHom.ker φ.1 := rfl

theorem goodPrimeOfHomC_bijective [Finite k'] (v : Place k F) :
    Function.Bijective (goodPrimeOfHomC (k' := k') (F' := F') v) := by
  constructor
  · rintro ⟨φ₁, h₁⟩ ⟨φ₂, h₂⟩ h
    have h' : RingHom.ker φ₁ = RingHom.ker φ₂ := by
      have := congrArg (fun P : GoodPrime k' (F' := F') v => P.1.asIdeal) h
      simpa using this
    apply Subtype.ext
    ext c
    change φ₁ c = φ₂ c
    have hc : c - constHom v (φ₁ c) ∈ RingHom.ker φ₂ := by
      rw [← h', RingHom.mem_ker, map_sub, h₁, sub_self]
    rw [RingHom.mem_ker, map_sub, h₂, sub_eq_zero] at hc
    exact hc.symm
  · rintro ⟨P, hP⟩
    let C := integralClosureAt F' v
    let g : k' →+* C ⧸ P.asIdeal := (Ideal.Quotient.mk P.asIdeal).comp (constHom v)
    have hg : Function.Bijective g := by
      refine ⟨g.injective, fun x => ?_⟩
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨a, ha⟩ := hP c
      exact ⟨a, (Ideal.Quotient.eq.2 ha).symm⟩
    let e : k' ≃+* C ⧸ P.asIdeal := RingEquiv.ofBijective g hg
    let φ : C →+* k' := e.symm.toRingHom.comp (Ideal.Quotient.mk P.asIdeal)
    have hφ : ∀ a : k', φ (constHom v a) = a := fun a => by
      change e.symm (g a) = a
      exact e.symm_apply_apply a
    refine ⟨⟨φ, hφ⟩, ?_⟩
    apply Subtype.ext
    apply HeightOneSpectrum.ext
    change RingHom.ker φ = P.asIdeal
    ext c
    rw [RingHom.mem_ker]
    change e.symm (Ideal.Quotient.mk P.asIdeal c) = 0 ↔ _
    rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]

variable (k') in

def homCEquivGoodPrime [Finite k'] (v : Place k F) :
    HomC k' (F' := F') v ≃ GoodPrime k' (F' := F') v :=
  Equiv.ofBijective _ (goodPrimeOfHomC_bijective v)

theorem mem_fiberCenter_iff {v : Place k F} {w : Place k F'} (hw : w.restrict F = v)
    (c : integralClosureAt F' v) :
    c ∈ (fiberCenter F' v hw).asIdeal ↔
      (⟨algebraMap (integralClosureAt F' v) F' c, forall_mem_of_restrict_eq hw c⟩ :
        w.toValuationSubring) ∈ maximalIdeal w.toValuationSubring := Iff.rfl

theorem deg_eq_one_iff_forall (w' : Place k' F') [Module.Finite k' w'.ResidueField] :
    w'.deg = 1 ↔ ∀ x : w'.ResidueField, ∃ a : k', algebraMap k' w'.ResidueField a = x := by
  unfold Place.deg
  rw [finrank_eq_one_iff_of_nonzero' (1 : w'.ResidueField) one_ne_zero]
  simp only [Algebra.algebraMap_eq_smul_one]

theorem deg_eq_one_iff_good (v : Place k F) (w' : Place k' F')
    [Module.Finite k' w'.ResidueField]
    (hw : (forgetConstants (K := k) w').restrict F = v) :
    w'.deg = 1 ↔ ∀ c : integralClosureAt F' v, ∃ a : k',
      c - constHom v a ∈ (fiberCenter F' v hw).asIdeal := by
  rw [deg_eq_one_iff_forall]
  constructor
  · intro h c
    let y : w'.toValuationSubring := ⟨(c : F'), forall_mem_of_restrict_eq hw c⟩
    obtain ⟨a, ha⟩ := h (residue _ y)
    refine ⟨a, ?_⟩
    rw [mem_fiberCenter_iff]
    have : residue w'.toValuationSubring (y - algebraMap k' w'.toValuationSubring a) = 0 := by
      rw [map_sub, ← ha, sub_eq_zero]; rfl
    rw [residue_eq_zero_iff] at this
    convert this using 1 <;> try rfl
  · intro h x
    obtain ⟨y, rfl⟩ := residue_surjective x
    have hy : (y : F') ∈ HeightOneSpectrum.valuationSubringAtPrime F' (fiberCenter F' v hw) := by
      rw [← toValuationSubring_eq_of_restrict_eq hw]; exact y.2
    obtain ⟨c, s, hs, hcs⟩ := hy
    obtain ⟨a, ha⟩ := h c
    obtain ⟨b, hb⟩ := h s
    have hs0 : s ≠ 0 := by rintro rfl; exact hs (Ideal.zero_mem _)
    have hsF : algebraMap (integralClosureAt F' v) F' s ≠ 0 := fun h0 =>
      hs0 ((map_eq_zero_iff _ (IsFractionRing.injective (integralClosureAt F' v) F')).mp h0)
    let cO : w'.toValuationSubring := ⟨algebraMap _ F' c, forall_mem_of_restrict_eq hw c⟩
    let sO : w'.toValuationSubring := ⟨algebraMap _ F' s, forall_mem_of_restrict_eq hw s⟩
    have hsO : sO ∉ maximalIdeal w'.toValuationSubring := fun hm =>
      hs ((mem_fiberCenter_iff hw s).2 hm)
    have hres_s : residue _ sO ≠ 0 := by rwa [Ne, residue_eq_zero_iff]
    have hca : residue _ cO = algebraMap k' _ a := by
      have hm : cO - algebraMap k' w'.toValuationSubring a ∈ maximalIdeal w'.toValuationSubring := by
        have := (mem_fiberCenter_iff hw _).1 ha
        convert this using 1 <;> try rfl
      rw [← residue_eq_zero_iff, map_sub, sub_eq_zero] at hm
      exact hm
    have hsb : residue _ sO = algebraMap k' _ b := by
      have hm : sO - algebraMap k' w'.toValuationSubring b ∈ maximalIdeal w'.toValuationSubring := by
        have := (mem_fiberCenter_iff hw _).1 hb
        convert this using 1 <;> try rfl
      rw [← residue_eq_zero_iff, map_sub, sub_eq_zero] at hm
      exact hm
    have hysc : y * sO = cO := by
      apply Subtype.ext
      change (y : F') * algebraMap _ F' s = algebraMap _ F' c
      rw [hcs, inv_mul_cancel_right₀ hsF]
    have hb0 : b ≠ 0 := by rintro rfl; rw [map_zero] at hsb; exact hres_s hsb
    refine ⟨a * b⁻¹, ?_⟩
    have : residue _ y * residue _ sO = residue _ cO := by rw [← map_mul, hysc]
    rw [hca, hsb] at this
    rw [map_mul, map_inv₀, ← this, mul_inv_cancel_right₀]
    rwa [← hsb]

variable (k') in

def DegOneOver (v : Place k F) : Type _ :=
  {w' : Place k' F' // restrictConstants F (K := k) w' = v ∧ w'.deg = 1}

def degOneOverEquivGoodPrime [∀ w' : Place k' F', Module.Finite k' w'.ResidueField]
    (v : Place k F) : DegOneOver k' (F' := F') v ≃ GoodPrime k' (F' := F') v := by
  let E : {w' : Place k' F' // restrictConstants F (K := k) w' = v} ≃
      HeightOneSpectrum (integralClosureAt F' v) :=
    ((constantFieldEquiv k k' (F' := F')).symm.subtypeEquiv (fun _ => Iff.rfl)).trans
      (fiberEquiv F' v)
  refine (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun w' : Place k' F' => restrictConstants F (K := k) w' = v) (fun w' => w'.deg = 1)).symm.trans
    (Equiv.subtypeEquiv E ?_)
  rintro ⟨w', hw'⟩
  exact deg_eq_one_iff_good v w' hw'

theorem card_degOneOver [Finite k'] [∀ w' : Place k' F', Module.Finite k' w'.ResidueField]
    (v : Place k F) [Module.Finite k v.ResidueField] (α : k')
    (htop : Algebra.adjoin k {α} = ⊤)
    (hgen : ∀ c : integralClosureAt F' v, ∃ p : (v.toValuationSubring)[X],
      aeval (algebraMap k' F' α) p = (c : F'))
    (hdvd : ∀ p : (v.toValuationSubring)[X], aeval (algebraMap k' F' α) p = 0 →
      (minpoly k α).map (algebraMap k v.toValuationSubring) ∣ p) :
    Nat.card (DegOneOver k' (F' := F') v) =
      if v.deg ∣ Module.finrank k k' then v.deg else 0 := by
  have e : DegOneOver k' (F' := F') v ≃ (v.ResidueField →ₐ[k] k') :=
    (degOneOverEquivGoodPrime v).trans <| (homCEquivGoodPrime k' v).symm.trans <|
      (homCEquivHomO k' v α htop hgen hdvd).trans (homOEquivAlgHom v)
  rw [Nat.card_congr e]
  split_ifs with h
  · exact FiniteField.natCard_algHom_of_finrank_dvd h
  · haveI : IsEmpty (v.ResidueField →ₐ[k] k') :=
      ⟨fun χ => h (FiniteField.nonempty_algHom_iff_finrank_dvd.mp ⟨χ⟩)⟩
    exact Nat.card_of_isEmpty

end Local

section ConstExt

variable {k k' F F' : Type*} [Field k] [Finite k] [Field k'] [Finite k'] [Field F] [Field F']
  [Algebra k k'] [Algebra k' F'] [Algebra k F'] [IsScalarTower k k' F']
  [Algebra k F] [Algebra F F'] [IsScalarTower k F F']

theorem finiteDimensional_of_adjoin_range_eq_top [Algebra.IsIntegral F F']
    (hgen : Algebra.adjoin F (Set.range (algebraMap k' F')) = ⊤) :
    FiniteDimensional F F' := by
  haveI : Algebra.FiniteType F F' :=
    ⟨⟨(Set.finite_range (algebraMap k' F')).toFinset, by
      rw [Set.Finite.coe_toFinset]; exact hgen⟩⟩
  exact Algebra.IsIntegral.finite

theorem adjoin_eq_top_of_primitive (α : k') (hα : IntermediateField.adjoin k {α} = ⊤) :
    Algebra.adjoin k {α} = ⊤ := by
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (Algebra.IsAlgebraic.isAlgebraic α), hα, IntermediateField.top_toSubalgebra]

theorem adjoin_algebraMap_eq_top (α : k') (htop : Algebra.adjoin k {α} = ⊤)
    (hgen : Algebra.adjoin F (Set.range (algebraMap k' F')) = ⊤) :
    Algebra.adjoin F {algebraMap k' F' α} = ⊤ := by
  rw [eq_top_iff, ← hgen]
  apply Algebra.adjoin_le
  rintro _ ⟨a, rfl⟩
  have ha : a ∈ Algebra.adjoin k {α} := htop ▸ Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at ha
  obtain ⟨r, rfl⟩ := ha
  change algebraMap k' F' (aeval α r) ∈ Algebra.adjoin F {algebraMap k' F' α}
  rw [← aeval_algebraMap_apply, ← aeval_map_algebraMap F]
  exact aeval_mem_adjoin_singleton F _

include k in

theorem isSeparable_algebraMap (α : k') : IsSeparable F (algebraMap k' F' α) := by
  have hsepk : IsSeparable k (algebraMap k' F' α) := by
    unfold IsSeparable
    rw [minpoly.algebraMap_eq (algebraMap k' F').injective]
    exact Algebra.IsSeparable.isSeparable k α
  exact IsSeparable.tower_top F hsepk

include k in

theorem isSeparable_of_adjoin_range_eq_top [Algebra.IsIntegral F F']
    (hgen : Algebra.adjoin F (Set.range (algebraMap k' F')) = ⊤) :
    Algebra.IsSeparable F F' := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element k k'
  have htop := adjoin_eq_top_of_primitive α hα
  have hFtop : IntermediateField.adjoin F {algebraMap k' F' α} = ⊤ :=
    IntermediateField.adjoin_eq_top_of_algebra F _ (adjoin_algebraMap_eq_top α htop hgen)
  haveI : Algebra.IsSeparable F (IntermediateField.adjoin F {algebraMap k' F' α}) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F F').2
      (isSeparable_algebraMap (k := k) α)
  exact Algebra.IsSeparable.of_algHom F (IntermediateField.adjoin F {algebraMap k' F' α})
    ((IntermediateField.equivOfEq hFtop).trans IntermediateField.topEquiv).symm.toAlgHom

theorem minpoly_algebraMap_eq_map [Algebra.IsIntegral F F']
    (hconst : ∀ y : F, IsAlgebraic k y → y ∈ (algebraMap k F).range) (α : k') :
    minpoly F (algebraMap k' F' α) = (minpoly k α).map (algebraMap k F) := by
  have hintk : IsIntegral k α := Algebra.IsIntegral.isIntegral α
  have hintF : IsIntegral F (algebraMap k' F' α) := Algebra.IsIntegral.isIntegral _
  have hμmon : (minpoly k α).Monic := minpoly.monic hintk
  have hgmon : (minpoly F (algebraMap k' F' α)).Monic := minpoly.monic hintF

  have hg_dvd : minpoly F (algebraMap k' F' α) ∣ (minpoly k α).map (algebraMap k F) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, aeval_algebraMap_apply, minpoly.aeval, map_zero]

  have h1 : ((minpoly k α).map (algebraMap k k')).Splits := Normal.splits inferInstance α
  have hne : ((minpoly k α).map (algebraMap k k')).map (algebraMap k' F') ≠ 0 :=
    ((hμmon.map _).map _).ne_zero
  have hdvd' : (minpoly F (algebraMap k' F' α)).map (algebraMap F F') ∣
      ((minpoly k α).map (algebraMap k k')).map (algebraMap k' F') := by
    rw [map_map, ← IsScalarTower.algebraMap_eq k k' F', IsScalarTower.algebraMap_eq k F F',
      ← map_map]
    exact Polynomial.map_dvd _ hg_dvd
  have hgsplit : ((minpoly F (algebraMap k' F' α)).map (algebraMap F F')).Splits :=
    (h1.map (algebraMap k' F')).of_dvd hne hdvd'

  have hroots : ∀ a ∈ ((minpoly F (algebraMap k' F' α)).map (algebraMap F F')).roots,
      a ∈ (algebraMap k' F').range := by
    intro a ha
    rw [mem_roots (hgmon.map _).ne_zero] at ha
    have ha' : a ∈ (((minpoly k α).map (algebraMap k k')).map (algebraMap k' F')).roots := by
      rw [mem_roots hne]
      exact eval_eq_zero_of_dvd_of_eval_eq_zero hdvd' ha
    rw [h1.roots_map (algebraMap k' F'), Multiset.mem_map] at ha'
    obtain ⟨b, -, rfl⟩ := ha'
    exact ⟨b, rfl⟩

  have hlift : (minpoly F (algebraMap k' F' α)).map (algebraMap F F') ∈ lifts (algebraMap k' F') :=
    hgsplit.mem_lift_of_roots_mem_range (hgmon.map _) (algebraMap k' F') hroots
  obtain ⟨h, hh⟩ := (mem_lifts _).1 hlift
  have hglifts : minpoly F (algebraMap k' F' α) ∈ lifts (algebraMap k F) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    apply hconst
    apply IsIntegral.isAlgebraic
    have h2 : IsIntegral k (algebraMap k' F' (h.coeff n)) :=
      ((Algebra.IsIntegral.isIntegral (R := k) (h.coeff n)).map (IsScalarTower.toAlgHom k k' F'))
    have h3 : algebraMap k' F' (h.coeff n) = algebraMap F F' ((minpoly F (algebraMap k' F' α)).coeff n) := by
      rw [← coeff_map, hh, coeff_map]
    rw [h3] at h2
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom k F F') (algebraMap F F').injective).mp h2
  obtain ⟨g₀, hg₀, -, hg₀mon⟩ := lifts_and_degree_eq_and_monic hglifts hgmon

  have hg₀α : aeval α g₀ = 0 := by
    apply (algebraMap k' F').injective
    rw [map_zero, ← aeval_algebraMap_apply, ← aeval_map_algebraMap F, hg₀, minpoly.aeval]
  have hμg : (minpoly k α).map (algebraMap k F) ∣ minpoly F (algebraMap k' F' α) := by
    rw [← hg₀]
    exact Polynomial.map_dvd _ (minpoly.dvd k α hg₀α)
  have hdeg : ((minpoly k α).map (algebraMap k F)).natDegree ≤
      (minpoly F (algebraMap k' F' α)).natDegree :=
    natDegree_le_of_dvd hμg hgmon.ne_zero
  exact (eq_of_monic_of_dvd_of_natDegree_le hgmon (hμmon.map _) hg_dvd hdeg).symm

theorem map_minpoly_dvd [Algebra.IsIntegral F F']
    (hconst : ∀ y : F, IsAlgebraic k y → y ∈ (algebraMap k F).range) (v : Place k F) (α : k')
    (p : (v.toValuationSubring)[X]) (hp : aeval (algebraMap k' F' α) p = 0) :
    (minpoly k α).map (algebraMap k v.toValuationSubring) ∣ p := by
  have hintk : IsIntegral k α := Algebra.IsIntegral.isIntegral α
  have hmon : ((minpoly k α).map (algebraMap k v.toValuationSubring)).Monic :=
    (minpoly.monic hintk).map _
  rw [← Polynomial.map_dvd_map (algebraMap v.toValuationSubring F)
    (IsFractionRing.injective v.toValuationSubring F) hmon, Polynomial.map_map,
    ← IsScalarTower.algebraMap_eq k v.toValuationSubring F,
    ← minpoly_algebraMap_eq_map (F' := F') hconst α]
  apply minpoly.dvd F
  rwa [aeval_map_algebraMap]

theorem exists_aeval_eq [Algebra.IsIntegral F F'] [FiniteDimensional F F']
    [Algebra.IsSeparable F F']
    (hconst : ∀ y : F, IsAlgebraic k y → y ∈ (algebraMap k F).range) (v : Place k F) (α : k')
    (hFtop : IntermediateField.adjoin F {algebraMap k' F' α} = ⊤)
    (c : integralClosureAt F' v) :
    ∃ p : (v.toValuationSubring)[X], aeval (algebraMap k' F' α) p = (c : F') := by
  set O := v.toValuationSubring
  have hintk : IsIntegral k α := Algebra.IsIntegral.isIntegral α
  have hintF : IsIntegral F (algebraMap k' F' α) := Algebra.IsIntegral.isIntegral _
  have hintO : IsIntegral O (algebraMap k' F' α) :=
    (mem_integralClosure_iff _ _).mp (constHom (F' := F') v α).2
  have hz : IsIntegral O (c : F') := (mem_integralClosure_iff _ _).mp c.2
  let pb : PowerBasis F F' := (IntermediateField.adjoin.powerBasis hintF).map
    ((IntermediateField.equivOfEq hFtop).trans IntermediateField.topEquiv)
  have hpb : pb.gen = algebraMap k' F' α := by
    rw [PowerBasis.map_gen, IntermediateField.adjoin.powerBasis_gen]
    rfl
  have hmem := Algebra.discr_mul_isIntegral_mem_adjoin F (B := pb) (hpb ▸ hintO) hz
  rw [hpb] at hmem

  set d : k' := aeval α (derivative (minpoly k α)) with hd
  have hd0 : d ≠ 0 :=
    (Algebra.IsSeparable.isSeparable k α).aeval_derivative_ne_zero (minpoly.aeval k α)
  have hderiv : aeval (algebraMap k' F' α) (derivative (minpoly F (algebraMap k' F' α)))
      = algebraMap k' F' d := by
    rw [minpoly_algebraMap_eq_map hconst, derivative_map, aeval_map_algebraMap,
      aeval_algebraMap_apply]
  have hNint : IsIntegral O (Algebra.norm F (algebraMap k' F' d)) :=
    Algebra.isIntegral_norm F ((mem_integralClosure_iff _ _).mp (constHom (F' := F') v d).2)
  have hNint' : IsIntegral O (Algebra.norm F (algebraMap k' F' d⁻¹)) :=
    Algebra.isIntegral_norm F ((mem_integralClosure_iff _ _).mp (constHom (F' := F') v d⁻¹).2)
  obtain ⟨u₁, hu₁⟩ := IsIntegrallyClosed.isIntegral_iff.mp hNint
  obtain ⟨u₂, hu₂⟩ := IsIntegrallyClosed.isIntegral_iff.mp hNint'
  have hu : u₁ * u₂ = 1 := by
    apply IsFractionRing.injective O F
    rw [map_mul, hu₁, hu₂, map_one, ← map_mul, ← map_mul, mul_inv_cancel₀ hd0, map_one, map_one]
  set e : ℕ := Module.finrank F F' * (Module.finrank F F' - 1) / 2
  have hdisc : Algebra.discr F pb.basis = algebraMap O F ((-1) ^ e * u₁) := by
    rw [Algebra.discr_powerBasis_eq_norm, hpb, hderiv, map_mul, map_pow, map_neg, map_one, hu₁]
  have ht : IsUnit ((-1 : O) ^ e * u₁) :=
    ((isUnit_one.neg).pow e).mul (IsUnit.of_mul_eq_one u₂ hu)
  obtain ⟨t, ht⟩ := ht
  rw [hdisc, algebraMap_smul, ← ht] at hmem
  have hc : (c : F') = ((↑t⁻¹ : O) : O) • ((↑t : O) • (c : F')) := by
    rw [smul_smul, Units.inv_mul, one_smul]
  have hmem' : (c : F') ∈ Algebra.adjoin O {algebraMap k' F' α} := by
    rw [hc]
    exact Subalgebra.smul_mem _ hmem _
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hmem'
  exact hmem'

end ConstExt

section Finiteness

variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]

theorem ord_ne_zero_of_not_mem (v : Place k F) {x : F} (hx : x ∉ v.toValuationSubring) :
    v.ord x ≠ 0 := by
  have hx0 : x ≠ 0 := by rintro rfl; exact hx (zero_mem _)
  have hinv : x⁻¹ ∈ v.toValuationSubring :=
    (v.toValuationSubring.mem_or_inv_mem x).resolve_left hx
  have hmax : (⟨x⁻¹, hinv⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    apply hx
    have h1 : ((u : v.toValuationSubring) : F) * ((u⁻¹ : (v.toValuationSubring)ˣ) :
        v.toValuationSubring) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv]; rfl
    rw [hu] at h1
    change x⁻¹ * _ = 1 at h1
    rw [mul_eq_one_iff_inv_eq₀ (inv_ne_zero hx0), inv_inv] at h1
    rw [h1]
    exact SetLike.coe_mem _
  have hpos : 0 < v.ord x⁻¹ := (mem_maximalIdeal_iff_ord_pos v (inv_ne_zero hx0) hinv).1 hmax
  rw [ord_inv] at hpos
  omega

theorem finite_setOf_deg_eq [IsCurveOver k F] {d : ℕ} (hd : 0 < d) :
    {v : Place k F | v.deg = d}.Finite := by
  classical
  by_cases hne : {v : Place k F | v.deg = d}.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    exact Set.finite_empty
  obtain ⟨v₀, hv₀⟩ := hne
  obtain ⟨x, -, hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.2 v₀.ne_top')
  have hx0 : x ≠ 0 := by rintro rfl; exact hx (zero_mem _)
  set q : ℕ := Nat.card k with hq
  have hqd : 1 < q ^ d := Nat.one_lt_pow hd.ne' Finite.one_lt_card
  set z : F := x ^ (q ^ d) - x with hz
  have hz0 : z ≠ 0 := by
    intro hz0
    apply hx
    have hint : IsIntegral k x := by
      refine ⟨X ^ (q ^ d) - X, monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hqd), ?_⟩
      rw [eval₂_sub, eval₂_X_pow, eval₂_X]
      exact hz0
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp
      (hint.tower_top (A := v₀.toValuationSubring))
    rw [← hy]
    exact SetLike.coe_mem y
  obtain ⟨D₁, hD₁, -⟩ := HasPrincipalDivisors.exists_divisor (K := k) x⁻¹ (inv_ne_zero hx0)
  obtain ⟨D₂, hD₂, -⟩ := HasPrincipalDivisors.exists_divisor (K := k) z hz0
  apply (D₁.support ∪ D₂.support).finite_toSet.subset
  intro v hv
  change v.deg = d at hv
  simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finsupp.mem_support_iff]
  by_cases hxv : x ∈ v.toValuationSubring
  · right
    rw [hD₂]
    haveI : Module.Finite k v.ResidueField := IsCurveOver.finite_residueField v
    haveI : Finite v.ResidueField := Module.finite_of_finite k
    letI : Fintype v.ResidueField := Fintype.ofFinite _
    have hcard : Fintype.card v.ResidueField = q ^ d := by
      rw [Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := k)]
      change Nat.card k ^ v.deg = q ^ d
      rw [hv]
    have hy : residue v.toValuationSubring
        ((⟨x, hxv⟩ : v.toValuationSubring) ^ (q ^ d) - ⟨x, hxv⟩) = 0 := by
      rw [map_sub, map_pow, ← hcard, FiniteField.pow_card, sub_self]
    rw [residue_eq_zero_iff] at hy
    have hzmem : z ∈ v.toValuationSubring := sub_mem (pow_mem hxv _) hxv
    have hyz : ((⟨x, hxv⟩ : v.toValuationSubring) ^ (q ^ d) - ⟨x, hxv⟩) = ⟨z, hzmem⟩ :=
      Subtype.ext (by
        simp only [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, hz])
    rw [hyz, mem_maximalIdeal_iff_ord_pos v hz0 hzmem] at hy
    exact hy.ne'
  · left
    rw [hD₁, ord_inv, neg_ne_zero]
    exact ord_ne_zero_of_not_mem v hxv

end Finiteness

section Global

theorem card_places_deg_one
    {k k' F F' : Type*} [Field k] [Finite k] [Field k'] [Finite k'] [Field F] [Field F']
    [Algebra k k'] [Algebra k' F'] [Algebra k F'] [IsScalarTower k k' F']
    [Algebra k F] [Algebra F F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']
    [AlgebraicCurve.IsCurveOver k F]
    [AlgebraicCurve.IsCurveOver k' F']
    (hgen : Algebra.adjoin F (Set.range (algebraMap k' F')) = ⊤)
    (hconst : ∀ y : F, IsAlgebraic k y → y ∈ (algebraMap k F).range) :
    Nat.card {w : AlgebraicCurve.Place k' F' | w.deg = 1} =
      ∑ d ∈ Nat.divisors (Module.finrank k k'),
        d * Nat.card {v : AlgebraicCurve.Place k F | v.deg = d} := by
  classical
  haveI : FiniteDimensional F F' := finiteDimensional_of_adjoin_range_eq_top hgen
  haveI : Algebra.IsSeparable F F' := isSeparable_of_adjoin_range_eq_top (k := k) hgen
  haveI : ∀ w' : Place k' F', Module.Finite k' w'.ResidueField := IsCurveOver.finiteResidue
  obtain ⟨α, hα⟩ := Field.exists_primitive_element k k'
  have htop : Algebra.adjoin k {α} = ⊤ := adjoin_eq_top_of_primitive α hα
  have hFtop : IntermediateField.adjoin F {algebraMap k' F' α} = ⊤ :=
    IntermediateField.adjoin_eq_top_of_algebra F _ (adjoin_algebraMap_eq_top α htop hgen)
  set n : ℕ := Module.finrank k k' with hn
  have hn0 : n ≠ 0 := Module.finrank_pos.ne'

  have hloc : ∀ v : Place k F,
      Nat.card (DegOneOver k' (F' := F') v) = if v.deg ∣ n then v.deg else 0 := by
    intro v
    haveI : Module.Finite k v.ResidueField := IsCurveOver.finite_residueField v
    exact card_degOneOver v α htop (exists_aeval_eq hconst v α hFtop)
      (map_minpoly_dvd hconst v α)
  have hfib : ∀ v : Place k F, Finite (DegOneOver k' (F' := F') v) := fun v =>
    ((restrictConstants_fiber_finite k' (K := k) (F := F) v).subset
      (fun w (h : restrictConstants F (K := k) w = v ∧ w.deg = 1) => h.1)).to_subtype

  have hdiv : ∀ w' : Place k' F', w'.deg = 1 → (restrictConstants F (K := k) w').deg ∣ n := by
    intro w' hw'
    by_contra h
    have h1 := hloc (restrictConstants F (K := k) w')
    rw [if_neg h] at h1
    haveI := hfib (restrictConstants F (K := k) w')
    haveI : Nonempty (DegOneOver k' (F' := F') (restrictConstants F (K := k) w')) :=
      ⟨⟨w', rfl, hw'⟩⟩
    exact Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩ h1

  have hTfin : {v : Place k F | v.deg ∣ n}.Finite := by
    have hU : {v : Place k F | v.deg ∣ n} ⊆ ⋃ d ∈ (n.divisors : Set ℕ),
        {v : Place k F | v.deg = d} := by
      intro v hv
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_coe, Nat.mem_divisors]
      exact ⟨v.deg, ⟨hv, hn0⟩, rfl⟩
    exact (Set.Finite.biUnion n.divisors.finite_toSet fun d hd =>
      finite_setOf_deg_eq (Nat.pos_of_mem_divisors hd)).subset hU
  set T : Finset (Place k F) := hTfin.toFinset with hT
  have hmemT : ∀ v, v ∈ T ↔ v.deg ∣ n := fun v => by
    rw [hT, Set.Finite.mem_toFinset]
    rfl

  set S : Set (Place k' F') := {w : Place k' F' | w.deg = 1} with hS
  let f : S → Place k F := fun w => restrictConstants F (K := k) w.1
  have hf : ∀ w : S, f w ∈ T := fun w => (hmemT _).2 (hdiv w.1 w.2)
  have e1 : (Σ v : {v // v ∈ T}, {w : S // f w = v}) ≃ S :=
    Equiv.sigmaSubtypeFiberEquiv f (· ∈ T) hf
  have e2 : ∀ v : Place k F, {w : S // f w = v} ≃ DegOneOver k' (F' := F') v := fun v =>
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun w : Place k' F' => w.deg = 1)
      (fun w => restrictConstants F (K := k) w = v)).trans
      (Equiv.subtypeEquivRight fun w => and_comm)
  haveI : ∀ v : {v // v ∈ T}, Finite {w : S // f w = v} := fun v =>
    haveI := hfib v.1
    Finite.of_equiv _ (e2 v.1).symm
  calc Nat.card S
      = Nat.card (Σ v : {v // v ∈ T}, {w : S // f w = v}) := Nat.card_congr e1.symm
    _ = ∑ v : {v // v ∈ T}, Nat.card {w : S // f w = v} := Nat.card_sigma
    _ = ∑ v ∈ T, Nat.card (DegOneOver k' (F' := F') v) := by
        rw [← Finset.sum_coe_sort T]
        exact Finset.sum_congr rfl fun v _ => Nat.card_congr (e2 v)
    _ = ∑ v ∈ T, v.deg :=
        Finset.sum_congr rfl fun v hv => by rw [hloc, if_pos ((hmemT v).1 hv)]
    _ = ∑ d ∈ n.divisors, ∑ v ∈ T with v.deg = d, v.deg :=
        (Finset.sum_fiberwise_of_maps_to
          (fun v hv => Nat.mem_divisors.2 ⟨(hmemT v).1 hv, hn0⟩) _).symm
    _ = ∑ d ∈ n.divisors, ∑ v ∈ T with v.deg = d, d := by
        refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun v hv => ?_
        exact (Finset.mem_filter.1 hv).2
    _ = ∑ d ∈ n.divisors, d * Nat.card {v : Place k F | v.deg = d} := by
        refine Finset.sum_congr rfl fun d hd => ?_
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
        congr 1
        have hset : {v : Place k F | v.deg = d} = ↑(T.filter fun v => v.deg = d) := by
          ext v
          simp only [Set.mem_setOf_eq, Finset.coe_filter, hmemT]
          exact ⟨fun h => ⟨h ▸ (Nat.mem_divisors.1 hd).1, h⟩, fun h => h.2⟩
        rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]

end Global

end AlgebraicCurve.Place.ConstFieldExtCount
p2m_reactivate "P2MW.S_AlgebraicCurve_card_places_deg_one_eq_sum_divisors_of_constantFieldExtension.AlgebraicCurve P2MW.S_AlgebraicCurve_card_places_deg_one_eq_sum_divisors_of_constantFieldExtension.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_card_places_deg_one_eq_sum_divisors_of_constantFieldExtension.AlgebraicCurve.Place.ConstFieldExtCount"
p2m_reactivate "P2MW.S_AlgebraicCurve_card_places_deg_one_eq_sum_divisors_of_constantFieldExtension.AlgebraicCurve P2MW.S_AlgebraicCurve_card_places_deg_one_eq_sum_divisors_of_constantFieldExtension.AlgebraicCurve.Place"
p2m_reactivate "P2MW.S_AlgebraicCurve_card_places_deg_one_eq_sum_divisors_of_constantFieldExtension.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_card_places_deg_one_eq_sum_divisors_of_constantFieldExtension.AlgebraicCurve P2MW.S_AlgebraicCurve_card_places_deg_one_eq_sum_divisors_of_constantFieldExtension.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_card_places_deg_one_eq_sum_divisors_of_constantFieldExtension.AlgebraicCurve.Place.ConstFieldExtCount"

theorem solution
    {k k' F F' : Type*} [Field k] [Finite k] [Field k'] [Finite k'] [Field F] [Field F']
    [Algebra k k'] [Algebra k' F'] [Algebra k F'] [IsScalarTower k k' F']
    [Algebra k F] [Algebra F F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']
    [AlgebraicCurve.IsCurveOver k F] [Algebra.EssFiniteType k F]
    [AlgebraicCurve.IsCurveOver k' F']
    (hgen : Algebra.adjoin F (Set.range (algebraMap k' F')) = ⊤)
    (hconst : ∀ y : F, IsAlgebraic k y → y ∈ (algebraMap k F).range) :
    Nat.card {w : AlgebraicCurve.Place k' F' | w.deg = 1} =
      ∑ d ∈ Nat.divisors (Module.finrank k k'),
        d * Nat.card {v : AlgebraicCurve.Place k F | v.deg = d} :=
  AlgebraicCurve.Place.ConstFieldExtCount.card_places_deg_one hgen hconst

end S_AlgebraicCurve_card_places_deg_one_eq_sum_divisors_of_constantFieldExtension
end P2MW
export P2MW.S_AlgebraicCurve_card_places_deg_one_eq_sum_divisors_of_constantFieldExtension (solution)
