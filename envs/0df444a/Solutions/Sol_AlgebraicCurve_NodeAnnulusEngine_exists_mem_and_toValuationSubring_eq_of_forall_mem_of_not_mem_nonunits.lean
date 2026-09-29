-- Prove2me | solution 1 for AlgebraicCurve.NodeAnnulusEngine.exists_mem_and_toValuationSubring_eq_of_forall_mem_of_not_mem_nonunits
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/d7237356-3265-5e05-9662-6e4fd4d03e67

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_Place_exists_of_valuationSubring
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_NodeAnnulusEngine_exists_mem_and_toValuationSubring_eq_of_forall_mem_of_not_mem_nonunits

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing
open scoped IntermediateField Polynomial

namespace TubeMaxAutoS

section ValSub

theorem mem_nonunits_iff_inv_not_mem {K : Type*} [Field K] (O : ValuationSubring K) {s : K} (hs0 : s ≠ 0) :
    s ∈ O.nonunits ↔ s⁻¹ ∉ O := by
  have h := O.inv_mem_nonunits_iff (x := s⁻¹)
  rw [inv_inv] at h
  rw [h]
  constructor
  · rintro (h0 | h0)
    · exact absurd (inv_eq_zero.mp h0) hs0
    · exact h0
  · exact fun h0 => Or.inr h0

theorem inv_mem_of_not_mem_nonunits {K : Type*} [Field K] (O : ValuationSubring K) {s : K} (hs0 : s ≠ 0) (hs : s ∉ O.nonunits) :
    s⁻¹ ∈ O := by
  by_contra h
  exact hs ((mem_nonunits_iff_inv_not_mem O hs0).mpr h)

theorem zero_mem_nonunits {K : Type*} [Field K] (O : ValuationSubring K) : (0 : K) ∈ O.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff, map_zero]; exact zero_lt_one

theorem mem_of_isIntegral {K : Type*} [Field K] (V : ValuationSubring K) {x : K} (h : IsIntegral V x) : x ∈ V := by
  obtain ⟨y, hy⟩ := (IsIntegrallyClosedIn.isIntegral_iff (R := V) (A := K)).mp h
  rw [← hy]; exact y.2

end ValSub

section Constants

theorem irreducible_of_residue {L : Type*} [Field L] (A : ValuationSubring L) (C : Subring L) (hC : ∀ c : L, c ∈ C → c ∈ A)
    [IsDomain ↥C] [IsDiscreteValuationRing ↥C] (ϖ : ↥C)
    (hϖ : ∀ d : ↥C, IsLocalRing.residue A ⟨(d : L), hC d d.2⟩ = 0 ↔ ∃ d' : ↥C, d = ϖ * d')
    (hϖ0 : ϖ ≠ 0) : Irreducible ϖ := by

  have hres1 : IsLocalRing.residue A ⟨((1 : ↥C) : L), hC _ (1 : ↥C).2⟩ ≠ 0 := by
    have : (⟨((1 : ↥C) : L), hC _ (1 : ↥C).2⟩ : A) = 1 := rfl
    rw [this, map_one]; exact one_ne_zero
  have hϖu : ¬ IsUnit ϖ := by
    intro hu
    apply hres1
    rw [hϖ]
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    exact ⟨w, hw.symm⟩

  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible ↥C
  obtain ⟨k, w, hkw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hϖ0 hp
  have hresϖ : IsLocalRing.residue A ⟨((ϖ : ↥C) : L), hC _ ϖ.2⟩ = 0 := (hϖ ϖ).mpr ⟨1, (mul_one _).symm⟩
  have hresp : IsLocalRing.residue A ⟨((p : ↥C) : L), hC _ p.2⟩ = 0 := by
    by_contra hne
    have hpu : IsUnit (⟨((p : ↥C) : L), hC _ p.2⟩ : A) := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hne
    have hwu : IsUnit (⟨(((w : ↥C) : ↥C) : L), hC _ (w : ↥C).2⟩ : A) := by
      obtain ⟨wi, hwi⟩ := (Units.isUnit w).exists_right_inv
      refine IsUnit.of_mul_eq_one (⟨((wi : ↥C) : L), hC _ wi.2⟩ : A) ?_
      apply Subtype.ext
      change ((w : ↥C) : L) * (wi : L) = 1
      rw [← Subring.coe_mul, hwi]; rfl
    have hϖA : (⟨((ϖ : ↥C) : L), hC _ ϖ.2⟩ : A) =
        ⟨(((w : ↥C) : ↥C) : L), hC _ (w : ↥C).2⟩ * ⟨((p : ↥C) : L), hC _ p.2⟩ ^ k := by
      apply Subtype.ext
      change ((ϖ : ↥C) : L) = ((w : ↥C) : L) * ((p : ↥C) : L) ^ k
      rw [hkw, Subring.coe_mul, Subring.coe_pow]
    have : IsUnit (⟨((ϖ : ↥C) : L), hC _ ϖ.2⟩ : A) := by rw [hϖA]; exact hwu.mul (hpu.pow k)
    exact ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr this) hresϖ
  obtain ⟨d', hd'⟩ := (hϖ p).mp hresp

  rcases hp.isUnit_or_isUnit hd' with hu | hu
  · exact absurd hu hϖu
  · have hassoc : Associated p ϖ := ⟨(hu.unit)⁻¹, by
      rw [hd', mul_assoc, IsUnit.mul_val_inv, mul_one]⟩
    exact hassoc.irreducible hp

theorem exists_eq_pow_mul_unit {L : Type*} [Field L] (A : ValuationSubring L) (C : Subring L) (hC : ∀ c : L, c ∈ C → c ∈ A)
    [IsDomain ↥C] [IsDiscreteValuationRing ↥C] (ϖ : ↥C)
    (hϖ : ∀ d : ↥C, IsLocalRing.residue A ⟨(d : L), hC d d.2⟩ = 0 ↔ ∃ d' : ↥C, d = ϖ * d')
    (hϖ0 : ϖ ≠ 0) (d : ↥C) (hd : d ≠ 0) : ∃ (k : ℕ) (w : (↥C)ˣ), d = (w : ↥C) * ϖ ^ k := by
  obtain ⟨k, w, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd (irreducible_of_residue A C hC ϖ hϖ hϖ0)
  exact ⟨k, w, h⟩

end Constants

section Eval

theorem isRational_of_isCurveOver {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F] [IsAlgClosed L] [IsCurveOver L F] (P : Place L F) : P.IsRational := by
  haveI : Module.Finite L P.ResidueField := IsCurveOver.finiteResidue P
  haveI : Algebra.IsIntegral L P.ResidueField := Algebra.IsIntegral.of_finite L P.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := L) (K := P.ResidueField)).2

def resEquiv {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F] (P : Place L F) (hP : P.IsRational) : L ≃+* P.ResidueField :=
  RingEquiv.ofBijective (algebraMap L P.ResidueField) ⟨(algebraMap L P.ResidueField).injective, hP⟩

@[scoped simp] theorem resEquiv_apply {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F] (P : Place L F) (hP : P.IsRational) (c : L) :
    resEquiv P hP c = algebraMap L P.ResidueField c := rfl

def evalHom {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F] (P : Place L F) (hP : P.IsRational) : P.toValuationSubring →+* L :=
  (resEquiv P hP).symm.toRingHom.comp (IsLocalRing.residue P.toValuationSubring)

theorem evalHom_apply {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F] (P : Place L F) (hP : P.IsRational) (g : P.toValuationSubring) :
    evalHom P hP g = P.evalAt (g : F) := by
  apply (resEquiv P hP).injective
  change (resEquiv P hP) ((resEquiv P hP).symm (IsLocalRing.residue P.toValuationSubring g)) = _
  rw [RingEquiv.apply_symm_apply, resEquiv_apply, P.algebraMap_evalAt hP g.2]

theorem evalHom_algebraMap {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F] (P : Place L F) (hP : P.IsRational) (c : L) :
    evalHom P hP (algebraMap L P.toValuationSubring c) = c := by
  apply (resEquiv P hP).injective
  change (resEquiv P hP) ((resEquiv P hP).symm
    (IsLocalRing.residue P.toValuationSubring (algebraMap L P.toValuationSubring c))) = _
  rw [RingEquiv.apply_symm_apply, resEquiv_apply, IsScalarTower.algebraMap_apply L P.toValuationSubring P.ResidueField]
  rfl

def toValSub {F : Type*} [Field F] (N : Subring F) (O : ValuationSubring F) (h : ∀ g : F, g ∈ N → g ∈ O) : N →+* O :=
  (N.subtype).codRestrict O (fun g => h g g.2)

end Eval

end TubeMaxAutoS
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_exists_mem_and_toValuationSubring_eq_of_forall_mem_of_not_mem_nonunits.TubeMaxAutoS"

open TubeMaxAutoS in
set_option maxHeartbeats 8000000 in
theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (S : Set (Place L F))
    (𝒩₀ : Subring F) [IsLocalRing ↥𝒩₀]
    (hS : ∀ P : Place L F, P ∈ S ↔
      (∀ f : F, f ∈ 𝒩₀ → f ∈ P.toValuationSubring) ∧
      (∀ f : ↥𝒩₀, ¬ IsUnit f → ∃ h : P.evalAt (f : F) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A))
    (C : Subring L) (hC : ∀ c : L, c ∈ C → c ∈ A)
    (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀)
    (ϖ : ↥C)
    (hϖ : ∀ d : ↥C, IsLocalRing.residue A ⟨(d : L), hC d d.2⟩ = 0 ↔ ∃ d' : ↥C, d = ϖ * d')
    [IsDomain ↥C] [IsDiscreteValuationRing ↥C]
    (halg : ∀ a : L, a ∈ A → IsAlgebraic ↥C a)
    (huniq : ∀ V : ValuationSubring L, (∀ c : L, c ∈ C → c ∈ V) → ((ϖ : ↥C) : L) ∈ V.nonunits → V = A)
    (hϖ𝒩 : ¬ IsUnit (⟨algebraMap L F ((ϖ : ↥C) : L), hCmem ϖ ϖ.2⟩ : ↥𝒩₀))
    (O : ValuationSubring F) (hO : ∀ f : F, f ∈ 𝒩₀ → f ∈ O)
    (hϖO : algebraMap L F ((ϖ : ↥C) : L) ∉ O.nonunits) (hOtop : O ≠ ⊤) :
    ∃ P ∈ S, P.toValuationSubring = O := by

  have hϖF0 : algebraMap L F ((ϖ : ↥C) : L) ≠ 0 := by
    intro h; rw [h] at hϖO; exact hϖO (zero_mem_nonunits O)
  have hϖL0 : ((ϖ : ↥C) : L) ≠ 0 := fun h => hϖF0 (by rw [h, map_zero])
  have hϖ0 : ϖ ≠ 0 := fun h => hϖL0 (by rw [h]; rfl)

  set V : ValuationSubring L := O.comap (algebraMap L F) with hV
  have hCV : ∀ c : L, c ∈ C → c ∈ V := fun c hc => by
    rw [hV, ValuationSubring.mem_comap]; exact hO _ (hCmem c hc)
  have hϖV : (((ϖ : ↥C) : L))⁻¹ ∈ V := by
    rw [hV, ValuationSubring.mem_comap, map_inv₀]
    exact inv_mem_of_not_mem_nonunits O hϖF0 hϖO
  have halgL : ∀ z : L, IsAlgebraic ↥C z := fun z => by
    rcases A.mem_or_inv_mem z with h | h
    · exact halg z h
    · exact IsAlgebraic.inv_iff.mp (halg _ h)
  have hLV : ∀ z : L, z ∈ V := by
    intro z
    obtain ⟨d, hd0, hdz⟩ := (halgL z).exists_integral_multiple

    have hdzV : (d : L) * z ∈ V := by
      apply mem_of_isIntegral V
      obtain ⟨p, hp, hpz⟩ := hdz
      set jCV : ↥C →+* ↥V := (C.subtype).codRestrict V (fun c => hCV c c.2) with hjCV
      refine ⟨p.map jCV, hp.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have : (algebraMap (↥V) L).comp jCV = algebraMap (↥C) L := RingHom.ext (fun _ => rfl)
      rw [this]
      rw [Algebra.smul_def] at hpz
      exact hpz

    obtain ⟨k, w, hkw⟩ := exists_eq_pow_mul_unit A C hC ϖ hϖ hϖ0 d hd0
    obtain ⟨wi, hwi⟩ := (Units.isUnit w).exists_right_inv
    have hdinv : ((d : ↥C) : L)⁻¹ = ((wi : ↥C) : L) * ((((ϖ : ↥C) : L))⁻¹) ^ k := by
      rw [hkw, Subring.coe_mul, Subring.coe_pow, mul_inv, ← inv_pow]
      congr 1
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← Subring.coe_mul, hwi]; rfl
    have hd0L : ((d : ↥C) : L) ≠ 0 := fun h => hd0 (Subtype.ext h)
    have : z = ((d : ↥C) : L)⁻¹ * (((d : ↥C) : L) * z) := by
      rw [← mul_assoc, inv_mul_cancel₀ hd0L, one_mul]
    rw [this, hdinv]
    exact V.toSubring.mul_mem (V.toSubring.mul_mem (hCV _ wi.2) (V.toSubring.pow_mem hϖV k)) hdzV
  have hLO : ∀ z : L, algebraMap L F z ∈ O := fun z => by
    have := hLV z
    rwa [hV, ValuationSubring.mem_comap] at this

  obtain ⟨tsep, -, hfd, -⟩ := IsCurveOver.exists_separating_transcendental (K := L) (F := F)
  haveI := hfd
  obtain ⟨P, hP⟩ := AlgebraicCurve.Place.exists_of_valuationSubring (K := L) tsep O hLO hOtop
  have hPr : P.IsRational := isRational_of_isCurveOver P
  refine ⟨P, ?_, hP⟩

  have hN : ∀ f : F, f ∈ 𝒩₀ → f ∈ P.toValuationSubring := fun f hf => hP ▸ hO f hf
  refine (hS P).mpr ⟨hN, ?_⟩
  set φ : ↥𝒩₀ →+* L := (evalHom P hPr).comp (toValSub 𝒩₀ P.toValuationSubring hN) with hφ
  have hφ_apply : ∀ g : ↥𝒩₀, φ g = P.evalAt (g : F) := fun g => evalHom_apply P hPr _
  have hφ_const : ∀ c : L, ∀ hc : algebraMap L F c ∈ 𝒩₀, φ ⟨algebraMap L F c, hc⟩ = c := by
    intro c hc
    change evalHom P hPr (toValSub 𝒩₀ P.toValuationSubring hN ⟨algebraMap L F c, hc⟩) = c
    have : toValSub 𝒩₀ P.toValuationSubring hN ⟨algebraMap L F c, hc⟩ = algebraMap L P.toValuationSubring c := rfl
    rw [this, evalHom_algebraMap]
  obtain ⟨V', hV'mem, hV'loc⟩ := IsLocalRing.exists_factor_valuationRing φ
  have hCV' : ∀ c : L, c ∈ C → c ∈ V' := by
    intro c hc
    have := hV'mem ⟨algebraMap L F c, hCmem c hc⟩
    rwa [hφ_const] at this
  have hϖV' : ((ϖ : ↥C) : L) ∈ V'.nonunits := by
    have hnu : ¬ IsUnit (φ.codRestrict V'.toSubring hV'mem ⟨algebraMap L F ((ϖ : ↥C) : L), hCmem ϖ ϖ.2⟩) :=
      fun hu => hϖ𝒩 (IsLocalHom.map_nonunit _ hu)
    have hmax : (⟨φ ⟨algebraMap L F ((ϖ : ↥C) : L), hCmem ϖ ϖ.2⟩, hV'mem _⟩ : V') ∈ maximalIdeal V' := hnu
    have h2 := ValuationSubring.coe_mem_nonunits_iff.mpr hmax
    have h3 : ((⟨φ ⟨algebraMap L F ((ϖ : ↥C) : L), hCmem ϖ ϖ.2⟩, hV'mem _⟩ : V') : L) = ((ϖ : ↥C) : L) :=
      hφ_const _ _
    rwa [h3] at h2
  have hVA : V' = A := huniq V' hCV' hϖV'
  subst hVA
  intro g hg
  have hnu : ¬ IsUnit (φ.codRestrict V'.toSubring hV'mem g) := fun hu => hg (IsLocalHom.map_nonunit _ hu)
  have hmax : (⟨φ g, hV'mem g⟩ : V') ∈ maximalIdeal V' := hnu
  have h1 : P.evalAt (g : F) ∈ V' := by rw [← hφ_apply]; exact hV'mem g
  refine ⟨h1, ?_⟩
  have : (⟨φ g, hV'mem g⟩ : V') = ⟨P.evalAt (g : F), h1⟩ := Subtype.ext (hφ_apply g)
  rw [this] at hmax
  exact hmax

end
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_exists_mem_and_toValuationSubring_eq_of_forall_mem_of_not_mem_nonunits.TubeMaxAutoS"

end S_AlgebraicCurve_NodeAnnulusEngine_exists_mem_and_toValuationSubring_eq_of_forall_mem_of_not_mem_nonunits
end P2MW
export P2MW.S_AlgebraicCurve_NodeAnnulusEngine_exists_mem_and_toValuationSubring_eq_of_forall_mem_of_not_mem_nonunits (solution)
