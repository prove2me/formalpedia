-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.existsUnique_place_forall_residue_sub_mem_nonunits
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/c9e3f519-a337-55f2-a946-a80bcb0a1df3

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_ValuationSubring_exists_le_forall_mem_iff_apply_mem
import Theorems.Thm_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_AlgebraicCurve_exists_separating_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_exists_forall_ord_eq
import Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_existsUnique_place_forall_residue_sub_mem_nonunits

set_option autoImplicit false

noncomputable section

open IsLocalRing Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "RegularProlongation Place HasPrincipalDivisors HasPrincipalDivisors.exists_divisor IsCurveOver IsCurveOver.finiteResidue RegularProlongation.eq_integers_of_forall_mem_adjoin_iff exists_separating_transcendental_of_perfectField Place.exists_forall_ord_eq"
namespace RegularProlongation
p2m_export "AlgebraicCurve.RegularProlongation" "smul_const_ne_zero integers residue_algebraMap residue_surjective algebraMap_mem_iff exists_smul_mem ker_residue residue eq_integers_of_forall_mem_adjoin_iff"
namespace ExUniqPlace
p2m_open "AlgebraicCurve.RegularProlongation AlgebraicCurve"

section Generic

theorem isIntegralElem_of_forall_mem {S F : Type*} [CommRing S] [Field F] (φ : S →+* F) (x : F)
    (hx : ∀ V : ValuationSubring F, (∀ r, φ r ∈ V) → x ∈ V) : φ.IsIntegralElem x := by
  set s : Set F := Set.range φ with hs
  have hmem : x ∈ (⨅ V : {V : ValuationSubring F // s ⊆ V.toSubring}, V.1.toSubring) := by
    refine Subring.mem_iInf.mpr ?_
    rintro ⟨V, hV⟩
    exact hx V (fun r => hV ⟨r, rfl⟩)
  rw [iInf_valuationSubring_superset] at hmem
  have hint : IsIntegral (Subring.closure s) x :=
    (mem_integralClosure_iff _ _).mp (Subalgebra.mem_toSubring.mp hmem)
  obtain ⟨P, hPm, hPx⟩ := hint
  have hTle : Subring.closure s ≤ φ.range :=
    Subring.closure_le.mpr (by rintro _ ⟨r, rfl⟩; exact ⟨r, rfl⟩)
  have hP'm : (P.map (algebraMap (Subring.closure s) F)).Monic := hPm.map _
  have hP'x : (P.map (algebraMap (Subring.closure s) F)).eval x = 0 := by
    rw [eval_map]; exact hPx
  have hlifts : P.map (algebraMap (Subring.closure s) F) ∈ lifts φ := by
    rw [lifts_iff_coeff_lifts]
    intro n
    rw [coeff_map]
    exact hTle (P.coeff n).2
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hlifts hP'm
  refine ⟨q, hqm, ?_⟩
  rw [← eval_map, hq, hP'x]

theorem coeff_minpoly_mem_range {S K₀ F : Type*} [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    [Field K₀] [Field F] [Algebra S K₀] [IsFractionRing S K₀] [Algebra K₀ F]
    (x : F) (hx : ((algebraMap K₀ F).comp (algebraMap S K₀)).IsIntegralElem x) (j : ℕ) :
    (minpoly K₀ x).coeff j ∈ (algebraMap S K₀).range := by
  letI : Algebra S F := ((algebraMap K₀ F).comp (algebraMap S K₀)).toAlgebra
  haveI : IsScalarTower S K₀ F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hx' : IsIntegral S x := hx
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' K₀ hx', coeff_map]
  exact ⟨_, rfl⟩

end Generic

section Transcendental

variable {L F : Type*} [Field L] [Field F] [Algebra L F]

theorem isIntegrallyClosed_adjoin (t : F) (ht : Transcendental L t) :
    IsIntegrallyClosed (Algebra.adjoin L ({t} : Set F)) := by
  have hinj := transcendental_iff_injective.mp ht
  let e : L[X] ≃ₐ[L] Algebra.adjoin L ({t} : Set F) :=
    (AlgEquiv.ofInjective (aeval t) hinj).trans
      (Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval L t).symm)
  exact IsIntegrallyClosed.of_equiv e.toRingEquiv

theorem exists_coeff_minpoly_eq_aeval (K₀ : IntermediateField L F) (t : F)
    (hK : K₀ = IntermediateField.adjoin L {t}) (ht : Transcendental L t) (x : F)
    (hx : ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → t ∈ V → x ∈ V) (j : ℕ) :
    ∃ b : L[X], algebraMap (↥K₀) F ((minpoly (↥K₀) x).coeff j) = aeval t b := by
  subst hK
  set S := Algebra.adjoin L ({t} : Set F) with hS
  haveI : IsIntegrallyClosed S := isIntegrallyClosed_adjoin t ht
  have hint : ((algebraMap (IntermediateField.adjoin L ({t} : Set F)) F).comp
      (algebraMap S (IntermediateField.adjoin L ({t} : Set F)))).IsIntegralElem x := by
    apply isIntegralElem_of_forall_mem
    intro V hV
    apply hx V
    · intro c
      exact hV (algebraMap L S c)
    · exact hV ⟨t, Algebra.self_mem_adjoin_singleton L t⟩
  obtain ⟨r, hr⟩ := coeff_minpoly_mem_range x hint j
  have hr2 : (r : F) ∈ (aeval (R := L) t).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval L t]; exact r.2
  obtain ⟨b, hb⟩ := hr2
  refine ⟨b, ?_⟩
  rw [← hr]
  exact hb.symm

theorem isIntegral_of_forall_mem (K₀ : IntermediateField L F) (t : F)
    (hK : K₀ = IntermediateField.adjoin L {t}) (x : F)
    (hx : ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → t ∈ V → x ∈ V) :
    IsIntegral (↥K₀) x := by
  subst hK
  have hint : (algebraMap (IntermediateField.adjoin L ({t} : Set F)) F).IsIntegralElem x := by
    apply isIntegralElem_of_forall_mem
    intro V hV
    apply hx V
    · intro c
      exact hV (algebraMap L _ c)
    · exact hV ⟨t, IntermediateField.mem_adjoin_simple_self L t⟩
  exact hint

end Transcendental

section Normalise

variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem exists_eq_C_mul_map (b : L[X]) (hb : b ≠ 0) :
    ∃ (c : L) (b₀ : A[X]), c ≠ 0 ∧ b = C c * b₀.map A.subtype ∧ ∃ i, b₀.coeff i = 1 := by
  classical
  obtain ⟨c, hcs, hc⟩ :=
    Finset.exists_max_image b.coeffs A.valuation (coeffs_nonempty_iff.mpr hb)
  obtain ⟨i₀, hi₀, hci₀⟩ := mem_coeffs_iff.mp hcs
  have hc0 : c ≠ 0 := by rw [hci₀]; exact mem_support_iff.mp hi₀
  have hcoef : ∀ n, c⁻¹ * b.coeff n ∈ A := by
    intro n
    by_cases hn : b.coeff n = 0
    · simp [hn]
    · apply (A.valuation_le_one_iff _).mp
      have h1 : A.valuation (c⁻¹ * c) = 1 := by rw [inv_mul_cancel₀ hc0, map_one]
      rw [map_mul, ← h1, map_mul]
      exact mul_le_mul_right (hc _ (coeff_mem_coeffs hn)) _
  have hl : C c⁻¹ * b ∈ lifts A.subtype := by
    rw [lifts_iff_coeff_lifts]
    intro n
    rw [coeff_C_mul]
    exact ⟨⟨_, hcoef n⟩, rfl⟩
  obtain ⟨b₀, hb₀⟩ := (mem_lifts _).mp hl
  refine ⟨c, b₀, hc0, ?_, i₀, ?_⟩
  · rw [hb₀, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hc0, C_1, one_mul]
  · apply A.subtype_injective
    have := congrArg (fun q => q.coeff i₀) hb₀
    simp only [coeff_map, coeff_C_mul] at this
    rw [map_one, this, ← hci₀, inv_mul_cancel₀ hc0]

end Normalise

section Prolongation

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

def constHom (R : RegularProlongation A F Fbar) : A →+* R.integers where
  toFun a := ⟨algebraMap L F a, (R.algebraMap_mem_iff a).mpr a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[scoped simp] theorem coe_constHom (R : RegularProlongation A F Fbar) (a : A) :
    ((constHom R a : R.integers) : F) = algebraMap L F a := rfl

theorem residue_constHom (R : RegularProlongation A F Fbar) (a : A) :
    R.residue (constHom R a) = algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) :=
  R.residue_algebraMap a

theorem coe_eval₂_constHom (R : RegularProlongation A F Fbar) (f : R.integers) (b : A[X]) :
    ((b.eval₂ (constHom R) f : R.integers) : F) = (b.map A.subtype).eval₂ (algebraMap L F) f := by
  have hcomp : R.integers.subtype.comp (constHom R) = (algebraMap L F).comp A.subtype := by
    ext a; rfl
  rw [eval₂_map, show ((b.eval₂ (constHom R) f : R.integers) : F) =
    R.integers.subtype (b.eval₂ (constHom R) f) from rfl, Polynomial.hom_eval₂, hcomp]
  rfl

theorem residue_eval₂_constHom (R : RegularProlongation A F Fbar) (f : R.integers) (b : A[X]) :
    R.residue (b.eval₂ (constHom R) f) = aeval (R.residue f) (b.map (IsLocalRing.residue A)) := by
  have hcomp : R.residue.comp (constHom R) =
      (algebraMap (ResidueField A) Fbar).comp (IsLocalRing.residue A) := by
    ext a; exact residue_constHom R a
  rw [Polynomial.hom_eval₂, hcomp, aeval_def, eval₂_map]

theorem residue_eval₂_ne_zero (R : RegularProlongation A F Fbar) (f : R.integers)
    (htr : Transcendental (ResidueField A) (R.residue f)) (b₀ : A[X]) (i : ℕ)
    (hi : b₀.coeff i = 1) : R.residue (b₀.eval₂ (constHom R) f) ≠ 0 := by
  rw [residue_eval₂_constHom]
  intro h0
  apply htr
  refine ⟨b₀.map (IsLocalRing.residue A), ?_, h0⟩
  intro hzero
  have := congrArg (fun q => q.coeff i) hzero
  simp [coeff_map, hi] at this

theorem transcendental_of_residue (R : RegularProlongation A F Fbar) (f : R.integers)
    (htr : Transcendental (ResidueField A) (R.residue f)) : Transcendental L (f : F) := by
  rintro ⟨b, hb0, hbf⟩
  obtain ⟨c, b₀, hc0, hb, i, hi⟩ := exists_eq_C_mul_map A b hb0
  apply residue_eval₂_ne_zero R f htr b₀ i hi
  have hval : (b₀.eval₂ (constHom R) f : R.integers) = 0 := by
    apply Subtype.ext
    rw [coe_eval₂_constHom, ZeroMemClass.coe_zero]
    have h1 : aeval (f : F) b = algebraMap L F c * (b₀.map A.subtype).eval₂ (algebraMap L F) f := by
      rw [hb, aeval_def, eval₂_mul, eval₂_C]
    rw [hbf] at h1
    have hc' : algebraMap L F c ≠ 0 := (_root_.map_ne_zero _).mpr hc0
    rcases mul_eq_zero.mp h1.symm with h | h
    · exact absurd h hc'
    · exact h
  rw [hval, map_zero]

theorem coeff_mem_of_aeval_mem (R : RegularProlongation A F Fbar) (f : R.integers)
    (htr : Transcendental (ResidueField A) (R.residue f)) (b : L[X])
    (hbO : aeval (f : F) b ∈ R.integers) (n : ℕ) : b.coeff n ∈ A := by
  by_cases hb0 : b = 0
  · simp [hb0]
  obtain ⟨c, b₀, hc0, hb, i, hi⟩ := exists_eq_C_mul_map A b hb0
  have hcoeff : b.coeff n = c * (b₀.coeff n : L) := by
    rw [hb, coeff_C_mul, coeff_map]; rfl
  suffices hcA : c ∈ A by rw [hcoeff]; exact A.mul_mem _ _ hcA (b₀.coeff n).2
  by_contra hcA
  have hcinv : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA
  have hnu : ¬IsUnit (⟨c⁻¹, hcinv⟩ : A) := by
    intro hu
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hu
    apply hcA
    have hy' : (c⁻¹ : L) * y = 1 := by
      have := congrArg (fun z : A => (z : L)) hy
      simpa using this
    have hyc : (y : L) = c := by
      rw [eq_inv_of_mul_eq_one_right hy', inv_inv]
    rw [← hyc]; exact y.2
  have hres0 : IsLocalRing.residue A ⟨c⁻¹, hcinv⟩ = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
  apply residue_eval₂_ne_zero R f htr b₀ i hi
  have hval : (b₀.eval₂ (constHom R) f : R.integers) =
      constHom R ⟨c⁻¹, hcinv⟩ * ⟨aeval (f : F) b, hbO⟩ := by
    apply Subtype.ext
    rw [coe_eval₂_constHom]
    show (b₀.map A.subtype).eval₂ (algebraMap L F) f = algebraMap L F c⁻¹ * aeval (f : F) b
    rw [hb, aeval_def, eval₂_mul, eval₂_C, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one,
      one_mul]
  rw [hval, map_mul, residue_constHom, hres0, map_zero, zero_mul]

theorem mem_of_forall_trace (O : ValuationSubring F) (K₀ : IntermediateField L F) (h : F)
    (hG : ∀ V : ValuationSubring F, (∀ e ∈ K₀, (e ∈ V ↔ e ∈ O)) → h ∈ V)
    (V : ValuationSubring F) (hV : ∀ e ∈ K₀, e ∈ O → e ∈ V) : h ∈ V := by
  set OG : ValuationSubring K₀ := O.comap (algebraMap K₀ F) with hOG
  have hOGV : ∀ x : OG, ((algebraMap K₀ F).comp OG.subtype) x ∈ V := fun x =>
    hV _ (x : K₀).2 (ValuationSubring.mem_comap.mp x.2)
  set ι : OG →+* V := ((algebraMap K₀ F).comp OG.subtype).codRestrict V hOGV with hι
  set φ : OG →+* ResidueField V := (IsLocalRing.residue V).comp ι with hφ
  obtain ⟨W, hW, hloc⟩ := IsLocalRing.exists_factor_valuationRing φ
  obtain ⟨O', hO'V, hmem, hnon⟩ := ValuationSubring.exists_le_forall_mem_iff_apply_mem V
    (IsLocalRing.residue V) (IsLocalRing.ker_residue (R := V)).symm.le W
  apply hO'V
  apply hG O'
  intro e he
  constructor
  · intro heO'
    by_contra heO
    have he0 : e ≠ 0 := by rintro rfl; exact heO O.zero_mem
    have heinv : e⁻¹ ∈ O := (O.mem_or_inv_mem e).resolve_left heO
    have heinvK : e⁻¹ ∈ K₀ := inv_mem he
    have hyOG : (⟨e⁻¹, heinvK⟩ : K₀) ∈ OG := ValuationSubring.mem_comap.mpr heinv
    set y : OG := ⟨⟨e⁻¹, heinvK⟩, hyOG⟩ with hy_def
    have hy : ¬IsUnit y := by
      intro hu
      obtain ⟨z, hz⟩ := isUnit_iff_exists_inv.mp hu
      apply heO
      have hz' : (e⁻¹ : F) * ((z : K₀) : F) = 1 := by
        have := congrArg (fun w : OG => ((w : K₀) : F)) hz
        simpa using this
      have hze : ((z : K₀) : F) = e := by rw [eq_inv_of_mul_eq_one_right hz', inv_inv]
      rw [← hze]; exact ValuationSubring.mem_comap.mp z.2
    have h1 : ¬IsUnit ((φ.codRestrict W.toSubring hW) y) := by
      intro hu
      haveI := hloc
      exact hy (IsLocalHom.map_nonunit _ hu)
    have h2 : φ y ∈ W.nonunits := by
      have h3 : (⟨φ y, hW y⟩ : W) ∈ IsLocalRing.maximalIdeal W :=
        (IsLocalRing.mem_maximalIdeal _).mpr h1
      exact ValuationSubring.coe_mem_nonunits_iff.mpr h3
    have h4 : (e⁻¹ : F) ∈ O'.nonunits := (hnon ⟨e⁻¹, hV _ heinvK heinv⟩).mpr h2
    rcases (O'.inv_mem_nonunits_iff).mp h4 with h5 | h5
    · exact he0 h5
    · exact h5 heO'
  · intro heO
    have heV : e ∈ V := hV e he heO
    apply (hmem ⟨e, heV⟩).mpr
    exact hW ⟨⟨e, he⟩, ValuationSubring.mem_comap.mpr heO⟩

theorem exists_monic (R : RegularProlongation A F Fbar) (f : R.integers)
    (htr : Transcendental (ResidueField A) (R.residue f)) (h : F)
    (hfin : ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → (f : F) ∈ V → h ∈ V)
    (hG : ∀ V : ValuationSubring F,
      (∀ e : F, e ∈ IntermediateField.adjoin L {(f : F)} → (e ∈ V ↔ e ∈ R.integers)) → h ∈ V) :
    ∃ p : Polynomial (Polynomial A), p.Monic ∧
      p.eval₂ (eval₂RingHom ((algebraMap L F).comp A.subtype) (f : F)) h = 0 := by

  set t : F := (f : F) with ht_def
  have htL : Transcendental L t := transcendental_of_residue R f htr
  set K₀ : IntermediateField L F := IntermediateField.adjoin L {t} with hK₀
  have htK : t ∈ K₀ := IntermediateField.mem_adjoin_simple_self L t

  have hint : IsIntegral K₀ h := isIntegral_of_forall_mem K₀ t rfl h hfin
  set P : K₀[X] := minpoly K₀ h with hP

  have hb' : ∀ j, ∃ b : L[X], algebraMap K₀ F (P.coeff j) = aeval t b :=
    fun j => exists_coeff_minpoly_eq_aeval K₀ t rfl htL h hfin j
  choose b hb using hb'

  have hPO : ∀ j, algebraMap K₀ F (P.coeff j) ∈ R.integers := by
    intro j
    let OG : ValuationSubring K₀ := R.integers.comap (algebraMap K₀ F)
    have hintG : ((algebraMap K₀ F).comp (algebraMap OG K₀)).IsIntegralElem h := by
      apply isIntegralElem_of_forall_mem
      intro V hV
      refine mem_of_forall_trace R.integers K₀ h hG V ?_
      intro e he heO
      exact hV ⟨⟨e, he⟩, ValuationSubring.mem_comap.mpr heO⟩
    obtain ⟨r, hr⟩ := coeff_minpoly_mem_range h hintG j
    rw [← hr]
    exact ValuationSubring.mem_comap.mp r.2

  have hbO : ∀ j, aeval t (b j) ∈ R.integers := fun j => hb j ▸ hPO j
  have hcoefA : ∀ j n, (b j).coeff n ∈ A :=
    fun j n => coeff_mem_of_aeval_mem R f htr (b j) (hbO j) n
  have hlift : ∀ j, ∃ a : A[X], a.map A.subtype = b j := by
    intro j
    have : b j ∈ lifts A.subtype := by
      rw [lifts_iff_coeff_lifts]; intro n; exact ⟨⟨_, hcoefA j n⟩, rfl⟩
    exact (mem_lifts _).mp this
  choose a ha using hlift

  set ι : A[X] →+* K₀ := eval₂RingHom ((algebraMap L K₀).comp A.subtype) ⟨t, htK⟩ with hι
  have hcompK : (algebraMap K₀ F).comp ((algebraMap L K₀).comp A.subtype) =
      (algebraMap L F).comp A.subtype := by
    ext x; rfl
  have hιF : ∀ q : A[X], algebraMap K₀ F (ι q) = (q.map A.subtype).eval₂ (algebraMap L F) t := by
    intro q
    rw [hι, coe_eval₂RingHom, Polynomial.hom_eval₂, hcompK, eval₂_map]
    rfl
  have hιa : ∀ j, ι (a j) = P.coeff j := by
    intro j
    apply (algebraMap K₀ F).injective
    rw [hιF, ha, hb j, aeval_def]
  have hPlifts : P ∈ lifts ι := by
    rw [lifts_iff_coeff_lifts]; intro j; exact ⟨a j, hιa j⟩
  obtain ⟨p, hpP, -, hpm⟩ := lifts_and_degree_eq_and_monic hPlifts (minpoly.monic hint)
  refine ⟨p, hpm, ?_⟩
  have h0 : aeval h P = 0 := minpoly.aeval K₀ h
  rw [aeval_def, ← hpP, eval₂_map] at h0
  have hcomp : (algebraMap K₀ F).comp ι = eval₂RingHom ((algebraMap L F).comp A.subtype) t := by
    refine Polynomial.ringHom_ext (fun x => ?_) ?_
    · rw [RingHom.comp_apply, hιF, Polynomial.map_C, eval₂_C, coe_eval₂RingHom, eval₂_C]
      rfl
    · rw [RingHom.comp_apply, hιF, Polynomial.map_X, eval₂_X, coe_eval₂RingHom, eval₂_X]
  rw [hcomp] at h0
  exact h0

end Prolongation

section GenericPlace

variable {k : Type*} [Field k] {E : Type*} [Field E] [Algebra k E]

theorem mem_valuationSubring_of_isIntegral {S : Type*} [CommRing S] [Algebra S E]
    (V : ValuationSubring E) (hS : ∀ s : S, algebraMap S E s ∈ V) {z : E}
    (hz : IsIntegral S z) : z ∈ V := by
  obtain ⟨p, hpm, hpz⟩ := hz
  set φ : S →+* V := (algebraMap S E).codRestrict V hS with hφ
  have hcomp : (algebraMap V E).comp φ = algebraMap S E := RingHom.ext fun _ => rfl
  have hint : IsIntegral V z := by
    refine ⟨p.map φ, hpm.map φ, ?_⟩
    rw [eval₂_map, hcomp]
    exact hpz
  obtain ⟨w, hw⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := E)).mp hint
  rw [← hw]
  exact w.2

def subalg (V : ValuationSubring E) (hV : ∀ c : k, algebraMap k E c ∈ V) : Subalgebra k E :=
  { V.toSubring with algebraMap_mem' := fun c => hV c }

theorem coe_adjoin_mem (V : ValuationSubring E) (hV : ∀ c : k, algebraMap k E c ∈ V) {y : E}
    (hy : y ∈ V) (s : Algebra.adjoin k ({y} : Set E)) : (s : E) ∈ V := by
  have hle : Algebra.adjoin k ({y} : Set E) ≤ subalg V hV :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hy)
  exact hle s.2

theorem isIntegral_self (y : E) : IsIntegral (Algebra.adjoin k ({y} : Set E)) y :=
  isIntegral_algebraMap (x := (⟨y, Algebra.self_mem_adjoin_singleton k y⟩ : Algebra.adjoin k {y}))

theorem isIntegral_const (y : E) (c : k) :
    IsIntegral (Algebra.adjoin k ({y} : Set E)) (algebraMap k E c) := by
  have h := isIntegral_algebraMap (R := Algebra.adjoin k ({y} : Set E)) (A := E)
    (x := algebraMap k (Algebra.adjoin k ({y} : Set E)) c)
  rwa [← IsScalarTower.algebraMap_apply] at h

theorem inv_adjoin_eq (y : E) :
    IntermediateField.adjoin k ({y⁻¹} : Set E) = IntermediateField.adjoin k ({y} : Set E) := by
  apply le_antisymm
  · exact IntermediateField.adjoin_simple_le_iff.mpr
      (IntermediateField.inv_mem _ (IntermediateField.mem_adjoin_simple_self k y))
  · refine IntermediateField.adjoin_simple_le_iff.mpr ?_
    have := IntermediateField.inv_mem _ (IntermediateField.mem_adjoin_simple_self k y⁻¹)
    rwa [inv_inv] at this

theorem ne_top_of_mem_nonunits {V : ValuationSubring E} {y : E} (hy : y ∈ V.nonunits)
    (hy0 : y ≠ 0) : V ≠ ⊤ := by
  intro htop
  rcases (ValuationSubring.mem_nonunits_iff_or (A := V)).mp hy with h | h
  · exact hy0 h
  · exact h (by rw [htop]; exact ValuationSubring.mem_top _)

theorem valuation_algebraMap_eq_one (P : Place k E) {c : k} (hc : c ≠ 0) :
    P.toValuationSubring.valuation (algebraMap k E c) = 1 := by
  let u : (P.toValuationSubring)ˣ :=
    ⟨algebraMap k P.toValuationSubring c, algebraMap k P.toValuationSubring c⁻¹,
      by rw [← map_mul, mul_inv_cancel₀ hc, map_one],
      by rw [← map_mul, inv_mul_cancel₀ hc, map_one]⟩
  exact P.toValuationSubring.valuation_unit u

theorem valuation_sub_algebraMap_eq_one (Q : Place k E) {y : E} {κ₀ κ : k}
    (h₀ : y - algebraMap k E κ₀ ∈ Q.toValuationSubring.nonunits) (hne : κ ≠ κ₀) :
    Q.toValuationSubring.valuation (y - algebraMap k E κ) = 1 := by
  have h1 : y - algebraMap k E κ = algebraMap k E (κ₀ - κ) + (y - algebraMap k E κ₀) := by
    rw [map_sub]; ring
  rw [h1, Valuation.map_add_eq_of_lt_left _ ?_, valuation_algebraMap_eq_one Q
    (sub_ne_zero.mpr hne.symm)]
  rw [valuation_algebraMap_eq_one Q (sub_ne_zero.mpr hne.symm)]
  exact (ValuationSubring.mem_nonunits_iff _).mp h₀

theorem exists_sub_algebraMap_mem_nonunits [IsAlgClosed k] [IsCurveOver k E] (P : Place k E)
    {h : E} (hh : h ∈ P.toValuationSubring) :
    ∃ c : k, h - algebraMap k E c ∈ P.toValuationSubring.nonunits := by
  haveI : Module.Finite k P.ResidueField := IsCurveOver.finiteResidue P
  haveI : Algebra.IsIntegral k P.ResidueField := Algebra.IsIntegral.of_finite k P.ResidueField
  obtain ⟨c, hc⟩ :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := P.ResidueField)).2
      (IsLocalRing.residue P.toValuationSubring ⟨h, hh⟩)
  refine ⟨c, ?_⟩
  have hmem : (⟨h, hh⟩ : P.toValuationSubring) - algebraMap k P.toValuationSubring c ∈
      maximalIdeal P.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← hc]
    exact (IsScalarTower.algebraMap_apply k P.toValuationSubring P.ResidueField c).symm
  have := ValuationSubring.coe_mem_nonunits_iff.mpr hmem
  simpa using this

theorem ord_nonneg_of_mem (v : Place k E) {f : E} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : E) * ((π : E) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem mem_of_ord_nonneg (v : Place k E) {f : E} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem ord_eq_zero_of_isUnit (Q : Place k E) {f : E} (hf : f ∈ Q.toValuationSubring)
    (hu : IsUnit (⟨f, hf⟩ : Q.toValuationSubring)) : Q.ord f = 0 := by
  have := Q.ord_coe_unit hu.unit
  rwa [hu.unit_spec] at this

theorem ord_eq_zero_of_valuation_eq_one (Q : Place k E) {f : E} (hf : f ∈ Q.toValuationSubring)
    (hv : Q.toValuationSubring.valuation f = 1) : Q.ord f = 0 :=
  ord_eq_zero_of_isUnit Q hf ((Q.toValuationSubring.valuation_eq_one_iff ⟨f, hf⟩).mpr hv)

theorem ord_prod (Q : Place k E) {ι : Type*} (s : Finset ι) (f : ι → E) :
    (∀ i ∈ s, f i ≠ 0) → Q.ord (∏ i ∈ s, f i) = ∑ i ∈ s, Q.ord (f i) := by
  classical
  refine Finset.induction_on s (fun _ => by simp) ?_
  intro a s ha ih hf
  rw [Finset.prod_insert ha, Finset.sum_insert ha,
    Q.ord_mul (hf a (Finset.mem_insert_self a s))
      (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
    ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem ord_pow (Q : Place k E) (f : E) (n : ℕ) : Q.ord (f ^ n) = (n : ℤ) * Q.ord f := by
  rw [← zpow_natCast]; exact Q.ord_zpow f n

theorem ord_pos_of_mem_nonunits (Q : Place k E) {f : E} (hf : f ∈ Q.toValuationSubring.nonunits)
    (hf0 : f ≠ 0) : 0 < Q.ord f := by
  obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hf
  exact (Q.mem_maximalIdeal_iff_ord_pos hf0 hmem).mp hmax

theorem mem_nonunits_of_ord_pos (Q : Place k E) {f : E} (hf0 : f ≠ 0) (h : 0 < Q.ord f) :
    f ∈ Q.toValuationSubring.nonunits := by
  have hmem : f ∈ Q.toValuationSubring := mem_of_ord_nonneg Q hf0 h.le
  exact ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr
    ⟨hmem, (Q.mem_maximalIdeal_iff_ord_pos hf0 hmem).mpr h⟩

end GenericPlace

section ValuationRingIsPlace

variable {k : Type*} [Field k] {E : Type*} [Field E] [Algebra k E]

theorem exists_place_eq_aux (t : E) (ht : Transcendental k t)
    (hfd : FiniteDimensional (IntermediateField.adjoin k ({t} : Set E)) E)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k ({t} : Set E)) E)
    (V : ValuationSubring E) (hk : ∀ κ : k, algebraMap k E κ ∈ V) (hV : V ≠ ⊤) (htV : t ∈ V) :
    ∃ Q : Place k E, Q.toValuationSubring = V := by
  classical
  haveI := hfd
  haveI := hsep
  set R₀ : Subalgebra k E := Algebra.adjoin k ({t} : Set E) with hR₀
  haveI : IsPrincipalIdealRing R₀ := by
    have hinj := transcendental_iff_injective.mp ht
    let e : k[X] ≃ₐ[k] R₀ := (AlgEquiv.ofInjective (aeval t) hinj).trans
      (Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval k t).symm)
    exact IsPrincipalIdealRing.of_surjective e.toRingEquiv.toRingHom e.surjective
  haveI : IsDedekindDomain R₀ := IsPrincipalIdealRing.isDedekindDomain R₀
  set Rt : Subalgebra R₀ E := integralClosure R₀ E with hRt
  haveI : IsDedekindDomain Rt :=
    integralClosure.isDedekindDomain R₀ (IntermediateField.adjoin k ({t} : Set E)) E
  haveI : IsFractionRing Rt E :=
    integralClosure.isFractionRing_of_finite_extension (A := R₀)
      (IntermediateField.adjoin k ({t} : Set E)) E

  have hR₀V : ∀ s : R₀, algebraMap R₀ E s ∈ V := fun s => coe_adjoin_mem V hk htV s
  have hRtV : ∀ z : Rt, algebraMap Rt E z ∈ V := fun z =>
    mem_valuationSubring_of_isIntegral V hR₀V z.2
  set φ : Rt →+* V := (algebraMap Rt E).codRestrict V hRtV with hφ

  set 𝔭 : Ideal Rt := (IsLocalRing.maximalIdeal V).comap φ with h𝔭
  haveI h𝔭prime : 𝔭.IsPrime := Ideal.IsPrime.comap φ
  have hunit : ∀ s : Rt, s ∉ 𝔭 → V.valuation (algebraMap Rt E s) = 1 := by
    intro s hs
    have hsu : IsUnit (φ s) := by
      by_contra hnu
      exact hs (Ideal.mem_comap.mpr ((IsLocalRing.mem_maximalIdeal _).mpr hnu))
    exact (V.valuation_eq_one_iff (φ s)).mp hsu
  have h𝔭ne : 𝔭 ≠ ⊥ := by
    intro hbot
    apply hV
    rw [eq_top_iff]
    intro z _
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Rt) z
    have hb𝔭 : b ∉ 𝔭 := by
      rw [hbot]
      intro hb0
      exact nonZeroDivisors.ne_zero hb ((Submodule.mem_bot _).mp hb0)
    apply (V.valuation_le_one_iff _).mp
    rw [map_div₀, hunit b hb𝔭, div_one]
    exact V.valuation_le_one (φ a)
  let P₀ : IsDedekindDomain.HeightOneSpectrum Rt := ⟨𝔭, h𝔭prime, h𝔭ne⟩
  have hle : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E P₀ ≤ V := by
    rintro z ⟨a, s, hs, rfl⟩
    apply (V.valuation_le_one_iff _).mp
    rw [map_mul, map_inv₀, hunit s hs, inv_one, mul_one]
    exact V.valuation_le_one (φ a)
  have heq : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E P₀ = V :=
    ValuationSubring.eq_of_le_of_ne_top _ hle hV
  refine ⟨⟨V, hk, hV, ?_⟩, rfl⟩
  rw [← heq]
  infer_instance

theorem exists_place_eq [PerfectField k] {y : E} (hy : Transcendental k y)
    [hfd : FiniteDimensional (IntermediateField.adjoin k ({y} : Set E)) E]
    (V : ValuationSubring E) (hk : ∀ κ : k, algebraMap k E κ ∈ V) (hV : V ≠ ⊤) :
    ∃ Q : Place k E, Q.toValuationSubring = V := by
  obtain ⟨t, ht, hfd', hsep⟩ :=
    AlgebraicCurve.exists_separating_transcendental_of_perfectField hy hfd
  rcases V.mem_or_inv_mem t with htV | htV
  · exact exists_place_eq_aux t ht hfd' hsep V hk hV htV
  · have ht' : Transcendental k t⁻¹ := fun h => ht (by simpa using h.inv)
    rw [← inv_adjoin_eq t] at hfd' hsep
    exact exists_place_eq_aux t⁻¹ ht' hfd' hsep V hk hV htV

theorem isIntegral_adjoin_of_forall_place [PerfectField k] {y : E} (hy : Transcendental k y)
    [FiniteDimensional (IntermediateField.adjoin k ({y} : Set E)) E] {g : E}
    (hg : ∀ Q : Place k E, y ∈ Q.toValuationSubring → g ∈ Q.toValuationSubring) :
    IsIntegral (Algebra.adjoin k ({y} : Set E)) g := by
  have := isIntegralElem_of_forall_mem (algebraMap (Algebra.adjoin k ({y} : Set E)) E) g ?_
  · exact this
  intro V hV
  by_cases hVtop : V = ⊤
  · rw [hVtop]; exact ValuationSubring.mem_top g
  have hkV : ∀ κ : k, algebraMap k E κ ∈ V := fun κ => hV (algebraMap k _ κ)
  have hyV : y ∈ V := hV ⟨y, Algebra.self_mem_adjoin_singleton k y⟩
  obtain ⟨Q, hQ⟩ := exists_place_eq hy V hkV hVtop
  rw [← hQ] at hyV ⊢
  exact hg Q hyV

end ValuationRingIsPlace

section Separate

variable {k : Type*} [Field k] {E : Type*} [Field E] [Algebra k E]

theorem exists_separating [IsAlgClosed k] [IsCurveOver k E]
    {y : E} (hy : Transcendental k y)
    [FiniteDimensional (IntermediateField.adjoin k ({y} : Set E)) E]
    (Q₁ Q₂ : Place k E) (hne : Q₁ ≠ Q₂) (c : k)
    (h₁ : y - algebraMap k E c ∈ Q₁.toValuationSubring.nonunits)
    (h₂ : y - algebraMap k E c ∈ Q₂.toValuationSubring.nonunits) :
    ∃ g : E, IsIntegral (Algebra.adjoin k ({y} : Set E)) g ∧
      g ∈ Q₁.toValuationSubring.nonunits ∧ g ∉ Q₂.toValuationSubring.nonunits := by
  classical

  have hyc0 : y - algebraMap k E c ≠ 0 := by
    intro h0
    apply hy
    rw [sub_eq_zero] at h0
    rw [h0]
    exact isAlgebraic_algebraMap c

  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := k) (y - algebraMap k E c) hyc0
  set T : Finset (Place k E) := insert Q₁ (insert Q₂ D.support) with hT

  obtain ⟨f, hf0, hf⟩ :=
    Place.exists_forall_ord_eq T (fun Q => if Q = Q₁ then (1 : ℤ) else 0)
  have hf₁ : Q₁.ord f = 1 := by
    have := hf Q₁ (by simp [hT])
    simpa using this
  have hf₂ : Q₂.ord f = 0 := by
    have := hf Q₂ (by simp [hT])
    rwa [if_neg (Ne.symm hne)] at this
  have hfT : ∀ Q ∈ T, 0 ≤ Q.ord f := by
    intro Q hQ
    rw [hf Q hQ]
    split_ifs <;> norm_num

  obtain ⟨Df, hDf, -⟩ := HasPrincipalDivisors.exists_divisor (K := k) f hf0
  set S : Finset (Place k E) :=
    Df.support.filter (fun Q => Q.ord f < 0 ∧ y ∈ Q.toValuationSubring) with hS
  have hSmem : ∀ Q ∈ S, Q.ord f < 0 ∧ y ∈ Q.toValuationSubring := fun Q hQ =>
    (Finset.mem_filter.mp hQ).2
  have hS_of : ∀ Q : Place k E, y ∈ Q.toValuationSubring → Q.ord f < 0 → Q ∈ S := by
    intro Q hyQ hord
    refine Finset.mem_filter.mpr ⟨?_, hord, hyQ⟩
    rw [Finsupp.mem_support_iff, hDf]
    exact hord.ne
  have hSnotT : ∀ Q ∈ S, Q ∉ T := fun Q hQ hQT => (not_le.mpr (hSmem Q hQ).1) (hfT Q hQT)

  have hκ' : ∀ Q ∈ S, ∃ κ : k, y - algebraMap k E κ ∈ Q.toValuationSubring.nonunits :=
    fun Q hQ => exists_sub_algebraMap_mem_nonunits Q (hSmem Q hQ).2
  choose! κ hκ using hκ'
  have hκc : ∀ Q ∈ S, κ Q ≠ c := by
    intro Q hQ hκQ
    apply hSnotT Q hQ
    have hpos : 0 < Q.ord (y - algebraMap k E c) := by
      have := hκ Q hQ
      rw [hκQ] at this
      exact ord_pos_of_mem_nonunits Q this hyc0
    have hQD : Q ∈ D.support := by
      rw [Finsupp.mem_support_iff, hD]
      exact hpos.ne'
    simp [hT, hQD]

  have hfac0 : ∀ Q : Place k E, y - algebraMap k E (κ Q) ≠ 0 := by
    intro Q h0
    apply hy
    rw [sub_eq_zero] at h0
    rw [h0]
    exact isAlgebraic_algebraMap _
  set g : E := f * ∏ Q' ∈ S, (y - algebraMap k E (κ Q')) ^ (-Q'.ord f).toNat with hg
  have hprod0 : (∏ Q' ∈ S, (y - algebraMap k E (κ Q')) ^ (-Q'.ord f).toNat) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun Q' _ => pow_ne_zero _ (hfac0 Q')
  have hg0 : g ≠ 0 := mul_ne_zero hf0 hprod0
  have hordg : ∀ Q : Place k E, Q.ord g =
      Q.ord f + ∑ Q' ∈ S, ((-Q'.ord f).toNat : ℤ) * Q.ord (y - algebraMap k E (κ Q')) := by
    intro Q
    rw [hg, Q.ord_mul hf0 hprod0,
      ord_prod Q S (fun Q' => (y - algebraMap k E (κ Q')) ^ (-Q'.ord f).toNat)
        (fun Q' _ => pow_ne_zero _ (hfac0 Q'))]
    simp only [ord_pow]
  have hfac_nonneg : ∀ Q : Place k E, y ∈ Q.toValuationSubring →
      ∀ Q' ∈ S, 0 ≤ ((-Q'.ord f).toNat : ℤ) * Q.ord (y - algebraMap k E (κ Q')) := by
    intro Q hyQ Q' _
    exact mul_nonneg (Int.natCast_nonneg _)
      (ord_nonneg_of_mem Q (sub_mem hyQ (Q.algebraMap_mem' _)))

  have hg_nonneg : ∀ Q : Place k E, y ∈ Q.toValuationSubring → 0 ≤ Q.ord g := by
    intro Q hyQ
    rw [hordg Q]
    by_cases hord : Q.ord f < 0
    · have hQS : Q ∈ S := hS_of Q hyQ hord
      have hpos : 1 ≤ Q.ord (y - algebraMap k E (κ Q)) :=
        ord_pos_of_mem_nonunits Q (hκ Q hQS) (hfac0 Q)
      have hm : ((-Q.ord f).toNat : ℤ) = -Q.ord f := Int.toNat_of_nonneg (by omega)
      have hle : ((-Q.ord f).toNat : ℤ) * Q.ord (y - algebraMap k E (κ Q)) ≤
          ∑ Q' ∈ S, ((-Q'.ord f).toNat : ℤ) * Q.ord (y - algebraMap k E (κ Q')) :=
        Finset.single_le_sum
          (f := fun Q' => ((-Q'.ord f).toNat : ℤ) * Q.ord (y - algebraMap k E (κ Q')))
          (hfac_nonneg Q hyQ) hQS
      have h3 : ((-Q.ord f).toNat : ℤ) ≤
          ((-Q.ord f).toNat : ℤ) * Q.ord (y - algebraMap k E (κ Q)) :=
        le_mul_of_one_le_right (Int.natCast_nonneg _) hpos
      linarith
    · have := Finset.sum_nonneg (hfac_nonneg Q hyQ)
      linarith

  have hy₁ : y ∈ Q₁.toValuationSubring := by
    have := add_mem (ValuationSubring.nonunits_subset h₁) (Q₁.algebraMap_mem' c)
    simpa using this
  have hy₂ : y ∈ Q₂.toValuationSubring := by
    have := add_mem (ValuationSubring.nonunits_subset h₂) (Q₂.algebraMap_mem' c)
    simpa using this

  have hg₁ : 0 < Q₁.ord g := by
    rw [hordg Q₁, hf₁]
    have := Finset.sum_nonneg (hfac_nonneg Q₁ hy₁)
    linarith
  have hg₂ : Q₂.ord g = 0 := by
    rw [hordg Q₂, hf₂, zero_add]
    refine Finset.sum_eq_zero fun Q' hQ' => ?_
    rw [ord_eq_zero_of_valuation_eq_one Q₂ (sub_mem hy₂ (Q₂.algebraMap_mem' _))
      (valuation_sub_algebraMap_eq_one Q₂ h₂ (hκc Q' hQ')), mul_zero]
  refine ⟨g, ?_, mem_nonunits_of_ord_pos Q₁ hg0 hg₁, fun hmem => ?_⟩
  · exact isIntegral_adjoin_of_forall_place hy fun Q hyQ =>
      mem_of_ord_nonneg Q hg0 (hg_nonneg Q hyQ)
  · have := ord_pos_of_mem_nonunits Q₂ hmem hg0
    omega

end Separate

section Main

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem exists_monic_of_isIntegral (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    {h : F} (hhO : h ∈ R.integers) (hh : IsIntegral (Algebra.adjoin L ({(x : F)} : Set F)) h) :
    ∃ p : Polynomial (Polynomial A), p.Monic ∧
      p.eval₂ (eval₂RingHom ((algebraMap L F).comp A.subtype) (x : F)) h = 0 := by
  refine exists_monic R x hx h ?_ ?_
  · intro V hVL hxV
    exact mem_valuationSubring_of_isIntegral V (coe_adjoin_mem V hVL hxV) hh
  · intro V hV
    rw [AlgebraicCurve.RegularProlongation.eq_integers_of_forall_mem_adjoin_iff A R x hx hfin
      hdeg V hV]
    exact hhO

theorem mem_of_sub_algebraMap_mem_nonunits (P : Place L F) {h : F} {b : L}
    (hb : h - algebraMap L F b ∈ P.toValuationSubring.nonunits) : h ∈ P.toValuationSubring := by
  have := add_mem (ValuationSubring.nonunits_subset hb) (P.algebraMap_mem' b)
  simpa using this

theorem mem_of_sub_mem_nonunits (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (P : Place L F) {a₀ : A}
    (ha₀ : (x : F) - algebraMap L F a₀ ∈ P.toValuationSubring.nonunits)
    {h : F} (hhO : h ∈ R.integers) (hh : IsIntegral (Algebra.adjoin L ({(x : F)} : Set F)) h)
    {b : L} (hb : h - algebraMap L F b ∈ P.toValuationSubring.nonunits) : b ∈ A := by
  obtain ⟨p, hpm, hp⟩ := exists_monic_of_isIntegral R x hx hfin hdeg hhO hh
  set OP := P.toValuationSubring with hOP
  have hxP : (x : F) ∈ OP := mem_of_sub_algebraMap_mem_nonunits P ha₀
  have hhP : h ∈ OP := mem_of_sub_algebraMap_mem_nonunits P hb

  set ψ : A[X] →+* OP := eval₂RingHom ((algebraMap L OP).comp A.subtype) ⟨x, hxP⟩ with hψ
  have hψF : (algebraMap OP F).comp ψ = eval₂RingHom ((algebraMap L F).comp A.subtype) (x : F) := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · simp only [hψ, RingHom.comp_apply, coe_eval₂RingHom, eval₂_C]
      rfl
    · simp only [hψ, RingHom.comp_apply, coe_eval₂RingHom, eval₂_X]
      rfl
  have hp' : p.eval₂ ψ ⟨h, hhP⟩ = 0 := by
    apply IsFractionRing.injective OP F
    rw [Polynomial.hom_eval₂, hψF, map_zero]
    exact hp

  have hπx : IsLocalRing.residue OP ⟨x, hxP⟩ = algebraMap L (ResidueField OP) (a₀ : L) := by
    have hm : (⟨x, hxP⟩ : OP) - algebraMap L OP (a₀ : L) ∈ maximalIdeal OP := by
      rw [← ValuationSubring.coe_mem_nonunits_iff]; exact ha₀
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at hm
    rw [hm]
    exact (IsScalarTower.algebraMap_apply L OP (ResidueField OP) _).symm
  have hπh : IsLocalRing.residue OP ⟨h, hhP⟩ = algebraMap L (ResidueField OP) b := by
    have hm : (⟨h, hhP⟩ : OP) - algebraMap L OP b ∈ maximalIdeal OP := by
      rw [← ValuationSubring.coe_mem_nonunits_iff]; exact hb
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at hm
    rw [hm]
    exact (IsScalarTower.algebraMap_apply L OP (ResidueField OP) _).symm
  have hcomp : (IsLocalRing.residue OP).comp ψ =
      ((algebraMap L (ResidueField OP)).comp A.subtype).comp (evalRingHom a₀) := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · simp only [hψ, RingHom.comp_apply, coe_eval₂RingHom, eval₂_C, coe_evalRingHom, eval_C]
      exact (IsScalarTower.algebraMap_apply L OP (ResidueField OP) _).symm
    · simp only [hψ, RingHom.comp_apply, coe_eval₂RingHom, eval₂_X, coe_evalRingHom, eval_X]
      exact hπx
  have h2 := congrArg (IsLocalRing.residue OP) hp'
  rw [Polynomial.hom_eval₂, map_zero, hπh, hcomp, ← eval₂_map, ← Polynomial.hom_eval₂,
    map_eq_zero] at h2

  have hint : IsIntegral A b := by
    refine ⟨p.map (evalRingHom a₀), hpm.map _, ?_⟩
    rw [show algebraMap A L = A.subtype from RingHom.ext fun _ => rfl]
    exact h2
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← ha]
  exact a.2

theorem mem_nonunits_of_residue_eq_zero (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (P : Place L F) {a₀ : A}
    (ha₀ : (x : F) - algebraMap L F a₀ ∈ P.toValuationSubring.nonunits)
    {h : F} (hhO : h ∈ R.integers) (hh : IsIntegral (Algebra.adjoin L ({(x : F)} : Set F)) h)
    (hres : R.residue ⟨h, hhO⟩ = 0)
    {b : L} (hb : h - algebraMap L F b ∈ P.toValuationSubring.nonunits) : b ∈ A.nonunits := by
  rcases eq_or_ne h 0 with rfl | hh0
  · have hb0 : b = 0 := by
      by_contra hb0
      have := (ValuationSubring.mem_nonunits_iff _).mp hb
      rw [zero_sub, Valuation.map_neg, valuation_algebraMap_eq_one P hb0] at this
      exact lt_irrefl _ this
    rw [hb0]
    exact zero_mem _
  · obtain ⟨c, hcO, hcres⟩ := R.exists_smul_mem h hh0
    have hc0 : c ≠ 0 := R.smul_const_ne_zero hcO hcres
    have hcu : IsIntegral (Algebra.adjoin L ({(x : F)} : Set F)) (c • h) := by
      rw [Algebra.smul_def]
      exact (isIntegral_const (x : F) c).mul hh
    have hsub : c • h - algebraMap L F (c * b) ∈ P.toValuationSubring.nonunits := by
      rw [Algebra.smul_def, map_mul, ← mul_sub, ValuationSubring.mem_nonunits_iff, map_mul,
        valuation_algebraMap_eq_one P hc0, one_mul]
      exact (ValuationSubring.mem_nonunits_iff _).mp hb
    have hcbA : c * b ∈ A := mem_of_sub_mem_nonunits R x hx hfin hdeg P ha₀ hcO hcu hsub
    have hcinvA : c⁻¹ ∈ A := by
      refine (A.mem_or_inv_mem c).resolve_left fun hcA => hcres ?_
      have heq : (⟨c • h, hcO⟩ : R.integers) = constHom R ⟨c, hcA⟩ * ⟨h, hhO⟩ :=
        Subtype.ext (Algebra.smul_def c h)
      rw [heq, map_mul, hres, mul_zero]
    have key : R.residue (constHom R ⟨c⁻¹, hcinvA⟩) = 0 := by
      have heq : (⟨h, hhO⟩ : R.integers) = constHom R ⟨c⁻¹, hcinvA⟩ * ⟨c • h, hcO⟩ := by
        apply Subtype.ext
        show h = algebraMap L F c⁻¹ * (c • h)
        rw [Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
      have := hres
      rw [heq, map_mul] at this
      exact (mul_eq_zero.mp this).resolve_right hcres
    have hbA : b ∈ A := by
      have : b = c⁻¹ * (c * b) := by rw [← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
      rw [this]
      exact mul_mem hcinvA hcbA
    refine ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr ⟨hbA, ?_⟩
    have hcm : (⟨c⁻¹, hcinvA⟩ : A) ∈ maximalIdeal A := by
      rw [← IsLocalRing.residue_eq_zero_iff]
      apply (algebraMap (ResidueField A) Fbar).injective
      rw [map_zero, ← residue_constHom R]
      exact key
    have heq : (⟨b, hbA⟩ : A) = ⟨c⁻¹, hcinvA⟩ * ⟨c * b, hcbA⟩ := by
      apply Subtype.ext
      show b = c⁻¹ * (c * b)
      rw [← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
    rw [heq]
    exact Ideal.mul_mem_right _ _ hcm

theorem exists_place [IsAlgClosed L] (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (P : Place L F) {a₀ : A}
    (ha₀ : (x : F) - algebraMap L F a₀ ∈ P.toValuationSubring.nonunits) :
    ∃ Q : Place (ResidueField A) Fbar,
      ∀ h : R.integers, IsIntegral (Algebra.adjoin L ({(x : F)} : Set F)) (h : F) →
        ∀ a : A, (h : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits →
          R.residue h - algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) ∈
            Q.toValuationSubring.nonunits := by
  classical
  have hxP : (x : F) ∈ P.toValuationSubring := mem_of_sub_algebraMap_mem_nonunits P ha₀

  set Sic : Subalgebra (Algebra.adjoin L ({(x : F)} : Set F)) F :=
    integralClosure (Algebra.adjoin L ({(x : F)} : Set F)) F with hSic
  set S : Subring F := Sic.toSubring ⊓ R.integers.toSubring with hSdef
  have hS_int : ∀ s : S, IsIntegral (Algebra.adjoin L ({(x : F)} : Set F)) (s : F) :=
    fun s => (Subring.mem_inf.mp s.2).1
  have hS_O : ∀ s : S, (s : F) ∈ R.integers := fun s => (Subring.mem_inf.mp s.2).2
  have hS_P : ∀ s : S, (s : F) ∈ P.toValuationSubring := fun s =>
    P.mem_toValuationSubring_of_isIntegral_adjoin hxP (hS_int s)
  have hmkS : ∀ {h : F}, IsIntegral (Algebra.adjoin L ({(x : F)} : Set F)) h → h ∈ R.integers →
      h ∈ S :=
    fun hh hhO => Subring.mem_inf.mpr ⟨hh, hhO⟩
  have hconstS : ∀ a : A, algebraMap L F a ∈ S := fun a =>
    hmkS (isIntegral_const (x : F) (a : L)) ((R.algebraMap_mem_iff a).mpr a.2)
  have hxS : (x : F) ∈ S := hmkS (isIntegral_self (x : F)) x.2
  let toO : S →+* R.integers := S.subtype.codRestrict R.integers hS_O
  let toP : S →+* P.toValuationSubring := S.subtype.codRestrict P.toValuationSubring hS_P
  let resS : S →+* Fbar := R.residue.comp toO
  have hresS : ∀ s : S, resS s = R.residue (toO s) := fun _ => rfl

  set I : Ideal S := (maximalIdeal P.toValuationSubring).comap toP with hI
  have hmemI : ∀ s : S, s ∈ I ↔ (s : F) ∈ P.toValuationSubring.nonunits := by
    intro s
    rw [hI, Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]
    exact Iff.rfl

  set B : Subring Fbar := resS.range with hB
  set resS' : S →+* B := resS.rangeRestrict with hresS'
  have hsurj : Function.Surjective resS' := RingHom.rangeRestrict_surjective resS
  have hcoe_resS' : ∀ s : S, ((resS' s : B) : Fbar) = resS s := fun _ => rfl
  set N : Ideal B := I.map resS' with hN

  have hNtop : N ≠ ⊤ := by
    intro htop
    have h1 : (1 : B) ∈ N := htop ▸ Submodule.mem_top
    obtain ⟨s, hsI, hs1⟩ := (Ideal.mem_map_iff_of_surjective resS' hsurj).mp h1
    have hs1' : resS s = 1 := by
      have := congrArg (fun b : B => (b : Fbar)) hs1
      simpa [hcoe_resS'] using this
    have hsO1 : (s : F) - 1 ∈ R.integers := sub_mem (hS_O s) (one_mem _)
    have hres0 : R.residue ⟨(s : F) - 1, hsO1⟩ = 0 := by
      have : (⟨(s : F) - 1, hsO1⟩ : R.integers) = toO s - 1 := Subtype.ext rfl
      rw [this, map_sub, map_one, sub_eq_zero, ← hresS]
      exact hs1'
    have hint : IsIntegral (Algebra.adjoin L ({(x : F)} : Set F)) ((s : F) - 1) :=
      (hS_int s).sub isIntegral_one
    have hnu : (s : F) - 1 - algebraMap L F (-1) ∈ P.toValuationSubring.nonunits := by
      rw [map_neg, map_one, sub_neg_eq_add, sub_add_cancel]
      exact (hmemI s).mp hsI
    have := mem_nonunits_of_residue_eq_zero R x hx hfin hdeg P ha₀ hsO1 hint hres0 hnu
    rw [ValuationSubring.mem_nonunits_iff, Valuation.map_neg, map_one] at this
    exact lt_irrefl _ this

  obtain ⟨V, hBV, hNV⟩ := Ideal.image_subset_nonunits_valuationSubring N hNtop
  have hkB : ∀ κ : ResidueField A, algebraMap (ResidueField A) Fbar κ ∈ B := by
    intro κ
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective κ
    refine ⟨⟨algebraMap L F a, hconstS a⟩, ?_⟩
    rw [hresS, show toO ⟨algebraMap L F a, hconstS a⟩ = constHom R a from Subtype.ext rfl,
      residue_constHom]
  have hkV : ∀ κ : ResidueField A, algebraMap (ResidueField A) Fbar κ ∈ V :=
    fun κ => hBV (hkB κ)
  have hIV : ∀ s : S, s ∈ I → resS s ∈ V.nonunits := fun s hsI =>
    hNV ⟨resS' s, Ideal.mem_map_of_mem resS' hsI, rfl⟩

  have hres_sub : ∀ (h : R.integers) (hh : IsIntegral (Algebra.adjoin L ({(x : F)} : Set F)) (h : F))
      (a : A), resS ⟨(h : F) - algebraMap L F a, sub_mem (hmkS hh h.2) (hconstS a)⟩ =
        R.residue h - algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) := by
    intro h hh a
    rw [hresS, show toO ⟨(h : F) - algebraMap L F a, sub_mem (hmkS hh h.2) (hconstS a)⟩ =
      h - constHom R a from Subtype.ext rfl, map_sub, residue_constHom]

  have hVtop : V ≠ ⊤ := by
    refine ne_top_of_mem_nonunits (y := R.residue x - algebraMap (ResidueField A) Fbar
      (IsLocalRing.residue A a₀)) ?_ ?_
    · rw [← hres_sub x (isIntegral_self (x : F)) a₀]
      exact hIV _ ((hmemI _).mpr ha₀)
    · intro h0
      apply hx
      rw [sub_eq_zero] at h0
      rw [h0]
      exact isAlgebraic_algebraMap _

  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : FiniteDimensional
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar :=
    Module.finite_of_finrank_pos hfin
  obtain ⟨Q, hQ⟩ := exists_place_eq hx V hkV hVtop
  refine ⟨Q, fun h hh a ha => ?_⟩
  rw [hQ, ← hres_sub h hh a]
  exact hIV _ ((hmemI _).mpr ha)

theorem main [IsAlgClosed L] [IsCurveOver L F] [IsCurveOver (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hchart : ∀ h : Fbar, IsIntegral (Algebra.adjoin (ResidueField A) {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h)
    (P : Place L F) (hP : ∃ a : A, (x : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits) :
    ∃! Q : Place (ResidueField A) Fbar,
      ∀ h : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (h : F) →
        ∀ a : A, (h : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits →
          R.residue h - algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) ∈
            Q.toValuationSubring.nonunits := by
  obtain ⟨a₀, ha₀⟩ := hP
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : FiniteDimensional
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar :=
    Module.finite_of_finrank_pos hfin
  obtain ⟨Q, hQ⟩ := exists_place R x hx hfin hdeg P ha₀
  refine ⟨Q, hQ, fun Q' hQ' => ?_⟩
  by_contra hne

  have h₁ := hQ' x (isIntegral_self (x : F)) a₀ ha₀
  have h₂ := hQ x (isIntegral_self (x : F)) a₀ ha₀

  obtain ⟨g, hg_int, hg₁, hg₂⟩ :=
    exists_separating hx Q' Q hne (IsLocalRing.residue A a₀) h₁ h₂
  obtain ⟨f₀, hf₀int, hf₀res⟩ := hchart g hg_int
  have hxP : (x : F) ∈ P.toValuationSubring := mem_of_sub_algebraMap_mem_nonunits P ha₀
  have hf₀P : (f₀ : F) ∈ P.toValuationSubring :=
    P.mem_toValuationSubring_of_isIntegral_adjoin hxP hf₀int

  obtain ⟨b, hb⟩ := exists_sub_algebraMap_mem_nonunits P hf₀P
  have hbA : b ∈ A := mem_of_sub_mem_nonunits R x hx hfin hdeg P ha₀ f₀.2 hf₀int hb
  have hb₁ := hQ' f₀ hf₀int ⟨b, hbA⟩ hb
  have hb₂ := hQ f₀ hf₀int ⟨b, hbA⟩ hb
  rw [hf₀res] at hb₁ hb₂

  set β : Fbar := algebraMap (ResidueField A) Fbar (IsLocalRing.residue A ⟨b, hbA⟩) with hβ
  have hβQ' : β ∈ Q'.toValuationSubring.nonunits := by
    have := sub_mem hg₁ hb₁
    simpa using this
  have hβ0 : β = 0 := by
    by_contra hβ0
    have hr0 : IsLocalRing.residue A ⟨b, hbA⟩ ≠ 0 := by
      intro h0
      apply hβ0
      rw [hβ, h0, map_zero]
    have := (ValuationSubring.mem_nonunits_iff _).mp hβQ'
    rw [hβ, valuation_algebraMap_eq_one Q' hr0] at this
    exact lt_irrefl _ this

  rw [hβ0, sub_zero] at hb₂
  exact hg₂ hb₂

end Main

end AlgebraicCurve.RegularProlongation.ExUniqPlace
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_existsUnique_place_forall_residue_sub_mem_nonunits.AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_existsUnique_place_forall_residue_sub_mem_nonunits.AlgebraicCurve.RegularProlongation P2MW.S_AlgebraicCurve_RegularProlongation_existsUnique_place_forall_residue_sub_mem_nonunits.AlgebraicCurve.RegularProlongation.ExUniqPlace"
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_existsUnique_place_forall_residue_sub_mem_nonunits.AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_existsUnique_place_forall_residue_sub_mem_nonunits.AlgebraicCurve.RegularProlongation"
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_existsUnique_place_forall_residue_sub_mem_nonunits.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_existsUnique_place_forall_residue_sub_mem_nonunits.AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_existsUnique_place_forall_residue_sub_mem_nonunits.AlgebraicCurve.RegularProlongation P2MW.S_AlgebraicCurve_RegularProlongation_existsUnique_place_forall_residue_sub_mem_nonunits.AlgebraicCurve.RegularProlongation.ExUniqPlace"

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_RegularProlongation_existsUnique_place_forall_residue_sub_mem_nonunits.AlgebraicCurve in

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] [IsCurveOver L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    [IsCurveOver (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hchart : ∀ h : Fbar, IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h)
    (P : Place L F) (hP : ∃ a : A, (x : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits) :
    ∃! Q : Place (IsLocalRing.ResidueField A) Fbar,
      ∀ h : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (h : F) →
        ∀ a : A, (h : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits →
          R.residue h - algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A a) ∈
            Q.toValuationSubring.nonunits :=
  AlgebraicCurve.RegularProlongation.ExUniqPlace.main R x hx hfin hdeg hchart P hP

end S_AlgebraicCurve_RegularProlongation_existsUnique_place_forall_residue_sub_mem_nonunits
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_existsUnique_place_forall_residue_sub_mem_nonunits (solution)
