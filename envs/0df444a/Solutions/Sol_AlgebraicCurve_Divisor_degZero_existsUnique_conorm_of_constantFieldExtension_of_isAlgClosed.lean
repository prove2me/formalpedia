-- Prove2me | solution 1 for AlgebraicCurve.Divisor.degZero.existsUnique_conorm_of_constantFieldExtension_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/010186d8-c089-527b-85e9-75faf15351be

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_degZero_existsUnique_conorm_of_constantFieldExtension_of_isAlgClosed

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Divisor_degZero_existsUnique_conorm_of_constantFieldExtension_of_isAlgClosed.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Divisor Divisor.degree Divisor.degree_single Divisor.degZero Divisor.principal HasPrincipalDivisors Pic Pic0 Pic0.mk HasPrincipalDivisors.exists_divisor IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed Place.exists_comap_algebraMap_eq_of_constantFieldExtension Place.exists_toValuationSubring_eq_comap_ringHom"
namespace HEXkit
p2m_open "AlgebraicCurve"

section Transfer

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F']
    [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']

theorem ord_eq_zero_of_mem_of_inv_mem {k L : Type*} [Field k] [Field L] [Algebra k L]
    (w : Place k L) {z : L} (hz : z ∈ w.toValuationSubring)
    (hzi : z⁻¹ ∈ w.toValuationSubring) : w.ord z = 0 := by
  rcases eq_or_ne z 0 with rfl | hz0
  · exact w.ord_zero
  · let u : w.toValuationSubringˣ :=
      ⟨⟨z, hz⟩, ⟨z⁻¹, hzi⟩, Subtype.ext (mul_inv_cancel₀ hz0), Subtype.ext (inv_mul_cancel₀ hz0)⟩
    exact w.ord_coe_unit u

theorem ord_algebraMap_base {k L : Type*} [Field k] [Field L] [Algebra k L]
    (w : Place k L) (a : k) : w.ord (algebraMap k L a) = 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [map_zero]; exact w.ord_zero
  · refine ord_eq_zero_of_mem_of_inv_mem w (w.algebraMap_mem' a) ?_
    rw [← map_inv₀]
    exact w.algebraMap_mem' _

theorem degree_eq_zero_of_forall_eq_ord {k L : Type*} [Field k] [Field L] [Algebra k L]
    [HasPrincipalDivisors k L] {f : L} (hf : f ≠ 0) {D : Divisor k L}
    (hD : ∀ v, D v = v.ord f) : Divisor.degree D = 0 := by
  obtain ⟨E, hE, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := k) f hf
  have : D = E := Finsupp.ext fun v => by rw [hD, hE]
  rw [this]
  exact hdeg

theorem mk_zsmul' {k L : Type*} [Field k] [Field L] [Algebra k L] (n : ℤ)
    (D : Divisor.degZero (K := k) (F := L)) : Pic0.mk (n • D) = n • Pic0.mk D :=
  QuotientAddGroup.mk_zsmul _ D n

theorem mk_eq_zero_iff' {k L : Type*} [Field k] [Field L] [Algebra k L]
    (D : Divisor.degZero (K := k) (F := L)) :
    Pic0.mk D = 0 ↔ (D : Divisor k L) ∈ (Divisor.principal : AddSubgroup (Divisor k L)) := by
  unfold Pic0.mk
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]

theorem mk_eq_mk_iff' {k L : Type*} [Field k] [Field L] [Algebra k L]
    (D E : Divisor.degZero (K := k) (F := L)) :
    Pic0.mk D = Pic0.mk E ↔
      -(D : Divisor k L) + E ∈ (Divisor.principal : AddSubgroup (Divisor k L)) := by
  unfold Pic0.mk
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  exact Iff.rfl

theorem natCast_mul_apply_eq_of_zsmul_mem_principal {k L : Type*} [Field k] [Field L]
    [Algebra k L] {n : ℕ} {D : Divisor.degZero (K := k) (F := L)}
    (h : ((n : ℤ) • D : Divisor.degZero (K := k) (F := L)) ∈
      (Divisor.principal : AddSubgroup (Divisor k L)).addSubgroupOf Divisor.degZero) :
    ∃ g : L, g ≠ 0 ∧ ∀ v : Place k L, (n : ℤ) * (D : Divisor k L) v = v.ord g := by
  rw [AddSubgroup.mem_addSubgroupOf] at h
  obtain ⟨g, hg, hDg⟩ := h
  refine ⟨g, hg, fun v => ?_⟩
  rw [← hDg v, AddSubgroupClass.coe_zsmul, Finsupp.smul_apply, smul_eq_mul]

section Lift

variable [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
  (hfg : ∃ x : F, Transcendental K x ∧
    FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
  (hfg' : ∃ x : F', Transcendental K' x ∧
    FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
  (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)

noncomputable def liftPlace (P : Place K F) : Place K' F' :=
  Classical.choose
    (AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension
      K F K' F' hfg hfg' hgen P)

theorem liftPlace_spec (P : Place K F) :
    (liftPlace hfg hfg' hgen P).toValuationSubring.comap (algebraMap F F') =
        P.toValuationSubring ∧
      (∀ f : F, (liftPlace hfg hfg' hgen P).ord (algebraMap F F' f) = P.ord f) ∧
      ∀ Q' : Place K' F', Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring →
        Q' = liftPlace hfg hfg' hgen P :=
  Classical.choose_spec
    (AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension
      K F K' F' hfg hfg' hgen P)

theorem liftPlace_comap (P : Place K F) :
    (liftPlace hfg hfg' hgen P).toValuationSubring.comap (algebraMap F F') =
      P.toValuationSubring :=
  (liftPlace_spec hfg hfg' hgen P).1

theorem ord_liftPlace (P : Place K F) (f : F) :
    (liftPlace hfg hfg' hgen P).ord (algebraMap F F' f) = P.ord f :=
  (liftPlace_spec hfg hfg' hgen P).2.1 f

theorem eq_liftPlace {P : Place K F} {Q' : Place K' F'}
    (h : Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring) :
    Q' = liftPlace hfg hfg' hgen P :=
  (liftPlace_spec hfg hfg' hgen P).2.2 Q' h

theorem liftPlace_injective :
    Function.Injective (liftPlace (K := K) (F := F) (K' := K') (F' := F') hfg hfg' hgen) := by
  intro P Q h
  apply Place.ext
  rw [← liftPlace_comap hfg hfg' hgen P, h, liftPlace_comap]

theorem ord_algebraMap_eq_zero_of_forall_ne (w : Place K' F')
    (hw : ∀ P : Place K F, w ≠ liftPlace hfg hfg' hgen P) (f : F) :
    w.ord (algebraMap F F' f) = 0 := by
  by_contra hne
  obtain ⟨x, hx, hfin⟩ := id hfg
  haveI := hfin
  have hwK : ∀ a : K, algebraMap F F' (algebraMap K F a) ∈ w.toValuationSubring := fun a => by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K K' F']
    exact w.algebraMap_mem' _
  have hwx : ∃ y : F, algebraMap F F' y ∉ w.toValuationSubring := by
    by_contra hall
    push Not at hall
    exact hne (ord_eq_zero_of_mem_of_inv_mem w (hall f) (by rw [← map_inv₀]; exact hall _))
  obtain ⟨v, hv⟩ := AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_ringHom
    (K := K) x (algebraMap F F') w.toValuationSubring hwK hwx
  exact hw v (eq_liftPlace hfg hfg' hgen hv.symm)

noncomputable def conormDiv : Divisor K F →+ Divisor K' F' :=
  Finsupp.mapDomain.addMonoidHom (liftPlace hfg hfg' hgen)

theorem conormDiv_apply_liftPlace (D : Divisor K F) (P : Place K F) :
    conormDiv hfg hfg' hgen D (liftPlace hfg hfg' hgen P) = D P :=
  Finsupp.mapDomain_apply (liftPlace_injective hfg hfg' hgen) D P

theorem conormDiv_apply_of_forall_ne (D : Divisor K F) (w : Place K' F')
    (hw : ∀ P : Place K F, w ≠ liftPlace hfg hfg' hgen P) : conormDiv hfg hfg' hgen D w = 0 :=
  Finsupp.mapDomain_notin_range D w (by rintro ⟨P, rfl⟩; exact hw P rfl)

theorem conormDiv_single (P : Place K F) (m : ℤ) :
    conormDiv hfg hfg' hgen (Finsupp.single P m) = Finsupp.single (liftPlace hfg hfg' hgen P) m :=
  Finsupp.mapDomain_single

theorem conormDiv_mem_principal {D : Divisor K F}
    (hD : D ∈ (Divisor.principal : AddSubgroup (Divisor K F))) :
    conormDiv hfg hfg' hgen D ∈ (Divisor.principal : AddSubgroup (Divisor K' F')) := by
  obtain ⟨f, hf, hDf⟩ := hD
  refine ⟨algebraMap F F' f, (map_ne_zero _).mpr hf, fun w => ?_⟩
  by_cases hw : ∃ P, w = liftPlace hfg hfg' hgen P
  · obtain ⟨P, rfl⟩ := hw
    rw [conormDiv_apply_liftPlace, ord_liftPlace, hDf]
  · push Not at hw
    rw [conormDiv_apply_of_forall_ne hfg hfg' hgen D w hw,
      ord_algebraMap_eq_zero_of_forall_ne hfg hfg' hgen w hw]

variable [IsAlgClosed K'] [IsCurveOver K' F']

theorem degree_conormDiv (D : Divisor K F) :
    Divisor.degree (conormDiv hfg hfg' hgen D) = Divisor.degree D := by
  refine Finsupp.induction D (by simp) fun P m D _ _ ih => ?_
  rw [map_add, map_add, map_add, ih, conormDiv_single, Divisor.degree_single,
    Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed,
    IsCurveOver.deg_eq_one_of_isAlgClosed]

noncomputable def conormDegZero :
    Divisor.degZero (K := K) (F := F) →+ Divisor.degZero (K := K') (F := F') :=
  ((conormDiv hfg hfg' hgen).domRestrict (Divisor.degZero (K := K) (F := F))).codRestrict _
    (fun D => show Divisor.degree (conormDiv hfg hfg' hgen (D : Divisor K F)) = 0 by
      rw [degree_conormDiv]; exact D.2)

theorem coe_conormDegZero (D : Divisor.degZero (K := K) (F := F)) :
    (conormDegZero hfg hfg' hgen D : Divisor K' F') = conormDiv hfg hfg' hgen D := rfl

end Lift

end Transfer

end AlgebraicCurve.HEXkit

open AlgebraicCurve.HEXkit in

theorem solution
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (D : Divisor.degZero (K := K) (F := F)) :
    ∃! D' : Divisor.degZero (K := K') (F := F'),
      (∀ (v' : Place K' F') (v : Place K F),
        v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring →
          (D' : Divisor K' F') v' = (D : Divisor K F) v) ∧
      (∀ v' : Place K' F',
        (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
          (D' : Divisor K' F') v' = 0) := by
  refine ⟨conormDegZero hfg hfg' hgen D, ⟨fun v' v h => ?_, fun v' h => ?_⟩, ?_⟩
  · rw [coe_conormDegZero, eq_liftPlace hfg hfg' hgen h, conormDiv_apply_liftPlace]
  · rw [coe_conormDegZero]
    refine conormDiv_apply_of_forall_ne hfg hfg' hgen _ v' fun P hP => h P ?_
    rw [hP, liftPlace_comap]
  · rintro D' ⟨hover, hoff⟩
    apply Subtype.ext
    ext v'
    by_cases hv : ∃ P, v' = liftPlace hfg hfg' hgen P
    · obtain ⟨P, rfl⟩ := hv
      rw [coe_conormDegZero, conormDiv_apply_liftPlace]
      exact hover _ P (liftPlace_comap hfg hfg' hgen P)
    · push Not at hv
      rw [coe_conormDegZero, conormDiv_apply_of_forall_ne hfg hfg' hgen _ v' hv]
      exact hoff v' fun P hP => hv P (eq_liftPlace hfg hfg' hgen hP)

end S_AlgebraicCurve_Divisor_degZero_existsUnique_conorm_of_constantFieldExtension_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_degZero_existsUnique_conorm_of_constantFieldExtension_of_isAlgClosed (solution)
