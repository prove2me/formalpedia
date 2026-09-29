-- Prove2me | solution 1 for AlgebraicCurve.IsCurveOver.exists_separating_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/f6204aaa-e070-50ce-9afd-cc4c321cff10

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

set_option autoImplicit false

open KaehlerDifferential Algebra IntermediateField

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver IsCurveOver.finrank_kaehler"
p2m_open "AlgebraicCurve"

namespace IsCurveOver
p2m_export "AlgebraicCurve.IsCurveOver" "finrank_kaehler instNontrivialKaehler"
p2m_open "AlgebraicCurve.IsCurveOver"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem not_isSeparable [IsCurveOver K F] : ¬ Algebra.IsSeparable K F := by
  intro hsep
  haveI : Algebra.FormallyUnramified K F := Algebra.FormallyUnramified.of_isSeparable K F
  exact false_of_nontrivial_of_subsingleton Ω[F⁄K]

theorem not_isAlgebraic [PerfectField K] [IsCurveOver K F] :
    ¬ Algebra.IsAlgebraic K F := by
  intro halg
  exact not_isSeparable (K := K) (F := F) Algebra.IsAlgebraic.isSeparable_of_perfectField

scoped instance instTranscendental [PerfectField K] [IsCurveOver K F] :
    Algebra.Transcendental K F :=
  Algebra.transcendental_iff_not_isAlgebraic.mpr not_isAlgebraic

theorem exists_transcendental [PerfectField K] [IsCurveOver K F] :
    ∃ t : F, Transcendental K t :=
  Algebra.Transcendental.transcendental

theorem trdeg_pos [PerfectField K] [IsCurveOver K F] :
    0 < Algebra.trdeg K F :=
  _root_.trdeg_pos K F

theorem trdeg_ne_zero [PerfectField K] [IsCurveOver K F] :
    Algebra.trdeg K F ≠ 0 :=
  trdeg_pos.ne'

theorem one_le_trdeg [PerfectField K] [IsCurveOver K F] :
    1 ≤ Algebra.trdeg K F :=
  Cardinal.one_le_iff_pos.mpr trdeg_pos

end IsCurveOver
p2m_reactivate "P2MW.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.AlgebraicCurve.IsCurveOver"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace IsCurveOver p2m_export "AlgebraicCurve.IsCurveOver" "finrank_kaehler instNontrivialKaehler" end IsCurveOver
p2m_open_scoped "AlgebraicCurve.IsCurveOver" in

theorem IsCurveOver.trdeg_eq_one [PerfectField K] [IsCurveOver K F]
    (htrdeg : Algebra.trdeg K F ≤ 1) :
    Algebra.trdeg K F = 1 :=
  le_antisymm htrdeg IsCurveOver.one_le_trdeg

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.AlgebraicCurve.IsCurveOver P2MW.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.AlgebraicCurve"

set_option autoImplicit false

noncomputable section

p2m_open "KaehlerDifferential IntermediateField TensorProduct Algebra.TensorProduct Module"
open scoped IntermediateField.algebraAdjoinAdjoin

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver IsCurveOver.finrank_kaehler"
p2m_open "AlgebraicCurve"

universe u₁ u₂

variable {K : Type u₁} {F : Type u₂} [Field K] [Field F] [Algebra K F]

variable {ι : Type*} {v : ι → F}

def kaehlerAdjoinBasis (hv : AlgebraicIndependent K v) :
    Basis ι (IntermediateField.adjoin K (Set.range v))
      Ω[(IntermediateField.adjoin K (Set.range v))⁄K] := by

  let Kv : IntermediateField K F := IntermediateField.adjoin K (Set.range v)

  letI : Algebra (MvPolynomial ι K) Kv :=
    ((algebraMap (Algebra.adjoin K (Set.range v)) Kv).comp
      (hv.aevalEquiv : MvPolynomial ι K →+* Algebra.adjoin K (Set.range v))).toAlgebra

  haveI : IsScalarTower K (MvPolynomial ι K) Kv :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show algebraMap K Kv a
        = algebraMap (Algebra.adjoin K (Set.range v)) Kv (hv.aevalEquiv (algebraMap K _ a))
      rw [AlgEquiv.commutes]; rfl

  haveI : IsFractionRing (MvPolynomial ι K) Kv :=
    IsFractionRing.of_ringEquiv_left hv.aevalEquiv.toRingEquiv (fun _ => rfl)

  haveI : Algebra.FormallyEtale (MvPolynomial ι K) Kv :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (MvPolynomial ι K))

  exact ((KaehlerDifferential.mvPolynomialBasis K ι).baseChange Kv).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (MvPolynomial ι K) Kv)

def kaehlerOfSeparatingTranscendentalBasis (hv : AlgebraicIndependent K v)
    [Algebra.IsSeparable (IntermediateField.adjoin K (Set.range v)) F] : Basis ι F Ω[F⁄K] :=
  haveI : Algebra.FormallyEtale (IntermediateField.adjoin K (Set.range v)) F :=
    Algebra.FormallyEtale.of_isSeparable _ _
  ((kaehlerAdjoinBasis hv).baseChange F).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K
      (IntermediateField.adjoin K (Set.range v)) F)

theorem finrank_kaehler_eq_card_of_separating {s : Finset F}
    (hs : AlgebraicIndependent K ((↑) : s → F))
    [Algebra.IsSeparable (IntermediateField.adjoin K (Set.range ((↑) : s → F))) F] :
    Module.finrank F Ω[F⁄K] = s.card := by
  rw [Module.finrank_eq_card_basis (kaehlerOfSeparatingTranscendentalBasis hs),
    Fintype.card_coe]

theorem finrank_kaehler_eq_card_of_separating' {s : Finset F}
    (hs : AlgebraicIndependent K ((↑) : s → F))
    [hsep : Algebra.IsSeparable (IntermediateField.adjoin K (s : Set F)) F] :
    Module.finrank F Ω[F⁄K] = s.card := by

  have heq : IntermediateField.adjoin K (s : Set F)
      = IntermediateField.adjoin K (Set.range ((↑) : s → F)) := by
    rw [Subtype.range_coe]
  let e : (IntermediateField.adjoin K (s : Set F)) ≃ₐ[K]
      (IntermediateField.adjoin K (Set.range ((↑) : s → F))) :=
    IntermediateField.equivOfEq heq

  haveI : Algebra.IsSeparable (IntermediateField.adjoin K (Set.range ((↑) : s → F))) F :=
    Algebra.IsSeparable.of_equiv_equiv e.toRingEquiv (RingEquiv.refl F)
      (RingHom.ext fun x => rfl)
  exact finrank_kaehler_eq_card_of_separating hs

namespace IsCurveOver
p2m_export "AlgebraicCurve.IsCurveOver" "finrank_kaehler instNontrivialKaehler"
p2m_open "AlgebraicCurve.IsCurveOver"

theorem trdeg_le_one [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    Algebra.trdeg K F ≤ 1 := by
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K F

  haveI := hsep
  have hcard : s.card = 1 := by
    rw [← finrank_kaehler_eq_card_of_separating' hs.1, IsCurveOver.finrank_kaehler]

  have htr := hs.cardinalMk_eq_trdeg
  rw [Cardinal.mk_coe_finset, hcard, Nat.cast_one] at htr
  exact htr.symm.le

theorem trdeg_eq_one_of_perfectField [PerfectField K] [Algebra.EssFiniteType K F]
    [IsCurveOver K F] : Algebra.trdeg K F = 1 :=
  IsCurveOver.trdeg_eq_one trdeg_le_one

end IsCurveOver
p2m_reactivate "P2MW.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.AlgebraicCurve.IsCurveOver P2MW.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.AlgebraicCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.AlgebraicCurve.IsCurveOver P2MW.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.AlgebraicCurve"

set_option autoImplicit false

p2m_open "IntermediateField Algebra TensorProduct.Algebra Algebra.TensorProduct.Algebra"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver IsCurveOver.finrank_kaehler"
p2m_open "AlgebraicCurve"

universe u₁ u₂

variable {K : Type u₁} {F : Type u₂} [Field K] [Field F] [Algebra K F]

namespace IsCurveOver
p2m_export "AlgebraicCurve.IsCurveOver" "finrank_kaehler instNontrivialKaehler"
p2m_open "AlgebraicCurve.IsCurveOver"

theorem exists_separating_transcendental_s6 [PerfectField K] [Algebra.EssFiniteType K F]
    [IsCurveOver K F] :
    ∃ t : F, Transcendental K t ∧ FiniteDimensional K⟮t⟯ F ∧ Algebra.IsSeparable K⟮t⟯ F := by

  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K F

  have hcard : s.card = 1 := by
    have htr := hs.cardinalMk_eq_trdeg
    rw [Cardinal.mk_coe_finset, IsCurveOver.trdeg_eq_one_of_perfectField] at htr
    exact_mod_cast htr

  obtain ⟨t, rfl⟩ := Finset.card_eq_one.mp hcard

  have htr : Transcendental K t := by
    have h1 := hs.1
    rw [show ((↑) : (↑({t} : Finset F)) → F) = fun _ => t from
      funext fun x => (Finset.mem_singleton.mp x.2).symm ▸ rfl] at h1
    exact (algebraicIndependent_unique_type_iff (ι := (↑({t} : Finset F)))).mp h1

  have heq : IntermediateField.adjoin K (↑({t} : Finset F) : Set F) = K⟮t⟯ := by
    rw [Finset.coe_singleton]
  haveI hsep' : Algebra.IsSeparable K⟮t⟯ F :=
    Algebra.IsSeparable.of_equiv_equiv
      (IntermediateField.equivOfEq heq).toRingEquiv (RingEquiv.refl F)
      (RingHom.ext fun _ => rfl)

  haveI : Algebra.EssFiniteType K⟮t⟯ F := Algebra.EssFiniteType.of_comp K K⟮t⟯ F
  exact ⟨t, htr, Algebra.finite_of_essFiniteType_of_isAlgebraic, hsep'⟩

end IsCurveOver
p2m_reactivate "P2MW.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.AlgebraicCurve.IsCurveOver P2MW.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.AlgebraicCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.AlgebraicCurve.IsCurveOver P2MW.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.AlgebraicCurve"

open IntermediateField _root_.Algebra _root_.TensorProduct.Algebra _root_.Algebra.TensorProduct.Algebra in
theorem _root_.P2MW.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.solution {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F] :
    ∃ t : F, Transcendental K t ∧ FiniteDimensional K⟮t⟯ F ∧ Algebra.IsSeparable K⟮t⟯ F :=
  AlgebraicCurve.IsCurveOver.exists_separating_transcendental_s6

end
p2m_reactivate "P2MW.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.AlgebraicCurve.IsCurveOver P2MW.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.AlgebraicCurve"

end
end S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
end P2MW
export P2MW.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental (solution)
