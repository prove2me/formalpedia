-- Prove2me | solution 1 for AlgebraicCurve.weilKaehlerAgree_of_residueTheorem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/7dfa0548-d4eb-5cc5-8132-e03e8a616d9a

import Mathlib
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import Theorems.Thm_AlgebraicCurve_weilOfKaehler_mem_omegaSpace_of_residueTheorem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_weilKaehlerAgree_of_residueTheorem

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
p2m_open "IsDedekindDomain WithZero Module IsLocalRing Module.IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "weilOfKaehler weilOfKaehler_apply ResidueTheorem WeilKaehlerAgree HasCanonicalLocalResidueKStar kaehlerResidueTerm single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue HasSeparableResidue.trace_ne_zero Place.ordDifferential Place Divisor HasPrincipalDivisors HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply adeleBdd adeleSpace omegaSpace omegaSpace_vanishBdd weilOfKaehler_mem_omegaSpace_of_residueTheorem"
p2m_open "AlgebraicCurve"
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place
p2m_export "AlgebraicCurve.Place" "localResidue localResidue_simplePole differentialCoeff_ne_zero uniformizer ord_uniformizer uniformizer_ne_zero DCoordGenerates differentialCoeff ordDifferential ext ResidueField ord ord_mul ord_inv ord_unit_smul_zpow toValuationSubring adicValuation_eq_exp_neg_ord"
p2m_open "AlgebraicCurve.Place"
variable (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu; push_cast at h; rw [zpow_natCast]; exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]; exact Int.natCast_nonneg n
p2m_export "AlgebraicCurve.Place" "ord_nonneg_of_mem"
end Place

section SingleEval

variable [HasCanonicalLocalResidueKStar K F]

open scoped Classical in

theorem kaehlerResidueTerm_single_of_ne {ω : Ω[F⁄K]} {v : Place K F} {g : F}
    {w : Place K F} (hw : w ≠ v) :
    kaehlerResidueTerm ω (Pi.single v g) w = 0 := by
  unfold kaehlerResidueTerm
  rw [Pi.single_eq_of_ne hw, zero_mul, map_zero, map_zero]

variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
  [Nontrivial Ω[F⁄K]]

open scoped Classical in

theorem weilOfKaehler_single_s6 {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : Place K F) (g : F) :
    weilOfKaehler K F hω (adeleSingle v g)
      = Algebra.trace K v.ResidueField (v.localResidue (g * v.differentialCoeff ω)) := by
  rw [weilOfKaehler_apply, adeleSingle_coe]
  refine (finsum_eq_single _ v fun w hw => kaehlerResidueTerm_single_of_ne hw).trans ?_
  unfold kaehlerResidueTerm
  rw [Pi.single_eq_same]

end SingleEval

section SimplePoleProbe

variable [HasCanonicalLocalResidueKStar K F]

namespace Place
p2m_export "AlgebraicCurve.Place" "localResidue localResidue_simplePole differentialCoeff_ne_zero uniformizer ord_uniformizer uniformizer_ne_zero DCoordGenerates differentialCoeff ordDifferential ext ResidueField ord ord_mul ord_inv ord_unit_smul_zpow toValuationSubring adicValuation_eq_exp_neg_ord"
p2m_open "AlgebraicCurve.Place"

variable (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.localResidue_mul_uniformizer_inv (c : v.toValuationSubring) :
    v.localResidue ((c : F) * v.uniformizer⁻¹) = IsLocalRing.residue _ c := by
  have hmul : v.uniformizer * ((c : F) * v.uniformizer⁻¹) = (c : F) := by
    rw [mul_comm (c : F), ← mul_assoc, mul_inv_cancel₀ v.uniformizer_ne_zero, one_mul]
  have hmem : v.uniformizer * ((c : F) * v.uniformizer⁻¹) ∈ v.toValuationSubring := by
    rw [hmul]; exact c.2
  rw [v.localResidue_simplePole _ hmem]
  congr 1
  exact Subtype.ext hmul

p2m_export "AlgebraicCurve.Place" "localResidue_mul_uniformizer_inv"
end Place

variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
  [Nontrivial Ω[F⁄K]]

def simplePoleProbe {ω : Ω[F⁄K]} (_hω : ω ≠ 0) (v : Place K F)
    (c : v.toValuationSubring) : adeleSpace K F :=
  adeleSingle v ((c : F) * v.uniformizer⁻¹ * (v.differentialCoeff ω)⁻¹)

theorem weilOfKaehler_simplePoleProbe {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : Place K F)
    (c : v.toValuationSubring) :
    weilOfKaehler K F hω (simplePoleProbe hω v c)
      = Algebra.trace K v.ResidueField (IsLocalRing.residue _ c) := by
  unfold simplePoleProbe
  rw [weilOfKaehler_single_s6 hω,
    mul_assoc, inv_mul_cancel₀ (v.differentialCoeff_ne_zero hω), mul_one,
    v.localResidue_mul_uniformizer_inv]

open scoped Classical in

theorem simplePoleProbe_mem_adeleBdd {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : Place K F)
    (c : v.toValuationSubring) {D : Divisor K F} (hDv : canonicalDivisorOf hω v < D v) :
    (simplePoleProbe hω v c : Place K F → F) ∈ adeleBdd D := by
  unfold simplePoleProbe
  rw [adeleSingle_coe]
  refine single_mem_adeleBdd v _ D ?_
  rcases eq_or_ne (c : F) 0 with hc | hc
  · rw [hc, zero_mul, zero_mul, Valuation.map_zero]; exact zero_le'
  · set g : F := (c : F) * v.uniformizer⁻¹ * (v.differentialCoeff ω)⁻¹ with hg
    have hg0 : g ≠ 0 :=
      mul_ne_zero (mul_ne_zero hc (inv_ne_zero v.uniformizer_ne_zero))
        (inv_ne_zero (v.differentialCoeff_ne_zero hω))
    rw [v.adicValuation_eq_exp_neg_ord hg0, WithZero.exp_le_exp, neg_le]

    rw [hg, v.ord_mul (mul_ne_zero hc (inv_ne_zero v.uniformizer_ne_zero))
        (inv_ne_zero (v.differentialCoeff_ne_zero hω)),
      v.ord_mul hc (inv_ne_zero v.uniformizer_ne_zero),
      v.ord_inv, v.ord_uniformizer, v.ord_inv]
    have hcnn : 0 ≤ v.ord (c : F) := v.ord_nonneg_of_mem c.2
    rw [canonicalDivisorOf_apply hω v, Place.ordDifferential] at hDv
    linarith

end SimplePoleProbe

namespace Place p2m_export "AlgebraicCurve.Place" "localResidue localResidue_simplePole differentialCoeff_ne_zero uniformizer ord_uniformizer uniformizer_ne_zero DCoordGenerates differentialCoeff ordDifferential ext ResidueField ord ord_mul ord_inv ord_unit_smul_zpow toValuationSubring adicValuation_eq_exp_neg_ord" end Place
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.exists_trace_residue_ne_zero [HasSeparableResidue K F] (v : Place K F) :
    ∃ c : v.toValuationSubring,
      Algebra.trace K v.ResidueField (IsLocalRing.residue _ c) ≠ 0 := by
  have htr := HasSeparableResidue.trace_ne_zero (K := K) (F := F) v
  rw [ne_eq, LinearMap.ext_iff, not_forall] at htr
  obtain ⟨x, hx⟩ := htr
  obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective x
  exact ⟨c, by simpa using hx⟩

end Place
p2m_export "AlgebraicCurve" "Place.exists_trace_residue_ne_zero"

section Nonvanishing

variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
  [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

theorem weilOfKaehler_ne_zero_s6 [HasSeparableResidue K F] [Nonempty (Place K F)]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) : weilOfKaehler K F hω ≠ 0 := by
  obtain ⟨v⟩ := ‹Nonempty (Place K F)›
  obtain ⟨c, hc⟩ := v.exists_trace_residue_ne_zero
  intro h
  apply hc
  rw [← weilOfKaehler_simplePoleProbe hω v c, h, LinearMap.zero_apply]

end Nonvanishing

section Maximality

variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
  [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

theorem trace_residueField_eq_zero_of_weilOfKaehler_mem {ω : Ω[F⁄K]} (hω : ω ≠ 0)
    {D : Divisor K F} (hD : weilOfKaehler K F hω ∈ omegaSpace D)
    {v : Place K F} (hDv : canonicalDivisorOf hω v < D v) :
    (Algebra.trace K v.ResidueField : _ →ₗ[K] K) = 0 := by
  ext x
  obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective x
  rw [LinearMap.zero_apply, ← weilOfKaehler_simplePoleProbe hω v c]
  exact omegaSpace_vanishBdd hD (simplePoleProbe_mem_adeleBdd hω v c hDv)

theorem weilOfKaehler_omegaSpace_le_canonical_s6 [HasSeparableResidue K F]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) {D : Divisor K F}
    (hD : weilOfKaehler K F hω ∈ omegaSpace D) :
    D ≤ canonicalDivisorOf hω := by
  intro v
  rcases le_or_gt (D v) (canonicalDivisorOf hω v) with h | h
  · exact h
  · exact absurd (trace_residueField_eq_zero_of_weilOfKaehler_mem hω hD h)
      (HasSeparableResidue.trace_ne_zero v)

end Maximality

section Discharge

variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
  [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

theorem weilKaehlerAgree_of_residueTheorem_s6 [HasSeparableResidue K F] [Nonempty (Place K F)]
    (hRT : ResidueTheorem K F) : WeilKaehlerAgree K F := by
  intro _ ω hω
  exact ⟨weilOfKaehler_ne_zero_s6 hω,
    weilOfKaehler_mem_omegaSpace_of_residueTheorem hRT hω,
    fun D hD => weilOfKaehler_omegaSpace_le_canonical_s6 hω hD⟩

theorem gate_weilKaehlerAgree_recovers_adeleBdd_vanish [HasSeparableResidue K F]
    [Nonempty (Place K F)] [HasPrincipalDivisors K F]
    (hRT : ResidueTheorem K F) {ω : Ω[F⁄K]} (hω : ω ≠ 0)
    {α : adeleSpace K F} (hα : (α : Place K F → F) ∈ adeleBdd (canonicalDivisorOf hω)) :
    weilOfKaehler K F hω α = 0 :=
  omegaSpace_vanishBdd (weilKaehlerAgree_of_residueTheorem_s6 hRT hω).2.1 hα

theorem gate_canonicalDivisor_maximal_fixedPoint [HasSeparableResidue K F]
    [Nonempty (Place K F)] [HasPrincipalDivisors K F]
    (hRT : ResidueTheorem K F) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    weilOfKaehler K F hω ∈ omegaSpace (canonicalDivisorOf hω) ∧
      ∀ D, weilOfKaehler K F hω ∈ omegaSpace D → D ≤ canonicalDivisorOf hω :=
  (weilKaehlerAgree_of_residueTheorem_s6 hRT hω).2

end Discharge

theorem _root_.P2MW.S_AlgebraicCurve_weilKaehlerAgree_of_residueTheorem.solution {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]] [HasSeparableResidue K F] [Nonempty (Place K F)]
    (hRT : ResidueTheorem K F) : WeilKaehlerAgree K F :=
  weilKaehlerAgree_of_residueTheorem_s6 hRT

end AlgebraicCurve
end

end S_AlgebraicCurve_weilKaehlerAgree_of_residueTheorem
end P2MW
export P2MW.S_AlgebraicCurve_weilKaehlerAgree_of_residueTheorem (solution)
