-- Prove2me | solution 1 for AlgebraicCurve.Place.module_finite_residueField_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/b1ade737-8387-5c9c-a781-226a7c5f79ca

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_module_finite_residueField_restrict

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "restrict restrictInclusion instAlgebraResidueFieldRestrictPushforward ext ResidueField FiniteResidue ord ord_mul ord_inv exists_unit_mul_zpow toValuationSubring"
p2m_open "AlgebraicCurve.Place"

section SinglePlace

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.mem_of_ord_nonneg' {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

p2m_export "AlgebraicCurve.Place" "mem_of_ord_nonneg'"
end SinglePlace

section Restrict

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F'] [Algebra F F'] [Algebra K F] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] (w : Place K F')

private abbrev _root_.AlgebraicCurve.Place.restrictSubringHom : (w.restrict F).toValuationSubring →+* w.toValuationSubring :=
  restrictInclusion F w

p2m_export "AlgebraicCurve.Place" "restrictSubringHom"
theorem coe_restrictSubringHom (x : (w.restrict F).toValuationSubring) :
    (w.restrictSubringHom x : F') = algebraMap F F' (x : F) := rfl

theorem algebraMap_residueField_residue (x : (w.restrict F).toValuationSubring) :
    algebraMap (w.restrict F).ResidueField w.ResidueField
        (IsLocalRing.residue _ x)
      = IsLocalRing.residue _ (w.restrictSubringHom x) :=
  IsLocalRing.ResidueField.map_residue _ _

private theorem _root_.AlgebraicCurve.Place.linearIndependent_of_residue {n : ℕ} {b : Fin n → w.ResidueField}
    (hb : LinearIndependent (w.restrict F).ResidueField b)
    (b' : Fin n → w.toValuationSubring)
    (hb' : ∀ i, IsLocalRing.residue _ (b' i) = b i) :
    LinearIndependent F (fun i => (b' i : F')) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  push Not at hne
  obtain ⟨i₀, hi₀⟩ := hne

  set v : Place K F := w.restrict F with hv
  set T : Finset (Fin n) := Finset.univ.filter fun i => g i ≠ 0 with hT
  have hT₀ : T.Nonempty := ⟨i₀, by simp [hT, hi₀]⟩
  obtain ⟨j, hjT, hjmin⟩ := T.exists_min_image (fun i => v.ord (g i)) hT₀
  have hgj : g j ≠ 0 := by simpa [hT] using hjT

  have hcmem : ∀ i, g i / g j ∈ v.toValuationSubring := by
    intro i
    rcases eq_or_ne (g i) 0 with h0 | h0
    · simp [h0, zero_div]
    · refine v.mem_of_ord_nonneg' (div_ne_zero h0 hgj) ?_
      have hle := hjmin i (by simp [hT, h0])
      rw [div_eq_mul_inv, v.ord_mul h0 (inv_ne_zero hgj), v.ord_inv]
      omega
  set c : (i : Fin n) → v.toValuationSubring := fun i => ⟨g i / g j, hcmem i⟩ with hc

  have hsum : (∑ i, w.restrictSubringHom (c i) * b' i) = 0 := by
    have hinj : Function.Injective
        (Subtype.val : w.toValuationSubring → F') := Subtype.val_injective
    apply hinj
    push_cast
    simp only [coe_restrictSubringHom]
    show (∑ i, algebraMap F F' (g i / g j) * (b' i : F')) = (0 : F')
    have hrescale : ∀ i, algebraMap F F' (g i / g j) * (b' i : F')
        = (g j)⁻¹ • (g i • (b' i : F')) := by
      intro i
      rw [smul_smul, Algebra.smul_def, div_eq_inv_mul, map_mul]
    simp only [hrescale]
    rw [← Finset.smul_sum, hg, smul_zero]

  have hres : (∑ i, (IsLocalRing.residue _ (c i)) • b i) = 0 := by
    have := congrArg (IsLocalRing.residue w.toValuationSubring) hsum
    rw [map_sum, map_zero] at this
    convert this using 2 with i
    rw [Algebra.smul_def, algebraMap_residueField_residue, ← hb' i, ← map_mul]

  have hzero := Fintype.linearIndependent_iff.mp hb _ hres j

  have hcj : c j = 1 := by
    ext
    show g j / g j = 1
    exact div_self hgj
  rw [hcj, map_one] at hzero
  exact one_ne_zero hzero

p2m_export "AlgebraicCurve.Place" "linearIndependent_of_residue"

private theorem _root_.AlgebraicCurve.Place.module_finite_residueField_restrict' [Module.Finite F F'] :
    Module.Finite (w.restrict F).ResidueField w.ResidueField := by
  rw [← Module.rank_lt_aleph0_iff]
  by_contra hlt
  rw [not_lt] at hlt

  obtain ⟨b, hb⟩ := exists_linearIndependent_of_le_rank
    (n := Module.finrank F F' + 1)
    (le_trans Cardinal.natCast_lt_aleph0.le hlt)
  choose b' hb' using fun i => IsLocalRing.residue_surjective (b i)
  have hli := w.linearIndependent_of_residue hb b' hb'
  have hcard := hli.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hcard
  omega

p2m_export "AlgebraicCurve.Place" "module_finite_residueField_restrict'"
end Restrict

end Place

end AlgebraicCurve

end

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_module_finite_residueField_restrict.AlgebraicCurve in

theorem solution (K F F' : Type*)
    [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] (w : Place K F') :
    Module.Finite (w.restrict F).ResidueField w.ResidueField :=
  w.module_finite_residueField_restrict'

end S_AlgebraicCurve_Place_module_finite_residueField_restrict
end P2MW
export P2MW.S_AlgebraicCurve_Place_module_finite_residueField_restrict (solution)
