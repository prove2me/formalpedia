-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.transcendental_of_residue_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/6b98e0f7-9679-5c6b-9129-c20b2a1ca8d2

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_transcendental_of_residue_transcendental

set_option autoImplicit false
set_option maxHeartbeats 4000000

open AlgebraicCurve IsLocalRing Polynomial

theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x)) :
    Transcendental L (x : F) := by
  intro halg
  obtain ⟨q, hq0, hqx⟩ := halg
  have hsupp : q.support.Nonempty := Polynomial.support_nonempty.mpr hq0
  apply hx

  obtain ⟨j₀, hj₀, hj₀max⟩ := Finset.exists_max_image q.support
    (fun j => A.valuation (q.coeff j)) hsupp
  have hcj₀ : q.coeff j₀ ≠ 0 := Polynomial.mem_support_iff.mp hj₀
  set c : L := (q.coeff j₀)⁻¹ with hc
  have hc0 : c ≠ 0 := inv_ne_zero hcj₀

  have hcoeff : ∀ j, c * q.coeff j ∈ A := by
    intro j
    by_cases hj : j ∈ q.support
    · have hv := hj₀max j hj
      rw [← A.valuation_le_one_iff, map_mul, hc, map_inv₀]
      have hvj₀ : A.valuation (q.coeff j₀) ≠ 0 := by
        simp only [ne_eq, map_eq_zero]; exact hcj₀
      calc (A.valuation (q.coeff j₀))⁻¹ * A.valuation (q.coeff j)
          ≤ (A.valuation (q.coeff j₀))⁻¹ * A.valuation (q.coeff j₀) :=
            mul_le_mul_right hv _
        _ = 1 := inv_mul_cancel₀ hvj₀
    · rw [Polynomial.notMem_support_iff.mp hj, mul_zero]
      exact A.zero_mem

  set q' : Polynomial A := q.support.sum
    (fun j => Polynomial.C ⟨c * q.coeff j, hcoeff j⟩ * Polynomial.X ^ j) with hq'

  have hq'map : q'.map A.subtype = c • q := by
    rw [hq']
    ext j
    simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero, Polynomial.coeff_smul,
      smul_eq_mul]
    rw [Finset.sum_ite_eq q.support j]
    by_cases hj : j ∈ q.support
    · simp [hj]
    · simp [hj, Polynomial.notMem_support_iff.mp hj]

  have hq'j₀ : q'.coeff j₀ = ⟨1, A.one_mem⟩ := by
    rw [hq']
    simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq q.support j₀, if_pos hj₀]
    refine Subtype.ext ?_
    show c * q.coeff j₀ = 1
    rw [hc, inv_mul_cancel₀ hcj₀]

  set q'' : Polynomial (ResidueField A) := q'.map (IsLocalRing.residue A) with hq''
  refine ⟨q'', ?_, ?_⟩
  ·
    intro hq''0
    have : q''.coeff j₀ = 0 := by rw [hq''0]; simp
    rw [hq'', Polynomial.coeff_map, hq'j₀] at this
    exact one_ne_zero (α := ResidueField ↥A)
      ((map_one (residue ↥A)).symm.trans this)
  ·

    have heval0 : (Polynomial.aeval (x : F)) (q'.map A.subtype) = 0 := by
      rw [hq'map, map_smul, hqx, smul_zero]

    let φ : A →+* R.integers :=
      { toFun := fun a => ⟨algebraMap L F a, (R.algebraMap_mem_iff a).mpr a.2⟩
        map_one' := Subtype.ext (map_one _)
        map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _)
        map_zero' := Subtype.ext (map_zero _)
        map_add' := fun _ _ => Subtype.ext (map_add _ _ _) }

    have hsub : R.integers.subtype.comp φ = (algebraMap L F).comp A.subtype := by
      ext a; rfl
    have hevO : (Polynomial.eval₂ φ x q' : R.integers) = 0 := by
      apply Subtype.ext
      show ((Polynomial.eval₂ φ x q' : R.integers) : F) = ((0 : R.integers) : F)
      have h1 : ((Polynomial.eval₂ φ x q' : R.integers) : F) =
          Polynomial.eval₂ ((algebraMap L F).comp A.subtype) (↑x) q' := by
        rw [← hsub]
        exact Polynomial.hom_eval₂ q' φ R.integers.subtype x
      rw [h1, ← Polynomial.eval₂_map]
      simpa [Polynomial.aeval_def] using heval0

    have hresφ : R.residue.comp φ = (algebraMap (ResidueField A) Fbar).comp (residue A) := by
      ext a
      exact R.residue_algebraMap a
    calc (Polynomial.aeval (R.residue x)) q''
        = Polynomial.eval₂ (algebraMap (ResidueField A) Fbar) (R.residue x)
            (q'.map (residue A)) := by rw [hq'', Polynomial.aeval_def]
      _ = Polynomial.eval₂ ((algebraMap (ResidueField A) Fbar).comp (residue A))
            (R.residue x) q' := by rw [Polynomial.eval₂_map]
      _ = Polynomial.eval₂ (R.residue.comp φ) (R.residue x) q' := by rw [hresφ]
      _ = R.residue (Polynomial.eval₂ φ x q') := (Polynomial.hom_eval₂ q' φ R.residue x).symm
      _ = R.residue 0 := by rw [hevO]
      _ = 0 := map_zero _

end S_AlgebraicCurve_RegularProlongation_transcendental_of_residue_transcendental
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_transcendental_of_residue_transcendental (solution)
