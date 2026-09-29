-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.mem_adjoin_iff_mem_integers_iff_of_transcendental_residue
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/d6ddb653-0685-5602-bf70-bba409bd0bc4

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_AlgebraicCurve_RegularProlongation_coeff_mem_of_aeval_mem_integers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_mem_adjoin_iff_mem_integers_iff_of_transcendental_residue

set_option autoImplicit false
set_option maxHeartbeats 9600000

open AlgebraicCurve IsLocalRing Polynomial

private theorem aux_mem_integers_iff
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (f : F) (hf : f ∈ R.integers)
    (htr : Transcendental (ResidueField A) (R.residue ⟨f, hf⟩))
    (q : L[X]) (hqf : aeval f q ≠ 0)
    (qA : Polynomial A) (hqAmap : qA.map A.subtype = q)
    (hqbar : qA.map (IsLocalRing.residue A) ≠ 0)
    (e : F) (p : L[X]) (hep : e * aeval f q = aeval f p) :
    e ∈ R.integers ↔ ∀ j, p.coeff j ∈ A := by
  classical
  let φ : A →+* R.integers :=
    { toFun := fun a => ⟨algebraMap L F a, (R.algebraMap_mem_iff a).mpr a.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _) }
  have hresφ : R.residue.comp φ =
      (algebraMap (ResidueField A) Fbar).comp (IsLocalRing.residue A) :=
    RingHom.ext fun a => R.residue_algebraMap a
  have hsubφ : R.integers.subtype.comp φ = (algebraMap L F).comp A.subtype :=
    RingHom.ext fun _ => rfl
  set qO : R.integers := Polynomial.eval₂ φ ⟨f, hf⟩ qA with hqO
  have hqO_coe : (qO : F) = aeval f q := by
    rw [hqO]
    calc ((Polynomial.eval₂ φ ⟨f, hf⟩ qA : R.integers) : F)
        = Polynomial.eval₂ (R.integers.subtype.comp φ) f qA :=
          Polynomial.hom_eval₂ qA φ R.integers.subtype ⟨f, hf⟩
      _ = Polynomial.eval₂ ((algebraMap L F).comp A.subtype) f qA := by rw [hsubφ]
      _ = Polynomial.eval₂ (algebraMap L F) f (qA.map A.subtype) :=
          (Polynomial.eval₂_map A.subtype (algebraMap L F) f).symm
      _ = aeval f q := by rw [hqAmap, Polynomial.aeval_def]
  have hqmem : aeval f q ∈ R.integers := hqO_coe ▸ qO.2
  have hqO_res : R.residue qO =
      aeval (R.residue ⟨f, hf⟩) (qA.map (IsLocalRing.residue A)) := by
    rw [hqO]
    calc R.residue (Polynomial.eval₂ φ ⟨f, hf⟩ qA)
        = Polynomial.eval₂ (R.residue.comp φ) (R.residue ⟨f, hf⟩) qA :=
          Polynomial.hom_eval₂ qA φ R.residue ⟨f, hf⟩
      _ = Polynomial.eval₂ ((algebraMap (ResidueField A) Fbar).comp (IsLocalRing.residue A))
            (R.residue ⟨f, hf⟩) qA := by rw [hresφ]
      _ = Polynomial.eval₂ (algebraMap (ResidueField A) Fbar) (R.residue ⟨f, hf⟩)
            (qA.map (IsLocalRing.residue A)) := (Polynomial.eval₂_map _ _ _).symm
      _ = aeval (R.residue ⟨f, hf⟩) (qA.map (IsLocalRing.residue A)) :=
          (Polynomial.aeval_def _ _).symm
  have hqO_unit : IsUnit qO := by
    apply R.isUnit_of_residue_ne_zero
    rw [hqO_res]
    exact fun habs => hqbar ((transcendental_iff.mp htr) _ habs)
  have hqinv : (aeval f q)⁻¹ ∈ R.integers := by
    obtain ⟨u, hu⟩ := hqO_unit
    have huF : ((u : R.integers) : F) = aeval f q := by rw [hu]; exact hqO_coe
    have huinv : ((↑u⁻¹ : R.integers) : F) = (aeval f q)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      have h1 : ((↑u⁻¹ : R.integers) * (↑u : R.integers) : R.integers) = 1 :=
        Units.inv_mul u
      calc ((↑u⁻¹ : R.integers) : F) * aeval f q
          = ((↑u⁻¹ : R.integers) : F) * ((↑u : R.integers) : F) := by rw [huF]
        _ = (((↑u⁻¹ : R.integers) * (↑u : R.integers) : R.integers) : F) := by
            exact_mod_cast rfl
        _ = ((1 : R.integers) : F) := by rw [h1]
        _ = 1 := by exact_mod_cast rfl
    rw [← huinv]; exact (↑u⁻¹ : R.integers).2
  constructor
  · intro heR
    have hpmem : aeval f p ∈ R.integers := hep ▸ mul_mem heR hqmem
    exact fun j =>
      RegularProlongation.coeff_mem_of_aeval_mem_integers A R ⟨f, hf⟩ htr p hpmem j
  · intro hpA
    have hpmem : aeval f p ∈ R.integers := by
      rw [aeval_eq_sum_range]
      refine sum_mem fun j _ => ?_
      rw [Algebra.smul_def]
      exact mul_mem ((R.algebraMap_mem_iff _).mpr (hpA j)) (pow_mem hf j)
    have heq : e = (aeval f p) * (aeval f q)⁻¹ := by
      rw [← hep, mul_inv_cancel_right₀ hqf]
    rw [heq]; exact mul_mem hpmem hqinv

theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fb₁ Fb₂ : Type*} [Field Fb₁] [Field Fb₂]
    [Algebra (IsLocalRing.ResidueField A) Fb₁] [Algebra (IsLocalRing.ResidueField A) Fb₂]
    (R₁ : RegularProlongation A F Fb₁) (R₂ : RegularProlongation A F Fb₂)
    (f : F) (hf₁ : f ∈ R₁.integers) (hf₂ : f ∈ R₂.integers)
    (htr₁ : Transcendental (IsLocalRing.ResidueField A) (R₁.residue ⟨f, hf₁⟩))
    (htr₂ : Transcendental (IsLocalRing.ResidueField A) (R₂.residue ⟨f, hf₂⟩))
    (e : F) (he : e ∈ IntermediateField.adjoin L ({f} : Set F)) :
    e ∈ R₁.integers ↔ e ∈ R₂.integers := by
  classical
  rcases eq_or_ne e 0 with rfl | hene
  · simp only [zero_mem]
  obtain ⟨r, s, hers⟩ := (IntermediateField.mem_adjoin_simple_iff L e).mp he
  have hsf : aeval f s ≠ 0 := fun h => hene (by rw [hers, h, div_zero])
  obtain ⟨c, hcmem, hcres⟩ := R₁.exists_smul_mem (aeval f s) hsf
  have hc0 : c ≠ 0 := R₁.smul_const_ne_zero hcmem hcres
  set q : L[X] := C c * s with hqdef
  have hcq : aeval f q = c • aeval f s := by
    simp only [hqdef, map_mul, aeval_C, Algebra.smul_def]
  have hqf : aeval f q ≠ 0 := hcq ▸ smul_ne_zero hc0 hsf
  have hqmem₁ : aeval f q ∈ R₁.integers := hcq ▸ hcmem
  have hqres₁ : R₁.residue ⟨aeval f q, hqmem₁⟩ ≠ 0 := by
    intro h; apply hcres
    have heq : (⟨aeval f q, hqmem₁⟩ : R₁.integers) = ⟨c • aeval f s, hcmem⟩ := Subtype.ext hcq
    rw [← heq]; exact h
  have hqA : ∀ j, q.coeff j ∈ A := fun j =>
    RegularProlongation.coeff_mem_of_aeval_mem_integers A R₁ ⟨f, hf₁⟩ htr₁ q hqmem₁ j

  set qA : Polynomial A :=
    q.support.sum (fun j => C ⟨q.coeff j, hqA j⟩ * X ^ j) with hqAdef
  have hqAmap : qA.map A.subtype = q := by
    ext j
    simp only [hqAdef, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.finset_sum_coeff,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq q.support j]
    by_cases hj : j ∈ q.support
    · simp [hj]
    · simp [hj, Polynomial.notMem_support_iff.mp hj]

  have hqbar_ne : qA.map (IsLocalRing.residue A) ≠ 0 := by
    intro hqz
    apply hqres₁
    let φ₁ : A →+* R₁.integers :=
      { toFun := fun a => ⟨algebraMap L F a, (R₁.algebraMap_mem_iff a).mpr a.2⟩
        map_one' := Subtype.ext (map_one _)
        map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _)
        map_zero' := Subtype.ext (map_zero _)
        map_add' := fun _ _ => Subtype.ext (map_add _ _ _) }
    have hresφ₁ : R₁.residue.comp φ₁ =
        (algebraMap (ResidueField A) Fb₁).comp (IsLocalRing.residue A) :=
      RingHom.ext fun a => R₁.residue_algebraMap a
    have heq' : (⟨aeval f q, hqmem₁⟩ : R₁.integers) = Polynomial.eval₂ φ₁ ⟨f, hf₁⟩ qA := by
      apply Subtype.ext
      have hsub : R₁.integers.subtype.comp φ₁ = (algebraMap L F).comp A.subtype :=
        RingHom.ext fun _ => rfl
      calc aeval f q
          = aeval f (qA.map A.subtype) := by rw [hqAmap]
        _ = Polynomial.eval₂ (algebraMap L F) f (qA.map A.subtype) := Polynomial.aeval_def _ _
        _ = Polynomial.eval₂ ((algebraMap L F).comp A.subtype) f qA :=
            Polynomial.eval₂_map A.subtype (algebraMap L F) f
        _ = Polynomial.eval₂ (R₁.integers.subtype.comp φ₁) f qA := by rw [hsub]
        _ = ((Polynomial.eval₂ φ₁ ⟨f, hf₁⟩ qA : R₁.integers) : F) :=
            (Polynomial.hom_eval₂ qA φ₁ R₁.integers.subtype ⟨f, hf₁⟩).symm
    rw [heq']
    calc R₁.residue (Polynomial.eval₂ φ₁ ⟨f, hf₁⟩ qA)
        = Polynomial.eval₂ (R₁.residue.comp φ₁) (R₁.residue ⟨f, hf₁⟩) qA :=
          Polynomial.hom_eval₂ qA φ₁ R₁.residue ⟨f, hf₁⟩
      _ = aeval (R₁.residue ⟨f, hf₁⟩) (qA.map (IsLocalRing.residue A)) := by
          rw [hresφ₁, ← Polynomial.eval₂_map, ← Polynomial.aeval_def]
      _ = 0 := by rw [hqz, map_zero]

  set p : L[X] := C c * r with hpdef
  have hep : e * aeval f q = aeval f p := by
    simp only [hqdef, hpdef, map_mul, aeval_C, hers]
    field_simp
  exact (aux_mem_integers_iff A R₁ f hf₁ htr₁ q hqf qA hqAmap hqbar_ne e p hep).trans
        (aux_mem_integers_iff A R₂ f hf₂ htr₂ q hqf qA hqAmap hqbar_ne e p hep).symm

end S_AlgebraicCurve_RegularProlongation_mem_adjoin_iff_mem_integers_iff_of_transcendental_residue
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_mem_adjoin_iff_mem_integers_iff_of_transcendental_residue (solution)
