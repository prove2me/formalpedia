-- Prove2me | Definitions.Def_BornVolumeLean_Volume_GaussianCPN
-- name    : BornVolumeLean_Volume_GaussianCPN
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:01:58.61169+00:00
-- url     : https://prove2.me/theorems/49ff0daf-d2c7-4cca-a23f-6cd4fb92d7b9
-- title:
--   Gaussian CPN
-- statement:
--   Definitions and structural lemmas for Gaussian CPN, from zblore's pinned Born weights as Fubini–Study volumes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/GaussianCPN.lean

module
public import Definitions.Def_BornVolumeLean_Volume_GaussianFS
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_UnitaryTransitive
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Theorems.Thm_BornVolume_unitary_norm_preserving
public import Theorems.Thm_P2M_Projectivization_measurable_mk__201516f83fba

set_option autoImplicit false
@[expose] public section
@[expose] public section
open MeasureTheory ProbabilityTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization
namespace BornVolume
variable {N : ℕ}
noncomputable def coordsN :
    EuclideanSpace ℝ (Fin N × Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin N) where
  toFun y := (WithLp.equiv 2 (Fin N → ℂ)).symm
    (fun i => (y (i, 0) : ℂ) + (y (i, 1) : ℂ) * Complex.I)
  invFun z := (WithLp.equiv 2 (Fin N × Fin 2 → ℝ)).symm
    (fun p => if p.2 = 0 then (z p.1).re else (z p.1).im)
  map_add' x y := by
    ext i
    simp only [WithLp.equiv_symm_apply, WithLp.ofLp_add, PiLp.toLp_apply, Pi.add_apply]
    push_cast
    ring
  map_smul' c x := by
    ext i
    simp only [WithLp.equiv_symm_apply, WithLp.ofLp_smul, PiLp.toLp_apply, Pi.smul_apply,
      RingHom.id_apply, smul_eq_mul]
    change _ = (c : ℂ) * _
    push_cast
    ring
  left_inv y := by
    ext p
    obtain ⟨i, j⟩ := p
    simp only [WithLp.equiv_symm_apply, PiLp.toLp_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    fin_cases j <;> simp
  right_inv z := by
    ext i
    simp only [WithLp.equiv_symm_apply, PiLp.toLp_apply, show (1 : Fin 2) = 0 ↔ False by decide,
      ite_true, ite_false]
    exact Complex.re_add_im (z i)
  norm_map' y := by
    show ‖(WithLp.equiv 2 (Fin N → ℂ)).symm
        (fun i => (y (i, 0) : ℂ) + (y (i, 1) : ℂ) * Complex.I)‖ = ‖y‖
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fintype.sum_prod_type]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Fin.sum_univ_two]
    simp only [WithLp.equiv_symm_apply, PiLp.toLp_apply,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Real.norm_eq_abs, sq_abs]
    ring
noncomputable def gaussianHN : Measure (EuclideanSpace ℂ (Fin N)) :=
  Measure.map coordsN (stdGaussian (EuclideanSpace ℝ (Fin N × Fin 2)))
instance instProbGaussianHN : IsProbabilityMeasure (gaussianHN (N := N)) := by
  unfold gaussianHN
  exact Measure.isProbabilityMeasure_map coordsN.continuous.measurable.aemeasurable
noncomputable def gaussianProjN (p₀ : CPN N) (v : EuclideanSpace ℂ (Fin N)) : CPN N :=
  if h : v = 0 then p₀ else Projectivization.mk ℂ v h
lemma measurable_gaussianProjN (p₀ : CPN N) : Measurable (gaussianProjN p₀) := by
  refine measurable_of_measurable_on_compl_singleton 0 ?_
  have hrestr : {v : EuclideanSpace ℂ (Fin N) | v ≠ 0}.domRestrict (gaussianProjN p₀)
      = fun v => Projectivization.mk' ℂ ⟨v.1, v.2⟩ := by
    funext v
    simp only [Set.domRestrict_apply, gaussianProjN, dif_neg v.2, Projectivization.mk'_eq_mk]
  rw [hrestr]
  exact Projectivization.measurable_mk'.comp (measurable_subtype_coe.subtype_mk)
noncomputable def gaussianCPN (p₀ : CPN N) : Measure (CPN N) :=
  Measure.map (gaussianProjN p₀) gaussianHN
instance instProbGaussianCPN (p₀ : CPN N) : IsProbabilityMeasure (gaussianCPN p₀) := by
  unfold gaussianCPN
  exact Measure.isProbabilityMeasure_map (measurable_gaussianProjN p₀).aemeasurable
lemma unitary_conjTranspose_mulN (U : Matrix.unitaryGroup (Fin N) ℂ) :
    U.valᴴ * U.val = 1 := by
  have h := U.2
  rw [Matrix.mem_unitaryGroup_iff'] at h
  rwa [Matrix.star_eq_conjTranspose] at h
lemma unitary_mul_conjTransposeN (U : Matrix.unitaryGroup (Fin N) ℂ) :
    U.val * U.valᴴ = 1 := by
  have h := U.2
  rw [Matrix.mem_unitaryGroup_iff] at h
  rwa [Matrix.star_eq_conjTranspose] at h
lemma toEuclideanLinN_real_smul (U : Matrix.unitaryGroup (Fin N) ℂ)
    (c : ℝ) (w : EuclideanSpace ℂ (Fin N)) :
    (Matrix.toEuclideanLin U.val) (c • w) = c • (Matrix.toEuclideanLin U.val) w := by
  apply (WithLp.equiv 2 (Fin N → ℂ)).injective
  simp only [WithLp.equiv_apply, Matrix.ofLp_toLpLin, Matrix.toLin'_apply, WithLp.ofLp_smul]
  exact Matrix.mulVec_smul _ _ _
noncomputable def conjRN (U : Matrix.unitaryGroup (Fin N) ℂ) :
    EuclideanSpace ℝ (Fin N × Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N × Fin 2) where
  toFun y := coordsN.symm ((Matrix.toEuclideanLin U.val) (coordsN y))
  invFun z := coordsN.symm ((Matrix.toEuclideanLin U.valᴴ) (coordsN z))
  map_add' x y := by simp only [map_add]
  map_smul' c x := by
    simp only [RingHom.id_apply, map_smul, toEuclideanLinN_real_smul]
  left_inv y := by
    show coordsN.symm ((Matrix.toEuclideanLin U.valᴴ)
        (coordsN (coordsN.symm ((Matrix.toEuclideanLin U.val) (coordsN y))))) = y
    rw [LinearIsometryEquiv.apply_symm_apply]
    rw [← LinearIsometryEquiv.symm_apply_apply coordsN y]
    apply congrArg coordsN.symm
    apply (WithLp.equiv 2 (Fin N → ℂ)).injective
    simp only [WithLp.equiv_apply, LinearIsometryEquiv.apply_symm_apply,
      Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
    rw [Matrix.mulVec_mulVec, unitary_conjTranspose_mulN, Matrix.one_mulVec]
  right_inv z := by
    show coordsN.symm ((Matrix.toEuclideanLin U.val)
        (coordsN (coordsN.symm ((Matrix.toEuclideanLin U.valᴴ) (coordsN z))))) = z
    rw [LinearIsometryEquiv.apply_symm_apply]
    rw [← LinearIsometryEquiv.symm_apply_apply coordsN z]
    apply congrArg coordsN.symm
    apply (WithLp.equiv 2 (Fin N → ℂ)).injective
    simp only [WithLp.equiv_apply, LinearIsometryEquiv.apply_symm_apply,
      Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
    rw [Matrix.mulVec_mulVec, unitary_mul_conjTransposeN, Matrix.one_mulVec]
  norm_map' y := by
    show ‖coordsN.symm ((Matrix.toEuclideanLin U.val) (coordsN y))‖ = ‖y‖
    rw [LinearIsometryEquiv.norm_map, unitary_norm_preserving, LinearIsometryEquiv.norm_map]
lemma stdGaussianN_ne_dirac [NeZero N] (x : EuclideanSpace ℝ (Fin N × Fin 2)) :
    stdGaussian (EuclideanSpace ℝ (Fin N × Fin 2)) ≠ Measure.dirac x := by
  intro hx
  set i₀ : Fin N × Fin 2 := (⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩, 0) with hi₀
  set L : StrongDual ℝ (EuclideanSpace ℝ (Fin N × Fin 2)) :=
    innerSL ℝ (EuclideanSpace.single i₀ (1 : ℝ)) with hLdef
  have hLnorm : ‖L‖ = 1 := by
    rw [hLdef, innerSL_apply_norm, PiLp.norm_single, norm_one]
  have hvar : Var[L; stdGaussian (EuclideanSpace ℝ (Fin N × Fin 2))] = 1 := by
    rw [variance_dual_stdGaussian, hLnorm, one_pow]
  rw [hx, ProbabilityTheory.variance_dirac] at hvar
  exact zero_ne_one hvar
instance instNoAtomsStdGaussianN [NeZero N] :
    NullSingletonClass (stdGaussian (EuclideanSpace ℝ (Fin N × Fin 2))) :=
  ProbabilityTheory.IsGaussian.nullSingletonClass stdGaussianN_ne_dirac
end BornVolume


