-- Prove2me | solution 1 for AutomorphicForm.CuspidalSpectrum.isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/5ce1cd44-673b-5703-aa77-c113d10bc1b9

import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
open scoped ComplexConjugate

noncomputable section

namespace ArchFlatProof

open scoped Classical
open NumberField.InfinitePlace NumberField.mixedEmbedding

variable {F : Type} [Field F] [NumberField F]

private def NZ (z : mixedSpace F) : Prop := (∀ w, z.1 w ≠ 0) ∧ ∀ w, z.2 w ≠ 0

private theorem mul_inv_of_NZ {z : mixedSpace F} (hz : NZ z) : z * z⁻¹ = 1 := by
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · exact mul_inv_cancel₀ (hz.1 w)
  · exact mul_inv_cancel₀ (hz.2 w)

private theorem isUnit_of_NZ {z : mixedSpace F} (hz : NZ z) : IsUnit z :=
  ⟨⟨z, z⁻¹, mul_inv_of_NZ hz, by rw [mul_comm]; exact mul_inv_of_NZ hz⟩, rfl⟩

private theorem NZ_of_isUnit {z : mixedSpace F} (hz : IsUnit z) : NZ z := by
  obtain ⟨u, rfl⟩ := hz
  have h1 : (u : mixedSpace F) * ((u⁻¹ : (mixedSpace F)ˣ) : mixedSpace F) = 1 := u.mul_inv
  refine ⟨fun w h0 => ?_, fun w h0 => ?_⟩
  · have := congrArg (fun z : mixedSpace F => z.1 w) h1
    simp only [Prod.fst_mul, Pi.mul_apply, Prod.fst_one, Pi.one_apply, h0, zero_mul] at this
    exact zero_ne_one this
  · have := congrArg (fun z : mixedSpace F => z.2 w) h1
    simp only [Prod.snd_mul, Pi.mul_apply, Prod.snd_one, Pi.one_apply, h0, zero_mul] at this
    exact zero_ne_one this

private theorem ringInverse_of_NZ {z : mixedSpace F} (hz : NZ z) : Ring.inverse z = z⁻¹ := by
  have h1 : z * Ring.inverse z = 1 := Ring.mul_inverse_cancel z (isUnit_of_NZ hz)
  have h2 : z * z⁻¹ = 1 := mul_inv_of_NZ hz
  calc Ring.inverse z = Ring.inverse z * (z * z⁻¹) := by rw [h2, mul_one]
    _ = (z * Ring.inverse z) * z⁻¹ := by ring
    _ = z⁻¹ := by rw [h1, one_mul]

private theorem isOpen_NZ : IsOpen {z : mixedSpace F | NZ z} := by
  have h1 : {z : mixedSpace F | NZ z} = (⋂ w, {z : mixedSpace F | z.1 w ≠ 0}) ∩ ⋂ w, {z : mixedSpace F | z.2 w ≠ 0} := by
    ext z; simp [NZ, Set.mem_iInter]
  rw [h1]
  refine (isOpen_iInter_of_finite fun w => ?_).inter (isOpen_iInter_of_finite fun w => ?_)
  · exact isOpen_ne_fun ((continuous_apply w).comp continuous_fst) continuous_const
  · exact isOpen_ne_fun ((continuous_apply w).comp continuous_snd) continuous_const

private theorem NZ_ringEquiv_of_isUnit {d : InfiniteAdeleRing F} (hd : IsUnit d) :
    NZ (InfiniteAdeleRing.ringEquiv_mixedSpace F d) :=
  NZ_of_isUnit (hd.map _)

private abbrev Ent (F : Type) [Field F] [NumberField F] := Fin 2 → Fin 2 → mixedSpace F

private def det₂ (A : Ent F) : mixedSpace F := A 0 0 * A 1 1 - A 0 1 * A 1 0

private def adj₂ (A : Ent F) : Ent F := fun i j =>
  if i = 0 then (if j = 0 then A 1 1 else -A 0 1) else (if j = 0 then -A 1 0 else A 0 0)

private def inv₂ (A : Ent F) : Ent F := fun i j => (det₂ A)⁻¹ * adj₂ A i j

private theorem det₂_archEntries (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    det₂ (archEntries F g) = InfiniteAdeleRing.ringEquiv_mixedSpace F (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)).det := by
  simp only [det₂, archEntries, Matrix.det_fin_two, map_sub, map_mul]

private theorem NZ_det₂_archEntries (g : GL (Fin 2) (InfiniteAdeleRing F)) : NZ (det₂ (archEntries F g)) := by
  rw [det₂_archEntries]
  exact NZ_ringEquiv_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit)

private theorem inv₂_archEntries (g : GL (Fin 2) (InfiniteAdeleRing F)) : inv₂ (archEntries F g) = archEntries F g⁻¹ := by
  set R := InfiniteAdeleRing.ringEquiv_mixedSpace F with hR
  set M : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) := (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) with hM
  have hdetU : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit

  have hRinv : R (Ring.inverse M.det) = (R M.det)⁻¹ := by
    have h1 : R M.det * R (Ring.inverse M.det) = 1 := by
      rw [← map_mul, Ring.mul_inverse_cancel _ hdetU, map_one]
    have h2 : R M.det * (R M.det)⁻¹ = 1 := mul_inv_of_NZ (NZ_ringEquiv_of_isUnit hdetU)
    calc R (Ring.inverse M.det) = R (Ring.inverse M.det) * (R M.det * (R M.det)⁻¹) := by rw [h2, mul_one]
      _ = (R M.det * R (Ring.inverse M.det)) * (R M.det)⁻¹ := by ring
      _ = (R M.det)⁻¹ := by rw [h1, one_mul]
  have hinvM : ((g⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) = Ring.inverse M.det • M.adjugate := by
    rw [Matrix.coe_units_inv, Matrix.inv_def]
  funext i j
  simp only [inv₂, archEntries, det₂_archEntries, hinvM, Matrix.smul_apply, smul_eq_mul, map_mul, ← hR, ← hM, hRinv,
    Matrix.adjugate_fin_two]
  congr 1
  fin_cases i <;> fin_cases j <;> simp [adj₂, archEntries, Matrix.of_apply, map_neg, ← hR, ← hM]

private theorem exists_archEntries_eq_of_NZ {A : Ent F} (hA : NZ (det₂ A)) : ∃ g : GL (Fin 2) (InfiniteAdeleRing F), archEntries F g = A := by
  set R := InfiniteAdeleRing.ringEquiv_mixedSpace F with hR
  set M : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) := Matrix.of fun i j => R.symm (A i j) with hM
  have hdet : R M.det = det₂ A := by
    simp only [hM, Matrix.det_fin_two, Matrix.of_apply, map_sub, map_mul, RingEquiv.apply_symm_apply, det₂]
  have hU : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have : IsUnit (R M.det) := by rw [hdet]; exact isUnit_of_NZ hA
    simpa using this.map R.symm
  obtain ⟨g, hg⟩ := hU
  refine ⟨g, funext fun i => funext fun j => ?_⟩
  simp only [archEntries, hg, hM, Matrix.of_apply, ← hR, RingEquiv.apply_symm_apply]

section Calculus

variable {F : Type} [Field F] [NumberField F]

private theorem contDiff_det₂ : ContDiff ℝ (⊤ : ℕ∞) (det₂ : Ent F → mixedSpace F) :=
  ((contDiff_apply_apply (𝕜 := ℝ) (E := mixedSpace F) (0 : Fin 2) (0 : Fin 2)).mul
    (contDiff_apply_apply (𝕜 := ℝ) (E := mixedSpace F) (1 : Fin 2) (1 : Fin 2))).sub
  ((contDiff_apply_apply (𝕜 := ℝ) (E := mixedSpace F) (0 : Fin 2) (1 : Fin 2)).mul
    (contDiff_apply_apply (𝕜 := ℝ) (E := mixedSpace F) (1 : Fin 2) (0 : Fin 2)))

private theorem contDiff_adj₂ (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun A : Ent F => adj₂ A i j) := by
  fin_cases i <;> fin_cases j
  · exact contDiff_apply_apply (𝕜 := ℝ) (E := mixedSpace F) (1 : Fin 2) (1 : Fin 2)
  · exact (contDiff_apply_apply (𝕜 := ℝ) (E := mixedSpace F) (0 : Fin 2) (1 : Fin 2)).neg
  · exact (contDiff_apply_apply (𝕜 := ℝ) (E := mixedSpace F) (1 : Fin 2) (0 : Fin 2)).neg
  · exact contDiff_apply_apply (𝕜 := ℝ) (E := mixedSpace F) (0 : Fin 2) (0 : Fin 2)

private theorem contDiffAt_inv_mixedSpace {z : mixedSpace F} (hz : NZ z) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z : mixedSpace F => z⁻¹) z := by
  have : (fun z : mixedSpace F => z⁻¹) = fun z => (fun w => (z.1 w)⁻¹, fun w => (z.2 w)⁻¹) := rfl
  rw [this]
  refine ContDiffAt.prodMk (contDiffAt_pi.mpr fun w => ?_) (contDiffAt_pi.mpr fun w => ?_)
  · exact (contDiffAt_inv ℝ (hz.1 w)).comp z (((contDiffAt_apply (𝕜 := ℝ) (E := ℝ) w _).comp z contDiffAt_fst))
  · exact (contDiffAt_inv ℝ (hz.2 w)).comp z (((contDiffAt_apply (𝕜 := ℝ) (E := ℂ) w _).comp z contDiffAt_snd))

private theorem contDiffAt_inv₂ {A : Ent F} (hA : NZ (det₂ A)) : ContDiffAt ℝ (⊤ : ℕ∞) (inv₂ : Ent F → Ent F) A := by
  refine contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => ?_
  show ContDiffAt ℝ (⊤ : ℕ∞) (fun A : Ent F => (det₂ A)⁻¹ * adj₂ A i j) A
  exact ((contDiffAt_inv_mixedSpace hA).comp A contDiff_det₂.contDiffAt).mul (contDiff_adj₂ i j).contDiffAt

private def normProd (z : mixedSpace F) : ℝ := (∏ w, ‖z.1 w‖) * ∏ w, ‖z.2 w‖ ^ 2

private theorem normProd_pos {z : mixedSpace F} (hz : NZ z) : 0 < normProd z :=
  mul_pos (Finset.prod_pos fun w _ => norm_pos_iff.mpr (hz.1 w))
    (Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.mpr (hz.2 w)) 2)

private theorem contDiffAt_normProd {z : mixedSpace F} (hz : NZ z) : ContDiffAt ℝ (⊤ : ℕ∞) (normProd : mixedSpace F → ℝ) z := by
  refine ContDiffAt.mul ?_ ?_
  · refine contDiffAt_prod fun w _ => ?_
    exact (contDiffAt_norm ℝ (hz.1 w)).comp z ((contDiffAt_apply (𝕜 := ℝ) (E := ℝ) w _).comp z contDiffAt_fst)
  · refine contDiffAt_prod fun w _ => ?_
    exact ((contDiff_norm_sq ℝ (E := ℂ)).contDiffAt).comp z ((contDiffAt_apply (𝕜 := ℝ) (E := ℂ) w _).comp z contDiffAt_snd)

private theorem contDiffAt_omega (σ : ℝ) {A : Ent F} (hA : NZ (det₂ A)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun A : Ent F => ((normProd (det₂ A) ^ (-σ) : ℝ) : ℂ)) A := by
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun A : Ent F => normProd (det₂ A)) A :=
    (contDiffAt_normProd hA).comp A contDiff_det₂.contDiffAt
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun A : Ent F => normProd (det₂ A) ^ (-σ)) A :=
    h1.rpow_const_of_ne (normProd_pos hA).ne'
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp A h2

end Calculus

section Weight

variable {F : Type} [Field F] [NumberField F]

private theorem normProd_det₂_archEntries (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    normProd (det₂ (archEntries F g))
      = NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F g)) := by
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult F (adelicArchGLIncl F g)
    (by rw [glFin_adelicArchGLIncl]; exact one_mem _)]
  set M : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) := (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) with hM

  have hloc : ∀ w : InfinitePlace F, NumberField.AdelicVolume.archDetNorm w (adelicArchGLIncl F g) = ‖M.det w‖ := by
    intro w
    unfold NumberField.AdelicVolume.archDetNorm
    rw [glArch_adelicArchGLIncl]
    show ‖((archEval F w).mapMatrix M).det‖ = ‖M.det w‖
    rw [← RingHom.map_det]
    rfl
  simp_rw [hloc]

  rw [← Fintype.prod_subtype_mul_prod_subtype (p := fun w : InfinitePlace F => w.IsReal)]
  rw [det₂_archEntries, normProd]
  congr 1
  · refine Fintype.prod_congr _ _ fun w => ?_
    rw [show (w : InfinitePlace F).mult = 1 by simp [NumberField.InfinitePlace.mult, w.2], pow_one]
    show ‖InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (M.det w)‖ = ‖M.det w‖
    exact (AddMonoidHomClass.isometry_iff_norm _).mp (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2) _
  · refine (Fintype.prod_equiv (Equiv.subtypeEquivRight (p := fun w : InfinitePlace F => ¬ w.IsReal)
      (q := fun w : InfinitePlace F => w.IsComplex) fun w => not_isReal_iff_isComplex)
      (fun w => ‖M.det (w : InfinitePlace F)‖ ^ (w : InfinitePlace F).mult)
      (fun w => ‖((InfiniteAdeleRing.ringEquiv_mixedSpace F) M.det).2 w‖ ^ 2) fun w => ?_).symm
    have hw : ¬ (w : InfinitePlace F).IsReal := w.2
    show ‖M.det (w : InfinitePlace F)‖ ^ (w : InfinitePlace F).mult
      = ‖InfinitePlace.Completion.extensionEmbedding (w : InfinitePlace F) (M.det w)‖ ^ 2
    rw [show (w : InfinitePlace F).mult = 2 by simp [NumberField.InfinitePlace.mult, hw]]
    rw [(AddMonoidHomClass.isometry_iff_norm _).mp (InfinitePlace.Completion.isometry_extensionEmbedding (w : InfinitePlace F)) _]

end Weight

section Main

variable {F : Type} [Field F] [NumberField F]

private def extFlat (σ : ℝ) (Φ : Ent F → ℂ) (A : Ent F) : ℂ :=
  if NZ (det₂ A) then conj (Φ (inv₂ A)) * ((normProd (det₂ A) ^ (-σ) : ℝ) : ℂ) else 0

private theorem extFlat_archEntries (σ : ℝ) (Φ : Ent F → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hΦ : ∀ g, fa g = Φ (archEntries F g)) (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    extFlat σ Φ (archEntries F g) = conj (fa g⁻¹) *
      ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F g)) ^ (-σ) : ℝ) : ℂ) := by
  rw [extFlat, if_pos (NZ_det₂_archEntries g), inv₂_archEntries, ← hΦ, normProd_det₂_archEntries]

private theorem contDiff_extFlat (σ : ℝ) (Φ : Ent F → ℂ) (hΦc : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hΦ : ∀ g, fa g = Φ (archEntries F g)) (hK : HasCompactSupport fa) :
    ContDiff ℝ (⊤ : ℕ∞) (extFlat σ Φ) := by

  have hent : Continuous (archEntries F) :=
    continuous_pi fun i => continuous_pi fun j =>
      (NumberField.AdelicBox.continuous_ringEquiv_mixedSpace F).comp (Units.continuous_val.matrix_elem i j)

  set C : Set (Ent F) := archEntries F '' (tsupport fa)⁻¹ with hC
  have hCcpt : IsCompact C := hK.inv.image hent
  have hCcl : IsClosed C := hCcpt.isClosed

  have hzero : ∀ A : Ent F, A ∉ C → extFlat σ Φ A = 0 := by
    intro A hA
    by_cases hNZ : NZ (det₂ A)
    · obtain ⟨g, rfl⟩ := exists_archEntries_eq_of_NZ hNZ
      rw [extFlat_archEntries σ Φ fa hΦ]
      have hg : g⁻¹ ∉ tsupport fa := fun h => hA ⟨g, by simpa using h, rfl⟩
      rw [image_eq_zero_of_notMem_tsupport hg, map_zero, zero_mul]
    · rw [extFlat, if_neg hNZ]
  refine contDiff_iff_contDiffAt.mpr fun A => ?_
  by_cases hA : A ∈ C
  ·
    obtain ⟨g, -, rfl⟩ := hA
    have hNZ := NZ_det₂_archEntries g
    have hopen : IsOpen {A : Ent F | NZ (det₂ A)} := isOpen_NZ.preimage contDiff_det₂.continuous
    have hev : extFlat σ Φ =ᶠ[nhds (archEntries F g)]
        fun A => conj (Φ (inv₂ A)) * ((normProd (det₂ A) ^ (-σ) : ℝ) : ℂ) := by
      filter_upwards [hopen.mem_nhds hNZ] with A hA'
      exact if_pos hA'
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    refine ContDiffAt.mul ?_ (contDiffAt_omega σ hNZ)
    exact Complex.conjCLE.contDiff.contDiffAt.comp _ (hΦc.contDiffAt.comp _ (contDiffAt_inv₂ hNZ))
  ·
    have hev : extFlat σ Φ =ᶠ[nhds A] fun _ => 0 := by
      filter_upwards [hCcl.isOpen_compl.mem_nhds hA] with A' hA'
      exact hzero A' hA'
    exact contDiffAt_const.congr_of_eventuallyEq hev

end Main

end ArchFlatProof

end

open ArchFlatProof in
theorem solution
    (F : Type) [Field F] [NumberField F] (σ : ℝ)
    (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hfa : IsArchTestFactor F fa) :
    IsArchTestFactor F (fun y : GL (Fin 2) (InfiniteAdeleRing F) => conj (fa y⁻¹) *
      ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F y)) ^ (-σ) : ℝ) : ℂ)) := by
  classical
  haveI : T2Space (GL (Fin 2) (InfiniteAdeleRing F)) := inferInstance
  obtain ⟨⟨Φ, hΦc, hΦ⟩, hK⟩ := hfa
  refine ⟨⟨extFlat σ Φ, contDiff_extFlat σ Φ hΦc fa hΦ hK, fun g => (extFlat_archEntries σ Φ fa hΦ g).symm⟩, ?_⟩
  refine HasCompactSupport.intro hK.inv ?_
  intro y hy
  have hy' : y⁻¹ ∉ tsupport fa := fun h => hy (by simpa using Set.inv_mem_inv.mpr h)
  show conj (fa y⁻¹) * _ = 0
  rw [image_eq_zero_of_notMem_tsupport hy', map_zero, zero_mul]

end S_AutomorphicForm_CuspidalSpectrum_isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow
end P2MW
export P2MW.S_AutomorphicForm_CuspidalSpectrum_isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow (solution)
