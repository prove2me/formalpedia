-- Prove2me | solution 1 for AutomorphicForm.isLevelSphericalOfType_ofChar_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/275eae80-b40e-5c3f-9e38-cf3b7b801133

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_ArchSpherical
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_isFactorizableTestFn_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isLevelSphericalOfType_ofChar_flat
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed"

set_option autoImplicit false

open NumberField IsDedekindDomain
open NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.CuspidalSpectrum

open scoped ComplexConjugate

noncomputable section

namespace Ws48FlatSph

variable {F : Type} [Field F] [NumberField F]

def wt (σ : ℝ) (x : GL (Fin 2) (InfiniteAdeleRing F)) : ℂ :=
  ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x)) ^ (-σ) : ℝ) : ℂ)

def aflat (σ : ℝ) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) : GL (Fin 2) (InfiniteAdeleRing F) → ℂ :=
  fun x => conj (fa x⁻¹) * wt σ x

theorem det_map_generalLinearGroup {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map φ g) =
      Units.map φ.toMonoidHom (Matrix.GeneralLinearGroup.det g) := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rfl

theorem det_rowIsometryInclAt₀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    Matrix.GeneralLinearGroup.det (rowIsometryInclAt₀ F w k) = 1 := by
  have hk : ((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det = 1 :=
    ((mem_rowIsometrySubgroup₀_iff (K := w.Completion)).mp k.2).1
  have hfin : Units.map (adeleFin (𝓞 F) F).toMonoidHom (Matrix.GeneralLinearGroup.det (rowIsometryInclAt₀ F w k)) = 1 := by
    rw [← det_map_generalLinearGroup]
    show Matrix.GeneralLinearGroup.det (glFin (𝓞 F) F (rowIsometryInclAt₀ F w k)) = 1
    rw [glFin_rowIsometryInclAt₀, map_one]
  have harch : ∀ v : InfinitePlace F, Units.map ((archEval F v).comp (adeleArch (𝓞 F) F)).toMonoidHom
      (Matrix.GeneralLinearGroup.det (rowIsometryInclAt₀ F w k)) = 1 := by
    intro v
    rw [← det_map_generalLinearGroup]
    have : Matrix.GeneralLinearGroup.map ((archEval F v).comp (adeleArch (𝓞 F) F)) (rowIsometryInclAt₀ F w k)
        = archComponent F v (glArch (𝓞 F) F (rowIsometryInclAt₀ F w k)) := rfl
    rw [this, glArch_rowIsometryInclAt₀]
    by_cases hv : v = w
    · subst hv
      show Matrix.GeneralLinearGroup.det (archComponent F v (archGLIncl F v (k : GL (Fin 2) v.Completion))) = 1
      rw [archComponent_archGLIncl_self]
      exact Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, hk, Units.val_one])
    · show Matrix.GeneralLinearGroup.det (archComponent F v (archGLIncl F w (k : GL (Fin 2) w.Completion))) = 1
      rw [archComponent_archGLIncl_of_ne F hv, map_one]
  refine Units.ext (Prod.ext (funext fun v => ?_) ?_)
  · have := congrArg (fun u : (v.Completion)ˣ => (u : v.Completion)) (harch v)
    have h__ := this
    try simp at h__
    try simp
    exact h__
  · have := congrArg (fun u : (FiniteAdeleRing (𝓞 F) F)ˣ => (u : FiniteAdeleRing (𝓞 F) F)) hfin
    have h__ := this
    try simp at h__
    try simp
    exact h__

theorem adelicArchGLIncl_archRowIsometryInclAt₀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    adelicArchGLIncl F (archRowIsometryInclAt₀ F w k) = rowIsometryInclAt₀ F w k := rfl

theorem wt_mul_left (σ : ℝ) (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
    (x : GL (Fin 2) (InfiniteAdeleRing F)) : wt σ (archRowIsometryInclAt₀ F w k * x) = wt σ x := by
  unfold wt
  rw [map_mul, map_mul, adelicArchGLIncl_archRowIsometryInclAt₀, det_rowIsometryInclAt₀, one_mul]

theorem wt_mul_right (σ : ℝ) (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
    (x : GL (Fin 2) (InfiniteAdeleRing F)) : wt σ (x * archRowIsometryInclAt₀ F w k) = wt σ x := by
  unfold wt
  rw [map_mul, map_mul, adelicArchGLIncl_archRowIsometryInclAt₀, det_rowIsometryInclAt₀, mul_one]

omit [NumberField F] in
theorem mem_archFactorCutSubmodule_ofChar_iff
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ) (g : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) :
    g ∈ archFactorCutSubmodule F (ArchTypeFamily.ofChar F χ) ↔
      ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
        g (x * archRowIsometryInclAt₀ F w k) = ((χ w k : ℂˣ) : ℂ) * g x := by
  show g ∈ ⨅ w : InfinitePlace F,
      ⨆ _ : Fin 1, archFactorTypeSubmoduleAt F w (ArchRepAt.ofChar F (χ w)) ↔ _
  simp only [iSup_const, Submodule.mem_iInf]
  exact forall_congr' fun w => mem_typeSubmodule_charRep_iff _ (χ w) g

omit [NumberField F] in
theorem mem_archFactorDualCutSubmodule_ofChar_iff
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ) (g : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) :
    g ∈ archFactorDualCutSubmodule F (ArchTypeFamily.ofChar F χ) ↔
      ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
        g (x * archRowIsometryInclAt₀ F w k) = ((χ w k⁻¹ : ℂˣ) : ℂ) * g x := by
  show g ∈ ⨅ w : InfinitePlace F,
      ⨆ _ : Fin 1, archFactorDualTypeSubmoduleAt F w (ArchRepAt.ofChar F (χ w)) ↔ _
  simp only [iSup_const, Submodule.mem_iInf]
  exact forall_congr' fun w => mem_typeSubmodule_charRep_dual_iff _ (χ w) g

theorem conj_eq_inv_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : conj z = z⁻¹ := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hz, one_pow, inv_one, Complex.ofReal_one, mul_one]

omit [NumberField F] in
theorem conj_char {χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ}
    (hχ : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ‖((χ w k : ℂˣ) : ℂ)‖ = 1)
    (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    conj ((χ w k : ℂˣ) : ℂ) = ((χ w k⁻¹ : ℂˣ) : ℂ) := by
  rw [map_inv, Units.val_inv_eq_inv_val]
  exact conj_eq_inv_of_norm_eq_one (hχ w k)

theorem isArchFactorBiFinite_aflat (σ : ℝ)
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (hχ : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ‖((χ w k : ℂˣ) : ℂ)‖ = 1)
    (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hbf : IsArchFactorBiFinite F (ArchTypeFamily.ofChar F χ) fa) :
    IsArchFactorBiFinite F (ArchTypeFamily.ofChar F χ) (aflat σ fa) := by
  obtain ⟨hL, hR⟩ := hbf
  rw [mem_archFactorCutSubmodule_ofChar_iff] at hL
  rw [mem_archFactorDualCutSubmodule_ofChar_iff] at hR

  refine ⟨(mem_archFactorCutSubmodule_ofChar_iff χ _).2 fun w k x => ?_,
    (mem_archFactorDualCutSubmodule_ofChar_iff χ _).2 fun w k x => ?_⟩
  ·
    show conj (fa (x * archRowIsometryInclAt₀ F w k)⁻¹⁻¹) * wt σ (x * archRowIsometryInclAt₀ F w k)⁻¹
        = ((χ w k : ℂˣ) : ℂ) * (conj (fa x⁻¹⁻¹) * wt σ x⁻¹)
    rw [inv_inv, inv_inv, hR w k x, map_mul, mul_inv_rev, ← map_inv, wt_mul_left, conj_char hχ, inv_inv, mul_assoc]
  ·
    show conj (fa (x * archRowIsometryInclAt₀ F w k)⁻¹) * wt σ (x * archRowIsometryInclAt₀ F w k)
        = ((χ w k⁻¹ : ℂˣ) : ℂ) * (conj (fa x⁻¹) * wt σ x)
    rw [hL w k x, map_mul, wt_mul_right, conj_char hχ, mul_assoc]

theorem aflat_conj_invariant (σ : ℝ) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hc : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
      fa (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = fa x) :
    ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
      aflat σ fa (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = aflat σ fa x := by
  intro w k x
  show conj (fa (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹)⁻¹) *
      wt σ (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = conj (fa x⁻¹) * wt σ x
  have h1 : (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹)⁻¹
      = archRowIsometryInclAt₀ F w k * x⁻¹ * (archRowIsometryInclAt₀ F w k)⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc]
  rw [h1, hc w k x⁻¹, ← map_inv, wt_mul_right, wt_mul_left]

theorem isFinTestFactor_indicator {S : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))} (hSo : IsOpen S) (hSc : IsCompact S) :
    IsFinTestFactor F (S.indicator fun _ => (1 : ℂ)) := by
  haveI : T2Space (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := inferInstance
  have hScl : IsClosed S := hSc.isClosed
  refine ⟨fun s => ?_, HasCompactSupport.intro hSc fun y hy => Set.indicator_of_notMem hy _⟩
  by_cases h1 : (1 : ℂ) ∈ s <;> by_cases h0 : (0 : ℂ) ∈ s
  · have : (S.indicator fun _ => (1 : ℂ)) ⁻¹' s = Set.univ := by
      ext y; by_cases hy : y ∈ S <;> simp [Set.indicator, hy, h1, h0]
    rw [this]; exact isOpen_univ
  · have : (S.indicator fun _ => (1 : ℂ)) ⁻¹' s = S := by
      ext y; by_cases hy : y ∈ S <;> simp [Set.indicator, hy, h1, h0]
    rw [this]; exact hSo
  · have : (S.indicator fun _ => (1 : ℂ)) ⁻¹' s = Sᶜ := by
      ext y; by_cases hy : y ∈ S <;> simp [Set.indicator, hy, h1, h0]
    rw [this]; exact hScl.isOpen_compl
  · have : (S.indicator fun _ => (1 : ℂ)) ⁻¹' s = ∅ := by
      ext y; by_cases hy : y ∈ S <;> simp [Set.indicator, hy, h1, h0]
    rw [this]; exact isOpen_empty

open scoped Classical in
theorem IsArchTestFactor.const_mul' {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (h : IsArchTestFactor F fa) (c : ℂ) :
    IsArchTestFactor F (fun y => c * fa y) := by
  obtain ⟨⟨Φ, hΦ, heq⟩, hK⟩ := h
  exact ⟨⟨fun A => c * Φ A, contDiff_const.mul hΦ, fun g => by show c * fa g = c * Φ (archEntries F g); rw [heq]⟩, hK.mul_left⟩

theorem isArchTestFactor_aflat (σ : ℝ) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hfa : IsArchTestFactor F fa) :
    IsArchTestFactor F (aflat σ fa) := by

  set S : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :=
    ((finiteLevelOne (𝓞 F) F (⊤ : Ideal (𝓞 F)) : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) :
      Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) with hS
  have hSo : IsOpen S := isOpen_finiteLevelOne (𝓞 F) F top_ne_bot
  have hSc : IsCompact S := isCompact_finiteLevelOne (𝓞 F) F (⊤ : Ideal (𝓞 F))
  set f₁ : AdelicGL2 (𝓞 F) F → ℂ := fun g => fa (glArch (𝓞 F) F g) * S.indicator (fun _ => (1 : ℂ)) (glFin (𝓞 F) F g)
    with hf₁
  have hf₁t : IsFactorizableTestFn F f₁ := ⟨fa, _, hfa, isFinTestFactor_indicator hSo hSc, fun g => rfl⟩
  obtain ⟨fa', ff', hfa', -, heq⟩ := isFactorizableTestFn_flat F σ f₁ hf₁t

  have h1S : (1 : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) ∈ S := one_mem _
  have key : ∀ x, aflat σ fa x = ff' 1 * fa' x := by
    intro x
    have h := heq (adelicArchGLIncl F x)
    rw [glArch_adelicArchGLIncl, glFin_adelicArchGLIncl] at h
    have h2 : flat F σ f₁ (adelicArchGLIncl F x) = aflat σ fa x := by
      show conj (f₁ (adelicArchGLIncl F x)⁻¹) * _ = conj (fa x⁻¹) * wt σ x
      rw [← map_inv]
      simp only [hf₁, glArch_adelicArchGLIncl, glFin_adelicArchGLIncl, Set.indicator_of_mem h1S, mul_one]
      rfl
    rw [← h2, h, mul_comm]
  have : aflat σ fa = fun x => ff' 1 * fa' x := funext key
  rw [this]
  exact IsArchTestFactor.const_mul' hfa' (ff' 1)

theorem ideleNorm_det_eq_of_glFin_mem_finiteLevelOne (N : Ideal (𝓞 F)) (g : AdelicGL2 (𝓞 F) F)
    (hg : glFin (𝓞 F) F g ∈ finiteLevelOne (𝓞 F) F N) :
    NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g)
      = NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F (glArch (𝓞 F) F g))) := by
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult F g
      (mem_finiteIntegralGL2_iff.mpr ⟨hg.1.integral, hg.2.integral⟩),
    NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult F (adelicArchGLIncl F (glArch (𝓞 F) F g))
      (by rw [glFin_adelicArchGLIncl]; exact one_mem _)]
  refine Finset.prod_congr rfl fun w _ => ?_
  unfold NumberField.AdelicVolume.archDetNorm
  rw [glArch_adelicArchGLIncl]

end Ws48FlatSph

end

open Ws48FlatSph in
theorem solution
    (F : Type) [Field F] [NumberField F] (σ : ℝ)
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (hχ : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ‖((χ w k : ℂˣ) : ℂ)‖ = 1)
    (N : Ideal (𝓞 F)) (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hf : IsLevelSphericalOfType F (ArchTypeFamily.ofChar F χ)
      (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) f) :
    IsLevelSphericalOfType F (ArchTypeFamily.ofChar F χ)
      (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (flat F σ f) := by
  obtain ⟨fa, hfa_t, hfa_bf, hfa_c, hfa_f⟩ := hf
  refine ⟨aflat σ fa, isArchTestFactor_aflat σ fa hfa_t, isArchFactorBiFinite_aflat σ χ hχ fa hfa_bf,
    aflat_conj_invariant σ fa hfa_c, fun g => ?_⟩
  set U : Subgroup (AdelicGL2 (𝓞 F) F) := levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F with hU
  set I : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) with hI
  have hIinv : ∀ y ∈ I, y⁻¹ ∈ I := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u⁻¹, inv_mem hu, map_inv _ _⟩
  have hIlevel : ∀ y : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F y ∈ I → glFin (𝓞 F) F y ∈ finiteLevelOne (𝓞 F) F N := by
    rintro y ⟨u, hu, hyu⟩
    rw [← hyu]
    exact (Subgroup.mem_inf.mp hu).1
  show conj (f g⁻¹) * ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-σ) : ℝ) : ℂ)
      = aflat σ fa (glArch (𝓞 F) F g) * I.indicator (fun _ => (1 : ℂ)) (glFin (𝓞 F) F g)
  rw [hfa_f g⁻¹, map_inv, map_inv]
  by_cases hg : glFin (𝓞 F) F g ∈ I
  · have hg' : (glFin (𝓞 F) F g)⁻¹ ∈ I := hIinv _ hg
    rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg', mul_one, mul_one,
      ideleNorm_det_eq_of_glFin_mem_finiteLevelOne N g (hIlevel g hg)]
    rfl
  · have hg' : (glFin (𝓞 F) F g)⁻¹ ∉ I := fun h => hg (by simpa using hIinv _ h)
    rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg', mul_zero, mul_zero, map_zero, zero_mul]

end S_AutomorphicForm_isLevelSphericalOfType_ofChar_flat
end P2MW
export P2MW.S_AutomorphicForm_isLevelSphericalOfType_ofChar_flat (solution)
