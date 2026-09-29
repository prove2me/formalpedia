-- Prove2me | solution 1 for AutomorphicForm.integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/2054aea8-9420-5098-86df-398245f325b4

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchSpherical
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace BiAvgSphFlatProof

variable {F : Type} [Field F] [NumberField F]

private theorem ext_archComponent {g g' : GL (Fin 2) (InfiniteAdeleRing F)}
    (h : ∀ v : InfinitePlace F, archComponent F v g = archComponent F v g') : g = g' := by
  refine Units.ext (Matrix.ext fun i j => funext fun v => ?_)
  have := congrArg (fun m : GL (Fin 2) v.Completion => (m : Matrix (Fin 2) (Fin 2) v.Completion) i j) (h v)
  simpa only [archComponent_apply] using this

private theorem iota_mulSingle [DecidableEq (InfinitePlace F)]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    ι (Pi.mulSingle w k) = archRowIsometryInclAt₀ F w k := by
  refine ext_archComponent fun v => ?_
  rw [hι]
  show ((Pi.mulSingle w k : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) v : GL (Fin 2) v.Completion)
    = archComponent F v (archGLIncl F w (k : GL (Fin 2) w.Completion))
  by_cases hv : v = w
  · subst hv; rw [Pi.mulSingle_eq_same, archComponent_archGLIncl_self]
  · rw [Pi.mulSingle_eq_of_ne hv, archComponent_archGLIncl_of_ne F hv]; rfl

private theorem det_map_generalLinearGroup {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map φ g) = Units.map φ.toMonoidHom (Matrix.GeneralLinearGroup.det g) := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rfl

private theorem det_adelicArchGLIncl_iota
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) : Matrix.GeneralLinearGroup.det (adelicArchGLIncl F (ι κ)) = 1 := by
  have hfin : Units.map (adeleFin (𝓞 F) F).toMonoidHom (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F (ι κ))) = 1 := by
    rw [← det_map_generalLinearGroup]
    show Matrix.GeneralLinearGroup.det (glFin (𝓞 F) F (adelicArchGLIncl F (ι κ))) = 1
    rw [glFin_adelicArchGLIncl, map_one]
  have harch : ∀ v : InfinitePlace F, Units.map ((archEval F v).comp (adeleArch (𝓞 F) F)).toMonoidHom
      (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F (ι κ))) = 1 := by
    intro v
    rw [← det_map_generalLinearGroup]
    have : Matrix.GeneralLinearGroup.map ((archEval F v).comp (adeleArch (𝓞 F) F)) (adelicArchGLIncl F (ι κ))
        = archComponent F v (glArch (𝓞 F) F (adelicArchGLIncl F (ι κ))) := rfl
    rw [this, glArch_adelicArchGLIncl, hι]
    exact Units.ext (by
      rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
      exact ((mem_rowIsometrySubgroup₀_iff (K := v.Completion)).mp (κ v).2).1)
  refine Units.ext (Prod.ext (funext fun v => ?_) ?_)
  · have := congrArg (fun u : (v.Completion)ˣ => (u : v.Completion)) (harch v)
    simp at this
    exact this
  · have := congrArg (fun u : (FiniteAdeleRing (𝓞 F) F)ˣ => (u : FiniteAdeleRing (𝓞 F) F)) hfin
    simp at this
    exact this

end BiAvgSphFlatProof

end

open BiAvgSphFlatProof in
theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    [BorelSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    (μ : Measure (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion))
    [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [μ.IsInvInvariant]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (σ : ℝ)
    (e : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ)
    (hecl : ∀ κ κ' : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), e (κ' * κ * κ'⁻¹) = e κ)
    (hefl : ∀ κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), e κ⁻¹ = conj (e κ))
    (h : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hhc : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
      h (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = h x)
    (hhf : ∀ x : GL (Fin 2) (InfiniteAdeleRing F), h x = conj (h x⁻¹) *
      ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x)) ^ (-σ) : ℝ) : ℂ)) :
    (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
      (∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
          e p.1 * e p.2 * h ((ι p.1)⁻¹ * (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) * (ι p.2)⁻¹)
          ∂(μ.prod μ)) =
      ∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), e p.1 * e p.2 * h ((ι p.1)⁻¹ * x * (ι p.2)⁻¹) ∂(μ.prod μ)) ∧
    ∀ x : GL (Fin 2) (InfiniteAdeleRing F),
      (∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), e p.1 * e p.2 * h ((ι p.1)⁻¹ * x * (ι p.2)⁻¹) ∂(μ.prod μ)) =
        conj (∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), e p.1 * e p.2 * h ((ι p.1)⁻¹ * x⁻¹ * (ι p.2)⁻¹) ∂(μ.prod μ)) *
          ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x)) ^ (-σ) : ℝ) : ℂ) := by
  classical

  haveI : SigmaFinite μ := IsFiniteMeasure.toSigmaFinite μ
  haveI : SFinite μ := inferInstance
  haveI : MeasurableMul (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) := inferInstance
  haveI : MeasurableInv (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) := inferInstance

  set G : GL (Fin 2) (InfiniteAdeleRing F) → (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ := fun x p =>
    e p.1 * e p.2 * h ((ι p.1)⁻¹ * x * (ι p.2)⁻¹) with hG
  set W : GL (Fin 2) (InfiniteAdeleRing F) → ℂ := fun x =>
    ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x)) ^ (-σ) : ℝ) : ℂ) with hW
  have hdet1 : ∀ κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), Matrix.GeneralLinearGroup.det (adelicArchGLIncl F (ι κ)) = 1 :=
    det_adelicArchGLIncl_iota ι hι
  refine ⟨fun w k x => ?_, fun x => ?_⟩

  · set κ₀ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) := Pi.mulSingle w k with hκ₀
    have hικ₀ : ι κ₀ = archRowIsometryInclAt₀ F w k := iota_mulSingle ι hι w k

    set cj : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) ≃ᵐ (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) := (MeasurableEquiv.mulLeft κ₀).trans (MeasurableEquiv.mulRight κ₀⁻¹) with hcj
    have hcj_apply : ∀ q : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), cj q = κ₀ * q * κ₀⁻¹ := fun q => rfl
    have hcjmp : MeasurePreserving cj μ μ :=
      (measurePreserving_mul_right μ κ₀⁻¹).comp (measurePreserving_mul_left μ κ₀)
    set Φ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) ≃ᵐ (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) := MeasurableEquiv.prodCongr cj cj with hΦ
    have hΦmp : MeasurePreserving Φ (μ.prod μ) (μ.prod μ) := hcjmp.prod hcjmp
    show ∫ p, G (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) p ∂(μ.prod μ) = ∫ p, G x p ∂(μ.prod μ)
    rw [← hΦmp.integral_comp' (G (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹))]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    show e (cj p.1) * e (cj p.2) * h ((ι (cj p.1))⁻¹ * (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) * (ι (cj p.2))⁻¹)
      = e p.1 * e p.2 * h ((ι p.1)⁻¹ * x * (ι p.2)⁻¹)
    rw [hcj_apply, hcj_apply, hecl, hecl, ← hικ₀]
    congr 1
    rw [← hhc w k ((ι p.1)⁻¹ * x * (ι p.2)⁻¹), ← hικ₀]
    congr 1
    simp only [map_mul, map_inv]
    group

  ·
    have hWι : ∀ (p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (y : GL (Fin 2) (InfiniteAdeleRing F)),
        W ((ι p.1)⁻¹ * y * (ι p.2)⁻¹) = W y := by
      intro p y
      simp only [hW, map_mul, map_inv, hdet1, inv_one, one_mul, mul_one]
    have hN1 : NumberField.TateGlobal.ideleNorm F 1 = 1 := by
      have h := NumberField.TateGlobal.ideleNorm_mul (F := F) 1 1
      rw [mul_one] at h
      have hp := NumberField.TateGlobal.ideleNorm_pos (F := F) 1
      nlinarith [h, hp]
    have hWinv : W x⁻¹ * W x = 1 := by
      simp only [hW, map_inv]
      have hpos := NumberField.TateGlobal.ideleNorm_pos (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x))
      have hinv : NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x))⁻¹
          = (NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x)))⁻¹ := by
        have h := NumberField.TateGlobal.ideleNorm_mul (F := F)
          (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x))⁻¹ (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x))
        rw [inv_mul_cancel, hN1] at h
        field_simp
        linarith
      rw [hinv, Real.inv_rpow hpos.le, ← Complex.ofReal_mul, inv_mul_cancel₀ (Real.rpow_pos_of_pos hpos _).ne',
        Complex.ofReal_one]
    have hWreal : ∀ y, conj (W y) = W y := fun y => by simp only [hW, Complex.conj_ofReal]
    have hconjh : ∀ z : GL (Fin 2) (InfiniteAdeleRing F), conj (h z) = h z⁻¹ * W z := by
      intro z
      have := congrArg conj (hhf z)
      rw [map_mul] at this
      rw [this, Complex.conj_conj]
      show h z⁻¹ * conj (W z) = h z⁻¹ * W z
      rw [hWreal]

    set H : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ := fun p => e p.1⁻¹ * e p.2⁻¹ * h (ι p.2 * x * ι p.1) with hH
    have hstep : conj (∫ p, G x⁻¹ p ∂(μ.prod μ)) * W x = ∫ p, H p ∂(μ.prod μ) := by
      rw [← integral_conj, ← integral_mul_const]
      refine integral_congr_ae (ae_of_all _ fun p => ?_)
      show conj (e p.1 * e p.2 * h ((ι p.1)⁻¹ * x⁻¹ * (ι p.2)⁻¹)) * W x = e p.1⁻¹ * e p.2⁻¹ * h (ι p.2 * x * ι p.1)
      rw [map_mul, map_mul, ← hefl, ← hefl, hconjh, hWι p x⁻¹]
      rw [show ((ι p.1)⁻¹ * x⁻¹ * (ι p.2)⁻¹)⁻¹ = ι p.2 * x * ι p.1 by group]
      rw [mul_assoc, mul_assoc (h (ι p.2 * x * ι p.1)), hWinv, mul_one]

    set Ψ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) ≃ᵐ (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) :=
      MeasurableEquiv.prodComm.trans (MeasurableEquiv.prodCongr (MeasurableEquiv.inv (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (MeasurableEquiv.inv (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion))) with hΨ
    have hΨ_apply : ∀ q : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), Ψ q = (q.2⁻¹, q.1⁻¹) := fun q => rfl
    have hΨmp : MeasurePreserving Ψ (μ.prod μ) (μ.prod μ) :=
      ((Measure.measurePreserving_inv μ).prod (Measure.measurePreserving_inv μ)).comp
        (Measure.measurePreserving_swap (μ := μ) (ν := μ))
    show ∫ p, G x p ∂(μ.prod μ) = conj (∫ p, G x⁻¹ p ∂(μ.prod μ)) * W x
    rw [hstep, ← hΨmp.integral_comp' H]
    refine integral_congr_ae (ae_of_all _ fun q => ?_)
    show e q.1 * e q.2 * h ((ι q.1)⁻¹ * x * (ι q.2)⁻¹) = H (Ψ q)
    rw [hΨ_apply]
    show e q.1 * e q.2 * h ((ι q.1)⁻¹ * x * (ι q.2)⁻¹) = e q.2⁻¹⁻¹ * e q.1⁻¹⁻¹ * h (ι q.1⁻¹ * x * ι q.2⁻¹)
    rw [inv_inv, inv_inv, map_inv, map_inv, mul_comm (e q.2) (e q.1)]

end S_AutomorphicForm_integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat
end P2MW
export P2MW.S_AutomorphicForm_integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat (solution)
