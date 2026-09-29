-- Prove2me | solution 1 for AutomorphicForm.exists_sum_mul_prod_localZeta_bottomRow_eq_of_isArchKFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/9e61d29b-0d42-59a0-b3d0-1bfae5b1da78

import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Theorems.Thm_AutomorphicForm_exists_eq_sum_prod_archComponent_of_isArchKFinite
import Theorems.Thm_AutomorphicForm_exists_sum_mul_localZeta_bottomRow_eq_of_rightTranslatesSpanFinite
import Theorems.Thm_NumberField_InfiniteAdeleRing_exists_schwartzMap_apply_ringEquiv_mixedSpace_eq_prod_of_polynomial_mul_gaussian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_sum_mul_prod_localZeta_bottomRow_eq_of_isArchKFinite

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicFourier NumberField.AdelicLevel NumberField.TateGlobal
open NumberField.InfinitePlace AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped NNReal SchwartzMap

namespace R4A

variable {F : Type} [Field F] [NumberField F]

theorem continuous_archUnitHom (w : InfinitePlace F) : Continuous (archUnitHom (F := F) w) := by
  classical
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun a : (w.Completion)ˣ =>
      ((Function.update (1 : InfiniteAdeleRing F) w (a : w.Completion), (1 : FiniteAdeleRing (𝓞 F) F)) :
        AdeleRing (𝓞 F) F)
    exact (continuous_const.update w Units.continuous_val).prodMk continuous_const
  · show Continuous fun a : (w.Completion)ˣ =>
      ((Function.update (1 : InfiniteAdeleRing F) w ((a⁻¹ : (w.Completion)ˣ) : w.Completion),
        (1 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F)
    exact (continuous_const.update w Units.continuous_coe_inv).prodMk continuous_const

theorem continuous_archLocalChar (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ)) (w : InfinitePlace F) :
    Continuous fun x : (w.Completion)ˣ => ((archLocalChar μ w x : ℂˣ) : ℂ) :=
  hμc.comp (continuous_archUnitHom w)

theorem norm_archLocalChar (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 F) F μ) (w : InfinitePlace F)
    (x : (w.Completion)ˣ) : ‖((archLocalChar μ w x : ℂˣ) : ℂ)‖ = 1 :=
  hμ _

theorem archLocalChar_mul_inv (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (w : InfinitePlace F) :
    archLocalChar (μ * ν⁻¹) w = archLocalChar μ w * (archLocalChar ν w)⁻¹ :=
  MonoidHom.ext fun _ => rfl

theorem det_eq_prod_archUnitHom (k : AdelicGL2 (𝓞 F) F) (hk : glFin (𝓞 F) F k = 1) :
    Matrix.GeneralLinearGroup.det k
      = ∏ w : InfinitePlace F, archUnitHom w (Matrix.GeneralLinearGroup.det (archComponent F w (glArch (𝓞 F) F k))) := by
  classical
  apply Units.ext
  rw [Units.coe_prod]
  refine Prod.ext ?_ ?_
  · have h1 : ∀ x : AdeleRing (𝓞 F) F, x.1 = adeleArch (𝓞 F) F x := fun x => rfl
    rw [h1, h1, map_prod]
    funext v
    have h3 : ∀ y : InfiniteAdeleRing F, y v = archEval F v y := fun y => rfl
    rw [h3 (adeleArch (𝓞 F) F _), h3 (∏ x, _), map_prod, Finset.prod_eq_single v (fun w _ hw => by
        show Function.update (1 : InfiniteAdeleRing F) w _ v = 1
        rw [Function.update_of_ne (Ne.symm hw)]; rfl)
      (fun h => (h (Finset.mem_univ v)).elim)]
    show ((Matrix.GeneralLinearGroup.det k : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 v
      = Function.update (1 : InfiniteAdeleRing F) v
          ((Matrix.GeneralLinearGroup.det (archComponent F v (glArch (𝓞 F) F k)) : (v.Completion)ˣ) : v.Completion) v
    rw [Function.update_self, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
    have : (archComponent F v (glArch (𝓞 F) F k) : Matrix (Fin 2) (Fin 2) v.Completion)
        = ((archEval F v).comp (adeleArch (𝓞 F) F)).mapMatrix (k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
      ext i j; rfl
    rw [this, ← RingHom.map_det]; rfl
  · have h2 : ∀ x : AdeleRing (𝓞 F) F, x.2 = adeleFin (𝓞 F) F x := fun x => rfl
    rw [h2, h2, map_prod]
    have hR : (∏ x : InfinitePlace F, adeleFin (𝓞 F) F
        ((archUnitHom x (Matrix.GeneralLinearGroup.det (archComponent F x (glArch (𝓞 F) F k))) :
          (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) = 1 :=
      Finset.prod_eq_one fun w _ => rfl
    rw [hR]
    show ((Matrix.GeneralLinearGroup.det k : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    have : (glFin (𝓞 F) F k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))
        = (adeleFin (𝓞 F) F).mapMatrix (k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
      ext i j; rfl
    have h := congrArg Matrix.det this
    rw [hk, Units.val_one, Matrix.det_one, ← RingHom.map_det] at h
    exact h.symm

theorem mu_det_eq_prod (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (k : AdelicGL2 (𝓞 F) F) (hk : glFin (𝓞 F) F k = 1) :
    ((μ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
      = ∏ w : InfinitePlace F, ((archLocalChar μ w
          (Matrix.GeneralLinearGroup.det (archComponent F w (glArch (𝓞 F) F k))) : ℂˣ) : ℂ) := by
  rw [det_eq_prod_archUnitHom k hk, map_prod, Units.coe_prod]; rfl

open scoped Classical in
theorem main
    [∀ w : InfinitePlace F, MeasurableSpace w.Completion] [∀ w : InfinitePlace F, BorelSpace w.Completion]
    (μa : (w : InfinitePlace F) → Measure w.Completion) [∀ w, (μa w).IsAddHaarMeasure]
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
    (U : AdelicGL2 (𝓞 F) F → ℂ) (hUc : Continuous U) (hUK : IsArchKFinite F U)
    (hUB : ∀ (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F),
        glFin (𝓞 F) F b = 1 →
        (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F b))) →
        ∀ g : AdelicGL2 (𝓞 F) F,
          U (b * g) = ((μ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
            * ((ν (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) * U g) :
    ∃ (m : ℕ) (g : Fin m → 𝓢((Fin 2 → mixedEmbedding.mixedSpace F), ℂ))
      (Φa : Fin m → (w : InfinitePlace F) → (Fin 2 → w.Completion) → ℂ)
      (E : Fin m → ℂ → ℂ),
      (∀ j, Differentiable ℂ (E j)) ∧
      (∀ j (y : Fin 2 → InfiniteAdeleRing F),
        g j (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i)) = ∏ w, Φa j w (fun i => y i w)) ∧
      ∀ (z : ℂ), 0 < z.re →
        ∀ (k : AdelicGL2 (𝓞 F) F), k ∈ adelicMaximalCompact F → glFin (𝓞 F) F k = 1 →
          (∑ j, E j z * (((μ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
              * ∏ w, LanglandsTunnell.TateLocal.localZeta (μa w)
                  (fun t => Φa j w (fun i => t
                    * (archComponent F w (glArch (𝓞 F) F k) : Matrix (Fin 2) (Fin 2) w.Completion) 1 i))
                  (archLocalChar (μ * ν⁻¹) w) z))
            = U k := by
  obtain ⟨m, f, hfc, hfK, hfB, hU⟩ :=
    AutomorphicForm.exists_eq_sum_prod_archComponent_of_isArchKFinite F μ ν hμc hνc U hUc hUK hUB
  have hloc : ∀ (j : Fin m) (w : InfinitePlace F),
      ∃ (m' : ℕ) (Φ : Fin m' → (Fin 2 → w.Completion) → ℂ) (e : Fin m' → ℂ → ℂ),
        (∀ l, Differentiable ℂ (e l)) ∧
        (∀ l, ∃ P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ, ∀ y : Fin 2 → w.Completion,
          Φ l y = MvPolynomial.eval
                (Sum.elim (fun i => Completion.extensionEmbedding w (y i))
                  (fun i => starRingEnd ℂ (Completion.extensionEmbedding w (y i)))) P
              * Complex.exp (-(Real.pi : ℂ) * ∑ i, (((‖y i‖ ^ 2 : ℝ)) : ℂ))) ∧
        ∀ z : ℂ, 0 < z.re →
          ∀ k : GL (Fin 2) w.Completion, IsRowIsometry k →
            (∑ l, e l z * (((archLocalChar μ w (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
                * LanglandsTunnell.TateLocal.localZeta (μa w)
                    (fun t => Φ l (fun i => t * (k : Matrix (Fin 2) (Fin 2) w.Completion) 1 i))
                    (archLocalChar μ w * (archLocalChar ν w)⁻¹) z))
              = f j w k :=
    fun j w => AutomorphicForm.exists_sum_mul_localZeta_bottomRow_eq_of_rightTranslatesSpanFinite F w (μa w)
      (archLocalChar μ w) (archLocalChar ν w) (norm_archLocalChar μ hμ w) (norm_archLocalChar ν hν w)
      (continuous_archLocalChar μ hμc w) (continuous_archLocalChar ν hνc w) (f j w) (hfc j w) (hfK j w) (hfB j w)
  choose m' Φ e he hP hZ using hloc

  let J : Type := Σ j : Fin m, ((w : InfinitePlace F) → Fin (m' j w))
  let eqv : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  have hjoint : ∀ q : J, ∃ g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace F), ℂ),
      ∀ y : Fin 2 → InfiniteAdeleRing F,
        g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i)) = ∏ w, Φ q.1 w (q.2 w) (fun i => y i w) :=
    fun q => NumberField.InfiniteAdeleRing.exists_schwartzMap_apply_ringEquiv_mixedSpace_eq_prod_of_polynomial_mul_gaussian
      F (fun w => Φ q.1 w (q.2 w)) (fun w => hP q.1 w (q.2 w))
  choose g hg using hjoint
  refine ⟨Fintype.card J, fun r => g (eqv.symm r), fun r w => Φ (eqv.symm r).1 w ((eqv.symm r).2 w),
    fun r z => ∏ w, e (eqv.symm r).1 w ((eqv.symm r).2 w) z, fun r => ?_, fun r y => hg _ y,
    fun z hz k hk hkf => ?_⟩
  · exact Differentiable.fun_finsetProd fun w _ => he _ w _

  set kw : (w : InfinitePlace F) → GL (Fin 2) w.Completion := fun w => archComponent F w (glArch (𝓞 F) F k) with hkw
  set T : J → ℂ := fun q => (∏ w, e q.1 w (q.2 w) z) * (((μ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
      * ∏ w, LanglandsTunnell.TateLocal.localZeta (μa w)
          (fun t => Φ q.1 w (q.2 w) (fun i => t * (kw w : Matrix (Fin 2) (Fin 2) w.Completion) 1 i))
          (archLocalChar (μ * ν⁻¹) w) z) with hT
  have hreidx : (∑ r : Fin (Fintype.card J), T (eqv.symm r)) = ∑ q : J, T q := Equiv.sum_comp eqv.symm T
  show (∑ r : Fin (Fintype.card J), T (eqv.symm r)) = U k
  rw [hreidx, hU k hk hkf, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_

  have hterm : ∀ l : (w : InfinitePlace F) → Fin (m' j w), T ⟨j, l⟩
      = ∏ w, (e j w (l w) z * (((archLocalChar μ w (Matrix.GeneralLinearGroup.det (kw w)) : ℂˣ) : ℂ)
          * LanglandsTunnell.TateLocal.localZeta (μa w)
              (fun t => Φ j w (l w) (fun i => t * (kw w : Matrix (Fin 2) (Fin 2) w.Completion) 1 i))
              (archLocalChar μ w * (archLocalChar ν w)⁻¹) z)) := by
    intro l
    simp only [hT, mu_det_eq_prod μ k hkf, archLocalChar_mul_inv, Finset.prod_mul_distrib]
    rfl
  rw [Finset.sum_congr rfl fun l _ => hterm l]
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun w => (Finset.univ : Finset (Fin (m' j w))))
    (fun w lw => e j w lw z * (((archLocalChar μ w (Matrix.GeneralLinearGroup.det (kw w)) : ℂˣ) : ℂ)
      * LanglandsTunnell.TateLocal.localZeta (μa w)
          (fun t => Φ j w lw (fun i => t * (kw w : Matrix (Fin 2) (Fin 2) w.Completion) 1 i))
          (archLocalChar μ w * (archLocalChar ν w)⁻¹) z))]
  exact Finset.prod_congr rfl fun w _ => hZ j w z hz (kw w) (hk.2 w)

end R4A

end

open MeasureTheory NumberField NumberField.AdelicFourier NumberField.AdelicLevel NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped NNReal SchwartzMap

open scoped Classical in
theorem solution
    (F : Type) [Field F] [NumberField F]
    [∀ w : InfinitePlace F, MeasurableSpace w.Completion] [∀ w : InfinitePlace F, BorelSpace w.Completion]
    (μa : (w : InfinitePlace F) → Measure w.Completion) [∀ w, (μa w).IsAddHaarMeasure]
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
    (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
    (U : AdelicGL2 (𝓞 F) F → ℂ) (_hUc : Continuous U) (_hUK : IsArchKFinite F U)
    (_hUB : ∀ (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F),
        glFin (𝓞 F) F b = 1 →
        (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F b))) →
        ∀ g : AdelicGL2 (𝓞 F) F,
          U (b * g) = ((μ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
            * ((ν (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) * U g) :
    ∃ (m : ℕ) (g : Fin m → 𝓢((Fin 2 → mixedEmbedding.mixedSpace F), ℂ))
      (Φa : Fin m → (w : InfinitePlace F) → (Fin 2 → w.Completion) → ℂ)
      (E : Fin m → ℂ → ℂ),
      (∀ j, Differentiable ℂ (E j)) ∧
      (∀ j (y : Fin 2 → InfiniteAdeleRing F),
        g j (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i)) = ∏ w, Φa j w (fun i => y i w)) ∧
      ∀ (z : ℂ), 0 < z.re →
        ∀ (k : AdelicGL2 (𝓞 F) F), k ∈ adelicMaximalCompact F → glFin (𝓞 F) F k = 1 →
          (∑ j, E j z * (((μ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
              * ∏ w, LanglandsTunnell.TateLocal.localZeta (μa w)
                  (fun t => Φa j w (fun i => t
                    * (archComponent F w (glArch (𝓞 F) F k) : Matrix (Fin 2) (Fin 2) w.Completion) 1 i))
                  (archLocalChar (μ * ν⁻¹) w) z))
            = U k :=
  R4A.main μa μ ν _hμ _hν _hμc _hνc U _hUc _hUK _hUB

end S_AutomorphicForm_exists_sum_mul_prod_localZeta_bottomRow_eq_of_isArchKFinite
end P2MW
export P2MW.S_AutomorphicForm_exists_sum_mul_prod_localZeta_bottomRow_eq_of_isArchKFinite (solution)
