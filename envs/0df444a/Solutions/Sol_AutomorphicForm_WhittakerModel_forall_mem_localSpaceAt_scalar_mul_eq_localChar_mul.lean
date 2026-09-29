-- Prove2me | solution 1 for AutomorphicForm.WhittakerModel.forall_mem_localSpaceAt_scalar_mul_eq_localChar_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/fba96c2a-5515-5b5c-a970-3c5c79b98aac

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.Analysis.MellinTransform
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange

import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_AdelicDock_LocalEmbedding

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_WhittakerModel_forall_mem_localSpaceAt_scalar_mul_eq_localChar_mul

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open scoped nonZeroDivisors

noncomputable section

namespace Ws23Central

open Matrix IsDedekindDomain NumberField AutomorphicForm

abbrev G2 : Type := AdelicGL2 (𝓞 ℚ) ℚ
abbrev 𝔸 : Type := AdeleRing (𝓞 ℚ) ℚ

abbrev archM (g : G2) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ) :=
  (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 2) (Fin 2) 𝔸)
abbrev finM (w : HeightOneSpectrum (𝓞 ℚ)) (g : G2) : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ) :=
  (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix
    ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 2) (Fin 2) 𝔸))

theorem archM_mul (g h : G2) : archM (g * h) = archM g * archM h := (RingHom.mapMatrix _).map_mul _ _
theorem finM_mul (w : HeightOneSpectrum (𝓞 ℚ)) (g h : G2) : finM w (g * h) = finM w g * finM w h := by
  show (RingHom.mapMatrix _) ((RingHom.mapMatrix _) (_ * _)) = _
  rw [map_mul, map_mul]

theorem eq_of_components {g h : G2} (ha : archM g = archM h) (hf : ∀ w, finM w g = finM w h) : g = h :=
  Units.ext (AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ ha
    (AdelicDock.matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ hf))

abbrev PE (p : HeightOneSpectrum (𝓞 ℚ)) (x : GL (Fin 2) (p.adicCompletion ℚ)) : G2 :=
  AdelicDock.finEmbed (𝓞 ℚ) ℚ (AdelicDock.localEmbed (𝓞 ℚ) ℚ p x)

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem archM_PE (x : GL (Fin 2) (p.adicCompletion ℚ)) : archM (PE p x) = 1 := by
  show (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix _ = 1
  rw [AdelicDock.coe_finEmbed, AdelicDock.mapMatrix_arch_finMat]

theorem finM_PE_self (x : GL (Fin 2) (p.adicCompletion ℚ)) : finM p (PE p x) = x := by
  show (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p).mapMatrix ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix _) = _
  rw [AdelicDock.coe_finEmbed, AdelicDock.mapMatrix_fin_finMat, AdelicDock.coe_localEmbed,
    AdelicDock.mapMatrix_localMat_self]

theorem finM_PE_of_ne (x : GL (Fin 2) (p.adicCompletion ℚ)) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ p) :
    finM w (PE p x) = 1 := by
  show (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix _) = _
  rw [AdelicDock.coe_finEmbed, AdelicDock.mapMatrix_fin_finMat, AdelicDock.coe_localEmbed,
    AdelicDock.mapMatrix_localMat_of_ne _ _ _ _ hw]

theorem mapMatrix_scalar {A B : Type*} [Semiring A] [Semiring B] (f : A →+* B) (a : A) :
    f.mapMatrix (Matrix.scalar (Fin 2) a) = Matrix.scalar (Fin 2) (f a) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Matrix.scalar_apply]
  · simp [Matrix.scalar_apply, h]

theorem coe_GLscalar {R : Type*} [CommRing R] (z : Rˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) z : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      Matrix.scalar (Fin 2) (z : R) := rfl

theorem PE_scalar (z : (p.adicCompletion ℚ)ˣ) :
    PE p (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Units.map (AdelicLevel.finIncl (𝓞 ℚ) ℚ) (AdelicLevel.localUnit (𝓞 ℚ) ℚ p z)) := by
  refine eq_of_components ?_ (fun w => ?_)
  · rw [archM_PE]
    show (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) = (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix _
    rw [coe_GLscalar, mapMatrix_scalar, Units.coe_map, AdelicLevel.adeleArch_apply]
    show (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) = Matrix.scalar (Fin 2) (AdelicLevel.finIncl (𝓞 ℚ) ℚ _).1
    rw [show (AdelicLevel.finIncl (𝓞 ℚ) ℚ (AdelicLevel.localUnit (𝓞 ℚ) ℚ p z : FiniteAdeleRing (𝓞 ℚ) ℚ)).1 = 1 from rfl,
      map_one]
  · show finM w _ = (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix _)
    rw [coe_GLscalar, mapMatrix_scalar, mapMatrix_scalar, Units.coe_map, AdelicLevel.adeleFin_apply,
      AdelicLevel.finAdeleEval_apply]
    by_cases hw : w = p
    · subst hw
      rw [finM_PE_self, coe_GLscalar]
      congr 1
      exact (AdelicLevel.localUnit_apply_self (𝓞 ℚ) ℚ _ _).symm
    · rw [finM_PE_of_ne _ _ hw]
      rw [show (AdelicLevel.finIncl (𝓞 ℚ) ℚ (AdelicLevel.localUnit (𝓞 ℚ) ℚ p z : FiniteAdeleRing (𝓞 ℚ) ℚ)).2 =
          (AdelicLevel.localUnit (𝓞 ℚ) ℚ p z : FiniteAdeleRing (𝓞 ℚ) ℚ) from rfl,
        AdelicLevel.localUnit_apply_of_ne (𝓞 ℚ) ℚ _ _ hw, map_one]

theorem GLscalar_comm (Z : 𝔸ˣ) (g : G2) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) Z * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) Z :=
  Units.ext (Matrix.scalar_commute (Z : 𝔸) (fun r => Commute.all _ r) (g : Matrix (Fin 2) (Fin 2) 𝔸)).eq

end Ws23Central

end

open Ws23Central in
theorem solution
    (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (x : AdelicGL2 (𝓞 ℚ) ℚ),
      φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * x) = ((ξ z : ℂˣ) : ℂ) * φ x)
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ pins ψ p φ,
      ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        W (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((localChar ξ p z : ℂˣ) : ℂ) * W g := by
  intro W hW
  refine Submodule.span_induction
    (p := fun (W : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) _ =>
      ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        W (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((localChar ξ p z : ℂˣ) : ℂ) * W g) ?_ ?_ ?_ ?_ hW
  · rintro _ ⟨h, rfl⟩ z g
    set Z : (AdeleRing (𝓞 ℚ) ℚ)ˣ := Units.map (AdelicLevel.finIncl (𝓞 ℚ) ℚ) (AdelicLevel.localUnit (𝓞 ℚ) ℚ p z)
      with hZ
    have hξ : ((localChar ξ p z : ℂˣ) : ℂ) = ((ξ Z : ℂˣ) : ℂ) := rfl

    have hcen' : ∀ y : AdelicGL2 (𝓞 ℚ) ℚ,
        φ (Matrix.GeneralLinearGroup.scalar (Fin 2) Z * y * h) = ((ξ Z : ℂˣ) : ℂ) * φ (y * h) := fun y => by
      rw [mul_assoc]; exact hcen Z (y * h)
    show whittakerCoefficient ℚ pins ψ (fun x => φ (x * h)) 1
        (AdelicDock.finEmbed (𝓞 ℚ) ℚ (AdelicDock.localEmbed (𝓞 ℚ) ℚ p (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g))) =
      ((localChar ξ p z : ℂˣ) : ℂ) * whittakerCoefficient ℚ pins ψ (fun x => φ (x * h)) 1
        (AdelicDock.finEmbed (𝓞 ℚ) ℚ (AdelicDock.localEmbed (𝓞 ℚ) ℚ p g))
    rw [map_mul, map_mul, hξ]
    change whittakerCoefficient ℚ pins ψ (fun x => φ (x * h)) 1 (PE p (Matrix.GeneralLinearGroup.scalar (Fin 2) z) * PE p g) =
      ((ξ Z : ℂˣ) : ℂ) * whittakerCoefficient ℚ pins ψ (fun x => φ (x * h)) 1 (PE p g)
    rw [PE_scalar, ← hZ]
    simp only [whittakerCoefficient]
    have hcomm : ∀ x : AdeleRing (𝓞 ℚ) ℚ,
        φ (unipotentGL2 x * (Matrix.GeneralLinearGroup.scalar (Fin 2) Z * PE p g) * h) =
          ((ξ Z : ℂˣ) : ℂ) * φ (unipotentGL2 x * PE p g * h) := fun x => by
      rw [← mul_assoc, ← GLscalar_comm Z (unipotentGL2 x), mul_assoc (Matrix.GeneralLinearGroup.scalar (Fin 2) Z)]
      exact hcen' _
    simp_rw [hcomm, mul_assoc]
    exact MeasureTheory.integral_const_mul _ _
  · intro z g
    simp
  · intro x y _ _ hx hy z g
    simp only [Pi.add_apply, hx z g, hy z g, mul_add]
  · intro a x _ hx z g
    simp only [Pi.smul_apply, hx z g, smul_eq_mul]
    ring

end S_AutomorphicForm_WhittakerModel_forall_mem_localSpaceAt_scalar_mul_eq_localChar_mul
end P2MW
export P2MW.S_AutomorphicForm_WhittakerModel_forall_mem_localSpaceAt_scalar_mul_eq_localChar_mul (solution)
