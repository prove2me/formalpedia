-- Prove2me | solution 1 for AutomorphicForm.addChar_eq_one_on_integers_off_of_whittakerCoefficient_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/c9e053ba-501c-58b6-87a2-bc686b1c0126

import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_CarrierPins
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_addChar_eq_one_on_integers_off_of_whittakerCoefficient_ne_zero

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Ws23
namespace C6AB
open Matrix MeasureTheory
open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AdelicDock UnramifiedWhittaker

variable (F : Type) [Field F] [NumberField F]

theorem globalPoints_unipotentGL2 (β : F) :
    globalPoints (𝓞 F) F (unipotentGL2 β) = unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [globalPoints, unipotentGL2]

theorem map_unipotentGL2_integers (v : HeightOneSpectrum (𝓞 F)) (r : v.adicCompletionIntegers F) :
    Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) (unipotentGL2 r) =
      unipotentGL2 (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [unipotentGL2]

theorem unipotent_eq_unipotentGL2 {K : Type*} [Field K] (x : K) : unipotent x = unipotentGL2 x := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [unipotent, unipotentGL2]

noncomputable def adeleAt (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) : AdeleRing (𝓞 F) F :=
  ((0 : InfiniteAdeleRing F), splice (𝓞 F) F v 0 x)

theorem splice_apply_eq_self (v : HeightOneSpectrum (𝓞 F)) (a : FiniteAdeleRing (𝓞 F) F) :
    splice (𝓞 F) F v a (a v) = a := by
  classical
  refine Subtype.ext (funext fun w => ?_)
  by_cases hw : w = v
  · subst hw
    exact splice_apply_self (𝓞 F) F w a (a w)
  · exact splice_apply_of_ne (𝓞 F) F v a (a v) hw

theorem coe_placeEmbed_apply (v : HeightOneSpectrum (𝓞 F)) (k : GL (Fin 2) (v.adicCompletion F)) (i j : Fin 2) :
    ((placeEmbed F v k : GL (Fin 2) (AdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        splice (𝓞 F) F v ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j)
          ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j)) : AdeleRing (𝓞 F) F) := by
  rfl

theorem placeEmbed_unipotent (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    placeEmbed F v (unipotent x) = unipotentGL2 (adeleAt F v x) := by
  refine Units.ext ?_
  ext i j
  rw [coe_placeEmbed_apply, unipotentGL2_coe]
  have hu : ((unipotent x : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) =
      !![1, x; 0, 1] := rfl
  rw [hu]
  have h1 : splice (𝓞 F) F v (1 : FiniteAdeleRing (𝓞 F) F) 1 = 1 := by
    have := splice_apply_eq_self F v 1
    exact this
  have h0 : splice (𝓞 F) F v (0 : FiniteAdeleRing (𝓞 F) F) 0 = 0 := by
    have := splice_apply_eq_self F v 0
    exact this
  fin_cases i <;> fin_cases j
  · show (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 0 0, splice (𝓞 F) F v ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 0) ((!![(1 : v.adicCompletion F), x; 0, 1]) 0 0)) : AdeleRing (𝓞 F) F) = !![(1 : AdeleRing (𝓞 F) F), adeleAt F v x; 0, 1] 0 0
    simp only [Matrix.one_apply_eq, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one]
    rw [h1]
    rfl
  · show (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 0 1, splice (𝓞 F) F v ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 1) ((!![(1 : v.adicCompletion F), x; 0, 1]) 0 1)) : AdeleRing (𝓞 F) F) = !![(1 : AdeleRing (𝓞 F) F), adeleAt F v x; 0, 1] 0 1
    simp only [Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rfl
  · show (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 1 0, splice (𝓞 F) F v ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0) ((!![(1 : v.adicCompletion F), x; 0, 1]) 1 0)) : AdeleRing (𝓞 F) F) = !![(1 : AdeleRing (𝓞 F) F), adeleAt F v x; 0, 1] 1 0
    simp only [Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [h0]
    rfl
  · show (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 1 1, splice (𝓞 F) F v ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1) ((!![(1 : v.adicCompletion F), x; 0, 1]) 1 1)) : AdeleRing (𝓞 F) F) = !![(1 : AdeleRing (𝓞 F) F), adeleAt F v x; 0, 1] 1 1
    simp only [Matrix.one_apply_eq, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [h1]
    rfl

theorem gl_eq_of_components (g h : GL (Fin 2) (AdeleRing (𝓞 F) F)) (harch : glArch (𝓞 F) F g = glArch (𝓞 F) F h)
    (hfin : ∀ w : HeightOneSpectrum (𝓞 F), finComponent (𝓞 F) F w (glFin (𝓞 F) F g) =
      finComponent (𝓞 F) F w (glFin (𝓞 F) F h)) : g = h := by
  refine Units.ext (matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 F) F ?_ ?_)
  · exact congrArg (fun x : GL (Fin 2) (InfiniteAdeleRing F) => (x : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))) harch
  · refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 F) F fun w => ?_
    exact congrArg (fun x : GL (Fin 2) (w.adicCompletion F) => (x : Matrix (Fin 2) (Fin 2) (w.adicCompletion F))) (hfin w)

theorem placeEmbed_mul_comm_of_finComponent_eq_one (v : HeightOneSpectrum (𝓞 F)) (k : GL (Fin 2) (v.adicCompletion F))
    (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) (hg : finComponent (𝓞 F) F v (glFin (𝓞 F) F g) = 1) :
    placeEmbed F v k * g = g * placeEmbed F v k := by
  refine gl_eq_of_components F _ _ ?_ fun w => ?_
  · rw [map_mul, map_mul, placeEmbed, MonoidHom.comp_apply, glArch_finEmbed, one_mul, mul_one]
  · rw [map_mul, map_mul, map_mul, map_mul, placeEmbed, MonoidHom.comp_apply, glFin_finEmbed]
    by_cases hw : w = v
    · subst hw
      rw [hg, mul_one, one_mul]
    · rw [finComponent_localEmbed_of_ne (𝓞 F) F _ k hw, one_mul, mul_one]

end Ws23.C6AB

open NumberField NumberField.AdelicLevel NumberField.AdelicBox MeasureTheory
open AutomorphicForm IsDedekindDomain UnramifiedWhittaker

theorem solution
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (G₀ : AdelicGL2 (𝓞 F) F → ℂ)
    (hleft : ∀ (β : F) (h : AdelicGL2 (𝓞 F) F), G₀ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * h) = G₀ h)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hKS : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
      ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers F)) (g : AdelicGL2 (𝓞 F) F),
        G₀ (g * placeEmbed F v
          (Matrix.GeneralLinearGroup.map
            (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) kv)) = G₀ g)
    (g₀ : AdelicGL2 (𝓞 F) F)
    (hg₀ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ∀ i j : Fin 2,
      ((g₀ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v =
        ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v)
    (a₀ : (AdeleRing (𝓞 F) F)ˣ)
    (ha₀ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ((a₀ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1)
    (hW : whittakerCoefficient F (productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ G₀ 1 (diagOne a₀ * g₀) ≠ 0) :
    ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ∀ r : v.adicCompletionIntegers F,
      ψ (@id (AdeleRing (𝓞 F) F) ((0 : InfiniteAdeleRing F),
        AdelicDock.splice (𝓞 F) F v 0 (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r))) = 1 := by
  classical
  intro v hv r
  set x : v.adicCompletion F := algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r with hx

  have hper : ∀ (β : F) (u : AdeleRing (𝓞 F) F),
      G₀ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + u) * (diagOne a₀ * g₀)) =
        G₀ (unipotentGL2 u * (diagOne a₀ * g₀)) := by
    intro β u
    rw [unipotentGL2_add, mul_assoc, hleft]
  have hcov := AutomorphicForm.whittakerCoefficient_unipotentGL2_mul F D
    (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
    ψ hψ.principalInvariant G₀ (diagOne a₀ * g₀) hper 1 (Ws23.C6AB.adeleAt F v x)
  rw [map_one, one_mul, ← Ws23.C6AB.placeEmbed_unipotent] at hcov

  have hfc_g₀ : finComponent (𝓞 F) F v (glFin (𝓞 F) F g₀) = 1 := by
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [finComponent_apply, glFin_apply, hg₀ v hv i j]
    fin_cases i <;> fin_cases j <;> rfl
  have hfc_a₀ : finComponent (𝓞 F) F v (glFin (𝓞 F) F (diagOne a₀)) = 1 := by
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [finComponent_apply, glFin_apply, diagOne_coe_apply]
    fin_cases i <;> fin_cases j
    · simpa using ha₀ v hv
    · rfl
    · rfl
    · rfl
  have hfc : finComponent (𝓞 F) F v (glFin (𝓞 F) F (diagOne a₀ * g₀)) = 1 := by
    rw [map_mul, map_mul, hfc_a₀, hfc_g₀, one_mul]
  have hcomm := Ws23.C6AB.placeEmbed_mul_comm_of_finComponent_eq_one F v (unipotent x) (diagOne a₀ * g₀) hfc
  rw [hcomm] at hcov

  have hinv : whittakerCoefficient F (productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ G₀ 1 (diagOne a₀ * g₀ * placeEmbed F v (unipotent x)) =
      whittakerCoefficient F (productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ G₀ 1 (diagOne a₀ * g₀) := by
    have hk : placeEmbed F v (unipotent x) = placeEmbed F v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) (unipotentGL2 r)) := by
      rw [Ws23.C6AB.map_unipotentGL2_integers, Ws23.C6AB.unipotent_eq_unipotentGL2]
    simp only [whittakerCoefficient]
    congr 1
    funext y
    rw [← mul_assoc, hk, hKS v hv]
  rw [hinv] at hcov

  have h2 : (ψ (Ws23.C6AB.adeleAt F v x) - 1) * whittakerCoefficient F (productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ G₀ 1 (diagOne a₀ * g₀) = 0 := by
    rw [sub_mul, one_mul, ← hcov, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact sub_eq_zero.mp h3
  · exact absurd h3 hW

end S_AutomorphicForm_addChar_eq_one_on_integers_off_of_whittakerCoefficient_ne_zero
end P2MW
export P2MW.S_AutomorphicForm_addChar_eq_one_on_integers_off_of_whittakerCoefficient_ne_zero (solution)
