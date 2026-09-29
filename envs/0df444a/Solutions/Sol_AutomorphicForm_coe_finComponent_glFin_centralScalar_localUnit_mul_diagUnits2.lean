-- Prove2me | solution 1 for AutomorphicForm.coe_finComponent_glFin_centralScalar_localUnit_mul_diagUnits2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/236d12e6-3d1c-517b-b272-b8ec0e59325e

import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_coe_finComponent_glFin_centralScalar_localUnit_mul_diagUnits2

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (t : (v.adicCompletion K)ˣ) (u : Kˣ) :
    ((AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K
        (AutomorphicForm.centralScalar (𝓞 K) K
            (Units.map (finIncl (𝓞 K) K : FiniteAdeleRing (𝓞 K) K →* AdeleRing (𝓞 K) K) (localUnit (𝓞 K) K v t)) *
          diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) :
        GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      Matrix.diagonal ![(t : v.adicCompletion K) * algebraMap K (v.adicCompletion K) (u : K), (t : v.adicCompletion K)]  := by
  classical
  have h0 : (0 : AdeleRing (𝓞 K) K).2 v = 0 := rfl
  have h1 : (1 : AdeleRing (𝓞 K) K).2 v = 1 := rfl
  ext i j : 1
  rw [AdelicLevel.finComponent_apply, AdelicLevel.glFin_apply, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have hz : ∀ i j : Fin 2, ((AutomorphicForm.centralScalar (𝓞 K) K
      (Units.map (finIncl (𝓞 K) K : FiniteAdeleRing (𝓞 K) K →* AdeleRing (𝓞 K) K) (localUnit (𝓞 K) K v t)) :
        GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      if i = j then ((finIncl (𝓞 K) K (localUnit (𝓞 K) K v t : FiniteAdeleRing (𝓞 K) K)) : AdeleRing (𝓞 K) K) else 0 := by
    intro i j
    change Matrix.scalar (Fin 2) _ i j = _
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    rfl
  have hd : ∀ i j : Fin 2, ((diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1 :
      GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      (!![algebraMap K (AdeleRing (𝓞 K) K) (u : K), 0; 0, 1] : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j :=
    fun _ _ => rfl
  have ht : ((finIncl (𝓞 K) K (localUnit (𝓞 K) K v t : FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K)).2 v =
      (t : v.adicCompletion K) := by
    show ((localUnit (𝓞 K) K v t : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v = (t : v.adicCompletion K)
    exact Function.update_self v (t : v.adicCompletion K) 1
  have hu : (algebraMap K (AdeleRing (𝓞 K) K) (u : K)).2 v = algebraMap K (v.adicCompletion K) (u : K) := rfl
  simp only [hz, hd]
  fin_cases i <;> fin_cases j
  · simp only [Fin.isValue, if_true, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.diagonal_apply_eq, Matrix.cons_val_zero]
    show ((finIncl (𝓞 K) K (localUnit (𝓞 K) K v t : FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K)).2 v *
        (algebraMap K (AdeleRing (𝓞 K) K) (u : K)).2 v + (0 : AdeleRing (𝓞 K) K).2 v * (0 : AdeleRing (𝓞 K) K).2 v = _
    rw [ht, hu, h0, zero_mul, add_zero]
    rfl
  · simp [Matrix.diagonal]
    rfl
  · simp [Matrix.diagonal]
    rfl
  · simp only [Fin.isValue, if_true, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.diagonal_apply_eq, Matrix.cons_val_zero, Matrix.head_cons]
    show (0 : AdeleRing (𝓞 K) K).2 v * (0 : AdeleRing (𝓞 K) K).2 v +
      ((finIncl (𝓞 K) K (localUnit (𝓞 K) K v t : FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K)).2 v * (1 : AdeleRing (𝓞 K) K).2 v = _
    rw [ht, h0, h1, zero_mul, zero_add, mul_one]
    rfl

end S_AutomorphicForm_coe_finComponent_glFin_centralScalar_localUnit_mul_diagUnits2
end P2MW
export P2MW.S_AutomorphicForm_coe_finComponent_glFin_centralScalar_localUnit_mul_diagUnits2 (solution)
