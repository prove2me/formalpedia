-- Prove2me | solution 1 for AutomorphicForm.isRegularSemisimple_finComponent_glFin_centralScalar_mul_diagUnits2_of_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/795568b7-da28-5db4-bc5f-c152e3a20794

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isRegularSemisimple_finComponent_glFin_centralScalar_mul_diagUnits2_of_ne_one

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

theorem solution (K : Type) [Field K] [NumberField K]
    (u : Kˣ) (hu : (u : K) ≠ 1) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    AutomorphicForm.IsRegularSemisimple (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))  := by
  rw [AutomorphicForm.isRegularSemisimple_iff_ne_zero]

  set g := AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K
    (AutomorphicForm.centralScalar (𝓞 K) K z *
      diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) with hg
  set zv : v.adicCompletion K := ((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v with hzv
  set uv : v.adicCompletion K := algebraMap K (v.adicCompletion K) (u : K) with huv
  have h0 : (0 : AdeleRing (𝓞 K) K).2 v = 0 := rfl
  have h1 : (1 : AdeleRing (𝓞 K) K).2 v = 1 := rfl
  have hu' : (algebraMap K (AdeleRing (𝓞 K) K) (u : K)).2 v = uv := rfl
  have hz : ∀ i j : Fin 2, ((AutomorphicForm.centralScalar (𝓞 K) K z : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j = if i = j then (z : AdeleRing (𝓞 K) K) else 0 := by
    intro i j
    change Matrix.scalar (Fin 2) _ i j = _
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  have hd : ∀ i j : Fin 2, ((diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1 :
      GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      (!![algebraMap K (AdeleRing (𝓞 K) K) (u : K), 0; 0, 1] : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j :=
    fun _ _ => rfl
  have hent : ∀ i j : Fin 2, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j =
      (!![zv * uv, 0; 0, zv] : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j := by
    intro i j
    rw [hg, AdelicLevel.finComponent_apply, AdelicLevel.glFin_apply, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [hz, hd]
    fin_cases i <;> fin_cases j
    · simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one]
      show ((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v * (algebraMap K (AdeleRing (𝓞 K) K) (u : K)).2 v +
        (0 : AdeleRing (𝓞 K) K).2 v * (0 : AdeleRing (𝓞 K) K).2 v = zv * uv
      rw [h0, zero_mul, add_zero]
      rfl
    · simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Matrix.head_cons]
      show ((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v * (0 : AdeleRing (𝓞 K) K).2 v +
        (0 : AdeleRing (𝓞 K) K).2 v * (1 : AdeleRing (𝓞 K) K).2 v = 0
      rw [h0, mul_zero, zero_mul, add_zero]
    · simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Matrix.head_cons]
      show (0 : AdeleRing (𝓞 K) K).2 v * (algebraMap K (AdeleRing (𝓞 K) K) (u : K)).2 v +
        ((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v * (0 : AdeleRing (𝓞 K) K).2 v = 0
      rw [h0, mul_zero, zero_mul, add_zero]
    · simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.head_cons]
      show (0 : AdeleRing (𝓞 K) K).2 v * (0 : AdeleRing (𝓞 K) K).2 v +
        ((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v * (1 : AdeleRing (𝓞 K) K).2 v = zv
      rw [h0, h1, zero_mul, zero_add, mul_one]

  have hzv0 : zv ≠ 0 := by
    have hzu : IsUnit zv := by
      refine ⟨⟨zv, ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v, ?_, ?_⟩, rfl⟩
      · show (((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v = 1
        rw [Units.mul_inv]; rfl
      · show ((((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) * ((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v = 1
        rw [Units.inv_mul]; rfl
    exact hzu.ne_zero
  have huv1 : uv - 1 ≠ 0 := by
    rw [sub_ne_zero, huv, ne_eq, ← (algebraMap K (v.adicCompletion K)).map_one]
    exact fun h => hu ((algebraMap K (v.adicCompletion K)).injective h)
  rw [Matrix.trace_fin_two, Matrix.det_fin_two, hent, hent, hent, hent]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.head_cons]
  have : (zv * uv + zv) ^ 2 - 4 * (zv * uv * zv - 0 * 0) = (zv * (uv - 1)) ^ 2 := by ring
  rw [this]
  exact pow_ne_zero 2 (mul_ne_zero hzv0 huv1)

end S_AutomorphicForm_isRegularSemisimple_finComponent_glFin_centralScalar_mul_diagUnits2_of_ne_one
end P2MW
export P2MW.S_AutomorphicForm_isRegularSemisimple_finComponent_glFin_centralScalar_mul_diagUnits2_of_ne_one (solution)
