-- Prove2me | solution 1 for AutomorphicForm.hasArchType0_fnTwist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/9802be23-6c14-5d4f-8d8f-ef377ad0a3b8

import Mathlib
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_hasArchType0_fnTwist

set_option autoImplicit false

open NumberField AutomorphicForm
open NumberField.AdelicLevel IsDedekindDomain

namespace RtwTwist

noncomputable section

variable (F : Type) [Field F] [NumberField F]

theorem det_adelicArchGLInclAt_eq_one (w : InfinitePlace F) (k : GL (Fin 2) w.Completion)
    (hk : (k : Matrix (Fin 2) (Fin 2) w.Completion).det = 1) :
    Matrix.GeneralLinearGroup.det (adelicArchGLInclAt F w k) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  set A : AdelicGL2 (𝓞 F) F := adelicArchGLInclAt F w k with hA
  have hAdef : A = adelicArchGLIncl F (archGLIncl F w k) := rfl
  refine Prod.ext ?_ ?_
  ·
    have h1 : ((A : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).det).1
        = ((adeleArch (𝓞 F) F).mapMatrix (A : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))).det :=
      (adeleArch_apply (𝓞 F) F _).symm.trans (RingHom.map_det (adeleArch (𝓞 F) F) _)
    have h2 : (adeleArch (𝓞 F) F).mapMatrix (A : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        = ((glArch (𝓞 F) F A : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := by
      ext i j; rfl
    rw [show (1 : AdeleRing (𝓞 F) F).1 = 1 from rfl, h1, h2, hAdef, glArch_adelicArchGLIncl]

    funext v
    have h3 : (((archGLIncl F w k : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)).det) v
        = ((Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) v).mapMatrix
            ((archGLIncl F w k : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))).det :=
      (Pi.evalRingHom_apply (fun v : InfinitePlace F => v.Completion) v _).symm.trans
        (RingHom.map_det (Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) v) _)
    rw [h3, show (1 : InfiniteAdeleRing F) v = 1 from rfl]
    have h4 : ((archGLIncl F w k : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))
        = archMatrixUpdate F w (k : Matrix (Fin 2) (Fin 2) w.Completion) := rfl
    by_cases hv : v = w
    · subst hv
      have h5 : (Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) v).mapMatrix
          (archMatrixUpdate F v (k : Matrix (Fin 2) (Fin 2) v.Completion)) = (k : Matrix (Fin 2) (Fin 2) v.Completion) := by
        ext i j; simp [RingHom.mapMatrix_apply, Matrix.map_apply, archMatrixUpdate_apply_self]
      rw [h4, h5, hk]
    · have h5 : (Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) v).mapMatrix
          (archMatrixUpdate F w (k : Matrix (Fin 2) (Fin 2) w.Completion)) = 1 := by
        ext i j; simp [RingHom.mapMatrix_apply, Matrix.map_apply, archMatrixUpdate_apply_of_ne F w _ i j hv]
      rw [h4, h5, Matrix.det_one]
  ·
    have h1 : ((A : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).det).2
        = ((adeleFin (𝓞 F) F).mapMatrix (A : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))).det :=
      (adeleFin_apply (𝓞 F) F _).symm.trans (RingHom.map_det (adeleFin (𝓞 F) F) _)
    have h2 : (adeleFin (𝓞 F) F).mapMatrix (A : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        = ((glFin (𝓞 F) F A : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := by
      ext i j; rfl
    rw [show (1 : AdeleRing (𝓞 F) F).2 = 1 from rfl, h1, h2, hAdef, glFin_adelicArchGLIncl, Units.val_one, Matrix.det_one]

end

end RtwTwist

open RtwTwist in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : HasArchType₀ F χ φ) :
    HasArchType₀ F χ (fnTwist F η φ) := by
  intro w k g
  have hk : ((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det = 1 :=
    ((mem_rowIsometrySubgroup₀_iff w.Completion).mp k.2).1
  have hdet := det_adelicArchGLInclAt_eq_one F w (k : GL (Fin 2) w.Completion) hk
  simp only [fnTwist_apply, chiDet, map_mul, hdet, mul_one, hφ w k g]
  ring

end S_AutomorphicForm_hasArchType0_fnTwist
end P2MW
export P2MW.S_AutomorphicForm_hasArchType0_fnTwist (solution)
