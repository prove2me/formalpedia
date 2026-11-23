-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GL2Classical_Iwasawa
-- name    : GroundTheory_AutomorphicForms_GL2Classical_Iwasawa
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:27.245644+00:00
-- url     : https://prove2.me/theorems/7444f782-b0b3-49ea-a3a4-52178f01af25
-- title:
--   Iwasawa
-- statement:
--   Definitions and structural lemmas for Iwasawa, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2Classical/Iwasawa.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix UpperHalfPlane
namespace GroundTheory.Automorphic
noncomputable section
namespace GL2Classical
theorem det_fin_two_kmat (w : ℂ) : (!![w.re, -w.im; w.im, w.re] : Matrix (Fin 2) (Fin 2) ℝ).det =
    Complex.normSq w := by
  rw [Matrix.det_fin_two_of, Complex.normSq_apply]
  ring
def kGL (w : ℂ) (hw : w ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![w.re, -w.im; w.im, w.re] (by
    rw [det_fin_two_kmat]
    exact (Complex.normSq_pos.2 hw).ne')
@[simp]
theorem coe_kGL (w : ℂ) (hw : w ≠ 0) :
    (kGL w hw : Matrix (Fin 2) (Fin 2) ℝ) = !![w.re, -w.im; w.im, w.re] :=
  rfl
def borelGL (z : ℍ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![z.im, z.re; 0, 1] (by
    rw [Matrix.det_fin_two_of]
    simpa using z.im_pos.ne')
end GL2Classical
end
end GroundTheory.Automorphic


