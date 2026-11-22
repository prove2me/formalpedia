-- Prove2me | Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GNonneg
-- name    : Formalism_FormalDegreeBessel_FormalDegreeRatio_GNonneg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:08:10.774832+00:00
-- url     : https://prove2.me/theorems/02e8bf7c-4d18-4742-b4aa-7e0563a2df07
-- title:
--   GNonneg
-- statement:
--   Definitions and structural lemmas for GNonneg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GNonneg.lean

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace Formalism.QuantumDeterminants
def gnExt {ι : Type*} [DecidableEq ι] (p : ι → Prop) : Matrix ι {i // p i} ℂ :=
  fun i j => if i = j.val then 1 else 0
def gnB (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ :=
  Matrix.of fun i j => gramVec k r z z' g j i
def gnPi (k r : ℕ) : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] (Fin (r + 1) → ℂ) where
  toFun y a := if h : a.val < r then y (eI k r ⟨a.val, h⟩) - y (esI k r ⟨a.val, h⟩)
    else y ⟨r + k, by omega⟩
  map_add' x y := by
    ext a
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c x := by
    ext a
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring
end Formalism.QuantumDeterminants


