-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ErealAddIInf
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_ErealAddIInf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:27:36.751986+00:00
-- url     : https://prove2.me/theorems/45bb6e41-8bbb-463f-a55e-6c905b10d445
-- title:
--   Ereal Add IInf
-- statement:
--   Definitions and structural lemmas for Ereal Add IInf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ErealAddIInf.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj
section Graded
variable {K R M W : Type} [Field K] [CommRing R] [Algebra K R] [AddCommMonoid M] (key : W → M)
  (C : W → Submodule K R)
def incG (w : W) : C w →ₗ[K] AddMonoidAlgebra R M where
  toFun F := AddMonoidAlgebra.single (key w) (F : R)
  map_add' F F' := by simp [AddMonoidAlgebra.single_add]
  map_smul' a F := by simp [AddMonoidAlgebra.smul_single]
def cfG (K : Type) [Field K] [Algebra K R] (m : M) : AddMonoidAlgebra R M →ₗ[K] R where
  toFun x := x.coeff m
  map_add' x y := by simp
  map_smul' a x := by simp
def vG (v : R → EReal) (x : AddMonoidAlgebra R M) : EReal := ⨅ m, v (x.coeff m)
variable {v : R → EReal}
end Graded
end Formalism.L2.Pj


