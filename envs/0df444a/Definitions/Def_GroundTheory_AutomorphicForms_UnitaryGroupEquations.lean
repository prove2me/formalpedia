-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_UnitaryGroupEquations
-- name    : GroundTheory_AutomorphicForms_UnitaryGroupEquations
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:15.909261+00:00
-- url     : https://prove2.me/theorems/84417b9b-9a9f-4d16-b943-6bf7dea98a52
-- title:
--   Unitary Group Equations
-- statement:
--   Definitions and structural lemmas for Unitary Group Equations, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryGroupEquations.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryGroupScheme
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj


set_option autoImplicit false
namespace GroundTheory.Automorphic
open Module Matrix TensorProduct
variable {F E : Type*} [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] (b : Basis κ F E)
section Coordinates
variable (R : Type*) [CommRing R] [Algebra F R] {S : Type*} [CommRing S] [Algebra F S]
noncomputable def matrixCoords : Matrix ι ι (R ⊗[F] E) ≃ (ι × ι × κ → R) where
  toFun g p := (Algebra.TensorProduct.basis R b).repr (g p.1 p.2.1) p.2.2
  invFun x i j := (Algebra.TensorProduct.basis R b).repr.symm
    (Finsupp.equivFunOnFinite.symm fun k => x (i, j, k))
  left_inv g := by
    ext i j
    simp
  right_inv x := by
    funext ⟨i, j, k⟩
    simp
variable {R}
end Coordinates
end GroundTheory.Automorphic


