-- Prove2me | Definitions.Def_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearIrreducible
-- name    : LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearIrreducible
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:47:48.746978+00:00
-- url     : https://prove2.me/theorems/047ac08d-5255-4ca0-b128-1bc744d3d6a0
-- title:
--   Inverse polynomial substitutions for shears
-- statement:
--   This constructs the algebra isomorphism on real plane polynomials induced by a shear. The shear with the negative parameter is proved to give its inverse.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CrossingLemma_Shear
import Mathlib

set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace PachDeZeeuw.Algebraic

open MvPolynomial


lemma aeval_shearVars_shearVars (a b : ℝ) (hab : a + b = 0) (i : Fin 2) :
    aeval (shearVars a) (shearVars b i) = (X i : PlanePoly) := by
  obtain rfl : b = -a := by linarith
  fin_cases i
  · show aeval (shearVars a) (X 0 + C (-a) * X 1) = X 0
    rw [map_add, map_mul, aeval_X, aeval_X, aeval_C, algebraMap_eq, C_neg]
    show (X 0 + C a * X 1) + (- C a) * X 1 = (X 0 : PlanePoly)
    ring
  · show aeval (shearVars a) (X 1) = X 1
    rw [aeval_X]; rfl


lemma shearAlgHom_comp_inv (s : ℝ) :
    (aeval (shearVars s)).comp (aeval (shearVars (-s))) = AlgHom.id ℝ PlanePoly := by
  apply algHom_ext
  intro i
  rw [AlgHom.comp_apply, aeval_X, AlgHom.id_apply]
  exact aeval_shearVars_shearVars s (-s) (by ring) i


lemma shearAlgHom_inv_comp (s : ℝ) :
    (aeval (shearVars (-s))).comp (aeval (shearVars s)) = AlgHom.id ℝ PlanePoly := by
  apply algHom_ext
  intro i
  rw [AlgHom.comp_apply, aeval_X, AlgHom.id_apply]
  exact aeval_shearVars_shearVars (-s) s (by ring) i


noncomputable def shearAlgEquiv (s : ℝ) : PlanePoly ≃ₐ[ℝ] PlanePoly :=
  AlgEquiv.ofAlgHom (aeval (shearVars s)) (aeval (shearVars (-s)))
    (shearAlgHom_comp_inv s) (shearAlgHom_inv_comp s)


end PachDeZeeuw.Algebraic


