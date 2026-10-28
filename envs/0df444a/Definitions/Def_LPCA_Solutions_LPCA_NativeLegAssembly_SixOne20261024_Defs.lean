-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_NativeLegAssembly_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_NativeLegAssembly_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:05:25.469522+00:00
-- url     : https://prove2.me/theorems/0d455967-5aae-4b64-864a-e9ca0e7cd5e2
-- title:
--   Native Leg Assembly — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for native leg assembly used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
--
--   Assemble component isomorphisms using the native homogeneous legs as
--   parameters. Their retraction identity proves bijectivity, without unfolding
--   the construction of any component or of the grading comparison.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_NativeLegAssembly.lean, selected declarations in lines 14–56; source SHA-256 4573cd9516295ee715d254d09e0802ed3ae784e9829d1c2e03e0f00be8bc1e7e; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.DirectSum.Module
import Definitions.Def_LPCA_Solutions_LPCA_DirectSumGeneratorEquations_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_DirectSumRestriction_SixOne20261024_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory

universe u

/-- Assemble component isomorphisms using the native homogeneous legs as
parameters. Their retraction identity proves bijectivity, without unfolding
the construction of any component or of the grading comparison. -/
noncomputable def nativeLegAssemblyEquiv (R : Type u) [Ring R]
    {I : Type u} [DecidableEq I]
    (A B : I → ModuleCat.{u} R) (e : ∀ i, A i ≅ B i)
    (H : ModuleCat.{u} R) (j : ∀ i, B i ⟶ H)
    (E : H ≅ ModuleCat.of R (DirectSum I (fun i => B i)))
    (hj : ∀ i, j i ≫ E.hom = ModuleCat.ofHom (DirectSum.lof R I (fun i => B i) i)) :
    DirectSum I (fun i => A i) ≃ₗ[R] H := by
  let F := DirectSum.toModule R I H (fun i => (j i).hom.comp (e i).hom.hom)
  let G := DirectSum.congrLinearEquiv (fun i => (e i).toLinearEquiv)
  have hcomp : E.hom.hom.comp F = G.toLinearMap := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, F, G, DirectSum.toModule_lof,
      LinearEquiv.coe_coe, directSumCongrEquiv_lof, Iso.toLinearEquiv_apply]
    exact congrArg (fun f => f ((e i).hom x)) (hj i)
  have hc : Function.Bijective (E.hom.hom.comp F) := by
    rw [hcomp]
    exact G.bijective
  have hf : Function.Bijective F := by
    constructor
    · intro x y hxy
      exact hc.injective (congrArg E.hom hxy)
    · intro y
      obtain ⟨x, hx⟩ := hc.surjective (E.hom y)
      exact ⟨x, E.toLinearEquiv.injective hx⟩
  exact LinearEquiv.ofBijective F hf

theorem nativeLegAssemblyEquiv_lof (R : Type u) [Ring R]
    {I : Type u} [DecidableEq I]
    (A B : I → ModuleCat.{u} R) (e : ∀ i, A i ≅ B i)
    (H : ModuleCat.{u} R) (j : ∀ i, B i ⟶ H)
    (E : H ≅ ModuleCat.of R (DirectSum I (fun i => B i)))
    (hj : ∀ i, j i ≫ E.hom = ModuleCat.ofHom (DirectSum.lof R I (fun i => B i) i))
    (i : I) (x : A i) :
    nativeLegAssemblyEquiv R A B e H j E hj (DirectSum.lof R I (fun i => A i) i x) =
      j i ((e i).hom x) :=
  DirectSum.toModule_lof R (ι := I) (N := H) (M := fun i => A i)
    (φ := fun i => (j i).hom.comp (e i).hom.hom) i x

end LPCA


