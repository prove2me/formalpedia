-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_PolynomialStableSubmodule_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_PolynomialStableSubmodule_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:05:33.689489+00:00
-- url     : https://prove2.me/theorems/c747c029-6c99-40e1-b59f-3da85165fe8c
-- title:
--   Polynomial Stable Submodule — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for polynomial stable submodule used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
--
--   A field subspace stable under the original polynomial variables gives
--   a submodule for the original polynomial action.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_PolynomialStableSubmodule.lean, selected declarations in lines 17–59; source SHA-256 7ce57225efff21b6042b7e1d1bdad8ae852f807b06b88e97d8343e7f438a03e8; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.MvPolynomial.Basic
import Definitions.Def_LPCA_Solutions_LPCA_ModuleSquareEvaluation_SixOne20261024_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory

universe u

variable (k W : Type u) [CommRing k]

/-- A field subspace stable under the original polynomial variables gives
a submodule for the original polynomial action. -/
noncomputable def polynomialSubmoduleOfField
    (M : ModuleCat.{u} (MvPolynomial W k)) (N : ModuleCat.{u} k)
    (e : (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial W k)).obj M ≅ N)
    (P : Submodule k N) (v : W → (N ⟶ N))
    (hX : ∀ j,
      (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial W k)).map
          (ModuleCat.ofHom (R := MvPolynomial W k) (X := M) (Y := M)
            (LinearMap.lsmul (MvPolynomial W k) M (MvPolynomial.X j))) ≫ e.hom =
        e.hom ≫ v j)
    (hP : ∀ j x, x ∈ P → v j x ∈ P) : Submodule (MvPolynomial W k) M where
  carrier := {x | e.hom x ∈ P}
  zero_mem' := by
    change e.hom (0 : M) ∈ P
    rw [e.hom.hom.map_zero]
    exact P.zero_mem
  add_mem' := by
    intro x y hx hy
    change e.hom (x + y) ∈ P
    rw [e.hom.hom.map_add]
    exact P.add_mem hx hy
  smul_mem' := by
    intro p x hx
    have h : ∀ y : M, e.hom y ∈ P → e.hom (p • y) ∈ P := by
      refine MvPolynomial.induction_on
        (motive := fun q => ∀ y : M, e.hom y ∈ P → e.hom (q • y) ∈ P) p ?_ ?_ ?_
      · intro a y hy
        change e.hom (a • (show (ModuleCat.restrictScalars
          (MvPolynomial.C : k →+* MvPolynomial W k)).obj M from y)) ∈ P
        rw [e.hom.hom.map_smul]
        exact P.smul_mem a hy
      · intro p q hp hq y hy
        rw [add_smul, e.hom.hom.map_add]
        exact P.add_mem (hp y hy) (hq y hy)
      · intro p j hp y hy
        rw [mul_smul]
        apply hp
        have h := moduleSquare_apply k _ _ _ _ _ _ _ _ (hX j) y
        change e.hom ((MvPolynomial.X j : MvPolynomial W k) • y) = v j (e.hom y) at h
        rw [h]
        exact hP j _ hy
    exact h x hx

end LPCA


