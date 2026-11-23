-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_LocalClassFormation_FiniteVanishing_IntScalars
-- name    : GroundTheory_ProfiniteCohomology_LocalClassFormation_FiniteVanishing_IntScalars
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:46.823309+00:00
-- url     : https://prove2.me/theorems/f01a910b-662c-4812-a8cc-2a757a4ac1fa
-- title:
--   Int Scalars
-- statement:
--   Definitions and structural lemmas for Int Scalars, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalClassFormation/FiniteVanishing/IntScalars.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.ProfCoh
open CategoryTheory Limits groupCohomology
variable {Γ : Type} [Group Γ]
abbrev uliftIntToIntRep (M : Rep.{0} (ULift.{0} ℤ) Γ) : Rep.{0} ℤ Γ :=
  Rep.of (X := M.V)
    { toFun := fun g => (M.ρ g).toAddMonoidHom.toIntLinearMap
      map_one' := by
        ext x
        simp
      map_mul' := fun g h => by
        ext x
        simp [Module.End.mul_apply] }
theorem inhomogeneousCochains_d_uliftIntToIntRep (M : Rep.{0} (ULift.{0} ℤ) Γ) (i j : ℕ)
    (x : (Fin i → Γ) → M.V) :
    ((inhomogeneousCochains (uliftIntToIntRep M)).d i j).hom x =
      ((inhomogeneousCochains M).d i j).hom x := by
  rcases eq_or_ne (i + 1) j with rfl | h
  · rw [inhomogeneousCochains.d_def, inhomogeneousCochains.d_def]
    funext g
    have hs : ∀ k : ℕ, ((-1 : ULift.{0} ℤ) ^ k) = (((-1 : ℤ) ^ k : ℤ) : ULift.{0} ℤ) := fun k => by
      simp
    simp only [inhomogeneousCochains.d_hom_apply, hs, Int.cast_smul_eq_zsmul]
    rfl
  · have h' : ¬ (ComplexShape.up ℕ).Rel i j := h
    rw [HomologicalComplex.shape _ _ _ h', HomologicalComplex.shape _ _ _ h']
    rfl
def cochainsScULiftIntIso (M : Rep.{0} (ULift.{0} ℤ) Γ) (n : ℕ) :
    (forget₂ (ModuleCat.{0} (ULift.{0} ℤ)) Ab).mapShortComplex.obj ((inhomogeneousCochains M).sc n) ≅
      (forget₂ (ModuleCat.{0} ℤ) Ab).mapShortComplex.obj
        ((inhomogeneousCochains (uliftIntToIntRep M)).sc n) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      ext x
      exact inhomogeneousCochains_d_uliftIntToIntRep M _ _ x)
    (by
      ext x
      exact inhomogeneousCochains_d_uliftIntToIntRep M _ _ x)
def forget₂HomologyIso {S₁ : ShortComplex (ModuleCat.{0} (ULift.{0} ℤ))}
    {S₂ : ShortComplex (ModuleCat.{0} ℤ)}
    (σ : (forget₂ (ModuleCat.{0} (ULift.{0} ℤ)) Ab).mapShortComplex.obj S₁ ≅
      (forget₂ (ModuleCat.{0} ℤ) Ab).mapShortComplex.obj S₂) :
    (ShortComplex.homologyFunctor _ ⋙ forget₂ (ModuleCat.{0} (ULift.{0} ℤ)) Ab).obj S₁ ≅
      (ShortComplex.homologyFunctor _ ⋙ forget₂ (ModuleCat.{0} ℤ) Ab).obj S₂ :=
  ((ShortComplex.homologyFunctorIso (forget₂ (ModuleCat.{0} (ULift.{0} ℤ)) Ab)).app S₁).symm ≪≫
    (ShortComplex.homologyFunctor Ab).mapIso σ ≪≫
    (ShortComplex.homologyFunctorIso (forget₂ (ModuleCat.{0} ℤ) Ab)).app S₂
def groupCohomologyULiftIntIso (M : Rep.{0} (ULift.{0} ℤ) Γ) (n : ℕ) :
    (forget₂ (ModuleCat.{0} (ULift.{0} ℤ)) Ab).obj (groupCohomology M n) ≅
      (forget₂ (ModuleCat.{0} ℤ) Ab).obj (groupCohomology (uliftIntToIntRep M) n) :=
  forget₂HomologyIso (cochainsScULiftIntIso M n)
def groupCohomologyULiftIntAddEquiv (M : Rep.{0} (ULift.{0} ℤ) Γ) (n : ℕ) :
    groupCohomology M n ≃+ groupCohomology (uliftIntToIntRep M) n :=
  (groupCohomologyULiftIntIso M n).addCommGroupIsoToAddEquiv
end GroundTheory.ProfCoh


