-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FinrankSectionsLineBundlePowEqPow
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FinrankSectionsLineBundlePowEqPow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:26:29.582834+00:00
-- url     : https://prove2.me/theorems/1faad5a0-2dc9-43f0-8a28-b2fba0e8bd69
-- title:
--   Finrank Sections Line Bundle Pow Eq Pow
-- statement:
--   Definitions and structural lemmas for Finrank Sections Line Bundle Pow Eq Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FinrankSectionsLineBundlePowEqPow.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
namespace GlobalTheory.FinrankGrowthBounds
open Filter Topology
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (T : Over S)
theorem lpow_g_add (a b : ℤ) (i j : Fin 1 → L.ι) :
    (LPow A L (a + b) T).g i j =
      (show Γ((T ⊗ A).left, (LPow A L (a + b) T).U i ⊓ (LPow A L (a + b) T).U j)ˣ from
        (LPow A L a T).g i j) *
      (show Γ((T ⊗ A).left, (LPow A L (a + b) T).U i ⊓ (LPow A L (a + b) T).U j)ˣ from
        (LPow A L b T).g i j) := by
  simp only [LPow, LB.LinComb, zpow_add, Finset.prod_mul_distrib]
  rfl
noncomputable def mulSec (a b : ℤ) (s : SecM A L b T) :
    SecM A L a T →ₗ[Γ(T.left, ⊤)] SecM A L (a + b) T where
  toFun f := ⟨fun i => (show Γ((T ⊗ A).left, LB.wchart L (fun _ : Fin 1 => (snd T A).left) i) from f.1 i) *
      (show Γ((T ⊗ A).left, LB.wchart L (fun _ : Fin 1 => (snd T A).left) i) from s.1 i), by
    intro i j
    have hf := f.2 i j
    have hs := s.2 i j
    rw [lpow_g_add A L T a b i j]
    refine (map_mul _ _ _).trans ?_
    refine (congrArg₂ (fun x y : Γ((T ⊗ A).left,
      (LPow A L (a + b) T).U i ⊓ (LPow A L (a + b) T).U j) => x * y) hf hs).trans ?_
    refine Eq.trans ?_ (congrArg₂ (· * ·) (Units.val_mul _ _).symm (map_mul _ _ _).symm)
    exact mul_mul_mul_comm _ _ _ _⟩
  map_add' f f' := Subtype.ext (funext fun i =>
    add_mul (R := Γ((T ⊗ A).left, LB.wchart L (fun _ : Fin 1 => (snd T A).left) i)) (f.1 i) (f'.1 i) (s.1 i))
  map_smul' c f := Subtype.ext (funext fun i => _root_.mul_assoc (liftHom A _ c) _ _)
end GlobalTheory.FinrankGrowthBounds


