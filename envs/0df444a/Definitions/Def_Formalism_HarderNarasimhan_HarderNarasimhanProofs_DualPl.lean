-- Prove2me | Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
-- name    : Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:44:54.424205+00:00
-- url     : https://prove2.me/theorems/d0be139b-69eb-4e78-8df1-e66e9bbd5f32
-- title:
--   Dual Pl
-- statement:
--   Definitions and structural lemmas for Dual Pl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DualPl.lean

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
namespace Formalism.HN.DualPolygon
section Defs
variable {K V ι : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
def cE : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) →ₗ[ℝ]
    EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) :=
  (WithLp.linearEquiv 2 ℝ (InfinitePlace K × ι × Fin 2 → ℝ)).symm.toLinearMap ∘ₗ
    (LinearMap.pi (fun p : InfinitePlace K × ι × Fin 2 =>
      (if p.2.2 = 0 then (1 : ℝ) else -1) • LinearMap.proj p)) ∘ₗ
    (WithLp.linearEquiv 2 ℝ (InfinitePlace K × ι × Fin 2 → ℝ)).toLinearMap
def tdualLat (A : Submodule (𝓞 K) V) : Submodule (𝓞 K) (Module.Dual K V) where
  carrier := {f | ∀ x ∈ A, ∃ z : ℤ, Algebra.trace ℚ K (f x) = z}
  zero_mem' := fun x _ => ⟨0, by simp⟩
  add_mem' := by
    rintro f g hf hg x hx
    obtain ⟨a, ha⟩ := hf x hx
    obtain ⟨c, hc⟩ := hg x hx
    exact ⟨a + c, by simp [ha, hc]⟩
  smul_mem' := by
    rintro r f hf x hx
    obtain ⟨a, ha⟩ := hf (r • x) (A.smul_mem r hx)
    have e : (r • f) x = f (r • x) := by
      rw [LinearMap.smul_apply, ← algebraMap_smul K r x, map_smul, algebraMap_smul]
    exact ⟨a, e ▸ ha⟩
def annO (N : Submodule (𝓞 K) V) : Submodule (𝓞 K) (Module.Dual K V) where
  carrier := {f | ∀ x ∈ N, f x = 0}
  zero_mem' := fun x _ => by simp
  add_mem' := by
    rintro f g hf hg x hx
    simp [hf x hx, hg x hx]
  smul_mem' := by
    rintro r f hf x hx
    simp [hf x hx]
end Defs
end Formalism.HN.DualPolygon
namespace Formalism.HN.DualPolygon
open Formalism.HN
section Assumptions
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
end Assumptions
end Formalism.HN.DualPolygon
namespace Formalism.HN.DualPolygon
open Formalism.HN
section Zlat
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
end Zlat
section Diff
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
open nonZeroDivisors
end Diff
end Formalism.HN.DualPolygon
namespace Formalism.HN.DualPolygon
open Formalism.HN
section Twist
attribute [local instance] Ideal.Quotient.field
variable {K W : Type} [Field K] [NumberField K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [FiniteDimensional K W]
omit [FiniteDimensional K W] in
include K in
theorem twist_torsionFree : IsAddTorsionFree W := ⟨fun n hn a c h => by
  have h' : (n : K) • a = (n : K) • c := by simpa [Nat.cast_smul_eq_nsmul] using h
  exact smul_right_injective W (Nat.cast_ne_zero.2 hn) h'⟩
example (X : Submodule (𝓞 K) W) : Module.IsTorsionFree ℤ X := by
  have := twist_torsionFree (K := K) (W := W)
  infer_instance
example (X : Submodule (𝓞 K) W) (hX : X.FG) : Module.Finite ℤ X := by
  have : Module.Finite (𝓞 K) X := Module.Finite.iff_fg.mpr hX
  exact Module.Finite.trans (𝓞 K) X
end Twist
section TwistInt
open scoped Pointwise
variable {K W : Type} [Field K] [NumberField K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [FiniteDimensional K W]
end TwistInt
end Formalism.HN.DualPolygon
namespace Formalism.HN.DualPolygon
open Formalism.HN
section Main
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
end Main
end Formalism.HN.DualPolygon
namespace Formalism.HN.DualPolygon
open Formalism.HN
section Key
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
end Key
end Formalism.HN.DualPolygon
namespace Formalism.HN.DualPolygon
open Formalism.HN
section HtDual
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
end HtDual
end Formalism.HN.DualPolygon
namespace Formalism.HN.DualPolygon
open Formalism.HN
section DD
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
end DD
end Formalism.HN.DualPolygon
namespace Formalism.HN.DualPolygon
open Formalism.HN
section HNDual
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
end HNDual
end Formalism.HN.DualPolygon
namespace Formalism.HN
open DualPolygon
end Formalism.HN


