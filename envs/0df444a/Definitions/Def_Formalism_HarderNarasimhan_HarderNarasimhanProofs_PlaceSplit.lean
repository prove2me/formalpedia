-- Prove2me | Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
-- name    : Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:20:39.477461+00:00
-- url     : https://prove2.me/theorems/f0f5bb90-ebe0-4f41-adf0-5f7e8843145b
-- title:
--   Place Split
-- statement:
--   Definitions and structural lemmas for Place Split, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
namespace Formalism.HN
namespace PlaceDecomposition
section
variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]
end
section
variable {P ι : Type*} [Fintype P] [DecidableEq P] [Fintype ι]
def prj (v : P) : EuclideanSpace ℝ (P × ι × Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (P × ι × Fin 2) where
  toFun w := (WithLp.equiv 2 _).symm (fun p => if p.1 = v then w p else 0)
  map_add' x y := by ext p; by_cases h : p.1 = v <;> simp [h]
  map_smul' c x := by ext p; by_cases h : p.1 = v <;> simp [h]
def psi (v : P) : (ι → ℂ) →ₗ[ℝ] EuclideanSpace ℝ (P × ι × Fin 2) where
  toFun z := (WithLp.equiv 2 _).symm
    (fun p => if p.1 = v then (if p.2.2 = 0 then (z p.2.1).re else (z p.2.1).im) else 0)
  map_add' x y := by ext p; by_cases h : p.1 = v <;> by_cases h' : p.2.2 = 0 <;> simp [h, h']
  map_smul' c x := by ext p; by_cases h : p.1 = v <;> by_cases h' : p.2.2 = 0 <;> simp [h, h']
end
section
variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
variable [DecidableEq (InfinitePlace K)]
end
section
variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
end
section
variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace K)]
end
end PlaceDecomposition
end Formalism.HN


