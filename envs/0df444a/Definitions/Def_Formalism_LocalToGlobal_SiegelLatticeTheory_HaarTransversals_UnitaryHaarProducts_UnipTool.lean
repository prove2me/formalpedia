-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:56:51.929796+00:00
-- url     : https://prove2.me/theorems/3d28cb88-9728-4aca-a821-596ad5860279
-- title:
--   Unip Tool
-- statement:
--   Definitions and structural lemmas for Unip Tool, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/UnipTool.lean

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
open Matrix
open scoped BigOperators Pointwise
namespace Formalism.L2.SG.Pf.Unip
section Pat
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K]
def InPat (lv : ι → ℕ) (k : ℕ) (Z : Matrix ι ι K) : Prop := ∀ i j, lv j < lv i + k → Z i j = 0
variable {lv : ι → ℕ} {k l : ℕ} {Z W : Matrix ι ι K}
end Pat
section Sharp
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [StarRing K]
def Graded (lv : ι → ℕ) (T : ℕ) (J : Matrix ι ι K) : Prop := ∀ i j, J i j ≠ 0 → lv i + lv j = T
variable {lv : ι → ℕ} {T k : ℕ}
def sharp (J J' M : Matrix ι ι K) : Matrix ι ι K := J' * Mᴴ * J
variable {J J' : Matrix ι ι K}
variable [Invertible (2 : K)]
def proj (J J' M : Matrix ι ι K) : Matrix ι ι K := (⅟2 : K) • (M - sharp J J' M)
end Sharp
section Cay
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [Invertible (2 : K)]
def geo (N : ℕ) (Y : Matrix ι ι K) : Matrix ι ι K := ∑ j ∈ Finset.range N, Y ^ j
def cay (N : ℕ) (Z : Matrix ι ι K) : Matrix ι ι K := 1 + Z * geo N ((⅟2 : K) • Z)
variable {lv : ι → ℕ} {k : ℕ}
variable [StarRing K]
end Cay
section Step
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K]
variable {lv : ι → ℕ} {k : ℕ}
variable [StarRing K] [Invertible (2 : K)] {T : ℕ} {J J' : Matrix ι ι K}
end Step
section Cover
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
end Cover
end Formalism.L2.SG.Pf.Unip


