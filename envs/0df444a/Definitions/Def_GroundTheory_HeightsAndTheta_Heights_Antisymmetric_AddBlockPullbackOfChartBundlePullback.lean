-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_AddBlockPullbackOfChartBundlePullback
-- name    : GroundTheory_HeightsAndTheta_Heights_Antisymmetric_AddBlockPullbackOfChartBundlePullback
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:58.436802+00:00
-- url     : https://prove2.me/theorems/9117d9fe-95d3-4b87-85a3-256c774bed85
-- title:
--   Add Block Pullback Of Chart Bundle Pullback
-- statement:
--   Definitions and structural lemmas for Add Block Pullback Of Chart Bundle Pullback, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/AddBlockPullbackOfChartBundlePullback.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsGluing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_LocallyFreeSpreadHyp
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
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo
section Rings
variable {Ω : Type} [Field Ω]
end Rings
section Join
variable {Ω Ω' : Type} [Field Ω] [Field Ω'] [Algebra Ω Ω'] {ι κ : Type}
end Join
section AddBlock
variable {K : Type} {ι : K → Type} {κ : Type}
def addBlockToSum : Option K → K ⊕ Unit
  | none => Sum.inr ()
  | some k => Sum.inl k
def addBlockIdxToSigma :
    (Σ o, addBlockIdx ι κ o) → (Σ k : K ⊕ Unit, Sum.elim ι (fun _ : Unit => κ) k)
  | ⟨none, i⟩ => ⟨Sum.inr (), i⟩
  | ⟨some k, i⟩ => ⟨Sum.inl k, i⟩
def sigmaToAddBlockIdx :
    (Σ k : K ⊕ Unit, Sum.elim ι (fun _ : Unit => κ) k) → (Σ o, addBlockIdx ι κ o)
  | ⟨Sum.inr (), i⟩ => ⟨none, i⟩
  | ⟨Sum.inl k, i⟩ => ⟨some k, i⟩
def addBlockIdxEquiv :
    (Σ o, addBlockIdx ι κ o) ≃ (Σ k : K ⊕ Unit, Sum.elim ι (fun _ : Unit => κ) k) where
  toFun := addBlockIdxToSigma
  invFun := sigmaToAddBlockIdx
  left_inv := by rintro ⟨_ | k, i⟩ <;> rfl
  right_inv := by rintro ⟨k | ⟨⟩, i⟩ <;> rfl
end AddBlock
section Readings
open IndefiniteRowSideFullHecke.Antisym
def ratsInReal : Subfield ℝ := (Rat.castHom ℝ).fieldRange
abbrev chartOne : Subalgebra ℤ ℝ := chartRing ℤ (fun _ : Unit => (1 : ℝ)) ()
abbrev zTwo : Subring ℝ := locAtIntPrime 2 chartOne.toSubring
def sqrtTwoLattice : Submodule zTwo ℝ := Submodule.span zTwo (Set.range ![(1 : ℝ), √2])
end Readings
end GroundTheory.Heights₂.Heights


