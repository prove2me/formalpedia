-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDimSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDimSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:24.663833+00:00
-- url     : https://prove2.me/theorems/6c995086-28a9-49b6-b51a-779b44eed073
-- title:
--   Alg Dim St
-- statement:
--   Definitions and structural lemmas for Alg Dim St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/KleimanNefness/AlgDimSt.lean

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
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
def DimLtStatement : Prop :=
  ∀ (F : Type) [Field F] (σ : Type) [Fintype σ] (V W : Ideal (MvPolynomial σ F)),
    V.IsPrime → W.IsPrime → V < W →
    ringKrullDim (MvPolynomial σ F ⧸ W) < ringKrullDim (MvPolynomial σ F ⧸ V)
def DimPITStatement : Prop :=
  ∀ (F : Type) [Field F] (σ : Type) [Fintype σ] (V W : Ideal (MvPolynomial σ F)) (s : MvPolynomial σ F),
    V.IsPrime → s ∉ V → W ∈ (V ⊔ Ideal.span {s}).minimalPrimes →
    ringKrullDim (MvPolynomial σ F ⧸ W) + 1 = ringKrullDim (MvPolynomial σ F ⧸ V)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH


