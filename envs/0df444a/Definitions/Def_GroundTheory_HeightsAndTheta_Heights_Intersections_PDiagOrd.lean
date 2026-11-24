-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagOrd
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagOrd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:13.632998+00:00
-- url     : https://prove2.me/theorems/1c655f78-7787-4330-81a0-4f90b646004d
-- title:
--   PDiag Ord
-- statement:
--   Definitions and structural lemmas for PDiag Ord, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOrd.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOffUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOrdOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
namespace DiagonalOrder
section Orders
variable {K : Type} {ι : K → Type}
end Orders
section Diagonal
variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]
def polyCoord (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) :
    (Σ k, T.wwIdx ι ν κ k) → MvPolynomial (Fin 2) Ω
  | ⟨.base, i⟩ => C (x i)
  | ⟨.det, l⟩ => C (δ l)
  | ⟨.line0, k⟩ => C (φ k (e 0)) + X 0 * C (φ k (e 1))
  | ⟨.line1, k⟩ => C (φ k (e 0)) + X 1 * C (φ k (e 1))
def polyConeMap (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) :
    MRing (T.wwIdx ι ν κ) →+* MvPolynomial T.WBlk (MvPolynomial (Fin 2) Ω) :=
  eval₂Hom (Int.castRingHom _) fun p => C (polyCoord x δ e φ p) * X p.1
end Diagonal
end DiagonalOrder
end
end GroundTheory.Heights₂.Heights.Inter


