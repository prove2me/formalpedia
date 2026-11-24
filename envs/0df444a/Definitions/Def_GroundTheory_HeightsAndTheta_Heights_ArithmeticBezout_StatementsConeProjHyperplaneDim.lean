-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeProjHyperplaneDim
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeProjHyperplaneDim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:44:14.508439+00:00
-- url     : https://prove2.me/theorems/8d105856-8f18-4232-a2b2-aacaa2305b04
-- title:
--   Statements Cone Proj Hyperplane Dim
-- statement:
--   Definitions and structural lemmas for Statements Cone Proj Hyperplane Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsConeProjHyperplaneDim.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeProjHyperplaneNull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
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
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj segre)
def coneFirstForm {n e : ℕ} (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    MvPolynomial (Fin n) ℂ :=
  rename (fun p : Σ k : Unit, PBlk n k => p.2) (ReciprocityTheory.ChartRestriction.G.Geo.psiPoly Ψ 0)
def ConeProjHyperplaneDim.Statement : Prop :=
  ∀ (n e : ℕ) (P : Ideal (MRing (PBlk n)))
    (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (complexFibreIdeal P ⊔ Ideal.span {coneFirstForm Ψ})) ≤
        ((e : ℕ) : WithBot ℕ∞)
end GroundTheory.Heights₂.Heights


