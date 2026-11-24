-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLocalSheets
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLocalSheets
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:00.157909+00:00
-- url     : https://prove2.me/theorems/0fba9cc9-29a6-41c2-acf2-bc13a1e1dac9
-- title:
--   PCone Local Sheets
-- statement:
--   Definitions and structural lemmas for PCone Local Sheets, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLocalSheets.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeLocalSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsQuasiFiniteSheets
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
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj mcPts fibre segre)
open Matrix
namespace ConeLocalSheets
variable {n e : ℕ}
def homogenize (c : MvPolynomial (Fin e) ℂ) : MvPolynomial (Fin (e + 1)) ℂ :=
  ∑ m ∈ c.support, C (coeff m c) * (X 0 ^ (c.totalDegree - m.degree) * rename Fin.succ (monomial m 1))
def lift (z : Fin n → ℂ) : (Σ k, PBlk n k) → ℂ := fun p => z p.2
def lin (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : (Fin n → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ) :=
  Ψ ∘ₗ LinearMap.funLeft ℂ ℂ (fun i : Unit → Fin n => i ())
def chartIdeal (P : Ideal (MRing (PBlk n))) (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    Ideal (MvPolynomial (Fin n) ℂ) :=
  Ideal.map ((rename (fun p : Σ k, PBlk n k => p.2)).toRingHom.comp (map (Int.castRingHom ℂ))) P ⊔
    Ideal.span {∑ j, C (LinearMap.toMatrix' (lin Ψ) 0 j) * X j - 1}
def tailMat (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Matrix (Fin e) (Fin n) ℂ :=
  (LinearMap.toMatrix' (lin Ψ)).submatrix Fin.succ id
end ConeLocalSheets
end GroundTheory.Heights₂.Heights


