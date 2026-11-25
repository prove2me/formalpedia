-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMax
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMax
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T03:06:44.454136+00:00
-- url     : https://prove2.me/theorems/df39c242-7a55-4960-9146-d79c3abae4b3
-- title:
--   POrbit Chart Max
-- statement:
--   Definitions and structural lemmas for POrbit Chart Max, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMax.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Theorems.Thm_GroundTheory_Arith_Toric_IsRationalPolyhedral_sup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
namespace OrbitChartMax
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
def dehomCoords {Ω : Type*} [Field Ω] (z : Coord n → Ω) (c : (k : ι) → Fin (n k + 1)) :
    Coord n → Ω :=
  fun p ↦ (z ⟨p.1, c p.1⟩)⁻¹ * z p
def homDeg (F : MvPolynomial (Coord n) ℤ) : ι → ℕ :=
  fun k ↦ F.support.sup fun m ↦ Finsupp.weight (coordDeg n) m k
def homogenize (c : (k : ι) → Fin (n k + 1)) (F : MvPolynomial (Coord n) ℤ) :
    MvPolynomial (Coord n) ℤ :=
  ∑ m ∈ F.support, monomial m (coeff m F) *
    chartMonomial c (homDeg F - Finsupp.weight (coordDeg n) m)
section Generic
variable (V : Ideal (MvPolynomial (Coord n) ℤ)) [V.IsPrime]
omit [Fintype ι] [DecidableEq ι] in

def genPt : Coord n → FractionRing (MvPolynomial (Coord n) ℤ ⧸ V) :=
  fun p ↦ algebraMap _ _ (Ideal.Quotient.mk V (X p))
end Generic
end OrbitChartMax
end
end GroundTheory.Heights₂.Heights


