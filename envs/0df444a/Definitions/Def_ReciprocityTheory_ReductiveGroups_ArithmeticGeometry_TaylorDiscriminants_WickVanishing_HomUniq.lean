-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HomUniq
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HomUniq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:59:19.953981+00:00
-- url     : https://prove2.me/theorems/a0151182-fce9-47ba-bdff-424568f553b5
-- title:
--   Hom Uniq
-- statement:
--   Definitions and structural lemmas for Hom Uniq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/HomUniq.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConstantCoeffEv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace ReciprocityTheory.ChartRestriction.G.TB
def HomUniqSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d) (ψ ψ' : Pt k 1 d),
    (∀ i, constantCoeff (ψ i) = 0) → (∀ i, constantCoeff (ψ' i) = 0) →
    comp1 ψ (pt k (n := 2) d 0 + pt k (n := 2) d 1) =
      G.add (comp1 ψ (pt k (n := 2) d 0)) (comp1 ψ (pt k (n := 2) d 1)) →
    comp1 ψ' (pt k (n := 2) d 0 + pt k (n := 2) d 1) =
      G.add (comp1 ψ' (pt k (n := 2) d 0)) (comp1 ψ' (pt k (n := 2) d 1)) →
    dLin ψ = dLin ψ' → ψ = ψ'
namespace HomUniqPf
open ReciprocityTheory.ChartRestriction.G.TB.LogPf Formalism.FG.SolveVAux
variable {k : Type} [CommRing k] {d : ℕ}
end HomUniqPf
end ReciprocityTheory.ChartRestriction.G.TB


