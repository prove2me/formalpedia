-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:45:36.683794+00:00
-- url     : https://prove2.me/theorems/8ffc1eea-6771-4c0f-824a-1ee00d052882
-- title:
--   Exp Law
-- statement:
--   Definitions and structural lemmas for Exp Law, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/ExpLaw.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_Models_FiniteGeneration_FiniteGenerationProofs_SolveV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_Models_FiniteGeneration_FiniteGenerationProofs_Imports
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_add

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
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] [Algebra ℚ k]
def ExpLawSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d) (ℓ : Pt k 1 d), (∀ i, constantCoeff (ℓ i) = 0) →
    dLin ℓ = 1 →
    comp1 ℓ (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) = comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1) →
    ∃ ε : Pt k 1 d, IsInvPair ε ℓ ∧ transF G.F ε ℓ = pt k (n := 2) d 0 + pt k (n := 2) d 1
def LogUniqueSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d) (ℓ ℓ' : Pt k 1 d),
    (∀ i, constantCoeff (ℓ i) = 0) → dLin ℓ = 1 →
    comp1 ℓ (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) = comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1) →
    (∀ i, constantCoeff (ℓ' i) = 0) → dLin ℓ' = 1 →
    comp1 ℓ' (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ℓ' (pt k (n := 2) d 0) + comp1 ℓ' (pt k (n := 2) d 1) → ℓ = ℓ'
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing


