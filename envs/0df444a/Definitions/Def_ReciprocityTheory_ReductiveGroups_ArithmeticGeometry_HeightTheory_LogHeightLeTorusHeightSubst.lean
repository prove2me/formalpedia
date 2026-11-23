-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LogHeightLeTorusHeightSubst
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LogHeightLeTorusHeightSubst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:37:31.439803+00:00
-- url     : https://prove2.me/theorems/cdffaee9-3fcc-4867-8c86-e31afdf2a715
-- title:
--   Log Height Le Torus Height Subst
-- statement:
--   Definitions and structural lemmas for Log Height Le Torus Height Subst, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/LogHeightLeTorusHeightSubst.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_LagrangeIdealLiftsFact
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ContinuousTorusPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NatDegreeLeAndCoeffProdPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
section CoeffIn
variable {R : Type*} [CommRing R] {V : Type*} [DecidableEq V]
noncomputable def asPolyInVar (i : V) : MvPolynomial V R →ₐ[R] Polynomial (MvPolynomial V R) :=
  MvPolynomial.aeval fun v => if v = i then Polynomial.X else Polynomial.C (MvPolynomial.X v)
end CoeffIn
end ReciprocityTheory.ChartRestriction.G.T0


