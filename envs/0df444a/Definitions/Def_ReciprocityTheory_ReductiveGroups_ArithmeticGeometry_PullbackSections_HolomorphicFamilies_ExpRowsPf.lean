-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_ExpRowsPf
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_ExpRowsPf
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T17:59:25.105614+00:00
-- url     : https://prove2.me/theorems/c5076d37-8623-56eb-9063-489a71bb5ca0
-- title:
--   Exp Rows Pf
-- statement:
--   Definitions and structural lemmas for Exp Rows Pf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/ExpRowsPf.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OpenRowsFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnChartX
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
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows
open AlgebraicGeometry CategoryTheory Opposite NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped MonObj
section Der
variable {g : ℕ} {Y : Scheme.{0}}
instance isLocalHom_fst : IsLocalHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom :=
  ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ha⟩
instance isLocalHom_epsMul (cc : ℂ) : IsLocalHom (epsMul cc) :=
  ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (by
    have := TrivSqZeroExt.isUnit_iff_isUnit_fst.mp ha
    simpa [epsMul] using this)⟩
instance isLocalHom_fst' : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)) :=
  isLocalHom_fst
instance isLocalHom_epsMul' (cc : ℂ) : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom (epsMul cc))) :=
  isLocalHom_epsMul cc
end Der
section Tan
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
def tyD (ty : Fin g → (E →+* ℂ)) (a : NumberField.RingOfIntegers E) : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z k => ty k (a : E) * z k
      map_add' := fun z z' => by funext k; simp [mul_add]
      map_smul' := fun t z => by funext k; simp; ring }
end Tan
end ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows


