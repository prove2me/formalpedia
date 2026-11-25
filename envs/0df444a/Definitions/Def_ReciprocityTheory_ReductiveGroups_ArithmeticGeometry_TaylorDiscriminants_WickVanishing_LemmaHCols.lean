-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LemmaHCols
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LemmaHCols
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T13:56:31.762353+00:00
-- url     : https://prove2.me/theorems/c6a7e952-9b23-5ac1-8310-228188b7554d
-- title:
--   Lemma HCols
-- statement:
--   Definitions and structural lemmas for Lemma HCols, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LemmaHCols.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GermSCCols
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnOperator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LemmaH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dpolyOf_add_P
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dpolyOf_smul_P

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols
variable {k : Type} [CommRing k] {ι : Type} [Fintype ι] {n : ℕ}
def Mf (mu : Fin n → MvPolynomial ι k →ₗ[k] k) (P : MvPolynomial (ι × Fin n) k) : k :=
  ∑ mo ∈ P.support, P.coeff mo * ∏ b, mu b (monomial (colM mo b) 1)
variable (mu : Fin n → MvPolynomial ι k →ₗ[k] k)
def combine (f : Fin n → (ι →₀ ℕ)) : ι × Fin n →₀ ℕ :=
  ∑ b, Finsupp.mapDomain (fun l => (l, b)) (f b)
variable [Algebra ℚ k]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
def valL {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type} [CommRing k]
    [Algebra ℚ k] [Algebra R k] (B : FB R d O) {ι : Type} [Fintype ι] (u : ι → Fin d → k) (g : PS k 1 d) :
    MvPolynomial ι k →ₗ[k] k where
  toFun Q := MvPowerSeries.constantCoeff (DpolyOf (B.FK k) u Q g)
  map_add' P Q := by rw [GE.dpolyOf_add_P, map_add]
  map_smul' a Q := by
    rw [GE.dpolyOf_smul_P, map_mul, MvPowerSeries.constantCoeff_C, RingHom.id_apply, smul_eq_mul]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols


