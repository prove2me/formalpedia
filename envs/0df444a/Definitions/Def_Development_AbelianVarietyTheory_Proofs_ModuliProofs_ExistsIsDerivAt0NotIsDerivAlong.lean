-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsDerivAt0NotIsDerivAlong
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsDerivAt0NotIsDerivAlong
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:41:13.75386+00:00
-- url     : https://prove2.me/theorems/721b3eea-5843-43b4-82d0-8ad0082557da
-- title:
--   Exists Is Deriv At0 Not Is Deriv Along
-- statement:
--   Definitions and structural lemmas for Exists Is Deriv At0 Not Is Deriv Along, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsDerivAt0NotIsDerivAlong.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PeriodMapPresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul


set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PeriodCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding IsTypeFn IsThetaFrame
open GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation hiding IsTypeFn IsThetaFrame
open scoped TensorProduct Topology
section Period
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
def imForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) : LinearMap.BilinForm ℝ (Fin g → ℂ) :=
  LinearMap.mk₂ ℝ (fun z w => (hermForm Hm z w).im)
    (fun a b c => by simp [hermForm, add_dotProduct])
    (fun r a b => by simp [hermForm, smul_dotProduct])
    (fun a b c => by simp [hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun r a b => by
      simp only [hermForm, star_smul, star_trivial, Matrix.mulVec_smul, dotProduct_smul]
      simp)
end Period
section Hol
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}
open Classical in

def jump (z : Fin 1 → ℂ) : Sp ℂ ⟶ Sp ℂ := spMap (if z = 0 then RingHom.id ℂ else starRingEnd ℂ)
end Hol
section Theta
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {g m : ℕ}
end Theta
section Family
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n)
end Family
end GlobalTheory.PeriodCompare


