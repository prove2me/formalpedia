-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftCompJetSub
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftCompJetSub
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:35:36.785677+00:00
-- url     : https://prove2.me/theorems/cafa3ec1-b067-4aa9-9bc8-ef65abdcbe18
-- title:
--   Dual Lift Comp Jet Sub
-- statement:
--   Definitions and structural lemmas for Dual Lift Comp Jet Sub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/DualLiftCompJetSub.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_RestrictDiagCompInclFst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow

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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
namespace ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
theorem jetAug_zR_lemma {κ : Type} {m : ℕ} (j : κ) : jetAug R κ m (zR m j) = 0 := by
  first
  | (show MvPolynomial.aeval (fun _ : κ => (0 : R)) (MvPolynomial.X j) = 0
     simp)
  | simp [jetAug, zR, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
theorem sum_smul_zR_mem {a : ℕ} (m : ℕ) (c : Fin a → R) :
    ∑ i, c i • zR (R := R) m i ∈ RingHom.ker (jetAug R (Fin a) m) := by
  rw [RingHom.mem_ker, map_sum]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [map_smul, jetAug_zR_lemma i, smul_zero]
def jetSub {a b : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (m : ℕ) : JetR R (Fin b) m →ₐ[R] JetR R (Fin a) m :=
  jetLift R (RingHom.ker (jetAug R (Fin a) m)) (ker_jetAug_pow (Fin a) m)
    (fun k => ∑ i, T (Pi.single i 1) k • zR m i) (fun k => sum_smul_zR_mem m _)
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
end ReciprocityTheory.ChartRestriction.G.Chart


