-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqLoc
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqLoc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:46:04.868128+00:00
-- url     : https://prove2.me/theorems/b933df86-ce2d-40cd-9ef3-b75da523c732
-- title:
--   Exp Uniq Loc
-- statement:
--   Definitions and structural lemmas for Exp Uniq Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqLoc.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_Ij_pow_eq_bot
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp

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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
open ReciprocityTheory.ChartRestriction.G.Chart (JetR zR IsUnivChart sp spMap spMap_comp comp_one')
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
section Maps
variable (d : ℕ)
abbrev sumJ (M : ℕ) : Jet R (Fin 1 × Fin d) M →ₐ[R] Jet R (Fin 2 × Fin d) M :=
  jetSubstP M fun p : Fin 1 × Fin d => (X ((0 : Fin 2), p.2) + X ((1 : Fin 2), p.2) : MvPolynomial (Fin 2 × Fin d) R)
abbrev cpy (M : ℕ) (i : Fin 2) : Jet R (Fin 1 × Fin d) M →ₐ[R] Jet R (Fin 2 × Fin d) M := jetCopy d M i
def diag (M : ℕ) : Jet R (Fin 2 × Fin d) M →ₐ[R] Jet R (Fin 1 × Fin d) M :=
  jetMap (fun q : Fin 2 × Fin d => (X ((0 : Fin 1), q.2) : MvPolynomial (Fin 1 × Fin d) R)) fun _ => X_mem_orig _
end Maps
variable {n : ℕ}
def cpyU (M : ℕ) (i : Fin 2) : JetR R (Fin n) M →ₐ[R] Jet R (Fin 2 × Fin n) M :=
  ReciprocityTheory.ChartRestriction.G.Chart.jetLift R (Ij R (Fin 2 × Fin n) M) (Ij_pow_eq_bot _ M) (fun j => zz M (i, j))
    (fun j => Ideal.subset_span ⟨(i, j), rfl⟩)
section Univ
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G}
  (hx : IsUnivChart G n x)
include hx
end Univ
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc


