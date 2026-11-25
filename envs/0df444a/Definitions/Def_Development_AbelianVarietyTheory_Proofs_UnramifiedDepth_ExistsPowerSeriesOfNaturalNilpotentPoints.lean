-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsPowerSeriesOfNaturalNilpotentPoints
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsPowerSeriesOfNaturalNilpotentPoints
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T18:02:43.154486+00:00
-- url     : https://prove2.me/theorems/c57cc2b9-7153-465b-96e7-6236f7c89c91
-- title:
--   Exists Power Series Of Natural Nilpotent Points
-- statement:
--   Definitions and structural lemmas for Exists Power Series Of Natural Nilpotent Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsPowerSeriesOfNaturalNilpotentPoints.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MemSupSpanXPowIffAndIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NEvalSqZero
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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ChF
section
variable {R : Type} [CommRing R] (I : Ideal R) (n d : ℕ)
abbrev MainNotions (k : ℕ) : Type :=
  Geo.Tor.JetR R (Fin n × Fin d) k ⧸ (I ^ (k + 1)).map (algebraMap R (Geo.Tor.JetR R (Fin n × Fin d) k))
def xK (k : ℕ) : Fin n → Fin d → MainNotions I n d k := fun i j =>
  Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (MvPolynomial.X (i, j)))
abbrev JJ : Ideal (PS R n d) :=
  I.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin n × Fin d) R) ⊔
    Ideal.span (Set.range (MvPowerSeries.X : Fin n × Fin d → MvPowerSeries (Fin n × Fin d) R))
variable {n d}
def Lev (k : ℕ) (S : Type) [CommRing S] [Algebra R S] (a : Fin n → Fin d → S) : Prop :=
  Kills I k S ∧ Ideal.span (Set.range fun q : Fin n × Fin d => a q.1 q.2) ^ (k + 1) = ⊥
variable {I}
end
end GlobalTheory.ChF


