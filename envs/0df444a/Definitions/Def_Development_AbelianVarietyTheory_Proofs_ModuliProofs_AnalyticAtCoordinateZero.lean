-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AnalyticAtCoordinateZero
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_AnalyticAtCoordinateZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:06:23.203971+00:00
-- url     : https://prove2.me/theorems/26aed102-b970-42a6-a28e-2384721e78b7
-- title:
--   Analytic At Coordinate Zero
-- statement:
--   Definitions and structural lemmas for Analytic At Coordinate Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/AnalyticAtCoordinateZero.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EventuallyEqOfAdditiveOfHasFDerivAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
namespace GlobalTheory.RelExp
variable {X : Scheme.{0}} {G : Over X}
abbrev pt {x : Sp ℂ ⟶ X} (a : Over.mk x ⟶ G) : Sp ℂ ⟶ G.left := a.left
abbrev crd {Z : Scheme.{0}} (U : Z.Opens) {κ : Type} (t : κ → Γ(Z, U)) (z : Sp ℂ ⟶ Z) : κ → ℂ :=
  fun i => valAt' z U (t i)
variable [GrpObj G] {g m n : ℕ} {y : (Fin m → ℂ) → (Sp ℂ ⟶ X)} {b₀ : Fin m → ℂ} {U : G.left.Opens}
  {t : Fin g → Γ(G.left, U)} {f : Fin n → Γ(G.left, U)} {O : Set ((Fin m → ℂ) × (Fin n → ℂ))}
abbrev crd0 (t : Fin g → Γ(G.left, U)) {x : Sp ℂ ⟶ X} (a : Over.mk x ⟶ G) : Fin g → ℂ :=
  crd U t (pt a) - crd U t (pt (1 : Over.mk x ⟶ G))
section Family
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {β : E → (Fin m → ℂ)}
  {a : ∀ w, Over.mk (y (β w)) ⟶ G} {w₀ : E}
end Family
end GlobalTheory.RelExp


