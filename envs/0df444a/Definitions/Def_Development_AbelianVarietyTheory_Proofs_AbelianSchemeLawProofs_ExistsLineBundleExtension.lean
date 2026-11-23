-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:30:31.273915+00:00
-- url     : https://prove2.me/theorems/13f1aa9b-a844-4533-9c60-18040518b1f1
-- title:
--   Exists Line Bundle Extension
-- statement:
--   Definitions and structural lemmas for Exists Line Bundle Extension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLineBundleExtension.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
noncomputable section
namespace GlobalTheory.ExtendLineBundle
variable {X Y : Scheme.{0}} [IsIntegral X]
theorem genericPoint_mem {U : X.Opens} {x : X} (hx : x ∈ U) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩
def localSubring (x : X) : Subring X.functionField :=
  (algebraMap (X.presheaf.stalk x) X.functionField).range
def localUnits (x : X) : Subgroup X.functionFieldˣ := (localSubring x).toSubmonoid.units
def Compatible (T : Set (X.Opens × X.functionFieldˣ)) : Prop :=
  ∀ p ∈ T, ∀ q ∈ T, ∀ y, y ∈ p.1 → y ∈ q.1 → p.2 / q.2 ∈ localUnits y
open Classical in

def unitVal (U : X.Opens) : Γ(X, U)ˣ →* X.functionFieldˣ :=
  if h : genericPoint X ∈ U then Units.map (X.presheaf.germ U _ h).hom else 1
variable (j : Y ⟶ X) [IsOpenImmersion j]
def imageUnit (V : Y.Opens) : Γ(Y, V)ˣ ≃* Γ(X, j ''ᵁ V)ˣ :=
  Units.mapEquiv (j.appIso V).symm.commRingCatIsoToRingEquiv.toMulEquiv
def imageVal (V : Y.Opens) : Γ(Y, V)ˣ →* X.functionFieldˣ :=
  (unitVal (j ''ᵁ V)).comp (imageUnit j V).toMonoidHom
end GlobalTheory.ExtendLineBundle
namespace GlobalTheory
open ExtendLineBundle
end GlobalTheory


