-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BigCellLocal
-- name    : Development_AutomorphicSpectrum_Proofs_MembershipProofs_BigCellLocal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:23.887533+00:00
-- url     : https://prove2.me/theorems/8188463d-b6b0-4652-8dfb-0c4b0ccfa979
-- title:
--   Big Cell Local
-- statement:
--   Definitions and structural lemmas for Big Cell Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/BigCellLocal.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsSkewOfDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix
namespace GlobalTheory.CompanionTheory.VacLoc.BigCellLocal
section Iso
variable {A : Type} [CommRing A] (σ : A →+* A) {ι : Type} [Fintype ι] [DecidableEq ι]
def Iso (D₁ D₂ M : Matrix ι ι A) : Prop := Mᵀ * D₁ * M.map σ = D₂
variable {σ}
end Iso
section Split
variable {A : Type} [CommRing A] {σ : A →+* A} {β : Type} [Fintype β] [DecidableEq β]
def Wm (A : Type) [CommRing A] (β : Type) [DecidableEq β] : Matrix (β ⊕ β) (β ⊕ β) A := fromBlocks 0 1 1 0
end Split
section Lift
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E} {A : Subring E} {σ : A →+* A}
  {ι : Type} [Fintype ι] [DecidableEq ι]
end Lift
end GlobalTheory.CompanionTheory.VacLoc.BigCellLocal


