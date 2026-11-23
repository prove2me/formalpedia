-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_LieBridgeB
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_LieBridgeB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:47.735335+00:00
-- url     : https://prove2.me/theorems/b7f1dacd-156d-46bb-968a-ccc431d1a35a
-- title:
--   Lie Bridge B
-- statement:
--   Definitions and structural lemmas for Lie Bridge B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/LieBridgeB.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
open Polynomial
section Split
variable {K S M O ι : Type} [Field K] [CharZero K] [CommRing S] [Algebra K S] [AddCommGroup M] [Module S M]
  [CommRing O] [Fintype ι] [DecidableEq ι]
def IsEigV (ρ : O →+* Module.End S M) (χ : O →+* K) (m : M) : Prop := ∀ a, ρ a m = algebraMap K S (χ a) • m
def lagr (x : ι → K) (τ : ι) : K[X] := Lagrange.basis Finset.univ x τ
end Split
section Split2
variable {K S M O ι : Type} [Field K] [CharZero K] [CommRing S] [Algebra K S] [AddCommGroup M] [Module S M]
  [CommRing O] [Fintype ι] [DecidableEq ι] (ρ : O →+* Module.End S M) (χ : ι → O →+* K) (α : O)
def proj (τ : ι) : Module.End S M := aeval (ρ α) ((lagr (fun τ => χ τ α) τ).map (algebraMap K S))
end Split2
end ReciprocityTheory.ChartRestriction.G.PullbackSections


