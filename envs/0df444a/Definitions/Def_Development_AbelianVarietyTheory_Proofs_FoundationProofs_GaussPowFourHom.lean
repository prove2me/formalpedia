-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GaussPowFourHom
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_GaussPowFourHom
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:12.883568+00:00
-- url     : https://prove2.me/theorems/641bbbec-bd89-427b-8b81-596ebfb2db67
-- title:
--   Gauss Pow Four Hom
-- statement:
--   Definitions and structural lemmas for Gauss Pow Four Hom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GaussPowFourHom.lean

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
namespace GlobalTheory.TripleIntertwiner
open Classical
section
variable {V : Type*} [AddCommGroup V]
abbrev rep {B A : AddSubgroup V} (q : A ⧸ B.addSubgroupOf A) : V := ((Quotient.out q : A) : V)
end
section
variable {V : Type*} [AddCommGroup V] {F : Type} [AddCommGroup F] [Module ℂ F]
def itw (W : V → F →ₗ[ℂ] F) (A B : AddSubgroup V) (f : F) : F :=
  ((Real.sqrt ((A.addSubgroupOf B).index : ℝ))⁻¹ : ℂ) • ∑ᶠ q : B ⧸ A.addSubgroupOf B, W (rep q) f
variable {W : V → F →ₗ[ℂ] F} {c : V → V → ℂ}
end
end GlobalTheory.TripleIntertwiner


