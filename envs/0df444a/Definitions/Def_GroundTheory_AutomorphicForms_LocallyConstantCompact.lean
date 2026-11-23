-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
-- name    : GroundTheory_AutomorphicForms_LocallyConstantCompact
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:46.2638+00:00
-- url     : https://prove2.me/theorems/cf952f29-7750-41a0-b102-24e2e4216491
-- title:
--   Locally Constant Compact
-- statement:
--   Definitions and structural lemmas for Locally Constant Compact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LocallyConstantCompact.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
open Set Filter Topology
open scoped Pointwise
section Space
variable (X : Type*) [TopologicalSpace X] (R E : Type*) [Semiring R] [AddCommMonoid E]
  [Module R E]
def locallyConstantCompactSupport : Submodule R (X → E) where
  carrier := {f | IsLocallyConstant f ∧ HasCompactSupport f}
  add_mem' {f g} hf hg := ⟨hf.1.comp₂ hg.1 (· + ·), hf.2.add hg.2⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  smul_mem' c f hf := ⟨hf.1.comp (c • ·), hf.2.mono fun x hx => by
    by_contra h
    exact hx (by simp [Function.notMem_support.1 h])⟩
variable {X R E}
end Space
section Group
variable {G : Type*} [Group G] {E : Type*}
variable [TopologicalSpace G] [IsTopologicalGroup G] {R : Type*} [Semiring R] [AddCommMonoid E]
  [Module R E]
theorem finite_image_mk_tsupport (K : OpenSubgroup G) {f : G → E} (hf : HasCompactSupport f) :
    (QuotientGroup.mk '' tsupport f : Set (G ⧸ (K : Subgroup G))).Finite :=
  (hf.image QuotientGroup.continuous_mk).finite_of_discrete
variable [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
end Group
end GroundTheory.Automorphic


