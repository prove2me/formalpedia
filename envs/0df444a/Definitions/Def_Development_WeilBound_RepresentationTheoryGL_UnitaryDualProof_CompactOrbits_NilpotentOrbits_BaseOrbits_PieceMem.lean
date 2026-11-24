-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_BaseOrbits_PieceMem
-- name    : Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_BaseOrbits_PieceMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:44.634005+00:00
-- url     : https://prove2.me/theorems/d3800272-6a85-421f-976e-2978baa50bad
-- title:
--   Piece Mem
-- statement:
--   Definitions and structural lemmas for Piece Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/BaseOrbits/PieceMem.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Set GroundTheory.Automorphic.Whittaker
namespace PositivityTheory.RgUd.T.Nil.BasePf
variable {Y W G : Type*} [TopologicalSpace Y] [T2Space Y] [TopologicalSpace W] [T2Space W]
  [Group G] [MulAction G W]
def rel (K : Subgroup G) : Setoid W where
  r a b := ∃ g ∈ K, g • b = a
  iseqv :=
    { refl := fun a => ⟨1, K.one_mem, one_smul _ _⟩
      symm := fun {a b} ⟨g, hg, h⟩ => ⟨g⁻¹, K.inv_mem hg, by rw [← h, inv_smul_smul]⟩
      trans := fun {a b c} ⟨g, hg, h⟩ ⟨g', hg', h'⟩ => ⟨g * g', K.mul_mem hg hg', by rw [mul_smul, h', h]⟩ }
abbrev TF (X : Type*) [TopologicalSpace X] : Submodule ℂ (X → ℂ) :=
  GroundTheory.Automorphic.locallyConstantCompactSupport X ℂ ℂ
variable {ι : Type*}
end PositivityTheory.RgUd.T.Nil.BasePf


