-- Prove2me | Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ThetaBasic
-- name    : Formalism_HermitianLattices_HermitianLatticesProofs_ThetaBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:58:28.019268+00:00
-- url     : https://prove2.me/theorems/f4f93ad6-af38-42df-8d96-7006e598947f
-- title:
--   Theta Basic
-- statement:
--   Definitions and structural lemmas for Theta Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ThetaBasic.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.K
noncomputable section
namespace Formalism.HermitianLatticesTheory
def thetaBasic_eqv {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
    [Module K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V] (g : V ≃ₗ[K] V)
    (L : Submodule (NumberField.RingOfIntegers K) V) : L ≃ gmap g L where
  toFun x := ⟨g x, Submodule.mem_map_of_mem x.2⟩
  invFun y := ⟨g.symm y, by
    obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.1 y.2
    have hz' : g z = (y : V) := hzy
    rw [← hz', LinearEquiv.symm_apply_apply]
    exact hz⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
end Formalism.HermitianLatticesTheory


