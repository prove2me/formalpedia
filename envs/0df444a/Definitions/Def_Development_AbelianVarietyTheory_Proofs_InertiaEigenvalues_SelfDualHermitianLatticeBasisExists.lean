-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualHermitianLatticeBasisExists
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualHermitianLatticeBasisExists
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:44.716124+00:00
-- url     : https://prove2.me/theorems/5d462958-66f5-40e0-ba5a-acfd73527750
-- title:
--   Self Dual Hermitian Lattice Basis Exists
-- statement:
--   Definitions and structural lemmas for Self Dual Hermitian Lattice Basis Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SelfDualHermitianLatticeBasisExists.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
namespace GlobalTheory.SelfDualLattice
section Forms
variable {K : UQ} {V : Type} [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V]
  {h : V → V → K.E}
def formL (hadd : ∀ x y z, h (x + y) z = h x z + h y z) (hsmul : ∀ (c : K.E) x z, h (c • x) z = c * h x z)
    (z : V) : V →ₗ[K.E] K.E where
  toFun x := h x z
  map_add' x y := hadd x y z
  map_smul' c x := hsmul c x z
end Forms
end GlobalTheory.SelfDualLattice
namespace GlobalTheory.SelfDualLattice
variable {K : UQ} {V : Type} [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V]
  {h : V → V → K.E}
end GlobalTheory.SelfDualLattice
namespace GlobalTheory.SelfDualLattice
end GlobalTheory.SelfDualLattice
namespace GlobalTheory.SelfDualLattice
end GlobalTheory.SelfDualLattice


