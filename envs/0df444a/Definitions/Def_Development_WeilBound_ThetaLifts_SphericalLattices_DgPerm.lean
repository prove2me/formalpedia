-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_SphericalLattices_DgPerm
-- name    : Development_WeilBound_ThetaLifts_SphericalLattices_DgPerm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:13.955001+00:00
-- url     : https://prove2.me/theorems/94cbc54f-c70b-48c2-8c3e-dda4512d236a
-- title:
--   Dg Perm
-- statement:
--   Definitions and structural lemmas for Dg Perm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SphericalLattices/DgPerm.lean

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
namespace PositivityTheory.Sph.M2.GenA
open Matrix
variable {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]
def dg : (n → Kˣ) →* GL n K where
  toFun D := ⟨diagonal fun i => (D i : K), diagonal fun i => (((D i)⁻¹ : Kˣ) : K),
    by simp [diagonal_mul_diagonal], by simp [diagonal_mul_diagonal]⟩
  map_one' := by ext1; simp
  map_mul' a b := by ext1; simp [diagonal_mul_diagonal]
def tv {i j : n} (h : i ≠ j) (s : K) : GL n K :=
  ⟨transvection i j s, transvection i j (-s), by rw [transvection_mul_transvection_same i j h]; simp,
    by rw [transvection_mul_transvection_same i j h]; simp⟩
end PositivityTheory.Sph.M2.GenA
end


