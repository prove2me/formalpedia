-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
-- name    : GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:11:50.862734+00:00
-- url     : https://prove2.me/theorems/34bd330c-132e-4f77-9549-f7887f838b38
-- title:
--   Rep Base
-- statement:
--   Definitions and structural lemmas for Rep Base, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RepBase.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic.HarishChandra
abbrev Poly (n : ℕ) := MvPolynomial (Fin n × Fin n) ℂ
variable {n : ℕ}
noncomputable def rowOp (i j : Fin n) : Module.End ℂ (Poly n) :=
  ∑ k : Fin n, (LinearMap.mulLeft ℂ (MvPolynomial.X (i, k) : Poly n)) ∘ₗ
    (MvPolynomial.pderiv (j, k) : Derivation ℂ (Poly n) (Poly n)).toLinearMap
end GroundTheory.Automorphic.HarishChandra


