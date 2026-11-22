-- Prove2me | Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_DualLattice
-- name    : Formalism_LatticeTheta_LatticeThetaProofs_DualLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:48:11.454732+00:00
-- url     : https://prove2.me/theorems/fa745464-1cc6-4c52-a98f-c4a8d897af5a
-- title:
--   Dual Lattice
-- statement:
--   Definitions and structural lemmas for Dual Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/DualLattice.lean

import Definitions.Def_Formalism_LatticeTheta_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.H
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
lemma dualLattice_innerₗ_nondegenerate : (innerₗ V).Nondegenerate := by
  first
    | exact (LinearMap.BilinForm.nondegenerate_iff (innerₗ V)
        (fun x => by rw [innerₗ_apply_apply]; exact real_inner_self_nonneg) isSymm_inner).2
        (fun x => by rw [innerₗ_apply_apply]; exact inner_self_eq_zero)
    | (unfold LinearMap.BilinForm.Nondegenerate
       intro m hm
       have h := hm m
       rw [innerₗ_apply_apply] at h
       exact inner_self_eq_zero.mp h)
variable [FiniteDimensional ℝ V]
end Formalism.H


