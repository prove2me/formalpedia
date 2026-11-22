-- Prove2me | Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassTelescope
-- name    : Formalism_HermitianLattices_HermitianLatticesProofs_MassTelescope
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:18:45.044226+00:00
-- url     : https://prove2.me/theorems/023c202a-7214-4dd5-b746-5a2711a0c594
-- title:
--   Mass Telescope
-- statement:
--   Definitions and structural lemmas for Mass Telescope, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/MassTelescope.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


set_option autoImplicit false
open NumberField
noncomputable section
namespace Formalism.HermitianLatticesTheory
section MassTelescopeAux
variable (K : Type) [Field K] [NumberField K] [StarRing K]
def massTelescope_form (n : ℕ) : (Fin n → K) →ₗ⋆[K] (Fin n → K) →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => ∑ i, star (x i) * y i)
    (by intro m₁ m₂ y; simp [star_add, add_mul, Finset.sum_add_distrib])
    (by
      intro c m y
      simp only [Pi.smul_apply, smul_eq_mul, star_mul, Finset.mul_sum, starRingEnd_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring)
    (by intro m y₁ y₂; simp [mul_add, Finset.sum_add_distrib])
    (by
      intro c m y
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring)
def massTelescope_lat (n : ℕ) : Submodule (RingOfIntegers K) (Fin n → K) :=
  Submodule.span (RingOfIntegers K) (Set.range (Pi.basisFun K (Fin n)))
end MassTelescopeAux
end Formalism.HermitianLatticesTheory


