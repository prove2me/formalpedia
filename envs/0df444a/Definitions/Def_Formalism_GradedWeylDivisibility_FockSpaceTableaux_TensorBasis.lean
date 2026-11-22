-- Prove2me | Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_TensorBasis
-- name    : Formalism_GradedWeylDivisibility_FockSpaceTableaux_TensorBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:43:09.548666+00:00
-- url     : https://prove2.me/theorems/797fa336-607d-418b-be41-d357066633d4
-- title:
--   Tensor Basis
-- statement:
--   Definitions and structural lemmas for Tensor Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/TensorBasis.lean

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.RingTheory.Localization.Module
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial PiTensorProduct
open scoped Pointwise
open Module
noncomputable section
namespace Formalism.GradedWeylDivisibility
section Field
variable (K : Type*) [Field K] {S : Type*} [Fintype S] [DecidableEq S] {k n : ℕ}
def ldtensor_psi : PiTensorProduct K (fun _ : S => MvPolynomial (Fin k × Fin n) K) →ₗ[K] MvPolynomial (S × (Fin k × Fin n)) K :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra K S (MvPolynomial (S × (Fin k × Fin n)) K)).compLinearMap
    (fun s => (blockEmb K (k := k) (n := n) s).toLinearMap))
end Field
end Formalism.GradedWeylDivisibility


