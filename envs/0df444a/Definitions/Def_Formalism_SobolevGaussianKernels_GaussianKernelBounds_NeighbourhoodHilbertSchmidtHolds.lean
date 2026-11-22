-- Prove2me | Definitions.Def_Formalism_SobolevGaussianKernels_GaussianKernelBounds_NeighbourhoodHilbertSchmidtHolds
-- name    : Formalism_SobolevGaussianKernels_GaussianKernelBounds_NeighbourhoodHilbertSchmidtHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:44:24.679025+00:00
-- url     : https://prove2.me/theorems/b671ed7f-6e7c-4b73-a561-81382b6a79c3
-- title:
--   Neighbourhood Hilbert Schmidt Holds
-- statement:
--   Definitions and structural lemmas for Neighbourhood Hilbert Schmidt Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SobolevGaussianKernels/GaussianKernelBounds/NeighbourhoodHilbertSchmidtHolds.lean

import Mathlib
import Definitions.Def_Formalism_SobolevGaussianKernels_StatementFU
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.SL.P
open Finset Module LinearMap Formalism.CorankShareLayerCake.FR Formalism.SL.FU
open scoped InnerProductSpace ComplexConjugate
section HS
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]
end HS
section Neb
variable {A : Type} [AddCommGroup A] [Fintype A] {H : Type} [AddCommGroup H] [Module ℂ H]
end Neb
end Formalism.SL.P


