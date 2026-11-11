-- Prove2me | Definitions.Def_FlexRigidity_IsSubnormalized
-- name    : FlexRigidity_IsSubnormalized
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:44.08405+00:00
-- url     : https://prove2.me/theorems/b722c8de-5f92-4bb6-91e0-aa9811c38337
-- title:
--   Subnormalized states $S_\le(A)$
-- statement:
--   An operator $X$ on a finite register $A$ is a **subnormalized state** when $X\succeq0$ and $\operatorname{Tr}X\le1$. The zero operator is included. This is the domain of the smoothing in the smooth max-divergence.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), §2.2, p. 17

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Subnormalized states** `S_≤(A)` (Arqand–Kundu–Tan, *Flexible rigidity*, arXiv:2610.00444,
artifact sha256 8c67699d…, §2.2, p. 17): positive semidefinite operators of trace at most one.
The zero operator is included, as in the paper. -/
def IsSubnormalized {I : Type} [Fintype I] (X : Matrix I I ℂ) : Prop :=
  X.PosSemidef ∧ tr X ≤ 1

end FlexRigidity


