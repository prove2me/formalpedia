-- Prove2me | Definitions.Def_FlexRigidity_IsAcceptSet
-- name    : FlexRigidity_IsAcceptSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:17:32.232202+00:00
-- url     : https://prove2.me/theorems/9437497e-fd84-4b7c-b546-0fa32af0ec3a
-- title:
--   Accept condition, Postulate Set 4.1(ii)
-- statement:
--   $S_\Omega$ is a nonempty closed convex subset of the probability simplex on $C$; the accept event is $\Omega=\{\mathbf c:\mathrm{freq}_{\mathbf c}\in S_\Omega\}$.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Postulate Set 4.1(ii), p. 28

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_IsDistribution
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Accept condition, Postulate Set 4.1(ii)** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, p. 28): `S_Ω` is a nonempty closed convex subset of
the probability simplex on `C`; the accept event is `Ω = {c : freq_c ∈ S_Ω}`. -/
def IsAcceptSet {C : Type} [Fintype C] (SΩ : Set (C → ℝ)) : Prop :=
  SΩ.Nonempty ∧ IsClosed SΩ ∧ Convex ℝ SΩ ∧ ∀ Q ∈ SΩ, IsDistribution Q

end FlexRigidity


