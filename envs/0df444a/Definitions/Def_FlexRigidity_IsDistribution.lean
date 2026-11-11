-- Prove2me | Definitions.Def_FlexRigidity_IsDistribution
-- name    : FlexRigidity_IsDistribution
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:51.772522+00:00
-- url     : https://prove2.me/theorems/c8808b06-9c7c-45a1-8683-06d7a01a6c55
-- title:
--   Probability distributions on a finite set
-- statement:
--   A function $Q:C\to\mathbb R$ on a finite set is a **probability distribution** when $Q(c)\ge0$ for all $c$ and $\sum_cQ(c)=1$.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), §2.1, p. 17

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

/-- **Probability distributions** on a finite set (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, §2.1, p. 17): nonnegative weights summing to one. -/
def IsDistribution {C : Type} [Fintype C] (Q : C → ℝ) : Prop :=
  (∀ c, 0 ≤ Q c) ∧ ∑ c, Q c = 1

end FlexRigidity


