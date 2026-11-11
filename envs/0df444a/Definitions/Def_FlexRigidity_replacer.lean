-- Prove2me | Definitions.Def_FlexRigidity_replacer
-- name    : FlexRigidity_replacer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:56.232948+00:00
-- url     : https://prove2.me/theorems/908e190f-ce37-4ec7-b0bf-d88b7085ec7f
-- title:
--   Replacer map $X_{SQ}\mapsto\omega_S\otimes\operatorname{Tr}_SX_{SQ}$
-- statement:
--   For a fixed operator $\omega_S$, the **replacer** map on $SQ$ is $\mathcal P[X_{SQ}]=\omega_S\otimes\operatorname{Tr}_S X_{SQ}$. In Definition 2.4 $\omega_S$ is a state; in Lemma 3.4 it is any positive definite operator, not necessarily normalized.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Definition 2.4, p. 18; Lemma 3.4, p. 24

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

/-- **Replacer map** `P[X_{SQ}] = ω_S ⊗ Tr_S X_{SQ}` (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, Definition 2.4, p. 18, and Lemma 3.4, p. 24, where
`ω_S` is positive definite but need not be normalized). -/
def replacer {S Q : Type} [Fintype S] (ω : Matrix S S ℂ) : Superop (S × Q) (S × Q) :=
  fun X => Matrix.kronecker ω (rightMarginal X)

end FlexRigidity


