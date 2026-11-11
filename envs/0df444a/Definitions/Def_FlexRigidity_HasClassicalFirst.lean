-- Prove2me | Definitions.Def_FlexRigidity_HasClassicalFirst
-- name    : FlexRigidity_HasClassicalFirst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:15:10.245279+00:00
-- url     : https://prove2.me/theorems/90e590f3-1e86-4b56-a341-e985920c3699
-- title:
--   Classical output register
-- statement:
--   A map $\Phi$ with output $ZW$ has **classical output $Z$** when every output is block diagonal in the computational basis of $Z$: $\Phi(X)_{(z,w),(z',w')}=0$ whenever $z\ne z'$, for every input $X$.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Lemma 3.5, p. 26; Postulate Set 4.1(i), p. 28

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

/-- **Classical output register** (Arqand–Kundu–Tan, *Flexible rigidity*, arXiv:2610.00444,
artifact sha256 8c67699d…, Lemma 3.5, p. 26, and Postulate Set 4.1(i), p. 28): a map
`Φ : Superop ι (Z × W)` has classical output `Z` when every output is block diagonal in the
computational basis of `Z`: `Φ(X)_{(z,w),(z′,w′)} = 0` whenever `z ≠ z′`, for every input `X`. -/
def HasClassicalFirst {ι Z W : Type} (Φ : Superop ι (Z × W)) : Prop :=
  ∀ (X : Matrix ι ι ℂ) (i j : Z × W), i.1 ≠ j.1 → Φ X i j = 0

end FlexRigidity


