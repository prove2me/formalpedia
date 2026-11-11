-- Prove2me | Definitions.Def_FlexRigidity_genIdx
-- name    : FlexRigidity_genIdx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:20:17.101205+00:00
-- url     : https://prove2.me/theorems/ea2793da-675c-4298-86ab-bea7ec008c68
-- title:
--   The set $E$ of the first $m$ generation rounds
-- statement:
--   For a string $u\in\{\mathrm{test},\mathrm{gen}\}^n$ with at least $m$ generation rounds, $E$ is the lexicographically first set of $m$ indices with $u_i=\mathrm{gen}$, i.e. the $m$ smallest such indices, listed in increasing order.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Protocol 2, step 3(a), p. 41; §5.6, p. 56

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_RoundO
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **The set `E` of Protocol 2, step 3(a)** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, p. 41, and the channel `M` of §5.6, p. 56): the
lexicographically first `m` indices `i` with `u_i = gen`, listed in increasing order, provided
there are at least `m` generation rounds. `genSet u` is the set of generation rounds. -/
def genSet {n : ℕ} (u : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => u i = false

/-- The `j`-th element (in increasing order) of the first `m` generation rounds. -/
def genIdx {n m : ℕ} (u : Fin n → Bool) (h : m ≤ (genSet u).card) (j : Fin m) : Fin n :=
  (genSet u).orderEmbOfFin rfl (Fin.castLE h j)

end FlexRigidity


