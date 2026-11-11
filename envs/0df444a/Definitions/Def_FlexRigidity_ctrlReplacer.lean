-- Prove2me | Definitions.Def_FlexRigidity_ctrlReplacer
-- name    : FlexRigidity_ctrlReplacer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:15:01.124195+00:00
-- url     : https://prove2.me/theorems/3604f020-bbc6-472a-b6ce-dc8998e513ea
-- title:
--   Controlled replacer, eq. (16)
-- statement:
--   Fix a set $\mathcal Z^*$ of classical values, positive reals $a_z$ and positive definite operators $\omega^z_S$. The CP map $\mathcal P$ on $ZSQ$ reads $Z$ and acts as
--   $$\mathcal P[|z\rangle\langle z|_Z\otimes\sigma_{SQ}]=\begin{cases}a_z|z\rangle\langle z|_Z\otimes\sigma_{SQ},&z\in\mathcal Z^*,\\ |z\rangle\langle z|_Z\otimes\omega^z_S\otimes\operatorname{Tr}_S\sigma_{SQ},&z\notin\mathcal Z^*.\end{cases}$$
--   So $Z$ is retained and $S$ is replaced by a $z$-dependent operator whenever $z\notin\mathcal Z^*$.
--
--   **Formalization Note** The paper specifies $\mathcal P$ on inputs classical on $Z$. Here $\mathcal P$ first discards the off-diagonal $z\neq z'$ blocks (pinching $Z$), which is how "reads $Z$" acts; on $Z$-classical inputs, the only inputs it is applied to, this is exactly (16).
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), eq. (16), p. 26

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

/-- **Controlled replacer, eq. (16)** (Arqand–Kundu–Tan, *Flexible rigidity*, arXiv:2610.00444,
artifact sha256 8c67699d…, p. 26): for a set `Z*` of classical values, positive reals `a_z` and
positive definite `ω^z_S`, the CP map `P` reads `Z` and acts as
`P[|z⟩⟨z|_Z ⊗ σ_{SQ}] = a_z |z⟩⟨z|_Z ⊗ σ_{SQ}` for `z ∈ Z*` and
`P[|z⟩⟨z|_Z ⊗ σ_{SQ}] = |z⟩⟨z|_Z ⊗ ω^z_S ⊗ Tr_S σ_{SQ}` for `z ∉ Z*`.

**Formalization Note** The paper defines `P` only on inputs classical on `Z`. Here `P` first
pinches `Z` (off-diagonal `z ≠ z′` blocks are discarded), which is how "reads `Z`" acts; on
`Z`-classical inputs (all inputs it is ever applied to, since it follows a channel with classical
output `Z`) it is exactly (16). The data conditions `a_z > 0`, `ω^z` positive definite are
hypotheses of the statements. -/
def ctrlReplacer {Z S Q : Type} [DecidableEq Z] [Fintype S] (Zs : Finset Z) (a : Z → ℝ)
    (ω : Z → Matrix S S ℂ) : Superop (Z × S × Q) (Z × S × Q) :=
  fun X => Matrix.of fun i j =>
    if i.1 = j.1 then
      (if i.1 ∈ Zs then (a i.1 : ℂ) * X i j
       else ω i.1 i.2.1 j.2.1 * ∑ t : S, X (i.1, t, i.2.2) (i.1, t, j.2.2))
    else 0

end FlexRigidity


