-- Prove2me | Definitions.Def_FlexRigidity_smoothMaxDiv
-- name    : FlexRigidity_smoothMaxDiv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:19:53.468798+00:00
-- url     : https://prove2.me/theorems/9242d580-67a7-443d-b810-174ec886afab
-- title:
--   Smooth max-divergence $D^\varepsilon_{\max}(\rho\|\sigma)$
-- statement:
--   For a nonzero subnormalized $\rho$, PSD $\sigma$ and $\varepsilon\in[0,\sqrt{\operatorname{Tr}\rho})$, the **$\varepsilon$-smooth max-divergence** is
--   $$D^\varepsilon_{\max}(\rho\|\sigma)=\inf_{\rho'\in S_\le(A),\ P(\rho',\rho)\le\varepsilon}D_{\max}(\rho'\|\sigma),\qquad D_{\max}(\rho'\|\sigma)=\inf\{\lambda:\rho'\le2^\lambda\sigma\},$$
--   smoothing in purified distance. It is the $\alpha=\infty$ case of Definition 2.9, the only smooth divergence the paper uses.
--
--   **Formalization Note** $D_{\max}$ is `maxRelative` of the reused module `QAlgorithms_Papers_Independent_Dependency50_P35` (an extended-real infimum, $+\infty$ when no $\lambda$ works). Values in $\overline{\mathbb R}$; the statements give the range of $\varepsilon$.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Definition 2.9, p. 20 (with Definition 2.7, p. 19)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_IsSubnormalized
import Definitions.Def_FlexRigidity_purifiedDist
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Smooth max-divergence** `D^ε_max(ρ‖σ)` (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, Definition 2.9, p. 20, at `α = ∞`):
`D^ε_max(ρ‖σ) = inf { D_max(ρ′‖σ) : ρ′ ∈ S_≤(A), P(ρ′, ρ) ≤ ε }`, smoothing in purified distance,
with `D_max(ρ′‖σ) = inf{λ : ρ′ ≤ 2^λ σ}` (Definition 2.7, p. 19).

**Formalization Note** `D_max` is `maxRelative` of the reused `Dependency50.P35` module (an
`EReal` infimum, `+∞` when no `λ` works). The paper uses `ε ∈ [0, √Tr ρ)` and nonzero
subnormalized `ρ`; statements state these ranges. -/
def smoothMaxDiv {I : Type} [Fintype I] [DecidableEq I] (ε : ℝ) (ρ σ : Matrix I I ℂ) : EReal :=
  sInf {v : EReal | ∃ ρ' : Matrix I I ℂ, IsSubnormalized ρ' ∧ purifiedDist ρ' ρ ≤ ε ∧
    v = maxRelative ρ' σ}

end FlexRigidity


