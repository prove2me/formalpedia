-- Prove2me | Definitions.Def_FlexRigidity_cost
-- name    : FlexRigidity_cost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:23:27.821702+00:00
-- url     : https://prove2.me/theorems/ef7436de-ff4d-4b7a-bab3-21bed7bbd96c
-- title:
--   The cost function $\mathrm{cost}_{\alpha,\mu}(\gamma,\varepsilon)$, eq. (66)
-- statement:
--   For $1<\alpha<2$, $0<\mu<1$, $0\le\varepsilon\le(1-\gamma)/2$,
--   $$\mathrm{cost}_{\alpha,\mu}(\gamma,\varepsilon)=\max_{\substack{0\le\delta\le\omega^*\\0\le\eta\le\hat B_{\mathsf G}(\delta)}}\Big\{\frac{1-\gamma+\varepsilon}{\alpha-1}\log\Big[a_\mu^{1-\alpha}(1-\eta)^{2-\alpha}+\Big(\frac{|S|(|S|-1)}{\mu}\Big)^{\alpha-1}\eta^{2-\alpha}\Big]-\frac{2-\alpha}{\alpha-1}\min_{Q_C:\|Q_C-P_C\|_{\mathrm{tr}}\le\varepsilon}D(Q_C\|P^\delta_C)\Big\},$$
--   with $P^\delta_C=(1-\gamma,\gamma(\omega^*-\delta),\gamma(1-\omega^*+\delta))$, log base 2.
--
--   **Formalization Note** The max and min are extended-real suprema and infima (Lemma 5.11 proves finiteness).
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), eq. (66), p. 54

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_BGhat
import Definitions.Def_FlexRigidity_aMu
import Definitions.Def_FlexRigidity_klDiv
import Definitions.Def_FlexRigidity_SAcc
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **The cost function `cost_{α,µ}(γ, ε)`, eq. (66)** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, p. 54): for `1 < α < 2`, `0 < µ < 1`,
`0 ≤ ε ≤ (1−γ)/2`,
`cost = max_{0≤δ≤ω*, 0≤η≤B̂_G(δ)} { ((1−γ+ε)/(α−1)) log[a_µ^{1−α}(1−η)^{2−α} + (|S|(|S|−1)/µ)^{α−1} η^{2−α}] − ((2−α)/(α−1)) min_{Q_C : ‖Q_C − P_C‖_tr ≤ ε} D(Q_C‖P^δ_C) }`,
with `P^δ_C = (1−γ, γ(ω*−δ), γ(1−ω*+δ))`, log base 2. The cost depends on the game only through
`ω = ω*`, `s = |S|` and `van_G`.

**Formalization Note** The max and min are `EReal` `sSup`/`sInf` (Lemma 5.11 proves finiteness);
`Q_C` ranges over distributions on `C`. -/
def cost (van : ℝ → ℝ) (ω : ℝ) (s : ℕ) (α μ γ ε : ℝ) : EReal :=
  sSup {v : EReal | ∃ δ ∈ Set.Icc 0 ω, ∃ η ∈ Set.Icc 0 (BGhat van ω δ),
    v = (((1 - γ + ε) / (α - 1) * Real.logb 2 (aMu μ s ^ (1 - α) * (1 - η) ^ (2 - α) +
          ((s : ℝ) * (s - 1) / μ) ^ (α - 1) * η ^ (2 - α)) : ℝ) : EReal) -
        (((2 - α) / (α - 1) : ℝ) : EReal) *
          sInf {w : EReal | ∃ Q ∈ SAcc γ ω ε, w = klDiv Q (PC γ (ω - δ))}}

end FlexRigidity


