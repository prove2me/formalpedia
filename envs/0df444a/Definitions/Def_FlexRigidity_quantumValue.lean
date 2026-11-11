-- Prove2me | Definitions.Def_FlexRigidity_quantumValue
-- name    : FlexRigidity_quantumValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:20:58.265993+00:00
-- url     : https://prove2.me/theorems/98fd050e-b6fc-479c-8c1d-60c475b1acb7
-- title:
--   Quantum value $\omega^*(\mathsf G)$
-- statement:
--   $\omega^*(\mathsf G)$ is the supremum of the winning probability over all finite-dimensional quantum strategies: normalized states on $M_{\mathrm A}\otimes M_{\mathrm B}$ of any finite dimensions and POVMs $\{H^x_a\}_a$, $\{K^y_b\}_b$.
--
--   **Formalization Note** Registers of dimension $d$ are $\mathbb C^d$, indexed by $\{0,\dots,d-1\}$; POVMs are `POVM` of the reused module `QAlgorithms_Papers_Independent_Dependency50_P35`. The supremum is over a set of reals bounded by $1$.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Definition 5.1, p. 39

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_winProb
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Quantum value** `ω*(G)`, Definition 5.1 (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, p. 39): the supremum of the winning probability over
**all finite-dimensional** quantum strategies: a normalized state on `M_A ⊗ M_B` of any finite
dimensions and POVMs `{H^x_a}_a`, `{K^y_b}_b`.

**Formalization Note** Registers of dimension `d` are `Fin d`; every finite-dimensional strategy is
unitarily equivalent to one of these. POVMs are `POVM` of the reused `Dependency50.P35` module
(PSD elements summing to `I`). The real `sSup` is over a set bounded by `1`; it is nonempty as soon
as `A` and `B` are nonempty. -/
def quantumValue {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) : ℝ :=
  sSup {w : ℝ | ∃ (dA dB : ℕ) (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (H : X → A → Matrix (Fin dA) (Fin dA) ℂ) (K : Y → B → Matrix (Fin dB) (Fin dB) ℂ),
    Density ρ ∧ (∀ x, POVM (H x)) ∧ (∀ y, POVM (K y)) ∧ w = winProb G ρ H K}

end FlexRigidity


