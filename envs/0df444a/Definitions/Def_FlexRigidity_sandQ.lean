-- Prove2me | Definitions.Def_FlexRigidity_sandQ
-- name    : FlexRigidity_sandQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:15:21.402721+00:00
-- url     : https://prove2.me/theorems/d3a81c0b-e105-4c39-86c2-d0a92f061ef8
-- title:
--   The sandwiched quasi-divergence $Q_\alpha(\rho\|\sigma)$
-- statement:
--   For PSD $\rho,\sigma$ and $\alpha\in(0,1)\cup(1,\infty)$,
--   $$Q_\alpha(\rho\|\sigma)=\operatorname{Tr}\Big[\big(\sigma^{\frac{1-\alpha}{2\alpha}}\rho\,\sigma^{\frac{1-\alpha}{2\alpha}}\big)^\alpha\Big]\quad(\rho\neq0),\qquad Q_\alpha(0\|\sigma)=0,$$
--   and for $\alpha>1$, $Q_\alpha=+\infty$ unless $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$. Negative powers use the Moore–Penrose pseudoinverse. It is used for subnormalized blocks, as in the block function $h_{i,c}$ of Lemma 4.3.
--
--   **Formalization Note** Values in $[0,\infty]$. The trace expression is `rawTrace` of the reused platform module `QAlgorithms_Papers_Independent_Dependency50_P35`, with the same pseudoinverse convention.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Definition 2.7, p. 19

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

open Classical in
/-- **The sandwiched quasi-divergence** `Q_α(ρ‖σ)` (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, Definition 2.7, p. 19):
`Q_α(ρ‖σ) = Tr[(σ^{(1−α)/(2α)} ρ σ^{(1−α)/(2α)})^α]` for `ρ ≠ 0`, `Q_α(0‖σ) = 0`, and for `α > 1`
`Q_α = +∞` unless `supp ρ ⊆ supp σ`; negative powers use the Moore–Penrose pseudoinverse.

**Formalization Note** Values are in `ℝ≥0∞` so that the `+∞` convention is representable. The
trace formula is `rawTrace` of the reused `Dependency50.P35` module (the same pseudoinverse
convention). `Dominates σ ρ` is `ker σ ⊆ ker ρ`, i.e. `supp ρ ⊆ supp σ` for PSD arguments. -/
def sandQ {I : Type} [Fintype I] [DecidableEq I] (a : ℝ) (ρ σ : Matrix I I ℂ) : ℝ≥0∞ :=
  if ρ = 0 then 0 else if 1 < a ∧ ¬ Dominates σ ρ then ⊤ else ENNReal.ofReal (rawTrace a ρ σ)

end FlexRigidity


