-- Prove2me | Definitions.Def_FlexRigidity_chanDiv
-- name    : FlexRigidity_chanDiv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:45.983269+00:00
-- url     : https://prove2.me/theorems/5648e6f9-413f-41b1-a4de-4c66bbfac66c
-- title:
--   Channel sandwiched divergence $D_\alpha(\mathcal E\|\mathcal F)$ (no stabilizer)
-- statement:
--   For a channel $\mathcal E\in\mathrm{CPTP}(Q,O)$ and a CP map $\mathcal F$ with the same input and output,
--   $$D_\alpha(\mathcal E\|\mathcal F)=\sup_{\rho\in S_=(Q)}D_\alpha(\mathcal E[\rho]\|\mathcal F[\rho]).$$
--   No purifying ("stabilizer") register is inserted (Remark 2.10); a stabilized divergence is written with an explicit $\mathrm{id}_R$.
--
--   **Formalization Note** $D_\alpha$ is the sandwiched Rényi divergence `divergence` of the reused module `QAlgorithms_Papers_Independent_Dependency50_P35`: base 2, normalized by $\operatorname{Tr}\rho$, $+\infty$ off support for $\alpha>1$, as in Definition 2.7. The supremum is in $\overline{\mathbb R}$.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Definition 2.10 and Remark 2.10, p. 22

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

/-- **Channel sandwiched divergence** (Arqand–Kundu–Tan, *Flexible rigidity*, arXiv:2610.00444,
artifact sha256 8c67699d…, Definition 2.10, p. 22): for a channel `E` and a CP map `F` with the
same input and output, `D_α(E‖F) = sup_{ρ ∈ S_=(Q)} D_α(E[ρ]‖F[ρ])`. **No stabilizer** is inserted
(Remark 2.10): a stabilized divergence is written with `idTensorSuperop` explicitly.

**Formalization Note** `D_α` is the sandwiched divergence `divergence` of the reused
`Dependency50.P35` module (base 2, trace-normalized, `+∞` off support for `α > 1`). The supremum
is an `EReal` `sSup` over normalized density matrices. -/
def chanDiv {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] (a : ℝ)
    (E F : Superop ι κ) : EReal :=
  sSup {v : EReal | ∃ ρ : Matrix ι ι ℂ, Density ρ ∧ v = divergence a (E ρ) (F ρ)}

end FlexRigidity


