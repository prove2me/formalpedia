-- Prove2me | Definitions.Def_ChanTomoNB_choiDist
-- name    : ChanTomoNB_choiDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:29:20.273764+00:00
-- url     : https://prove2.me/theorems/06474a47-8e00-4132-8579-3c270f1b4e1a
-- title:
--   Choi trace norm distance $d_1^{-1}\|C_{\mathcal E}-C_{\mathcal F}\|_1$
-- statement:
--   For superoperators $\mathcal E,\mathcal F:L(\mathbb C^{d_1})\to L(\mathbb C^{d_2})$ the **Choi trace norm distance** is
--   $$
--   \frac1{d_1}\,\|C_{\mathcal E}-C_{\mathcal F}\|_1 ,
--   $$
--   where $\|M\|_1=\operatorname{tr}\sqrt{M^\dagger M}$ is the trace (Schatten-1) norm.
--
--   It is one of the two error metrics of the tomography problem.
--
--   **Formalization Note** $\|\cdot\|_1$ is the published `WildeQIT.traceNorm`; $d_1$ is the number of input basis states. Defined for all linear maps, so it applies to estimates that are not channels.
-- source:
--   Chen, Oufkir, Quantum channel tomography: optimal bounds in the near-boundary regime, arXiv:2611.03639v1, §2.1, p.10

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_ChanTomoNB_choi

open Matrix

namespace ChanTomoNB

/-- The Choi trace norm distance `d1⁻¹ ‖C_E − C_F‖₁`. Chen, Oufkir, *Quantum channel tomography:
optimal bounds in the near-boundary regime*, arXiv:2611.03639v1, §2.1, p.10.

**Formalization Note.** `‖·‖₁` is the published `WildeQIT.traceNorm` (`Tr √(M†M)`), and
`d1 = |A|` is the input dimension. Defined for all linear maps, so it applies to estimates that
are not channels. -/
noncomputable def choiDist {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (E F : Superop A B) : ℝ :=
  WildeQIT.traceNorm (choi E - choi F) / Fintype.card A

end ChanTomoNB


