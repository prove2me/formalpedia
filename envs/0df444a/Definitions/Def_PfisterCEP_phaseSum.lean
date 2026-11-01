-- Prove2me | Definitions.Def_PfisterCEP_phaseSum
-- name    : PfisterCEP_phaseSum
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:26:45.312599+00:00
-- url     : https://prove2.me/theorems/df0da1d9-f454-420c-9405-64e3d9fc735f
-- title:
--   Phase sum $\mathbf P=\sum_{j=1}^N P_j$
-- statement:
--   The **phase sum** of $N$ modes is
--
--   $$\mathbf P=\sum_{j=1}^{N}P_j=\sum_{j=1}^N i\,(a_j^\dagger-a_j).$$
--
--   In a frequency comb it is the total phase of the comb, i.e. the carrier-envelope phase whose squeezing is the subject of the paper.
-- source:
--   Pfister, Graph states and carrier-envelope phase squeezing, arXiv:quant-ph/0701104v2, Sec. b, p.2, left column

import Mathlib
import Definitions.Def_PfisterCEP_phaseQuad

namespace PfisterCEP

/-- **Phase sum `𝐏 = ∑_{j=1}^N Pⱼ`.**
O. Pfister, *Graph states and carrier-envelope phase squeezing*, arXiv:quant-ph/0701104v2, Sec. b, p.2, left column: "the phase sum P = ∑_{j=1}^N Pj" (bold **P**). -/
def phaseSum {A : Type*} [Ring A] [Algebra ℂ A] {N : ℕ} (a ad : Fin N → A) : A :=
  ∑ j, phaseQuad a ad j

end PfisterCEP


