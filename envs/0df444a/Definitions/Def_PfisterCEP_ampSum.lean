-- Prove2me | Definitions.Def_PfisterCEP_ampSum
-- name    : PfisterCEP_ampSum
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:26:51.449502+00:00
-- url     : https://prove2.me/theorems/79f7acc3-ac97-4148-bf26-85647c798fd6
-- title:
--   Total amplitude $X=\sum_j X_j$
-- statement:
--   The **total amplitude** of $N$ modes is
--
--   $$X=\sum_{j=1}^{N}X_j=\sum_{j=1}^N (a_j+a_j^\dagger).$$
--
--   It is the quadrature whose squeezing gives the "total-amplitude" graph states of Fig. 3 when the sign of the coupling is reversed.
-- source:
--   Pfister, Graph states and carrier-envelope phase squeezing, arXiv:quant-ph/0701104v2, Sec. b, p.2 (Fig. 3; quadratures of the left column)

import Mathlib
import Definitions.Def_PfisterCEP_ampQuad

namespace PfisterCEP

/-- **Total amplitude `X = ∑ⱼ Xⱼ`.**
O. Pfister, *Graph states and carrier-envelope phase squeezing*, arXiv:quant-ph/0701104v2, Sec. b, p.2 (Fig. 3: "Graph states for total-phase or total-amplitude squeezing"; the
amplitude quadratures `Xⱼ` of the left column). -/
def ampSum {A : Type*} [Ring A] [Algebra ℂ A] {N : ℕ} (a ad : Fin N → A) : A :=
  ∑ j, ampQuad a ad j

end PfisterCEP


