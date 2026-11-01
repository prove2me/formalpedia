-- Prove2me | Definitions.Def_PfisterCEP_phaseQuad
-- name    : PfisterCEP_phaseQuad
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:26:00.99351+00:00
-- url     : https://prove2.me/theorems/2d20d3a3-3045-4253-b8dd-37c011c3f30d
-- title:
--   Phase quadrature $P_j=i(a_j^\dagger-a_j)$
-- statement:
--   For modes $a_j$, $a_j^\dagger$ the **phase quadrature** of mode $j$ is
--
--   $$P_j=i\,(a_j^\dagger-a_j).$$
--
--   It is the field quadrature called "phase" in the paper; the phase sum $\mathbf P=\sum_j P_j$ is built from it.
--
--   **Formalization Note** The sign is the printed one; with $i(a_j-a_j^\dagger)$ instead, the phase sum would be amplified rather than squeezed by $H_3$.
-- source:
--   Pfister, Graph states and carrier-envelope phase squeezing, arXiv:quant-ph/0701104v2, Sec. b, p.2, left column

import Mathlib

namespace PfisterCEP

/-- **Phase quadrature `Pⱼ = i(a†ⱼ − aⱼ)`.**
O. Pfister, *Graph states and carrier-envelope phase squeezing*, arXiv:quant-ph/0701104v2, Sec. b, p.2, left column: "Pj = i(a†j − aj) (“phase”)".

**Formalization Note** `ad j` plays `a†ⱼ`; the sign is the printed one (`a†ⱼ − aⱼ`, the dagger
prints as "a." in the text layer). -/
def phaseQuad {A : Type*} [Ring A] [Algebra ℂ A] {N : ℕ} (a ad : Fin N → A) (j : Fin N) : A :=
  Complex.I • (ad j - a j)

end PfisterCEP


