-- Prove2me | Definitions.Def_PfisterCEP_ampQuad
-- name    : PfisterCEP_ampQuad
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:26:03.503465+00:00
-- url     : https://prove2.me/theorems/3b4d0e09-1f5d-4bc1-8d56-1f48c410e78d
-- title:
--   Amplitude quadrature $X_j=a_j+a_j^\dagger$
-- statement:
--   For modes $a_j$, $a_j^\dagger$ the **amplitude quadrature** of mode $j$ is
--
--   $$X_j=a_j+a_j^\dagger .$$
--
--   It is the field quadrature called "amplitude" in the paper; the amplitude differences $X_k-X_l$ and the total amplitude $\sum_j X_j$ are built from it.
-- source:
--   Pfister, Graph states and carrier-envelope phase squeezing, arXiv:quant-ph/0701104v2, Sec. b, p.2, left column

import Mathlib

namespace PfisterCEP

/-- **Amplitude quadrature `Xⱼ = aⱼ + a†ⱼ`.**
O. Pfister, *Graph states and carrier-envelope phase squeezing*, arXiv:quant-ph/0701104v2, Sec. b, p.2, left column: "the field quadratures Xj = aj + a†j (“amplitude”)".

**Formalization Note** `ad j` plays `a†ⱼ`. -/
def ampQuad {A : Type*} [Ring A] [Algebra ℂ A] {N : ℕ} (a ad : Fin N → A) (j : Fin N) : A :=
  a j + ad j

end PfisterCEP


