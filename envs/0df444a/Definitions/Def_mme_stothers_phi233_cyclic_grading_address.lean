-- Prove2me | Definitions.Def_mme_stothers_phi233_cyclic_grading_address
-- name    : mme_stothers_phi233_cyclic_grading_address
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-02T23:37:35.018432+00:00
-- url     : https://prove2.me/theorems/25933bf5-f2b1-4d23-b0c7-fe1e1b50cbd5
-- title:
--   Cyclic product grading address for a $\Phi_{233}$ ambient edge
-- statement:
--   For a cyclic ambient edge $(x,y,z)$ consisting of three same-marginal $\Phi_{233}$ addresses, this definition records its address in the product grading on $T\otimes\pi T\otimes\pi^2T$. At a mode $i$ and word coordinate $j$, it combines the grade of $x$ at mode $i$, the grade of $y$ pulled back through the inverse cyclic permutation, and the grade of $z$ pulled back through the inverse twice-cyclic permutation. The resulting alphabet has $5^3$ elements.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), cyclic construction and Lemma 5.1(v), pp. 365--367; https://www.maths.ed.ac.uk/~sandy/a11164.pdf

import Definitions.Def_mme_stothers_phi233_cyclic_ambient_data
import Definitions.Def_mme_cyclic_triple_grading

open MME

namespace MME.StothersFourth.Phi233

set_option autoImplicit false

/-- The grade word of a cyclic ambient edge in the cyclic product grading. -/
def cyclicGradingAddress
    {N alpha beta gamma delta : ℕ}
    (e : CyclicAmbientEdge N alpha beta gamma delta)
    (i : Fin 3) (j : Fin (2 * N)) : Fin (5 * (5 * 5)) :=
  mmeCyclicTripleGrade
    (fun s ↦ e.1.1 s j)
    (fun s ↦ e.2.1.1 s j)
    (fun s ↦ e.2.2.1 s j) i

end MME.StothersFourth.Phi233


