-- Prove2me | Definitions.Def_mme_stothers_phi233_exact_label
-- name    : mme_stothers_phi233_exact_label
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-02T22:45:50.800549+00:00
-- url     : https://prove2.me/theorems/683e3ca0-2c2f-4e04-97d5-137b6574c613
-- title:
--   Canonical fine-block label of an exact phi_233 address
-- statement:
--   For each coordinate of a supported exact $\varphi_{233}$ profile, select the corresponding one of the ten fine-block labels. The accompanying structural identity states that applying the ten-label pattern map recovers the coordinate's three first-square grades. This provides a stable index for grouping literal tensor factors by their exact profile multiplicities.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(v), printed p. 366, and the ten-term decomposition used in its proof; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi233_profile_data

open MME

namespace MME.StothersFourth.Phi233

set_option autoImplicit false

/-- The fine-block label selected at one coordinate of an exact `phi_233` profile. -/
noncomputable def exactLabelAt
    {N alpha beta gamma delta : ℕ}
    (x : ExactProfileAddress N alpha beta gamma delta)
    (j : Fin (2 * N)) : Fin 10 :=
  Classical.choose (x.1.2.1 j)

@[simp] theorem addressType_exactLabelAt
    {N alpha beta gamma delta : ℕ}
    (x : ExactProfileAddress N alpha beta gamma delta)
    (j : Fin (2 * N)) :
    addressType x.1.1 j = pattern (exactLabelAt x j) :=
  Classical.choose_spec (x.1.2.1 j)

end MME.StothersFourth.Phi233


