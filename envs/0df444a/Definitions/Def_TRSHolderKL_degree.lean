-- Prove2me | Definitions.Def_TRSHolderKL_degree
-- name    : TRSHolderKL_degree
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:55:29.082999+00:00
-- url     : https://prove2.me/theorems/bdd233be-16bb-4dfe-917d-d3d239ceb540
-- title:
--   Degree of singularity (Definition 3.4)
-- statement:
--   The **degree of singularity** $d$ of a system $q_i(x)\le0$, $i\in[m]$, is $0$ if the system has no nonlinear singular inequality, and otherwise one plus the number of irregular inequalities. It determines the Hölder exponent $1/2^d$ in the error bound of Lemma 3.5.
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, Definition 3.4, p.5

import Mathlib
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_TRSHolderKL_IsNonlinear
import Definitions.Def_TRSHolderKL_IsSingularIn
import Definitions.Def_TRSHolderKL_IsIrregular
open RBMSensitivity (E)

namespace TRSHolderKL

open Classical in
/-- Definition 3.4, Jiang and Li, arXiv:1911.11955v2, p.5: the degree of singularity of the
system is `0` if it has no nonlinear singular inequality, and otherwise one plus the number
of irregular inequalities. -/
noncomputable def degree {n m : ℕ} (q : Fin m → E n → ℝ) : ℕ :=
  if ∃ i, IsNonlinear (q i) ∧ IsSingularIn q Finset.univ i then
    1 + (Finset.univ.filter fun i => IsIrregular q i).card
  else 0

end TRSHolderKL


