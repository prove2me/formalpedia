-- Prove2me | Definitions.Def_SybilClinch_Run_wealth
-- name    : SybilClinch_Run_wealth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:41:32.056633+00:00
-- url     : https://prove2.me/theorems/fcd6b99e-e2c9-433b-892b-ce80f84d7c26
-- title:
--   Quantity-denominated wealth $W_N=X_N+B_N/p$
-- statement:
--   For a set $N$ of identities, $W_N:=X_N+B_N/p$ (45): the $X$ already received plus the amount of $X$ the remaining effective budget could buy at the current price. Effective budgets are zero at and after the terminal state.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §4.6, (45), p.22 (PDF p.24)

import Mathlib
import Definitions.Def_SybilClinch_Run_alloc
import Definitions.Def_SybilClinch_Run_budOf

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §4.6, (45), printed p.22 (PDF p.24): the quantity-denominated wealth of a set `N` of
identities, `W_N := X_N + B_N/p` (effective budgets being zero at and after the terminal state). -/
noncomputable def Run.wealth (M : TargetMech) (P : OneSidedProfile) (R : Run) (N : Finset ℕ)
    (p : ℝ) : ℝ :=
  R.alloc N p + R.budOf M P N p / p

end SybilClinch


