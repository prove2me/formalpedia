-- Prove2me | Definitions.Def_MultitaskContracts_Instance_MMLRP
-- name    : MultitaskContracts_Instance_MMLRP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:32:51.49917+00:00
-- url     : https://prove2.me/theorems/8f5581aa-7e40-4e5b-9636-d6db750adbdd
-- title:
--   Multivariate Monotone Likelihood Ratio Property (MMLRP), eq. (2) / Definition 10
-- statement:
--   An instance satisfies the **Multivariate Monotone Likelihood Ratio Property (MMLRP)** if for every pair of strategies $S\subseteq S'$ and every pair of performances $Y\subseteq Y'$,
--   $$P_{S'}(Y')\,P_S(Y)\ \ge\ P_{S'}(Y)\,P_S(Y'). \tag{2}$$
--   It extends the classical monotone likelihood ratio property to the partially ordered strategy and performance spaces $2^K$ (ordered by inclusion), and is the second class of the dependence hierarchy.
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), eq. (2), p.6 (PDF p.8); Definition 10, p.42 (PDF p.44)

import Mathlib
import Definitions.Def_MultitaskContracts_Instance

set_option autoImplicit false

namespace MultitaskContracts

open scoped ENNReal

/-- **Multivariate Monotone Likelihood Ratio Property (MMLRP)** (eq. (2), §2, p.6, PDF 8;
Definition 10, p.42, PDF 44): for every pair of strategies `S ⊆ S'` and every pair of
performances `Y ⊆ Y'`, `P_{S'}(Y') P_S(Y) ≥ P_{S'}(Y) P_S(Y')`.
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), eq. (2), p.6 and Definition 10, p.42. -/
def Instance.MMLRP {K : Type*} [Fintype K] [DecidableEq K] (I : Instance K) : Prop :=
  ∀ S S' Y Y' : Finset K, S ⊆ S' → Y ⊆ Y' →
    I.P S' Y * I.P S Y' ≤ I.P S' Y' * I.P S Y

end MultitaskContracts


