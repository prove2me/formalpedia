-- Prove2me | Definitions.Def_SecondBestBT_IsFeasible
-- name    : SecondBestBT_IsFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:46:17.010608+00:00
-- url     : https://prove2.me/theorems/7803dadf-4e9b-42bf-9d9c-06c2c0ab88b4
-- title:
--   Feasible mechanism: well defined, BIC, interim IR, ex-ante WBB
-- statement:
--   A mechanism is **feasible** on the type set $T$ for the priors $F_S,F_B$ if it is well defined, Bayesian incentive compatible on $T$, interim individually rational on $T$, and ex-ante weakly budget balanced. These are the mechanisms over which the second-best benchmark is taken.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 2, pp.4–5

import Mathlib
import Definitions.Def_SecondBestBT_WellDefined
import Definitions.Def_SecondBestBT_IsBIC
import Definitions.Def_SecondBestBT_IsInterimIR
import Definitions.Def_SecondBestBT_IsExAnteWBB

open MeasureTheory

namespace SecondBestBT

/-- A mechanism is feasible on the type set `T` when it is well defined, BIC, interim IR and
ex-ante WBB: the class over which the second-best benchmark is taken (Liu–Qin–Ren–Wang,
arXiv:2606.03849, held version sha256 17184930…, Section 2, p.5: "the supremum of GFT over BIC,
interim-IR, ex-ante WBB mechanisms"). -/
def IsFeasible (T : Set ℝ) (μS μB : Measure ℝ) (M : Mechanism) : Prop :=
  WellDefined T μS μB M ∧ IsBIC T μS μB M ∧ IsInterimIR T μS μB M ∧ IsExAnteWBB μS μB M

end SecondBestBT


