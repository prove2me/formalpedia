-- Prove2me | Definitions.Def_AvgPHETH_Supplement_restrictRound
-- name    : AvgPHETH_Supplement_restrictRound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:38:23.395892+00:00
-- url     : https://prove2.me/theorems/71220efb-42e2-481e-9d8c-7e7aa42617e3
-- title:
--   A restriction round: $p_j$-random restrictions of the unassigned variables of each family
-- statement:
--   A $p$-random restriction of a family $\mathcal V$ of variables over an alphabet $\Sigma$ (Definition 4.4) chooses a uniformly random subset of $\mathcal V$ of size $\lfloor p|\mathcal V|\rfloor$ to leave unassigned and sets all other variables to independent uniformly random values of $\Sigma$.
--
--   A **restriction round** of the oracle construction applies, independently for each family of each group that is still to be completed, a $p_j$-random restriction to the currently unassigned variables of the family, where $j$ is the depth of the family.
--
--   This definition is the round as a deterministic function of the partial assignment $\rho$ before the round and of fresh seeds, one sequence of real numbers per variable.
--
--   **Formalization Note** The theorems take the seeds independent and uniform on $[0,1]$. The first seed of a variable is a priority: among the $N$ unassigned variables of a family, those with fewer than $\lfloor p_jN\rfloor$ unassigned family members of smaller priority stay unassigned; with probability one the priorities are distinct and this is a uniformly random subset of size $\lfloor p_jN\rfloor$. The next seeds give the bits of the value (a bit is $1$ iff its seed is below $1/2$). Assigned variables and groups that are not to be restricted are left unchanged.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, step 1 of the construction, pp.40–41 (PDF 42–43); Definition 4.4, p.17 (PDF 19)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_CVar_IsValid
import Definitions.Def_AvgPHETH_Supplement_CVar_valLen
import Definitions.Def_AvgPHETH_Supplement_CVar_SameFamily
import Definitions.Def_AvgPHETH_Supplement_pExp

namespace AvgPHETH.Supplement

/-- One **restriction round** of the oracle construction, as a deterministic function of fresh seeds
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, step 1 of the construction, pp.40–41 (PDF 42–43), with the `p`-random restriction of
Definition 4.4, p.17 (PDF 19)): independently for each family of each group `(k, n)` with `live k n`,
a `p_j`-random restriction is applied to the currently unassigned variables of the family (`j` its
depth): `⌊p_j N⌋` of the `N` unassigned variables, a uniformly random subset of that size, stay
unassigned, and every other one gets an independent uniformly random value of its alphabet.

**Formalization Note** `ρ` is the partial assignment before the round (`none` = unassigned) and `u v c`
are the seeds of the variable `v` in this round, real numbers that the theorems take independent and
uniform on `[0,1]`. Channel `0` is a priority: the unassigned variables of a family that stay
unassigned are those with fewer than `⌊p_j N⌋ = N / 2^{pExp}` unassigned family members of smaller
priority, which for distinct priorities (probability one) is the set of the `⌊p_j N⌋` smallest, a
uniformly random subset of that size. Channel `l + 1` gives the `l`-th bit of the value (`1` iff the
seed is `< 1/2`), a uniform value of `{0,1}^{valLen}`. Seeds of different rounds are independent, so
conditionally on the earlier rounds this is the page's restriction. Assigned variables, names that
are not variables, and groups that are not `live` are left as they are. -/
noncomputable def restrictRound (ε : ℕ → ℝ) (u : CVar → ℕ → ℝ) (live : ℕ → ℕ → Prop)
    (ρ : CVar → Option (List Bool)) : CVar → Option (List Bool) := by
  classical
  exact fun v =>
    if v.IsValid ε ∧ live v.k v.x.length ∧ ρ v = none then
      if {w : CVar | w.IsValid ε ∧ v.SameFamily w ∧ ρ w = none ∧ u w 0 < u v 0}.ncard <
          {w : CVar | w.IsValid ε ∧ v.SameFamily w ∧ ρ w = none}.ncard /
            2 ^ pExp ε v.path.length v.x.length then
        none
      else some ((List.range (v.valLen ε)).map (fun l => decide (u v (l + 1) < 1 / 2)))
    else ρ v

end AvgPHETH.Supplement


