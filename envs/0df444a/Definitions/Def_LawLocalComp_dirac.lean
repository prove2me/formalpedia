-- Prove2me | Definitions.Def_LawLocalComp_dirac
-- name    : LawLocalComp_dirac
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:11:18.15911+00:00
-- url     : https://prove2.me/theorems/9c6cf9c5-d923-49a0-a783-a7244c893366
-- title:
--   Point mass $\delta_t$
-- statement:
--   For $t\ge 0$, the **point mass** $\delta_t$ is the law with $\mathbb P(\delta_t=t)=1$. These are the paper's constant inputs $t$.
--
--   **Formalization Note** For $t<0$ the atom is clipped to $\max\{t,0\}=0$, so the function is total on $\mathbb R$; every use has $t\ge0$.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), §1, p.2; §5, p.8

import Mathlib
import Definitions.Def_LawLocalComp_Law

namespace LawLocalComp

/-- **The point mass `δ_t`.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), §1, p.2 ("point masses are included"); §5, p.8 (constant inputs `t`).

`dirac t` puts mass `1` on `max t 0`; for `t ≥ 0` it is the point mass at `t`.

**Formalization Note.** Laws live on `[0, ∞)`, so a negative argument is clipped to `0`; every use
in this mission has `t ≥ 0`. -/
noncomputable def dirac (t : ℝ) : Law where
  w := Finsupp.single (max t 0) 1
  nonneg := by
    intro x
    rw [Finsupp.single_apply]
    split_ifs <;> norm_num
  supp := by
    intro x hx
    have hx' := Finsupp.support_single_subset hx
    rw [Finset.mem_singleton] at hx'
    subst hx'
    exact Set.mem_Ici.mpr (le_max_right t 0)
  sum_one := by
    rw [Finsupp.support_single _ one_ne_zero]
    simp

end LawLocalComp


