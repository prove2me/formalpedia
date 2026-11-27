-- Prove2me | Definitions.Def_FreeOrderEPTAS_Supplement_convert
-- name    : FreeOrderEPTAS_Supplement_convert
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:38:31.006281+00:00
-- url     : https://prove2.me/theorems/272516b2-573c-4e1a-9e60-1e2bc1211091
-- title:
--   The conversion of Claim 6.3
-- statement:
--   Let $\sigma$ be a permutation and $t_1\ge\dots\ge t_n$ the thresholds of the optimal stopping rule for $Y$ on $\sigma$ ($t_s$ is the optimal continuation value after time $s$). Call time $s$ *kept* when $t_s\le\kappa_{\sigma(s)}$. The converted solution of Pandora's Box with Commitment probes the boxes of the kept times in the order $\sigma$ and selects the first $X_{\sigma(s)}\ge t_s$, stopping at the last kept box in any case; the other boxes are never probed. If no time is kept, it is the empty solution.
--
--   **Formalization Note** `convertWith κ t σ` takes the indices and thresholds as arguments; `convert P σ` uses Weitzman's indices and the thresholds $t_s=R_{s+1}$ of the base recursion for $Y$. The skipped boxes are placed after the kept ones in the permutation and are never reached.
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, proof of Claim 6.3, p.32

import Mathlib
import Definitions.Def_FreeOrderEPTAS_Supplement_pandoraOPT
import Definitions.Def_FreeOrderEPTAS_Supplement_Ylaw
import Definitions.Def_FreeOrderEPTAS_R

namespace FreeOrderEPTAS.Supplement

variable {n : ℕ}

open Classical in
/-- The conversion of Claim 6.3 (arXiv:2007.13121v3, p.32), for indices `κ`, thresholds `t` and a
permutation `σ` (`t s` is the threshold of the variable inspected at time `s`). A time `s` is *kept*
when `t s ≤ κ_{σ(s)}`; the others are skipped ("we can assume that t_i ≤ κ_i, since otherwise …
such variables can be ignored (skipped)"). If no time is kept, the result is the empty solution.
Otherwise the boxes of the kept times are probed first, in the order of `σ`, then the skipped ones;
the rule selects the first probed `X ≥ t` among the kept boxes, and stops at the last kept box in any
case, so the skipped boxes are never probed. -/
noncomputable def convertWith (κ : Fin n → WithTop ℝ) (t : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    PBCPolicy n :=
  let kept : Fin n → Prop := fun s => ((t s : ℝ) : WithTop ℝ) ≤ κ (σ s)
  let k : ℕ := (Finset.univ.filter kept).card
  if k = 0 then none
  else
    let π : Equiv.Perm (Fin n) := Tuple.sort (fun s => if kept s then s.val else n + s.val)
    some (π.trans σ,
      { stop := fun u obs => decide (u.val + 1 = k ∨ t (π u) ≤ obs (Fin.last u.val))
        measurable_stop := fun u => by
          refine measurable_to_bool ?_
          have : (fun obs : Fin (u.val + 1) → ℝ =>
              decide (u.val + 1 = k ∨ t (π u) ≤ obs (Fin.last u.val))) ⁻¹' {true} =
              {_obs | u.val + 1 = k} ∪ {obs | t (π u) ≤ obs (Fin.last u.val)} := by
            ext obs; simp
          rw [this]
          exact (MeasurableSet.const _).union
            (measurableSet_le measurable_const (measurable_pi_apply _)) })

/-- Claim 6.3's conversion of a permutation `σ` for the instance `Y` (arXiv:2007.13121v3, p.32):
the thresholds are those of the optimal stopping rule for `Y` on `σ`, `t_s = R_{s+1}` (the base
recursion `R (Ylaw P) σ (s + 1)`, 0-based), and the indices are Weitzman's `κ`. -/
noncomputable def convert (P : PandoraInstance n) (σ : Equiv.Perm (Fin n)) : PBCPolicy n :=
  convertWith (kappa P) (fun s => R (Ylaw P) σ (s.val + 1)) σ

end FreeOrderEPTAS.Supplement


