-- Prove2me | Definitions.Def_VolunteerNotify_Supplement_instanceI3
-- name    : VolunteerNotify_Supplement_instanceI3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:24:53.383978+00:00
-- url     : https://prove2.me/theorems/73e51867-0664-5e52-9142-2991ba4337c2
-- title:
--   Instance $\mathcal I_3$ — deterministic inactivity of length $n$
-- statement:
--   For $n\ge1$, instance $\mathcal I_3(n)$ has $V=n$ volunteers, $S=1$ task type and $T=n^2$ periods. The inter-activity time is deterministic of length $n$, $g(\tau)=\mathbb 1(\tau=n)$, so its MDHR is $0$ when $n\ge2$. A task arrives in every period with probability $\lambda_{1,t}=1/n$, and every volunteer matches with probability $p_{v,1}=1/n$.
--
--   This instance gives the bound $0.334$ of Theorem 2 at $q=0$, through Lemma 6.
--
--   **Formalization Note** $n\ge1$ is required so that $g(0)=0$. The source takes $n$ "sufficiently large"; that qualifier is stated in Lemma 6.
-- source:
--   Manshadi, Rodilitz, Online Policies for Efficient Volunteer Crowdsourcing, arXiv:2002.08474v7, Instance I3, p.23 (repeated p.42)

import Mathlib
import Definitions.Def_VolunteerNotify_Instance

namespace VolunteerNotify.Supplement

/-- Instance `I3(n)`, Manshadi–Rodilitz, arXiv:2002.08474v7, p.23 (repeated p.42), for `n ≥ 1`:
`V = n` volunteers, `S = 1` task type, `T = n²` periods, deterministic inter-activity time of
length `n`, `g(τ) = 𝟙(τ = n)`, arrival probabilities `λ_{1,t} = 1/n` for all `t`, and match
probabilities `p_{v,1} = 1/n` for all `v`.

**Formalization Note.** `n ≥ 1` is needed for `g(0) = 0` (`Z > 0`). The source takes `n`
"sufficiently large"; that qualifier is in Lemma 6, not in the instance. Its MDHR is `0` for
`n ≥ 2` (p.23). -/
noncomputable def instanceI3 (n : ℕ) (hn : 1 ≤ n) : Instance n 1 (n ^ 2) where
  lam _ _ := 1 / (n : ℝ)
  p _ _ := 1 / (n : ℝ)
  g τ := if τ = n then 1 else 0
  lam_nonneg s t := by positivity
  lam_sum_le_one t := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [Fin.sum_univ_one]
    exact div_le_one_of_le₀ hn' (by positivity)
  p_mem v s := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact ⟨by positivity, div_le_one_of_le₀ hn' (by positivity)⟩
  g_nonneg τ := by
    split_ifs
    · exact zero_le_one
    · exact le_refl 0
  g_zero := by
    have : (0 : ℕ) ≠ n := by omega
    simp [this]
  g_hasSum := hasSum_ite_eq n 1

end VolunteerNotify.Supplement


