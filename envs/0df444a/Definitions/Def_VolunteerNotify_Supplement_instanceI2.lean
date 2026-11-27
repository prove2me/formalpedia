-- Prove2me | Definitions.Def_VolunteerNotify_Supplement_instanceI2
-- name    : VolunteerNotify_Supplement_instanceI2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:24:31.183865+00:00
-- url     : https://prove2.me/theorems/c83036f1-dc1a-48af-996f-476034031464
-- title:
--   Instance $\mathcal I_2$ — geometric inactivity, $q=1/n$
-- statement:
--   For $n\ge1$ and $q=1/n$, instance $\mathcal I_2(n)$ has $V=n$ volunteers, $S=1$ task type and $T=n^2+1$ periods. The inter-activity time is geometric with parameter $q$,
--   $$
--   g(\tau)=q(1-q)^{\tau-1}\quad(\tau\ge1),\qquad g(0)=0 .
--   $$
--   A task arrives in period $1$ with probability $\lambda_{1,1}=1$ and in every later period with probability $\lambda_{1,t}=q$, and every volunteer matches with probability $p_{v,1}=q$.
--
--   This instance gives the second term of the bound in Theorem 2, through Lemma 5.
--
--   **Formalization Note** Periods are `Fin`-indexed, so paper period $t$ is the value $t-1$. The geometric weights are proved to be a probability law on $\{1,2,\dots\}$ inside the definition.
-- source:
--   Manshadi, Rodilitz, Online Policies for Efficient Volunteer Crowdsourcing, arXiv:2002.08474v7, Instance I2, p.22 (repeated p.37)

import Mathlib
import Definitions.Def_VolunteerNotify_Instance

namespace VolunteerNotify.Supplement

/-- The geometric law with parameter `q` on `{1, 2, …}`, Manshadi–Rodilitz, arXiv:2002.08474v7,
Instance I2, p.22: `g(τ) = q (1 − q)^{τ − 1}` for `τ ≥ 1`, and `g(0) = 0`. -/
noncomputable def geomMass (q : ℝ) (τ : ℕ) : ℝ :=
  if τ = 0 then 0 else q * (1 - q) ^ (τ - 1)

/-- For `0 < q ≤ 1` the geometric weights are nonnegative. -/
theorem geomMass_nonneg {q : ℝ} (h0 : 0 < q) (h1 : q ≤ 1) (τ : ℕ) : 0 ≤ geomMass q τ := by
  unfold geomMass
  split_ifs
  · exact le_refl 0
  · have : 0 ≤ 1 - q := by linarith
    positivity

/-- For `0 < q ≤ 1` the geometric weights sum to `1`. -/
theorem geomMass_hasSum {q : ℝ} (h0 : 0 < q) (h1 : q ≤ 1) : HasSum (geomMass q) 1 := by
  have hr0 : 0 ≤ 1 - q := by linarith
  have hr1 : 1 - q < 1 := by linarith
  have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left q
  have hq : q * (1 - (1 - q))⁻¹ = 1 := by
    rw [sub_sub_cancel]; exact mul_inv_cancel₀ h0.ne'
  rw [hq] at hg
  rw [← hasSum_nat_add_iff' 1]
  simpa [geomMass, Finset.sum_range_one] using hg

/-- Instance `I2(n)`, Manshadi–Rodilitz, arXiv:2002.08474v7, p.22 (repeated p.37), for `n ≥ 1`
and `q = 1/n`: `V = n` volunteers, `S = 1` task type, `T = n² + 1` periods, geometric
inter-activity times `g(τ) = q (1 − q)^{τ − 1}`, arrival probabilities `λ_{1,1} = 1` and
`λ_{1,t} = q` for `t ∈ [T] ∖ [1]`, and match probabilities `p_{v,1} = q` for all `v`.

**Formalization Note.** Periods are `Fin`-indexed: paper period `t` is the `Fin` value `t − 1`,
so `λ_{1,1}` is the value at `0`. -/
noncomputable def instanceI2 (n : ℕ) (hn : 1 ≤ n) : Instance n 1 (n ^ 2 + 1) where
  lam _ t := if (t : ℕ) = 0 then 1 else 1 / (n : ℝ)
  p _ _ := 1 / (n : ℝ)
  g := geomMass (1 / (n : ℝ))
  lam_nonneg s t := by
    split_ifs
    · exact zero_le_one
    · positivity
  lam_sum_le_one t := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [Fin.sum_univ_one]
    split_ifs
    · exact le_refl 1
    · exact div_le_one_of_le₀ hn' (by positivity)
  p_mem v s := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact ⟨by positivity, div_le_one_of_le₀ hn' (by positivity)⟩
  g_nonneg τ := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact geomMass_nonneg (by positivity) (div_le_one_of_le₀ hn' (by positivity)) τ
  g_zero := by simp [geomMass]
  g_hasSum := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact geomMass_hasSum (by positivity) (div_le_one_of_le₀ hn' (by positivity))

end VolunteerNotify.Supplement


