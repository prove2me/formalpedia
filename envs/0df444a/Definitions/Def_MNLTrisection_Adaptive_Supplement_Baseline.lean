-- Prove2me | Definitions.Def_MNLTrisection_Adaptive_Supplement_Baseline
-- name    : MNLTrisection_Adaptive_Supplement_Baseline
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:11:30.684312+00:00
-- url     : https://prove2.me/theorems/e591b43f-2bfd-47a8-8178-5d9cdab256c1
-- title:
--   Algorithms 1–2 — baseline trisection policy
-- statement:
--   For known revenues $r_i\in[0,1]$ and horizon $T\ge2$, the baseline policy starts with $[a,b]=[0,1]$, forms $x=(2a+b)/3$ and $y=(a+2b)/3$, and runs
--
--   $$n=16\lceil(y-x)^{-2}\ln T\rceil$$
--
--   inner iterations per epoch. Exploration offers the revenue level set $\mathcal L_y$, accumulates observed revenue $\rho_t$, and uses the confidence interval $\rho_t/t\pm\sqrt{\ln(T^2)/(2t)}$. Once $y$ leaves that interval, exploration statistics freeze. Each inner iteration then offers $\mathcal L_a$. The next interval is $[a,y]$ if the upper confidence bound is below $y$, and $[x,b]$ otherwise. Every offer consumes one customer, and execution truncates after exactly $T$ offers. The published state, level-set and revenue interfaces are reused, with a distinct baseline update.
--
--   This supplies the actual policy in Theorem 2, including its last partial epoch, without an oracle for unknown utilities.
--
--   **Formalization Note** Products and periods are zero based; inner counts are one based. Empty level sets are allowed, as in the published base model. The count is the algorithm box's $16\lceil\epsilon^{-2}\ln T\rceil$, whereas p.10 and Supplement B use conflicting placements of 16 and $\ln(T^2)$. At $T=1$ the printed loop has zero iterations and cannot serve the horizon; the total Lean function outside $T\ge2$ is not claimed to formalize that undefined execution.
-- source:
--   Chen, Wang & Zhou, An Optimal Policy for Dynamic Assortment Planning Under Uncapacitated Multinomial Logit Models, arXiv:1805.04785v2, PDF pp.9–11, Algorithms 1–2; Supplement B, PDF pp.22–23

import Mathlib
import Definitions.Def_MNLTrisection_Adaptive_Model

namespace MNLTrisection.Adaptive.Supplement

open MNLBandit.UCB

/-- Algorithm 1, PDF p.9 line 6: select the algorithm box's log T,
not the conflicting log(T²) in the prose and Supplement B. -/
noncomputable def baselineInnerLen (T : ℕ) (e : ℝ) : ℕ :=
  16 * ⌈e⁻¹ ^ 2 * Real.log (T : ℝ)⌉₊

/-- Algorithm 2 with δ = 1/T². Inner sample/iteration counts are one-based. -/
noncomputable def baselineRadius (T t : ℕ) : ℝ :=
  Real.sqrt (Real.log ((T : ℝ) ^ 2) / (2 * t))

/-- Baseline update, distinct from the published adaptive update.
Exploration consumes one customer, then exploitation consumes the next.
After exploration stops the confidence bounds and accumulated reward freeze. -/
noncomputable def baselineStep {N : ℕ} (r : Fin N → ℝ) (T : ℕ)
    (s : AlgState) (c : Option (Fin N)) : AlgState := by
  classical
  exact if s.exploreNow then
    let t : ℕ := s.k + 1
    let ρ' := s.rho + choiceRev r c
    { s with rho := ρ', lo := ρ' / t - baselineRadius T t,
             up := ρ' / t + baselineRadius T t, explored := true }
  else
    if baselineInnerLen T (s.y - s.x) ≤ s.k + 1 then
      (if s.up < s.y then epochStart (s.tau + 1) s.a s.y
       else epochStart (s.tau + 1) s.x s.b)
    else { s with k := s.k + 1, explored := false }

/-- Baseline state after exactly t customer observations; the horizon may
truncate either half of the last inner iteration or the last epoch. -/
noncomputable def baselineStateAt {N : ℕ} (r : Fin N → ℝ) (T t : ℕ)
    (p : Fin t → Option (Fin N)) : AlgState :=
  (List.ofFn p).foldl (baselineStep r T) initState

/-- Algorithm 1 on its meaningful horizon domain T ≥ 2.
This total Lean function's values at T ≤ 1 are only a totalization;
Theorem 2 makes no claim there. It sees known r and T, never unknown v. -/
noncomputable def baselinePolicy {N : ℕ} (r : Fin N → ℝ) (T : ℕ) : Policy N :=
  fun t p => offerOf r (baselineStateAt r T t p)

end MNLTrisection.Adaptive.Supplement


