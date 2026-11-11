-- Prove2me | Definitions.Def_GapAgnosticGS_armGap
-- name    : GapAgnosticGS_armGap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:32:46.22022+00:00
-- url     : https://prove2.me/theorems/4af23dc5-e960-4886-a79f-d5a48433cf9f
-- title:
--   Reward gap $\Delta_{\rm arm}$ between the best and second-best arm
-- statement:
--   For a hidden-basis environment with $n\ge2$ arms, the **arm gap** is
--
--   $$\Delta_{\rm arm}:=p_\star-\max_{j\ne j_\star}p_j ,$$
--
--   i.e. $p_\star$ minus the second largest reward with multiplicity. $\Delta_{\rm arm}>0$ holds exactly when the best arm $j_\star$ is unique; with ties $\Delta_{\rm arm}=0$, as the paper says for the non-unique case.
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), §1, p.5 (PDF p.6): "If j⋆ is unique, let ∆_arm := p⋆ − max_{j≠j⋆} p_j"; §3.4, p.13 (PDF p.14)

import Definitions.Def_GapAgnosticGS_pStar
import Definitions.Def_GapAgnosticGS_secondReward

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), §1, p.5 (PDF p.6): "If j⋆ is unique, let ∆_arm := p⋆ − max_{j≠j⋆} p_j"; §3.4, p.13
(PDF p.14): "the non-unique case, where ∆arm = 0". The reward gap between the best and the
second best arm (with multiplicity).

**Formalization Note.** `armGap Env > 0` holds exactly when the best arm is unique; then it is
the paper's `∆_arm`, and with ties it is `0`, as on p.13. -/
noncomputable def armGap {n : ℕ} {A : Type} [Fintype A] [DecidableEq A] {a₀ : A}
    {Prj : Matrix A A ℂ} (Env : HidEnv n A a₀ Prj) : ℝ :=
  pStar Env - secondReward Env

end GapAgnosticGS


