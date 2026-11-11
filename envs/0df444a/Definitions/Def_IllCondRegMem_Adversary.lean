-- Prove2me | Definitions.Def_IllCondRegMem_Adversary
-- name    : IllCondRegMem_Adversary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:56:37.023163+00:00
-- url     : https://prove2.me/theorems/ca90688d-a012-4d6e-ab4c-8aa9a9dbfb07
-- title:
--   Adaptive $\kappa$-conditioned adversaries for non-i.i.d. regression
-- statement:
--   In **non-i.i.d. linear regression** the target $x^\star$ is drawn once and, on each round $t$, an **adaptive adversary** selects a covariance matrix $\Sigma_t$ that may depend on the target, on the history of samples and on the learner's current memory state; the covariate is then drawn as $a_t\sim\mathcal N(0,\Sigma_t)$ and the learner receives $(a_t,a_t^\top x^\star)$. The adversary is **$\kappa$-conditioned** when every $\Sigma_t$ it selects is $\kappa$-conditioned.
--
--   Concretely, on round $t$ the adversary sees its own randomness, $x^\star$, the samples $(a_s,b_s)_{s<t}$ and $\mathrm{Memory}_{t-1}$, and outputs a matrix $A_t$; the covariate is $a_t=A_tg_t$ with $g_t\sim\mathcal N(0,I_d)$ fresh, so that $\Sigma_t=A_tA_t^\top$.
--
--   **Formalization Note** The adversary outputs a factor $A_t$ of $\Sigma_t$; since $\mathcal N(0,AA^\top)$ is the law of $Ag$, every covariance is available. Its randomness is one uniform seed in $[0,1]$. The history argument is the vector of all $T$ samples with the entries of rounds $\ge t$ set to $0$. Each entry of $A_t$ is required to be jointly measurable in (seed, target, history) for each round and memory value.
-- source:
--   M. Blanchard, D. Hansen, A. Jayant, V. Sharan, Polynomial Memory-Sample Separations in Non-i.i.d. Ill-Conditioned Regression, STOC 2027 submission (held version, sha256 6369d09f…), §2, p.6 (PDF p.7), Definition 3; Theorem 1, p.3 (PDF p.4)

import Mathlib
import Definitions.Def_IllCondRegMem_IsCondBounded
import Definitions.Def_IllCondRegMem_Learner

open MeasureTheory Matrix

namespace IllCondRegMem

/-- **Adaptive κ-conditioned adversary** for non-i.i.d. linear regression.
Blanchard, Hansen, Jayant, Sharan, *Polynomial Memory-Sample Separations in Non-i.i.d.
Ill-Conditioned Regression*, STOC 2027 submission (held version, sha256 6369d09f…), §2, p.6:
"the covariates a_t may be generated from changing covariance matrices Σ_t potentially dependent
on the history and the current memory state of the learner"; Definition 3, p.6 (dependence on
"the target, history, and the learner's current memory state"); Theorem 1, p.3 ("any adaptive
adversary selecting κ … -conditioned covariance matrices Σ_t on each round").

On round `t` the adversary sees its own random seed `ω`, the target `x⋆`, the samples of the
previous rounds and the learner's current memory state, and outputs a matrix `A_t`; the
covariate is then `a_t = A_t g_t` with `g_t ∼ N(0, I_d)` fresh, so `a_t ∼ N(0, Σ_t)` with
`Σ_t = A_t A_tᵀ`, and `Σ_t` must be κ-conditioned.

**Formalization Note.** The adversary outputs a factor `A_t` of `Σ_t`; since `N(0, A Aᵀ)` is the
law of `A g`, every choice of covariance is available. The history argument is the vector of all
`T` samples with the entries of rounds `≥ t` set to `0` (only the past is visible). The
adversary's randomness is one uniform seed in `[0,1]`. Joint measurability in
(seed, target, history), for each round and memory value, is required so that the interaction
defines a probability law. -/
structure Adversary (d M T : ℕ) (κ : ℝ) where
  /-- The factor `A_t` chosen on round `t` from (seed, target, past samples, current memory). -/
  choose : Fin T → unitInterval → Vec d → (Fin T → Vec d × ℝ) → Mem M → Matrix (Fin d) (Fin d) ℝ
  /-- Joint measurability of each entry in (seed, target, history). -/
  choose_measurable : ∀ t m i j, Measurable fun p : unitInterval × Vec d × (Fin T → Vec d × ℝ) =>
    choose t p.1 p.2.1 p.2.2 m i j
  /-- Every chosen covariance `A_t A_tᵀ` is κ-conditioned. -/
  cond_bounded : ∀ t ω x h m, IsCondBounded κ (choose t ω x h m * (choose t ω x h m)ᵀ)

end IllCondRegMem


