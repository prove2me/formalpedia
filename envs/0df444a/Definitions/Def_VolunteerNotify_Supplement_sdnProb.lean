-- Prove2me | Definitions.Def_VolunteerNotify_Supplement_sdnProb
-- name    : VolunteerNotify_Supplement_sdnProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:25:17.066102+00:00
-- url     : https://prove2.me/theorems/6ea4227e-fbe9-556f-808d-18ab31399bbb
-- title:
--   Algorithm 2 — the scaled-down notification (SDN) policy: $\beta_{v,t}$ and the notification probabilities
-- statement:
--   Let $q$ be the MDHR of $g$ and $G$ its CDF. For an input $x\in\mathbb R^{V\times S\times T}$ (in Algorithm 2 the ex ante solution $x^*$ of (5)), the offline phase of the **scaled-down notification (SDN) policy** sets $\beta_{v,1}=1$ and, for $t\ge2$,
--   $$
--   \beta_{v,t}=1-\sum_{t'=1}^{t-1}\sum_{s=1}^S\lambda_{s,t'}\,\frac{x_{v,s,t'}}{2-q}\,\big(1-G(t-t')\big).
--   $$
--   In the online phase, when a task of type $s$ arrives at $t$, it notifies each volunteer $v$ independently with probability
--   $$
--   w_{v,s,t}=\frac{x_{v,s,t}}{(2-q)\,\beta_{v,t}} .
--   $$
--   Lemma 7 shows that $\beta_{v,t}$ is the probability that $v$ is active at $t$ and that $\beta_{v,t}\ge\frac1{2-q}$, so $w\in[0,1]$ whenever $x\in\mathcal P$.
--
--   **Formalization Note** $q$ is the published `mdhr`, an infimum. The online phase is the published `Process` with $w$ as notification probabilities. At the first period the sum is empty, which gives $\beta_{v,1}=1$.
-- source:
--   Manshadi, Rodilitz, Online Policies for Efficient Volunteer Crowdsourcing, arXiv:2002.08474v7, Algorithm 2, p.46

import Mathlib
import Definitions.Def_VolunteerNotify_mdhr
import Definitions.Def_VolunteerNotify_Instance

namespace VolunteerNotify.Supplement

variable {V S T : ℕ}

/-- `β_{v,t}` of the offline phase of the scaled-down notification (SDN) policy, Algorithm 2,
Manshadi–Rodilitz, arXiv:2002.08474v7, p.46: `β_{v,1} = 1` and, for `t ≥ 2`,
`β_{v,t} = 1 − ∑_{t'=1}^{t−1} ∑_{s=1}^S λ_{s,t'} x_{v,s,t'}/(2 − q) · (1 − G(t − t'))`, with
`G = cdf g` and `q = mdhr g`.

**Formalization Note.** Periods are `Fin`-indexed (paper index = value + 1). At the first period
the sum is empty, which gives `β_{v,1} = 1`. `t' < t` in the sum, so the natural subtraction is
exact. The input `x` is arbitrary; Algorithm 2 uses `x*` of (5), and Lemmas 7–8 any `x ∈ P`. -/
noncomputable def sdnBeta (I : Instance V S T) (x : Decision V S T) (v : Fin V) (t : Fin T) : ℝ :=
  1 - ∑ t' ∈ Finset.Iio t, ∑ s,
    I.lam s t' * (x v s t' / (2 - mdhr I.g)) * (1 - cdf I.g ((t : ℕ) - (t' : ℕ)))

/-- The notification probabilities of the online phase of the SDN policy, Algorithm 2,
arXiv:2002.08474v7, p.46: if a task of type `s` arrives at `t`, notify `v` with probability
`x_{v,s,t} / ((2 − q) β_{v,t})`. The online phase is the published `Process I (sdnProb I x) μ`,
which notifies independently with these probabilities.

**Formalization Note.** For `x ∈ P`, Lemma 7 gives `β_{v,t} ≥ 1/(2 − q) > 0`, so the probability is
well defined and lies in `[0, 1]`; Lean's `x / 0 = 0` is never used there. -/
noncomputable def sdnProb (I : Instance V S T) (x : Decision V S T) : Decision V S T :=
  fun v s t => x v s t / ((2 - mdhr I.g) * sdnBeta I x v t)

end VolunteerNotify.Supplement


