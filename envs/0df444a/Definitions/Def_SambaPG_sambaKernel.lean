-- Prove2me | Definitions.Def_SambaPG_sambaKernel
-- name    : SambaPG_sambaKernel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:37:49.86259+00:00
-- url     : https://prove2.me/theorems/f0f26659-025d-4000-ad17-ccce599137e5
-- title:
--   The SAMBA transition probabilities $\kappa_\alpha(p,S)$
-- statement:
--   From a state $p$, SAMBA chooses the leading arm $\ell$ with probability $\lambda\{v\in[0,1]:\mathrm{lead}(p,v)=\ell\}$, plays arm $a$ with probability $p_a$, and receives reward $1$ with probability $r_a$ and $0$ otherwise. Writing $\mathrm{step}(p,\ell,a,x)$ for the update (6), the probability that the next state lies in a set $S$ is
--
--   $$
--   \kappa_\alpha(p,S)=\sum_{\ell}\lambda\{\mathrm{lead}(p,\cdot)=\ell\}\sum_a p_a\Big(r_a\,\mathbf 1_S(\mathrm{step}(p,\ell,a,1))+(1-r_a)\,\mathbf 1_S(\mathrm{step}(p,\ell,a,0))\Big).
--   $$
--
--   This is the transition kernel of the SAMBA Markov chain in Theorem 1.
-- source:
--   Denisov & Walton, Regret Analysis of a Markov Policy Gradient Algorithm for Multi-arm Bandits, arXiv:2007.10229v3, §2.2, p.4; §3.4, p.7, eq. (6)

import Mathlib
import Definitions.Def_SambaPG_sambaStep
import Definitions.Def_SambaPG_BernoulliBandit

open MeasureTheory

namespace SambaPG

/-- **The transition probabilities of the SAMBA Markov chain.**
Denisov & Walton, arXiv:2007.10229v3, §2.2, p.4 ("the probabilities `(p_a(t) : a ∈ A)` are a
Markov chain"), §3.4, p.7, eq. (6).

From the state `p`, the leading arm is `ℓ` with probability `λ{v ∈ [0, 1] : lead p v = ℓ}`, the arm
`a` is played with probability `p_a`, and it pays `1` with probability `r_a` and `0` otherwise. So
the probability of moving into a set `S` of probability vectors is
`κ_α(p, S) = Σ_ℓ λ{lead p · = ℓ} Σ_a p_a (r_a 1_S(step(p, ℓ, a, 1)) + (1 − r_a) 1_S(step(p, ℓ, a, 0)))`,
where `step` is the update (6). -/
noncomputable def sambaKernel {A : Type*} [Fintype A] [DecidableEq A] (B : BernoulliBandit A)
    (α : ℝ) (lead : (A → ℝ) → ℝ → A) (p : A → ℝ) (S : Set (A → ℝ)) : ℝ :=
  ∑ ℓ, (volume {v ∈ Set.Icc (0 : ℝ) 1 | lead p v = ℓ}).toReal *
    ∑ a, p a * (B.r a * S.indicator 1 (sambaStep α p ℓ a 1) +
      (1 - B.r a) * S.indicator 1 (sambaStep α p ℓ a 0))

end SambaPG


