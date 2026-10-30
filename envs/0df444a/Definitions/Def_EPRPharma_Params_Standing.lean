-- Prove2me | Definitions.Def_EPRPharma_Params_Standing
-- name    : EPRPharma_Params_Standing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:03:55.659246+00:00
-- url     : https://prove2.me/theorems/dd829692-ae8f-4751-b79d-545b699b1bab
-- title:
--   Standing assumptions $\alpha,\beta,o_d,k>0$ and $u_p,\epsilon_e,\epsilon_s\ge 0$
-- statement:
--   The standing assumptions on a parameter vector are
--
--   $$\alpha>0,\quad \beta>0,\quad o_d>0,\quad u_p\ge 0,\quad k>0,\quad \epsilon_e\ge 0,\quad \epsilon_s\ge 0 .$$
--
--   The paper prints no sign conditions; these are the conventions of the model. $\alpha,\beta$ are constants of quadratic costs and the proofs divide by $\alpha$, $\beta$ and $k$; $o_d$ is a disutility, $u_p$ a benefit and $\epsilon_e,\epsilon_s$ disutilities. The proof of Lemma 1 uses $u_p\ge 0$. The condition $\epsilon_e\ge 0$ cannot be dropped: for $\alpha=\beta=o_d=1$ over-prescription is never profitable, so eliminating it is welfare maximizing for every $\epsilon_e$, and Proposition 3's "if and only if $\epsilon_e\ge\bar\epsilon_e$" would have no real threshold if $\epsilon_e$ ranged over all of $\mathbb R$.
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), §3, pp. 9–13; proofs, Online Appendix pp. 1–3 (unnumbered)

import Mathlib
import Definitions.Def_EPRPharma_Params

namespace EPRPharma

/-- **Standing assumptions on the parameters.**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), §3, pp. 9–13 (unnumbered; no sign
conditions are printed): α > 0, β > 0, o_d > 0, u_p ≥ 0, k > 0, ε_e ≥ 0, ε_s ≥ 0.

**Formalization Note.** α and β are the constants of the quadratic promotional costs αη_d², βη_p²,
and the proofs (Online Appendix pp. 1–3) divide by α, β and k (1/(4α), o_d/(2β), r^i_EC = (3 − 6α +
3u_p)/k); o_d is a disutility ("bad reputation"), u_p a benefit, ε_e and ε_s disutilities. u_p ≥ 0
is used in the proof of Lemma 1 (Online Appendix p. 1: "η_d ≥ p + o_d(1 − η_p)(≥ p − u_p)"). ε_e ≥ 0
is needed: with α = β = o_d = 1 no equilibrium over-prescribes, so eliminating over-prescription is
welfare maximizing for every ε_e and Proposition 3's "if and only if ε_e ≥ ε̄_e" has no real threshold
if ε_e may be any real. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.alpha ∧ 0 < P.beta ∧ 0 < P.od ∧ 0 ≤ P.up ∧ 0 < P.k ∧ 0 ≤ P.epsE ∧ 0 ≤ P.epsS

end EPRPharma


