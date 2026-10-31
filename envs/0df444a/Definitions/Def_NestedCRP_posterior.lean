-- Prove2me | Definitions.Def_NestedCRP_posterior
-- name    : NestedCRP_posterior
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:29:46.731033+00:00
-- url     : https://prove2.me/theorems/4fae4d9e-4459-4929-a8a1-0723e44bdf8b
-- title:
--   hLDA joint probability and posterior
-- statement:
--   The joint probability of a state $x=(T,z)$ and the corpus $w$ under hLDA, with $\theta$ and $\beta$ integrated out, is
--
--   $$
--   \mathrm{joint}(T,z)=\mathrm{ncrp}(T)\cdot\prod_d\mathrm{stick}(z_d)\cdot\mathrm{topic}(T,z).
--   $$
--
--   The posterior, the target $p(c_{1:D},z_{1:D}\mid\gamma,\eta,m,\pi,w_{1:D})$ of the sampler, is
--
--   $$
--   \Pi(x)=\frac{\mathrm{joint}(x)}{\sum_y\mathrm{joint}(y)}.
--   $$
--
--   **Formalization Note** The joint is built from the integrals, never from the collapsed formulas, so the conditionals of §5 are theorems rather than assumptions. The denominator is the marginal probability of the corpus; it is positive and finite.
-- source:
--   Blei–Griffiths–Jordan, The nested Chinese restaurant process and Bayesian nonparametric inference of topic hierarchies, J. ACM 57(2), Article 7 (2010), https://doi.org/10.1145/1667053.1667056, §4, p.7:11; §5, p.7:14

import Mathlib
import Definitions.Def_NestedCRP_Hyper
import Definitions.Def_NestedCRP_ncrpMass
import Definitions.Def_NestedCRP_stickMass
import Definitions.Def_NestedCRP_topicMass

namespace NestedCRP

variable {V D : ℕ}

/-- The joint probability `p(c, z, w | γ, η, m, π)` of the hLDA generative process, with `θ` and `β`
integrated out: nCRP mass × level masses × word mass. Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), §4, p.7:11. -/
noncomputable def joint (H : Hyper) (C : Corpus V D) (x : C.State) : ℝ :=
  ncrpMass H.gamma x.1 * (∏ d, stickMass H.m H.pi (x.2 d)) * topicMass H.eta C x.1 x.2

/-- The posterior `p(c_{1:D}, z_{1:D} | γ, η, m, π, w_{1:D})`, the target of the sampler:
`joint x / ∑_y joint y`. Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), §5, p.7:14.

**Formalization Note** The denominator is the marginal probability of the corpus. -/
noncomputable def posterior (H : Hyper) (C : Corpus V D) (x : C.State) : ℝ :=
  joint H C x / ∑' y, joint H C y

end NestedCRP


