-- Prove2me | Definitions.Def_OnlineMatchFrameworks_Charge
-- name    : OnlineMatchFrameworks_Charge
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:31:49.270237+00:00
-- url     : https://prove2.me/theorems/478d9a34-c73b-4003-afcd-f440d5cf7908
-- title:
--   The imaginary charges $\mathbb E[\sum_v c_v(\mathrm{ALG})]$
-- statement:
--   The charging argument for Lemma 2 assigns, when customer $v$ is matched to item $u$, the weight $\tfrac12 w_u$ to $v$ and $\tfrac12 x_{u,v'}p_{u,v'}w_u$ to every customer $v'$. So $c_v(\mathrm{ALG})=\tfrac12 w_v+\tfrac12\sum_{u\in U_m}x_{u,v}p_{u,v}w_u$, where $U_m$ is the set of items matched by the end. The expectation of the total charge is the recursion
--   $$
--   \mathrm{charge}(x,[\,],A)=\tfrac12\sum_{u\notin A}\sum_{v\in V}x_{u,v}p_{u,v}w_u,
--   $$
--   $$
--   \mathrm{charge}(x,v::vs,A)=\sum_l\mathrm{BB}(A,v)(l)\Bigl[\sum_i\mathrm{mp}_v(l,i)\bigl(\tfrac12 w_{l_i}+\mathrm{charge}(x,vs,A\setminus\{l_i\})\bigr)+\Bigl(1-\sum_i\mathrm{mp}_v(l,i)\Bigr)\mathrm{charge}(x,vs,A)\Bigr].
--   $$
--   It connects the algorithm's reward to the LP objective.
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, Appendix A, proof of Lemma 2, pp.39–40

import Definitions.Def_OnlineMatchFrameworks_BlackBox

open scoped BigOperators

namespace OnlineMatchFrameworks

variable {U V : Type*} [DecidableEq U] [Fintype U] [Fintype V]

namespace Instance

/-- **The imaginary charges `E[∑_v c_v(ALG)]`.** arXiv:1907.03963v6, proof of Lemma 2, pp.39–40:
"when a vertex v is matched to some u ∈ U, we assign 0.5 w_u to v and for all v′ ∈ V (including v
itself) we assign 0.5 x_{u,v′} p_{u,v′} w_u to v′", and
`c_v(ALG) = 0.5 w_v + 0.5 ∑_{u ∈ U_m} x_{u,v} p_{u,v} w_u`, with `U_m` the items matched by the end.
`chargeFrom x BB vs A` is the expected total charge when the customers `vs` are still to come and
`A` is available, by the same recursion as `algFrom`. -/
noncomputable def chargeFrom (G : Instance U V) (x : U → V → ℝ)
    (BB : Finset U → V → PMF (Policy U)) : List V → Finset U → ℝ
  | [], A => (1 / 2) * ∑ u ∈ Aᶜ, ∑ v, x u v * G.p u v * G.w u
  | v :: vs, A =>
      ∑ l : Policy U, (BB A v l).toReal *
        (∑ i : Fin l.1.length, G.matchProb v l.1 i *
            ((1 / 2) * G.w (l.1.get i) + G.chargeFrom x BB vs (A.erase (l.1.get i))) +
          (1 - ∑ i : Fin l.1.length, G.matchProb v l.1 i) * G.chargeFrom x BB vs A)

end Instance

end OnlineMatchFrameworks


