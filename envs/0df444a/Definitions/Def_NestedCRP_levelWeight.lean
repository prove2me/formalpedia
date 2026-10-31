-- Prove2me | Definitions.Def_NestedCRP_levelWeight
-- name    : NestedCRP_levelWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:28:47.352494+00:00
-- url     : https://prove2.me/theorems/483b6c17-8b3f-4ec5-9860-d1f2223388ca
-- title:
--   Level weight of Eq. (2) with the word predictive of Eq. (3)
-- statement:
--   Fix a state and a site $s_0=(d,n)$. For a level $k$ and a word $v$, let $C_k(v)$ count the sites $s\ne s_0$ with level $k$, whose document shares the node of $d$ at level $k$, and whose word is $v$. The word predictive is
--
--   $$
--   \mathrm{lik}(k)=\frac{C_k(w_{d,n})+\eta}{\sum_v C_k(v)+V\eta},
--   $$
--
--   and the weight of level $k$ in Eq. (2) is the level prior of §5.1 times $\mathrm{lik}(k)$.
--
--   **Formalization Note** Eq. (3) is $\propto$ in the word only. Its dropped denominator depends on the level, so the numerator alone is not the level likelihood Eq. (2) needs: with one document, words $(a,b)$, $b$ at the first level, $V=2$ and $\eta=\tfrac12$, the numerators are $\tfrac12$ at both levels while the likelihoods are $\tfrac14$ and $\tfrac12$. The normalized form is the one Eq. (6) prints. The weight uses the state only away from $s_0$.
-- source:
--   Blei–Griffiths–Jordan, The nested Chinese restaurant process and Bayesian nonparametric inference of topic hierarchies, J. ACM 57(2), Article 7 (2010), https://doi.org/10.1145/1667053.1667056, Eq. (2) and Eq. (3), p.7:16; Eq. (6), p.7:21

import Mathlib
import Definitions.Def_NestedCRP_Hyper
import Definitions.Def_NestedCRP_stickMass
import Definitions.Def_NestedCRP_Corpus

namespace NestedCRP

variable {V D : ℕ}

open Classical in
/-- `C_k(v)`: the words other than site `s₀` with level `k`, in the node of `s₀`'s document at level
`k`, and equal to `v`. Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), Eq. (3), p.7:16. -/
noncomputable def siteCount (C : Corpus V D) (x : C.State) (s₀ : C.Site) (k : ℕ) (v : Fin V) : ℕ :=
  (Finset.univ.filter fun s : C.Site =>
    s ≠ s₀ ∧ x.2 s.1 s.2 = k ∧ x.1.Rel k s.1 s₀.1 ∧ C.word s = v).card

/-- The word predictive at level `k`:
`(C_k(w_{d,n}) + η) / (∑_v C_k(v) + Vη)`. Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), Eq. (3), p.7:16, and Eq. (6), p.7:21.

**Formalization Note** Eq. (3) is `∝` in the word only. The denominator depends on the level, so the
numerator alone is not the level likelihood Eq. (2) needs: with one document, words `(a, b)`, `b` at
the first level, `V = 2` and `η = ½`, the numerators are ½ at both levels and the likelihoods ¼
and ½. The normalized form is the one Eq. (6) prints. -/
noncomputable def levelLik (η : ℝ) (C : Corpus V D) (x : C.State) (s₀ : C.Site) (k : ℕ) : ℝ :=
  ((siteCount C x s₀ k (C.word s₀) : ℝ) + η) / ((∑ v, (siteCount C x s₀ k v : ℝ)) + V * η)

/-- The Eq. (2) weight of level `k` for site `s₀`: the level prior times the word predictive.
Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), Eq. (2), p.7:16.

**Formalization Note** It uses `x` only away from `s₀`, so it is the weight of the conditional given
the other variables. -/
noncomputable def levelWeight (H : Hyper) (C : Corpus V D) (x : C.State) (s₀ : C.Site) (k : ℕ) : ℝ :=
  levelPrior H.m H.pi (x.2 s₀.1) s₀.2 k * levelLik H.eta C x s₀ k

end NestedCRP


