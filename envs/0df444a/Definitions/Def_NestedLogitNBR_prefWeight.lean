-- Prove2me | Definitions.Def_NestedLogitNBR_prefWeight
-- name    : NestedLogitNBR_prefWeight
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:34:44.239088+00:00
-- url     : https://prove2.me/theorems/419034c7-60f7-4f94-8daa-52f90f2e42db
-- title:
--   Total preference weight $V_i(S)$ of an assortment (with $v_{i0}=0$)
-- statement:
--   In the nested logit model with $m$ nests and $n$ products per nest, let $v_{ij}\ge0$ be the preference weight of product $j$ in nest $i$. The total preference weight of an assortment $S\subseteq N=\{1,\dots,n\}$ offered in nest $i$ is
--
--   $$
--   V_i(S)=\sum_{j\in S}v_{ij}.
--   $$
--
--   The paper defines $V_i(S)=v_{i0}+\sum_{j\in S}v_{ij}$ (p. 7); Section 4, where the result of this mission lives, assumes $v_{i0}=0$ for every nest (p. 16), which is built in here. $V_i$ enters the nest choice probabilities $V_i(S_i)^{\gamma_i}/(v_0+\sum_l V_l(S_l)^{\gamma_l})$ and every constraint of the linear programs (3), (4) and (7).
--
--   **Formalization Note** Products are indexed by `Fin n` from $0$: Lean product $j$ is the paper's product $j+1$.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014, doi:10.1287/opre.2014.1256), §1, p. 7 (definition of V_i(S_i)); §4, p. 16 (v_i0 = 0)

import Mathlib

namespace NestedLogitNBR

/-- **Total preference weight `V_i(S)` of an assortment in a nest (with `v_i0 = 0`).**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014,
doi:10.1287/opre.2014.1256), §1, p. 7: "We use `V_i(S_i)` to denote the total preference weight of all available
options when we offer the assortment `S_i ⊂ N` in nest `i`. In other words, we have
`V_i(S_i) = v_i0 + Σ_{j∈S_i} v_ij`." Section 4 (p. 16) assumes "`v_i0 = 0` for all `i ∈ M`",
so in this mission `V_i(S) = Σ_{j∈S} v_ij`.

There are `m` nests (`Fin m`) with `n` products each (`Fin n`); `v i j` is the preference
weight `v_ij` of product `j` in nest `i`.

**Formalization Note.** Lean product `j : Fin n` is the paper's product `j.val + 1`. The
no-purchase weight `v_i0` is `0`, the standing assumption of Section 4 (p. 16). -/
def prefWeight {m n : ℕ} (v : Fin m → Fin n → ℝ) (i : Fin m) (S : Finset (Fin n)) : ℝ :=
  ∑ j ∈ S, v i j

end NestedLogitNBR


