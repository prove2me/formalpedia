-- Prove2me | Definitions.Def_NashStackelberg_Alg1Output
-- name    : NashStackelberg_Alg1Output
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:18:23.665476+00:00
-- url     : https://prove2.me/theorems/6147c331-d97b-494b-822c-a7060cd50930
-- title:
--   The possible outputs of Algorithm 1 (Enumeration Algorithm for NASPs)
-- statement:
--   Algorithm 1 takes a NASP $N$ and either returns a lottery $(\hat x^i,p^i)$ for every player or returns `no`. A value is a possible output on $N$ when:
--
--   1. **`no`** (Step 9) exactly when the convexified game $\widetilde N$ (strategy sets $\mathrm{cl\,conv}(\mathcal F^i)$, costs of $N$) has no pure Nash equilibrium (Step 4);
--   2. **lotteries $L$** (Step 8) when there is a PNE $\tilde x$ of $\widetilde N$ (Step 4) such that for every player $i$:
--      - if $\tilde x^i\in\mathcal F^i$ (Step 6), the lottery $L^i$ puts probability $1$ on a point equal to $\tilde x^i$ and probability $0$ on every other point;
--      - otherwise (Step 7), every point $\hat x^i_j$ of $L^i$ lies in $\mathcal F^i$, $p^i_j\ge0$, $\sum_j p^i_j=1$, and $\tilde x^i=\sum_j p^i_j\hat x^i_j$.
--
--   Algorithm 1 makes choices (which PNE of $\widetilde N$ is found, which decomposition is used in Step 7); the definition describes every possible run, so a statement about all outputs is a statement about every run.
--
--   **Formalization Note** The algorithm is modelled by this input–output relation rather than as a program; its Steps 2–3 (computing $\mathrm{cl\,conv}(\mathcal F^i)$ by Theorem 3) are absorbed into the use of $\widetilde{\mathcal F}^i$.
-- source:
--   Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, When Nash Meets Stackelberg, arXiv:1910.06452v6, Algorithm 1, p.12, and the paragraph "The Enumeration Algorithm", pp.11–12

import Mathlib
import Definitions.Def_NashStackelberg_IsPNE
import Definitions.Def_NashStackelberg_NASP_Ftilde
import Definitions.Def_NashStackelberg_NASP_cost
import Definitions.Def_NashStackelberg_Lottery

open Matrix

namespace NashStackelberg

/-- **The possible outputs of Algorithm 1 (Enumeration Algorithm for NASPs)** (Carvalho,
Dragotto, Feijoo, Lodi & Sankaranarayanan, *When Nash Meets Stackelberg*, arXiv:1910.06452v6,
Algorithm 1, p.12).

`Alg1Output N out` says that `out` is a value Algorithm 1 can return on the NASP `N`:

* `none` (Step 9, "return no") exactly when the convexified game `Ñ` (strategy sets
  `cl conv 𝓕ⁱ`, same costs) has no PNE (Step 4);
* `some L` (Step 8) when there is a PNE `x̃` of `Ñ` (Step 4) such that, for every player `i`,
  - if `x̃ⁱ ∈ 𝓕ⁱ` (Step 6), the lottery `L i` puts probability `1` on a point equal to `x̃ⁱ` and `0`
    on every other point;
  - otherwise (Step 7), every point `x̂ⁱⱼ` of `L i` lies in `𝓕ⁱ`, `pⁱⱼ ≥ 0`, `Σⱼ pⁱⱼ = 1`, and
    `x̃ⁱ = Σⱼ pⁱⱼ x̂ⁱⱼ`.

**Formalization Note.** The algorithm's nondeterministic choices (which PNE of `Ñ` Step 4 finds,
which decomposition Step 7 uses) are modelled by a relation: every `out` with `Alg1Output N out`
is a possible run. -/
def Alg1Output {n : ℕ} (N : NASP n) : Option ((i : Fin n) → Lottery (N.Var i)) → Prop
  | none => ¬ ∃ x, IsPNE N.Ftilde N.cost x
  | some L => ∃ x, IsPNE N.Ftilde N.cost x ∧ ∀ i,
      (x i ∈ N.F i →
        ∃ j, (L i).pts j = x i ∧ (L i).prob j = 1 ∧ ∀ j', j' ≠ j → (L i).prob j' = 0) ∧
      (x i ∉ N.F i →
        (∀ j, (L i).pts j ∈ N.F i) ∧ (∀ j, 0 ≤ (L i).prob j) ∧ ∑ j, (L i).prob j = 1 ∧
          ∑ j, (L i).prob j • (L i).pts j = x i)

end NashStackelberg


