-- Prove2me | Definitions.Def_PCLAssort_Alg1Output
-- name    : PCLAssort_Alg1Output
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:20:48.163261+00:00
-- url     : https://prove2.me/theorems/4c3cdc53-5684-4661-955a-bc0ec566d3a2
-- title:
--   Outputs of Algorithm 1 (max-dicut with a knapsack constraint)
-- statement:
--   Let $(x,y)$ be the optimal basic solution of the LP (9) returned in step 1. A vertex set $T$ is a possible output of Algorithm 1 if it arises as follows, with $F(x)=\sum_{(i,j)\in E}w_{ij}x_i(1-x_j)$:
--
--   1. take a value $\delta\in(0,\tfrac12)$ with $x_i\in\{0,\delta,\tfrac12,1-\delta,1\}$ for all $i$ (Theorem 5);
--   2. if $\sum_i s_ix_i=c$, let $\hat x$ be whichever of $x$ and $x'$ (equation (10)) has the larger value of $F$;
--   3. if $\sum_i s_ix_i<c$, let $\hat x=x$;
--   4. apply pipage rounding to $\hat x$ to obtain $x^*$ with at most one fractional variable; let $I_1=\{j: x^*_j=1\}$ and $I_2$ the set containing the fractional coordinate, if any;
--   5. if all $s_i=1$ (cardinality constraint), output the better of $I_1$ and $I_1\cup I_2$;
--   6. otherwise (knapsack constraint), output the better of $I_1$ and $I_2$.
--
--   "Better" compares cut values.
--
--   **Formalization Note** The algorithm is a relation between its input $x$ and its output $T$. Every choice the text leaves open (the value $\delta$, ties in the argmax and in "better of", the pair chosen at each pipage step) is existentially quantified, so a statement "every output satisfies P" covers every run. When $x^*$ is integral, $I_2=\emptyset$.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), Algorithm 1, p.795 (PDF p.11)

import Mathlib
import Definitions.Def_PCLAssort_cutValue
import Definitions.Def_PCLAssort_dicutF
import Definitions.Def_PCLAssort_alg1Shift
import Definitions.Def_PCLAssort_PipageRun
import Definitions.Def_PCLAssort_fracCoords

namespace PCLAssort

/-- `T` is a possible output of Algorithm 1 (Max-Dicut with a Knapsack Constraint) (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, p.795)
when step 1 returns the optimal basic solution of LP (9) whose `x`-part is `x`:

1. (input) `x`;
2. if `∑_i s_i x_i = c`: with `δ` the value given by Theorem 5 and `x′` as in (10),
   `x̂ ← argmax{F(x), F(x′)}`;
3. if `∑_i s_i x_i < c`: `x̂ ← x`;
4. apply pipage rounding to `x̂` and obtain `x*` with at most one fractional variable;
   `I₁ = {j ∈ V : x*_j = 1}`, `I₂ = {i}` for the fractional variable `x*_i`;
5. (cardinality) if all `s_i = 1`, output the better of `I₁` and `I₁ ∪ I₂`;
6. (knapsack) otherwise output the better of `I₁` and `I₂`.

Here `F(x) = ∑_{(i,j)∈E} w_ij x_i (1 − x_j)`, and "better" compares cut values.

**Formalization Note.** The algorithm is encoded as an output relation; every choice the text leaves
open is existentially quantified: `δ` (any value with the conclusion of Theorem 5), the argmax on a
tie, the pipage run, and the "better of" on a tie. `I₂` is the set of fractional coordinates of
`x*`, i.e. `{i}`, or `∅` if `x*` is integral. -/
def Alg1Output {V : Type} [Fintype V] [DecidableEq V] (E : Finset (V × V)) (w : V × V → ℝ)
    (s : V → ℝ) (c : ℝ) (x : V → ℝ) (T : Finset V) : Prop :=
  ∃ δ : ℝ, (0 < δ ∧ δ < 1 / 2 ∧
      ∀ i, x i = 0 ∨ x i = δ ∨ x i = 1 / 2 ∨ x i = 1 - δ ∨ x i = 1) ∧
    ∃ xhat : V → ℝ,
      (∑ i, s i * x i = c →
        (xhat = x ∨ xhat = alg1Shift s x δ) ∧
          dicutF E w x ≤ dicutF E w xhat ∧ dicutF E w (alg1Shift s x δ) ≤ dicutF E w xhat) ∧
      (∑ i, s i * x i < c → xhat = x) ∧
      ∃ xstar : V → ℝ, PipageRun s (dicutF E w) xhat xstar ∧
        ((∀ i, s i = 1) →
          (T = Finset.univ.filter (fun j => xstar j = 1) ∨
              T = Finset.univ.filter (fun j => xstar j = 1) ∪ fracCoords xstar) ∧
            cutValue E w (Finset.univ.filter (fun j => xstar j = 1)) ≤ cutValue E w T ∧
            cutValue E w (Finset.univ.filter (fun j => xstar j = 1) ∪ fracCoords xstar) ≤
              cutValue E w T) ∧
        (¬ (∀ i, s i = 1) →
          (T = Finset.univ.filter (fun j => xstar j = 1) ∨ T = fracCoords xstar) ∧
            cutValue E w (Finset.univ.filter (fun j => xstar j = 1)) ≤ cutValue E w T ∧
            cutValue E w (fracCoords xstar) ≤ cutValue E w T)

end PCLAssort


