-- Prove2me | Definitions.Def_WildeQIT_ZhangAudenaert_probNe
-- name    : WildeQIT_ZhangAudenaert_probNe
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:05.76399+00:00
-- url     : https://prove2.me/theorems/044f4224-3b1b-407d-a8d5-183beedf98a6
-- title:
--   Probability that two random variables differ, $\Pr\{\hat X\neq\hat Y\}$
-- statement:
--   Let $(\hat X,\hat Y)$ be a pair of random variables taking values in the same finite alphabet $\mathcal A$, with joint distribution $c(x,y)=\Pr\{\hat X=x,\hat Y=y\}$. The probability that they differ is
--
--   $$
--   \Pr\{\hat X\neq\hat Y\}=\sum_{(x,y)\in\mathcal A\times\mathcal A,\;x\neq y} c(x,y).
--   $$
--
--   It is the probability of error $p_e\equiv\Pr\{\hat X\neq X\}$ in Fano's inequality and the quantity $\Pr\{\hat X\neq\hat Y\}$ of a coupling in Lemma 10.7.2; together with $\Pr\{\hat X=\hat Y\}=\sum_x c(x,x)$ it sums to one.
--
--   **Formalization Note** A pair of random variables is represented by its joint distribution, a `WildeQIT.FinDist (α × α)`, as in the published definition of $\Pr\{\hat X=\hat Y\}$ (`WildeQIT.FinDist.probEq`).
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §10.7.3, p. 304 (p_e ≡ Pr{X̂ ≠ X}); Lemma 10.7.2, eq. (10.104), p. 308

import Definitions.Def_WildeQIT_FinDist

namespace WildeQIT.ZhangAudenaert

/-- **The probability that two random variables differ, `Pr{X̂ ≠ Ŷ}`.**
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §10.7.3, p. 304
(`p_e ≡ Pr{X̂ ≠ X}`, the probability of error in Fano's inequality) and Lemma 10.7.2, (10.104),
p. 308 (`Pr{X̂ ≠ Ŷ}` for a coupling).

For a joint distribution `c` of a pair `(X, Y)` of random variables taking values in the same
finite alphabet `α`, `probNe c = ∑_{(x, y) : x ≠ y} c(x, y)`.

**Formalization Note.** A pair of random variables is represented by its joint distribution
(`WildeQIT.FinDist (α × α)`), as in the published `WildeQIT.FinDist.probEq`, which is
`Pr{X̂ = Ŷ}`; the two sum to one. -/
noncomputable def probNe {α : Type} [Fintype α] [DecidableEq α] (c : FinDist (α × α)) : ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t : α × α => t.1 ≠ t.2), c.prob t

end WildeQIT.ZhangAudenaert


