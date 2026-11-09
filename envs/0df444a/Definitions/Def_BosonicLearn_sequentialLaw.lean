-- Prove2me | Definitions.Def_BosonicLearn_sequentialLaw
-- name    : BosonicLearn_sequentialLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:15:06.889278+00:00
-- url     : https://prove2.me/theorems/8664cfef-732e-4934-81a5-fe3a6d0af756
-- title:
--   Joint law of an adaptive sequence of outcomes
-- statement:
--   Let $\kappa_0,\dots,\kappa_{N-1}$ be Markov kernels, where $\kappa_t$ gives the law of the outcome $x_t\in\mathcal O$ of round $t$ as a function of the earlier outcomes $(x_0,\dots,x_{t-1})$. The joint law of $(x_0,\dots,x_{t-1})$ is defined recursively: the empty transcript has probability one, and
--
--   $$\mathbb P_{t+1}(dx_0\cdots dx_t)=\mathbb P_t(dx_0\cdots dx_{t-1})\,\kappa_t(x_0,\dots,x_{t-1};dx_t).$$
--
--   This is the probability space of an adaptive single-copy protocol, in which the $t$-th measurement may depend on the first $t-1$ outcomes.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §5.1, p. 30

import Mathlib

open MeasureTheory ProbabilityTheory

namespace BosonicLearn

/-- **Law of the first `t` outcomes of an adaptive sequence of measurements.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §5.1, p. 30: "A non-entangled adaptive learning protocol on N copies can be specified by a family of
sequences of POVMs … Here, the t-th POVM can depend on the first t − 1 measurement outcomes x_{<t}."

Given, for each round `t < N`, a Markov kernel `κ t` from the earlier outcomes `(x₀,…,x_{t−1})` to the
outcome of round `t`, `sequentialLaw κ t _` is the joint law of `(x₀,…,x_{t−1})`: the Dirac mass on the empty
transcript for `t = 0`, and for `t + 1` the law of the first `t` outcomes composed with `κ t` and appended
(`Fin.snoc`).

**Formalization Note.** `Measure.compProd` is used; it is the intended joint law when the kernels are
s-finite (they are Markov in every use, `AdaptiveScheme.round_markov`). -/
noncomputable def sequentialLaw {O : Type} [MeasurableSpace O] {N : ℕ}
    (κ : (t : Fin N) → Kernel (Fin t → O) O) : (t : ℕ) → t ≤ N → Measure (Fin t → O)
  | 0, _ => Measure.dirac (fun i => Fin.elim0 i)
  | t + 1, h => ((sequentialLaw κ t (Nat.le_of_succ_le h)) ⊗ₘ (κ ⟨t, h⟩)).map
      (fun p => Fin.snoc (α := fun _ => O) p.1 p.2)

end BosonicLearn


