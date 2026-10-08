-- Prove2me | Definitions.Def_McFadden1974_MLE_Axioms
-- name    : McFadden1974_MLE_Axioms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T04:03:35.065386+00:00
-- url     : https://prove2.me/theorems/dad88efa-25b1-47dc-9c48-8f5d990dd194
-- title:
--   Axioms 5 and 6 and Equation (21) — full rank, the inequalities condition, and b(γ)
-- statement:
--   In the conditional logit model (data $z_{in}$, $S_{in}$, probabilities $P_{in}(\theta)$ and means $\bar z_n(\theta)$ as in Equations (16)–(20)):
--
--   1. **Axiom 5 (Full Rank).** The $\big(\sum_{n=1}^N J_n\big) \times K$ matrix whose rows are $z_{in} - \bar z_n(\theta)$, for $i = 1,\dots,J_n$ and $n = 1,\dots,N$, has rank $K$.
--   2. **Axiom 6.** There exists no nonzero $\gamma \in \mathbb{R}^K$ such that
--   $$S_{in}(z_{jn} - z_{in})\gamma \le 0 \quad \text{for all } i, j = 1,\dots,J_n \text{ and } n = 1,\dots,N.$$
--   3. **Equation (21).** For $\gamma \in \mathbb{R}^K$,
--   $$b(\gamma) = \max_{n=1,\dots,N}\ \max_{i,j=1,\dots,J_n} S_{in}(z_{jn} - z_{in})\gamma.$$
--
--   Axiom 5 makes the Hessian of the log-likelihood negative definite; Axiom 6 is the condition that decides whether the maximum likelihood estimator exists (Lemma 3), and $b$ measures, along each unit direction, how fast the log-likelihood decreases.
--
--   **Formalization Note** The page does not say at which $\theta$ the weights in $\bar z_n$ are evaluated; Axiom 5 is encoded as rank $K$ at every $\theta$. The row space is the same for all $\theta$ (the weights are positive and sum to one), so this equals rank $K$ at any single $\theta$. The double maximum in (21) is a supremum over a nonempty finite index set because the data include at least one observed trial, so it is attained.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 116 (PDF p. 12), Axiom 5, Axiom 6, Equation (21)

import Mathlib
import Definitions.Def_McFadden1974_MLE_Model

/-!
# McFadden (1974), §II — Axioms 5 and 6 and the function `b` of (21)

Definition bundle on top of the conditional logit model `McFadden1974.MLE.Data`.

McFadden, *Conditional Logit Analysis of Qualitative Choice Behavior*, in P. Zarembka (ed.),
*Frontiers in Econometrics*, Academic Press (1974), p. 116 (PDF p. 12), Axiom 5, Axiom 6 and
Equation (21).
-/

namespace McFadden1974.MLE

open scoped RealInnerProductSpace

namespace Data

variable {K : ℕ} (d : Data K)

/-- The `(∑_{n=1}^N J_n) × K` matrix of **Axiom 5** (p. 116, PDF p. 12), evaluated at the
parameter `θ`: its rows, indexed by the pairs `(n, i)` with `i = 1, …, J_n`, are the centred
attribute vectors `z_in − z̄_n(θ)`, where `z̄_n(θ) = ∑_i z_in P_in(θ)`. -/
noncomputable def designMatrix (θ : EuclideanSpace ℝ (Fin K)) :
    Matrix (Σ n : Fin d.N, Fin (d.J n)) (Fin K) ℝ :=
  fun p k => (d.z p.1 p.2 - d.zbar p.1 θ) k

/-- **Axiom 5 (Full Rank)** (p. 116, PDF p. 12): "The `∑_{n=1}^N J_n × K` matrix whose rows are
`(z_in − z̄_n)` for `i = 1, …, J_n` and `n = 1, …, N` is of rank `K`."

**Formalization Note.** The page does not say at which `θ` the weights `P_in` defining `z̄_n` are
evaluated. The axiom is encoded as "rank `K` at every `θ`". The row space does not depend on `θ`
(the weights are positive and sum to one, so the rows span the same space as the differences
`z_in − z_jn`), hence this is equivalent to rank `K` at any single `θ`. -/
def Axiom5 : Prop :=
  ∀ θ : EuclideanSpace ℝ (Fin K), (d.designMatrix θ).rank = K

/-- **Axiom 6** (p. 116, PDF p. 12): "There exists no nonzero `K`-vector `γ` satisfying
`S_in (z_jn − z_in) γ ≤ 0` for `i, j = 1, …, J_n` and `n = 1, …, N`."

The quantifier ranges over all `n` and all pairs `i, j`, including `i = j` and unchosen `i`
(where `S_in = 0`), exactly as on the page. -/
def Axiom6 : Prop :=
  ∀ γ : EuclideanSpace ℝ (Fin K),
    (∀ (n : Fin d.N) (i j : Fin (d.J n)), (d.S n i : ℝ) * ⟪d.z n j - d.z n i, γ⟫ ≤ 0) → γ = 0

/-- **Equation (21)** (p. 116, PDF p. 12): `b(γ) = Max_{n=1,…,N} Max_{i,j=1,…,J_n}
S_in (z_jn − z_in) γ`.

**Formalization Note.** The double maximum is the supremum over the finite index type of triples
`(n, (i, j))`. This index type is nonempty because `Data.trials` gives at least one trial and
`Data.observed` gives at least one alternative in each trial, so the supremum is attained. -/
noncomputable def b (γ : EuclideanSpace ℝ (Fin K)) : ℝ :=
  ⨆ x : (Σ n : Fin d.N, Fin (d.J n) × Fin (d.J n)),
    (d.S x.1 x.2.1 : ℝ) * ⟪d.z x.1 x.2.2 - d.z x.1 x.2.1, γ⟫

end Data

end McFadden1974.MLE


