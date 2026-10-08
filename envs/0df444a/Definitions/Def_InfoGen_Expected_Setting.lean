-- Prove2me | Definitions.Def_InfoGen_Expected_Setting
-- name    : InfoGen_Expected_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:25:46.670314+00:00
-- url     : https://prove2.me/theorems/2448e9fb-1023-4ad4-ac81-b346694b90b6
-- title:
--   §1, p. 2, and App. A, p. 11 — mutual information I(X;Y) = D(P_{X,Y}‖P_X ⊗ P_Y) and the expected generalization error gen(μ, P_{W|S})
-- statement:
--   This module fixes the two objects of Xu and Raginsky's analysis that are not already provided by the published learning setting `LearnStability.Characterization.Setting` (which supplies the sample law $\mu^{\otimes n}$, the population risk $L_\mu(w)=\int_{\mathsf Z}\ell(w,z)\,\mu(dz)$ and the empirical risk $L_s(w)=\frac1n\sum_{i=1}^n\ell(w,z_i)$).
--
--   The paper's setting (§1, p. 2): "there is an instance space Z, a hypothesis space W, and a nonnegative loss function ℓ : W × Z → ℝ₊. A learning algorithm characterized by a Markov kernel $P_{W|S}$ takes as input a dataset of size n, i.e., an n-tuple $S = (Z_1,\dots,Z_n)$ of i.i.d. random elements of Z with some unknown distribution µ, and picks a random element W of W as the output hypothesis according to $P_{W|S}$."
--
--   1. **Mutual information.** For a probability law $P_{X,Y}$ of a pair $(X,Y)$ on $\mathsf X\times\mathsf Y$, with marginals $P_X$ and $P_Y$,
--   $$
--   I(X;Y)=D\big(P_{X,Y}\,\big\|\,P_X\otimes P_Y\big)\in[0,\infty],
--   $$
--   the Kullback–Leibler divergence of the joint law from the product of its marginals (App. A, p. 11: "The result follows by noting that $I(X; Y) = D(P_{X,Y}\|P_X \otimes P_Y)$"). In particular $I(S;W)$ is this quantity for the joint law $P_{S,W}=\mu^{\otimes n}\otimes P_{W|S}$.
--
--   2. **Expected generalization error** (eq. (4), p. 2). For a loss $\ell$, a data distribution $\mu$ and a learning algorithm $P_{W|S}$,
--   $$
--   \mathrm{gen}(\mu,P_{W|S})=\mathbb E\big[L_\mu(W)-L_S(W)\big],
--   $$
--   "where the expectation is taken with respect to the joint distribution $P_{S,W} = \mu^{\otimes n}\otimes P_{W|S}$".
--
--   These are the two quantities related by Theorem 1 of the paper: the generalization error is controlled by the mutual information between the input dataset and the output hypothesis.
--
--   **Formalization Note** The mutual information is Mathlib's `klDiv P (P.fst.prod P.snd)` with values in $[0,\infty]$; it is not truncated to a real number, so statements that use $I$ inside a square root carry the hypothesis $I\ne\infty$. The definition accepts any measure $P$ but has the paper's meaning when $P$ is a probability law. The algorithm $P_{W|S}$ is a kernel from samples `Fin n → Z` to `W`, and the joint law is the composition-product `sampleLaw μ n ⊗ₘ κ`; the consuming theorems require $\mu$ to be a probability measure, $\kappa$ to be a Markov kernel, and $n>0$. The generalization error integrates the pointwise difference $L_\mu(w)-L_s(w)$ under the joint law (rather than subtracting two separate expectations, each of which may be infinite for an unbounded loss). Lean's real integral is $0$ when its integrand is not integrable, and `empRisk` divides by zero when $n=0$; the paper's interpretation applies under the theorems' measurability, moment, and positive-sample-size hypotheses. Nonnegativity of the loss is likewise imposed by those theorems, rather than by this definition.
-- source:
--   Xu & Raginsky, arXiv:1705.07809v2, §1 eqs. (1)–(4), p. 2; App. A, p. 11 (I(X;Y) = D(P_{X,Y}‖P_X ⊗ P_Y))

import Mathlib
import Definitions.Def_LearnStability_Characterization_Setting

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

namespace InfoGen.Expected

open LearnStability.Characterization

/-- The mutual information `I(X; Y) = D(P_{X,Y} ‖ P_X ⊗ P_Y)` of a joint law `P` on `α × β`, the
Kullback–Leibler divergence of `P` from the product of its marginals (Xu & Raginsky,
arXiv:1705.07809v2, App. A, p. 11, last line). It takes values in `[0, ∞]`. -/
noncomputable def mutualInfo {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure (α × β)) : ℝ≥0∞ :=
  klDiv P (P.fst.prod P.snd)

/-- The expected generalization error `gen(μ, P_{W|S}) = E[L_μ(W) − L_S(W)]` of a learning
algorithm `κ = P_{W|S}`, the expectation being taken under the joint law
`P_{S,W} = μ^{⊗n} ⊗ P_{W|S}` (eq. (4), p. 2). The pointwise difference is integrated. -/
noncomputable def genError {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    (ℓ : W → Z → ℝ) (μ : Measure Z) {n : ℕ} (κ : Kernel (Fin n → Z) W) : ℝ :=
  ∫ p, (risk ℓ μ p.2 - empRisk ℓ p.1 p.2) ∂(sampleLaw μ n ⊗ₘ κ)

end InfoGen.Expected


