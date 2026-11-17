-- Prove2me | Definitions.Def_MultiThinkCoT_Supplement_recoveryProb
-- name    : MultiThinkCoT_Supplement_recoveryProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:58:20.435103+00:00
-- url     : https://prove2.me/theorems/21c45e22-0a1c-485f-b9f4-5ca3d815d372
-- title:
--   The uniform-ordering parity model of Theorem 9 and the success probability $\Pr[\widehat S=S_\star]$
-- statement:
--   In the noiseless uniform-ordering model, the hidden support $S_\star$ is drawn uniformly from the $k$-subsets $\binom{[d]}{k}$. Given $S_\star$, $m$ samples $(x^{(i)},z^{(i)})$ are drawn i.i.d.: $x^{(i)}\sim\mathrm{Unif}(\{0,1\}^d)$, an ordering $\pi^{(i)}\sim\mathrm{Unif}(\mathrm{Bij}([k],S_\star))$ independent of $x^{(i)}$, and $z^{(i)}=(z_1,\dots,z_k)$ the partial parities $z_t=z_{t-1}\oplus x^{(i)}_{\pi^{(i)}(t)}$, $z_0=0$.
--
--   A (possibly randomized) estimator maps a dataset to a probability distribution over subsets of $[d]$. Its **success probability** is
--
--   $$
--   \Pr\big[\widehat S=S_\star\big],
--   $$
--
--   taken jointly over $S_\star$, the samples and the estimator's internal randomness.
--
--   **Formalization Note** The prior is uniform on the $k$-subsets of `Fin d` (a point mass at $\emptyset$ when $k>d$, a case Theorem 9 excludes). Orderings are uniform on the bijections `Fin k ≃ S`; for a set of size other than $k$ there is no bijection and the sample uses the all-zero CoT, a branch outside the support of the prior.
-- source:
--   Joshi, Magen, Srebro, Tsilivis, Vardi, Learning to Think from Multiple Thinkers: How Chain-of-Thought Heterogeneity Affects Efficient Learnability, arXiv:2604.24737 (held version, sha256 e663a640…), Appendix G.2, Theorem 9, p.63 (PDF p.63); generators and input law, Appendix G, pp.59–60

import Mathlib
import Definitions.Def_MultiThinkCoT_endToEndError
import Definitions.Def_MultiThinkCoT_Supplement_parityChain

namespace MultiThinkCoT.Supplement

/-!
# The uniform-ordering model of Theorem 9 and the success probability of an estimator

N. Joshi, R. Magen, N. Srebro, N. Tsilivis, G. Vardi, *Learning to Think from Multiple Thinkers:
How Chain-of-Thought Heterogeneity Affects Efficient Learnability*, arXiv:2604.24737 (held
version, sha256 e663a640…), Appendix G.2, Theorem 9, p.63 (PDF p.63), with the generators and
the input law of Appendix G, pp.59–60.

Noiseless case `η = 0`. `S⋆` is drawn uniformly from `([d] choose k)`. Given `S⋆`, `m` i.i.d.
samples `(x(i), z(i))`: `x(i) ∼ Unif({0,1}^d)`, `π(i) ∼ Unif(Bij([k], S⋆))` independent of `x(i)`,
and `z(i) = f_{S⋆,π(i)}^{CoT}(x(i)) ∈ {0,1}^k`. A (possibly randomized) estimator `Ŝ` maps the
dataset to a distribution over subsets of `[d]`; `Pr[Ŝ = S⋆]` is over `S⋆`, the samples and the
estimator's randomness.

**Formalization Note.**
* `Bij([k], S)` is `Fin k ≃ S`, uniform via `PMF.uniformOfFintype`. When `|S| ≠ k` there is no
  bijection; `uniformOrderSample` then returns `(x, 0)` (the all-`false` CoT). That branch is never reached on the
  support of the prior, which only charges `k`-subsets.
* `supportPrior d k` is the uniform law on the `k`-subsets of `Fin d` (and the point mass at `∅`
  when `k > d`, where there is no `k`-subset; Theorem 9 assumes `k ≤ d − 1`).
* `recoveryProb d k m E` is the real number `Pr[Ŝ = S⋆]` for the randomized estimator
  `E : dataset → PMF (Finset (Fin d))`.
-/

/-- One sample `(x, z)`: `x ∼ Unif({0,1}^d)`, `π ∼ Unif(Bij([k], S))`, `z = f_{S,π}^{CoT}(x)`. -/
noncomputable def uniformOrderSample {d : ℕ} (k : ℕ) (S : Finset (Fin d)) :
    PMF ((Fin d → Bool) × (Fin k → Bool)) :=
  (PMF.uniformOfFintype (Fin d → Bool)).bind fun x =>
    if h : S.card = k then
      (@PMF.uniformOfFintype (Fin k ≃ S) _
          ⟨(Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, h])).symm⟩).map
        fun π => (x, parityCoT x fun t => (π t : Fin d))
    else PMF.pure (x, fun _ => false)

/-- The uniform prior on the `k`-subsets of `[d]`. -/
noncomputable def supportPrior (d k : ℕ) : PMF (Finset (Fin d)) :=
  if h : k ≤ d then
    PMF.uniformOfFinset ((Finset.univ : Finset (Fin d)).powersetCard k)
      (Finset.powersetCard_nonempty.mpr (by simpa using h))
  else PMF.pure ∅

/-- `Pr[Ŝ = S⋆]` for `S⋆ ∼ supportPrior d k`, `m` i.i.d. samples from `uniformOrderSample k S⋆`,
and the randomized estimator `E`. -/
noncomputable def recoveryProb (d k m : ℕ)
    (E : (Fin m → (Fin d → Bool) × (Fin k → Bool)) → PMF (Finset (Fin d))) : ℝ :=
  (((supportPrior d k).bind fun S =>
      (iidSample (uniformOrderSample k S) m).bind fun data =>
        (E data).map fun Shat => (S, Shat)).toOuterMeasure {p | p.2 = p.1}).toReal

end MultiThinkCoT.Supplement


