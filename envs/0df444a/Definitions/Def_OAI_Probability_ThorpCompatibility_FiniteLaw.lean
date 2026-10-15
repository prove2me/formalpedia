-- Prove2me | Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
-- name    : OAI_Probability_ThorpCompatibility_FiniteLaw
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:12:35.257048+00:00
-- url     : https://prove2.me/theorems/aa57fd8a-9b91-4832-9b88-f39bf4d64894
-- title:
--   Finite probability laws: mean, relative entropy, uniform deficit, push-forward and tilt
-- statement:
--   This module sets up an elementary calculus of probability distributions on finite sets. Throughout, $\Omega$ and $\Omega'$ are finite sets.
--
--   1. *Law.* A law on $\Omega$ is a function $P:\Omega\to\mathbb{R}$ with $P(a)\ge 0$ for every $a\in\Omega$ and $\sum_{a\in\Omega}P(a)=1$, i.e. a probability mass function.
--   2. *Mean.* For $f:\Omega\to\mathbb{R}$, $\mathbb{E}_P[f]=\sum_{a\in\Omega}P(a)\,f(a)$.
--   3. *Relative entropy.* For two laws $P,Q$ on $\Omega$,
--   $$
--   D(P\,\|\,Q)=\sum_{a\in\Omega}P(a)\log\frac{P(a)}{Q(a)} .
--   $$
--   4. *Uniform deficit.* $\Delta(P)=\log|\Omega|+\sum_{a\in\Omega}P(a)\log P(a)$. This is the gap between the maximal entropy $\log|\Omega|$ and the Shannon entropy of $P$, and it equals the relative entropy of $P$ with respect to the uniform law.
--   5. *Uniform law.* If $\Omega\ne\varnothing$, the uniform law is $U_\Omega(a)=1/|\Omega|$ for all $a\in\Omega$.
--   6. *Push-forward.* For a map $f:\Omega\to\Omega'$, the law $f_*P$ on $\Omega'$ is
--   $$
--   (f_*P)(b)=\sum_{a\in\Omega:\ f(a)=b}P(a),
--   $$
--   the distribution of the random variable $f$ under $P$.
--   7. *Tilt.* For a weight $\alpha:\Omega\to\mathbb{R}$ with $\alpha(x)\ge 0$ for all $x$ and $Z=\sum_{x}\alpha(x)>0$, the tilted law is $x\mapsto\alpha(x)/Z$.
--
--   These are the basic objects of the entropy method used for the weighted compatibility bound. Tilting the uniform law by a nonnegative weight produces the Gibbs law whose relative entropies are compared, and push-forwards express the marginals of a law on a product set.
--
--   **Formalization Note** The structure is `Law` with fields `mass`, `nonneg` and `total`. The operations are `Law.mean`, `Law.relativeEntropy`, `Law.uniformDeficit`, `Law.uniform` (which requires a `Nonempty` instance), `Law.map` and `Law.tilt`, and the tilt takes the nonnegativity and positivity proofs as arguments. Lean's conventions $\log 0=0$ and $x/0=0$ apply. Terms with $P(a)=0$ vanish, as in the usual convention $0\log 0=0$. A term with $P(a)>0=Q(a)$ also contributes $0$ rather than $+\infty$, however, so `relativeEntropy` agrees with the Kullback–Leibler divergence only when $Q(a)=0$ implies $P(a)=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/FiniteLaw.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/FiniteLaw.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpWeightedCompatibility mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpWeightedCompatibility

namespace OAI

open scoped Classical

namespace ThorpCompatibility
open Finset

structure Law (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

namespace Law
variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def mean (P : Law α) (f : α → ℝ) : ℝ := ∑ a, P.mass a * f a

noncomputable def relativeEntropy (P Q : Law α) : ℝ :=
  ∑ a, P.mass a * Real.log (P.mass a / Q.mass a)

noncomputable def uniformDeficit (P : Law α) : ℝ :=
  Real.log (Fintype.card α) + ∑ a, P.mass a * Real.log (P.mass a)

noncomputable def uniform [Nonempty α] : Law α where
  mass _ := 1 / (Fintype.card α : ℝ)
  nonneg _ := by positivity
  total := by simp [Fintype.card_ne_zero]

noncomputable def map (P : Law α) (f : α → β) : Law β := by
  classical
  exact {
    mass := fun b => ∑ a, if f a = b then P.mass a else 0
    nonneg := fun b => Finset.sum_nonneg fun a _ => by
      split_ifs <;> simp_all [P.nonneg]
    total := by
      rw [Finset.sum_comm]
      simpa using P.total
  }

noncomputable def tilt (a : α → ℝ) (ha : ∀ x, 0 ≤ a x)
    (hZ : 0 < ∑ x, a x) : Law α where
  mass x := a x / ∑ x, a x
  nonneg x := div_nonneg (ha x) hZ.le
  total := by rw [← Finset.sum_div, div_self hZ.ne']

end Law
end ThorpCompatibility

end OAI


