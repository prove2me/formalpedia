-- Prove2me | Definitions.Def_MarkovSA_IsMarkovWrt
-- name    : MarkovSA_IsMarkovWrt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:11.970473+00:00
-- url     : https://prove2.me/theorems/bcf98a32-5302-4c83-865b-a36961431c80
-- title:
--   $Y$ is a Markov chain with transition matrix $P$ relative to a filtration $\mathcal G$
-- statement:
--   Let $(\Omega,\mathbb P)$ be a probability space with a filtration $(\mathcal G_k)_{k\ge0}$, and $P$ a transition matrix on the finite set $\mathcal Y$. A sequence $(Y_k)$ is a **Markov chain with transition matrix $P$ relative to $(\mathcal G_k)$** if every $Y_k$ is $\mathcal G_k$-measurable and, for all $k$ and $y\in\mathcal Y$,
--
--   $$
--   \mathbb P\big(Y_{k+1}=y\,\big|\,\mathcal G_k\big)=P(Y_k,y)\quad\text{almost surely.}
--   $$
--
--   This is how the mission reads the paper's "Let $\{Y_k\}$ be Markov chain" (reading R1): the proof of Lemma A.3 (3) (p.34) conditions the chain on the past of the iterates, so the iterates must be adapted to a filtration with respect to which the chain is Markov. When $w\equiv0$, the natural filtration of $Y$ qualifies.
--
--   **Formalization Note** The conditional probability is the conditional expectation of the indicator of $\{Y_{k+1}=y\}$; the law of $Y_0$ is arbitrary.
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, §2.1, p.5 (reading R1)

import Mathlib
open MeasureTheory

namespace MarkovSA

/-- `Y` is a **Markov chain with transition matrix `P` relative to the filtration `G`**: each `Y k` is
`G k`-measurable and `ℙ(Y_{k+1} = y | G_k) = P(Y_k, y)` almost surely, for all `k` and `y`.

This is the reading R1 of "Let `{Y_k}` be Markov chain with stationary distribution `μ`"
(Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, §2.1, p.5): the proof (p.34) conditions the chain on the past of the iterates, so the
iterates must not anticipate the chain. With `w ≡ 0` the natural filtration of `Y` satisfies it.

**Formalization Note.** The conditional probability is the conditional expectation of the real
indicator of `{Y_{k+1} = y}`; the law of `Y 0` is arbitrary. -/
def IsMarkovWrt {𝒴 : Type*} [Fintype 𝒴] [DecidableEq 𝒴] [MeasurableSpace 𝒴] [MeasurableSingletonClass 𝒴] {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Pr : Measure Ω) (P : Matrix 𝒴 𝒴 ℝ) (G : Filtration ℕ mΩ) (Y : ℕ → Ω → 𝒴) : Prop :=
  (∀ k, Measurable[G k] (Y k)) ∧
    ∀ (k : ℕ) (y : 𝒴),
      Pr[{ω | Y (k + 1) ω = y}.indicator (fun _ => (1 : ℝ)) | G k] =ᵐ[Pr] fun ω => P (Y k ω) y

end MarkovSA


