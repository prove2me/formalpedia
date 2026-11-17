-- Prove2me | Definitions.Def_MultiThinkCoT_Supplement_parityChain
-- name    : MultiThinkCoT_Supplement_parityChain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:57:39.465078+00:00
-- url     : https://prove2.me/theorems/f6136fe3-c169-4bf1-9a0b-7ac17cbf2957
-- title:
--   Parity CoTs with propagating noise, and the adversarial observation model of Theorem 8
-- statement:
--   Fix $(d,k)$, a support $S\subseteq[d]$ with $|S|=k$, and an ordering $\pi\in\mathrm{Bij}([k],S)$. The generator $f_{S,\pi}$ produces from $x\in\{0,1\}^d$ the chain of thought
--
--   $$
--   z_0:=0,\qquad z_t:=z_{t-1}\oplus x_{\pi(t)},\quad t=1,\dots,k,
--   $$
--
--   so $z_k=\bigoplus_{j\in S}x_j$. Under **propagating noise** of level $\eta$, with $\xi_1,\dots,\xi_k\sim\mathrm{Bernoulli}(\eta)$ i.i.d., the chain is $\tilde z_0:=0$, $\tilde z_t:=(\tilde z_{t-1}\oplus x_{\pi(t)})\oplus\xi_t$.
--
--   In the **learning problem** of Theorem 8 the inputs are $(x^{(1)},\dots,x^{(m)})\sim\mathrm{Unif}(\{0,1\}^d)$ i.i.d.; an adversary chooses for each example an ordering $\pi^{(i)}\in\mathrm{Bij}([k],S_\star)$ as a function of the whole input sequence; the noise vectors are independent across examples and of the inputs; and the learner receives $\big((x^{(1)},\tilde z^{(1)}),\dots,(x^{(m)},\tilde z^{(m)})\big)$ with $\tilde z^{(i)}=(\tilde z^{(i)}_1,\dots,\tilde z^{(i)}_k)$.
--
--   **Formalization Note** Inputs are functions `Fin d → Bool` and CoTs `Fin k → Bool`; the paper's step $t\in\{1,\dots,k\}$ is the index $t-1$, and $z_0$ is not part of the observed CoT. These generators act on $\{0,1\}^d$ directly, not through the next-token maps of the base mission. $\mathrm{Bij}([k],S)$ is the type of bijections `Fin k ≃ S`. The Bernoulli law clamps $\eta$ to $[0,1]$, which changes nothing for $\eta\in[0,1/2)$. The adversary is a deterministic map from input sequences to orderings.
-- source:
--   Joshi, Magen, Srebro, Tsilivis, Vardi, Learning to Think from Multiple Thinkers: How Chain-of-Thought Heterogeneity Affects Efficient Learnability, arXiv:2604.24737 (held version, sha256 e663a640…), Appendix G, paragraphs "Generators", "Propagating noise during generation", "Learning problem", pp.59–60 (PDF pp.59–60)

import Mathlib
import Definitions.Def_MultiThinkCoT_endToEndError

namespace MultiThinkCoT.Supplement

/-!
# Parity CoTs with propagating noise, and the observation model of Theorem 8

N. Joshi, R. Magen, N. Srebro, N. Tsilivis, G. Vardi, *Learning to Think from Multiple Thinkers:
How Chain-of-Thought Heterogeneity Affects Efficient Learnability*, arXiv:2604.24737 (held
version, sha256 e663a640…), Appendix G, paragraphs "Generators", "Propagating noise during
generation" and "Learning problem", pp.59–60 (PDF pp.59–60).

For `S ⊆ [d]` with `|S| = k` and an ordering `π ∈ Bij([k], S)`, the generator `f_{S,π}` produces
`z_0 := 0`, `z_t := z_{t−1} ⊕ x_{π(t)}`, `t = 1, …, k`. With noise `(ξ_1, …, ξ_k) ∼iid
Bernoulli(η)`, the noisy chain is `z̃_0 := 0`, `z̃_t := (z̃_{t−1} ⊕ x_{π(t)}) ⊕ ξ_t`. In the learning
problem, `(x(1), …, x(m)) ∼iid Unif({0,1}^d)`; the adversary chooses for each example an ordering
`π(i) ∈ Bij([k], S⋆)`, which "may depend adversarially on the entire input sequence"; the learner
receives `((x(1), z̃(1)), …, (x(m), z̃(m)))`.

**Formalization Note.**
* Inputs are `Fin d → Bool`, CoTs `Fin k → Bool`; the paper's step `t ∈ {1, …, k}` is index
  `t − 1 : Fin k` (so `π(t)` is `π ⟨t − 1, _⟩` and `z_t` is `noisyCoT … ⟨t − 1, _⟩`). The token
  `z_0 = 0` is not part of the observed CoT. These generators are modelled directly on
  `{0,1}^d → {0,1}^k`, not through the next-token maps `MultiThinkCoT.Gen`.
* `Bij([k], S)` is the type `Fin k ≃ S` of bijections onto the subtype of `S`.
* `bern η` is the Bernoulli law with `Pr[true] = η` (`true` = the bit is flipped), with `η`
  clamped to `[0, 1]`; Theorem 8 only uses `η ∈ [0, 1/2)`, where no clamping happens.
* The adversary is a deterministic map from the input sequence to the orderings; the noise
  vectors `ξ(i)` are i.i.d. across `i` and independent of the inputs, as in the paper.
-/

/-- The noisy chain `z̃_t`, `t = 0, 1, …` (`z̃_t = z̃_k` for `t > k`). -/
def noisyChain {d k : ℕ} (x : Fin d → Bool) (π : Fin k → Fin d) (ξ : Fin k → Bool) : ℕ → Bool
  | 0 => false
  | n + 1 =>
    if h : n < k then xor (xor (noisyChain x π ξ n) (x (π ⟨n, h⟩))) (ξ ⟨n, h⟩)
    else noisyChain x π ξ n

/-- The observed noisy CoT `(z̃_1, …, z̃_k)`. -/
def noisyCoT {d k : ℕ} (x : Fin d → Bool) (π : Fin k → Fin d) (ξ : Fin k → Bool) :
    Fin k → Bool :=
  fun t => noisyChain x π ξ (t.1 + 1)

/-- The noiseless CoT `(z_1, …, z_k)` of `f_{S,π}`, `z_t = z_{t−1} ⊕ x_{π(t)}`. -/
def parityCoT {d k : ℕ} (x : Fin d → Bool) (π : Fin k → Fin d) : Fin k → Bool :=
  noisyCoT x π fun _ => false

/-- `Bernoulli(η)` on `Bool` (`Pr[true] = η`, with `η` clamped to `[0, 1]`). -/
noncomputable def bern (η : ℝ) : PMF Bool :=
  PMF.ofFintype
    (fun b => if b then ((min 1 η.toNNReal : NNReal) : ENNReal)
      else ((1 - min 1 η.toNNReal : NNReal) : ENNReal))
    (by
      rw [Fintype.sum_bool]
      simp only [if_true, Bool.false_eq_true, if_false]
      rw [← ENNReal.coe_add, add_tsub_cancel_of_le (min_le_left _ _), ENNReal.coe_one])

/-- The law of the dataset `((x(i), z̃(i)))_{i ≤ m}` of Theorem 8: inputs i.i.d. uniform on
`{0,1}^d`, orderings `π(i) = adv (x(1..m)) i ∈ Bij([k], S)`, noise vectors i.i.d.
`Bernoulli(η)^k`, independent across `i` and of the inputs. -/
noncomputable def noisySampleLaw (d k m : ℕ) (S : Finset (Fin d)) (η : ℝ)
    (adv : (Fin m → Fin d → Bool) → Fin m → (Fin k ≃ S)) :
    PMF (Fin m → (Fin d → Bool) × (Fin k → Bool)) :=
  (iidSample (PMF.uniformOfFintype (Fin d → Bool)) m).bind fun xs =>
    (iidSample (iidSample (bern η) k) m).map fun ξ i =>
      (xs i, noisyCoT (xs i) (fun t => ((adv xs i t : S) : Fin d)) (ξ i))

end MultiThinkCoT.Supplement


