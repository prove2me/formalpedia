-- Prove2me | Definitions.Def_PartPredAlloc_expect
-- name    : PartPredAlloc_expect
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:16:21.989985+00:00
-- url     : https://prove2.me/theorems/89cdb0a3-738d-4a68-b10b-3d9b7a9bc0cc
-- title:
--   The partially predictable arrival model: outcomes $(\mathcal S,\sigma_{\mathcal S})$, $\vec V=\vec v_I\circ\sigma^{-1}$, expectation and probability
-- statement:
--   An adversary fixes an initial sequence $\vec v_I=(v_{I,1},\dots,v_{I,n})$. Each customer joins the **stochastic group** $\mathcal S\subseteq\{1,\dots,n\}$ independently with probability $p$; the others form the adversarial group. Given $\mathcal S$, a permutation $\sigma$ of $\{1,\dots,n\}$ fixing every position outside $\mathcal S$ is chosen uniformly at random (the set $\mathrm{fix}(\mathcal S)$ of such permutations has $|\mathcal S|!$ elements). Customer $j$ arrives in slot $\sigma(j)$, so the arrival sequence is
--
--   $$
--   V_t=v_{I,\sigma^{-1}(t)},\qquad t=1,\dots,n.
--   $$
--
--   The expectation of a function $f$ of the outcome $(\mathcal S,\sigma)$ is
--
--   $$
--   \mathbb E[f]=\sum_{\mathcal S}p^{|\mathcal S|}(1-p)^{n-|\mathcal S|}\,\frac{1}{|\mathrm{fix}(\mathcal S)|}\sum_{\sigma\in\mathrm{fix}(\mathcal S)}f(\mathcal S,\sigma),
--   $$
--
--   the probability of an event is the expectation of its indicator, and the conditional probability given $\mathcal S$ is the uniform average over $\sigma\in\mathrm{fix}(\mathcal S)$.
--
--   This is the probability space of every probabilistic statement of the mission (Definition 1: the expectation is over $\mathcal S$ and $\sigma_{\mathcal S}$).
--
--   **Formalization Note** Everything is a finite sum. In the example of Figure 1, $\sigma_{\mathcal S}(2)=6$ means customer 2 arrives at position 6.
-- source:
--   Hwang, Jaillet, Manshadi, Online Resource Allocation under Partially Predictable Demand, arXiv:1810.00447v1, §3, pp.9–10, Figure 1 and Definition 1

import Mathlib
import Definitions.Def_PartPredAlloc_Cust

namespace PartPredAlloc

/-- The permutations of the positions `{1, …, n}` (here `Fin n`) that fix every position outside the
stochastic group `S` (arXiv:1810.00447v1, §3, p.10: "customers in the stochastic group are permuted
uniformly at random among themselves"). There are `|S|!` of them. -/
def fixers {n : ℕ} (S : Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun σ => ∀ j, j ∉ S → σ j = j)

/-- The arrival sequence of the partially predictable model (arXiv:1810.00447v1, §3, p.10, Figure 1):
customer `j` of the adversarial sequence `v_I` arrives in slot `σ(j)`, so the realized sequence is
`v_t = v_I(σ⁻¹(t))`.

**Formalization Note.** Positions `1, …, n` are `i : Fin n` with position `i + 1`. In Figure 1,
`σ_S(2) = 6` means that customer 2 arrives at position 6. -/
def arrival {n : ℕ} (vI : Fin n → Cust) (σ : Equiv.Perm (Fin n)) : Fin n → Cust :=
  fun t => vI (σ.symm t)

/-- Expectation over the randomness of the partially predictable model (arXiv:1810.00447v1, §3,
p.10, Definition 1): each position joins the stochastic group `S` independently with probability
`p`, and given `S` the permutation `σ` is uniform over `fixers S`. For a function `f` of the
outcome `(S, σ)`,
`expect n p f = ∑_S p^{|S|} (1 − p)^{n − |S|} · (1/|fixers S|) ∑_{σ ∈ fixers S} f S σ`.

**Formalization Note.** The expectation is an explicit finite sum, with no measure theory.
`fixers S` always contains the identity, so the inner division is by a positive number. -/
noncomputable def expect (n : ℕ) (p : ℝ) (f : Finset (Fin n) → Equiv.Perm (Fin n) → ℝ) : ℝ :=
  ∑ S : Finset (Fin n), p ^ S.card * (1 - p) ^ (n - S.card) *
    ((∑ σ ∈ fixers S, f S σ) / ((fixers S).card : ℝ))

open Classical in
/-- The probability of an event `E` on outcomes `(S, σ)` of the partially predictable model
(arXiv:1810.00447v1, §3, p.10): the expectation of its indicator. -/
noncomputable def prob (n : ℕ) (p : ℝ) (E : Finset (Fin n) → Equiv.Perm (Fin n) → Prop) : ℝ :=
  expect n p (fun S σ => if E S σ then 1 else 0)

open Classical in
/-- The conditional probability of an event `E` on permutations given the stochastic group `S`:
`σ` uniform over `fixers S` (arXiv:1810.00447v1, §3, p.10). -/
noncomputable def probGivenS {n : ℕ} (S : Finset (Fin n)) (E : Equiv.Perm (Fin n) → Prop) : ℝ :=
  (∑ σ ∈ fixers S, if E σ then (1 : ℝ) else 0) / ((fixers S).card : ℝ)

end PartPredAlloc


