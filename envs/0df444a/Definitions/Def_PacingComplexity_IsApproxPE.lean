-- Prove2me | Definitions.Def_PacingComplexity_IsApproxPE
-- name    : PacingComplexity_IsApproxPE
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:27:14.898483+00:00
-- url     : https://prove2.me/theorems/9dfa529c-6a5c-4be3-a9f3-66b09641ed30
-- title:
--   $(\delta,\gamma)$-approximate pacing equilibrium (Definition 2)
-- statement:
--   Let $G=(n,m,(v_{ij}),(B_i))$ be an SPP game and $\delta,\gamma\in[0,1)$. A pair $(\alpha,x)$ with $\alpha\in[0,1]^n$, $x\in[0,1]^{n\times m}$ and $\sum_{i}x_{ij}\le1$ for every good $j$ is a **$(\delta,\gamma)$-approximate pacing equilibrium** if
--
--   1. (a) only buyers close to the highest bid win: $x_{ij}>0$ implies $\alpha_iv_{ij}\ge(1-\delta)h_j(\alpha)$;
--   2. (b) every good with a positive bid is fully allocated: $h_j(\alpha)>0$ implies $\sum_i x_{ij}=1$;
--   3. (c) budgets are respected: $\sum_j x_{ij}\,p_j(\alpha)\le B_i$;
--   4. (d) no buyer paces much without need: $\sum_j x_{ij}\,p_j(\alpha)<(1-\gamma)B_i$ implies $\alpha_i\ge 1-\gamma$.
--
--   With $\delta=\gamma=0$ this is an exact pacing equilibrium. Every winner pays the second-highest bid $p_j(\alpha)$ of the whole good, also a winner whose own bid is below the top.
--
--   **Formalization Note** The range $\delta,\gamma\in[0,1)$ is not a clause of the predicate; it is guaranteed wherever the predicate is used (the search problem takes $\delta=\gamma=n^{-c}$ with $n\ge2$ buyers, the gadget lemmas $\delta=\gamma=1/n^7$ with $n\ge2$).
-- source:
--   Chen, Kroer, Kumar, The Complexity of Pacing for Second-Price Auctions, arXiv:2103.13969v2, Definition 2, p.7

import Mathlib
import Definitions.Def_PacingComplexity_highBid
import Definitions.Def_PacingComplexity_secondBid

namespace PacingComplexity

/-- **(δ, γ)-approximate pacing equilibrium**, Definition 2 of Chen, Kroer, Kumar, *The Complexity
of Pacing for Second-Price Auctions*, arXiv:2103.13969v2, p.7: "(α, x), with α = (αi) ∈ [0, 1]^n,
x = (xij) ∈ [0, 1]^{nm} and Σ_{i∈[n]} xij ≤ 1 for all j ∈ [m], is a (δ, γ)-approximate pacing
equilibrium of G if
(a) xij > 0 implies αi vij ≥ (1 − δ)hj(α).
(b) hj(α) > 0 implies Σ_{i∈[n]} xij = 1.
(c) Σ_{j∈[m]} xij pj(α) ≤ Bi.
(d) Σ_{j∈[m]} xij pj(α) < (1 − γ)Bi implies αi ≥ 1 − γ."

`IsApproxPE v B δ γ α x` is the conjunction of the three membership constraints and the four
clauses (a)–(d), with `h_j = highBid v α j` and `p_j = secondBid v α j`.

**Formalization Note** Every buyer who wins part of good `j` pays the second-highest bid `p_j(α)`
of the whole good, also when her own bid is below the top bid. The paper fixes `δ, γ ∈ [0, 1)`
before the definition; that range is not a clause of the predicate but a side condition wherever
the predicate is used (`ApproxPacing` takes `δ = γ = n^(−c)` with `n ≥ 2` buyers; the gadget
theorems take `δ = γ = 1/n^7` with `n ≥ 2`). -/
def IsApproxPE {N G : Type} [Fintype N] [Fintype G] (v : N → G → ℝ) (B : N → ℝ) (δ γ : ℝ)
    (α : N → ℝ) (x : N → G → ℝ) : Prop :=
  (∀ i, 0 ≤ α i ∧ α i ≤ 1) ∧
  (∀ i j, 0 ≤ x i j ∧ x i j ≤ 1) ∧
  (∀ j, ∑ i, x i j ≤ 1) ∧
  (∀ i j, 0 < x i j → (1 - δ) * highBid v α j ≤ α i * v i j) ∧
  (∀ j, 0 < highBid v α j → ∑ i, x i j = 1) ∧
  (∀ i, ∑ j, x i j * secondBid v α j ≤ B i) ∧
  (∀ i, ∑ j, x i j * secondBid v α j < (1 - γ) * B i → 1 - γ ≤ α i)

end PacingComplexity


