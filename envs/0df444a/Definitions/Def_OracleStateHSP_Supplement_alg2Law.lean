-- Prove2me | Definitions.Def_OracleStateHSP_Supplement_alg2Law
-- name    : OracleStateHSP_Supplement_alg2Law
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:10:50.168082+00:00
-- url     : https://prove2.me/theorems/1d979d15-84db-43a8-b0bf-a0908b4c6409
-- title:
--   Output law of Algorithm 2 (copy-based HSP-Sampler)
-- statement:
--   Algorithm 2 takes a generating set $S^\perp$ of $K^\perp \le H^\perp$ and $\tilde\delta \in (0, 1]$, and for $i = 0, 1, \dots, m - 1$ with
--   $$
--   m = \Big\lceil \frac{2}{\varepsilon} \ln \frac{1}{\tilde\delta} \Big\rceil
--   $$
--   draws $s^\perp$ by weak Fourier sampling from a fresh copy of $|\varphi\rangle$; if $s^\perp \notin \mathrm{span}(S^\perp)$ it returns $s^\perp$. After $m$ draws it returns END.
--
--   This definition gives, for each possible output $o$ ($\mathrm{END}$ or $\lambda \in \hat G$), the probability that Algorithm 2 outputs $o$:
--   $$
--   \Pr[\text{output} = o] = \sum_{\lambda_0, \dots, \lambda_{m-1} \in \hat G} \Big(\prod_{i} P(\lambda_i)\Big)\, [F(\lambda_0, \dots, \lambda_{m-1}) = o],
--   $$
--   where $P$ is the Fourier sampling distribution and $F$ returns the first $\lambda_i \notin \langle S^\perp \rangle$ (one membership test per draw), or END if there is none.
--
--   **Formalization Note** $\ln$ is the natural logarithm and $\lceil\cdot\rceil$ is taken in $\mathbb N$, so $m = 0$ at $\tilde\delta = 1$. Draws after the first new element are never made by the algorithm; summing them out does not change the law.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, Algorithm 2, p.25; eq. (24), p.22

import Mathlib
import Definitions.Def_OracleStateHSP_Supplement_fourierProb

namespace OracleStateHSP

namespace Supplement

/-- The output law of Algorithm 2 (copy-based HSP-Sampler, Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, p.25) on input `S⊥` and failure
probability `δ̃`, for the state `|φ⟩` with gap `ε`: for `i = 0, …, m − 1` with
`m = ⌈(2/ε) ln(1/δ̃)⌉`, draw `s⊥` by weak Fourier sampling from a fresh copy of `|φ⟩`; if
`s⊥ ∉ span(S⊥)`, return `s⊥`; after `m` draws return END. The value at `o` is the probability that
the output is `o` (`none` = END):
`∑_(λ_0, …, λ_(m−1)) ∏_i P(λ_i) · [F(λ_0, …, λ_(m−1)) = o]`,
where the draws are i.i.d. from `P` (`fourierProb`) and `F` returns the first `λ_i ∉ ⟨S⊥⟩`
(one membership test per draw), or END if there is none.

**Formalization Note.** `ln` is the natural logarithm `Real.log`; `m = ⌈·⌉₊` (`Nat.ceil`), so
`m = 0` at `δ̃ = 1`. Draws not reached by the loop (after the first new element) are summed out,
which does not change the law. -/
noncomputable def alg2Law {n : ℕ} {M : Fin n → ℕ} [∀ l, NeZero (M l)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : CycProd n M → Matrix ι ι ℂ) (φ : EuclideanSpace ℂ ι) (S : Finset (CycProd n M))
    (ε δt : ℝ) (o : Option (CycProd n M)) : ℝ :=
  ∑ lams : Fin ⌈(2 / ε) * Real.log (1 / δt)⌉₊ → CycProd n M,
    (∏ i, fourierProb R φ (lams i)) *
      (if (List.ofFn lams).find?
          (fun lam => @decide (lam ∉ AddSubgroup.closure (S : Set (CycProd n M)))
            (Classical.propDecidable _)) = o then 1 else 0)

end Supplement

end OracleStateHSP


