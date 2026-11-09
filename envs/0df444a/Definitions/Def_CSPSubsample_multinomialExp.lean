-- Prove2me | Definitions.Def_CSPSubsample_multinomialExp
-- name    : CSPSubsample_multinomialExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:14:38.708126+00:00
-- url     : https://prove2.me/theorems/af418919-ae55-4034-8eea-9f9a71163ff9
-- title:
--   Expectation under $\mathrm{Multinomial}(N,y)$
-- statement:
--   For $y\in\Delta_d$ (a probability vector on $[d]$), $(N_j)_{j\in[d]}\sim\mathrm{Multinomial}(N,y)$ is the vector of counts of the $d$ outcomes in $N$ independent draws from $y$. For a function $F$ of the counts,
--   $$
--   \mathbb E[F(N_1,\dots,N_d)]=\sum_{(s_1,\dots,s_N)\in[d]^N}\Big(\prod_{t=1}^Ny_{s_t}\Big)\,F\big(\#\{t:s_t=1\},\dots,\#\{t:s_t=d\}\big).
--   $$
--   This is the law whose factorial moments (Claim 4.3) control the bias of $f(Z)$.
-- source:
--   Bernasconi, Castiglioni, Celli, Farina, Malavolta, A Subsampling Theorem for Constraint Satisfaction Problems with Large Arity, arXiv:2608.00203 (PDF sha256 fd9ae01113266fee273c46c14c8a1a39f36a958dba3fc276cd74bf4c3daff445), Claim 4.3, p.10 (PDF p.12)

import Mathlib

set_option autoImplicit false

namespace CSPSubsample

/-- The count `N_j = #{t : s_t = j}` of outcome `j` in a sequence `s` of `N` draws. -/
def countOf {N d : ℕ} (s : Fin N → Fin d) (j : Fin d) : ℕ :=
  (Finset.univ.filter fun t => s t = j).card

/-- The expectation `E[F(N_1, …, N_d)]` for `(N_j)_{j ∈ [d]} ∼ Multinomial(N, y)`
(arXiv:2608.00203 (PDF sha256 fd9ae011…), Claim 4.3, p.10 = PDF p.12).

**Formalization Note** The multinomial law is the law of the counts of `N` i.i.d. draws from
`y ∈ Δ_d`; the expectation is written as the sum over the `d^N` draw sequences
`s : Fin N → Fin d`, each weighted by its probability `∏_t y_{s_t}`. -/
noncomputable def multinomialExp (d N : ℕ) (y : Fin d → ℝ) (F : (Fin d → ℕ) → ℝ) : ℝ :=
  ∑ s : Fin N → Fin d, (∏ t, y (s t)) * F (countOf s)

end CSPSubsample


