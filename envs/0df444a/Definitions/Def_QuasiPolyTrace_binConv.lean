-- Prove2me | Definitions.Def_QuasiPolyTrace_binConv
-- name    : QuasiPolyTrace_binConv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:52.209297+00:00
-- url     : https://prove2.me/theorems/cb72efe2-35bc-40d6-b847-cd001715ceb0
-- title:
--   Binomial blurring $f*\mathrm{Bin}(R,p)$
-- statement:
--   For a real or complex sequence $f:\mathbb Z\to\mathbb K$, a natural number $R$ and $p\in\mathbb R$, the **binomially blurred** sequence is the convolution of $f$ with the probability mass function of $\mathrm{Bin}(R,p)$:
--
--   $$
--   (f*\mathrm{Bin}(R,p))(j)=\sum_{i=0}^{R} f(j-i)\,\mathrm{bin}(R,i,p),\qquad j\in\mathbb Z .
--   $$
--
--   In the paper this is written $f_b:=f*\mathrm{Bin}(R,p)$. Its generating function is $F(z)\,((1-p)+pz)^R$ when $F$ is that of $f$. Zooming out by $R$ positions in the deletion channel blurs the sequence of shifted statistics in exactly this way (Corollary 6).
--
--   **Formalization Note** One definition serves real sequences (Lemmas 14, 16, Corollary 17) and complex ones (Corollary 34); the sum is finite because $\mathrm{bin}(R,\cdot,p)$ vanishes outside $\{0,\dots,R\}$.
-- source:
--   Burudgunte, Valiant, Wang, Quasipolynomial Trace Reconstruction, manuscript of November 2, 2026 (later version of arXiv:2607.04073; sha256 9ecb6d18…), Lemma 14, p.16; Lemma 16, p.18; Corollary 34, pp.30–31 (f ∗ Bin(R, p))

import Mathlib
import Definitions.Def_QuasiPolyTrace_bin

namespace QuasiPolyTrace

/-- **Binomial blurring `f ∗ Bin(R, p)`.** Burudgunte, Valiant, Wang, *Quasipolynomial Trace Reconstruction*, manuscript of November 2, 2026
(later version of arXiv:2607.04073; sha256 9ecb6d18…), Lemma 14, p.16, Lemma 16, p.18 and Corollary 34,
p.30: "the binomially blurred version of f by convolving with the binomial: let `f_b := f ∗ Bin(R, p)`".

For a sequence `f : ℤ → 𝕜` (real or complex),
`(f ∗ Bin(R, p))(j) = ∑_{i=0}^{R} f(j − i) · bin(R, i, p)`.

**Formalization Note.** The convolution is with the probability mass function `i ↦ bin(R, i, p)`, which
vanishes outside `{0, …, R}`, so the sum is finite. Its generating function is `((1 − p) + p z)^R`, as in
the proof of Lemma 14 (p.16). -/
noncomputable def binConv {𝕜 : Type*} [RCLike 𝕜] (f : ℤ → 𝕜) (R : ℕ) (p : ℝ) (j : ℤ) : 𝕜 :=
  ∑ i ∈ Finset.range (R + 1), f (j - i) * ((bin R i p : ℝ) : 𝕜)

end QuasiPolyTrace


