-- Prove2me | Definitions.Def_OptimalSpectrum_Entangled_gPoly
-- name    : OptimalSpectrum_Entangled_gPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:43.936831+00:00
-- url     : https://prove2.me/theorems/f1efb620-4635-44c3-bfff-1a63956f5bd7
-- title:
--   Symmetric multiaffine estimator $g_p(X_1,\dots,X_n)$, Eq. (36)
-- statement:
--   For Hermitian matrices $X_1,\dots,X_n$ and $1\le m\le n$,
--
--   $$g_m(X_1,\dots,X_n)=\frac1{n^{\downarrow m}}\sum_{\substack{i_1,\dots,i_m\in[n]\\\text{all distinct}}}\mathrm{tr}(X_{i_1}\cdots X_{i_m}),\qquad g_0\equiv d,\qquad g_p=\sum_{m=0}^K p_mg_m$$
--
--   for $p(x)=\sum_m p_mx^m$. The unentangled moment estimate is $\widehat F_p=g_p(X_1,\dots,X_n)$ for i.i.d. single-copy estimators $X_i$.
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, §7.1.1, Eq. (36), p. 20 (PDF p. 22)

import Mathlib

namespace OptimalSpectrum.Entangled

/-- **The symmetric multiaffine moment estimator `g_p`.**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, §7.1.1, Eq. (36), printed p. 20 (PDF p. 22): "For deterministic Hermitian matrices
X₁, …, X_n, define g_m(X₁, …, X_n) := (1/n^↓m) ∑_(i₁,…,i_m ∈ [n] all distinct) tr(X_(i₁) ⋯ X_(i_m)),
1 ⩽ m ⩽ K, and set g₀ ≡ d. … For p(x) = ∑_(m=0)^K p_m x^m, define g_p := ∑_(m=0)^K p_m g_m."

**Formalization Note.** Ordered tuples of distinct indices are embeddings `Fin m ↪ Fin n`; the sum
runs over `m ≤ deg p`. The real part of the trace is taken (the trace is real on the Hermitian
inputs of the paper; the page says `g_p` is real-valued). -/
noncomputable def gPoly (d n : ℕ) (p : Polynomial ℝ) (X : Fin n → Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ∑ m ∈ Finset.range (p.natDegree + 1), p.coeff m *
    (if m = 0 then (d : ℝ)
     else (1 / (n.descFactorial m : ℝ)) *
       ∑ t : Fin m ↪ Fin n, (Matrix.trace (List.ofFn fun j => X (t j)).prod).re)

end OptimalSpectrum.Entangled


