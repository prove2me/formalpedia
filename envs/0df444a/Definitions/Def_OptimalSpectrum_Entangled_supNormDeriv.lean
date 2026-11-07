-- Prove2me | Definitions.Def_OptimalSpectrum_Entangled_supNormDeriv
-- name    : OptimalSpectrum_Entangled_supNormDeriv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:17.301919+00:00
-- url     : https://prove2.me/theorems/724f659f-b304-4f08-9049-ff6fef4bcfc3
-- title:
--   Sup norm $\|p^{(r)}\|_{\infty,[0,L]}$ of a polynomial derivative
-- statement:
--   For a real polynomial $p$, an order $r\ge0$ and $L\ge0$,
--
--   $$\|p^{(r)}\|_{\infty,[0,L]}=\max_{x\in[0,L]}\big|p^{(r)}(x)\big|,$$
--
--   where $p^{(r)}$ is the $r$-th derivative. The variance bounds of Section 7 are stated in terms of these norms.
--
--   **Formalization Note** Defined as a supremum over $[0,L]$; every use has $L>0$ or eigenvalues in $[0,L]$, so the set is nonempty and compact.
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, Lemma 7.1, p. 19 (PDF p. 21)

import Mathlib

namespace OptimalSpectrum.Entangled

/-- **Sup norm `‖p^(r)‖_(∞,[0,L])` of a derivative of a polynomial.**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, Lemma 7.1, printed p. 19 (PDF p. 21): "We write p^(r) for the rth derivative of the scalar
polynomial p", with `∥·∥_(∞,[0,L])` the supremum norm on `[0, L]`.

`supNormDeriv p r L = sup_(x ∈ [0,L]) |p^(r)(x)|`.

**Formalization Note.** For `L ≥ 0` the interval is nonempty and compact, so the supremum is a
maximum; every statement using it has `L > 0` or `λᵢ ∈ [0, L]`. -/
noncomputable def supNormDeriv (p : Polynomial ℝ) (r : ℕ) (L : ℝ) : ℝ :=
  sSup ((fun x => |(Polynomial.derivative^[r] p).eval x|) '' Set.Icc 0 L)

end OptimalSpectrum.Entangled


