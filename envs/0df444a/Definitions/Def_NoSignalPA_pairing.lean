-- Prove2me | Definitions.Def_NoSignalPA_pairing
-- name    : NoSignalPA_pairing
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:02:35.274391+00:00
-- url     : https://prove2.me/theorems/9ed42850-132a-40e0-81a4-032359f37805
-- title:
--   The pairing $\langle c|Q\rangle$ on $\mathbb R^{16^n}$
-- statement:
--   For vectors $c,Q\in\mathbb R^{16^n}$ indexed by $(\mathbf a,\mathbf b,\mathbf x,\mathbf y)\in(\{0,1\}^n)^4$,
--
--   $$
--   \langle c|Q\rangle=\sum_{\mathbf a,\mathbf b,\mathbf x,\mathbf y}c(\mathbf a,\mathbf b,\mathbf x,\mathbf y)\,Q(\mathbf a,\mathbf b,\mathbf x,\mathbf y).
--   $$
--
--   This is the inner product the paper writes as $\langle\mathrm{CHSH}|^{\otimes N_r}|P_{\mathbf a,\mathbf b|\mathbf x,\mathbf y}\rangle$ and $\langle\Gamma_{\mathbf a}|P_{\mathbf a,\mathbf b|\mathbf x,\mathbf y}\rangle$. The sum over settings is not normalized: a box has total mass $4^n$ in it.
-- source:
--   Masanes, Universally-composable privacy amplification from causality constraints, arXiv:0807.2158v4, eqs. (2), (5), pp.1–2; Lemma 1, p.2

import Mathlib
import Definitions.Def_NoSignalPA_Str

namespace NoSignalPA

/-- **The pairing `⟨c|Q⟩` of two vectors in `ℝ^{16^n}`.**
Ll. Masanes, *Universally-composable privacy amplification from causality constraints*,
arXiv:0807.2158v4, eqs. (2), (5), p. 1–2, and Lemma 1, p. 2 (printed = PDF pages): `⟨CHSH|P_{a,b|x,y}⟩` and
`⟨Γ_a|P_{a,b|x,y}⟩` are the Euclidean inner products of the coefficient vector with the vector
of all probabilities (3).

`pairing c Q = Σ_{a,b,x,y ∈ {0,1}^n} c(a,b,x,y) Q(a,b,x,y)`.

**Formalization Note.** Vectors of `ℝ^{16^n}` are functions of `(a, b, x, y)`, in this argument
order. The sum runs over all settings `x, y` and is not normalized: a box has total mass `4^n`
in it, as in the paper (`⟨CHSH|P⟩ ≥ √2` for local boxes when `n = 1`). -/
def pairing {n : ℕ} (c Q : Str n → Str n → Str n → Str n → ℝ) : ℝ :=
  ∑ a : Str n, ∑ b : Str n, ∑ x : Str n, ∑ y : Str n, c a b x y * Q a b x y

end NoSignalPA


