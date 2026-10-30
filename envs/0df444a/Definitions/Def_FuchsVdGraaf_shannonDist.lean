-- Prove2me | Definitions.Def_FuchsVdGraaf_shannonDist
-- name    : FuchsVdGraaf_shannonDist
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:15:14.500624+00:00
-- url     : https://prove2.me/theorems/d738c4f2-3d98-43d2-be3e-2ce5361a70f7
-- title:
--   Shannon distinguishability $SD(p_0,p_1)$ (Definition 10)
-- statement:
--   Let $p_0, p_1$ be probability distributions on a finite set $\mathcal X$. Toss a fair coin $T\in\{0,1\}$ and draw $X$ from $p_T$. The **Shannon distinguishability** is the mutual information $\mathrm{SD}(p_0,p_1) = I(T;X)$, which by the expansion on p.15 equals
--
--   $$
--   \mathrm{SD}(p_0,p_1) = H(p) - \Big(\tfrac12 H(p_0) + \tfrac12 H(p_1)\Big), \qquad p(x) = \tfrac12\big(p_0(x) + p_1(x)\big),
--   $$
--
--   with entropies in bits. It is the amount of information one sample conveys about which distribution it came from: $0$ for identical, $1$ for orthogonal distributions.
--
--   **Formalization Note** Defined through the expansion (32) of $I(T;X) = H(X) - H(X\mid T)$, which avoids the quotient $r_0(x) = p_0(x)/(2p(x))$ of the alternative form (40), undefined where $p(x) = 0$.
-- source:
--   Fuchs and van de Graaf, Cryptographic Distinguishability Measures for Quantum Mechanical States, arXiv:quant-ph/9712042v2, Definition 10, eq. (36), p.15, via eqs. (30)-(35)

import Mathlib
import Definitions.Def_FuchsVdGraaf_entropy

namespace FuchsVdGraaf

/-- Fuchs and van de Graaf, arXiv:quant-ph/9712042v2, Definition 10, eq. (36), p.15: the
Shannon distinguishability `SD(p₀, p₁) = I(T; X)`, the mutual information between a fair coin
`T ∈ {0, 1}` and the sample `X ∼ p_T`. By the paper's expansion (30)–(35), p.15,
`SD(p₀, p₁) = H(p) − (½ H(p₀) + ½ H(p₁))` with `p(x) = ½ (p₀(x) + p₁(x))`.

**Formalization Note.** Defined through the expansion (32), entropies in bits (`entropy`).
This avoids the quotient `r₀(x) = p₀(x)/(2p(x))` of (40), which is `0/0` where `p(x) = 0`. -/
noncomputable def shannonDist {X : Type} [Fintype X] (p0 p1 : X → ℝ) : ℝ :=
  entropy (fun x => (p0 x + p1 x) / 2) - (entropy p0 + entropy p1) / 2

end FuchsVdGraaf


