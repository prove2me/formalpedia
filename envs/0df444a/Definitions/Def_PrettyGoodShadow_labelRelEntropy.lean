-- Prove2me | Definitions.Def_PrettyGoodShadow_labelRelEntropy
-- name    : PrettyGoodShadow_labelRelEntropy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:22:33.476342+00:00
-- url     : https://prove2.me/theorems/a0e6d207-99cd-4145-84f4-dc558eb57c0c
-- title:
--   Classical relative entropy $D(q\|p)$ of priors
-- statement:
--   For priors $q,p$ on a finite label set,
--
--   $$
--   D(q\|p)=\sum_x q_x\log\frac{q_x}{p_x}.
--   $$
--
--   It bounds the telescoped relative entropy in Lemma 4.9.
--
--   **Formalization Note** Natural logarithm. Terms with $q_x=0$ vanish. Every statement using it assumes $\operatorname{supp}(q)\subseteq\operatorname{supp}(p)$, the case in which the value is finite.
-- source:
--   Grewal, Pelecanos, Spilecki, Tang, Wright, Pretty good shadow tomography, arXiv:2610.06781 (sha256 bd055b7d…), p.22

import Mathlib

namespace PrettyGoodShadow

/-- **Classical relative entropy of priors** `D(q ∥ p) = Σ_x q_x log(q_x / p_x)` (arXiv:2610.06781, sha256
bd055b7d…, p.22).

**Formalization Note** Natural logarithm. Terms with `q_x = 0` vanish. Every statement using it assumes
`supp(q) ⊆ supp(p)`, the case in which the page's value is finite and the division is by a positive number. -/
noncomputable def labelRelEntropy {L : Type} [Fintype L] (q p : L → ℝ) : ℝ :=
  ∑ x, q x * Real.log (q x / p x)

end PrettyGoodShadow


