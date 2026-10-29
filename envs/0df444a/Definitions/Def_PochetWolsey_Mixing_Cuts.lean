-- Prove2me | Definitions.Def_PochetWolsey_Mixing_Cuts
-- name    : PochetWolsey_Mixing_Cuts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:28:13.431862+00:00
-- url     : https://prove2.me/theorems/38d84218-28d0-4114-a62b-b1ecd86626d8
-- title:
--   The two mixing-inequality right-hand sides
-- statement:
--   Let $b\in\mathbb R^K$, let $T$ be a nonempty subset of the coordinates, and enumerate it as $i_1,\ldots,i_q$. Write $f_k=b_k-\lfloor b_k\rfloor$ and set the predecessor level of $i_1$ to zero. For $y\in\mathbb R^K$, define
--   $$
--   C_T(y)=\sum_{\tau=1}^q(f_{i_\tau}-f_{i_{\tau-1}})(\lfloor b_{i_\tau}\rfloor+1-y_{i_\tau}),\qquad
--   D_T(y)=C_T(y)+(1-f_{i_q})(\lfloor b_{i_1}\rfloor-y_{i_1}).
--   $$
--   The mixing inequalities are $s\ge C_T(y)$ and $s\ge D_T(y)$. This file defines the algebraic expressions; injectivity and nondecreasing fractional parts are hypotheses of the validity theorem.
--
--   **Formalization Note** The formulas are defined for every sequence of length $q=t+1$, including repeated or unsorted coordinates; validity is only asserted for an injective sorted sequence. The first term is separated from the sum over consecutive pairs, so $t=0$ gives exactly the singleton case without a missing predecessor or truncated subtraction.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, p. 242 (PDF 256), Proposition 8.4, Eqs. (8.7)–(8.8)

import Mathlib
import Definitions.Def_PochetWolsey_Mixing_Model

namespace PochetWolsey.Mixing

noncomputable def cutRhs {K t : ℕ} (b : Fin K → ℝ)
    (i : Fin (t + 1) → Fin K) (y : Fin K → ℝ) : ℝ :=
  frac (b (i 0)) * ((⌊b (i 0)⌋ : ℝ) + 1 - y (i 0)) +
    ∑ j : Fin t, (frac (b (i j.succ)) - frac (b (i j.castSucc))) *
      ((⌊b (i j.succ)⌋ : ℝ) + 1 - y (i j.succ))

noncomputable def wrapCutRhs {K t : ℕ} (b : Fin K → ℝ)
    (i : Fin (t + 1) → Fin K) (y : Fin K → ℝ) : ℝ :=
  cutRhs b i y + (1 - frac (b (i (Fin.last t)))) *
    ((⌊b (i 0)⌋ : ℝ) - y (i 0))

end PochetWolsey.Mixing


