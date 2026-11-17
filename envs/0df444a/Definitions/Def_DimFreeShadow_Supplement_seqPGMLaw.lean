-- Prove2me | Definitions.Def_DimFreeShadow_Supplement_seqPGMLaw
-- name    : DimFreeShadow_Supplement_seqPGMLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:59:47.851395+00:00
-- url     : https://prove2.me/theorems/8c8e7419-344c-4fc8-bd65-27edf22b63cc
-- title:
--   Algorithm 1 — joint law of the label and the full history of the $r$-round sequential posterior PGM
-- statement:
--   Let $\mathcal E=\{(p_x,\rho_x):x\in\mathcal X\}$ be a finite ensemble of states on $\mathcal H$ and let $r,n\ge1$ be integers. The **$r$-round sequential posterior PGM** (Algorithm 1) draws a label $X\sim p$ and receives $r$ groups of $n$ fresh copies of $\rho_X$. Starting from the prior $p^{\emptyset}=p$, in round $s$ it measures the next group with the completed PGM $\{G^{(s)}_{y\mid h}\}_y$ of the posterior ensemble $\{(p^h_x,\rho_x^{\otimes n})\}$, where $h=(y_1,\dots,y_{s-1})$ is the history so far (Eq. (2)), and after observing $Y_s=y$ updates the posterior by Bayes' rule,
--
--   $$
--   p^{(h,y)}_x=\frac{p^h_x\operatorname{Tr}\big(G^{(s)}_{y\mid h}\rho_x^{\otimes n}\big)}{p^h_y}\qquad\text{(Eq. (3))}.
--   $$
--
--   The joint law of the label and the full history $H_r=(Y_1,\dots,Y_r)\in\mathcal X^r$ is
--
--   $$
--   \Pr[X=x,\ H_r=h]=p_x\prod_{s=1}^{r}\operatorname{Tr}\big(G^{(s)}_{y_s\mid(y_1,\dots,y_{s-1})}\,\rho_x^{\otimes n}\big),\qquad h=(y_1,\dots,y_r).
--   $$
--
--   The measurements depend only on the ensemble, not on any observable to be estimated.
--
--   **Formalization Note** The helper `posteriorStep` is the update of Eq. (3) and `posterior` applies it along a history (a list in chronological order). When $p^h_y=0$ the outcome has probability zero and the paper completes the posterior arbitrarily (p.8); here the posterior is left unchanged, which does not affect the law (every history through a zero-probability prefix has law $0$). $\mathcal X^r$ is `Fin r → X` with 0-based rounds, $\rho^{\otimes n}$ is the published `tensorPow`, and traces enter through their real parts.
-- source:
--   Jeronimo, Huang, Liu, Dimension-Free Polylogarithmic Quantum Shadow Tomography, arXiv:2608.06345 (sha256 a1a42249…), §2.2, Eqs. (2)–(3), p.6; Algorithm 1, p.7; conventions p.8; Eq. (12), p.12

import Mathlib
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_DimFreeShadow_Supplement_pgmEffect

namespace DimFreeShadow

namespace Supplement

open ShadowTomography.UpperBound (tensorPow)

/-- **One Bayes update of the posterior** (arXiv:2608.06345, sha256 a1a42249…, §2.2, Eq. (3),
p.6, and Algorithm 1, line 10, p.7): after observing `Y_s = y` with the completed PGM
`G^{(s)}_{y|h}` of the current posterior `q = p^h` on `n` fresh copies,
`p^{(h,y)}_x = p^h_x Tr(G^{(s)}_{y|h} ρ_x^{⊗n}) / p^h_y`.

**Formalization Note** The paper's denominator is `p^h_y`, which equals the marginal
`Tr(G^{(s)}_{y|h} ρ̄^{(s)}_h)` (p.8). When `p^h_y = 0` the outcome `y` has probability zero and
the paper completes the posterior arbitrarily (p.8); here it is left unchanged. This choice does
not affect `seqPGMLaw`, which vanishes on every history through a zero-probability prefix.
Traces through real parts. -/
noncomputable def posteriorStep {X d : Type} [Fintype X] [Fintype d] [DecidableEq d]
    (ρ : X → Matrix d d ℂ) (n : ℕ) (q : X → ℝ) (y : X) : X → ℝ :=
  fun x => if q y = 0 then q x else
    q x * (pgmEffect q (fun x' => tensorPow (ρ x') n) y * tensorPow (ρ x) n).trace.re / q y

/-- **Posterior after a history** `p^h` (arXiv:2608.06345, sha256 a1a42249…, §2.2, p.6–7):
starting from `p^∅ = p`, apply the update of Eq. (3) once per observed outcome, in order.
The history `h = (y_1, …, y_{s−1})` is a list in chronological order. -/
noncomputable def posterior {X d : Type} [Fintype X] [Fintype d] [DecidableEq d]
    (ρ : X → Matrix d d ℂ) (n : ℕ) (p : X → ℝ) (h : List X) : X → ℝ :=
  h.foldl (posteriorStep ρ n) p

/-- **Joint law of the label and the full history of the r-round sequential posterior PGM**
(arXiv:2608.06345, sha256 a1a42249…, §2.2, Eqs. (2)–(3), p.6, Algorithm 1, p.7, Eq. (12),
p.12). For an ensemble `{(p_x, ρ_x)}` and integers `r, n`, the label `X` is drawn from `p`, and
in round `s = 1, …, r` the completed PGM `G^{(s)}_{·|H_{s−1}}` of the posterior ensemble
`{(p^{H_{s−1}}_x, ρ_x^{⊗n})}` (Eq. (2)) is measured on `n` fresh copies of `ρ_X`. Hence
`Pr[X = x, H_r = h] = p_x ∏_{s=1}^r Tr(G^{(s)}_{y_s|(y_1,…,y_{s−1})} ρ_x^{⊗n})` for
`h = (y_1, …, y_r) ∈ X^r`, i.e. `p_x Tr(M̃^{[r]}_h ρ_x^{⊗rn})` with the full-history effects of
Eq. (12).

**Formalization Note** `X^r` is `Fin r → X`, rounds 0-based (`s : Fin r` is the paper's round
`s + 1`), and the history before round `s` is the first `s` entries of `h`. `n` copies form
`Fin n → d` and `ρ^{⊗n}` is the published `tensorPow`. The PGMs do not depend on any observable.
Traces through real parts. -/
noncomputable def seqPGMLaw {X d : Type} [Fintype X] [Fintype d] [DecidableEq d]
    (p : X → ℝ) (ρ : X → Matrix d d ℂ) (n r : ℕ) (x : X) (h : Fin r → X) : ℝ :=
  p x * ∏ s : Fin r,
    (pgmEffect (posterior ρ n p ((List.ofFn h).take s)) (fun x' => tensorPow (ρ x') n) (h s) *
      tensorPow (ρ x) n).trace.re

end Supplement

end DimFreeShadow


