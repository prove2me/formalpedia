-- Prove2me | Definitions.Def_SinglePointPricing_Det_Supplement_LP
-- name    : SinglePointPricing_Det_Supplement_LP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T17:30:23.287578+00:00
-- url     : https://prove2.me/theorems/34ef99df-5a05-4764-adb4-056f5ca55cc5
-- title:
--   (LP) (corrected: terminal oracle) — point-information factor-revealing linear program
-- statement:
--   Fix $\alpha\in[0,1]$, $q\in(0,1)$, $w>0$ and $N>1$. The point-information program uses a strictly increasing positive grid $A=(a_0,\ldots,a_{2N})$ with $a_N<w=a_{N+1}$. Write $O(r)=\operatorname{opt}(F_\alpha(\cdot\mid r,(w,q)))$ and define $d_i=\lim_{r\uparrow a_{i+1}}O(r)$ for $i<2N$. For the terminal row use the saturated high-branch oracle
--   $$
--   d_{2N}=\frac{w\widetilde v_\alpha}{\Gamma_\alpha^{-1}(q)},\qquad
--   \underline L_{\alpha,q,A}=\sup\left\{c:\ p_j\ge0,\ \sum_{j=0}^{2N}p_j\le1,\quad c\le\frac{\sum_{j=0}^{2N}a_j\overline F_\alpha(a_j\mid a_i,(w,q))p_j}{d_i}\quad(0\le i\le2N)\right\}.
--   $$
--   Here $\widetilde v_0=1$, $\widetilde v_1=e^{-1}$, and $\widetilde v_\alpha=\alpha^{\alpha/(1-\alpha)}$ for $0<\alpha<1$, all reused from the base mission. The set of objectives is nonempty and bounded above, and Theorem 3 asserts normalized attainment as well as its performance guarantee. Finite positive endpoint left limits exist; in particular the low-side limit at $w$ is $w$, not the high-branch oracle at $w$.
--
--   **Formalization Note** The page leaves $a_{2N+1}$ undefined. Appendix F appends the upper parameter endpoint. At $\alpha=0$ the terminal oracle is the limit at infinity, $wq/(1-q)$. When $\alpha>0$ and $\overline r_\alpha\ge w$, the displayed terminal value is precisely the oracle at that endpoint. When $\overline r_\alpha<w$, the high-parameter family is empty; the terminal value continues the saturated high branch rather than switching to the low branch of the published piecewise function. The literal switch would destroy convergence (see DISPROOF.md). All coefficients are computed from the source family; the value is not defined to be a maximin ratio. Outside the stated parameter and grid domains the definitions are total functions with no asserted mathematical interpretation.
-- source:
--   Allouah, Bahamou & Besbes, Optimal Pricing with a Single Point, arXiv:2103.05611v2, (LP), pp. 25–26; Appendix F, pp. App-40–App-48

import Mathlib
import Definitions.Def_SinglePointPricing_Det_Supplement_Grid
import Definitions.Def_SinglePointPricing_Det_WorstCase

namespace SinglePointPricing.Det.Supplement

noncomputable section
open Filter Topology

/-- Printed one-sided oracle at a finite positive endpoint. In particular at
`b = w` this uses the low branch's limit, never the value of the high branch. -/
def leftOracle (α w q b : ℝ) : ℝ :=
  limUnder (𝓝[<] b) (fun r : ℝ => optFun (Fbar α w q r))

/-- Saturated high-branch oracle revenue `w ṽ_α / Γ_α⁻¹(q)`.
For `α=0` this is the limit at infinity `wq/(1-q)`; for `α>0` it is
the oracle at the high-branch monopoly point. If that point lies below `w`,
the high parameter interval is empty and this is still the saturated oracle,
not the low-branch `Fbar` at that point. See the source correction evidence. -/
def topOracle (α w q : ℝ) : ℝ := w * vTilde α / GammaAInv α q

/-- (LP), p. 26: append the terminal high-branch oracle after the `2N+1` points. -/
def lpNorm (α w q : ℝ) (a : ℕ → ℝ) (N i : ℕ) : ℝ :=
  if i < 2 * N then leftOracle α w q (a (i + 1)) else topOracle α w q

/-- The actual linear constraints of (LP), including subprobability mass. -/
def LPFeasible (α w q : ℝ) (a : ℕ → ℝ) (N : ℕ) (p : ℕ → ℝ) (c : ℝ) : Prop :=
  (∀ j < 2 * N + 1, 0 ≤ p j) ∧
  (∑ j ∈ Finset.range (2 * N + 1), p j) ≤ 1 ∧
  ∀ i < 2 * N + 1, c ≤
    (∑ j ∈ Finset.range (2 * N + 1), a j * Fbar α w q (a i) (a j) * p j) /
      lpNorm α w q a N i

/-- The (LP) objective supremum; attainment is a theorem clause. -/
def LPval (α w q : ℝ) (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  sSup {c : ℝ | ∃ p : ℕ → ℝ, LPFeasible α w q a N p c}

end
end SinglePointPricing.Det.Supplement


