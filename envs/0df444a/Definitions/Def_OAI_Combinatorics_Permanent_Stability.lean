-- Prove2me | Definitions.Def_OAI_Combinatorics_Permanent_Stability
-- name    : OAI_Combinatorics_Permanent_Stability
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T17:49:15.352424+00:00
-- url     : https://prove2.me/theorems/d16171d7-ef2c-4f1e-b685-753270bcaef8
-- title:
--   Row deficits, $2\times2$ pair permanents and the uniform law for four-row permanent estimates
-- statement:
--   This module introduces the elementary quadratic quantities used in the stability estimates for the four-row permanent inequality. Throughout, the sites are $\{0,1,2,3\}$; a *row* is a vector $a=(a_0,a_1,a_2,a_3)\in\mathbb{R}^4$, an *array* is a real $4\times4$ matrix $f=(f_{ij})_{i,j=0}^{3}$ with rows $f_i=(f_{i0},f_{i1},f_{i2},f_{i3})$, and a *law* is a real-valued function on the symmetric group $S_4$ of permutations of the four sites.
--
--   1. **Row square sum.** $S(a)=\sum_{j=0}^{3}a_j^2$. The normalization used later is $S(a)=4$, i.e. mean square $1$ for the uniform counting measure on the four sites, as for the all-ones row $\mathbf{1}=(1,1,1,1)$.
--
--   2. **Squared distance to the all-ones row.** $\rho(a)=\sum_{j=0}^{3}(a_j-1)^2$.
--
--   3. **Row inner product.** $\langle a,b\rangle=\sum_{j=0}^{3}a_jb_j$.
--
--   4. **Pair-permanent vector.** For two rows $a,b$ and a pair of sites $k<l$, put $w_{kl}(a,b)=a_kb_l+a_lb_k$, the permanent of the $2\times2$ submatrix in columns $k,l$ of the $2\times4$ matrix with rows $a$ and $b$. The six values form a vector $w(a,b)\in\mathbb{R}^6$, listed in lexicographic order of the pairs:
--   $$
--   w(a,b)=\bigl(w_{01}(a,b),\,w_{02}(a,b),\,w_{03}(a,b),\,w_{12}(a,b),\,w_{13}(a,b),\,w_{23}(a,b)\bigr).
--   $$
--   In this order the entries with indices $m$ and $5-m$ (for $m=0,\dots,5$) belong to complementary pairs of sites.
--
--   5. **Pair-permanent square sum.** $Q(a,b)=\sum_{0\le k<l\le3}(a_kb_l+a_lb_k)^2$, the squared Euclidean norm of $w(a,b)$.
--
--   6. **Uniform law.** $u(\pi)=\tfrac{1}{24}$ for every $\pi\in S_4$.
--
--   7. **Total distance to the all-ones matrix.** For an array $f$, $\Delta(f)=\sum_{i=0}^{3}\rho(f_i)=\sum_{i,j=0}^{3}(f_{ij}-1)^2$, the squared Frobenius distance from $f$ to the all-ones matrix $J$.
--
--   At the extremal configuration $f=J$ one has $S(\mathbf{1})=4$, $\rho(\mathbf{1})=0$, $w(\mathbf{1},\mathbf{1})=(2,2,2,2,2,2)$ and $Q(\mathbf{1},\mathbf{1})=24$. The quantities $\rho$ and $\Delta$ measure how far normalized rows are from this configuration, while the pair permanents enter through the Laplace expansion of the permanent along rows $0$ and $1$,
--   $$
--   \operatorname{per}(f)=\sum_{\pi\in S_4}\prod_{i=0}^{3}f_{i\pi(i)}=\sum_{m=0}^{5}w_m(f_0,f_1)\,w_{5-m}(f_2,f_3).
--   $$
--   Together they express the exponent-two stability estimate for the uniform law, the perturbation bound for laws near $u$, and the lower bound for $\ell^p$ row norms below exponent two.
--
--   **Formalization Note** Sites are `Fin 4`, rows are real functions on `Site`, arrays have type `Functions` (real functions of two sites) and laws have type `Law` (real functions on `Perm`). The definitions are `rowSq`, `rowDist`, `rowDot`, `pairEntries` (a `Fin 6`-indexed vector), `pairSq`, `uniformLaw` and `totalDist`; no nonnegativity or normalization is built into any of them.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Permanent/Stability.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Permanent/Stability.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FourRowPermanent mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FourRowPermanent

namespace OAI

noncomputable section
namespace FourRow
open scoped BigOperators

/- Quantitative exponent-two stability estimates. -/
def rowSq (a : Site → ℝ) : ℝ := ∑ j, a j ^ 2

def rowDist (a : Site → ℝ) : ℝ := ∑ j, (a j - 1) ^ 2

def rowDot (a b : Site → ℝ) : ℝ := ∑ j, a j * b j

def pairEntries (a b : Site → ℝ) : Fin 6 → ℝ :=
  ![a 0 * b 1 + a 1 * b 0,
    a 0 * b 2 + a 2 * b 0,
    a 0 * b 3 + a 3 * b 0,
    a 1 * b 2 + a 2 * b 1,
    a 1 * b 3 + a 3 * b 1,
    a 2 * b 3 + a 3 * b 2]

def pairSq (a b : Site → ℝ) : ℝ := ∑ j, pairEntries a b j ^ 2

def uniformLaw : Law := fun _ => 1 / 24

def totalDist (f : Functions) : ℝ := ∑ i, rowDist (f i)

end FourRow
end

end OAI


