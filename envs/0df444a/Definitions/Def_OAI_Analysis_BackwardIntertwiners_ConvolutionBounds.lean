-- Prove2me | Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
-- name    : OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:50:46.673314+00:00
-- url     : https://prove2.me/theorems/38518f2e-5d60-4db3-bd57-f4a9c63fab83
-- title:
--   Exponential envelope bounds and centered correlations of two-sided sequences
-- statement:
--   This file fixes the growth-and-decay hypotheses on a pair of two-sided complex sequences and two auxiliary quantities that enter the estimate of their correlations. Throughout, $A,B:\mathbb{N}\to\mathbb{R}$ are real sequences and $b,c:\mathbb{Z}\to\mathbb{C}$ are two-sided complex sequences.
--
--   1. **Envelope bounds.** The pair $(b,c)$ satisfies the envelope bounds with exponents $(A,B)$ if for every $n\in\mathbb{N}$
--   $$|b(n)|\le e^{-B(n)},\qquad |b(-n)|\le e^{A(n)},\qquad |c(n)|\le e^{B(n)},\qquad |c(-n)|\le e^{-A(n)}.$$
--   Thus $b$ decays at rate $B$ to the right and may grow at rate $A$ to the left, while $c$ has the mirror behaviour. At $n=0$ the first two bounds both apply to $b(0)$ and the last two both apply to $c(0)$.
--   2. **Centered correlation.** For $m,p\in\mathbb{N}$ and $n\in\mathbb{Z}$,
--   $$\kappa_{b,c}(m,p;n)=b(p+n)\,c(n-m).$$
--   Summed over $n\in\mathbb{Z}$ this is the correlation $\sum_{j\in\mathbb{Z}}b(j)\,c(j-r)$ at lag $r=m+p$, re-indexed so that the term $n=0$ is the product $b(p)\,c(-m)$.
--   3. **Geometric middle term.** For $\lambda\in\mathbb{R}$ and $k\in\mathbb{N}$, $g_\lambda(k)=e^{-\lambda(k+1)}$; for $\lambda>0$ one has $\sum_{k\ge0}g_\lambda(k)=1/(e^\lambda-1)$.
--
--   These objects are used in a quantitative obstruction. Call $F:\mathbb{N}\to\mathbb{R}$ discretely convex if $n\mapsto F(n+1)-F(n)$ is non-decreasing, and put $\tau_F(q,k)=\exp(F(k+1)+F(q)-F(q+k+1))$. If $A,B$ are discretely convex with $A(0)=B(0)=0$ and summable sequences $e^{-(A(n+1)-A(n))}$, $e^{-(B(n+1)-B(n))}$, the envelope bounds hold, $|b(p)|=e^{-B(p)}$ and $|c(-m)|=e^{-A(m)}$ for some $m,p\ge1$, the slopes satisfy $A(m)-A(m-1)+\lambda\le B(p+1)-B(p)$ and $B(p)-B(p-1)+\lambda\le A(m+1)-A(m)$ for some $\lambda>0$, and $\sum_n\kappa_{b,c}(m,p;n)=0$, then
--   $$1\le 2\sum_{k\ge0}g_\lambda(k)+\sum_{k\ge0}\tau_A(m+p,k)+\sum_{k\ge0}\tau_B(m+p,k).$$
--   For $\lambda>\log 3$ the geometric part is below $1$, and this is what drives the support-separation results for sequences with vanishing correlations.
--
--   **Formalization Note** `EnvelopeBounds A B b c` is a structure with the fields `b_pos`, `b_neg`, `c_pos`, `c_neg`; natural numbers are cast to integers, so `b (-(n : ℤ))` is $b(-n)$, and the norm of a complex number is its absolute value. The other definitions are `centeredCorrelation b c m p n` and `geometricMiddle lam k`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/ConvolutionBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/ConvolutionBounds.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BackwardIntertwiners mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

structure EnvelopeBounds (A B : ℕ → ℝ) (b c : ℤ → ℂ) : Prop where
  b_pos : ∀ n : ℕ, ‖b n‖ ≤ Real.exp (-B n)
  b_neg : ∀ n : ℕ, ‖b (-(n : ℤ))‖ ≤ Real.exp (A n)
  c_pos : ∀ n : ℕ, ‖c n‖ ≤ Real.exp (B n)
  c_neg : ∀ n : ℕ, ‖c (-(n : ℤ))‖ ≤ Real.exp (-A n)

def centeredCorrelation (b c : ℤ → ℂ) (m p : ℕ) (n : ℤ) : ℂ :=
  b ((p : ℤ)+n) * c (-(m : ℤ)+n)

namespace EnvelopeBounds

variable {A B : ℕ → ℝ} {b c : ℤ → ℂ}

end EnvelopeBounds

def geometricMiddle (lam : ℝ) (k : ℕ) : ℝ := Real.exp (-lam * ((k : ℝ)+1))

namespace EnvelopeBounds

variable {A B : ℕ → ℝ} {b c : ℤ → ℂ}

end EnvelopeBounds

end
end BackwardIntertwiners

end OAI


