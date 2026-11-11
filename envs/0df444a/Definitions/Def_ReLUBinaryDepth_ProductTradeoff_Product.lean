-- Prove2me | Definitions.Def_ReLUBinaryDepth_ProductTradeoff_Product
-- name    : ReLUBinaryDepth_ProductTradeoff_Product
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:37.755951+00:00
-- url     : https://prove2.me/theorems/300294d3-5384-4862-8963-40049ab909d7
-- title:
--   Bounded Boolean products, selector and accumulator
-- statement:
--   For $B>1$ and fixed constants $0\le\theta_i(b)\le B$, define the product
--   $$P(x)=\prod_{i=0}^{n-1}\theta_i(x_i).$$
--   The selector expression, defined independently of its correctness, is
--   $$S_{\theta,M}(x,a)=\operatorname{ReLU}(a\theta(0)-Mx)+\operatorname{ReLU}(a\theta(1)-M(1-x)).$$
--   For $M=B^n$, the accumulator starts at $a(0)=1$ and, for $k<n$, satisfies the defining recurrence $a(k+1)=S_{\theta_k,M}(x_k,a(k))$. Beyond $n$ it stays constant. Zero coefficients are admitted, and the empty product is 1.
--
--   These definitions specify the function to be computed and the numerical recurrence used by the construction, without assuming that they agree. The zero-based $a(k)$ is the source's $a_{k+1}$.
-- source:
--   Neil Krishnan, Elchanan Mossel, STOC 2027 submission #1645 (October 2026), Theorem 1.1 p. 2, Lemma 2.1 p. 3 and Lemma 2.2 p. 4. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1645.pdf

import Definitions.Def_ReLUBinaryDepth_ProductTradeoff_Network

namespace ReLUBinaryDepth.ProductTradeoff

noncomputable section

def Admissible {n : ℕ} (B : ℝ) (θ : Fin n → Bool → ℝ) : Prop :=
  1 < B ∧ ∀ i b, 0 ≤ θ i b ∧ θ i b ≤ B

def productMap {n : ℕ} (θ : Fin n → Bool → ℝ) (x : Cube n) : ℝ :=
  ∏ i, θ i (x i)

def selector (θ : Bool → ℝ) (M : ℝ) (x : Bool) (a : ℝ) : ℝ :=
  relu (a * θ false - M * bit x) + relu (a * θ true - M * (1 - bit x))

/-- Zero-based a(0) is the source's a₁. After n stages the extension stays constant. -/
def accumulator {n : ℕ} (B : ℝ) (θ : Fin n → Bool → ℝ) (x : Cube n) : ℕ → ℝ
  | 0 => 1
  | k + 1 => if h : k < n then
      selector (θ ⟨k, h⟩) (B ^ n) (x ⟨k, h⟩) (accumulator B θ x k)
    else accumulator B θ x k

end
end ReLUBinaryDepth.ProductTradeoff


