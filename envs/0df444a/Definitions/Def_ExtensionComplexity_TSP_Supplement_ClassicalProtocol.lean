-- Prove2me | Definitions.Def_ExtensionComplexity_TSP_Supplement_ClassicalProtocol
-- name    : ExtensionComplexity_TSP_Supplement_ClassicalProtocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:35:55.978488+00:00
-- url     : https://prove2.me/theorems/3233fef3-09ac-4b08-8099-a8cc6f88e667
-- title:
--   Classical private-coin randomized protocols computing matrices in expectation (§4.4; cited model)
-- statement:
--   Let $I$ and $J$ be Alice's and Bob's input sets. A classical randomized protocol with nonnegative outputs is a finite binary protocol tree. At an internal node one party sends one bit: Alice sends $1$ with probability $p(i)\in[0,1]$ on input $i$, or Bob sends $1$ with probability $q(j)\in[0,1]$ on input $j$; the node's position records the transcript so far, and each party's randomness is private. At a leaf one party outputs a nonnegative real number $f(i)\ge0$ (Alice) or $g(j)\ge0$ (Bob) depending on its own input and the transcript. The expected output $\mathbb E_P(i,j)$ is defined recursively,
--
--   $$
--   \mathbb E_{\text{send}(p;P_0,P_1)}(i,j)=(1-p(i))\,\mathbb E_{P_0}(i,j)+p(i)\,\mathbb E_{P_1}(i,j),
--   $$
--
--   and the protocol computes a real matrix $M$ in expectation when $\mathbb E_P(i,j)=M_{ij}$ for all $i,j$. Its cost is the number of bits on the longest transcript (the depth of the tree).
--
--   The paper does not define this model; it cites Faenza et al. (2011) for randomized protocols with nonnegative outputs computing a matrix in expectation (p. 17:4), and its proof of Theorem 18 (p. 17:19) uses private randomness ("all inputs $a$ for which Alice has positive probability of sending $m$"). Private random strings reused across rounds give exactly these transcript-conditional sending probabilities, and a randomized leaf output can be replaced by its conditional expectation, which is again a nonnegative function of the outputting party's input. Multi-round protocols and either party outputting are allowed, so one-way protocols are a special case.
-- source:
--   Fiorini, Massar, Pokutta, Tiwary, de Wolf, Exponential lower bounds for polytopes in combinatorial optimization, J. ACM 62(2) (2015), Art. 17, DOI 10.1145/2716307, p. 17:4 (model cited from Faenza et al. 2011) and p. 17:19, §4.4, Theorem 18 and its proof

import Mathlib

namespace ExtensionComplexity.TSP.Supplement

/-- A classical randomized communication protocol with private coins and nonnegative outputs,
the model of Faenza et al. [2011] that §1 (p. 17:4) and §4.4 (p. 17:19) cite. It is a binary
protocol tree. At an internal node one party sends one bit: Alice sends `1` with probability
`p i` on input `i` (Bob likewise with `q j` on input `j`), so the node's position encodes the
transcript so far. At a leaf one party outputs a nonnegative real depending on its own input
and the transcript (a randomized output is replaced by its conditional expectation, which is
again a nonnegative function of that party's input). Private random strings shared across
rounds give exactly these transcript-conditional probabilities. -/
inductive ClassicalProtocol (ι κ : Type*)
  | aliceOutputs (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
  | bobOutputs (g : κ → ℝ) (hg : ∀ j, 0 ≤ g j)
  | aliceSends (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
      (onZero onOne : ClassicalProtocol ι κ)
  | bobSends (q : κ → ℝ) (hq : ∀ j, 0 ≤ q j ∧ q j ≤ 1)
      (onZero onOne : ClassicalProtocol ι κ)

namespace ClassicalProtocol

variable {ι κ : Type*}

/-- Communication cost: the number of bits exchanged on the longest transcript (tree depth). -/
def cost : ClassicalProtocol ι κ → ℕ
  | aliceOutputs _ _ => 0
  | bobOutputs _ _ => 0
  | aliceSends _ _ c₀ c₁ => max (cost c₀) (cost c₁) + 1
  | bobSends _ _ c₀ c₁ => max (cost c₀) (cost c₁) + 1

/-- Expected output on inputs `i` (Alice) and `j` (Bob). -/
noncomputable def expectedOutput : ClassicalProtocol ι κ → ι → κ → ℝ
  | aliceOutputs f _, i, _ => f i
  | bobOutputs g _, _, j => g j
  | aliceSends p _ c₀ c₁, i, j => (1 - p i) * expectedOutput c₀ i j + p i * expectedOutput c₁ i j
  | bobSends q _ c₀ c₁, i, j => (1 - q j) * expectedOutput c₀ i j + q j * expectedOutput c₁ i j

/-- The protocol computes `M` in expectation: the expected output on `(i, j)` is `M i j`. -/
def Computes (P : ClassicalProtocol ι κ) (M : Matrix ι κ ℝ) : Prop :=
  ∀ i j, P.expectedOutput i j = M i j

end ClassicalProtocol

end ExtensionComplexity.TSP.Supplement


