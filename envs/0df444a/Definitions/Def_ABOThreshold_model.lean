-- Prove2me | Definitions.Def_ABOThreshold_model
-- name    : ABOThreshold_model
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-21T11:22:27.705693+00:00
-- url     : https://prove2.me/theorems/4df34e0d-c328-46ed-b506-e70645ba0972
-- title:
--   Rectangles, $(r,k)$-sparse fault patterns and the fault-tolerance thresholds
-- statement:
--   This file sets up the combinatorial model underlying the recursive fault analysis of Aharonov and Ben-Or.
--
--   **Rectangles and fault patterns.** Fix a branching number $A$, the number of locations of a rectangle. A $0$-rectangle is a single location of the circuit and an $(r+1)$-rectangle is composed of $A$ many $r$-rectangles, so an $r$-rectangle has $A^{r}$ locations. A *fault pattern* of an $r$-rectangle, written $\mathrm{FaultPattern}(A,r)$, records for each of its locations whether a fault occurred: at level $0$ it is a single boolean, and at level $r+1$ it is an $A$-tuple of fault patterns of level $r$. Every level is a finite type with decidable equality.
--
--   **Sparseness (Definition 18).** Fix also $k$, the number of faulty sub-rectangles a rectangle tolerates (in the paper $k=\lfloor d/l\rfloor$ for a code correcting $d$ errors with spread $l$). A fault pattern is $(0,k)$-*sparse* when the single location carries no fault, and $(r+1,k)$-*sparse* when at most $k$ of its $A$ constituent $r$-rectangles carry a pattern that is not $(r,k)$-sparse.
--
--   **Independent noise.** Under probabilistic noise of rate $\eta$ each location is faulty with probability $\eta$, independently of all others. The weight of a fault pattern is accordingly the product, over all $A^{r}$ locations, of $\eta$ at faulty locations and $1-\eta$ at clean ones, and
--
--   $$P(r) \;=\; \sum_{p \text{ } (r,k)\text{-sparse}} \mathrm{weight}(p), \qquad Q(r) \;=\; 1 - P(r)$$
--
--   are the probability that the faults of an $r$-rectangle form an $(r,k)$-sparse set and the probability that they do not.
--
--   **Thresholds.** With $A$ the maximal number of locations in a rectangle, the threshold condition for probabilistic noise (Definition 19) is
--
--   $$\binom{A}{k+1}\eta^{k+1} < \eta,$$
--
--   and the threshold condition for general noise (Definition 21) is
--
--   $$e\binom{A}{k+1}(2\eta)^{k+1} < 2\eta .$$
--
--   The associated thresholds are $\eta_c = \binom{A}{k+1}^{-1/k}$ and $\eta_c' = \tfrac12\bigl(e\binom{A}{k+1}\bigr)^{-1/k}$.
--
--   This bundle is the vocabulary in which the milestones and the goal of this mission are stated; it mentions no quantum mechanics, so it is reusable for any concatenated fault-tolerance analysis.
--
--   **Formalization Note** The paper prints the two thresholds with exponent $-k$ (equations 7.4 and 8.6). That exponent is inconsistent with the paper's own threshold conditions 7.3 and 8.5: solving $\binom{A}{k+1}\eta^{k+1}<\eta$ gives $\eta<\binom{A}{k+1}^{-1/k}$. The exponent $-1/k$ is therefore used here, which is the reading under which the paper's assertion that every $\eta<\eta_c$ satisfies the threshold condition is correct. Sparseness is formalized as a boolean-valued decidable predicate, and the weight and probability functions are ordinary real-valued finite sums and products, so no constraint such as $0\le\eta\le1$ is built into the definitions; each theorem states the range hypotheses it needs.
-- source:
--   Dorit Aharonov and Michael Ben-Or, Fault-Tolerant Quantum Computation With Constant Error Rate, arXiv:quant-ph/9906129v1, https://arxiv.org/abs/quant-ph/9906129, pp. 49-54, Definitions 18, 19, 20, 21, 22 (eqs. 7.3, 7.4, 8.5, 8.6)

import Mathlib

set_option autoImplicit false

namespace ABOThreshold

/-- `FaultPattern A r` is the set of fault patterns of an `r`-rectangle in which every
`(s+1)`-rectangle is composed of exactly `A` `s`-rectangles. A `0`-rectangle is a single
location, and a fault pattern there is a boolean recording whether a fault occurred. -/
def FaultPattern (A : ℕ) : ℕ → Type
  | 0 => Bool
  | r + 1 => Fin A → FaultPattern A r

instance instDecidableEqFaultPattern (A : ℕ) : (r : ℕ) → DecidableEq (FaultPattern A r)
  | 0 => inferInstanceAs (DecidableEq Bool)
  | r + 1 =>
      letI := instDecidableEqFaultPattern A r
      inferInstanceAs (DecidableEq (Fin A → FaultPattern A r))

instance instFintypeFaultPattern (A : ℕ) : (r : ℕ) → Fintype (FaultPattern A r)
  | 0 => inferInstanceAs (Fintype Bool)
  | r + 1 =>
      letI := instFintypeFaultPattern A r
      letI := instDecidableEqFaultPattern A r
      inferInstanceAs (Fintype (Fin A → FaultPattern A r))

/-- `IsSparse A k r p` is Aharonov–Ben-Or's `(r, k)`-sparseness of the set of faulty locations
`p` inside an `r`-rectangle: a `(0, k)`-sparse set is empty (no fault at the location), and a set
is `(r+1, k)`-sparse when at most `k` of the `A` constituent `r`-rectangles carry a set of faults
that fails to be `(r, k)`-sparse. -/
def IsSparse (A k : ℕ) : (r : ℕ) → FaultPattern A r → Bool
  | 0, b => !b
  | r + 1, p =>
      decide ((Finset.univ.filter fun i : Fin A => IsSparse A k r (p i) = false).card ≤ k)

/-- The probability weight of a single fault pattern when every location independently suffers a
fault with probability `η`. -/
def weight (A : ℕ) (η : ℝ) : (r : ℕ) → FaultPattern A r → ℝ
  | 0, b => cond (b : Bool) η (1 - η)
  | r + 1, p => ∏ i : Fin A, weight A η r (p i)

/-- `sparseProb A k η r` is the probability that the faults of an `r`-rectangle form an
`(r, k)`-sparse set, under independent probabilistic noise of rate `η`. -/
noncomputable def sparseProb (A k : ℕ) (η : ℝ) (r : ℕ) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (FaultPattern A r)).filter fun p => IsSparse A k r p,
    weight A η r p

/-- `badProb A k η r = 1 - sparseProb A k η r` is the probability that the faults of an
`r`-rectangle fail to be `(r, k)`-sparse. -/
noncomputable def badProb (A k : ℕ) (η : ℝ) (r : ℕ) : ℝ := 1 - sparseProb A k η r

/-- The threshold condition of Definition 19: `C(A, k+1) * η^(k+1) < η`. -/
def ThresholdCondition (A k : ℕ) (η : ℝ) : Prop :=
  (A.choose (k + 1) : ℝ) * η ^ (k + 1) < η

/-- The probabilistic-noise threshold `η_c` of Definition 20. -/
noncomputable def thresholdProb (A k : ℕ) : ℝ :=
  ((A.choose (k + 1) : ℝ)) ^ (-(1 : ℝ) / (k : ℝ))

/-- The threshold condition for general noise, Definition 21: `e * C(A, k+1) * (2η)^(k+1) < 2η`. -/
def ThresholdConditionGeneral (A k : ℕ) (η : ℝ) : Prop :=
  Real.exp 1 * (A.choose (k + 1) : ℝ) * (2 * η) ^ (k + 1) < 2 * η

/-- The general-noise threshold `η_c'` of Definition 22. -/
noncomputable def thresholdGeneral (A k : ℕ) : ℝ :=
  (1 / 2 : ℝ) * (Real.exp 1 * (A.choose (k + 1) : ℝ)) ^ (-(1 : ℝ) / (k : ℝ))

end ABOThreshold


