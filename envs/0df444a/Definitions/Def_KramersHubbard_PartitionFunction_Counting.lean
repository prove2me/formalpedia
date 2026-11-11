-- Prove2me | Definitions.Def_KramersHubbard_PartitionFunction_Counting
-- name    : KramersHubbard_PartitionFunction_Counting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:05:48.118233+00:00
-- url     : https://prove2.me/theorems/907eb0e8-30ee-4cfb-ba73-0ef5a6e5263d
-- title:
--   Interaction-strength schedule and inverse product estimator
-- statement:
--   Let
--
--   $$W(t)=\sum_{X\subseteq K}t^{|X|}\det G[X],\qquad\mu_t(X)=t^{|X|}\det G[X]/W(t).$$
--
--   Start at $t_0=0$ and $t_1=(1+\beta\sum_iU_i)^{-1}$, and multiply successive positive strengths by $1+1/|K|$, capping at $1$. The stage count is computed using the ceiling of the corresponding logarithmic ratio; if $K$ is empty there is one positive stage. Given $k$ stages and tolerance $\varepsilon$, use $n=\lceil64ek/\varepsilon^2\rceil$ independent samples at each stage and set
--
--   $$\widehat\theta_i=\frac1n\sum_j(t_{i-1}/t_i)^{|X_{ij}|},\qquad\widehat W=(\prod_i\widehat\theta_i)^{-1}.$$
--
--   A zero product declares failure and returns $0$. The probability of a complete sample array is the product of its sample probabilities over every stage and sample. The convention $0^0=1$ preserves the empty configuration.
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Ojas Parekh, Andrew Zhao, STOC 2027 submission #1325 (October 2026), Efficient classical simulation of Fermi-Hubbard models with Kramers symmetry, Eqs.(34)-(35), (61)-(65), pp.15-16,30-31; printed page = 1-based PDF page. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1325.pdf; PDF SHA-256 e3fd3fa7390d8ff9f0f1e2ee07e6ebc5b8d7304e26be9e76959d9587f4564eae. Canonical submitted artifact, citation_basis: published; title-page date November 3, 2026; no assertion of conference acceptance.

import Definitions.Def_KramersHubbard_PartitionFunction_Green

noncomputable section
open scoped BigOperators

namespace KramersHubbard.PartitionFunction

/-- Eq.(34). The empty minor contributes 1, including at t=0. -/
def countingW {N r M : ℕ} (D : Data N r) (β t : ℝ) : ℂ :=
  ∑ X : Finset (Insertion M r), (t : ℂ)^X.card * blockDet (green D β) X X

def countingLaw {N r M : ℕ} (D : Data N r) (β t : ℝ) (X : Finset (Insertion M r)) : ℂ :=
  (t : ℂ)^X.card * blockDet (green D β) X X / countingW (M := M) D β t

/-- Actual number of positive-strength stages: the first strength, then capped
    geometric steps. With no insertions or zero total coupling, one stage suffices. -/
def stageCount {N r} (D : Data N r) (β : ℝ) (M : ℕ) : ℕ :=
  if M * (2*r) = 0 then 1 else
    1 + Nat.ceil (Real.log (1 + β * ∑ i, D.U i) /
      Real.log (1 + 1 / ((M * (2*r) : ℕ) : ℝ)))

def strength {N r} (D : Data N r) (β : ℝ) (M j : ℕ) : ℝ :=
  if j = 0 then 0 else
    min 1 ((1 + β * ∑ i, D.U i)⁻¹ *
      (1 + 1 / ((M * (2*r) : ℕ) : ℝ)) ^ (j-1))

def sampleCount (k : ℕ) (eps : ℝ) : ℕ := Nat.ceil (64 * Real.exp 1 * k / eps^2)

/-- Inverse of the product of the actual empirical means. Zero product is a
    declared failure with output 0, not a successful reciprocal. -/
def productEstimate {p k n} (t : ℕ → ℝ)
    (xs : Fin k → Fin n → Finset (Fin p)) : ℝ :=
  let a := ∏ i : Fin k, (∑ j : Fin n, (t i.val / t (i.val+1)) ^ (xs i j).card) / n
  if a = 0 then 0 else a⁻¹

/-- Product law over the entire array: stages as well as samples are independent. -/
def arrayProbability {p k n} (nu : Fin k → Finset (Fin p) → ℝ)
    (xs : Fin k → Fin n → Finset (Fin p)) : ℝ :=
  ∏ i, ∏ j, nu i (xs i j)

end KramersHubbard.PartitionFunction


