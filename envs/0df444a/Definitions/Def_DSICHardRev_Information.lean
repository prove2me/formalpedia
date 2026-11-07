-- Prove2me | Definitions.Def_DSICHardRev_Information
-- name    : DSICHardRev_Information
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:33:50.625416+00:00
-- url     : https://prove2.me/theorems/e0007f48-2fe0-41f5-a801-319fe19af037
-- title:
--   Total variation, conditional entropy and conditional mutual information of finite random variables
-- statement:
--   Let $(\Omega,P)$ be a finite probability space and let $X,Y,Z$ be random variables with finite ranges. Logarithms are binary.
--
--   1. **Total variation.** For distributions $D,D'$ on a finite set $\mathcal X$,
--   $$\mathrm{TV}(D,D')=\max_{E\subseteq\mathcal X}\Big|\sum_{x\in E}\big(D(x)-D'(x)\big)\Big|.$$
--   2. **Conditional law.** $\mathrm{Law}(X\mid Y=y)$ is $x\mapsto \Pr[X=x,Y=y]/\Pr[Y=y]$.
--   3. **Conditional entropy.**
--   $$\mathbb H(X\mid Y)=-\sum_{y}\sum_{x}\Pr[X=x,Y=y]\,\log\Pr[X=x\mid Y=y].$$
--   4. **Conditional mutual information.** $\mathbb I(X;Y\mid Z)=\mathbb H(X\mid Z)-\mathbb H(X\mid Y,Z)$.
--   5. **Expectation of a function of $Y$.** $\mathbb E[g(Y)]=\sum_y\Pr[Y=y]\,g(y)$.
--
--   These quantities carry the information-theoretic part of the simultaneous communication lower bound.
--
--   **Formalization Note** The probability space is a vector of non-negative real weights summing to one on a finite type; since every quantity depends only on the joint law, this is the same as discrete random variables with finite ranges on any probability space. A term with $\Pr[X=x,Y=y]=0$ contributes $0$ to the entropy.
-- source:
--   Qiu, The Hardness of Dominant Strategy Mechanism Design, Revisited, arXiv:2610.06773 (version of 27 Oct 2026, sha256 a9f98f35…), §2.5, pp.10–11: Definitions 2.21, 2.22, 2.23, 2.25 (log is binary, p.10)

import Mathlib

namespace DSICHardRev

/-!
# Finite information theory: total variation, conditional entropy, conditional mutual information

F. V. Qiu, *The Hardness of Dominant Strategy Mechanism Design, Revisited*, arXiv:2610.06773
(version of 27 Oct 2026, sha256 a9f98f35…), §2.5, pp.10–11: Definition 2.21 (Total Variation
Distance), Definition 2.22 (Entropy), Definition 2.23 (Mutual Information), Definition 2.25
(`Law(X | Y = y)`); "We use log to denote the binary logarithm" (p.10).

**Formalization Note.**
* Random variables are maps `X : Ω → α` on a finite sample space `Ω` carrying a probability vector
  `P : FinProb Ω` (non-negative real weights summing to `1`); every range type is finite. All the
  quantities below depend only on the joint law, so this is the same as discrete random variables
  with finite ranges on an arbitrary probability space.
* `prob P A` is the probability of the event `A`; `condLaw P X Y y` is `Law(X | Y = y)`, the
  function `x ↦ Pr[X = x, Y = y] / Pr[Y = y]`.
* `condEntropy P X Y = − ∑_y ∑_x Pr[X = x, Y = y] · log₂ (Pr[X = x, Y = y] / Pr[Y = y])`
  (Definition 2.22); a term with `Pr[X = x, Y = y] = 0` is `0` (the factor in front vanishes).
* `mutualInfo P X Y Z = ℍ(X | Z) − ℍ(X | (Y, Z))` (Definition 2.23, first expression).
* `tv p q = max_{E ⊆ X} |∑_{x ∈ E} (p x − q x)|` (Definition 2.21), a maximum over the finite
  powerset.
* `expectOver P Y g = ∑_y Pr[Y = y] · g y`, the expectation of `g(Y)`; values `y` of probability `0`
  carry weight `0`.
-/

/-- A probability vector on a finite type: non-negative real weights summing to one. -/
structure FinProb (Ω : Type) [Fintype Ω] where
  /-- The weight of each outcome. -/
  p : Ω → ℝ
  /-- Weights are non-negative. -/
  nonneg : ∀ ω, 0 ≤ p ω
  /-- Weights sum to one. -/
  sum_eq_one : ∑ ω, p ω = 1

namespace FinProb

variable {Ω α β γ : Type} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ]

open Classical in
/-- The probability `Pr[A]` of an event `A ⊆ Ω`. -/
noncomputable def prob (P : FinProb Ω) (A : Ω → Prop) : ℝ :=
  ∑ ω, if A ω then P.p ω else 0

/-- `Law(X | Y = y)` (Definition 2.25): `x ↦ Pr[X = x, Y = y] / Pr[Y = y]`. -/
noncomputable def condLaw (P : FinProb Ω) (X : Ω → α) (Y : Ω → β) (y : β) : α → ℝ :=
  fun x => P.prob (fun ω => X ω = x ∧ Y ω = y) / P.prob (fun ω => Y ω = y)

/-- Conditional entropy in bits (Definition 2.22):
`ℍ(X | Y) = − ∑_y ∑_x Pr[X = x, Y = y] log₂ Pr[X = x | Y = y]`. -/
noncomputable def condEntropy (P : FinProb Ω) (X : Ω → α) (Y : Ω → β) : ℝ :=
  -∑ y, ∑ x, P.prob (fun ω => X ω = x ∧ Y ω = y) *
    Real.logb 2 (P.prob (fun ω => X ω = x ∧ Y ω = y) / P.prob (fun ω => Y ω = y))

/-- Conditional mutual information in bits (Definition 2.23):
`𝕀(X ; Y | Z) = ℍ(X | Z) − ℍ(X | Y, Z)`. -/
noncomputable def mutualInfo (P : FinProb Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) : ℝ :=
  P.condEntropy X Z - P.condEntropy X (fun ω => (Y ω, Z ω))

/-- The expectation `E[g(Y)] = ∑_y Pr[Y = y] g(y)`. -/
noncomputable def expectOver (P : FinProb Ω) (Y : Ω → β) (g : β → ℝ) : ℝ :=
  ∑ y, P.prob (fun ω => Y ω = y) * g y

end FinProb

/-- Total variation distance of two distributions on a finite set (Definition 2.21):
`TV(D, D') = max_{E ⊆ X} |∑_{x ∈ E} (D(x) − D'(x))|`. -/
def tv {α : Type} [Fintype α] (p q : α → ℝ) : ℝ :=
  (Finset.univ : Finset (Finset α)).sup' Finset.univ_nonempty fun E => |∑ x ∈ E, (p x - q x)|

end DSICHardRev


