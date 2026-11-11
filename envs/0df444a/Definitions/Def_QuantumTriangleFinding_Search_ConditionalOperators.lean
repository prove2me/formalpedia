-- Prove2me | Definitions.Def_QuantumTriangleFinding_Search_ConditionalOperators
-- name    : QuantumTriangleFinding_Search_ConditionalOperators
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:25:22.249058+00:00
-- url     : https://prove2.me/theorems/19dd70fb-03eb-4311-9a01-f8a5c61447e5
-- title:
--   Conditional resampling and forbidden Boolean patterns
-- statement:
--   For a finite Boolean coordinate set $I$ and a law $\rho$, fix every coordinate except $i$. Let $E_{\rho,i}$ average $f^x$ over that conditional fiber, and let $D_{\rho,i}=I-E_{\rho,i}$. Explicitly,
--   $$ (E_{\rho,i}f)^x=\sum_{y:y_{I\setminus\{i\}}=x_{I\setminus\{i\}}}\frac{\rho(y)}{\sum_{z:z_{I\setminus\{i\}}=x_{I\setminus\{i\}}}\rho(z)}f^y.$$
--   Only support points occur, so each denominator includes the positive mass of $x$. A forced coordinate has a singleton fiber, hence $E_i=I$ and $D_i=0$. Weighted and block sums of the $D_i$ define the generators used in the resolvents.
--
--   For a finite family $\mathcal F$ of nonempty forbidden subsets, let $\Omega$ exclude every all-ones pattern in $\mathcal F$, and put $\mu=\nu_p(\cdot\mid\Omega)$. The family itself may be empty. Define $A_{ij}(x)$ to indicate that a forbidden subset contains $i,j$ and has all its other coordinates present. The diagonal operator multiplies by $A_{ij}(x)$; $N_{i,B}(x)=\sum_{j\in B\setminus\{i\}}A_{ij}(x)$ counts interactions in a block.
--
--   Outside-coordinate preservation means that a kernel never connects different outside assignments. An outside-$B$ event is constant on every such fiber. These are separate notions from an event depending on the full input. No independence of conditioned coordinates is imposed.
-- source:
--   Arjan Cornelissen, Amin Shiraz Gilani, Xingyu Zhou, STOC 2027 submission #1375 (October 2026), (3.4), p. 15; (4.5), pp. 17–18; §4.3, (4.11), (4.16), p. 19; Lemma 4.5, p. 22

import Definitions.Def_QuantumTriangleFinding_Search_FiniteProbability

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace QuantumTriangleFinding.Search

/-- Equation (3.4): the fiber fixes every coordinate other than i. -/
def SameOutside {I : Type} (B : Finset I) (x y : I → Bool) : Prop :=
  ∀ j, j ∉ B → x j = y j

def fiberMass {I : Type} [Fintype I] (ρ : (I → Bool) → ℝ) (i : I) (x : I → Bool) : ℝ := by
  classical
  exact ∑ y, if ∀ j, j ≠ i → y j = x j then ρ y else 0

def conditionalAverage {I : Type} [Fintype I] (ρ : (I → Bool) → ℝ) (i : I) :
    Matrix (Support ρ) (Support ρ) ℂ := by
  classical
  exact fun x y => if ∀ j, j ≠ i → y.val j = x.val j then
    (ρ y.val / fiberMass ρ i x.val : ℝ) else 0

def conditionalDifference {I : Type} [Fintype I] (ρ : (I → Bool) → ℝ) (i : I) :
    Matrix (Support ρ) (Support ρ) ℂ := 1 - conditionalAverage ρ i

/-- Equation (4.5); weights are nonnegative in each theorem that uses this operator. -/
def weightedDifferences {I : Type} [Fintype I] (ρ : (I → Bool) → ℝ) (w : I → ℝ) :
    Matrix (Support ρ) (Support ρ) ℂ := ∑ i, (w i : ℂ) • conditionalDifference ρ i

def blockDifferences {I : Type} [Fintype I] (ρ : (I → Bool) → ℝ) (B : Finset I) :
    Matrix (Support ρ) (Support ρ) ℂ := ∑ i ∈ B, conditionalDifference ρ i

/-- Equation (4.11): the family may be empty; each member is nonempty in the theorems. -/
def allowed {I : Type} (ℱ : Finset (Finset I)) : Set (I → Bool) :=
  {x | ∀ C ∈ ℱ, ¬ ∀ i ∈ C, x i = true}

def conditionedBernoulli {I : Type} [Fintype I] (p : ℝ) (ℱ : Finset (Finset I)) :
    (I → Bool) → ℝ := condition (bernoulli p) (allowed ℱ)

/-- Equation (4.16). This depends only on coordinates outside i,j. -/
def interaction {I : Type} (ℱ : Finset (Finset I)) (i j : I) (x : I → Bool) : ℝ := by
  classical
  exact if ∃ C ∈ ℱ, i ∈ C ∧ j ∈ C ∧ ∀ k ∈ C, k ≠ i → k ≠ j → x k = true then 1 else 0

def interactionOperator {I : Type} [Fintype I] (ρ : (I → Bool) → ℝ)
    (ℱ : Finset (Finset I)) (i j : I) : Matrix (Support ρ) (Support ρ) ℂ :=
  Matrix.diagonal fun x => (interaction ℱ i j x.val : ℂ)

def interactionCount {I : Type} (ℱ : Finset (Finset I)) (B : Finset I) (i : I)
    (x : I → Bool) : ℝ := by
  classical
  exact ∑ j ∈ B.erase i, interaction ℱ i j x

/-- A kernel preserves outside coordinates when all entries joining different fibers vanish. -/
def PreservesOutside {I : Type} [Fintype I] (ρ : (I → Bool) → ℝ) (B : Finset I)
    (A : Matrix (Support ρ) (Support ρ) ℂ) : Prop :=
  ∀ x y, ¬ SameOutside B x.val y.val → A x y = 0

def OutsideEvent {I : Type} (B : Finset I) (G : Set (I → Bool)) : Prop :=
  ∀ x y, SameOutside B x y → (x ∈ G ↔ y ∈ G)

end QuantumTriangleFinding.Search


