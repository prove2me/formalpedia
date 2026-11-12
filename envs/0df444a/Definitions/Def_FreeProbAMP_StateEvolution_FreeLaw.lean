-- Prove2me | Definitions.Def_FreeProbAMP_StateEvolution_FreeLaw
-- name    : FreeProbAMP_StateEvolution_FreeLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:24:57.294204+00:00
-- url     : https://prove2.me/theorems/4041c783-6204-432e-ba20-d6addb86cc9d
-- title:
--   Faithful tracial C*-probability, joint semicircularity and strong convergence
-- statement:
--   Let $\mathcal N$ be a genuine unital complex C*-algebra. A faithful tracial state $\tau$ is a continuous complex-linear functional, normalized by $\tau(1)=1$, tracial, positive on $a^*a$, and faithful: $\tau(a^*a)=0$ implies $a=0$.
--
--   A self-adjoint family $(S_i)$ is jointly centered semicircular when every mixed moment satisfies the noncrossing-pairing formula
--
--   $$\tau(S_{i_1}\cdots S_{i_m})=\sum_{\pi\in NC_2(m)}\prod_{\{r,s\}\in\pi}\tau(S_{i_r}S_{i_s}).$$
--
--   There are no pairings for odd $m$, so every odd mixed moment vanishes. Covariances may be nonzero between distinct coordinates. Noncommutative polynomials are arbitrary finite linear combinations of words with complex scalar coefficients. Strong convergence of a joint self-adjoint matrix tuple $X^d$ to $x$ requires, for every such polynomial $P$,
--
--   $$\tau_d(P(X^d))\xrightarrow{\mathbb P}\tau(P(x)),\qquad
--   \|P(X^d)\|_{\rm op}\xrightarrow{\mathbb P}\|P(x)\|.$$
--
--   The convergence interface covers arbitrary complex Hermitian comparison matrices as well as the real symmetric AMP matrices. Freeness of two self-adjoint families means that every nonempty alternating product of centered polynomials from the two families has trace zero. These definitions retain both moments and spectral information and are reusable for matrix limits beyond AMP.
--
--   **Formalization Note** The dimension index $d\ge0$ represents physical dimension $d+1$. Pairings are fixed-point-free involutive permutations with no crossing chords. No finite matrix algebra or covariance-only law substitutes for the C*-probability space.
-- source:
--   August Chen, Ahmed El Alaoui, STOC 2027 submission #1182 (October 2026), p. 4, (2.3) and Definition 2.7; p. 29, Proposition 6.2

import Mathlib
import Definitions.Def_FreeProbAMP_StateEvolution_Matrices

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section

namespace FreeProbAMP.StateEvolution
attribute [local instance] Classical.propDecidable

/-- A normalized positive faithful trace on a genuine unital C*-algebra. -/
structure FaithfulTrace (B : Type*) [CStarAlgebra B] where
  value : B →L[ℂ] ℂ
  unit : value 1 = 1
  tracial : ∀ a b, value (a*b) = value (b*a)
  positive : ∀ a, 0 ≤ (value (star a*a)).re ∧ (value (star a*a)).im = 0
  faithful : ∀ a, value (star a*a) = 0 → a = 0

/-- Noncrossing pairings are fixed-point-free involutions without crossing chords. -/
def IsNCPairing {m : ℕ} (π : Equiv.Perm (Fin m)) : Prop :=
  (∀ i, π (π i) = i ∧ π i ≠ i) ∧
  ¬ ∃ i j : Fin m, i < j ∧ j < π i ∧ π i < π j

/-- Wick's formula for the whole joint semicircular law, including all odd moments. -/
def JointSemicircular {ι B : Type*} [CStarAlgebra B] (τ : FaithfulTrace B)
    (S : ι → B) : Prop :=
  (∀ i, star (S i) = S i) ∧ ∀ (m : ℕ) (w : Fin m → ι),
    τ.value ((List.ofFn (fun j => S (w j))).prod) =
      ∑ π : Equiv.Perm (Fin m), if IsNCPairing π then
        ∏ j ∈ Finset.univ.filter (fun j => j < π j), τ.value (S (w j)*S (w (π j))) else 0

/-- Finite words with scalar complex coefficients: the full noncommutative polynomial algebra. -/
abbrev NCPolynomial (ι : Type*) := List ι →₀ ℂ

def evalNC {ι B : Type*} [Ring B] [Algebra ℂ B] (P : NCPolynomial ι) (X : ι → B) : B :=
  P.sum (fun w c => c • (w.map X).prod)

variable {Ω B : Type*} [MeasurableSpace Ω] [CStarAlgebra B]

/-- Definition 2.7 for arbitrary Hermitian matrices, including the comparison array
of Proposition 6.2. Real AMP matrices use `Strong` below. -/
def StrongComplex {ι : Type*} (μ : Measure Ω) (τ : FaithfulTrace B)
    (X : (d : ℕ) → Ω → ι → CMat (d+1)) (x : ι → B) : Prop :=
  (∀ i, star (x i) = x i) ∧
  (∀ d i, Measurable (fun ω => X d ω i) ∧ ∀ᵐ ω ∂μ, (X d ω i).conjTranspose = X d ω i) ∧
  ∀ P : NCPolynomial ι,
    InProb μ (fun d ω => ‖ctraceN (evalNC P (X d ω)) - τ.value (evalNC P x)‖) 0 ∧
    InProb μ (fun d ω => copNorm (evalNC P (X d ω))) ‖evalNC P x‖

/-- Definition 2.7. The two tests are joint and cover every noncommutative polynomial. -/
def Strong {ι : Type*} (μ : Measure Ω) (τ : FaithfulTrace B)
    (X : (d : ℕ) → Ω → ι → RMat (d+1)) (x : ι → B) : Prop :=
  (∀ i, star (x i) = x i) ∧
  (∀ d i, Measurable (fun ω => X d ω i) ∧ ∀ᵐ ω ∂μ, (X d ω i).transpose = X d ω i) ∧
  ∀ P : NCPolynomial ι,
    InProb μ (fun d ω => ‖ctraceN (evalNC P (fun i => complexify (X d ω i))) -
        τ.value (evalNC P x)‖) 0 ∧
    InProb μ (fun d ω => copNorm (evalNC P (fun i => complexify (X d ω i)))) ‖evalNC P x‖

/-- Algebraic freeness of two families, formulated on all centered polynomials in each family. -/
def FreeFamilies {ι κ : Type*} (τ : FaithfulTrace B) (x : ι → B) (y : κ → B) : Prop :=
  ∀ (m : ℕ) (side : Fin m → Bool) (z : Fin m → B),
    (∀ j : Fin m, τ.value (z j) = 0 ∧
      if side j then ∃ P : NCPolynomial ι, z j = evalNC P x
      else ∃ P : NCPolynomial κ, z j = evalNC P y) →
    (∀ i j : Fin m, i.val+1 = j.val → side i ≠ side j) →
    0 < m → τ.value ((List.ofFn z).prod) = 0

end FreeProbAMP.StateEvolution


