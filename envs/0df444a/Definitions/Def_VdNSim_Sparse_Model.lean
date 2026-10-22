-- Prove2me | Definitions.Def_VdNSim_Sparse_Model
-- name    : VdNSim_Sparse_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:31:15.544041+00:00
-- url     : https://prove2.me/theorems/e0f81720-2093-4b49-975f-99d726d37a88
-- title:
--   Sparse operator column data and the sampling estimator, pp. 10–13
-- statement:
--   For a finite computational basis $X$, a state is represented by its complex coefficients $\psi_x$, and its Born probability is $p_x=|\psi_x|^2$. An operator $A$ is **$s$-sparse** when every row and column has at most $s$ nonzero entries. **Column data** $(\alpha_i,r_i)_{i=1}^s$ represent the entries in a column by
--
--   $$A_{yx}=\sum_{i:r_i(x)=y}\alpha_i(x),$$
--
--   with distinct nonzero coefficients assigned distinct rows. The model also defines the functions $F_i$ and $G_i$ of Eqs. (7)–(8), their finite expectations, the sample means formed from $K$ draws each from $p_x=|\psi_x|^2$ and $q_y=|\phi_y|^2$, and the probability that the resulting estimator differs from a target by more than $\varepsilon$.
--
--   These definitions make the paper's sampling argument a precise finite probability statement, with one pair of sample sets shared by all $i$.
--
--   **Formalization Note** The model omits the polynomial running-time parts of CT and ECS. Column data may list nonzero entries in any order, provided they are distinct. Empty sums are zero. At a zero denominator, Lean's total division returns zero; the corresponding sampling outcome has zero mass, and the active branch of $G_i$ always has a positive denominator.
-- source:
--   Van den Nest, Simulating quantum computers with probabilistic methods, arXiv:0911.1624v3, p. 10, Eq. (2); p. 12, Eqs. (5)–(8); p. 13, Eq. (9); p. 23, Appendix A

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

noncomputable section
open Classical
open scoped Matrix

namespace VdNSim.Sparse

/-- Labels of the computational basis of an n-qubit system. -/
abbrev Bits (n : ℕ) := Fin n → Bool

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Born probability of a basis outcome. -/
def prob (ψ : X → ℂ) (x : X) : ℝ := ‖ψ x‖ ^ 2

/-- Matrix element with the row as output basis label. -/
def matElem (ϕ : X → ℂ) (A : Matrix X X ℂ) (ψ : X → ℂ) : ℂ :=
  ∑ y, ∑ x, star (ϕ y) * A y x * ψ x

/-- At most s nonzero entries in each column and in each row. -/
def IsSparse (s : ℕ) (A : Matrix X X ℂ) : Prop :=
  (∀ x, (Finset.univ.filter fun y => A y x ≠ 0).card ≤ s) ∧
  (∀ y, (Finset.univ.filter fun x => A y x ≠ 0).card ≤ s)

/-- Equation (2): the nonzero column entries, with no duplicate nonzero row labels. -/
structure ColumnData (A : Matrix X X ℂ) (s : ℕ) where
  α : Fin s → X → ℂ
  r : Fin s → X → X
  eq2 : ∀ x y, A y x = ∑ i ∈ Finset.univ.filter (fun i => r i x = y), α i x
  inj : ∀ x (i j : Fin s), α i x ≠ 0 → α j x ≠ 0 → r i x = r j x → i = j

variable {A : Matrix X X ℂ} {s : ℕ}

/-- Equation (7), with delta_i(x)=1 exactly when p_x >= q_(r_i(x)). -/
def F (ψ ϕ : X → ℂ) (D : ColumnData A s) (i : Fin s) (x : X) : ℂ :=
  if prob ϕ (D.r i x) ≤ prob ψ x then
    star (ϕ (D.r i x)) * ψ x / (prob ψ x : ℂ) * D.α i x else 0

/-- Equation (8), where epsilon_i is complementary to delta_i. -/
def G (ψ ϕ : X → ℂ) (D : ColumnData A s) (i : Fin s) (y : X) : ℂ :=
  ∑ x ∈ Finset.univ.filter (fun x => D.r i x = y ∧ D.α i x ≠ 0),
    if prob ψ x < prob ϕ y then
      star (ϕ y) * ψ x / (prob ϕ y : ℂ) * D.α i x else 0

/-- Finite expectation under a probability mass function. -/
def expect (p : X → ℝ) (f : X → ℂ) : ℂ := ∑ x, (p x : ℂ) * f x

/-- Probability of an event among K independent draws from a finite law. -/
def sampleProb (p : X → ℝ) (K : ℕ) (E : (Fin K → X) → Prop) : ℝ :=
  ∑ xs : Fin K → X, (∏ k, p (xs k)) * if E xs then 1 else 0

/-- The paper's estimator, using one p-sample and one q-sample shared by every i. -/
def estimate (ψ ϕ : X → ℂ) (D : ColumnData A s) {K : ℕ}
    (xs ys : Fin K → X) : ℂ :=
  ∑ i, ((K : ℂ)⁻¹ * ∑ k, F ψ ϕ D i (xs k) +
         (K : ℂ)⁻¹ * ∑ k, G ψ ϕ D i (ys k))

/-- Failure probability for the strict error event under independent p- and q-samples. -/
def failProb (ψ ϕ : X → ℂ) (D : ColumnData A s) (K : ℕ)
    (target : ℂ) (ε : ℝ) : ℝ :=
  ∑ xs : Fin K → X, ∑ ys : Fin K → X,
    (∏ k, prob ψ (xs k)) * (∏ k, prob ϕ (ys k)) *
      if ε < ‖estimate ψ ϕ D xs ys - target‖ then 1 else 0

end VdNSim.Sparse


