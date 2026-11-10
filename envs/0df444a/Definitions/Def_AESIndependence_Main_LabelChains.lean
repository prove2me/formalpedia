-- Prove2me | Definitions.Def_AESIndependence_Main_LabelChains
-- name    : AESIndependence_Main_LabelChains
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T04:09:28.946206+00:00
-- url     : https://prove2.me/theorems/1c5b0a86-1116-4639-9acf-8c0c107abb80
-- title:
--   Permutation-label chains, balanced simulations and multiplicity-sensitive gaps
-- statement:
--   Let $X$ be a finite state space. A permutation-label chain consists of a label distribution $\lambda$ and, for each label $v$, a permutation $g_v$ of $X$. Its transition matrix uses the column convention
--   $$K(y,x)=\Pr_{v\sim\lambda}[g_v(x)=y].$$
--   A balanced simulation of $g$ of length $\ell$ is one input-independent PMF $\mu$ on label sequences of that fixed length. Every sequence of positive mass has product $g$ as a function on all states, and every coordinate marginal is exactly $\lambda$. Coordinates may be correlated. The first list entry acts first; the resulting product is $w_\ell\cdots w_1$.
--   For a symmetric stochastic matrix on at least two states, its ordinary gap is the infimum of $\langle f,(I-K)f\rangle$ over real functions satisfying $\sum_x f(x)=0$ and $\sum_x f(x)^2=1$. This equals $1-\lambda_2(K)$ with multiplicity, including extra stationary modes of reducible chains. The inner product is counting measure; both numerator and normalization would acquire the same factor for uniform measure. Uniform mass is $|X|^{-1}$; total variation is half the finite absolute-difference sum.
--   The lazy generator matrix is $\frac12I+\frac1{4c}\sum_i(g_i+g_i^{-1})$. These definitions contain no expansion or simulation assertions and supply the generic chain interface independently of AES.
--   **Formalization Note** The Rayleigh set is nonempty and bounded on finite spaces with at least two elements; theorem domains enforce this. Label distributions are PMFs, while matrices and total variation use real entries. Empty-space uniform mass is not used as a probability law.
-- source:
--   Angelos Pelecanos, Stefano Tessaro, Vinod Vaikuntanathan, STOC 2027 submission #1279 (October 2026), Definitions 2.11–2.15, Eq. (2.1), §2.4 and Theorem 2.19, pp.12–14 (PDF pp.12–14)

import Mathlib

namespace AESIndependence.Main
noncomputable section
open scoped BigOperators

/-- Ordered distinct tuples. -/
abbrev DistinctTuple (X : Type) (t : ℕ) := {x : Fin t → X // Function.Injective x}

/-- Apply a permutation to all entries, using the same permutation. -/
def tuplePerm {X : Type} {t : ℕ} (g : Equiv.Perm X) :
    Equiv.Perm (DistinctTuple X t) where
  toFun x := ⟨g ∘ x.val, g.injective.comp x.property⟩
  invFun x := ⟨g.symm ∘ x.val, g.symm.injective.comp x.property⟩
  left_inv x := by apply Subtype.ext; funext i; simp
  right_inv x := by apply Subtype.ext; funext i; simp

/-- Matrices use columns for the current state: K y x = Pr[x -> y]. -/
structure LabelChain (X Λ : Type) where
  law : PMF Λ
  action : Λ → Equiv.Perm X

def LabelChain.matrix {X Λ : Type} (K : LabelChain X Λ) :
    Matrix X X ℝ :=
  fun y x => ((K.law.map (fun v => K.action v x)) y).toReal

/-- Application order: the head is applied first. -/
def runWord {X : Type} (w : List (X → X)) (x : X) : X :=
  w.foldl (fun y f => f y) x

def sequenceAction {X Λ : Type} {ℓ : ℕ} (act : Λ → X → X)
    (w : Fin ℓ → Λ) : X → X := runWord ((List.ofFn w).map act)

/-- A fixed length and input-independent law, with the exact target-label marginals. -/
def BalancedSimulation {X Λ : Type} (act : Λ → X → X) (law : PMF Λ)
    (ℓ : ℕ) (g : X → X) : Prop :=
  ∃ μ : PMF (Fin ℓ → Λ),
    (∀ w, μ w ≠ 0 → sequenceAction act w = g) ∧
    ∀ i : Fin ℓ, μ.map (fun w => w i) = law

/-- The actual column transition matrix is symmetric. -/
def IsReversibleUniform {X : Type} (K : Matrix X X ℝ) : Prop :=
  ∀ x y, K x y = K y x

/-- Mean-zero unit sphere; all eigenvalue-1 modes except the constant remain. -/
def rayleighValues {X : Type} [Fintype X] (K : Matrix X X ℝ) : Set ℝ :=
  {q | ∃ f : X → ℝ, (∑ x, f x) = 0 ∧ (∑ x, (f x)^2) = 1 ∧
    q = ∑ x, f x * (f x - ∑ y, K x y * f y)}

/-- Ordinary multiplicity-sensitive gap for symmetric stochastic K on at least two states. -/
def spectralGap {X : Type} [Fintype X] (K : Matrix X X ℝ) : ℝ :=
  sInf (rayleighValues K)

def lambdaTwo {X : Type} [Fintype X] (K : Matrix X X ℝ) : ℝ :=
  1 - spectralGap K

/-- Uniform finite mass; only used as a probability law on nonempty spaces. -/
def uniformMass (X : Type) [Fintype X] : X → ℝ :=
  fun _ => (Fintype.card X : ℝ)⁻¹

def totalVariation {X : Type} [Fintype X] (μ ν : X → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ x, |μ x - ν x|

/-- Probability matrix of a fixed permutation, in the column convention. -/
def permutationMatrix {X : Type} (g : Equiv.Perm X) : Matrix X X ℝ := by
  classical
  exact fun y x => if g x = y then 1 else 0

/-- Exactly 1/2 laziness, and weight 1/(4c) for each generator and inverse. -/
def lazyGeneratorMatrix {X : Type} {c : ℕ} (g : Fin c → Equiv.Perm X) :
    Matrix X X ℝ :=
  fun y x => (1 / 2 : ℝ) * permutationMatrix (Equiv.refl X) y x +
    (1 / (4 * (c : ℝ))) * ∑ i,
      (permutationMatrix (g i) y x + permutationMatrix (g i).symm y x)

end
end AESIndependence.Main


