-- Prove2me | Definitions.Def_QuantumTriangleFinding_Search_FiniteProbability
-- name    : QuantumTriangleFinding_Search_FiniteProbability
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:23:52.188927+00:00
-- url     : https://prove2.me/theorems/a58cf68b-cd26-44af-b869-25e348c1f92d
-- title:
--   Finite laws and probability-weighted complex vectors
-- statement:
--   Let $X$ be a finite set and let $\rho:X\to\mathbb R$ be a probability mass function. Nonnegativity and total mass one reuse the published probability-vector predicate, which permits zero masses. Its support is $S_\rho=\{x:\rho(x)>0\}$. Conditioning on a positive-probability event $A$ is the normalized restriction $\rho(x)1_A(x)/\rho(A)$. On Boolean strings, the product law has mass $\nu_p(x)=\prod_i p^{x_i}(1-p)^{1-x_i}$.
--
--   For any finite complex workspace $W$, a joint vector is represented by its unweighted workspace vectors $f^x\in W$, with
--   $$\langle f,g\rangle_\rho=\sum_{x\in S_\rho}\rho(x)\langle f^x,g^x\rangle,\qquad \|f\|_\rho^2=\sum_x\rho(x)\|f^x\|^2,\qquad \|f\|_{\infty,\rho}=\max_{x\in S_\rho}\|f^x\|.$$
--
--   Kernels act on these functions and as the identity on the workspace. Weighted self-adjointness, positive semidefiniteness, operator order, commutators, phase operators and the actual matrix inverse $(I+H/R)^{-1}$ provide the common operator interface. No desired estimate is a field of these definitions. All arbitrary laws are required to satisfy the probability predicate in their theorem statements. Conditioning is used only at positive mass, and inverse formulas only where positivity ensures invertibility.
--
--   These definitions preserve the paper's conjugate-linear-first inner product and its square-root ket weights without inserting those weights into the infinity norm.
-- source:
--   Arjan Cornelissen, Amin Shiraz Gilani, Xingyu Zhou, STOC 2027 submission #1375 (October 2026), §§3.1–3.2, pp. 13–15; (4.6), p. 18

import Mathlib
import Definitions.Def_MaxCutSample2027_Coreset_averages

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace QuantumTriangleFinding.Search

/-- Sections 3.1–3.2, pp.13–15: a finite probability mass function.
The predicate is imposed on arbitrary laws; constructed conditional laws are explicit functions. -/
def IsProbability {X : Type} [Fintype X] (ρ : X → ℝ) : Prop :=
  MaxCutSample2027.Coreset.IsProbabilityVector ρ

abbrev Support {X : Type} (ρ : X → ℝ) := {x : X // 0 < ρ x}
noncomputable instance supportFintype {X : Type} [Fintype X] (ρ : X → ℝ) :
    Fintype (Support ρ) := Fintype.ofFinite _
noncomputable instance supportDecidableEq {X : Type} (ρ : X → ℝ) :
    DecidableEq (Support ρ) := Classical.decEq _

/-- Finite event probability, and normalized restriction, only used at positive mass. -/
def eventProb {X : Type} [Fintype X] (ρ : X → ℝ) (A : Set X) : ℝ := by
  classical
  exact ∑ x, if x ∈ A then ρ x else 0

def condition {X : Type} [Fintype X] (ρ : X → ℝ) (A : Set X) : X → ℝ := by
  classical
  exact fun x => if x ∈ A then ρ x / eventProb ρ A else 0

noncomputable instance bitsFintype {I : Type} [Fintype I] : Fintype (I → Bool) :=
  Fintype.ofFinite _

def bernoulli {I : Type} [Fintype I] (p : ℝ) (x : I → Bool) : ℝ :=
  ∏ i, if x i then p else 1 - p

def BitsLE {I : Type} (x y : I → Bool) : Prop := ∀ i, x i = true → y i = true

def DownwardClosed {I : Type} (Ω : Set (I → Bool)) : Prop :=
  ∀ ⦃x y⦄, BitsLE x y → y ∈ Ω → x ∈ Ω

def Increasing {I : Type} (A : Set (I → Bool)) : Prop :=
  ∀ ⦃x y⦄, BitsLE x y → x ∈ A → y ∈ A

/-- Weighted function coordinates: the actual ket has coefficient √ρ(x) f(x). -/
abbrev Joint {X : Type} (ρ : X → ℝ) (W : Type) [Fintype W] :=
  Support ρ → EuclideanSpace ℂ W

def normSq {X W : Type} [Fintype X] [Fintype W] (ρ : X → ℝ) (f : Joint ρ W) : ℝ :=
  ∑ x, ρ x.val * ‖f x‖ ^ 2

def jointNorm {X W : Type} [Fintype X] [Fintype W] (ρ : X → ℝ) (f : Joint ρ W) : ℝ :=
  Real.sqrt (normSq ρ f)

def infinityNorm {X W : Type} [Fintype X] [Fintype W] (ρ : X → ℝ)
    (f : Joint ρ W) : ℝ :=
  ((Finset.univ.sup fun x : Support ρ => ‖f x‖₊) : NNReal)

def jointInner {X W : Type} [Fintype X] [Fintype W] (ρ : X → ℝ)
    (f g : Joint ρ W) : ℂ :=
  ∑ x, (ρ x.val : ℂ) * inner ℂ (f x) (g x)

/-- Kernels in unweighted workspace coordinates. All workspace extensions are tensor identities. -/
def applyKernel {X Y E : Type} [Fintype X] [AddCommMonoid E] [Module ℂ E]
    (A : Matrix Y X ℂ) (f : X → E) : Y → E := fun y => ∑ x, A y x • f x

def matrixAct {X : Type} [Fintype X] (A : Matrix X X ℂ)
    (v : EuclideanSpace ℂ X) : EuclideanSpace ℂ X :=
  WithLp.toLp 2 (A.mulVec v)

/-- Weighted adjointness: diag(ρ) A is Hermitian. -/
def SelfAdjoint {X : Type} [Fintype X] (ρ : X → ℝ)
    (A : Matrix (Support ρ) (Support ρ) ℂ) : Prop :=
  ∀ x y, (ρ x.val : ℂ) * A x y = star ((ρ y.val : ℂ) * A y x)

def Positive {X : Type} [Fintype X] (ρ : X → ℝ)
    (A : Matrix (Support ρ) (Support ρ) ℂ) : Prop :=
  SelfAdjoint ρ A ∧ ∀ f : Support ρ → ℂ,
    0 ≤ (∑ x, (ρ x.val : ℂ) * star (f x) * (A.mulVec f) x).re

def OperatorLE {X : Type} [Fintype X] (ρ : X → ℝ)
    (A B : Matrix (Support ρ) (Support ρ) ℂ) : Prop := Positive ρ (B - A)

def commutator {X : Type} [Fintype X] (A B : Matrix X X ℂ) : Matrix X X ℂ :=
  A * B - B * A

/-- The genuine matrix inverse. Our theorems use R>0 and positive semidefinite H,
so I+H/R is invertible; no inverse or desired estimate is supplied as data. -/
def resolvent {X : Type} [Fintype X] [DecidableEq X] (H : Matrix X X ℂ) (R : ℝ) :
    Matrix X X ℂ := (1 + (R : ℂ)⁻¹ • H)⁻¹

/-- Phase query on an arbitrary input register; `read` cannot be accessed by the algorithm. -/
def inputPhase {I X : Type} [Fintype X] (ρ : X → ℝ) (read : X → I → Bool) (i : I) :
    Matrix (Support ρ) (Support ρ) ℂ :=
  Matrix.diagonal fun x => if read x.val i then -1 else 1

end QuantumTriangleFinding.Search


