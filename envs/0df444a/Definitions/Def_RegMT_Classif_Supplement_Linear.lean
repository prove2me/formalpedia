-- Prove2me | Definitions.Def_RegMT_Classif_Supplement_Linear
-- name    : RegMT_Classif_Supplement_Linear
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T05:24:27.13586+00:00
-- url     : https://prove2.me/theorems/a05fad51-000c-4282-a5dc-4758763a6cf4
-- title:
--   Programs (5) and (17) on closed convex supports
-- statement:
--   Let $L(t)=\max_{j\le J}(a_jt+b_j)$, with nonempty finite piece and sample index sets. Let $r_w(x,y)=\langle w,x\rangle-y$. Program (5) has variables $\lambda\ge0,s_i,p_{ij}$ in the joint dual space and constraints
--   $$S_\Xi(a_jr_w-p_{ij})+b_j+p_{ij}(\hat\xi_i)\le s_i,\qquad\|p_{ij}\|_*\le\lambda.$$
--   Program (17) has two dual variables for each sample and piece, with $a_j\hat y_iw-p^+_{ij}$ and $-a_j\hat y_iw-p^-_{ij}$ inside the feature-support functions; its second constraint subtracts $\kappa\lambda$. Both values are the infimum of $\lambda\rho+N^{-1}\sum_i s_i$. The joint regression dual variable is precisely the pair $(p_{ij},u_{ij})$ in the paper, under the published coordinate isomorphism. Support functions and program infima use extended reals, so an unbounded support is permitted. These definitions also transcribe Theorem 3.11(i), p.11, (17).
-- source:
--   Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, Regularization via Mass Transportation, arXiv:1710.10016v3, p.8, Theorem 3.1(i), (5); p.11, Theorem 3.11(i), (17)

import Mathlib
import Definitions.Def_RegMT_Classif_Supplement_Support
import Definitions.Def_RegMT_Classif_Supplement_Transport
import Definitions.Def_RegMT_Regress_Model

open scoped ENNReal

noncomputable section

namespace RegMT.Classif.Supplement

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Finite nonempty maximum, using an extended supremum to avoid a real empty supremum. -/
def Piecewise {J : ℕ} (a b : Fin J → ℝ) (L : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, (L t : EReal) = ⨆ j, ((a j * t + b j : ℝ) : EReal)

structure Program5 (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (N J : ℕ) where
  lam : ℝ
  slack : Fin N → ℝ
  dual : Fin N → Fin J → (E →L[ℝ] ℝ)

def feasible5 {n N J : ℕ} (e : E ≃L[ℝ] (Fin n → ℝ) × ℝ) (S : Set E)
    (z : Fin N → E) (a b : Fin J → ℝ) (w : Fin n → ℝ) (q : Program5 E N J) : Prop :=
  0 ≤ q.lam ∧ ∀ i j,
    support S (a j • RegMT.Regress.pairing e w - q.dual i j) +
      ((b j + q.dual i j (z i) : ℝ) : EReal) ≤ (q.slack i : EReal) ∧
    ‖q.dual i j‖ ≤ q.lam

def value5 {n N J : ℕ} (e : E ≃L[ℝ] (Fin n → ℝ) × ℝ) (S : Set E)
    (z : Fin N → E) (a b : Fin J → ℝ) (ρ : ℝ) (w : Fin n → ℝ) : EReal :=
  ⨅ q : Program5 E N J, ⨅ (_ : feasible5 e S z a b w q),
    ((q.lam * ρ + (N : ℝ)⁻¹ * ∑ i, q.slack i : ℝ) : EReal)

structure Program17 (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (N J : ℕ) where
  lam : ℝ
  slack : Fin N → ℝ
  plus : Fin N → Fin J → (V →L[ℝ] ℝ)
  minus : Fin N → Fin J → (V →L[ℝ] ℝ)

def feasible17 {N J : ℕ} (X : Set V) (x : Fin N → V) (y : Fin N → Bool)
    (a b : Fin J → ℝ) (κ : ℝ) (w : V →L[ℝ] ℝ) (q : Program17 V N J) : Prop :=
  0 ≤ q.lam ∧ ∀ i j,
    support X ((a j * DRLogReg.Reformulation.sgn (y i)) • w - q.plus i j) +
      ((b j + q.plus i j (x i) : ℝ) : EReal) ≤ (q.slack i : EReal) ∧
    support X ((-a j * DRLogReg.Reformulation.sgn (y i)) • w - q.minus i j) +
      ((b j + q.minus i j (x i) - κ * q.lam : ℝ) : EReal) ≤ (q.slack i : EReal) ∧
    ‖q.plus i j‖ ≤ q.lam ∧ ‖q.minus i j‖ ≤ q.lam

def value17 {N J : ℕ} (X : Set V) (x : Fin N → V) (y : Fin N → Bool)
    (a b : Fin J → ℝ) (κ ρ : ℝ) (w : V →L[ℝ] ℝ) : EReal :=
  ⨅ q : Program17 V N J, ⨅ (_ : feasible17 X x y a b κ w q),
    ((q.lam * ρ + (N : ℝ)⁻¹ * ∑ i, q.slack i : ℝ) : EReal)

end RegMT.Classif.Supplement


