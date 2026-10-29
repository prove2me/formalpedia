-- Prove2me | Definitions.Def_WangMinimaxRegret_Reformulation_Model
-- name    : WangMinimaxRegret_Reformulation_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:33:02.048408+00:00
-- url     : https://prove2.me/theorems/8e043446-0008-487e-8f6d-a190fef1de1c
-- title:
--   Valuation information and Stieltjes payment mechanisms
-- statement:
--   Let $a\ge0$, let $b\in\mathbb R\cup\{+\infty\}$ with $a\le b$, and set $I=\{x\in\mathbb R:a\le x\le b\}$. There are $K\ge0$ specified finite real moments $\mu_1,\ldots,\mu_K$. A moment law is any Borel probability measure $F$ supported on $I$ satisfying integrability of $x^k$ and $\int x^k\,dF=\mu_k$ for $1\le k\le K$. Its CDF is $F(({-\infty},x])$. The printed ambiguity class additionally requires $F(({-\infty},a])=0$; consistency means that this class is nonempty. The moment-law class alone is used in displayed problem (2). At finite $b$, support and probability normalization imply $F(b)=1$; at infinity this is total mass one.
--
--   Payments are real, nondecreasing, right-continuous Stieltjes functions $m$, zero below $a$, normalized by $m(0)=0$, and extended constantly above finite $b$. They are nonnegative on $I$. Their cumulative allocation and feasibility budget are
--   $$q_m(x)=\int_{I\cap(0,x]}\frac{1}{t}\,dm(t),\qquad q_m(x)\le1\quad(x\in I).$$
--   The measure $dm$ is locally finite and may have infinite total mass. The integral includes the payment jump at a positive lower endpoint; no payment atom is allowed at zero. Allocation need not reach one. Atomic, mixed, and continuous valuation laws are all permitted.
--
--   The independent direct-mechanism predicate for real functions $q,m$ requires $0\le q(x)\le1$, $xq(x)-m(x)\ge0$, and $xq(x)-m(x)\ge xq(y)-m(y)$ for every $x,y\in I$. It records individual rationality and incentive compatibility, rather than defining them using dual certificates.
-- source:
--   Wang, Liu and Zhang (2024), Minimax Regret Robust Screening with Moment Information, https://doi.org/10.1287/msom.2023.0072, Section 2, pp. 6–7, direct mechanisms, M and the ambiguity class

import Mathlib

open MeasureTheory Set
open scoped ENNReal NNReal
set_option autoImplicit false
noncomputable section

namespace WangMinimaxRegret.Reformulation

structure Data where
  a : ℝ
  b : WithTop ℝ
  nonneg_a : 0 ≤ a
  ordered : (a : WithTop ℝ) ≤ b
  K : ℕ
  mu : Fin K → ℝ

def interval (d : Data) : Set ℝ := {x | d.a ≤ x ∧ (x : WithTop ℝ) ≤ d.b}

/-- The law's right-continuous CDF; laws below are Borel measures on the real line. -/
def cdf (F : Measure ℝ) (x : ℝ) : ℝ≥0∞ := F (Iic x)

/-- Display (2), which does not impose F(a)=0. Order zero is total mass one. -/
def MomentLaw (d : Data) (F : Measure ℝ) : Prop :=
  IsProbabilityMeasure F ∧ F (interval d)ᶜ = 0 ∧
    ∀ i : Fin d.K, Integrable (fun x : ℝ => x ^ (i.val + 1)) F ∧
      (∫ x : ℝ, x ^ (i.val + 1) ∂F) = d.mu i

/-- The printed ambiguity class, including its lower-endpoint restriction. -/
def Ambiguous (d : Data) (F : Measure ℝ) : Prop :=
  MomentLaw d F ∧ cdf F d.a = 0

def Consistent (d : Data) : Prop := ∃ F : Measure ℝ, Ambiguous d F

/-- Cumulative allocation from the payment Stieltjes measure. Integrate only at
positive valuations; the zero atom is forbidden by the payment normalization. -/
def allocation (d : Data) (m : StieltjesFunction ℝ) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in interval d ∩ Ioc 0 x, ENNReal.ofReal (1 / t) ∂m.measure

/-- The payment's zero/constant extensions only specify values outside the valuation domain.
StieltjesFunction supplies monotonicity and right continuity, without finite total variation. -/
def IsPayment (d : Data) (m : StieltjesFunction ℝ) : Prop :=
  m 0 = 0 ∧ (∀ x : ℝ, x < d.a → m x = 0) ∧
  (∀ x y : ℝ, d.b ≤ (x : WithTop ℝ) → d.b ≤ (y : WithTop ℝ) → m x = m y) ∧
  (∀ x ∈ interval d, 0 ≤ m x) ∧
  ∀ x ∈ interval d, allocation d m x ≤ 1

/-- The economic direct-mechanism inequalities, independently of the payment budget. -/
def DirectICIR (d : Data) (q m : ℝ → ℝ) : Prop :=
  (∀ x ∈ interval d, 0 ≤ q x ∧ q x ≤ 1) ∧
  (∀ x ∈ interval d, 0 ≤ x * q x - m x) ∧
  ∀ x ∈ interval d, ∀ y ∈ interval d, x * q y - m y ≤ x * q x - m x

end WangMinimaxRegret.Reformulation


