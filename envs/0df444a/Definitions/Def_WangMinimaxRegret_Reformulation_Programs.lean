-- Prove2me | Definitions.Def_WangMinimaxRegret_Reformulation_Programs
-- name    : WangMinimaxRegret_Reformulation_Programs
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:34:27.847961+00:00
-- url     : https://prove2.me/theorems/4ea97b2e-c969-4901-af7c-14c14a98850b
-- title:
--   Homogenized measure LP, dual, and robust screening LP
-- statement:
--   For data $d$, feasible payment $m$, and finite price $p\in I$, define the measure LP (3) with carrier $I$, cost $m$, centered moment tests $x^k-\mu_k$ with right-hand side zero, and tail test $\mathbf1_{[p,\infty)}$ with right-hand side one. Thus $H$ is a finite nonnegative measure with finite specified moments and
--   $$\int(x^k-\mu_k)\,dH=0\ (1\le k\le K),\qquad H([p,\infty))=1.$$
--   The $k=0$ centered row is identically zero, not a probability constraint. Its objective is $\int m\,dH$. Define the rescalings $H=F/T_F(p)$ and $F=H/H(\mathbb R)$; theorems use them only when their denominators are positive and finite.
--
--   For real multipliers $\ell\in\mathbb R^K$, set $A_\ell(x)=\sum_{k=1}^K(x^k-\mu_k)\ell_k$. A dual pair $(\theta,\ell)$ is feasible when
--   $$A_\ell(x)\le m(x)\quad(x\in I,\ x<p),\qquad \theta+A_\ell(x)\le m(x)\quad(x\in I,\ x\ge p).$$
--   Its value is the supremum of real $\theta$, in extended reals. The robust LP has $m\in\mathcal M$, real $r\ge0$, and arbitrary price-indexed real multipliers $\lambda_k(p)$, with the above inequalities for every $p\in I$ and $\theta=rp$. There is no regularity requirement on $\lambda$; its real-line extension is ignored outside $I$. The LP value is the supremum of feasible $r$, and an optimal triple is feasible and attains it. This program is defined without reference to the original competitive ratio.
-- source:
--   Wang, Liu and Zhang (2024), Minimax Regret Robust Screening with Moment Information, https://doi.org/10.1287/msom.2023.0072, Section 2, pp. 8–9, equations (3)–(4) and (P-LP)

import Definitions.Def_WangMinimaxRegret_Reformulation_MeasureLP
import Definitions.Def_WangMinimaxRegret_Reformulation_Revenue

open MeasureTheory Set
open scoped ENNReal NNReal
set_option autoImplicit false
noncomputable section

namespace WangMinimaxRegret.Reformulation

/-- Equation (3) as a measure LP. The none row is tail mass one; the some rows
are centered moments. The redundant k=0 equation is identically zero. -/
def homogenizedLP (d : Data) (m : StieltjesFunction ℝ) (p : ℝ) : MeasureLP (Option (Fin d.K)) where
  carrier := interval d
  cost := fun x => ENNReal.ofReal (m x)
  test := fun i => match i with
    | none => (Ici p).indicator (fun _ => (1 : ℝ))
    | some j => fun x => x ^ (j.val + 1) - d.mu j
  target := fun i => match i with
    | none => 1
    | some _ => 0

def scaleToTail (F : Measure ℝ) (p : ℝ) : Measure ℝ := (tail F p)⁻¹ • F

def normalizeMass (H : Measure ℝ) : Measure ℝ := (H univ)⁻¹ • H

def momentPolynomial (d : Data) (lam : Fin d.K → ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin d.K, (x ^ (i.val + 1) - d.mu i) * lam i

/-- The two distinct half-interval inequalities of (4). -/
def DualFeasible (d : Data) (m : StieltjesFunction ℝ) (p theta : ℝ)
    (lam : Fin d.K → ℝ) : Prop :=
  (∀ x ∈ interval d, x < p → momentPolynomial d lam x ≤ m x) ∧
  ∀ x ∈ interval d, p ≤ x → theta + momentPolynomial d lam x ≤ m x

def dualValue (d : Data) (m : StieltjesFunction ℝ) (p : ℝ) : EReal :=
  ⨆ theta : ℝ, ⨆ lam : Fin d.K → ℝ, ⨆ (_ : DualFeasible d m p theta lam),
    (theta : EReal)

/-- Price-indexed multipliers have no regularity restriction. -/
def LPFeasible (d : Data) (m : StieltjesFunction ℝ) (r : ℝ)
    (lam : ℝ → Fin d.K → ℝ) : Prop :=
  IsPayment d m ∧ 0 ≤ r ∧ ∀ p ∈ interval d, DualFeasible d m p (r * p) (lam p)

def lpValue (d : Data) : EReal :=
  ⨆ m : StieltjesFunction ℝ, ⨆ r : ℝ, ⨆ lam : ℝ → Fin d.K → ℝ,
    ⨆ (_ : LPFeasible d m r lam), (r : EReal)

def LPOptimal (d : Data) (m : StieltjesFunction ℝ) (r : ℝ)
    (lam : ℝ → Fin d.K → ℝ) : Prop :=
  LPFeasible d m r lam ∧ (r : EReal) = lpValue d

end WangMinimaxRegret.Reformulation


