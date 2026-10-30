-- Prove2me | Definitions.Def_JiangALSOX_Dominance_Programs
-- name    : JiangALSOX_Dominance_Programs
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T01:05:34.075449+00:00
-- url     : https://prove2.me/theorems/f2d354bc-e74c-4e92-893c-82202245e3bc
-- title:
--   Exact slack-based ALSO-X and CVaR bilevel programs
-- statement:
--   For a real budget $t$, write $D_t=\{x\in X:c^\top x\le t\}$. The hinge feasible pairs are $x\in D_t$ and measurable $s:\Xi\to\mathbb R$ with $s\ge0$ and $g(x,\cdot)\le s$ almost surely. Their objective is $E[s]\in[0,+\infty]$. The predicate of optimality requires feasibility and an objective no larger than that of every feasible pair.
--
--   The CVaR feasible triples are $x\in D_t$, $\beta\le0$ and measurable $s$ with $s\ge\beta$ and $g(x,\cdot)\le s$ almost surely. Their objective is
--   $$F(s,\beta)=\varepsilon\beta+E[(s-\beta)_+]=E[s]-(1-\varepsilon)\beta,$$
--   where the last equality is valid on the feasible set. Its optimum is again defined by comparison with all feasible triples.
--
--   Let $T_A$ consist of those $t$ for which some hinge-optimal pair satisfies $P(s=0)\ge1-\varepsilon$. Let $T_C$ consist of those $t$ for which some CVaR-optimal triple satisfies $F(s,\beta)\le0$. Define
--   $$v^A=\inf T_A,\qquad v^{CVaR}=\inf T_C.$$
--   Both outer values are extended real: the empty set has infimum $+\infty$, and an unbounded-below set has infimum $-\infty$. Lower-level attainment is required by each budget membership; it is not assumed for every budget. Multiple optimal slacks are retained, and the upper level existentially selects among them. These definitions use (7) and (13) themselves, not the projected hinge expression (6) or the feasibility formulation (12c).
-- source:
--   Nan Jiang and Weijun Xie, ALSO-X and ALSO-X+: Better Convex Approximations for Chance Constrained Programs, arXiv:2012.04763v4 (14 October 2021), https://arxiv.org/abs/2012.04763v4, pp. 6–7, (7); pp. 12–13, (13); p. 41, (34)–(35)

import Definitions.Def_JiangALSOX_Dominance_ExtendedExpectation
import Definitions.Def_JiangALSOX_Dominance_Model

open MeasureTheory

namespace JiangALSOX.Dominance

def hingeFeasible {n m I : ℕ} (D : Model n m I) (t : ℝ)
    (x : Fin n → ℝ) (s : D.Ξ → ℝ) : Prop :=
  x ∈ D.X ∧ dotProduct D.c x ≤ t ∧ Measurable s ∧
    (∀ᵐ ξ ∂D.P, 0 ≤ s ξ ∧ loss D x ξ ≤ s ξ)

noncomputable def hingeObjective {n m I : ℕ} (D : Model n m I) (s : D.Ξ → ℝ) : EReal :=
  (positiveExpectation D.P s).toEReal

def hingeOptimal {n m I : ℕ} (D : Model n m I) (t : ℝ)
    (x : Fin n → ℝ) (s : D.Ξ → ℝ) : Prop :=
  hingeFeasible D t x s ∧ ∀ y r, hingeFeasible D t y r →
    hingeObjective D s ≤ hingeObjective D r

def cvarFeasible {n m I : ℕ} (D : Model n m I) (t : ℝ)
    (x : Fin n → ℝ) (s : D.Ξ → ℝ) (β : ℝ) : Prop :=
  x ∈ D.X ∧ dotProduct D.c x ≤ t ∧ β ≤ 0 ∧ Measurable s ∧
    (∀ᵐ ξ ∂D.P, β ≤ s ξ ∧ loss D x ξ ≤ s ξ)

noncomputable def cvarObjective {n m I : ℕ} (D : Model n m I)
    (s : D.Ξ → ℝ) (β : ℝ) : EReal :=
  ((D.ε * β : ℝ) : EReal) +
    (positiveExpectation D.P (fun ξ => s ξ - β)).toEReal

def cvarOptimal {n m I : ℕ} (D : Model n m I) (t : ℝ)
    (x : Fin n → ℝ) (s : D.Ξ → ℝ) (β : ℝ) : Prop :=
  cvarFeasible D t x s β ∧ ∀ y r b, cvarFeasible D t y r b →
    cvarObjective D s β ≤ cvarObjective D r b

def alsoBudgets {n m I : ℕ} (D : Model n m I) : Set ℝ :=
  {t | ∃ x s, hingeOptimal D t x s ∧
    ENNReal.ofReal (1 - D.ε) ≤ D.P {ξ | s ξ = 0}}

def cvarBudgets {n m I : ℕ} (D : Model n m I) : Set ℝ :=
  {t | ∃ x s β, cvarOptimal D t x s β ∧ cvarObjective D s β ≤ 0}

noncomputable def alsoValue {n m I : ℕ} (D : Model n m I) : EReal :=
  sInf ((fun t : ℝ => (t : EReal)) '' alsoBudgets D)

noncomputable def cvarValue {n m I : ℕ} (D : Model n m I) : EReal :=
  sInf ((fun t : ℝ => (t : EReal)) '' cvarBudgets D)

end JiangALSOX.Dominance


