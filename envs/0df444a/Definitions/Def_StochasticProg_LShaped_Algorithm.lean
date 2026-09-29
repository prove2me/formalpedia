-- Prove2me | Definitions.Def_StochasticProg_LShaped_Algorithm
-- name    : StochasticProg_LShaped_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:05:40.811995+00:00
-- url     : https://prove2.me/theorems/3b2d998a-1cd2-402e-88b9-cfb71ea491df
-- title:
--   The L-shaped algorithm's master program, state and Step 1-2-3 transition
-- statement:
--   This bundle formalizes the L-shaped algorithm itself (Birge & Louveaux §5.1, pp. 183-184,
--   "L-Shaped Algorithm"), as an abstract transition system over the cuts accumulated so far,
--   built on the bases and cut coefficients of the companion `Bases` bundle.
--
--   `State inst` is the algorithm's state after some number of outer iterations: a pair
--   `(Sf, So)` where `Sf` records, as `(scenario, feasibility-basis)` pairs, which feasibility
--   cuts (1.3) Step 2 has added so far, and `So` records which Step-3 witnesses (one basis per
--   scenario) have each produced an optimality cut (1.4) so far.
--
--   `MasterFeasible inst Sf x` says $x\in K_1$ and satisfies every feasibility cut recorded in
--   `Sf` (Step 1, using (1.3) built from `feasCutCoeffs`). `MasterOptFeasible inst So x θ` says
--   $(x,\theta)$ satisfies every optimality cut recorded in `So` (built from `optCutCoeffs`).
--   `IsMasterOptimal inst Sf So x θ` says $(x,\theta)$ solves the master program (1.2)-(1.4) with
--   cuts `Sf`, `So`: it minimizes $c^Tx+\theta$ over the cut-restricted master polytope when `So`
--   is nonempty, and minimizes $c^Tx$ alone when `So` is empty — matching the algorithm's own
--   convention (p. 205) that $\theta$ "is set equal to $-\infty$ and is not considered" until the
--   first optimality cut exists. `IsMasterInfeasible inst Sf` says the master program has become
--   infeasible for the recorded feasibility cuts — the algorithm's eventual certificate (via the
--   goal theorem) that $K_1\cap K_2=\varnothing$.
--
--   `Step inst s s'` is one admissible Steps-1-2-3 transition of the algorithm: from a
--   master-optimal $(x,\theta)$ at state $s=(S_f,S_o)$, either (`feas`) a fresh feasibility cut is
--   added, witnessed by a scenario $k$ and a feasibility basis $b$ for which `IsFeasBasisOptimalAt`
--   holds and the LP's optimal value is strictly positive (so $x\notin K_2$ at scenario $k$) — Step
--   2's branch when the feasibility test fails; or (`opt`), once $x\in K_2$, a fresh optimality cut
--   is added, witnessed by a per-scenario basis family $\beta$ attaining the true recourse value
--   at every scenario, for which the current $\theta$ violates the resulting cut — Step 3's branch
--   when the termination test $\theta^\nu\ge w^\nu$ fails. In both cases the added witness (pair or
--   tuple) must not already be recorded.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, pp. 183-184, Chapter 5, Section 5.1 (Eqs. 1.2-1.4, Steps 1-3)

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_LShaped_Bases

namespace StochasticProg.LShaped

open StochasticProg.Recourse

variable {n1 n2 m1 m2 K : ℕ}

/-- The algorithm's state after some number of outer iterations: `Sf` records, as
`(scenario, basis)` pairs, which feasibility cuts (1.3) Step 2 has added so far; `So`
records which Step-3 witnesses (one basis per scenario) have each produced an optimality
cut (1.4) so far. -/
def State (inst : Instance n1 n2 m1 m2 K) : Type :=
  Finset (Fin K × FeasBasis n2 m2) × Finset (Fin K → Basis n2 m2)

/-- `x ∈ K1` and satisfies every feasibility cut (1.3) recorded in `Sf` (Step 1, using
Eq. (1.3)). -/
def MasterFeasible (inst : Instance n1 n2 m1 m2 K) (Sf : Finset (Fin K × FeasBasis n2 m2))
    (x : Fin n1 → ℝ) : Prop :=
  x ∈ K1 inst ∧
    ∀ p ∈ Sf, (feasCutCoeffs inst p.1 p.2).2 ≤ dotProduct (feasCutCoeffs inst p.1 p.2).1 x

/-- `(x, θ)` satisfies every optimality cut (1.4) recorded in `So`. -/
def MasterOptFeasible (inst : Instance n1 n2 m1 m2 K) (So : Finset (Fin K → Basis n2 m2))
    (x : Fin n1 → ℝ) (θ : ℝ) : Prop :=
  ∀ β ∈ So, (optCutCoeffs inst β).2 ≤ dotProduct (optCutCoeffs inst β).1 x + θ

/-- `(x, θ)` is a Step-1 optimal solution of the master program (1.2)-(1.4) with the
recorded cuts `Sf`, `So`: minimizes `cᵀx + θ` over the master polytope when `So` is
nonempty, and minimizes `cᵀx` alone (θ dropped, "set to `−∞` and not considered", p. 183)
when `So` is empty. -/
def IsMasterOptimal (inst : Instance n1 n2 m1 m2 K) (Sf : Finset (Fin K × FeasBasis n2 m2))
    (So : Finset (Fin K → Basis n2 m2)) (x : Fin n1 → ℝ) (θ : ℝ) : Prop :=
  MasterFeasible inst Sf x ∧
    (So.Nonempty → MasterOptFeasible inst So x θ) ∧
    (if So.Nonempty then
        ∀ x' θ', MasterFeasible inst Sf x' → MasterOptFeasible inst So x' θ' →
          dotProduct inst.c x + θ ≤ dotProduct inst.c x' + θ'
      else
        ∀ x', MasterFeasible inst Sf x' → dotProduct inst.c x ≤ dotProduct inst.c x')

/-- The master program (1.2)-(1.4) has no feasible `x` for the recorded feasibility cuts
`Sf` — the algorithm's certificate, via `thm2_finite_convergence`, that `K1 ∩ K2 = ∅`. -/
def IsMasterInfeasible (inst : Instance n1 n2 m1 m2 K) (Sf : Finset (Fin K × FeasBasis n2 m2)) :
    Prop :=
  ¬ ∃ x, MasterFeasible inst Sf x

/-- One admissible transition of the L-shaped algorithm (Steps 1-3, pp. 183-184): from
cut set `(Sf, So)`, Step 1's optimum `(x, θ)` is either extended by a fresh feasibility
cut, found in Step 2 as a scenario `k` and witness basis `b` for which the feasibility-test
LP (1.8) has a positive optimal value (so `x ∉ K2`), or, once `x ∈ K2`, by a fresh
optimality cut found in Step 3 as a witness `β` attaining the true recourse value at every
scenario whose implied bound `x` currently violates. Both cases require the added basis
(pair or tuple) to be one not already recorded, matching the "return to Step 1" / "stop"
branching of the text. -/
inductive Step (inst : Instance n1 n2 m1 m2 K) : State inst → State inst → Prop
  | feas (Sf : Finset (Fin K × FeasBasis n2 m2)) (So : Finset (Fin K → Basis n2 m2))
      (x : Fin n1 → ℝ) (θ : ℝ) (hopt : IsMasterOptimal inst Sf So x θ)
      (k : Fin K) (b : FeasBasis n2 m2) (hb : IsFeasBasisOptimalAt inst k b x)
      (hpos : 0 < feasBasisValue inst k b x) (hnew : (k, b) ∉ Sf) :
      Step inst (Sf, So) (insert (k, b) Sf, So)
  | opt (Sf : Finset (Fin K × FeasBasis n2 m2)) (So : Finset (Fin K → Basis n2 m2))
      (x : Fin n1 → ℝ) (θ : ℝ) (hopt : IsMasterOptimal inst Sf So x θ)
      (hK2 : x ∈ K2 inst) (β : Fin K → Basis n2 m2) (hβ : IsOptimalAt inst x β)
      (hviol : θ < (optCutCoeffs inst β).2 - dotProduct (optCutCoeffs inst β).1 x)
      (hnew : β ∉ So) :
      Step inst (Sf, So) (Sf, insert β So)

end StochasticProg.LShaped


