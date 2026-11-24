-- Prove2me | Definitions.Def_ALADIN_LocalStab_Supplement_Countermodels
-- name    : ALADIN_LocalStab_Supplement_Countermodels
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T02:08:47.335044+00:00
-- url     : https://prove2.me/theorems/aa802dd9-0a9f-4752-a1ce-ca5ab64b0b6e
-- title:
--   Explicit disk-exterior and convex scalar data for testing Lemma 1 and Theorems 2/4
-- statement:
--   These are explicitly constructed instances of the paper's block problem, not new claims from the paper. The first has one block $(u,v)$, objective $u^2$, equality $v=0$, inequality $1-u^2-v^2\le0$, identity scaling, and center $(0,1)$. Its designated projections are $(\pm1,0)$. The step data have $y=(0,1)$, $\kappa=\lambda/2$, $C=(0,-2)$, $H=I$, $\Delta y=0$, $s=1$, and $\lambda_{QP}=\lambda+\mu$.
--
--   The second has one scalar block, objective
--   $$f(q)=q^2/2+q^3/3+q^4/4,$$
--   equality $q=0$, one always inactive inequality $-1\le0$, and identity scaling. For $t>0$ put $x=0$, $y=t$, $\lambda=-((1+\rho)t+t^2+t^3)$, $H=1+2t+3t^2$, and $\mu=t^{-2}$. Its exact QP solution is $z=y+\Delta y=(H+\rho)t/(H+\mu)$, $s=z$, $\lambda_{QP}=\lambda+\mu z$. The line-search candidate is $a=-\lambda/(\lambda_{QP}-\lambda)$. These definitions provide concrete data for the separately stated counterexample targets.
-- source:
--   Houska, Frasch, Diehl, An augmented Lagrangian based algorithm for distributed nonconvex optimization, SIAM J. Optim. 26 (2016), DOI 10.1137/140975991, pp. 1101, 1108, problem (1.1), Algorithm 2; constructed counterexamples to pp. 1115–1116, 1119, detailed in DISPROOF.md

import Mathlib
import Definitions.Def_ALADIN_LocalStab_Supplement_Algorithm

noncomputable section

namespace ALADIN.LocalStab.Supplement

open Matrix

/-- Smooth exterior-of-a-disk example: min u^2 subject to v=0 and 1-u^2-v^2≤0. -/
def diskProblem : Problem 1 2 1 1 where
  f := fun _ z => z 0 ^ 2
  h := fun _ z _ => 1 - z 0 ^ 2 - z 1 ^ 2
  A := fun _ _ j => if j = 1 then 1 else 0
  b := 0

def north : Fin 1 → Fin 2 → ℝ := fun _ j => if j = 0 then 0 else 1

def east : Fin 1 → Fin 2 → ℝ := fun _ j => if j = 0 then 1 else 0

def west : Fin 1 → Fin 2 → ℝ := fun _ j => if j = 0 then -1 else 0

def diskScaling : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ := fun _ => 1

/-- All data before globalization, with exact active Jacobian. H is allowed to be inexact in §6. -/
def diskStep (ρ μ l : ℝ) : Step 1 2 1 1 where
  ρ := ρ
  Sig := diskScaling
  μ := μ
  y := north
  κ := fun _ _ => l / 2
  C := fun _ _ j => if j = 0 then 0 else -2
  H := fun _ => 1
  dy := 0
  s := fun _ => 1
  lamQP := fun _ => l + μ

/-- A globally strictly convex scalar objective. The constraints are q=0 and the inactive inequality -1≤0. -/
def quarticProblem : Problem 1 1 1 1 where
  f := fun _ z => z 0 ^ 2 / 2 + z 0 ^ 3 / 3 + z 0 ^ 4 / 4
  h := fun _ _ _ => -1
  A := fun _ => 1
  b := 0

def scalarScaling : Fin 1 → Matrix (Fin 1) (Fin 1) ℝ := fun _ => 1

def quarticH (t : ℝ) : ℝ := 1 + 2*t + 3*t^2

def quarticLam (ρ t : ℝ) : Fin 1 → ℝ := fun _ => -((1+ρ)*t + t^2 + t^3)

def quarticZ (ρ t : ℝ) : ℝ := (quarticH t + ρ)*t / (quarticH t + 1/t^2)

def quarticQP (ρ t : ℝ) : ℝ := quarticLam ρ t 0 + (1/t^2) * quarticZ ρ t

/-- The unique exact-data NLP and QP solutions; mu=1/t^2 tends to infinity. -/
def quarticStep (ρ t : ℝ) : Step 1 1 1 1 where
  ρ := ρ
  Sig := scalarScaling
  μ := 1 / t^2
  y := fun _ _ => t
  κ := 0
  C := 0
  H := fun _ _ _ => quarticH t
  dy := fun _ _ => quarticZ ρ t - t
  s := fun _ => quarticZ ρ t
  lamQP := fun _ => quarticQP ρ t

/-- The exact dual maximizer on the overshooting segment is at lambda=0. -/
def quarticAlpha (ρ t : ℝ) : ℝ :=
  -(quarticLam ρ t 0) / (quarticQP ρ t - quarticLam ρ t 0)

end ALADIN.LocalStab.Supplement


