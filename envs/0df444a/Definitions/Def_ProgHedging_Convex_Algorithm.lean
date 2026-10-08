-- Prove2me | Definitions.Def_ProgHedging_Convex_Algorithm
-- name    : ProgHedging_Convex_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:17:27.401815+00:00
-- url     : https://prove2.me/theorems/1a24be1e-7d39-409a-ad5e-efcbaa05648f
-- title:
--   Progressive hedging with exact minimization, one exact iteration, and the norm ‖(X, W)‖_r (pp. 9, 20–23)
-- statement:
--   Fix $r>0$. The **progressive hedging algorithm** (p. 9) generates policies $X^\nu$ and price systems $W^\nu\in\mathcal M$, $\nu=0,1,2,\dots$, from an arbitrary $X^0$ and some $W^0\in\mathcal M$:
--
--   1. $\hat X^\nu=JX^\nu$;
--   2. for each scenario $s$, $X^{\nu+1}(s)$ is an optimal solution of
--   $$
--   (P^\nu_s)\qquad \text{minimize } f_s(x)+x\cdot W^\nu(s)+\tfrac12 r\,|x-\hat X^\nu(s)|^2 \text{ over } x\in C_s ;
--   $$
--   3. $W^{\nu+1}=W^\nu+rKX^{\nu+1}$.
--
--   A pair of sequences $(X^\nu,W^\nu)$ satisfying this with exact minimization in Step 2 is an **exact progressive hedging sequence**. A single **exact iteration** from $(V,W)$ to $(V',W')$ means: some policy $X^+$ has $X^+(s)$ optimal in $(P^\nu_s)$ with data $\hat X^\nu(s)=V(s)$, $W^\nu(s)=W(s)$ for every $s$, and $V'=JX^+$, $W'=W+rKX^+$. Finally,
--
--   $$
--   \|(X,W)\|_r=\bigl(\|X\|^2+r^{-2}\|W\|^2\bigr)^{1/2}
--   $$
--
--   with $\|\cdot\|$ the norm $\langle X,X\rangle^{1/2}$ of the scenario model (5.2).
--
--   The exact iteration is the map $(\hat X^\nu,W^\nu)\mapsto(\hat X^{\nu+1},W^{\nu+1})$; in the proof of Theorem 5.1 it is the operator $M_r$ of (5.22)–(5.23) in the rescaled variables $(V,\bar W)=(\hat X,r^{-1}W)$, and $\|\cdot\|_r$ is the Euclidean norm of those variables (5.7).
--
--   **Formalization Note.** Exact minimization of $(P^\nu)$ over $\mathcal C$ is stated scenario by scenario, as in Step 2 of the paper ("this decomposes into solving, for each scenario $s\in S$, the subproblem $(P^\nu_s)$"). $X^0$ is unconstrained, as in Theorem 5.1.
-- source:
--   Rockafellar and Wets, Scenarios and policy aggregation in optimization under uncertainty, IIASA Working Paper WP-87-119 (1987), pp. 8–9 (the algorithm), p. 20 (exact minimization, (5.2)), pp. 21–23 ((5.5)–(5.7), (5.22))

import Mathlib
import Definitions.Def_ProgHedging_Convex_Problem

open scoped RealInnerProductSpace

namespace ProgHedging.Convex

/-- The progressive hedging algorithm with exact minimization (p. 9; "exact minimization", p. 20),
from an arbitrary `X⁰` and `W⁰ ∈ ℳ`: in iteration `ν`, `X̂^ν = J X^ν` (Step 1); for each scenario
`s`, `X^{ν+1}(s)` is an optimal solution of
`(P^ν_s)  minimize f_s(x) + x·W^ν(s) + ½ r |x − X̂^ν(s)|²  over x ∈ C_s` (Step 2);
`W^{ν+1} = W^ν + r K X^{ν+1}` (Step 3). -/
def Problem.IsExactPHSeq {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) (r : ℝ)
    (X W : ℕ → Policy S n) : Prop :=
  W 0 ∈ pr.M ∧ ∀ ν,
    (∀ s, X (ν + 1) s ∈ pr.C s ∧ ∀ z ∈ pr.C s,
      pr.subObj s (pr.J (X ν) s) (W ν s) r (X (ν + 1) s) ≤
        pr.subObj s (pr.J (X ν) s) (W ν s) r z) ∧
    W (ν + 1) = W ν + r • pr.K (X (ν + 1))

/-- (5.2), p. 20: `‖(X, W)‖_r = (‖X‖² + r^{−2}‖W‖²)^{1/2}`, with `‖·‖` the norm (2.3). -/
noncomputable def Problem.rnorm {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) (r : ℝ)
    (X W : Policy S n) : ℝ :=
  Real.sqrt (pr.ip X X + (r⁻¹) ^ 2 * pr.ip W W)

/-- One iteration of the algorithm with exact minimization, from `(X̂^ν, W^ν) = (V, W)` to
`(X̂^{ν+1}, W^{ν+1}) = (V', W')`: some `X^{ν+1}` solves every `(P^ν_s)` exactly with data
`V(s), W(s)`, `V' = J X^{ν+1}` and `W' = W + r K X^{ν+1}` (p. 9). In the notation of the proof of
Theorem 5.1 this is the map `M_r` of (5.22)–(5.23), after the rescaling (5.5)–(5.6). -/
def Problem.IsStep {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) (r : ℝ)
    (V W V' W' : Policy S n) : Prop :=
  ∃ Xp : Policy S n,
    (∀ s, Xp s ∈ pr.C s ∧ ∀ z ∈ pr.C s,
      pr.subObj s (V s) (W s) r (Xp s) ≤ pr.subObj s (V s) (W s) r z) ∧
    V' = pr.J Xp ∧ W' = W + r • pr.K Xp

end ProgHedging.Convex


