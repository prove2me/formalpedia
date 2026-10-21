-- Prove2me | Definitions.Def_PESContracts_Linear_Model
-- name    : PESContracts_Linear_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:49.797128+00:00
-- url     : https://prove2.me/theorems/7f8a1b53-a4ea-4581-b629-7b3116cdffbb
-- title:
--   §2, §2.1, §4 — conservation model, direct contracts, and linear contracts
-- statement:
--   An agent owns an initial forest area $a_0>0$ and has a privately known baseline conservation fraction $\theta$ supported on $[\underline\theta,\bar\theta]\subseteq[0,1]$. Conservation $a$ must lie in $[0,a_0]$. For cost curvature $h>0$, the cost of conservation beyond the baseline is
--
--   $$
--   c_h(x)=\begin{cases}(h/2)x^2,&x\geq0,\\0,&x<0.\end{cases}
--   $$
--
--   A direct revelation contract assigns an action $a(\theta)$ and nonnegative payment $P(\theta)$ to each reported type. It is feasible when actions lie in $[0,a_0]$, every true type receives nonnegative utility from truthful reporting, and truthful reporting maximizes utility among reports in the type interval. The principal's expected payoff is $\mathbb E_\mu[k a(\theta)-P(\theta)]$.
--
--   A linear contract pays $p a$ for all conserved area. Its closed-form action is $a_L(\theta;p)=\min\{\theta a_0+p/h,a_0\}$, its full-conservation threshold is $\tilde\theta(p)=1-p/(ha_0)$, and its payoff is $\operatorname{Obj}^L(p)=(k-p)\mathbb E_\mu[a_L(\theta;p)]$. The best linear payoff is the supremum over $p\geq0$.
--
--   These definitions share the model used by the four milestones and Theorem 1. The type law $\mu$ is any probability measure concentrated on the type interval, including distributions with atoms.
--
--   **Formalization Note** Positive $a_0$ is explicit because the paper divides by $ha_0$. Feasibility and best response constrain only supported types; the expectation uses a probability measure on the real line. The closed-form action describes nonnegative prices on supported types.
-- source:
--   Li, Ashlagi & Lo, Simple and Approximately Optimal Contracts for Payment for Ecosystem Services, SSRN preprint 3754041 (version of 2021-05-19), pp. 4–5, 9, §2, §2.1, §4, Equation (3); https://ssrn.com/abstract=3754041

import Mathlib
open MeasureTheory

namespace PESContracts.Linear

/-- Parameters of the quadratic conservation model in §2. -/
structure Params where
  a0 : ℝ
  h : ℝ
  θlo : ℝ
  θhi : ℝ

/-- The model's parameter restrictions, including positive initial area. -/
def Params.Standing (M : Params) : Prop :=
  0 < M.a0 ∧ 0 < M.h ∧ 0 ≤ M.θlo ∧ M.θlo ≤ M.θhi ∧ M.θhi ≤ 1

def Params.types (M : Params) : Set ℝ := Set.Icc M.θlo M.θhi

/-- Conservation cost from §2: quadratic above the baseline and zero below it. -/
noncomputable def cost (h x : ℝ) : ℝ :=
  if 0 ≤ x then h / 2 * x ^ 2 else 0

/-- A direct revelation contract assigns an action and a payment to each reported type. -/
structure DirectContract where
  a : ℝ → ℝ
  P : ℝ → ℝ

noncomputable def DirectContract.util (M : Params) (C : DirectContract)
    (θ θ' : ℝ) : ℝ :=
  C.P θ' - cost M.h (C.a θ' - θ * M.a0)

/-- Action bounds, limited liability, individual rationality, and incentive compatibility. -/
def DirectContract.Feasible (M : Params) (C : DirectContract) : Prop :=
  ∀ θ ∈ M.types,
    C.a θ ∈ Set.Icc 0 M.a0 ∧
    0 ≤ C.P θ ∧
    0 ≤ C.util M θ θ ∧
    ∀ θ' ∈ M.types, C.util M θ θ' ≤ C.util M θ θ

noncomputable def DirectContract.payoff (k : ℝ) (μ : Measure ℝ)
    (C : DirectContract) : ℝ :=
  ∫ θ, (k * C.a θ - C.P θ) ∂μ

/-- Agent utility under a price paid for every unit of conserved area. -/
noncomputable def linUtil (M : Params) (p θ a : ℝ) : ℝ :=
  p * a - cost M.h (a - θ * M.a0)

/-- A typewise best-response selection to the linear price. -/
def IsLinearBestResponse (M : Params) (p : ℝ) (aL : ℝ → ℝ) : Prop :=
  ∀ θ ∈ M.types,
    aL θ ∈ Set.Icc 0 M.a0 ∧
    ∀ a ∈ Set.Icc 0 M.a0, linUtil M p θ a ≤ linUtil M p θ (aL θ)

/-- Closed-form action in Equation (3), for nonnegative prices on supported types. -/
noncomputable def linAction (M : Params) (p θ : ℝ) : ℝ :=
  min (θ * M.a0 + p / M.h) M.a0

/-- Threshold for full conservation in §4. -/
noncomputable def θtilde (M : Params) (p : ℝ) : ℝ :=
  1 - p / (M.h * M.a0)

/-- Principal payoff at linear price p, Equation (3) in expectation form. -/
noncomputable def ObjL (M : Params) (k : ℝ) (μ : Measure ℝ) (p : ℝ) : ℝ :=
  (k - p) * ∫ θ, linAction M p θ ∂μ

/-- Best linear-contract payoff over nonnegative prices. -/
noncomputable def ObjLstar (M : Params) (k : ℝ) (μ : Measure ℝ) : ℝ :=
  sSup (ObjL M k μ '' Set.Ici 0)

end PESContracts.Linear


