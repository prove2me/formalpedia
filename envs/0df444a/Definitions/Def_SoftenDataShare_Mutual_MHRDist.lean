-- Prove2me | Definitions.Def_SoftenDataShare_Mutual_MHRDist
-- name    : SoftenDataShare_Mutual_MHRDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T23:11:44.402563+00:00
-- url     : https://prove2.me/theorems/b6664d6d-4578-4aca-9f68-34d06e5fdcdb
-- title:
--   Section 2 — a distribution on [0, 1] with positive C¹ density and strictly increasing hazard rate
-- statement:
--   This file fixes the distribution of consumer locations in the Hotelling line model of Choe, Cong and Wang.
--
--   Let $F:\mathbb R\to\mathbb R$ and $f:\mathbb R\to\mathbb R$. The **hazard rate** of $(F,f)$ at $x$ is
--   $$h(x)=\frac{f(x)}{1-F(x)}.$$
--   The pair $(F,f)$ is a **monotone-hazard-rate distribution on $[0,1]$** if
--   1. $F(0)=0$ and $F(1)=1$;
--   2. $F$ is differentiable on $[0,1]$ (one-sided at the endpoints) with derivative $f$, and $f$ is continuous on $[0,1]$;
--   3. $f(x)>0$ for every $x\in[0,1]$;
--   4. $h$ is strictly increasing on $[0,1)$.
--
--   Then $F$ is the cumulative distribution function of a consumer's location on $[0,1]$ and $f$ its strictly positive density. This is the standing assumption of every result of the paper.
--
--   **Formalization Note** The paper asks for a "smooth" distribution function; this file asks only that $F$ be continuously differentiable on $[0,1]$, which is weaker, so every theorem stated under it is at least as strong as the paper's. The hazard rate is undefined at $x=1$ (Lean's division by zero gives $0$ there), so monotonicity is required on $[0,1)$. Values of $F$ and $f$ outside $[0,1]$ are unconstrained and never used.
-- source:
--   Choe, Cong & Wang, Softening Competition through Unilateral Sharing of Customer Data, Monash Discussion Paper 2021-10 (rev. Oct. 20, 2022), p. 6, Section 2 (the model)

import Mathlib

namespace SoftenDataShare.Mutual

/-- The hazard rate `h(x) = f(x) / (1 - F(x))` of a distribution with c.d.f. `F` and density `f`.
At `x = 1` (where `F 1 = 1`) Lean's division by zero gives the junk value `0`; it is never used. -/
noncomputable def hazard (F f : ℝ → ℝ) (x : ℝ) : ℝ := f x / (1 - F x)

/-- A distribution of consumer locations on `[0, 1]` with c.d.f. `F` and density `f`, as in
Section 2 of Choe, Cong & Wang: `F(0) = 0`, `F(1) = 1`, `F` is continuously differentiable on
`[0, 1]` with derivative `f` (one-sided at the endpoints), `f` is strictly positive on `[0, 1]`,
and the hazard rate `h = f / (1 - F)` is strictly increasing on `[0, 1)` (monotone hazard rate
condition). Values of `F` and `f` outside `[0, 1]` are unconstrained and never used. -/
structure MHRDist (F f : ℝ → ℝ) : Prop where
  F_zero : F 0 = 0
  F_one : F 1 = 1
  hasDerivWithinAt : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt F (f x) (Set.Icc 0 1) x
  continuousOn_density : ContinuousOn f (Set.Icc 0 1)
  density_pos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < f x
  hazard_strictMonoOn : StrictMonoOn (hazard F f) (Set.Ico 0 1)

end SoftenDataShare.Mutual


