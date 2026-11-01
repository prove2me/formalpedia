-- Prove2me | Definitions.Def_StructBandit_dualFn
-- name    : StructBandit_dualFn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:32:34.618671+00:00
-- url     : https://prove2.me/theorems/f962bb9d-649a-4fdc-82dc-c5a18d75f813
-- title:
--   Dual cone $\mathcal K^\star$ and the dual function $\mathrm{Dual}(\eta,x',P;\mu)$
-- statement:
--   Let $\mathcal K=\mathrm{cone}(\mathcal P)$ and $\mathcal K^\star=\{\lambda:\ \langle\lambda,Q\rangle\ge0\ \forall Q\in\mathcal K\}$ with $\langle\lambda,Q\rangle=\sum_{x,r}\lambda(r,x)Q(r,x)$. A dual vector is $\mu=(\alpha,\beta,\lambda)\in\mathbb R_+\times\mathbb R\times\mathcal K^\star$. The **dual function** is
--
--   $$
--   \mathrm{Dual}(\eta,x',P;\mu):=\sum_{x\in\tilde X(P),r}\eta(x)\log\Big(\tfrac{\eta(x)-\lambda(r,x)-\beta-\alpha r\mathbb 1(x=x')}{\eta(x)}\Big)P(r,x)-\sum_{x\in x^\star(P),r}\lambda(r,x)P(r,x)+\alpha\,\mathrm{Rew}^\star(P)+\beta|\tilde X(P)|
--   $$
--
--   when $\eta(x)-\lambda(r,x)-\beta-\alpha r\mathbb 1(x=x')\ge0$ for all $x\in\tilde X(P)$, $r$, and $-\infty$ otherwise. The **dual-test function** is $\overline{\mathrm{Dual}}(\eta,x',P;\mu):=\max_{\rho\ge0}\mathrm{Dual}(\eta,x',P;\rho\mu)$.
--
--   By weak duality (Lemma 1) $\mathrm{Dual}$ lower-bounds $\mathrm{Dist}$; DUSA uses it to test cheaply whether enough information has been collected.
--
--   **Formalization Note** Values in `EReal`. A logarithmic term is $0$ when $\eta(x)P(r,x)=0$ and $-\infty$ when $\eta(x)P(r,x)\ne0$ and the argument of the logarithm is $0$ (the limits of the derivation in App. C.2).
-- source:
--   Van Parys & Golrezaei, Optimal Learning for Structured Bandits, arXiv:2007.07302v3, §5.2, pp.21–22, Eq. (14); Eq. (17), p.23; Algorithm 1, p.24

import Mathlib
import Definitions.Def_StructBandit_IsStructureSet

open scoped BigOperators

namespace StructBandit

/-- The conic hull `K = cone(S) := {θ·Q : θ ≥ 0, Q ∈ S}` of the structure set `S` (the paper's `𝒫`)
(arXiv:2007.07302v3, §5.2, p.21). -/
def coneHull {R : Finset ℝ} {X : Type*} (S : Set (R → X → ℝ)) : Set (R → X → ℝ) :=
  {Q | ∃ θ : ℝ, 0 ≤ θ ∧ ∃ Q₀ ∈ S, Q = θ • Q₀}

/-- The dual cone `K⋆ := {λ : ⟨λ,Q⟩ ≥ 0 ∀ Q ∈ K}` with `⟨λ,Q⟩ = ∑_{x∈X,r∈R} λ(r,x) Q(r,x)`
(arXiv:2007.07302v3, p.22). For a structure set `S` the cone `K` is closed and convex, so `K⋆⋆ = K` and
this is "the unique cone that satisfies `Q ∈ K` iff `⟨λ,Q⟩ ≥ 0 ∀ λ ∈ K⋆`" of p.22. -/
def dualCone {R : Finset ℝ} {X : Type*} [Fintype X] (S : Set (R → X → ℝ)) : Set (R → X → ℝ) :=
  {lam | ∀ Q ∈ coneHull S, 0 ≤ ∑ x, ∑ r, lam r x * Q r x}

/-- A dual vector `µ = (α, β, λ)` (arXiv:2007.07302v3, p.22): `α = µ.1`, `β = µ.2.1`, `λ = µ.2.2`. -/
abbrev DualVec (R : Finset ℝ) (X : Type*) : Type _ := ℝ × ℝ × (R → X → ℝ)

/-- Dual feasibility `µ ∈ ℝ₊ × ℝ × K⋆` (p.22): `α ≥ 0`, `β ∈ ℝ`, `λ ∈ K⋆`. -/
def IsDualFeasible {R : Finset ℝ} {X : Type*} [Fintype X] (S : Set (R → X → ℝ))
    (μ : DualVec R X) : Prop :=
  0 ≤ μ.1 ∧ μ.2.2 ∈ dualCone S

/-- The scaled dual vector `ρ·µ = (ρα, ρβ, ρλ)`. -/
def scaleDual {R : Finset ℝ} {X : Type*} (ρ : ℝ) (μ : DualVec R X) : DualVec R X :=
  (ρ * μ.1, ρ * μ.2.1, ρ • μ.2.2)

open Classical in
/-- The slack `ω = η(x) − λ(r,x) − β − α r 𝟙(x = x′)` inside the logarithm of (14). -/
noncomputable def dualSlack {R : Finset ℝ} {X : Type*} (η : X → ℝ) (x' : X) (μ : DualVec R X)
    (x : X) (r : R) : ℝ :=
  η x - μ.2.2 r x - μ.2.1 - μ.1 * (r : ℝ) * (if x = x' then 1 else 0)

/-- One term `η(x) log(ω/η(x)) P(r,x)` of (14), with the values the derivation of App. C.2 (p.43)
gives at the boundary: `0` when `η(x)P(r,x) = 0`, `−∞` when `η(x)P(r,x) ≠ 0` and `ω = 0`. -/
noncomputable def dualTerm {R : Finset ℝ} {X : Type*} (η : X → ℝ) (x' : X) (P : R → X → ℝ)
    (μ : DualVec R X) (x : X) (r : R) : EReal :=
  if η x * P r x = 0 then 0
  else if dualSlack η x' μ x r = 0 then ⊥
  else ((η x * Real.log (dualSlack η x' μ x r / η x) * P r x : ℝ) : EReal)

open Classical in
/-- **The dual function** `Dual(η,x′,P;µ)` (arXiv:2007.07302v3, Eq. (14), p.22):
`∑_{x∈X̃(P),r∈R} η(x) log((η(x)−λ(r,x)−β−αr𝟙(x=x′))/η(x)) P(r,x) − ∑_{x∈x⋆(P),r∈R} λ(r,x)P(r,x)
 + α Rew⋆(P) + β|X̃(P)| + χ_{−∞}(η(x) − λ(r,x) − β − αr𝟙(x=x′) ≥ 0)`.

**Formalization Note.** Values in `EReal`. The characteristic function `χ_{−∞}` is `0` when the slack
is nonnegative for every `x ∈ X̃(P)` and `r ∈ R` (the index range of the sum it closes) and `−∞`
otherwise. Each logarithmic term is `dualTerm`: `0` if `η(x)P(r,x) = 0`, `−∞` if `η(x)P(r,x) ≠ 0` and the
slack is `0`, the printed expression otherwise; Lean's `Real.log 0 = 0` decides no case. The formula is
used as printed for every `P` and `x′` (Lemma 1 applies it on `P_Ω` and DUSA at the empirical `P_t`). -/
noncomputable def dualFn {R : Finset ℝ} {X : Type*} [Fintype X] [Nonempty X] (η : X → ℝ) (x' : X)
    (P : R → X → ℝ) (μ : DualVec R X) : EReal :=
  if ∀ x ∈ subArms P, ∀ r, 0 ≤ dualSlack η x' μ x r then
    (∑ x ∈ subArms P, ∑ r, dualTerm η x' P μ x r) +
      ((-(∑ x ∈ optArms P, ∑ r, μ.2.2 r x * P r x) + μ.1 * rewStar P
        + μ.2.1 * ((subArms P).card : ℝ) : ℝ) : EReal)
  else ⊥

/-- **The dual-test function** `Dual‾(η,x,P;µ) := max_{ρ≥0} Dual(η,x,P;ρµ)` of the sufficient
information test (arXiv:2007.07302v3, Eq. (17), p.23; Algorithm 1, p.24; "dual-test function", p.25), a
supremum in `EReal`. It is also the constraint function of (18) and (19). -/
noncomputable def dualSup {R : Finset ℝ} {X : Type*} [Fintype X] [Nonempty X] (η : X → ℝ) (x' : X)
    (P : R → X → ℝ) (μ : DualVec R X) : EReal :=
  ⨆ (ρ : ℝ) (_ : 0 ≤ ρ), dualFn η x' P (scaleDual ρ μ)

end StructBandit


