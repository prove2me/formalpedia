-- Prove2me | Definitions.Def_ProbMetricStab_MixedInt_ObjectiveStability
-- name    : ProbMetricStab_MixedInt_ObjectiveStability
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:11:05.381927+00:00
-- url     : https://prove2.me/theorems/c1e341c3-ba88-485d-8571-0f21a736fcd2
-- title:
--   §1–§2, pp. 2–10, d = 0 — 𝒫(Ξ), normal integrands, v, S, v_𝒰, S_𝒰, CLM sets, 𝒫_{ℱ_𝒰}, d_{ℱ_𝒰}, ψ, ψ⁻¹, Ψ
-- statement:
--   This module fixes the objects of the general stability theory of §2 for a stochastic program **without probabilistic constraints** ($d = 0$):
--   $$
--   \min\Big\{\int_\Xi f(\xi,x)\,\nu(d\xi)\ :\ x\in X\Big\},
--   $$
--   where $X\subseteq\mathbb R^m$, $\Xi\subseteq\mathbb R^s$, $f:\Xi\times\mathbb R^m\to\overline{\mathbb R}$ and $\nu$ is a probability measure on $\Xi$.
--
--   1. $\mathcal P(\Xi)$ is the set of Borel probability measures on $\Xi$.
--   2. $f$ is a **normal integrand** on $\Xi\times\mathbb R^m$ if its epigraphical mapping $\xi\mapsto\operatorname{epi}f(\xi,\cdot)=\{(x,r)\in\mathbb R^m\times\mathbb R: f(\xi,x)\le r\}$ is closed-valued and measurable: every epigraph is closed, and for every open $O\subseteq\mathbb R^m\times\mathbb R$ the set $\{\xi\in\Xi:\operatorname{epi}f(\xi,\cdot)\cap O\ne\emptyset\}$ is Borel.
--   3. For $\nu\in\mathcal P(\Xi)$ and a nonempty $\mathcal U\subseteq\mathbb R^m$: the optimal value $v(\nu)=\inf\{\int_\Xi f(\xi,x)\nu(d\xi):x\in X\}$, the solution set $S(\nu)=\{x\in X:\int_\Xi f(\xi,x)\nu(d\xi)=v(\nu)\}$, and their localized versions $v_{\mathcal U}(\nu)$, $S_{\mathcal U}(\nu)$, where $X$ is replaced by $X\cap\operatorname{cl}\mathcal U$.
--   4. $S_{\mathcal U}(\nu)$ is a **complete local minimizing (CLM) set** with respect to $\mathcal U$ if $\mathcal U$ is open and $\emptyset\ne S_{\mathcal U}(\nu)\subseteq\mathcal U$.
--   5. The class
--   $$
--   \mathcal P_{\mathcal F_{\mathcal U}}(\Xi)=\Big\{\nu\in\mathcal P(\Xi):\ -\infty<\int_\Xi\inf_{x\in X,\ \|x\|\le r}f(\xi,x)\,\nu(d\xi)\ \text{for each } r>0,\ \ \sup_{x\in X\cap\operatorname{cl}\mathcal U}\int_\Xi f(\xi,x)\,\nu(d\xi)<\infty\Big\}
--   $$
--   and the **minimal information distance** $d_{\mathcal F_{\mathcal U}}(\mu,\nu)=\sup_{x\in X\cap\operatorname{cl}\mathcal U}\big|\int_\Xi f(\xi,x)(\mu-\nu)(d\xi)\big|$.
--   6. The **growth function** $\psi(\tau)=\inf\{\int_\Xi f(\xi,x)\mu(d\xi)-v(\mu): d(x,S(\mu))\ge\tau,\ x\in X\cap\operatorname{cl}\mathcal U\}$ for $\tau\ge0$, its generalized inverse $\psi^{-1}(t)=\sup\{\tau\ge0:\psi(\tau)\le t\}$, and the two moduli $\Psi(\eta)=\eta+\psi^{-1}(\eta)$ (Theorem 2.3) and $\Psi(\eta)=\eta+\psi^{-1}(2\eta)$ (Corollary 2.8).
--   7. $A+R\mathbb B=\{a+b: a\in A,\ \|b\|\le R\}$, with $\mathbb B$ the closed unit ball.
--
--   These are the objects in which Theorems 2.2 and 2.3 are stated; the mixed-integer program (9) is one instance, with $f=f_0$.
--
--   **Formalization Note** $\mathbb R^m$ and $\mathbb R^s$ are Euclidean spaces (the paper leaves the norm open, and every statement of this mission has existential constants). A measure in $\mathcal P(\Xi)$ is a Borel probability measure on $\mathbb R^s$ with $\nu(\mathbb R^s\setminus\Xi)=0$, and integrands are defined on all of $\mathbb R^s\times\mathbb R^m$; their values off $\Xi$ do not affect any integral. The integral of an extended-real integrand is the published `DupacovaWets.Consistency.expect`: $+\infty$ if $\int f^+=\infty$, otherwise $\int f^+-\int f^-$. Optimal values and $\psi$ are extended-real infima, equal to $+\infty$ on an empty set; the paper's "min" in $\psi$ is read as an infimum. The distance $d(x,A)$ is the extended distance (infinite for $A=\emptyset$), and $d_{\mathcal F_{\mathcal U}}$, $\psi^{-1}$, $\Psi$ take values in $[0,\infty]$.
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), p. 2 (normal integrands, 𝒫(Ξ), v, S), p. 4 (ℱ_𝒰, 𝒫_{ℱ_𝒰}, d_{ℱ_𝒰}), p. 5 (v_𝒰, S_𝒰), p. 6 (CLM set), p. 8 (Theorem 2.3: ψ, ψ⁻¹, Ψ), p. 10 (Corollary 2.8: Ψ(η) = η + ψ⁻¹(2η)); case d = 0

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_ProbMetricStab_TwoStage_Setting

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbMetricStab.MixedInt

/-! Rachev & Römisch, *Quantitative stability in stochastic programming: The method of probability
metrics*, preprint, §1 (p. 2) and §2 (pp. 4–10), for an objective-only program (`d = 0`):
`min { ∫_Ξ f(ξ, x) ν(dξ) : x ∈ X }` with an extended-real normal integrand `f`.

Conventions: `ℝ^m`, `ℝ^s` are `EuclideanSpace ℝ (Fin m)`, `EuclideanSpace ℝ (Fin s)`; a measure in
`𝒫(Ξ)` is a Borel probability measure on `ℝ^s` with `ν Ξᶜ = 0`; the integral `∫_Ξ f(ξ, x) ν(dξ)` of an
extended-real integrand is the published `DupacovaWets.Consistency.expect` (`+∞` when `∫ f⁺ = ∞`,
else `∫ f⁺ − ∫ f⁻`); optimal values are `EReal` infima (`+∞` on an empty feasible set); distances
are `ℝ≥0∞`-valued. -/

/-- `𝒫(Ξ)` (p. 2): Borel probability measures on `ℝ^s` that are concentrated on `Ξ`. -/
def ProbOn {s : ℕ} (Ξ : Set (EuclideanSpace ℝ (Fin s))) : Set (Measure (EuclideanSpace ℝ (Fin s))) :=
  {ν | IsProbabilityMeasure ν ∧ ν Ξᶜ = 0}

variable {m s : ℕ}

/-- `∫_Ξ f(ξ, x) ν(dξ)`, the extended-real expectation of the integrand at the decision `x`. -/
noncomputable def intObj (f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal)
    (ν : Measure (EuclideanSpace ℝ (Fin s))) (x : EuclideanSpace ℝ (Fin m)) : EReal :=
  DupacovaWets.Consistency.expect ν (fun ξ => f ξ x)

/-- Optimal value `v(ν) = inf { ∫_Ξ f(ξ, x) ν(dξ) : x ∈ X }` (p. 2 with `d = 0`). -/
noncomputable def optVal (f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal)
    (X : Set (EuclideanSpace ℝ (Fin m))) (ν : Measure (EuclideanSpace ℝ (Fin s))) : EReal :=
  ⨅ x ∈ X, intObj f ν x

/-- Solution set `S(ν) = { x ∈ X : ∫_Ξ f(ξ, x) ν(dξ) = v(ν) }` (p. 2). -/
def solSet (f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal)
    (X : Set (EuclideanSpace ℝ (Fin m))) (ν : Measure (EuclideanSpace ℝ (Fin s))) :
    Set (EuclideanSpace ℝ (Fin m)) :=
  {x | x ∈ X ∧ intObj f ν x = optVal f X ν}

/-- Localized optimal value `v_𝒰(ν) = inf { ∫_Ξ f(ξ, x) ν(dξ) : x ∈ X ∩ cl 𝒰 }` (p. 5; for
`d = 0`, `M_𝒰(ν) = X ∩ cl 𝒰`). -/
noncomputable def locOptVal (f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal)
    (X U : Set (EuclideanSpace ℝ (Fin m))) (ν : Measure (EuclideanSpace ℝ (Fin s))) : EReal :=
  ⨅ x ∈ X ∩ closure U, intObj f ν x

/-- Localized solution set `S_𝒰(ν) = { x ∈ X ∩ cl 𝒰 : ∫_Ξ f(ξ, x) ν(dξ) = v_𝒰(ν) }` (p. 5). -/
def locSolSet (f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal)
    (X U : Set (EuclideanSpace ℝ (Fin m))) (ν : Measure (EuclideanSpace ℝ (Fin s))) :
    Set (EuclideanSpace ℝ (Fin m)) :=
  {x | x ∈ X ∩ closure U ∧ intObj f ν x = locOptVal f X U ν}

/-- `S_𝒰(ν)` is a complete local minimizing (CLM) set with respect to `𝒰` (p. 6): `𝒰` is open and
`S_𝒰(ν)` is nonempty and contained in `𝒰`. -/
def IsCLMSet (f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal)
    (X U : Set (EuclideanSpace ℝ (Fin m))) (ν : Measure (EuclideanSpace ℝ (Fin s))) : Prop :=
  IsOpen U ∧ (locSolSet f X U ν).Nonempty ∧ locSolSet f X U ν ⊆ U

/-- `𝒫_{ℱ_𝒰}(Ξ)` (p. 4, `d = 0`): the measures `ν ∈ 𝒫(Ξ)` with
`−∞ < ∫_Ξ inf_{x ∈ X, ‖x‖ ≤ r} f(ξ, x) ν(dξ)` for each `r > 0` and
`sup_{x ∈ X ∩ cl 𝒰} ∫_Ξ f(ξ, x) ν(dξ) < ∞`. -/
def PFU (Ξ : Set (EuclideanSpace ℝ (Fin s)))
    (f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal)
    (X U : Set (EuclideanSpace ℝ (Fin m))) : Set (Measure (EuclideanSpace ℝ (Fin s))) :=
  {ν | ν ∈ ProbOn Ξ ∧
    (∀ r : ℝ, 0 < r →
      ⊥ < DupacovaWets.Consistency.expect ν
        (fun ξ => ⨅ x ∈ X ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) r, f ξ x)) ∧
    (⨆ x ∈ X ∩ closure U, intObj f ν x) < ⊤}

/-- The minimal information distance `d_{ℱ_𝒰}(μ, ν) = sup_{x ∈ X ∩ cl 𝒰} |∫_Ξ f(ξ, x)(μ − ν)(dξ)|`
(p. 4, `d = 0`), valued in `ℝ≥0∞`. -/
noncomputable def dFU (f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal)
    (X U : Set (EuclideanSpace ℝ (Fin m))) (μ ν : Measure (EuclideanSpace ℝ (Fin s))) : ℝ≥0∞ :=
  ⨆ x ∈ X ∩ closure U, EReal.abs (intObj f μ x - intObj f ν x)

/-- `A + R𝔹 = { a + b : a ∈ A, ‖b‖ ≤ R }` with `𝔹` the closed unit ball, for a radius
`R ∈ [0, ∞]`. -/
def addBall (A : Set (EuclideanSpace ℝ (Fin m))) (R : ℝ≥0∞) : Set (EuclideanSpace ℝ (Fin m)) :=
  {x | ∃ a ∈ A, edist x a ≤ R}

/-- The growth function of the problem on `cl 𝒰` (Theorem 2.3, p. 8, and Corollary 2.8, p. 10,
`d = 0`): `ψ(τ) = inf { ∫_Ξ f(ξ, x) μ(dξ) − v(μ) : d(x, S(μ)) ≥ τ, x ∈ X ∩ cl 𝒰 }` for `τ ∈ ℝ₊`,
an `EReal` infimum (`+∞` when no feasible point is `τ`-far from `S(μ)`). -/
noncomputable def growthFn (f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal)
    (X U : Set (EuclideanSpace ℝ (Fin m))) (μ : Measure (EuclideanSpace ℝ (Fin s))) (τ : ℝ≥0) :
    EReal :=
  ⨅ x ∈ {x | x ∈ X ∩ closure U ∧ (τ : ℝ≥0∞) ≤ Metric.infEDist x (solSet f X μ)},
    (intObj f μ x - optVal f X μ)

/-- `ψ⁻¹(t) = sup { τ ∈ ℝ₊ : ψ(τ) ≤ t }` (p. 8), valued in `ℝ≥0∞`. -/
noncomputable def growthInv (f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal)
    (X U : Set (EuclideanSpace ℝ (Fin m))) (μ : Measure (EuclideanSpace ℝ (Fin s))) (t : ℝ≥0∞) :
    ℝ≥0∞ :=
  ⨆ (τ : ℝ≥0) (_ : growthFn f X U μ τ ≤ (t : EReal)), (τ : ℝ≥0∞)

/-- `Ψ(η) = η + ψ⁻¹(η)` of Theorem 2.3 (p. 8). -/
noncomputable def PsiThm23 (f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal)
    (X U : Set (EuclideanSpace ℝ (Fin m))) (μ : Measure (EuclideanSpace ℝ (Fin s))) (η : ℝ≥0∞) :
    ℝ≥0∞ :=
  η + growthInv f X U μ η

/-- `Ψ(η) = η + ψ⁻¹(2η)` of Corollary 2.8 (p. 10). -/
noncomputable def PsiCor28 (f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal)
    (X U : Set (EuclideanSpace ℝ (Fin m))) (μ : Measure (EuclideanSpace ℝ (Fin s))) (η : ℝ≥0∞) :
    ℝ≥0∞ :=
  η + growthInv f X U μ (2 * η)

end ProbMetricStab.MixedInt


