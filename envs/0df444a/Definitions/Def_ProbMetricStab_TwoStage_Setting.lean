-- Prove2me | Definitions.Def_ProbMetricStab_TwoStage_Setting
-- name    : ProbMetricStab_TwoStage_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:04:02.167972+00:00
-- url     : https://prove2.me/theorems/3b4c40c9-367a-434c-a541-b8de648ccaf8
-- title:
--   §1–§2, pp. 2–10 — model (1) with d = 0, normal integrands, 𝒫_p, ζ_p, ℱ_g, ζ_g, 𝒫_g, 𝒫_{ℱ_𝒰}, v, S, ψ, Ψ
-- statement:
--   This module fixes the general objects of Rachev and Römisch's stability theory that the linear two-stage mission uses: the stochastic program (1) with only an objective ($d=0$), its optimal value and solution set, the Fortet–Mourier metrics, and the growth function of Corollary 2.8.
--
--   Throughout, $\Xi\subseteq\mathbb R^s$ and $X\subseteq\mathbb R^m$, and $f_0:\Xi\times\mathbb R^m\to\overline{\mathbb R}$ is an extended-real integrand.
--
--   1. **Polyhedra.** A set in $\mathbb R^n$ is a polyhedron if it is a finite intersection of closed half-spaces $\{x:\langle a_i,x\rangle\le b_i\}$.
--   2. **Normal integrands** (p. 2). $f_0$ is a normal integrand if its epigraphical mapping $\xi\mapsto\operatorname{epi}f_0(\xi,\cdot)=\{(x,r)\in\mathbb R^m\times\mathbb R: f_0(\xi,x)\le r\}$ is closed-valued and measurable: each $\operatorname{epi}f_0(\xi,\cdot)$ is closed, and for every open $O\subseteq\mathbb R^m\times\mathbb R$ the set $\{\xi\in\Xi:\operatorname{epi}f_0(\xi,\cdot)\cap O\ne\emptyset\}$ is Borel. It is a normal convex integrand if moreover every $f_0(\xi,\cdot)$ is convex (has a convex epigraph).
--   3. **Measures** (pp. 2–3). $\mathcal P(\Xi)$ is the set of Borel probability measures on $\Xi$, and for $p\ge1$
--   $$\mathcal P_p(\Xi)=\Big\{\nu\in\mathcal P(\Xi):\int_\Xi\|\xi\|^p\,\nu(d\xi)<\infty\Big\}.$$
--   4. **Fortet–Mourier metric** (p. 3). With $\mathcal F_p(\Xi)=\{f:\Xi\to\mathbb R:\ |f(\xi)-f(\tilde\xi)|\le\max\{1,\|\xi\|^{p-1},\|\tilde\xi\|^{p-1}\}\|\xi-\tilde\xi\|\ \forall\xi,\tilde\xi\in\Xi\}$,
--   $$\zeta_p(\mu,\nu)=\sup_{f\in\mathcal F_p(\Xi)}\Big|\int_\Xi f(\xi)\,(\mu-\nu)(d\xi)\Big|.$$
--   5. **The class $\mathcal F_g$** (p. 10). For $\xi_0\in\Xi$ and $g:\mathbb R_+\to\mathbb R_+$, $\mathcal F_g(\Xi)$ is the set of $f$ with $|f(\xi)-f(\tilde\xi)|\le\max\{1,g(\|\xi-\xi_0\|),g(\|\tilde\xi-\xi_0\|)\}\|\xi-\tilde\xi\|$ on $\Xi$; $\zeta_g$ is the corresponding distance, and $\mathcal P_g(\Xi)=\{\nu\in\mathcal P(\Xi):\int_\Xi\max\{1,g(\|\xi\|)\}\|\xi\|\,\nu(d\xi)<\infty\}$.
--   6. **Optimal value and solution set** (p. 2, $d=0$). $v(\nu)=\inf\{\int_\Xi f_0(\xi,x)\,\nu(d\xi):x\in X\}$ and $S(\nu)=\{x\in X:\int_\Xi f_0(\xi,x)\,\nu(d\xi)=v(\nu)\}$.
--   7. **$\mathcal P_{\mathcal F_{\mathcal U}}(\Xi)$** (p. 4, $d=0$). For $\mathcal U\subseteq\mathbb R^m$, the $\nu\in\mathcal P(\Xi)$ with $-\infty<\int_\Xi\inf_{x\in X,\|x\|\le r}f_0(\xi,x)\,\nu(d\xi)$ for each $r>0$ and $\sup_{x\in X\cap\operatorname{cl}\mathcal U}\int_\Xi f_0(\xi,x)\,\nu(d\xi)<\infty$.
--   8. **Growth function** (Corollary 2.8, p. 10). For $\tau\ge0$,
--   $$\psi(\tau)=\min\Big\{\int_\Xi f_0(\xi,x)\,\mu(d\xi)-v(\mu):\ d(x,S(\mu))\ge\tau,\ x\in X\cap\operatorname{cl}\mathcal U\Big\},$$
--   $\psi^{-1}(t)=\sup\{\tau\ge0:\psi(\tau)\le t\}$ and $\Psi(\eta)=\eta+\psi^{-1}(2\eta)$.
--
--   These are the vocabulary of Corollary 2.8 and of Theorem 3.3: the distance in which the two-stage program is stable, and the function $\Psi$ that measures how far solution sets move.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`; the paper never fixes its norm and all its statements carry existential constants, so the Euclidean norm is a faithful instance. A measure in $\mathcal P(\Xi)$ is a Borel probability measure on $\mathbb R^s$ with $\nu(\Xi^c)=0$, and $\int_\Xi$ integrates over $\nu$ restricted to $\Xi$. Integrals of $\overline{\mathbb R}$-valued integrands use the published `DupacovaWets.Consistency.expect` ($+\infty$ when the positive part has infinite integral). Moments are lower Lebesgue integrals in $[0,\infty]$. In $\zeta_p$ and $\zeta_g$ the term of a test function that is not integrable on $\Xi$ for both measures is $+\infty$, so an undefined integral is never read as $0$; on $\mathcal P_p(\Xi)$ every $f\in\mathcal F_p(\Xi)$ is integrable and the convention never triggers. $v$, $\psi$ are infima in $\overline{\mathbb R}$ ($+\infty$ over an empty set), so the paper's "min" in $\psi$ is read as an infimum; $d(x,A)$ is the extended distance ($+\infty$ for $A=\emptyset$); $\psi^{-1}$ and $\Psi$ take values in $[0,\infty]$; $g$ is a map $\mathbb R_{\ge0}\to\mathbb R_{\ge0}$.
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), pp. 2–4 and 10, (1), (2), definition of ζ_p, 𝒫_{ℱ_𝒰}, Corollary 2.8

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbMetricStab.TwoStage

/-- A polyhedron in `ℝ^n` (pp. 10–11): a finite intersection of closed half-spaces
`{x | ⟨a_i, x⟩ ≤ b_i}`, `i ∈ Fin k` (`k = 0` gives the whole space). -/
def IsPolyhedron {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ (k : ℕ) (a : Fin k → EuclideanSpace ℝ (Fin n)) (b : Fin k → ℝ),
    P = {x | ∀ i, inner ℝ (a i) x ≤ b i}

/-- The epigraph `epi f(ξ, ·) = {(x, r) ∈ ℝ^m × ℝ : f(ξ, x) ≤ r}` of an extended-real function
on `ℝ^m` (p. 2). -/
def epi {m : ℕ} (φ : EuclideanSpace ℝ (Fin m) → EReal) : Set (EuclideanSpace ℝ (Fin m) × ℝ) :=
  {p | φ p.1 ≤ (p.2 : EReal)}

/-- Normal integrand (p. 2, after (1)): `f : Ξ × ℝ^m → ℝ̄` is a normal integrand if its
epigraphical mapping `ξ ↦ epi f(ξ, ·)` is closed-valued and measurable, i.e. `epi f(ξ, ·)` is
closed for every `ξ ∈ Ξ`, and for every open `O ⊆ ℝ^m × ℝ` the set `{ξ ∈ Ξ : epi f(ξ, ·) ∩ O ≠ ∅}`
is a Borel set. Only the values of `f` on `Ξ × ℝ^m` matter. -/
def IsNormalIntegrand {m s : ℕ} (Ξ : Set (EuclideanSpace ℝ (Fin s)))
    (f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal) : Prop :=
  (∀ ξ ∈ Ξ, IsClosed (epi (f ξ))) ∧
  ∀ O : Set (EuclideanSpace ℝ (Fin m) × ℝ), IsOpen O →
    MeasurableSet {ξ | ξ ∈ Ξ ∧ (epi (f ξ) ∩ O).Nonempty}

/-- Normal convex integrand (Proposition 3.2, p. 11): a normal integrand with `f(ξ, ·)` convex
for each `ξ ∈ Ξ`, convexity of an extended-real function meaning convexity of its epigraph. -/
def IsNormalConvexIntegrand {m s : ℕ} (Ξ : Set (EuclideanSpace ℝ (Fin s)))
    (f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal) : Prop :=
  IsNormalIntegrand Ξ f ∧ ∀ ξ ∈ Ξ, Convex ℝ (epi (f ξ))

/-- `ν ∈ 𝒫(Ξ)` (p. 2): `ν` is a Borel probability measure on `ℝ^s` concentrated on `Ξ`. -/
def IsProbOn {s : ℕ} (Ξ : Set (EuclideanSpace ℝ (Fin s)))
    (ν : Measure (EuclideanSpace ℝ (Fin s))) : Prop :=
  IsProbabilityMeasure ν ∧ ν Ξᶜ = 0

/-- `𝒫_p(Ξ) = {ν ∈ 𝒫(Ξ) : ∫_Ξ ‖ξ‖^p ν(dξ) < ∞}` (p. 3). -/
def Pp {s : ℕ} (Ξ : Set (EuclideanSpace ℝ (Fin s))) (p : ℝ) :
    Set (Measure (EuclideanSpace ℝ (Fin s))) :=
  {ν | IsProbOn Ξ ν ∧ ∫⁻ ξ in Ξ, (‖ξ‖₊ : ℝ≥0∞) ^ p ∂ν < ∞}

/-- The Fortet–Mourier class (p. 3)
`ℱ_p(Ξ) = {f : Ξ → ℝ : |f(ξ) − f(ξ̃)| ≤ max{1, ‖ξ‖^{p−1}, ‖ξ̃‖^{p−1}} ‖ξ − ξ̃‖ ∀ ξ, ξ̃ ∈ Ξ}`;
a function on `ℝ^s` whose values on `Ξ` satisfy the inequality. -/
def Fp {s : ℕ} (Ξ : Set (EuclideanSpace ℝ (Fin s))) (p : ℝ) :
    Set (EuclideanSpace ℝ (Fin s) → ℝ) :=
  {f | ∀ ξ ∈ Ξ, ∀ ξ' ∈ Ξ,
    |f ξ - f ξ'| ≤ max 1 (max (‖ξ‖ ^ (p - 1)) (‖ξ'‖ ^ (p - 1))) * ‖ξ - ξ'‖}

/-- The term `|∫_Ξ f(ξ)(μ − ν)(dξ)|` of a ζ-structure distance, valued in `[0, ∞]`. It is the
absolute difference of the Bochner integrals over `Ξ` when `f` is integrable on `Ξ` with respect
to both measures, and `+∞` otherwise (so that no undefined integral is read as `0`). -/
noncomputable def zetaTerm {s : ℕ} (Ξ : Set (EuclideanSpace ℝ (Fin s)))
    (μ ν : Measure (EuclideanSpace ℝ (Fin s))) (f : EuclideanSpace ℝ (Fin s) → ℝ) : ℝ≥0∞ :=
  open Classical in
  if IntegrableOn f Ξ μ ∧ IntegrableOn f Ξ ν then
    ‖(∫ ξ in Ξ, f ξ ∂μ) - ∫ ξ in Ξ, f ξ ∂ν‖ₑ
  else ⊤

/-- The Fortet–Mourier metric of order `p` (p. 3):
`ζ_p(μ, ν) = sup_{f ∈ ℱ_p(Ξ)} |∫_Ξ f(ξ)(μ − ν)(dξ)|`, valued in `[0, ∞]`. -/
noncomputable def zetaP {s : ℕ} (Ξ : Set (EuclideanSpace ℝ (Fin s))) (p : ℝ)
    (μ ν : Measure (EuclideanSpace ℝ (Fin s))) : ℝ≥0∞ :=
  ⨆ f ∈ Fp Ξ p, zetaTerm Ξ μ ν f

/-- The class (p. 10), for `ξ₀ ∈ Ξ` and `g : ℝ₊ → ℝ₊`:
`ℱ_g(Ξ) = {f : |f(ξ) − f(ξ̃)| ≤ max{1, g(‖ξ − ξ₀‖), g(‖ξ̃ − ξ₀‖)} ‖ξ − ξ̃‖ ∀ ξ, ξ̃ ∈ Ξ}`. -/
def Fg {s : ℕ} (Ξ : Set (EuclideanSpace ℝ (Fin s))) (ξ₀ : EuclideanSpace ℝ (Fin s))
    (g : ℝ≥0 → ℝ≥0) : Set (EuclideanSpace ℝ (Fin s) → ℝ) :=
  {f | ∀ ξ ∈ Ξ, ∀ ξ' ∈ Ξ,
    |f ξ - f ξ'| ≤ max 1 (max (g ‖ξ - ξ₀‖₊ : ℝ) (g ‖ξ' - ξ₀‖₊ : ℝ)) * ‖ξ - ξ'‖}

/-- `ζ_g(μ, ν) = d_{ℱ_g(Ξ)}(μ, ν) = sup_{f ∈ ℱ_g(Ξ)} |∫_Ξ f(ξ)(μ − ν)(dξ)|` (p. 10). -/
noncomputable def zetaG {s : ℕ} (Ξ : Set (EuclideanSpace ℝ (Fin s))) (ξ₀ : EuclideanSpace ℝ (Fin s))
    (g : ℝ≥0 → ℝ≥0) (μ ν : Measure (EuclideanSpace ℝ (Fin s))) : ℝ≥0∞ :=
  ⨆ f ∈ Fg Ξ ξ₀ g, zetaTerm Ξ μ ν f

/-- `𝒫_g(Ξ) = {ν ∈ 𝒫(Ξ) : ∫_Ξ max{1, g(‖ξ‖)} ‖ξ‖ ν(dξ) < ∞}` (p. 10). -/
def Pg {s : ℕ} (Ξ : Set (EuclideanSpace ℝ (Fin s))) (g : ℝ≥0 → ℝ≥0) :
    Set (Measure (EuclideanSpace ℝ (Fin s))) :=
  {ν | IsProbOn Ξ ν ∧ ∫⁻ ξ in Ξ, ((max 1 (g ‖ξ‖₊) * ‖ξ‖₊ : ℝ≥0) : ℝ≥0∞) ∂ν < ∞}

/-! ### Model (1) with `d = 0`: `min {∫_Ξ f₀(ξ, x) ν(dξ) : x ∈ X}` -/

/-- The objective `∫_Ξ f₀(ξ, x) ν(dξ)` of (1)/(3) for `d = 0`, as an extended real
(`+∞` when the positive part has infinite integral). -/
noncomputable def objective {m s : ℕ} (Ξ : Set (EuclideanSpace ℝ (Fin s)))
    (f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal)
    (ν : Measure (EuclideanSpace ℝ (Fin s))) (x : EuclideanSpace ℝ (Fin m)) : EReal :=
  DupacovaWets.Consistency.expect (ν.restrict Ξ) (fun ξ => f ξ x)

/-- The optimal value `v(ν) = inf {∫_Ξ f₀(ξ, x) ν(dξ) : x ∈ X}` (p. 2, `d = 0`), `+∞` on `X = ∅`. -/
noncomputable def v {m s : ℕ} (X : Set (EuclideanSpace ℝ (Fin m)))
    (Ξ : Set (EuclideanSpace ℝ (Fin s)))
    (f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal)
    (ν : Measure (EuclideanSpace ℝ (Fin s))) : EReal :=
  ⨅ x ∈ X, objective Ξ f ν x

/-- The solution set `S(ν) = {x ∈ X : ∫_Ξ f₀(ξ, x) ν(dξ) = v(ν)}` (p. 2, `d = 0`). -/
def S {m s : ℕ} (X : Set (EuclideanSpace ℝ (Fin m))) (Ξ : Set (EuclideanSpace ℝ (Fin s)))
    (f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal)
    (ν : Measure (EuclideanSpace ℝ (Fin s))) : Set (EuclideanSpace ℝ (Fin m)) :=
  {x | x ∈ X ∧ objective Ξ f ν x = v X Ξ f ν}

/-- `𝒫_{ℱ_𝒰}(Ξ)` for `d = 0` (p. 4): the `ν ∈ 𝒫(Ξ)` with
`−∞ < ∫_Ξ inf_{x ∈ X, ‖x‖ ≤ r} f₀(ξ, x) ν(dξ)` for each `r > 0` and
`sup_{x ∈ X ∩ cl 𝒰} ∫_Ξ f₀(ξ, x) ν(dξ) < ∞`. -/
def PFU {m s : ℕ} (X : Set (EuclideanSpace ℝ (Fin m))) (Ξ : Set (EuclideanSpace ℝ (Fin s)))
    (f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal)
    (U : Set (EuclideanSpace ℝ (Fin m))) : Set (Measure (EuclideanSpace ℝ (Fin s))) :=
  {ν | IsProbOn Ξ ν ∧
    (∀ r : ℝ, 0 < r →
      ⊥ < DupacovaWets.Consistency.expect (ν.restrict Ξ)
        (fun ξ => ⨅ x ∈ {x : EuclideanSpace ℝ (Fin m) | x ∈ X ∧ ‖x‖ ≤ r}, f ξ x)) ∧
    (⨆ x ∈ X ∩ closure U, objective Ξ f ν x) < ⊤}

/-- The growth function of Corollary 2.8 (p. 10), for `τ ∈ ℝ₊`:
`ψ(τ) = min {∫_Ξ f₀(ξ, x) μ(dξ) − v(μ) : d(x, S(μ)) ≥ τ, x ∈ X ∩ cl 𝒰}`, read as an infimum
in `ℝ̄` (`+∞` when no point of `X ∩ cl 𝒰` is `τ`-far from `S(μ)`); `d(x, S(μ))` is the
extended distance, `+∞` when `S(μ) = ∅`. -/
noncomputable def psi {m s : ℕ} (X : Set (EuclideanSpace ℝ (Fin m)))
    (Ξ : Set (EuclideanSpace ℝ (Fin s)))
    (f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal)
    (μ : Measure (EuclideanSpace ℝ (Fin s))) (U : Set (EuclideanSpace ℝ (Fin m))) (τ : ℝ≥0) :
    EReal :=
  ⨅ x ∈ {x : EuclideanSpace ℝ (Fin m) |
      x ∈ X ∧ x ∈ closure U ∧ (τ : ℝ≥0∞) ≤ Metric.infEDist x (S X Ξ f μ)},
    (objective Ξ f μ x - v X Ξ f μ)

/-- The generalized inverse `ψ^{-1}(t) = sup {τ ∈ ℝ₊ : ψ(τ) ≤ t}`, valued in `[0, ∞]`. -/
noncomputable def psiInv {m s : ℕ} (X : Set (EuclideanSpace ℝ (Fin m)))
    (Ξ : Set (EuclideanSpace ℝ (Fin s)))
    (f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal)
    (μ : Measure (EuclideanSpace ℝ (Fin s))) (U : Set (EuclideanSpace ℝ (Fin m))) (t : ℝ≥0∞) :
    ℝ≥0∞ :=
  ⨆ τ ∈ {τ : ℝ≥0 | psi X Ξ f μ U τ ≤ (t : EReal)}, (τ : ℝ≥0∞)

/-- `Ψ(η) = η + ψ^{-1}(2η)` of Corollary 2.8 (p. 10), valued in `[0, ∞]`. -/
noncomputable def Psi {m s : ℕ} (X : Set (EuclideanSpace ℝ (Fin m)))
    (Ξ : Set (EuclideanSpace ℝ (Fin s)))
    (f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal)
    (μ : Measure (EuclideanSpace ℝ (Fin s))) (U : Set (EuclideanSpace ℝ (Fin m))) (η : ℝ≥0∞) :
    ℝ≥0∞ :=
  η + psiInv X Ξ f μ U (2 * η)

end ProbMetricStab.TwoStage


