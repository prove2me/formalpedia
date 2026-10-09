-- Prove2me | Definitions.Def_FastCLO_ETO_Model
-- name    : FastCLO_ETO_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T05:16:13.956479+00:00
-- url     : https://prove2.me/theorems/07fdd8b4-7626-4f3b-810e-2ff026d0bc58
-- title:
--   Optimal value, optimal set Z*(x), gap Δ(x), the noise condition (7), policies into Z∠, plug-in policies (3) and the regret (2)
-- statement:
--   Fix a polytope $\mathcal Z$ with norm bound $B$ and extreme points $\mathcal Z^\angle$, and an instance with feature law $\mathbb P_X$ and regression function $f^*$.
--
--   1. The **optimal value** at $x$ is $\inf_{z \in \mathcal Z} f^*(x)^\top z$, and the **optimal set** is $\mathcal Z^*(x) = \{z \in \mathcal Z : f^*(x)^\top z \le f^*(x)^\top z' \text{ for all } z' \in \mathcal Z\}$.
--   2. The **gap** is $\Delta(x) = \inf_{z \in \mathcal Z^\angle \setminus \mathcal Z^*(x)} f^*(x)^\top z - \inf_{z \in \mathcal Z} f^*(x)^\top z$ if $\mathcal Z^*(x) \ne \mathcal Z$, and $\Delta(x) = 0$ otherwise.
--   3. The **noise condition** (Assumption 2) with parameters $\alpha, \gamma$ holds if
--   $$\mathbb P_X\bigl(0 < \Delta(X) \le \delta\bigr) \le (\gamma\delta/B)^\alpha \qquad \text{for all } \delta > 0.$$
--   4. A **policy** is a map $\pi : \mathbb R^p \to \mathcal Z^\angle$.
--   5. For a map $f : \mathbb R^p \to \mathbb R^d$ (an estimate of $f^*$), a **plug-$f$-in policy** is a policy $\pi_f$ with $\pi_f(x) \in \arg\min_{z \in \mathcal Z} f(x)^\top z$ for every $x$.
--   6. A data-driven policy assigns to every data set $\mathcal D$ of size $n$ a policy $\hat\pi_{\mathcal D}$; its **regret** is
--   $$\mathrm{Regret}(\hat\pi) = \mathbb E_{\mathcal D}\,\mathbb E_X\Bigl[f^*(X)^\top \hat\pi_{\mathcal D}(X) - \min_{z \in \mathcal Z} f^*(X)^\top z\Bigr],$$
--   with $\mathcal D \sim \mathbb P^n$ and $X \sim \mathbb P_X$ independent.
--
--   The noise condition measures how much mass of $X$ sits near dual degeneracy; the plug-in policy is the estimate-then-optimize (ETO) decision rule whose regret the mission bounds.
--
--   **Formalization Note** The infima are real infima of nonempty bounded sets: $\mathcal Z$ is nonempty and bounded, and when $\mathcal Z^*(x) \ne \mathcal Z$ the finite set $\mathcal Z^\angle \setminus \mathcal Z^*(x)$ is nonempty (if all extreme points were optimal, all of $\mathcal Z = \mathrm{conv}\,\mathcal Z^\angle$ would be). The probability in the noise condition is an extended nonnegative real compared with $(\gamma\delta/B)^\alpha$ as a real power, with $0^0 = 1$ at $\alpha = 0$. The paper restricts plug-in policies to selections that break ties consistently by an ordering of $\mathcal Z^\angle$; the definition admits any selection from the argmin with values in $\mathcal Z^\angle$, so upper bounds proved for it cover the paper's. The paper writes the regret as $\mathbb E_{\mathcal D}\mathbb E_X[f^*(X)^\top(\hat\pi(X) - \pi^*(X))]$; since $\pi^*(x) \in \mathcal Z^*(x)$ this is the same quantity.
-- source:
--   Hu, Kallus, Mao, Fast Rates for Contextual Linear Optimization, arXiv:2011.03030v3, Eq. (1)–(3), pp. 1–2; Assumption 2 (Eq. (7)), p. 8

import Mathlib
import Definitions.Def_FastCLO_ETO_Instance
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace FastCLO.ETO

variable {p d : ℕ}

/-- The optimal value `inf_{z ∈ Z} f*(x)ᵀ z` of the conditional problem at `x`
(arXiv:2011.03030v3, Eq. (1), p. 1).

Formalization Note: the real `sInf` is taken over the image of the nonempty bounded set `Z` under a
continuous linear map, so it is a genuine infimum (indeed a minimum). -/
noncomputable def optVal (P : Polytope d) (I : Instance p d) (x : FastCLO.ERM.Vec p) : ℝ :=
  sInf ((fun z => ⟪I.fstar x, z⟫_ℝ) '' P.Z)

/-- The set `Z*(x) = argmin_{z ∈ Z} f*(x)ᵀ z` of optimal decisions at `x` (arXiv:2011.03030v3,
§1, pp. 1–2). -/
def Zstar (P : Polytope d) (I : Instance p d) (x : FastCLO.ERM.Vec p) : Set (FastCLO.ERM.Vec d) :=
  {z ∈ P.Z | ∀ z' ∈ P.Z, ⟪I.fstar x, z⟫_ℝ ≤ ⟪I.fstar x, z'⟫_ℝ}

/-- The suboptimality gap `Δ(x)` of Assumption 2 (arXiv:2011.03030v3, p. 8):
`Δ(x) = inf_{z ∈ Z∠ \ Z*(x)} f*(x)ᵀ z − inf_{z ∈ Z} f*(x)ᵀ z` if `Z*(x) ≠ Z`, and `Δ(x) = 0`
otherwise.

Formalization Note: when `Z*(x) ≠ Z` the set `Z∠ \ Z*(x)` is nonempty (if every extreme point were
optimal, every point of `Z = conv Z∠` would be) and finite, so the real `sInf` is a genuine minimum. -/
noncomputable def gap (P : Polytope d) (I : Instance p d) (x : FastCLO.ERM.Vec p) : ℝ :=
  if Zstar P I x = P.Z then 0
  else sInf ((fun z => ⟪I.fstar x, z⟫_ℝ) '' (P.ext \ Zstar P I x)) - optVal P I x

/-- The noise condition (7) of Assumption 2 (arXiv:2011.03030v3, p. 8): for some `α, γ ≥ 0`,
`P_X(0 < Δ(X) ≤ δ) ≤ (γ δ / B)^α` for all `δ > 0`.

Formalization Note: the probability is an `ℝ≥0∞`-valued measure, compared with `ENNReal.ofReal` of
the real power `(γδ/B)^α` (`Real.rpow` of a nonnegative base when `γ ≥ 0`; `0 ^ 0 = 1`, matching the
page's reading at `α = 0`). The constraints `α, γ ≥ 0` are hypotheses of the theorems that use it. -/
def NoiseCond (P : Polytope d) (I : Instance p d) (α γ : ℝ) : Prop :=
  ∀ δ > 0, I.μ {x | 0 < gap P I x ∧ gap P I x ≤ δ} ≤ ENNReal.ofReal ((γ * δ / P.B) ^ α)

/-- A policy with values in the extreme points, `π : ℝ^p → Z∠` (arXiv:2011.03030v3, p. 2,
"Π ⊆ [ℝ^p → Z∠]"). -/
def IsPolicy (P : Polytope d) (π : FastCLO.ERM.Vec p → FastCLO.ERM.Vec d) : Prop := ∀ x, π x ∈ P.ext

/-- A plug-`f`-in policy (3) (arXiv:2011.03030v3, p. 2): `π` takes values in the extreme points `Z∠`
and, at every `x`, minimizes the linear objective `f(x)ᵀ z` over `Z`, i.e.
`π_f(x) ∈ argmin_{z ∈ Z} f(x)ᵀ z` with `π_f(x) ∈ Z∠`.

Formalization Note: the page restricts to selections that "break ties arbitrarily but consistently
(i.e., by some ordering over Z∠)". This predicate admits *any* selection from the argmin with values
in `Z∠`; an upper bound proved for every such selection covers the consistent ones. -/
def IsPlugIn (P : Polytope d) (f π : FastCLO.ERM.Vec p → FastCLO.ERM.Vec d) : Prop :=
  IsPolicy P π ∧ ∀ x, ∀ z ∈ P.Z, ⟪f x, π x⟫_ℝ ≤ ⟪f x, z⟫_ℝ

/-- The regret (2) of a data-driven policy (arXiv:2011.03030v3, p. 2),
`E_D E_X[f*(X)ᵀ π̂_D(X) − min_{z∈Z} f*(X)ᵀ z]`, where `alg D` is the policy computed from the data
`D` and `D` is drawn from `n` i.i.d. copies of `(X, Y)`.

Formalization Note: the page writes `E_D E_X[f*(X)ᵀ(π̂(X) − π*(X))]`; since `π*(x) ∈ Z*(x)`,
`f*(x)ᵀπ*(x)` is the optimal value, so the two agree. -/
noncomputable def regret (P : Polytope d) (I : Instance p d) (n : ℕ)
    (alg : (Fin n → FastCLO.ERM.Vec p × FastCLO.ERM.Vec d) → FastCLO.ERM.Vec p → FastCLO.ERM.Vec d) : ℝ :=
  ∫ D, ∫ x, (⟪I.fstar x, alg D x⟫_ℝ - optVal P I x) ∂I.μ ∂(I.sample n)

end FastCLO.ETO


