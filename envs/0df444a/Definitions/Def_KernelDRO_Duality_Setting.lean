-- Prove2me | Definitions.Def_KernelDRO_Duality_Setting
-- name    : KernelDRO_Duality_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:25:51.88966+00:00
-- url     : https://prove2.me/theorems/f4497498-a6c0-4913-b3ea-d2e70503d65a
-- title:
--   §2, §3.1, (11), (12), pp. 2–3, 13 — RKHS evaluation, mean embedding $\mu_P$, ambiguity set $\mathcal K_{\mathcal C}$, support function $\delta^*_{\mathcal C}$, primal and dual values
-- statement:
--   This file sets up the objects of Kernel Distributionally Robust Optimization.
--
--   Let $\mathcal X$ be a measurable space (in every theorem of the mission, a compact metric space with its Borel $\sigma$-algebra) and $\mathcal P$ the set of probability measures on $\mathcal X$. Let $\mathcal H$ be a real Hilbert space and $\varphi:\mathcal X\to\mathcal H$ a **feature map**, so that $k(x,y)=\langle\varphi(x),\varphi(y)\rangle_{\mathcal H}$ is a positive definite kernel and $\mathcal H$ plays the role of its reproducing kernel Hilbert space.
--
--   1. **Evaluation.** An element $f\in\mathcal H$ is evaluated at $\xi\in\mathcal X$ by the reproducing property, $f(\xi)=\langle f,\varphi(\xi)\rangle_{\mathcal H}$.
--   2. **Mean embedding.** For $P\in\mathcal P$, $\mu_P=\int\varphi\,dP\in\mathcal H$ (a Bochner integral).
--   3. **Ambiguity set.** For $\mathcal C\subseteq\mathcal H$, $\mathcal K_{\mathcal C}=\{P\in\mathcal P:\mu_P\in\mathcal C\}$.
--   4. **Support function.** $\delta^*_{\mathcal C}(f)=\sup_{\mu\in\mathcal C}\langle f,\mu\rangle_{\mathcal H}\in[-\infty,+\infty]$.
--   5. **Primal value (11).** For a loss $l:\mathcal X\to[-\infty,+\infty]$,
--   $$\mathrm{(P)}=\sup_{P\in\mathcal K_{\mathcal C}}\int l\,dP .$$
--   6. **Dual feasibility and dual value (12).** $(f_0,f)\in\mathbb R\times\mathcal H$ is dual feasible if $l(\xi)\le f_0+f(\xi)$ for all $\xi\in\mathcal X$, and
--   $$\mathrm{(D)}=\inf\Big\{f_0+\delta^*_{\mathcal C}(f)\ :\ f_0\in\mathbb R,\ f\in\mathcal H,\ l(\xi)\le f_0+f(\xi)\ \ \forall\xi\in\mathcal X\Big\}.$$
--
--   These are the inner problems of the Kernel DRO primal (2) and dual (4); the generalized duality theorem asserts $\mathrm{(P)}=\mathrm{(D)}$.
--
--   **Formalization Note** All values are extended reals: $\delta^*_\emptyset=-\infty$, $\delta^*_{\mathcal H}(f)=+\infty$ for $f\ne0$, the primal value over an empty ambiguity set is $-\infty$ and the dual value with no feasible $(f_0,f)$ is $+\infty$. The integral $\int l\,dP$ is the published `WassersteinDRO.Duality.erealExpectation`. The paper's "min" in (12) is read as an infimum, since dual attainment is not proved and can fail (e.g. $\mathcal X=[0,1]$, $\varphi(x)=x$, $\mathcal C=(-\infty,0]$, $l(x)=\sqrt x$). The dual variable ranges over $\mathcal H$, not over all functions on $\mathcal X$.
-- source:
--   Zhu, Jitkrittum, Diehl & Schölkopf, Kernel Distributionally Robust Optimization, arXiv:2006.06981v3, §2 Notation, p. 2; §2.2, p. 3; §3.1, (2), p. 3; App. A Notation and §A.1, (11), (12), p. 13; §D.2, p. 23

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_erealExpectation

open MeasureTheory

namespace KernelDRO.Duality

open WassersteinDRO.Duality

/-- Evaluation of an RKHS function through the feature map: `rkhsEval φ f ξ = ⟪f, φ ξ⟫`, the value
`f(ξ)` of `f ∈ ℋ` at `ξ ∈ 𝒳` by the reproducing property "f(x) = ⟨f, φ(x)⟩_ℋ for any f ∈ ℋ, x ∈ 𝒳"
(Zhu, Jitkrittum, Diehl & Schölkopf, Kernel Distributionally Robust Optimization,
arXiv:2006.06981v3, §2.2, p. 3).

**Formalization Note.** The RKHS is taken in feature-map form: `ℋ` is a real Hilbert space and
`φ : 𝒳 → ℋ` a feature map with `k(x, y) = ⟪φ x, φ y⟫`; an element `f ∈ ℋ` acts on `𝒳` only through
`ξ ↦ ⟪f, φ ξ⟫`. The canonical RKHS of a kernel `k` with `φ(x) = k(x, ·)` is the instance. -/
def rkhsEval {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (φ : X → H) (f : H)
    (ξ : X) : ℝ :=
  inner ℝ f (φ ξ)

/-- The kernel mean embedding `µ_P := ∫ φ dP ∈ ℋ` of a Borel probability measure `P` on `𝒳`
(Zhu, Jitkrittum, Diehl & Schölkopf, Kernel Distributionally Robust Optimization,
arXiv:2006.06981v3, §2.2, p. 3, "µ_P := ∫ k(x, ·) dP"; the mean map `𝒯 : P ↦ µ_P` of §D.2, p. 23).

**Formalization Note.** A Bochner integral in `ℋ`. For a continuous `φ` on a compact metric space
`𝒳` (the setting of every theorem of this mission) `φ` is bounded and strongly measurable, so the
integral is a genuine one and never Lean's junk value `0`. -/
noncomputable def meanEmbedding {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (φ : X → H) (P : ProbabilityMeasure X) : H :=
  ∫ x, φ x ∂(P : Measure X)

/-- The RKHS ambiguity set `𝒦_𝒞 = {P : ∫ φ dP = µ, µ ∈ 𝒞, P ∈ 𝒫}` (Zhu, Jitkrittum, Diehl &
Schölkopf, Kernel Distributionally Robust Optimization, arXiv:2006.06981v3, §3.1, p. 3; and §D.2,
p. 23): the Borel probability measures on `𝒳` whose mean embedding lies in `𝒞 ⊆ ℋ`. The moment
variable `µ` of (2) is eliminated, since it is determined by `P`. -/
def ambiguitySet {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (φ : X → H) (C : Set H) : Set (ProbabilityMeasure X) :=
  {P | meanEmbedding φ P ∈ C}

/-- The support function `δ*_𝒞(f) := sup_{µ∈𝒞} ⟨f, µ⟩_ℋ` of `𝒞 ⊆ ℋ` (Zhu, Jitkrittum, Diehl &
Schölkopf, Kernel Distributionally Robust Optimization, arXiv:2006.06981v3, §2 Notation, p. 2, and
Theorem 3.1, (4), p. 5).

**Formalization Note.** Valued in `EReal`: `δ*_𝒞(f) = +∞` when `µ ↦ ⟪f, µ⟫` is unbounded above on
`𝒞` (e.g. `𝒞 = ℋ`, `f ≠ 0`, Table 1, p. 4), and `δ*_∅ = −∞`, the supremum of the empty set. No real
`sSup` junk value is involved. -/
noncomputable def supportFun {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Set H) (f : H) : EReal :=
  ⨆ μ ∈ C, ((inner ℝ f μ : ℝ) : EReal)

/-- The optimal value of the inner moment problem (11),
`sup_{P∈𝒫, µ∈𝒞} ∫ l dP subject to ∫ φ dP = µ` (Zhu, Jitkrittum, Diehl & Schölkopf, Kernel
Distributionally Robust Optimization, arXiv:2006.06981v3, §A.1, (11), p. 13; the inner problem of
(2), p. 3): the worst-case expected loss over the ambiguity set `𝒦_𝒞`.

**Formalization Note.** The loss `l : 𝒳 → [−∞, +∞]` is extended-real valued and `∫ l dP` is the
published `WassersteinDRO.Duality.erealExpectation`, which is `+∞` iff `∫ l⁺ dP = ∞` and
`∫ l⁺ dP − ∫ l⁻ dP ∈ [−∞, ∞)` otherwise. For the upper semicontinuous losses of this mission, which
are bounded above on the compact `𝒳`, `∫ l⁺ dP < ∞`, so this is the paper's `∫ l dP ∈ [−∞, ∞)`.
The supremum over the empty ambiguity set is `−∞`. -/
noncomputable def primalValue {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (φ : X → H) (C : Set H) (l : X → EReal) : EReal :=
  ⨆ P ∈ ambiguitySet φ C, erealExpectation (P : Measure X) l

/-- Dual feasibility in (12): `(f₀, f) ∈ ℝ × ℋ` satisfies the semi-infinite constraint
`l(ξ) ≤ f₀ + f(ξ), ∀ ξ ∈ 𝒳` (Zhu, Jitkrittum, Diehl & Schölkopf, Kernel Distributionally Robust
Optimization, arXiv:2006.06981v3, §A.1, (12), p. 13; Theorem 3.1, (4), p. 5), with
`f(ξ) = ⟪f, φ ξ⟫` by the reproducing property. -/
def IsDualFeasible {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (φ : X → H)
    (l : X → EReal) (f₀ : ℝ) (f : H) : Prop :=
  ∀ ξ, l ξ ≤ ((f₀ + rkhsEval φ f ξ : ℝ) : EReal)

/-- The optimal value of the dual problem (12),
`min_{f₀∈ℝ, f∈ℋ} δ*_𝒞(f) + f₀ subject to l(ξ) ≤ f₀ + f(ξ), ∀ ξ ∈ 𝒳` (Zhu, Jitkrittum, Diehl &
Schölkopf, Kernel Distributionally Robust Optimization, arXiv:2006.06981v3, Proposition A.1, (12),
p. 13; the inner problem of (4), Theorem 3.1, p. 5).

**Formalization Note.** The printed "min" is read as an infimum: the paper's proof (p. 15) only
produces `ε`-optimal dual solutions and dual attainment can fail (e.g. `𝒳 = [0, 1]`, `ℋ = ℝ`,
`φ(x) = x`, `𝒞 = (−∞, 0]`, `l(x) = √x`), so "min" is an overstatement of the page. The dual variable
`f` ranges over `ℋ`, never over arbitrary functions `𝒳 → ℝ` (Example 3.3, p. 4). The value is in
`EReal`: `+∞` when no `(f₀, f)` is feasible; the sum `(f₀ : EReal) + δ*_𝒞(f)` adds a real number to
an extended real, so `⊤ + ⊥` never arises. -/
noncomputable def dualValue {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : X → H) (C : Set H) (l : X → EReal) : EReal :=
  ⨅ (f₀ : ℝ) (f : H) (_ : IsDualFeasible φ l f₀ f), (f₀ : EReal) + supportFun C f

end KernelDRO.Duality


