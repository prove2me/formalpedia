-- Prove2me | Definitions.Def_MFEUnique_Uniq_Equilibrium
-- name    : MFEUnique_Uniq_Equilibrium
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:20.681143+00:00
-- url     : https://prove2.me/theorems/bbe685bf-78e4-45a0-95b9-bbc730d56a4f
-- title:
--   Definitions 2–3, §3.1, pp. 10–12 — the kernel Q, the operator M_s, X-ergodicity, MFE, and the monotonicity conditions on Q and ⪰
-- statement:
--   This definition collects the equilibrium notions of Light and Weintraub (§2.3 and §3.1) for the game of `MFEUnique.Uniq.Game`.
--
--   Fix a stationary strategy $g : X \times \mathcal P(X) \to A$. The induced **Markov kernel** is
--   $$Q_g(x, s, B) = \Pr\big(w(x, g(x, s), s, \zeta) \in B\big) = \sum_{j=1}^{J} p_j\, \mathbf 1\{w(x, g(x, s), s, \zeta_j) \in B\},$$
--   and for each population state $s$ the operator $M_s$ on measures is
--   $$M_s\theta(B) = \int_X Q_g(x, s, B)\, \theta(dx).$$
--
--   1. **Weak convergence** (p. 7): $\mu_n \to \mu$ weakly if $\int f\, d\mu_n \to \int f\, d\mu$ for every bounded continuous $f : X \to \mathbb R$.
--   2. **X-ergodicity** (Definition 3): for every $s \in \mathcal P(X)$, $M_s$ has a unique fixed point $\mu_s$ in $\mathcal P(X)$, and $M_s^n\theta \to \mu_s$ weakly for every $\theta \in \mathcal P(X)$.
--   3. **Mean field equilibrium** (Definition 2): $(g, s)$ is an MFE if $g(x, s) \in G(x, s)$ for every $x$ (optimality) and $s(B) = \int_X Q_g(x, s, B)\, s(dx)$ for every Borel set $B$ (consistency).
--   4. With $X$ carrying a partial order and $\succeq_{SD}$ the usual stochastic order, $Q$ is **increasing in $x$** if $Q(x_2, s, \cdot) \succeq_{SD} Q(x_1, s, \cdot)$ whenever $x_2 \ge x_1$, and **decreasing in $s$** if $Q(x, s_1, \cdot) \succeq_{SD} Q(x, s_2, \cdot)$ whenever $s_2 \succeq s_1$, for a binary relation $\succeq$ on $\mathcal P(X)$.
--   5. The relation $\succeq$ has the **standing property** of p. 12 if $s_2 \sim s_1$ (that is, $s_2 \succeq s_1$ and $s_1 \succeq s_2$) implies $\pi(x, a, s_1) = \pi(x, a, s_2)$ for all $(x, a)$ and $w(x, a, s_1, \zeta) = w(x, a, s_2, \zeta)$ for all $(x, a, \zeta)$; it **agrees with** $\succeq_{SD}$ if $s_1 \succeq_{SD} s_2$ implies $s_1 \succeq s_2$; and it is **complete** if for all $s_1, s_2$ either $s_1 \succeq s_2$ or $s_2 \succeq s_1$.
--
--   These are exactly the hypotheses of the uniqueness theorem (Theorem 1).
--
--   **Formalization Note** $\succeq_{SD}$ is the published platform order `StochIneqPO.Comparison.StochLE`, whose arguments are swapped relative to the paper's notation: `StochLE P₁ P₂` reads "$P_1$ is stochastically smaller than $P_2$", i.e. $P_2 \succeq_{SD} P_1$. It uses bounded measurable increasing test functions, while the paper uses every increasing $f$ "when the integrals exist"; for probability measures the two coincide (truncate $f$ and use dominated convergence). The relation $\succeq$ is a predicate `R` with `R a b` meaning $a \succeq b$; no order axioms are assumed. $M_s\theta$ is written as $\sum_j p_j\, \theta \circ f_j^{-1}$ with $f_j(x) = w(x, g(x, s), s, \zeta_j)$; Lean's push-forward of a non-measurable map is the zero measure, but under the hypotheses of the theorems $x \mapsto g(x, s)$ is continuous (Lemma 3 with single-valued $G$), so this junk case does not arise. Iterates $M_s^n\theta$ are taken on measures, and weak convergence is the p. 7 definition applied to them.
-- source:
--   Light and Weintraub, Mean Field Equilibrium: Uniqueness, Existence, and Comparative Statics, arXiv:1903.02273v3, pp. 7 (weak convergence), 10 (Q_g, Definition 2), 11 (Eq. (1), M_s, Definition 3), 12 (⪰SD, the relation ⪰, complete, agrees with, Q increasing in x / decreasing in s)

import Mathlib
import Definitions.Def_StochIneqPO_Comparison_StochLE
import Definitions.Def_MFEUnique_Uniq_Game

namespace MFEUnique.Uniq

open MeasureTheory Filter Topology BoundedContinuousFunction StochIneqPO.Comparison

variable {X : Type*} [MeasurableSpace X] {q J : ℕ} {E : Type*}
  {A : Set (EuclideanSpace ℝ (Fin q))}

/-- The Markov kernel induced by the stationary strategy `g` (p. 10):
`Q_g(x, s, ·) = Pr(w(x, g(x, s), s, ζ) ∈ ·) = ∑_j p_j δ_{w(x, g(x, s), s, ζ_j)}`. -/
noncomputable def Game.Qk (G : Game X q J E A) (g : X → ProbabilityMeasure X → A) (x : X)
    (s : ProbabilityMeasure X) : Measure X :=
  ∑ j, ENNReal.ofReal (G.p j) • Measure.dirac (G.w x (g x s) s (G.ζ j))

/-- The operator `M_s θ(B) = ∫_X Q_g(x, s, B) θ(dx)` (p. 11), written as the mixture of the
push-forwards of `θ` under the maps `x ↦ w(x, g(x, s), s, ζ_j)`. -/
noncomputable def Game.Mop (G : Game X q J E A) (g : X → ProbabilityMeasure X → A)
    (s : ProbabilityMeasure X) (θ : Measure X) : Measure X :=
  ∑ j, ENNReal.ofReal (G.p j) • θ.map (fun x => G.w x (g x s) s (G.ζ j))

/-- Weak convergence of a sequence of measures (p. 7): `∫ f dμ_n → ∫ f dν` for every bounded
continuous `f : X → ℝ`. -/
def WeakConv [TopologicalSpace X] (μ : ℕ → Measure X) (ν : Measure X) : Prop :=
  ∀ f : X →ᵇ ℝ, Tendsto (fun n => ∫ x, f x ∂(μ n)) atTop (𝓝 (∫ x, f x ∂ν))

/-- Definition 3 (p. 11): `Q_g` is `X`-ergodic if for every population state `s` the operator
`M_s` has a unique fixed point `μ_s` in `P(X)`, and `M_s^n θ` converges weakly to `μ_s` for every
`θ ∈ P(X)`. -/
def Game.IsXErgodic [TopologicalSpace X] (G : Game X q J E A)
    (g : X → ProbabilityMeasure X → A) : Prop :=
  ∀ s : ProbabilityMeasure X, ∃ μ : ProbabilityMeasure X,
    G.Mop g s μ = μ ∧
    (∀ ν : ProbabilityMeasure X, G.Mop g s ν = ν → ν = μ) ∧
    ∀ θ : ProbabilityMeasure X, WeakConv (fun n => (G.Mop g s)^[n] θ) μ

/-- Definition 2 (p. 10): `(g, s)` is a mean field equilibrium if `g(x, s) ∈ G(x, s)` for every
`x` (optimality) and `s(B) = ∫_X Q_g(x, s, B) s(dx)` for every Borel `B` (consistency). -/
def Game.IsMFE (G : Game X q J E A) (g : X → ProbabilityMeasure X → A)
    (s : ProbabilityMeasure X) : Prop :=
  (∀ x, g x s ∈ G.Gopt x s) ∧ G.Mop g s s = s

/-- `Q` is increasing in `x` (p. 12): `Q(x₂, s, ·) ⪰SD Q(x₁, s, ·)` whenever `x₂ ≥ x₁`.
(`StochLE P₁ P₂` reads "`P₂ ⪰SD P₁`".) -/
def Game.IncreasingInX [Preorder X] (G : Game X q J E A)
    (g : X → ProbabilityMeasure X → A) : Prop :=
  ∀ (s : ProbabilityMeasure X) (x₁ x₂ : X), x₁ ≤ x₂ → StochLE (G.Qk g x₁ s) (G.Qk g x₂ s)

/-- `Q` is decreasing in `s` (p. 12): `Q(x, s₁, ·) ⪰SD Q(x, s₂, ·)` whenever `s₂ ⪰ s₁`, where
`R a b` means `a ⪰ b`. -/
def Game.DecreasingInS [Preorder X] (G : Game X q J E A)
    (R : ProbabilityMeasure X → ProbabilityMeasure X → Prop)
    (g : X → ProbabilityMeasure X → A) : Prop :=
  ∀ (x : X) (s₁ s₂ : ProbabilityMeasure X), R s₂ s₁ → StochLE (G.Qk g x s₂) (G.Qk g x s₁)

/-- The standing property of the binary relation `⪰` on `P(X)` (p. 12): `s₂ ∼ s₁` (i.e.
`s₂ ⪰ s₁` and `s₁ ⪰ s₂`) implies `π(x, a, s₁) = π(x, a, s₂)` for all `(x, a)` and
`w(x, a, s₁, ζ) = w(x, a, s₂, ζ)` for all `(x, a, ζ)`. -/
def Game.RelStanding (G : Game X q J E A)
    (R : ProbabilityMeasure X → ProbabilityMeasure X → Prop) : Prop :=
  ∀ s₁ s₂ : ProbabilityMeasure X, R s₂ s₁ → R s₁ s₂ →
    (∀ x a, G.pay x a s₁ = G.pay x a s₂) ∧ (∀ x a e, G.w x a s₁ e = G.w x a s₂ e)

/-- `⪰` agrees with `⪰SD` (p. 12): `s₁ ⪰SD s₂` implies `s₁ ⪰ s₂`. -/
def AgreesSD [Preorder X] (R : ProbabilityMeasure X → ProbabilityMeasure X → Prop) : Prop :=
  ∀ s₁ s₂ : ProbabilityMeasure X, StochLE (s₂ : Measure X) (s₁ : Measure X) → R s₁ s₂

/-- `⪰` is complete (p. 12): for all `s₁, s₂` either `s₁ ⪰ s₂` or `s₂ ⪰ s₁`. -/
def IsComplete (R : ProbabilityMeasure X → ProbabilityMeasure X → Prop) : Prop :=
  ∀ s₁ s₂ : ProbabilityMeasure X, R s₁ s₂ ∨ R s₂ s₁

end MFEUnique.Uniq


