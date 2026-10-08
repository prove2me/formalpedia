-- Prove2me | Definitions.Def_BERicci_Energy_Conditions
-- name    : BERicci_Energy_Conditions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T03:32:59.688099+00:00
-- url     : https://prove2.me/theorems/2c3a4f92-8bb1-43ee-b94e-8ef0ae6b7a46
-- title:
--   pp. 21–24, 33 — conditions (MD), (ED.a), (ED.b), weak L² convergence, minimal weak gradient |Df|_w, upper gradient (3.3)
-- statement:
--   Let $(X,d)$ be a metric space with a Borel measure $m$, and let $\mathcal E$ be a Dirichlet form on $L^2(X,m)$, with $\mathbb L_C$ the continuous functions $\psi\in\mathbb G$ with $\Gamma(\psi)\le1$ $m$-a.e.
--
--   1. **Condition (MD)** (Measure–Distance interaction, p. 21): (MD.a) $(X,d)$ is complete and separable, the σ-algebra is the $m$-completion of the Borel σ-algebra, and $\operatorname{supp}(m)=X$; (MD.b) $m(B_r(x))<\infty$ for every $x\in X$ and $r>0$.
--   2. **Condition (ED)** (Energy–Distance interaction, p. 33): (ED.a) every $\psi\in\mathbb L_C$ is 1-Lipschitz with respect to $d$; (ED.b) every Lipschitz $\psi$ with $|D\psi|\le1$ and bounded support belongs to $\mathbb L_C$.
--   3. **Minimal weak gradient** (p. 24). For $f\in L^2(X,m)$ with $\mathrm{Ch}(f)<\infty$, $|Df|_w$ is the unique nonnegative $w\in L^2(X,m)$ such that
--   $$\mathrm{Lip}_b(X)\cap L^2(X,m)\ni f_n\rightharpoonup f,\quad |Df_n|\rightharpoonup G\ \text{ in }L^2(X,m)\ \Longrightarrow\ w\le G,\qquad \mathrm{Ch}(f)=\tfrac12\int_X w^2\,dm.$$
--   The predicate "$w$ is a minimal weak gradient of $f$" states exactly these conditions, with weak $L^2$ convergence $u_n\rightharpoonup u$ meaning $\int u_nh\,dm\to\int uh\,dm$ for every $h\in L^2(X,m)$.
--   4. **Upper gradient** (3.3), p. 22. A bounded Borel function $g:X\to[0,\infty)$ is an upper gradient of a Lipschitz $\varphi$ if, for every absolutely continuous curve $\gamma:[a,b]\to X$,
--   $$\Big|\frac{d}{dt}\varphi(\gamma(t))\Big|\le g(\gamma(t))\,|\dot\gamma|(t)\qquad\text{for a.e. }t\in(a,b).$$
--
--   Conditions (MD) and (ED) are the compatibility conditions between a distance and the measure, respectively the Dirichlet form, under which Theorems 3.9–3.14 relate $\mathcal E$ to the metric structure.
--
--   **Formalization Note** The distance $d$ is the metric of $X$. The parts of (MD.a) on completeness, separability and the σ-algebra are carried by the typeclass binders `[CompleteSpace X] [SecondCountableTopology X] [BorelSpace X]` of each statement (the Borel σ-algebra stands for its $m$-completion); the definition `MD` holds full support and (MD.b). Bounded support is `Bornology.IsBounded (Function.support ψ)`. The minimal weak gradient carries $w\ge0$ explicitly: without it, $-|Df|_w$ would satisfy the two displayed conditions as well. The slope of a Lipschitz function is finite, so it is converted to a real number before testing weak convergence. An absolutely continuous curve is a $\gamma:\mathbb R\to X$ with $d(\gamma(s),\gamma(t))\le\int_s^tv$ for $a\le s\le t\le b$ and some $v\in L^1(a,b)$ (3.1). Since the metric velocity $|\dot\gamma|$ is the a.e.-smallest such $v$ and is itself one, the upper-gradient inequality is required for every such $v$ in place of $|\dot\gamma|$, which is equivalent.
-- source:
--   arXiv:1209.5786v4, Condition (MD), p. 21; (3.1), p. 21; (3.3), p. 22; minimal weak gradient, p. 24; Condition (ED), p. 33

import Mathlib
import Definitions.Def_BERicci_Gamma_Setting

namespace BERicci.Energy

open MeasureTheory Filter Topology
open scoped ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- **Condition (MD)** (p. 21) for the metric `d` of `X`: `supp m = X` (the part of (MD.a) not carried by the
binders `[CompleteSpace X] [SecondCountableTopology X] [BorelSpace X]`) and (MD.b), finite measure of balls. -/
def MD (m : Measure X) : Prop := m.IsOpenPosMeasure ∧ BERicci.Gamma.MDb m

/-- **(ED.a)** (p. 33): every `ψ ∈ L_C` is 1-Lipschitz with respect to the metric of `X`. -/
def EDa (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) : Prop :=
  ∀ ψ : X → ℝ, BERicci.Gamma.IsLC m E ψ → LipschitzWith 1 ψ

/-- **(ED.b)** (p. 33): every Lipschitz `ψ` with `|Dψ| ≤ 1` and bounded support belongs to `L_C`. -/
def EDb (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) : Prop :=
  ∀ ψ : X → ℝ, (∃ K, LipschitzWith K ψ) → (∀ x, BERicci.Gamma.slope ψ x ≤ 1) →
    Bornology.IsBounded (Function.support ψ) → BERicci.Gamma.IsLC m E ψ

/-- `fs n ⇀ f` weakly in `L²(X, m)`, tested against every `h ∈ L²(X, m)`. -/
def L2WeakTendsto (m : Measure X) (fs : ℕ → X → ℝ) (f : X → ℝ) : Prop :=
  (∀ n, MemLp (fs n) 2 m) ∧ MemLp f 2 m ∧
    ∀ h : X → ℝ, MemLp h 2 m →
      Tendsto (fun n => ∫ x, fs n x * h x ∂m) atTop (𝓝 (∫ x, f x * h x ∂m))

/-- **Minimal weak gradient** `|Df|_w` (p. 24): `w ∈ L²(X, m)`, `w ≥ 0`, below every weak `L²` limit `G` of
`|Df_n|` along `Lip_b(X) ∩ L²(X, m) ∋ f_n ⇀ f`, and `Ch(f) = ½ ∫ w² dm`. -/
def IsMinWeakGrad (m : Measure X) (f w : X → ℝ) : Prop :=
  MemLp w 2 m ∧ 0 ≤ᵐ[m] w ∧
    (∀ (fs : ℕ → X → ℝ) (G : X → ℝ), (∀ n, BERicci.Gamma.IsLipB (fs n)) → L2WeakTendsto m fs f →
      L2WeakTendsto m (fun n x => (BERicci.Gamma.slope (fs n) x).toReal) G → w ≤ᵐ[m] G) ∧
    BERicci.Gamma.cheeger m f = (1 / 2 : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (w x ^ 2) ∂m

/-- **Upper gradient** (3.3), p. 22: a bounded Borel `g : X → [0, ∞)` is an upper gradient of `φ ∈ Lip(X)` if
for every absolutely continuous curve `γ ∈ AC([a, b]; X)` — (3.1) holds with some `v ∈ L¹(a, b)` — the map
`φ ∘ γ` satisfies `|d/dt φ(γ(t))| ≤ g(γ(t)) |γ̇|(t)` for a.e. `t ∈ (a, b)`. The metric velocity `|γ̇|` is the
a.e.-smallest admissible `v` and is itself admissible, so the inequality is stated, equivalently, for every
admissible `v` in place of `|γ̇|`. -/
def IsUpperGradient (g φ : X → ℝ) : Prop :=
  Measurable g ∧ (∀ x, 0 ≤ g x) ∧ (∃ C : ℝ, ∀ x, g x ≤ C) ∧
    ∀ (a b : ℝ) (γ : ℝ → X) (v : ℝ → ℝ), a ≤ b → IntegrableOn v (Set.Icc a b) →
      (∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ b → dist (γ s) (γ t) ≤ ∫ r in s..t, v r) →
      ∀ᵐ t ∂(volume.restrict (Set.Ioo a b)), |deriv (fun r => φ (γ r)) t| ≤ g (γ t) * v t

end BERicci.Energy


