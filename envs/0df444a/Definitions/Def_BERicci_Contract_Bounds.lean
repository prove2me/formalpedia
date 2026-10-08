-- Prove2me | Definitions.Def_BERicci_Contract_Bounds
-- name    : BERicci_Contract_Bounds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T03:34:03.99711+00:00
-- url     : https://prove2.me/theorems/16ae3a7d-4de8-4caf-ae12-1073087846a8
-- title:
--   (2.12), (3.5), (3.12), (3.15), (3.16), pp. 13–26 — mass preservation, Hopf–Lax map, W₁, W_(β), the Lipschitz and gradient bounds
-- statement:
--   The objects specific to §3.2 of the paper.
--
--   1. **Mass preservation** (2.12): $\int_X\mathsf P_tf\,dm=\int_Xf\,dm$ for every $t\ge0$ and $f\in L^1\cap L^2(X,m)$.
--   2. A function $C:[0,\infty)\to[0,\infty)$ is **bounded on intervals** if it is bounded on $[0,T]$ for every $T>0$.
--   3. The **Lipschitz bound (3.15)**: for every $t\ge0$ and $f\in\mathrm{Lip}_b(X)\cap L^2(X,m)$, the function $\mathsf P_tf$ has a version in $\mathrm{Lip}_b(X)$ with
--   $$\mathrm{Lip}(\mathsf P_tf)\le C(t)\,\mathrm{Lip}(f).$$
--   4. The **Hopf–Lax map (3.5)**: for $t>0$,
--   $$Q_tf(x):=\inf_{y\in X}\Big(f(y)+\frac{\mathsf d^2(y,x)}{2t}\Big),\qquad Q_0f=f.$$
--   5. The **pointwise gradient bound (3.16)**: for every $t\ge0$, $x\in X$ and $f\in\mathrm{Lip}_b(X)\cap L^2(X,m)$,
--   $$|D\tilde{\mathsf P}_tf|^2(x)\le C^2(t)\,\tilde{\mathsf P}_t|Df|^2(x),$$
--   where $\tilde{\mathsf P}_tg(x)=\int g\,d\mathsf H_t\delta_x$ is the pointwise version given by the dual semigroup and $|Df|$ is the slope.
--   6. The **Wasserstein distances** $W_1$ ((3.12) with $p=1$) and, for a continuous, concave, bounded modulus $\beta:[0,\infty)\to[0,\infty)$ with $0=\beta(0)<\beta(r)$ for $r>0$,
--   $$W_{(\beta)}(\mu_1,\mu_2):=\inf\Big\{\int_{X^2}\beta(\mathsf d(x_1,x_2))\,d\boldsymbol\mu:\ \pi^i_\sharp\boldsymbol\mu=\mu_i\Big\}.$$
--
--   These are the hypotheses and the auxiliary objects of Proposition 3.2, Lemma 3.4 and Theorem 3.5.
--
--   **Formalization Note** Mass preservation is stated on $L^1\cap L^2$, where the heat flow of the Setting is pinned; the paper's $L^1$ extension agrees there. "$\mathrm{Lip}(\mathsf P_tf)\le C(t)\mathrm{Lip}(f)$" is written as "every Lipschitz constant $K$ of $f$ gives the Lipschitz constant $C(t)K$ of the version", which is equivalent and avoids an infimum. In (3.16) both sides are in $[0,\infty]$ and $\tilde{\mathsf P}_t|Df|^2(x)$ is a lower Lebesgue integral. The Hopf–Lax infimum is a real infimum, which is the paper's value for $f$ bounded below (the only case used). $W_1$ and $W_{(\beta)}$ take values in $[0,\infty]$.
-- source:
--   arXiv:1209.5786v4, (2.12), p. 13; (3.5), p. 22; (3.12) and W_(β), p. 24; (3.15), (3.16), p. 26

import Mathlib
import Definitions.Def_BERicci_Contract_Dual

namespace BERicci.Contract

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X]

/-- The mass-preserving property (2.12), p. 13, written on `L¹ ∩ L²(X, m)`, where the heat flow
`P` of the Setting is pinned: `∫ P_t f dm = ∫ f dm` for all `t ≥ 0`. -/
def MassPreserving (m : Measure X) (P : ℝ → (X → ℝ) → X → ℝ) : Prop :=
  ∀ f : X → ℝ, Integrable f m → MemLp f 2 m → ∀ t : ℝ, 0 ≤ t → ∫ x, P t f x ∂m = ∫ x, f x ∂m

/-- `C` is bounded on every interval `[0, T]`, `T > 0` (pp. 26, after (3.15) and (3.16)). -/
def BoundedOnIntervals (C : ℝ → ℝ≥0) : Prop :=
  ∀ T : ℝ, 0 < T → ∃ B : ℝ≥0, ∀ t ∈ Set.Icc 0 T, C t ≤ B

section Metric
variable [MetricSpace X]

/-- (3.15), p. 26: for every `t ≥ 0` and `f ∈ Lip_b(X) ∩ L²(X, m)`, `P_t f` has a representative in
`Lip_b(X)` whose Lipschitz constant is at most `C(t) Lip(f)` (stated for every Lipschitz constant `K`
of `f`, which is equivalent). -/
def LipContraction (m : Measure X) (P : ℝ → (X → ℝ) → X → ℝ) (C : ℝ → ℝ≥0) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ f : X → ℝ, BERicci.Gamma.IsLipB f → MemLp f 2 m →
    ∃ g : X → ℝ, g =ᵐ[m] P t f ∧ BERicci.Gamma.IsLipB g ∧ ∀ K : ℝ≥0, LipschitzWith K f → LipschitzWith (C t * K) g

/-- The Hopf–Lax evolution (3.5), p. 22: `Q_t f(x) = inf_{y ∈ X} f(y) + d²(y, x)/(2t)` for `t > 0`,
`Q_0 f = f`. (A real infimum: it is the book's value when `f` is bounded below.) -/
noncomputable def hopfLax (t : ℝ) (f : X → ℝ) (x : X) : ℝ :=
  if t = 0 then f x else ⨅ y : X, f y + dist y x ^ 2 / (2 * t)

variable [BorelSpace X]

/-- (3.16), p. 26: `|D P̃_t f|²(x) ≤ C²(t) P̃_t |Df|²(x)` for all `t ≥ 0`, `x ∈ X` and
`f ∈ Lip_b(X) ∩ L²(X, m)`, where `P̃_t g(x) = ∫ g dH_tδ_x` and the BERicci.Gamma.slope is that of the pointwise version
`P̃_t f`. Values in `[0, ∞]`. -/
def GradBound (m : Measure X) (H : ℝ → Measure X → Measure X) (C : ℝ → ℝ≥0) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ f : X → ℝ, BERicci.Gamma.IsLipB f → MemLp f 2 m → ∀ x : X,
    BERicci.Gamma.slope (Ptilde H t f) x ^ 2 ≤ ((C t : ℝ≥0∞)) ^ 2 * ∫⁻ y, BERicci.Gamma.slope f y ^ 2 ∂(H t (Measure.dirac x))

/-- `W₁(μ₁, μ₂)` ((3.12) with `p = 1`), an extended value. -/
noncomputable def W1 (μ₁ μ₂ : Measure X) : ℝ≥0∞ :=
  ⨅ (γ : Measure (X × X)) (_ : BERicci.Gamma.IsCoupling μ₁ μ₂ γ), ∫⁻ p, edist p.1 p.2 ∂γ

/-- A continuous, concave and bounded modulus of continuity `β : [0, ∞) → [0, ∞)` with
`0 = β(0) < β(r)` for every `r > 0` (p. 24). -/
def IsModulus (β : ℝ → ℝ) : Prop :=
  ContinuousOn β (Set.Ici 0) ∧ ConcaveOn ℝ (Set.Ici 0) β ∧ (∃ B : ℝ, ∀ r, 0 ≤ r → β r ≤ B) ∧
    β 0 = 0 ∧ ∀ r, 0 < r → 0 < β r

/-- `W_(β)(μ₁, μ₂) = inf ∫ β(d(x₁, x₂)) dμ` over couplings (p. 24). -/
noncomputable def Wbeta (β : ℝ → ℝ) (μ₁ μ₂ : Measure X) : ℝ≥0∞ :=
  ⨅ (γ : Measure (X × X)) (_ : BERicci.Gamma.IsCoupling μ₁ μ₂ γ), ∫⁻ p, ENNReal.ofReal (β (dist p.1 p.2)) ∂γ

end Metric

end BERicci.Contract


