-- Prove2me | Definitions.Def_DistTransform_Distortion_Model
-- name    : DistTransform_Distortion_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:49.548708+00:00
-- url     : https://prove2.me/theorems/809634c1-7200-4c65-9508-38b6d8f63ae0
-- title:
--   §2, pp. 3–6 — M∞, M−, M+, quantiles (1), ⩽st, shape transforms T^[φ], H0 and probability distortions (Def. 1), the properties of Def. 2
-- statement:
--   This file fixes the objects of Liu, Schied and Wang's characterization of probability distortions.
--
--   **Distributions.** A distribution is a Borel probability measure $F$ on $\mathbb R$, identified with its cumulative distribution function $F(x)=F((-\infty,x])$. The set of all distributions is $\mathcal M_0$. The set $\mathcal M_\infty$ consists of the distributions with bounded support, i.e. those with $F([a,b])=1$ for some $a\le b$. Two further classes are used in the proof of Theorem 1:
--
--   1. $\mathcal M_-$: distributions whose support has infinite lower bound and finite upper bound, i.e. $F(b)=1$ for some $b$ and $F(a)>0$ for every $a$;
--   2. $\mathcal M_+$: distributions whose support has finite lower bound and infinite upper bound, i.e. $F(a)=0$ for some $a$ and $F(b)<1$ for every $b$.
--
--   **Quantiles.** The left and right quantiles of $F$ at level $t$ are
--   $$
--   F^{-1}(t)=\inf\{x\in\mathbb R: F(x)\ge t\},\qquad F^{-1}_+(t)=\inf\{x\in\mathbb R: F(x)>t\}.
--   $$
--
--   **Stochastic order.** $F\preceq_{\mathrm{st}}G$ means $F((x,\infty))\le G((x,\infty))$ for every $x\in\mathbb R$, equivalently $F(x)\ge G(x)$ for every $x$.
--
--   **Shape transforms.** For a strictly increasing continuous $\varphi:\mathbb R\to\mathbb R$ with $\varphi(\mathbb R)=\mathbb R$, the shape transform $T^{[\varphi]}(F)=F\circ\varphi^{-1}$ is the law of $\varphi(X)$ for $X\sim F$.
--
--   **Probability distortions.** $\mathcal H_0$ is the class of functions $g$ that are increasing and right-continuous on $[0,1]$ with $g(0)=0$ and $g(1)=1$. A distributional transform $T$ is a *probability distortion* on a set $\mathcal M$ of distributions if there is $g\in\mathcal H_0$ with
--   $$
--   T(F)(x)=g(F(x))\qquad\text{for all }F\in\mathcal M,\ x\in\mathbb R.
--   $$
--
--   **Properties (Definition 2).** For a set $\mathcal M$ of distributions and a map $T$ on distributions:
--
--   1. $T$ is *monotone* if $T(F)\preceq_{\mathrm{st}}T(G)$ whenever $F\preceq_{\mathrm{st}}G$ with $F,G\in\mathcal M$;
--   2. $T$ is *lower-semicontinuous* if $T(F)\preceq_{\mathrm{st}}G$ whenever $G\in\mathcal M$, $(F_n)\subset\mathcal M$ converges weakly to $F\in\mathcal M$ and $T(F_n)\preceq_{\mathrm{st}}G$ for all $n$;
--   3. $T$ *commutes with shape transforms* if $\mathcal M$ is closed under every $T^{[\varphi]}$ and $T\circ T^{[\varphi]}=T^{[\varphi]}\circ T$ on $\mathcal M$.
--
--   These are the hypotheses and the conclusion of Theorem 1 of the paper, and of every milestone of the mission.
--
--   **Formalization Note** Distributions are `ProbabilityMeasure ℝ` and cdfs are Mathlib's `ProbabilityTheory.cdf`; the paper's atomless probability space is not needed, since every Borel probability measure on $\mathbb R$ is the law of a random variable on such a space. Quantiles are real-valued `sInf`s; they are the paper's quantiles at levels $t\in(0,1)$ for every distribution, and additionally at $t=1$ (left) and $t=0$ (right) on $\mathcal M_\infty$, and every statement of the mission evaluates them only there. The stochastic order reuses the published `StochasticOrders.Usual.UsualOrder` on the identity random variables (the survival-function form; the paper notes on p. 5 that it is equivalent to its integral definition). Shape transforms are order isomorphisms `ℝ ≃o ℝ` (exactly the strictly increasing continuous surjections of $\mathbb R$), acting by pushforward. $g\in\mathcal H_0$ is a function $\mathbb R\to\mathbb R$ constrained on $[0,1]$ only. "Probability distortion" is stated as an equation of cdfs on $\mathcal M$, not as a constructed measure $g\circ F$. Weak convergence is convergence in Mathlib's topology on `ProbabilityMeasure ℝ`.
-- source:
--   Liu, Schied and Wang, Distributional transforms, probability distortions, and their applications, SSRN 3419388 (version of March 19, 2020), pp. 3–6, §2, Eq. (1), Definitions 1–2, Example 5; p. 8 (M−, M+)

import Mathlib
import Definitions.Def_StochasticOrders_Usual_UsualOrder

namespace DistTransform.Distortion

open MeasureTheory ProbabilityTheory Filter Topology

/-- `M∞` (p. 3): the distributions of bounded random variables, i.e. the Borel probability
measures on `ℝ` that give mass one to some compact interval `[a, b]`. -/
def Minf : Set (ProbabilityMeasure ℝ) :=
  {F | ∃ a b : ℝ, (F : Measure ℝ) (Set.Icc a b) = 1}

/-- `M−` (p. 8): distributions whose support has infinite lower bound and finite upper bound,
i.e. the cdf reaches `1` at some point but is positive everywhere. -/
def Mminus : Set (ProbabilityMeasure ℝ) :=
  {F | (∃ b : ℝ, cdf (F : Measure ℝ) b = 1) ∧ ∀ a : ℝ, 0 < cdf (F : Measure ℝ) a}

/-- `M+` (p. 8): distributions whose support has finite lower bound and infinite upper bound,
i.e. the cdf vanishes at some point but stays below `1` everywhere. -/
def Mplus : Set (ProbabilityMeasure ℝ) :=
  {F | (∃ a : ℝ, cdf (F : Measure ℝ) a = 0) ∧ ∀ b : ℝ, cdf (F : Measure ℝ) b < 1}

/-- The (left) quantile `F⁻¹(t) = inf {x ∈ ℝ : F(x) ≥ t}` of eq. (1), p. 4, as a real `sInf`.
It is the paper's (finite) quantile for `t ∈ (0, 1)` on every distribution, and also at `t = 1`
on `M∞`; elsewhere the real `sInf` returns a junk value and is never used. -/
noncomputable def leftQuantile (F : ProbabilityMeasure ℝ) (t : ℝ) : ℝ :=
  sInf {x : ℝ | t ≤ cdf (F : Measure ℝ) x}

/-- The right quantile `F⁻¹₊(t) = inf {x ∈ ℝ : F(x) > t}` (p. 4), as a real `sInf`. It is the
paper's (finite) value for `t ∈ (0, 1)` on every distribution, and also at `t = 0` on `M∞`. -/
noncomputable def rightQuantile (F : ProbabilityMeasure ℝ) (t : ℝ) : ℝ :=
  sInf {x : ℝ | t < cdf (F : Measure ℝ) x}

/-- Stochastic order `F ⩽st G` (p. 5): the usual stochastic order of the published definition
`StochasticOrders.Usual.UsualOrder`, applied to the identity random variables on `(ℝ, F)` and
`(ℝ, G)`, i.e. `F((x, ∞)) ≤ G((x, ∞))` for all `x`, equivalently `F(x) ≥ G(x)` for all `x`. -/
def StLE (F G : ProbabilityMeasure ℝ) : Prop :=
  StochasticOrders.Usual.UsualOrder (F : Measure ℝ) (G : Measure ℝ) id id

/-- The shape transform `T^[φ](F) = F ∘ φ⁻¹` of Example 5, p. 5: the law of `φ(X)` for `X ∼ F`,
for `φ` strictly increasing, continuous and onto `ℝ` (an order isomorphism of `ℝ`). -/
noncomputable def shape (φ : ℝ ≃o ℝ) (F : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  F.map φ.continuous.measurable.aemeasurable

/-- The class `H0` (p. 4): `g` is increasing and right-continuous on `[0, 1]` with `g(0) = 0`
and `g(1) = 1`. Only the values of `g` on `[0, 1]` matter. -/
def IsH0 (g : ℝ → ℝ) : Prop :=
  MonotoneOn g (Set.Icc 0 1) ∧
    (∀ t ∈ Set.Ico (0 : ℝ) 1, ContinuousWithinAt g (Set.Ici t) t) ∧
    g 0 = 0 ∧ g 1 = 1

/-- Definition 1, p. 4: `T` is a probability distortion on `M` if `T(F) = g ∘ F` (as cdfs) for
all `F ∈ M`, for some `g ∈ H0`. -/
def IsProbabilityDistortion (M : Set (ProbabilityMeasure ℝ))
    (T : ProbabilityMeasure ℝ → ProbabilityMeasure ℝ) : Prop :=
  ∃ g : ℝ → ℝ, IsH0 g ∧
    ∀ F ∈ M, ∀ x : ℝ, cdf (T F : Measure ℝ) x = g (cdf (F : Measure ℝ) x)

/-- Definition 2, p. 5: `T` is monotone on `M` if `T(F) ⩽st T(G)` whenever `F ⩽st G`,
`F, G ∈ M`. -/
def IsMonotoneT (M : Set (ProbabilityMeasure ℝ))
    (T : ProbabilityMeasure ℝ → ProbabilityMeasure ℝ) : Prop :=
  ∀ F ∈ M, ∀ G ∈ M, StLE F G → StLE (T F) (T G)

/-- Definition 2, pp. 5–6: `T` is lower-semicontinuous on `M` if `T(F) ⩽st G` whenever
`G ∈ M`, `(Fₙ) ⊂ M` converges weakly to `F ∈ M` and `T(Fₙ) ⩽st G` for all `n`. -/
def IsLSC (M : Set (ProbabilityMeasure ℝ))
    (T : ProbabilityMeasure ℝ → ProbabilityMeasure ℝ) : Prop :=
  ∀ (Fs : ℕ → ProbabilityMeasure ℝ) (F G : ProbabilityMeasure ℝ),
    (∀ n, Fs n ∈ M) → F ∈ M → G ∈ M →
    Tendsto Fs atTop (𝓝 F) → (∀ n, StLE (T (Fs n)) G) → StLE (T F) G

/-- Definition 2, p. 6: `T` commutes with shape transforms on `M` if `M` is closed under every
`T^[φ]` and `T ∘ T^[φ] = T^[φ] ∘ T` on `M`. -/
def CommutesWithShape (M : Set (ProbabilityMeasure ℝ))
    (T : ProbabilityMeasure ℝ → ProbabilityMeasure ℝ) : Prop :=
  ∀ φ : ℝ ≃o ℝ, Set.MapsTo (shape φ) M M ∧ ∀ F ∈ M, T (shape φ F) = shape φ (T F)

end DistTransform.Distortion


