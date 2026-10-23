-- Prove2me | Definitions.Def_RepRegion_Density_Model
-- name    : RepRegion_Density_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:16:21.885888+00:00
-- url     : https://prove2.me/theorems/f0d45186-2600-4f27-a6b2-a5b400449088
-- title:
--   §3.1, §6.1, §6.4, pp. 5–6, 19–21, 26 — RRS methods, sampling, empirical measure, support, uniform-scale classes, method properties, the density estimate ĝ
-- statement:
--   This file sets up the objects of *representative region selection* (RRS) and of its convergence theory.
--
--   **RRS methods (§3.1).** Let $M$ be a set. An *RRS method* on $M$ is a pair $(\mathcal C, f)$ where $\mathcal C \subseteq 2^M$ is a class of allowed regions and $f$ maps every finite set $S \subseteq M$ to a finite set $f(S) \subseteq \mathcal C$ of regions. Its *coverage region* on $S$ is $C(S; f) = \bigcup_{A \in f(S)} A$. The method is *sample-covering* if $S \subseteq C(S; f)$ for every finite $S$, and *sample-intersecting* if every $A \in f(S)$ meets $S$.
--
--   **Sampling (§6.1.1).** $(M, d)$ is a metric space with a σ-algebra, $X_1, X_2, \dots$ are i.i.d. $M$-valued random variables on a probability space $(\Omega, \mathcal F, P)$ with law $P_X$, $S_n = \{X_1, \dots, X_n\}$ is the set of the first $n$ observations and $C_n(f) = C(S_n; f)$. The empirical measure of a set $T$ is
--   $$\hat P_{X,n}(T) = \frac{\#\{i \le n : X_i \in T\}}{n}.$$
--   The *support* of a measure $\nu$ is the set of points $y$ with $\nu(B[y; r]) > 0$ for every $r > 0$.
--
--   **Scalable classes (§6.1.2).** A *scalable class* $(\mathcal C, \Theta, R)$ consists of a map $R : \Theta \times \mathbb R^+ \to 2^M$, non-decreasing in the scale $\lambda$, with $\mathcal C = \{R(\theta, \lambda) : (\theta, \lambda) \in \Xi\}$ for some $\Xi \subseteq \Theta \times \mathbb R^+$. Below, $R(\theta, \mu)$ for $\mu \le 0$ means $\emptyset$.
--
--   1. *Uniform-scale* (Definition 6.2): for every $\varepsilon > 0$ there is $\delta > 0$ such that for every region $R(\theta, \lambda) \in \mathcal C$, every $x \in R(\theta, \lambda)$ has $B[x; \delta] \subseteq R(\theta, \lambda + \varepsilon)$ and every $x \in R(\theta, \lambda - \varepsilon)$ has $B[x; \delta] \subseteq R(\theta, \lambda)$.
--   2. *Uniformly continuous with respect to* $\nu$ (Definition 6.3): every $R(\theta, \lambda)$ is measurable, and for every $\varepsilon > 0$ there is $\delta > 0$ such that for every region $R(\theta, \lambda) \in \mathcal C$,
--   $$\nu(R(\theta, \lambda + \delta)) \le \nu(R(\theta, \lambda)) + \varepsilon, \qquad \nu(R(\theta, \lambda)) \le \nu(R(\theta, \lambda - \delta)) + \varepsilon.$$
--
--   **Properties of methods (§6.1.2).** $f$ is *uniformly positive* with respect to a measure $\mu$ if the regions of $\mathcal C$ are measurable and some $\gamma > 0$ satisfies $\mu(A) \ge \gamma$ for every $A \in f(S)$ and every finite $S$. It has *diameter asymptotically bounded by* $L$ if almost surely there is $N$ such that for all $n > N$, $d(x, y) \le L$ for all $x, y \in A$ and every $A \in f(S_n)$; it has *asymptotically-bounded cardinality* if for some $u$, almost surely $|f(S_n)| \le u$ for all large $n$. A family $\{(\mathcal C, f_m)\}_{m \in \mathbb N}$ is *arbitrarily precise* if for every $\varepsilon > 0$ there is $N$ such that every $f_m$ with $m > N$ has diameter asymptotically bounded by $\varepsilon$.
--
--   **The density estimate (§6.4).** With $c_n(x; f) = \{A \in f(S_n) : x \in A\}$ and a reference measure $\mu$,
--   $$\hat g_n(x; f) = \begin{cases} \dfrac{1}{|c_n(x; f)|} \displaystyle\sum_{A \in c_n(x; f)} \frac{\hat P_{X,n}(A)}{\mu(A)} & \text{if } c_n(x; f) \neq \emptyset, \\ 0 & \text{if } c_n(x; f) = \emptyset. \end{cases}$$
--
--   These objects are shared by every statement of the mission: the Glivenko–Cantelli theorem for uniform-scale classes, the coverage results, and the consistency of $\hat g$.
--
--   **Formalization Note.** Observations are indexed from $0$, so $S_n = \{X_0, \dots, X_{n-1}\}$. The empirical measure counts observations with multiplicity, $\#\{i < n : X_i \in T\}/n$; the paper writes $|T \cap S_n|/n$ with $S_n$ a set, which undercounts repeated values and would make Theorem 6.1 false for laws with atoms (for $P_X = \delta_a$ it would give $1/n \to 0$). The method $f$ is still applied to the finite set $S_n$. The scale map is a function `R : Θ → ℝ → Set M` read only at positive scales; the terms $R(\theta, \lambda - \varepsilon)$ and $R(\theta, \lambda - \delta)$ of Definitions 6.2 and 6.3, which the paper leaves undefined when the scale is not positive, are read as $\emptyset$ (`regionExt`); this convention is needed for Theorem 6.1 to hold (see that theorem's note). Measures of regions are compared with addition in $[0, \infty]$ rather than truncated subtraction. Diameters are stated pairwise, not through `Metric.diam`. Uniform positivity is read per region ($\mu(A) \ge \gamma$ for each $A \in f(S)$), which is how the proof of Theorem 6.4 uses the printed "$\mu(f(S)) \ge \gamma$". In $\hat g$, $\mu(A)$ is converted to a real number, so theorems using $\hat g$ assume $\mu(A) < \infty$ for the regions the methods output.
-- source:
--   Estes, Ball & Lovell, Data Exploration by Representative Region Selection: Axioms and Convergence, SSRN preprint 3005997, pp. 5–6, 19–21, 26, Definitions 3.1–3.4, 6.1–6.3, 6.5–6.8, §6.1.1, §6.4

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology ENNReal

namespace RepRegion.Density

open Classical

variable {M Ω Θ : Type*}

/-- Definition 3.1 (p. 5): `(C, f)` is an RRS method on `M` when `f` maps every finite subset of `M`
to a finite set of regions, each of which lies in the class `C ⊆ 2^M`. -/
def IsRRSMethod (C : Set (Set M)) (f : Finset M → Finset (Set M)) : Prop :=
  ∀ S : Finset M, ∀ A ∈ f S, A ∈ C

/-- Definition 3.2 (p. 5): the coverage region `C(S; f) = ⋃_{A ∈ f(S)} A`. -/
def coverage (f : Finset M → Finset (Set M)) (S : Finset M) : Set M :=
  ⋃ A ∈ f S, A

/-- Definition 3.3 (p. 6): sample-covering, `C(S; f) ⊇ S` for every finite `S`. -/
def SampleCovering (f : Finset M → Finset (Set M)) : Prop :=
  ∀ S : Finset M, (S : Set M) ⊆ coverage f S

/-- Definition 3.4 (p. 6): sample-intersecting, every chosen region meets the sample. -/
def SampleIntersecting (f : Finset M → Finset (Set M)) : Prop :=
  ∀ S : Finset M, ∀ A ∈ f S, (A ∩ (S : Set M)).Nonempty

/-- §6.1.1 (p. 19): the sample `S_n = {X₁, …, X_n}` as a finite set; indices are 0-based, so
`S_n = {X 0 ω, …, X (n-1) ω}`. -/
noncomputable def sample (X : ℕ → Ω → M) (n : ℕ) (ω : Ω) : Finset M :=
  (Finset.range n).image (fun i => X i ω)

/-- §6.1.1 (p. 19): the empirical measure `P̂_{X,n}(T)`, the proportion of the first `n`
observations that fall in `T`, counted with multiplicity. At `n = 0` it is `0`. -/
noncomputable def empFreq (X : ℕ → Ω → M) (n : ℕ) (ω : Ω) (T : Set M) : ℝ :=
  (((Finset.range n).filter (fun i => X i ω ∈ T)).card : ℝ) / n

/-- §6.1.1 (p. 19): the support of a measure, the points all of whose closed balls of positive
radius have positive measure. -/
def supp [PseudoMetricSpace M] [MeasurableSpace M] (ν : Measure M) : Set M :=
  {y | ∀ r : ℝ, 0 < r → 0 < ν (Metric.closedBall y r)}

/-- Definition 6.1 (p. 20): `(C, Θ, R)` is a scalable class of regions: `C` is the image of some
`Ξ ⊆ Θ × ℝ⁺` under `R`, and `R θ` is non-decreasing in the scale. `R` is read only at scales
`λ > 0`. -/
def IsScalableClass (C : Set (Set M)) (R : Θ → ℝ → Set M) : Prop :=
  (∃ Ξ : Set (Θ × ℝ), (∀ p ∈ Ξ, 0 < p.2) ∧ C = {A | ∃ p ∈ Ξ, A = R p.1 p.2}) ∧
  ∀ (θ : Θ) (l l' : ℝ), 0 < l → l ≤ l' → R θ l ⊆ R θ l'

/-- The region `R(θ, μ)` with the convention that a region at a non-positive scale is empty
(`R` is only defined on `Θ × ℝ⁺`). Used for the terms `R(θ, λ - ε)`, `R(θ, λ - δ)` of
Definitions 6.2 and 6.3. -/
def regionExt (R : Θ → ℝ → Set M) (θ : Θ) (μ : ℝ) : Set M :=
  if 0 < μ then R θ μ else ∅

/-- Definition 6.2 (p. 20): uniform-scale. For every `ε > 0` there is `δ > 0` such that for every
region `R(θ, λ) ∈ C` (`λ > 0`): every point of `R(θ, λ)` has its closed `δ`-ball inside
`R(θ, λ + ε)`, and every point of `R(θ, λ - ε)` has its closed `δ`-ball inside `R(θ, λ)`
(with `R(θ, λ - ε) = ∅` when `λ ≤ ε`). -/
def UniformScale [PseudoMetricSpace M] (C : Set (Set M)) (R : Θ → ℝ → Set M) : Prop :=
  IsScalableClass C R ∧
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (θ : Θ) (l : ℝ), 0 < l → R θ l ∈ C →
    (∀ x ∈ R θ l, Metric.closedBall x δ ⊆ R θ (l + ε)) ∧
    (∀ x ∈ regionExt R θ (l - ε), Metric.closedBall x δ ⊆ R θ l)

/-- Definition 6.3 (p. 20): `R` is uniformly continuous with respect to `ν`. Every `R(θ, λ)`
(`λ > 0`) is measurable, and for every `ε > 0` there is `δ > 0` such that for every region
`R(θ, λ) ∈ C`: `ν(R(θ, λ + δ)) - ν(R(θ, λ)) ≤ ε` and `ν(R(θ, λ)) - ν(R(θ, λ - δ)) ≤ ε`, written
with addition in `ℝ≥0∞`, and with `R(θ, λ - δ) = ∅` when `λ ≤ δ`. -/
def UnifContWrt [MeasurableSpace M] (C : Set (Set M)) (R : Θ → ℝ → Set M) (ν : Measure M) :
    Prop :=
  IsScalableClass C R ∧ (∀ (θ : Θ) (l : ℝ), 0 < l → MeasurableSet (R θ l)) ∧
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (θ : Θ) (l : ℝ), 0 < l → R θ l ∈ C →
    ν (R θ (l + δ)) ≤ ν (R θ l) + ENNReal.ofReal ε ∧
    ν (R θ l) ≤ ν (regionExt R θ (l - δ)) + ENNReal.ofReal ε

/-- Definition 6.5 (p. 21): `f` is uniformly positive with respect to `μ`: the regions of `C` are
measurable, and there is `γ > 0` with `μ(A) ≥ γ` for every region `A ∈ f(S)` and every finite
`S`. -/
def UniformlyPositive [MeasurableSpace M] (C : Set (Set M)) (f : Finset M → Finset (Set M))
    (μ : Measure M) : Prop :=
  (∀ A ∈ C, MeasurableSet A) ∧
  ∃ γ : ℝ, 0 < γ ∧ ∀ S : Finset M, ∀ A ∈ f S, ENNReal.ofReal γ ≤ μ A

/-- Definition 6.7 (p. 21) with a given bound `L`: almost surely there is `N` such that for all
`n > N`, any two points of any region of `f(S_n)` are at distance at most `L`. -/
def AsympDiamLE [PseudoMetricSpace M] [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → M)
    (f : Finset M → Finset (Set M)) (L : ℝ) : Prop :=
  ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ n > N, ∀ A ∈ f (sample X n ω), ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ L

/-- Definition 6.7 (p. 21): asymptotically-bounded diameter, `∃ L` outside the almost-sure
quantifier. -/
def AsympBoundedDiam [PseudoMetricSpace M] [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → M)
    (f : Finset M → Finset (Set M)) : Prop :=
  ∃ L : ℝ, AsympDiamLE P X f L

/-- p. 21 ("we define asymptotically-bounded cardinality similarly", after Definitions 6.6 and
6.7): there is `u` such that almost surely, eventually `|f(S_n)| ≤ u`. -/
def AsympBoundedCard [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → M)
    (f : Finset M → Finset (Set M)) : Prop :=
  ∃ u : ℕ, ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ n > N, (f (sample X n ω)).card ≤ u

/-- Definition 6.8 (p. 21): the family `{(C, f_m)}` is arbitrarily precise: for every `ε > 0`
there is `N` such that for all `m > N`, `f_m` has diameter asymptotically bounded by `ε`. -/
def ArbitrarilyPrecise [PseudoMetricSpace M] [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → M) (f : ℕ → Finset M → Finset (Set M)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m > N, AsympDiamLE P X (f m) ε

/-- §6.4 (p. 26): `c(S, x; f) = {A ∈ f(S) : x ∈ A}`, the chosen regions that cover `x`. -/
noncomputable def coverSet (f : Finset M → Finset (Set M)) (S : Finset M) (x : M) :
    Finset (Set M) :=
  (f S).filter (fun A => x ∈ A)

/-- §6.4 (p. 26): the density estimate `ĝ_n(x; f)`: the average of `P̂_{X,n}(A) / μ(A)` over
the regions `A ∈ c_n(x; f)`, and `0` when no chosen region covers `x`. -/
noncomputable def ghat [MeasurableSpace M] (μ : Measure M) (f : Finset M → Finset (Set M))
    (X : ℕ → Ω → M) (n : ℕ) (ω : Ω) (x : M) : ℝ :=
  if coverSet f (sample X n ω) x = ∅ then 0
  else (1 / ((coverSet f (sample X n ω) x).card : ℝ)) *
    ∑ A ∈ coverSet f (sample X n ω) x, empFreq X n ω A / (μ A).toReal

end RepRegion.Density


