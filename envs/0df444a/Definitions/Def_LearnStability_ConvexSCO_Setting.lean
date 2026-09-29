-- Prove2me | Definitions.Def_LearnStability_ConvexSCO_Setting
-- name    : LearnStability_ConvexSCO_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T18:13:46.170172+00:00
-- url     : https://prove2.me/theorems/1ebb2120-4eb4-4c72-be15-f1c4c6901187
-- title:
--   General Learning Setting: risks, learning rules, consistency, AERM, generalization, uniform- and average-RO stability
-- statement:
--   This file fixes the vocabulary of Vapnik's *General Learning Setting* as used by Shalev-Shwartz, Shamir, Srebro and Sridharan.
--
--   Let $Z$ be a measurable space of instances, $\mathcal H$ a set of hypotheses and $f(h;z)$ a real objective. A distribution $D$ on $Z$ is fixed but unknown; a sample of size $m$ is $S=(z_1,\dots,z_m)\sim D^m$.
--
--   1. **Risks.** $F(h)=\mathbb E_{z\sim D}[f(h;z)]$, $F_S(h)=\frac1m\sum_{i=1}^m f(h;z_i)$, $F^*=\inf_{h\in\mathcal H}F(h)$, and the minimal empirical risk $F_S(\hat h_S)=\inf_{h\in\mathcal H}F_S(h)$ (only this value is used, no minimizer is chosen).
--   2. **Learning rules.** A rule maps every sample $S\in Z^m$ to a hypothesis $A(S)$. It is *measurable* when $(S,z)\mapsto f(A(S);z)$ is jointly measurable for every $m$.
--   3. **Consistency** with rate $\varepsilon$ under $D$ (Eq. (2)): for every $m\ge1$,
--   $$\mathbb E_{S\sim D^m}\big[F(A(S))-F^*\big]\le\varepsilon(m).$$
--   4. **AERM** with rate $\varepsilon$: $\mathbb E_{S\sim D^m}[F_S(A(S))-F_S(\hat h_S)]\le\varepsilon(m)$. **Generalization** with rate $\varepsilon$: $\mathbb E_{S\sim D^m}[|F(A(S))-F_S(A(S))|]\le\varepsilon(m)$.
--   5. **Uniform-RO stability** with rate $\varepsilon$ (Definition 4): for every $m\ge1$, every sample $S$, every choice of replacements $z'_1,\dots,z'_m$ and every $z'\in Z$,
--   $$\frac1m\sum_{i=1}^m\big|f(A(S^{(i)});z')-f(A(S);z')\big|\le\varepsilon(m),$$
--   where $S^{(i)}$ is $S$ with $z_i$ replaced by $z'_i$.
--   6. **Average-RO stability** with rate $\varepsilon$ under $D$ (Definition 5): with $S,(z'_1,\dots,z'_m)\sim D^m$ independent,
--   $$\Big|\frac1m\sum_{i=1}^m\mathbb E\big[f(A(S^{(i)});z'_i)-f(A(S);z'_i)\big]\Big|\le\varepsilon(m).$$
--
--   These notions are the language in which the paper's stability argument for stochastic convex optimization (Theorem 8, Theorem 2) is phrased.
--
--   **Formalization Note** Samples are functions $\mathrm{Fin}\,m\to Z$ and $D^m$ is the product measure; $S^{(i)}$ is `Function.update S i (S' i)`. All rate conditions are imposed for $m\ge1$. Measurability of rules and of $S\mapsto\inf_hF_S(h)$ is not discussed in the paper; it is the series' standing convention, stated as separate predicates, because without it the expectations are Lean's junk value $0$.
-- source:
--   Shalev-Shwartz, Shamir, Srebro and Sridharan, Learnability, Stability and Uniform Convergence, JMLR 11 (2010), pp. 2637–2639 (§2, Eq. (2), Table 1, definitions of ERM, AERM, generalization) and p. 2648, Definitions 4 and 5

import Mathlib

open MeasureTheory

namespace LearnStability.ConvexSCO

variable {H Z : Type*} [MeasurableSpace Z]

/-- The law `D^m` of an i.i.d. sample `S = (z_1, …, z_m)` of size `m` drawn from `D`
(Shalev-Shwartz et al. 2010, §2, p. 2637). -/
noncomputable def sampleLaw (D : Measure Z) (m : ℕ) : Measure (Fin m → Z) :=
  Measure.pi fun _ : Fin m => D

/-- The risk `F(h) = E_{z∼D}[f(h; z)]` of a hypothesis `h` (p. 2637). -/
noncomputable def risk (f : H → Z → ℝ) (D : Measure Z) (h : H) : ℝ :=
  ∫ z, f h z ∂D

/-- The empirical risk `F_S(h) = (1/m) ∑_{i=1}^m f(h; z_i)` on a sample `S` of size `m`
(p. 2638). -/
noncomputable def empRisk (f : H → Z → ℝ) {m : ℕ} (S : Fin m → Z) (h : H) : ℝ :=
  (∑ i, f h (S i)) / m

/-- The optimal risk `F* = inf_{h ∈ H} F(h)` over the whole hypothesis type (p. 2638). -/
noncomputable def optRisk (f : H → Z → ℝ) (D : Measure Z) : ℝ :=
  ⨅ h, risk f D h

/-- The minimal empirical risk `F_S(ĥ_S) = inf_{h ∈ H} F_S(h)` (p. 2639). Only the value of
the infimum is used, as in the paper; no minimiser is chosen. -/
noncomputable def ermValue (f : H → Z → ℝ) {m : ℕ} (S : Fin m → Z) : ℝ :=
  ⨅ h, empRisk f S h

/-- A learning rule `A : ∪_m Z^m → H` (p. 2637) is *measurable* for the objective `f` if, for
every sample size `m`, the map `(S, z) ↦ f(A(S); z)` is jointly measurable. This is the
series' standing measurability convention; the paper does not discuss measurability. -/
def IsMeasurableRule (f : H → Z → ℝ) (A : (m : ℕ) → (Fin m → Z) → H) : Prop :=
  ∀ m : ℕ, Measurable (fun p : (Fin m → Z) × Z => f (A m p.1) p.2)

/-- The minimal empirical risk `S ↦ inf_h F_S(h)` is measurable for every sample size
(standing measurability convention of the series). -/
def ErmValueMeasurable (f : H → Z → ℝ) : Prop :=
  ∀ m : ℕ, Measurable (fun S : Fin m → Z => ermValue f S)

/-- `A` is *consistent with rate* `ε` under `D` (Eq. (2), p. 2638):
`E_{S∼D^m}[F(A(S)) − F*] ≤ ε(m)` for every `m ≥ 1`. -/
def IsConsistentUnder (f : H → Z → ℝ) (A : (m : ℕ) → (Fin m → Z) → H) (D : Measure Z)
    (ε : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∫ S, (risk f D (A m S) - optRisk f D) ∂(sampleLaw D m) ≤ ε m

/-- `A` is an *AERM with rate* `ε` under `D` (p. 2639):
`E_{S∼D^m}[F_S(A(S)) − F_S(ĥ_S)] ≤ ε(m)` for every `m ≥ 1`. -/
def IsAERMUnder (f : H → Z → ℝ) (A : (m : ℕ) → (Fin m → Z) → H) (D : Measure Z)
    (ε : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∫ S, (empRisk f S (A m S) - ermValue f S) ∂(sampleLaw D m) ≤ ε m

/-- `A` *generalizes with rate* `ε` under `D` (p. 2639):
`E_{S∼D^m}[|F(A(S)) − F_S(A(S))|] ≤ ε(m)` for every `m ≥ 1`. -/
def GeneralizesUnder (f : H → Z → ℝ) (A : (m : ℕ) → (Fin m → Z) → H) (D : Measure Z)
    (ε : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∫ S, |risk f D (A m S) - empRisk f S (A m S)| ∂(sampleLaw D m) ≤ ε m

/-- `A` is *uniform-RO stable with rate* `ε` (Definition 4, p. 2648): for every `m ≥ 1`, every
sample `S`, every vector of replacements `S'` and every test point `z'`,
`(1/m) ∑_i |f(A(S^{(i)}); z') − f(A(S); z')| ≤ ε(m)`, where `S^{(i)}` is `S` with its `i`-th
entry replaced by `S' i`. No distribution is involved. -/
def UniformROStable (f : H → Z → ℝ) (A : (m : ℕ) → (Fin m → Z) → H) (ε : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ (S S' : Fin m → Z) (z' : Z),
    (∑ i, |f (A m (Function.update S i (S' i))) z' - f (A m S) z'|) / m ≤ ε m

/-- `A` is *average-RO stable with rate* `ε` under `D` (Definition 5, p. 2648): for every
`m ≥ 1`, with `S, S' ∼ D^m` independent,
`|(1/m) ∑_i E[f(A(S^{(i)}); z'_i) − f(A(S); z'_i)]| ≤ ε(m)`. -/
def AverageROStableUnder (f : H → Z → ℝ) (A : (m : ℕ) → (Fin m → Z) → H) (D : Measure Z)
    (ε : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    |(∑ i, ∫ p, (f (A m (Function.update p.1 i (p.2 i))) (p.2 i) - f (A m p.1) (p.2 i))
        ∂((sampleLaw D m).prod (sampleLaw D m))) / m| ≤ ε m

end LearnStability.ConvexSCO


