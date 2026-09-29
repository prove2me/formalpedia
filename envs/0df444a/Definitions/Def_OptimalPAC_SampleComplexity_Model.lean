-- Prove2me | Definitions.Def_OptimalPAC_SampleComplexity_Model
-- name    : OptimalPAC_SampleComplexity_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T21:25:44.898062+00:00
-- url     : https://prove2.me/theorems/59e58b48-cf20-474a-a42a-f08e7766d45d
-- title:
--   Realizable PAC model: VC dimension, consistent classifiers, error, majority vote, well-behaved classes and the sample complexity $\mathcal M(\varepsilon,\delta)$
-- statement:
--   The objects of Hanneke's realizable PAC model.
--
--   Fix an instance space $\mathcal X$ equipped with a $\sigma$-algebra and the label space $\mathcal Y=\{-1,+1\}$. A **classifier** is a measurable map $h:\mathcal X\to\mathcal Y$, and the **concept space** $\mathbb C$ is a set of classifiers. A **data set** is a finite sequence $S=\{(x_1,y_1),\ldots,(x_k,y_k)\}$ in $\mathcal X\times\mathcal Y$; the union of two sequences is their concatenation.
--
--   1. **Shattering and VC dimension.** A sequence $x_1,\ldots,x_k$ is **shattered** by $\mathbb C$ if for all $y_1,\ldots,y_k\in\mathcal Y$ some $h\in\mathbb C$ has $h(x_i)=y_i$ for every $i$. The **VC dimension** $d$ of $\mathbb C$ is the largest $k$ such that some sequence of $k$ points is shattered, and $\infty$ if there is no largest such $k$.
--   2. **Consistent classifiers.** $\mathbb C[S]=\{h\in\mathbb C:\ h(x)=y\text{ for all }(x,y)\in S\}$.
--   3. **Labelled sample.** For a target $f^\star$ and points $x_1,\ldots,x_m$, $(x,f^\star(x))$ denotes the data set $\{(x_1,f^\star(x_1)),\ldots,(x_m,f^\star(x_m))\}$.
--   4. **Error.** $\mathrm{ER}(h)=\{x:\ h(x)\ne f^\star(x)\}$ and, for a probability measure $P$, $\mathrm{er}_P(h;f^\star)=P(\mathrm{ER}(h))$.
--   5. **Truncated logarithms.** $\mathrm{Log}(z)=\ln(\max\{z,e\})$ and $\mathrm{Log}_2(z)=\log_2(\max\{z,2\})$.
--   6. **Sample-consistent learner.** A map $L$ from data sets to classifiers with $L(S)\in\mathbb C[S]$ whenever $\mathbb C[S]\ne\emptyset$.
--   7. **Majority vote.** $\mathrm{Majority}(h_1,\ldots,h_k)(x)=\mathrm{sign}\left(\sum_{i=1}^k h_i(x)\right)=2\mathbb 1\left[\sum_{i=1}^k h_i(x)\ge0\right]-1$; ties are resolved in favour of $+1$.
--   8. **Sample complexity** (Definition 1). For $\varepsilon,\delta\in(0,1)$, $\mathcal M(\varepsilon,\delta)$ is the smallest $m\in\mathbb N\cup\{0\}$ for which there is a learning algorithm $\mathcal A$ such that for every probability measure $\mathcal P$ on $\mathcal X$ and every $f^\star\in\mathbb C$, if $X_1,\ldots,X_m$ are independent with law $\mathcal P$ and $\hat h=\mathcal A((X_i,f^\star(X_i))_{i\le m})$, then
--   $$\mathbb P\left(\mathrm{er}_{\mathcal P}(\hat h;f^\star)>\varepsilon\right)\le\delta;$$
--   $\mathcal M(\varepsilon,\delta)=\infty$ if no such $m$ exists.
--   9. **Measurability conditions.** $\mathbb C$ is **well-behaved** if, for every $f^\star\in\mathbb C$, every probability measure $Q$, every $m$ and every $t$, the event "some $h\in\mathbb C$ consistent with $(Z_i,f^\star(Z_i))_{i\le m}$ has $\mathrm{er}_Q(h;f^\star)>t$" is null-measurable under $Q^m$, and the double-sample event of Blumer, Ehrenfeucht, Haussler and Warmuth (some $h\in\mathbb C$ agrees with $f^\star$ on a first sample of size $m$ and disagrees with it on at least $tm/2$ points of a second one) is null-measurable under $Q^m\otimes Q^m$. A learner $L$ is **measurable** if, for every $k$, $((x_i,y_i)_{i\le k},x)\mapsto L(\{(x_i,y_i)\}_{i\le k})(x)$ is jointly measurable.
--
--   These are the objects in which Theorem 2 and the steps of its proof are stated.
--
--   **Formalization Note** Labels are `Bool`, with `true` for $+1$ and `false` for $-1$; the majority vote is `true` iff at least as many voters say `true` as `false`. Data sets are lists. The VC dimension is a supremum in $\mathbb N\cup\{\infty\}$. The error is the real value of the (outer) measure of $\mathrm{ER}(h)$. In $\mathcal M(\varepsilon,\delta)$ the algorithm is a deterministic map from data sets to measurable classifiers, chosen before $\mathcal P$ and $f^\star$; the failure event is bounded in outer measure, and $\mathcal M=\infty$ is the infimum of the empty set in $\mathbb N\cup\{\infty\}$. The paper also admits randomized algorithms (footnote 2), which can only make $\mathcal M$ smaller, so an upper bound on this $\mathcal M$ implies the paper's. The two measurability conditions are the explicit form of the paper's blanket assumption (p. 3) that the events in its probability claims are measurable; every countable class of measurable classifiers is well-behaved and has a measurable sample-consistent learner (the first consistent classifier in an enumeration).
-- source:
--   Hanneke, The Optimal Sample Complexity of PAC Learning, arXiv:1507.00473v4, pp. 1–3 (§2: classifiers, concept space, er_P, data sets, C[S], shattering, VC dimension, Log, Log_2, measurability assumption), p. 2 Definition 1, p. 6 (§4.2: learner L, Majority), p. 8 (ER(h))

import Mathlib

/-!
# Hanneke (2016), *The Optimal Sample Complexity of PAC Learning*: the model

S. Hanneke, *The Optimal Sample Complexity of PAC Learning*, arXiv:1507.00473v4, §2 (pp. 1–3),
Definition 1 (p. 2), §4.2 (p. 6) and the proof of Theorem 2 (p. 8).

Instances live in a measurable space `X`; the label space `𝒴 = {-1, +1}` is encoded as `Bool`
(`true` = `+1`, `false` = `-1`). A data set is a finite sequence, encoded as a `List (X × Bool)`;
the paper's `∪` of sequences is `++`.
-/

open MeasureTheory

namespace OptimalPAC.SampleComplexity

/-- A sequence `x₁, …, x_k` of points is **shattered** by `C` (p. 2): every labelling
`y₁, …, y_k` is realized by some classifier of `C`. -/
def Shatters {X : Type*} (C : Set (X → Bool)) {k : ℕ} (x : Fin k → X) : Prop :=
  ∀ y : Fin k → Bool, ∃ h ∈ C, ∀ i, h (x i) = y i

/-- The **VC dimension** of `C` (p. 2): the largest `k` such that some sequence of `k` points is
shattered by `C`, and `⊤` if there is no largest such `k`. -/
noncomputable def vcDim {X : Type*} (C : Set (X → Bool)) : ℕ∞ :=
  ⨆ (k : ℕ) (_ : ∃ x : Fin k → X, Shatters C x), (k : ℕ∞)

/-- `ℂ[S]` (p. 2): the classifiers of `C` consistent with the data set `S`. -/
def consistent {X : Type*} (C : Set (X → Bool)) (S : List (X × Bool)) : Set (X → Bool) :=
  {h | h ∈ C ∧ ∀ p ∈ S, h p.1 = p.2}

/-- The labelled sample `(x₁, f(x₁)), …, (x_m, f(x_m))` of the points `x` under the target `f`
(p. 2, `(S_x, f⋆(S_x))`; p. 8, `𝕊_{1:m}`). -/
def labeled {X : Type*} (f : X → Bool) {m : ℕ} (x : Fin m → X) : List (X × Bool) :=
  List.ofFn (fun i : Fin m => (x i, f (x i)))

/-- The error region `ER(h) = {x : h(x) ≠ f⋆(x)}` of `h` with respect to the target `f` (p. 8). -/
def ER {X : Type*} (h f : X → Bool) : Set X :=
  {x | h x ≠ f x}

/-- The error `er_P(h; f⋆) = P(x : h(x) ≠ f⋆(x))` (p. 2), as a real number (`P` is a probability
measure in every use, so `toReal` loses nothing). -/
noncomputable def er {X : Type*} [MeasurableSpace X] (P : Measure X) (h f : X → Bool) : ℝ :=
  (P (ER h f)).toReal

/-- `Log(z) = ln(max{z, e})` (p. 3). -/
noncomputable def Log (z : ℝ) : ℝ :=
  Real.log (max z (Real.exp 1))

/-- `Log₂(z) = log₂(max{z, 2})` (p. 3). -/
noncomputable def Log2 (z : ℝ) : ℝ :=
  Real.logb 2 (max z 2)

/-- `L` is a **sample-consistent learner** for `C` (p. 6): whenever `ℂ[S] ≠ ∅`, `L(S) ∈ ℂ[S]`.
On data sets with `ℂ[S] = ∅` (where the paper leaves `L` undefined) its value is unconstrained. -/
def IsConsistentLearner {X : Type*} (C : Set (X → Bool)) (L : List (X × Bool) → X → Bool) :
    Prop :=
  ∀ S, (consistent C S).Nonempty → L S ∈ consistent C S

/-- Measurability of a learner (explicit form of the measurability assumption of p. 3): for every
sample size `k`, the map `((x₁,y₁),…,(x_k,y_k)), x ↦ L({(x_i,y_i)})(x)` is jointly measurable. -/
def LearnerMeasurable {X : Type*} [MeasurableSpace X] (L : List (X × Bool) → X → Bool) : Prop :=
  ∀ k : ℕ, Measurable (fun p : (Fin k → X × Bool) × X => L (List.ofFn p.1) p.2)

/-- The event of Lemma 4 (p. 8) under the law `Q`: some classifier of `C` consistent with the
labelled sample `(z_i, f(z_i))_{i ≤ m}` has error larger than `t`. -/
def consistentBadEvent {X : Type*} [MeasurableSpace X] (C : Set (X → Bool)) (Q : Measure X)
    (f : X → Bool) (m : ℕ) (t : ℝ) : Set (Fin m → X) :=
  {z | ∃ h ∈ consistent C (labeled f z), t < er Q h f}

/-- The double-sample event of Blumer, Ehrenfeucht, Haussler and Warmuth (1989): some `h ∈ C`
agrees with the target `f` on every point of the first sample and disagrees with it on at least
`t m / 2` points of the second. -/
def doubleSampleEvent {X : Type*} (C : Set (X → Bool)) (f : X → Bool) (t : ℝ) (m : ℕ) :
    Set ((Fin m → X) × (Fin m → X)) :=
  {p | ∃ h ∈ C, (∀ i, h (p.1 i) = f (p.1 i)) ∧
    t * m / 2 ≤ ({i : Fin m | h (p.2 i) ≠ f (p.2 i)}.ncard : ℝ)}

/-- `C` is **well-behaved** (explicit form of the measurability assumption of p. 3, in the sense of
Blumer et al. 1989): for every target `f ∈ C`, every probability measure `Q`, every `m` and `t`,
the event of Lemma 4 is null-measurable under `Qᵐ` and the double-sample event is null-measurable
under `Qᵐ ⊗ Qᵐ`. Every countable class of measurable classifiers is well-behaved. -/
def WellBehaved {X : Type*} [MeasurableSpace X] (C : Set (X → Bool)) : Prop :=
  ∀ f ∈ C, ∀ Q : Measure X, IsProbabilityMeasure Q → ∀ (m : ℕ) (t : ℝ),
    NullMeasurableSet (consistentBadEvent C Q f m t) (Measure.pi fun _ : Fin m => Q) ∧
    NullMeasurableSet (doubleSampleEvent C f t m)
      ((Measure.pi fun _ : Fin m => Q).prod (Measure.pi fun _ : Fin m => Q))

/-- The majority classifier (p. 6): `Majority(h₁,…,h_k)(x) = sign(∑ h_i(x)) = 2·𝟙[∑ h_i(x) ≥ 0] − 1`.
With `true = +1`, this is `+1` iff at least as many `h_i(x)` are `+1` as are `−1`: **ties go to
`+1`**, as printed. -/
def majority {X : Type*} (hs : List (X → Bool)) : X → Bool :=
  fun x => decide (hs.countP (fun h => h x = false) ≤ hs.countP (fun h => h x = true))

/-- The **sample complexity** `𝓜(ε, δ)` of `(ε, δ)`-PAC learning `C` (Definition 1, p. 2): the
smallest `m` for which some learning algorithm `A`, mapping data sets to classifiers (measurable
functions, p. 2), satisfies, for every probability measure `P` on `X` and every target `f ∈ C`,
`ℙ(er_P(A(𝕏_{1:m}, f(𝕏_{1:m}))) > ε) ≤ δ`; `⊤` (`= ∞`) if there is no such `m`. The algorithm is
chosen before `P` and `f` and sees only the labelled sample. -/
noncomputable def sampleComplexity {X : Type*} [MeasurableSpace X] (C : Set (X → Bool))
    (ε δ : ℝ) : ℕ∞ :=
  ⨅ (m : ℕ) (_ : ∃ A : List (X × Bool) → X → Bool, (∀ S, Measurable (A S)) ∧
      ∀ P : Measure X, IsProbabilityMeasure P → ∀ f ∈ C,
        Measure.pi (fun _ : Fin m => P) {x | ε < er P (A (labeled f x)) f} ≤ ENNReal.ofReal δ),
    (m : ℕ∞)

end OptimalPAC.SampleComplexity


