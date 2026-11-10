-- Prove2me | Definitions.Def_DistRobustHalfspace_Main_Testers
-- name    : DistRobustHalfspace_Main_Testers
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:16:51.550973+00:00
-- url     : https://prove2.me/theorems/c886fb15-f2cb-4277-b20e-d55d6b6ff214
-- title:
--   Halfspaces on ℝⁿ, distances, general and non-adaptive query testers, robust (Def. 1.2) and picky (Def. 1.6) testing
-- statement:
--   The objects of §1 (pp. 1–4) of the paper.
--
--   **Space, functions, halfspaces.** $\mathbb R^n$ is `Rn n` (Euclidean space on coordinates $0,\dots,n-1$, Borel $\sigma$-algebra). A Boolean function $f:\mathbb R^n\to\{\pm1\}$ is a real-valued function that is Borel measurable and takes only the values $1$ and $-1$ (`IsBoolFn`; footnote 1, p. 2). $\operatorname{sign}(r)=+1$ for $r\ge 0$ and $-1$ for $r<0$ (`sgn`; the paper does not fix $\operatorname{sign}(0)$). A **halfspace** is $f(x)=\operatorname{sign}(\langle w,x\rangle-t)$ for some $w\in\mathbb R^n$, $t\in\mathbb R$ (p. 1); $w=0$ is allowed, so both constant functions are halfspaces. $\operatorname{dist}_D(f,g)=\Pr_{x\sim D}[f(x)\ne g(x)]$ (p. 1), and $f$ is **$\varepsilon$-far** from halfspaces under $D$ when $\operatorname{dist}_D(f,h)>\varepsilon$ for every halfspace $h$. Distributions are Borel probability measures (`ProbabilityMeasure`); `gaussPM n` is the standard Gaussian $\mathcal N(0,I_n)$ (Mathlib's `stdGaussian`).
--
--   **Testers.** A `Tester n α` is a randomized algorithm with sample access to $D$ and non-adaptive query access to $f$, with outputs in $\alpha$. It draws samples $S=(y_i)_{i\in I}$ i.i.d. from $D$ ($I$ finite) and a random seed $\omega\sim\mu$ from an arbitrary probability space (for instance Gaussian vectors), independently. Its query points $Q(S,\omega)_j$, $j\in J$ ($J$ finite), are fixed by the samples and the seed before any answer is seen (**non-adaptive**). Its output is $\delta(S,\omega,(f(Q(S,\omega)_j))_j)$. The numbers of samples and queries are $|I|$ and $|J|$, the same on every run. `prob T D f E` is the probability that the output satisfies $E$. `IsMeasurable` says the query map and the decision rule are jointly measurable, so that these probabilities are probabilities of events. A tester is fixed before $D$ and $f$, so it sees them only through its samples and answers.
--
--   **Definition 1.2** (p. 2). A tester with outputs $\{\mathrm{Accept},\mathrm{Reject},\mathrm{Tantrum}\}$ is a **$C$-robust halfspace tester** for proximity parameter $\varepsilon$ if, for **every** distribution $D$ (not necessarily in $C$) and every Boolean $f$, the following hold simultaneously with probability at least $3/4$:
--   - (Completeness) if $f$ is a halfspace, the output is Accept or Tantrum;
--   - (Soundness) if $f$ is $\varepsilon$-far from halfspaces under $D$, the output is Reject or Tantrum;
--   - (Assertiveness) if $D\in C$, the output is not Tantrum.
--
--   **Definition 1.6** (p. 4). A tester with outputs $\{\mathrm{Accept}=\texttt{true},\mathrm{Reject}=\texttt{false}\}$ is a **$(D^*,C)$-picky halfspace tester** for $\varepsilon$ if, for every $D\in C$ and every Boolean $f$, the following hold simultaneously with probability at least $3/4$: (Completeness) if $f$ is a halfspace and $D=D^*$, it Accepts; (Soundness) if $f$ is $\varepsilon$-far from halfspaces under $D$, it Rejects.
--
--   Both predicates include `IsMeasurable`. The picky predicate also includes the standing condition $D^*\in C$.
--
--   **Formalization Note.** "The following hold with probability at least $3/4$" is read jointly: one event, the conjunction of the implications. The output space $\{\bot\}\cup\mathbb R$ of Lemma 2.21 is `Option ℝ`, with the $\sigma$-algebra of $\mathrm{Unit}\oplus\mathbb R$. `sign(0) = +1` fixes the boundary convention throughout; an arbitrary input distribution may charge the boundary.
--
--   **General query access.** `AdaptiveTester` models the general algorithms in Definitions 1.2 and 1.6 and Proposition A.1. At stage $i$, its query is a measurable function of the samples, seed, and preceding answers. The answer array begins at zero and is updated at index $i$ after the query, so unqueried values cannot be inspected. After its fixed finite query budget the decision reads the transcript. Samples may be drawn in advance and consumed as needed; early stopping is padded with ignored queries. `AdaptiveTester.IsRobust` and `.IsPicky` give the same joint guarantees as above, with $D^*\in C$ included in `.IsPicky`. `Tester` is the non-adaptive model used for the upper-bound constructions.
-- source:
--   Xi Chen, Renato Ferreira Pinto Jr., Nathaniel Harms, Rocco A. Servedio, Distribution-Robust Halfspace Testing, 2026 (STOC 2027 submission manuscript, sha256 545c331d…1018a87), §1, pp. 1–4 (PDF 3–6): p. 1 (halfspaces, dist_D), footnote 1 p. 2, Definition 1.2 p. 2, Definition 1.6 p. 4

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace DistRobustHalfspace.Main

/-- The ambient space `ℝⁿ`, as the Euclidean space on coordinates `Fin n` (Borel σ-algebra). -/
abbrev Rn (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- The `±1`-valued sign used by halfspaces: `sign(r) = +1` for `r ≥ 0` and `-1` for `r < 0`.
The paper never fixes `sign(0)`; `sign(0) = +1` is the convention chosen here. -/
noncomputable def sgn (r : ℝ) : ℝ := if 0 ≤ r then 1 else -1

/-- A Boolean function `f : ℝⁿ → {±1}`, encoded as a real-valued function taking only the values
`1` and `-1`, and Borel measurable (footnote 1, p. 2 of the paper). -/
def IsBoolFn {n : ℕ} (f : Rn n → ℝ) : Prop :=
  Measurable f ∧ ∀ x, f x = 1 ∨ f x = -1

/-- `f` is a halfspace (a linear classifier, p. 1): `f(x) = sign(⟨w, x⟩ − t)` for every `x`, for
some `w ∈ ℝⁿ` and `t ∈ ℝ`. `w = 0` is allowed, so the two constant functions are halfspaces. -/
def IsHalfspace {n : ℕ} (f : Rn n → ℝ) : Prop :=
  ∃ (w : Rn n) (t : ℝ), ∀ x, f x = sgn (⟪w, x⟫ - t)

/-- `dist_D(f, g) = P_{x∼D}[f(x) ≠ g(x)]` (p. 1). -/
noncomputable def distD {n : ℕ} (D : ProbabilityMeasure (Rn n)) (f g : Rn n → ℝ) : ℝ :=
  ((D : Measure (Rn n)) {x | f x ≠ g x}).toReal

/-- `f` is `ε`-far from halfspaces under `D`: `dist_D(f, h) > ε` for every halfspace `h`. -/
def FarFromHalfspaces {n : ℕ} (D : ProbabilityMeasure (Rn n)) (f : Rn n → ℝ) (ε : ℝ) : Prop :=
  ∀ h : Rn n → ℝ, IsHalfspace h → ε < distD D f h

/-- The standard Gaussian `N(0, Iₙ)` on `ℝⁿ` as a probability measure (Mathlib's `stdGaussian`). -/
noncomputable def gaussPM (n : ℕ) : ProbabilityMeasure (Rn n) :=
  ⟨stdGaussian (Rn n), inferInstance⟩

/-- The three outputs of a distribution-robust tester. -/
inductive Verdict
  | accept
  | reject
  | tantrum
  deriving DecidableEq

instance : MeasurableSpace Verdict := ⊤

/-- The output space `{⊥} ∪ ℝ` of the threshold estimator (Lemma 2.21), `none = ⊥`, with the
σ-algebra transported from `Unit ⊕ ℝ`. -/
instance instMeasurableSpaceOptionReal : MeasurableSpace (Option ℝ) :=
  MeasurableSpace.map (fun x : Unit ⊕ ℝ => Sum.elim (fun _ => none) some x) inferInstance

/-- A randomized tester on `ℝⁿ` with output in `α`, sample access to an input distribution `D`
and **non-adaptive** query access to a function `f`.

It draws the samples `S = (y_i)_{i ∈ SampleIdx}` i.i.d. from `D` and an independent internal
random seed `ω ∼ μ` (an arbitrary probability space, e.g. Gaussian vectors). Its query points
`query S ω` are fixed by the samples and the seed alone, before any answer is seen; its output is
`decide S ω a`, where `a j = f(query S ω j)` are the answers. The numbers of samples and of
queries are `|SampleIdx|` and `|QueryIdx|` (worst case = every run). A tester is chosen before
`D` and `f`, so it can depend on them only through samples and answers. -/
structure Tester (n : ℕ) (α : Type) where
  /-- Index set of the samples drawn from `D`. -/
  SampleIdx : Type
  [sampleFintype : Fintype SampleIdx]
  /-- Index set of the queries made to `f`. -/
  QueryIdx : Type
  [queryFintype : Fintype QueryIdx]
  /-- The internal randomness. -/
  Ω : Type
  [measΩ : MeasurableSpace Ω]
  /-- The law of the internal randomness. -/
  μ : Measure Ω
  [probμ : IsProbabilityMeasure μ]
  /-- The query points, as a function of the samples and the seed only (non-adaptive). -/
  query : (SampleIdx → Rn n) → Ω → QueryIdx → Rn n
  /-- The output, as a function of the samples, the seed and the answers. -/
  decide : (SampleIdx → Rn n) → Ω → (QueryIdx → ℝ) → α

attribute [instance] Tester.sampleFintype Tester.queryFintype Tester.measΩ Tester.probμ

namespace Tester

variable {n : ℕ} {α : Type}

/-- The number of samples the tester draws. -/
def numSamples (T : Tester n α) : ℕ := Fintype.card T.SampleIdx

/-- The number of queries the tester makes. -/
def numQueries (T : Tester n α) : ℕ := Fintype.card T.QueryIdx

/-- The output of one run on samples `S`, seed `ω`, and query access to `f`. -/
def run (T : Tester n α) (f : Rn n → ℝ) (S : T.SampleIdx → Rn n) (ω : T.Ω) : α :=
  T.decide S ω (fun j => f (T.query S ω j))

/-- The probability that the output satisfies `E`, when the samples are i.i.d. from `D` and the
seed is drawn from `μ` independently. -/
noncomputable def prob (T : Tester n α) (D : ProbabilityMeasure (Rn n)) (f : Rn n → ℝ)
    (E : α → Prop) : ℝ≥0∞ :=
  ((Measure.pi fun _ : T.SampleIdx => (D : Measure (Rn n))).prod T.μ)
    {p | E (T.run f p.1 p.2)}

/-- The query map and the decision rule are jointly measurable, so every output probability is
the probability of a measurable event. -/
def IsMeasurable [MeasurableSpace α] (T : Tester n α) : Prop :=
  Measurable (fun p : (T.SampleIdx → Rn n) × T.Ω => T.query p.1 p.2) ∧
    Measurable (fun p : ((T.SampleIdx → Rn n) × T.Ω) × (T.QueryIdx → ℝ) =>
      T.decide p.1.1 p.1.2 p.2)

end Tester

/-- **Definition 1.2** (p. 2): `T` is a `C`-robust halfspace tester for proximity parameter `ε`:
for every Borel distribution `D` on `ℝⁿ` (not necessarily in `C`) and every Borel
`f : ℝⁿ → {±1}`, with probability at least `3/4` the following hold simultaneously:
Completeness (`f` a halfspace ⇒ output ≠ Reject), Soundness (`f` `ε`-far from every halfspace
under `D` ⇒ output ≠ Accept), Assertiveness (`D ∈ C` ⇒ output ≠ Tantrum). -/
def IsRobustTester {n : ℕ} (T : Tester n Verdict) (C : Set (ProbabilityMeasure (Rn n)))
    (ε : ℝ) : Prop :=
  T.IsMeasurable ∧
    ∀ (D : ProbabilityMeasure (Rn n)) (f : Rn n → ℝ), IsBoolFn f →
      (3 / 4 : ℝ≥0∞) ≤ T.prob D f (fun o =>
        (IsHalfspace f → o ≠ Verdict.reject) ∧
        (FarFromHalfspaces D f ε → o ≠ Verdict.accept) ∧
        (D ∈ C → o ≠ Verdict.tantrum))

/-- **Definition 1.6** (p. 4): `T` (output `true` = Accept, `false` = Reject) is a
`(D∗, C)`-picky halfspace tester for proximity parameter `ε`: for every `D ∈ C` and every Borel
`f : ℝⁿ → {±1}`, with probability at least `3/4` both hold: Completeness (`f` a halfspace and
`D = D∗` ⇒ Accept) and Soundness (`f` `ε`-far from every halfspace under `D` ⇒ Reject). -/
def IsPickyTester {n : ℕ} (T : Tester n Bool) (Dstar : ProbabilityMeasure (Rn n))
    (C : Set (ProbabilityMeasure (Rn n))) (ε : ℝ) : Prop :=
  Dstar ∈ C ∧ T.IsMeasurable ∧
    ∀ D ∈ C, ∀ f : Rn n → ℝ, IsBoolFn f →
      (3 / 4 : ℝ≥0∞) ≤ T.prob D f (fun o =>
        (IsHalfspace f ∧ D = Dstar → o = true) ∧
        (FarFromHalfspaces D f ε → o = false))

/-- General query testers for Definitions 1.2/1.6 and Proposition A.1. Unlike `Tester`,
queries may depend on previous answers. The samples are drawn in advance; an algorithm
that requests samples during execution can consume this independent sample sequence as needed.
`numQueries` is a worst-case bound, padded by ignored queries after early termination.
The query at stage `i` receives only the first `i` answers, with every later entry zero.
Neither the query nor decision maps have access to the input law or the function oracle. -/
structure AdaptiveTester (n : ℕ) (α : Type) where
  SampleIdx : Type
  [sampleFintype : Fintype SampleIdx]
  numQueries : ℕ
  Ω : Type
  [measΩ : MeasurableSpace Ω]
  μ : Measure Ω
  [probμ : IsProbabilityMeasure μ]
  query : ℕ → (SampleIdx → Rn n) → Ω → (ℕ → ℝ) → Rn n
  decide : (SampleIdx → Rn n) → Ω → (ℕ → ℝ) → α

attribute [instance] AdaptiveTester.sampleFintype AdaptiveTester.measΩ AdaptiveTester.probμ

namespace AdaptiveTester

variable {n : ℕ} {α : Type}

/-- The maximum number of samples drawn from the input distribution. -/
def numSamples (T : AdaptiveTester n α) : ℕ := Fintype.card T.SampleIdx

/-- The answers after `k` adaptive queries; entries at indices `k` and above are zero.
At stage `k`, the next point depends only on samples, seed, and the preceding answers. -/
noncomputable def answers (T : AdaptiveTester n α) (f : Rn n → ℝ)
    (S : T.SampleIdx → Rn n) (ω : T.Ω) : ℕ → (ℕ → ℝ)
  | 0 => fun _ => 0
  | k + 1 =>
      let a := T.answers f S ω k
      Function.update a k (f (T.query k S ω a))

/-- Execute the finite query sequence and return the decision. -/
noncomputable def run (T : AdaptiveTester n α) (f : Rn n → ℝ)
    (S : T.SampleIdx → Rn n) (ω : T.Ω) : α :=
  T.decide S ω (T.answers f S ω T.numQueries)

/-- Output probability under independent input samples and internal randomness. -/
noncomputable def prob (T : AdaptiveTester n α) (D : ProbabilityMeasure (Rn n))
    (f : Rn n → ℝ) (E : α → Prop) : ℝ≥0∞ :=
  ((Measure.pi fun _ : T.SampleIdx => (D : Measure (Rn n))).prod T.μ)
    {p | E (T.run f p.1 p.2)}

/-- Joint measurability of each query rule and of the decision. Finite recursion then
makes the output measurable for every Borel oracle. -/
def IsMeasurable [MeasurableSpace α] (T : AdaptiveTester n α) : Prop :=
  (∀ i < T.numQueries,
    Measurable (fun p : ((T.SampleIdx → Rn n) × T.Ω) × (ℕ → ℝ) =>
      T.query i p.1.1 p.1.2 p.2)) ∧
  Measurable (fun p : ((T.SampleIdx → Rn n) × T.Ω) × (ℕ → ℝ) =>
    T.decide p.1.1 p.1.2 p.2)

/-- Definition 1.2 for general, possibly adaptive query testers. -/
def IsRobust (T : AdaptiveTester n Verdict) (C : Set (ProbabilityMeasure (Rn n)))
    (ε : ℝ) : Prop :=
  T.IsMeasurable ∧
    ∀ (D : ProbabilityMeasure (Rn n)) (f : Rn n → ℝ), IsBoolFn f →
      (3 / 4 : ℝ≥0∞) ≤ T.prob D f (fun o =>
        (IsHalfspace f → o ≠ Verdict.reject) ∧
        (FarFromHalfspaces D f ε → o ≠ Verdict.accept) ∧
        (D ∈ C → o ≠ Verdict.tantrum))

/-- Definition 1.6 for general query testers, including its standing `D∗ ∈ C` condition. -/
def IsPicky (T : AdaptiveTester n Bool) (Dstar : ProbabilityMeasure (Rn n))
    (C : Set (ProbabilityMeasure (Rn n))) (ε : ℝ) : Prop :=
  Dstar ∈ C ∧ T.IsMeasurable ∧
    ∀ D ∈ C, ∀ f : Rn n → ℝ, IsBoolFn f →
      (3 / 4 : ℝ≥0∞) ≤ T.prob D f (fun o =>
        (IsHalfspace f ∧ D = Dstar → o = true) ∧
        (FarFromHalfspaces D f ε → o = false))

end AdaptiveTester

end DistRobustHalfspace.Main


