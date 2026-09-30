-- Prove2me | Definitions.Def_UnderstandingML_Framework
-- name    : UnderstandingML_Framework
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T03:24:33.43254+00:00
-- url     : https://prove2.me/theorems/0fccafb3-79e4-4d73-909b-aa590a7d7e42
-- title:
--   Chapters 2-4: risk, empirical risk, i.i.d. samples, ERM, learners; PAC learnability (Def. 3.1), agnostic PAC learnability (Def. 3.4), ε-representative samples and uniform convergence
-- statement:
--   The statistical learning framework of Chapters 2–4.
--
--   **Risk and ERM (§2.1–2.2, §3.2.2).** For a domain $Z$, a hypothesis type with a class $H$ and a loss $\ell : H \times Z \to \mathbb{R}$: `risk loss D h` is $L_D(h) = \mathbb{E}_{z \sim D}[\ell(h, z)]$ (3.3), `empRisk loss S h` is $L_S(h) = \frac1m \sum_i \ell(h, z_i)$ (3.4), `iidLaw D m` is $D^m$, the law of $m$ i.i.d. examples, `IsERM loss H S h` says $h \in \operatorname{argmin}_{h' \in H} L_S(h')$ (2.4), a `Learner Z Hyp` is a map from samples of each size to hypotheses, and `IsERMLearner` says every output is an ERM hypothesis.
--
--   **Binary classification (§2.1, §3.1).** `loss01` is the 0–1 loss; `labeledLaw D f` is the law of $(x, f(x))$ with $x \sim D$; `trueError D f h` is $L_{(D,f)}(h) = D(\{x : h(x) \ne f(x)\})$ (2.1); `Realizable H D f` is Definition 2.1 (some $h^\star \in H$ has $L_{(D,f)}(h^\star) = 0$). `IsPACWith H A mH` is **Definition 3.1** for the algorithm $A$ and sample-complexity function $m_H$: for every $\epsilon, \delta \in (0,1)$, every distribution $D$ over $X$ and every measurable labeling function $f$ satisfying realizability, for all $m \ge m_H(\epsilon, \delta)$ the probability under $D^m$ (of labeled examples) that $L_{(D,f)}(A(S)) > \epsilon$ is at most $\delta$; `PACLearnable H` is the existence of such $m_H$ and $A$.
--
--   **General loss (§3.2.2).** `IsAgnosticPACWith loss H A mH` is **Definition 3.4**: $A$ returns hypotheses in $H$ and for every $\epsilon, \delta \in (0,1)$, every distribution $D$ over $Z$ and $m \ge m_H(\epsilon, \delta)$, the probability that $L_D(A(S)) > \min_{h' \in H} L_D(h') + \epsilon$ (written: some $h' \in H$ has $L_D(h') + \epsilon < L_D(A(S))$) is at most $\delta$; `AgnosticPACLearnable`.
--
--   **Uniform convergence (§4.1).** `IsRepresentative loss H D ε S` is Definition 4.1 ($|L_S(h) - L_D(h)| \le \epsilon$ for all $h \in H$); `HasUniformConvergenceWith loss H mUC` is Definition 4.3 (for all $\epsilon, \delta$, $D$ and $m \ge m^{UC}_H(\epsilon,\delta)$, a sample is $\epsilon$-representative with probability at least $1-\delta$); `HasUniformConvergence`.
--
--   **Conventions.** Probabilities of failure are outer measures under the product law; hypotheses and labeling functions are measurable in the theorems (Remark 3.1); a learning algorithm is a deterministic function of the sample.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §2.1 the statistical learning framework and (2.1) (pp. 33-35), §2.2 ERM (2.4) (p. 37), Definition 2.1 (p. 38), Definition 3.1 (p. 43), §3.2.2 and Definition 3.4 (pp. 47-49), Definitions 4.1 and 4.3 (pp. 54-55)

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, Chapters 2–4:
# the statistical learning framework, PAC learning and uniform convergence

Shalev-Shwartz and Ben-David, *Understanding Machine Learning: From Theory to Algorithms*,
Cambridge University Press 2014, doi:10.1017/CBO9781107298019.

**The statistical learning framework (§2.1, §3.2.2).** A domain `Z` of examples, a set `H` of
hypotheses and a loss function `ℓ : H × Z → ℝ₊`. The **risk** of `h` under a distribution `D`
over `Z` is `L_D(h) = E_{z ~ D} ℓ(h, z)` (3.3); the **empirical risk** on a sample
`S = (z₁, …, z_m)` is `L_S(h) = (1/m) ∑ ℓ(h, zᵢ)` (3.4). A training sample is drawn i.i.d.,
`S ~ D^m`. The **ERM** rule returns a hypothesis in `H` minimizing `L_S` (2.4). For binary
classification, `Z = X × {0,1}`, hypotheses are `h : X → {0,1}`, and the 0–1 loss gives the
**true error** `L_{(D,f)}(h) = D({x : h(x) ≠ f(x)})` (2.1) when labels are produced by `f`, or
`L_D(h) = D({(x, y) : h(x) ≠ y})` (3.1) for a joint distribution.

**Learnability.** `H` is **PAC learnable** (Definition 3.1) if there are a sample-complexity
function `m_H : (0,1)² → ℕ` and a learning algorithm such that for every `ε, δ ∈ (0,1)`, every
distribution `D` over `X` and every labeling function `f` for which the realizability
assumption holds (Definition 2.1: some `h⋆ ∈ H` has `L_{(D,f)}(h⋆) = 0`), running the algorithm
on `m ≥ m_H(ε, δ)` i.i.d. examples labeled by `f` returns `h` with `L_{(D,f)}(h) ≤ ε` with
probability at least `1 − δ`. `H` is **agnostic PAC learnable** with respect to `Z` and `ℓ`
(Definition 3.4) if for every distribution `D` over `Z` the algorithm returns `h ∈ H` with
`L_D(h) ≤ min_{h' ∈ H} L_D(h') + ε` with probability at least `1 − δ`. A sample is
**ε-representative** (Definition 4.1) if `|L_S(h) − L_D(h)| ≤ ε` for all `h ∈ H`; `H` has the
**uniform convergence property** (Definition 4.3) if some `m^{UC}_H` makes a sample of
`m ≥ m^{UC}_H(ε, δ)` examples ε-representative with probability at least `1 − δ`.

**Conventions.** A learning algorithm is a function from samples of each size to hypotheses;
"with probability at least `1 − δ`" is stated as an upper bound `δ` on the outer measure of the
failure set under `D^m`; `min_{h' ∈ H} L_D(h') + ε < L_D(h)` is written as `∃ h' ∈ H`,
`L_D(h') + ε < L_D(h)`, which needs no infimum. Measurability of hypotheses and labeling
functions is assumed where the book's Remark 3.1 requires it.
-/

open MeasureTheory

namespace UnderstandingML

/-! ### The general framework: risk, empirical risk, samples and ERM -/

section Framework

variable {Z : Type*} [MeasurableSpace Z] {Hyp : Type*}

/-- The **risk** `L_D(h) = E_{z ~ D}[ℓ(h, z)]` (3.3). -/
noncomputable def risk (loss : Hyp → Z → ℝ) (D : Measure Z) (h : Hyp) : ℝ :=
  ∫ z, loss h z ∂D

/-- The **empirical risk** `L_S(h) = (1/m) ∑ᵢ ℓ(h, zᵢ)` on the sample `S` (3.4). -/
noncomputable def empRisk (loss : Hyp → Z → ℝ) {m : ℕ} (S : Fin m → Z) (h : Hyp) : ℝ :=
  (∑ i, loss h (S i)) / m

/-- `D^m`, the law of a sample of `m` i.i.d. examples (§2.3.1). -/
noncomputable def iidLaw (D : Measure Z) (m : ℕ) : Measure (Fin m → Z) :=
  Measure.pi (fun _ ↦ D)

/-- `h` is an **ERM hypothesis** for `S`: `h ∈ argmin_{h' ∈ H} L_S(h')` (2.4). -/
def IsERM (loss : Hyp → Z → ℝ) (H : Set Hyp) {m : ℕ} (S : Fin m → Z) (h : Hyp) : Prop :=
  h ∈ H ∧ ∀ h' ∈ H, empRisk loss S h ≤ empRisk loss S h'

/-- A **learning algorithm**: for each sample size, a map from samples to hypotheses. -/
abbrev Learner (Z Hyp : Type*) := (m : ℕ) → (Fin m → Z) → Hyp

/-- `A` implements the `ERM_H` rule: every output is an ERM hypothesis for its sample. -/
def IsERMLearner (loss : Hyp → Z → ℝ) (H : Set Hyp) (A : Learner Z Hyp) : Prop :=
  ∀ (m : ℕ) (S : Fin m → Z), IsERM loss H S (A m S)

/-- **Agnostic PAC learnability with respect to `Z` and `ℓ`, with sample complexity `mH` and
algorithm `A`** (Definition 3.4): `A` returns hypotheses in `H`, and for every `ε, δ ∈ (0,1)`,
every distribution `D` over `Z` and every `m ≥ mH(ε, δ)`, the probability that
`L_D(A(S)) > min_{h' ∈ H} L_D(h') + ε` is at most `δ`. -/
def IsAgnosticPACWith (loss : Hyp → Z → ℝ) (H : Set Hyp) (A : Learner Z Hyp) (mH : ℝ → ℝ → ℕ) :
    Prop :=
  (∀ (m : ℕ) (S : Fin m → Z), A m S ∈ H) ∧
  ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 → ∀ D : Measure Z, IsProbabilityMeasure D →
    ∀ m : ℕ, mH ε δ ≤ m →
      iidLaw D m {S | ∃ h' ∈ H, risk loss D h' + ε < risk loss D (A m S)} ≤ ENNReal.ofReal δ

/-- `H` is **agnostic PAC learnable** with respect to `Z` and `ℓ` (Definition 3.4). -/
def AgnosticPACLearnable (loss : Hyp → Z → ℝ) (H : Set Hyp) : Prop :=
  ∃ (mH : ℝ → ℝ → ℕ) (A : Learner Z Hyp), IsAgnosticPACWith loss H A mH

/-- `S` is **ε-representative** with respect to `H`, `ℓ` and `D` (Definition 4.1):
`|L_S(h) − L_D(h)| ≤ ε` for every `h ∈ H`. -/
def IsRepresentative (loss : Hyp → Z → ℝ) (H : Set Hyp) (D : Measure Z) (ε : ℝ) {m : ℕ}
    (S : Fin m → Z) : Prop :=
  ∀ h ∈ H, |empRisk loss S h - risk loss D h| ≤ ε

/-- `H` has the **uniform convergence property** with the function `mUC` (Definition 4.3): for
every `ε, δ ∈ (0,1)` and every distribution `D`, a sample of `m ≥ mUC(ε, δ)` i.i.d. examples is
ε-representative with probability at least `1 − δ`. -/
def HasUniformConvergenceWith (loss : Hyp → Z → ℝ) (H : Set Hyp) (mUC : ℝ → ℝ → ℕ) : Prop :=
  ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 → ∀ D : Measure Z, IsProbabilityMeasure D →
    ∀ m : ℕ, mUC ε δ ≤ m →
      iidLaw D m {S | ¬ IsRepresentative loss H D ε S} ≤ ENNReal.ofReal δ

/-- `H` has the uniform convergence property (Definition 4.3). -/
def HasUniformConvergence (loss : Hyp → Z → ℝ) (H : Set Hyp) : Prop :=
  ∃ mUC : ℝ → ℝ → ℕ, HasUniformConvergenceWith loss H mUC

end Framework

/-! ### Binary classification with the 0–1 loss -/

section Classification

variable {X : Type*} [MeasurableSpace X]

/-- The **0–1 loss** `ℓ_{0−1}(h, (x, y)) = 𝟙[h(x) ≠ y]` (§3.2.2). -/
def loss01 (h : X → Bool) (z : X × Bool) : ℝ :=
  if h z.1 = z.2 then 0 else 1

/-- The law of a labeled example `(x, f(x))` with `x ~ D` (the data of §2.1: a distribution over
`X` and a labeling function). -/
noncomputable def labeledLaw (D : Measure X) (f : X → Bool) : Measure (X × Bool) :=
  D.map (fun x ↦ (x, f x))

/-- The **true error** `L_{(D,f)}(h) = D({x : h(x) ≠ f(x)})` (2.1). -/
noncomputable def trueError (D : Measure X) (f h : X → Bool) : ℝ :=
  (D {x | h x ≠ f x}).toReal

/-- The **realizability assumption** (Definition 2.1): some `h⋆ ∈ H` has `L_{(D,f)}(h⋆) = 0`. -/
def Realizable (H : Set (X → Bool)) (D : Measure X) (f : X → Bool) : Prop :=
  ∃ h ∈ H, trueError D f h = 0

/-- **PAC learnability with sample complexity `mH` and algorithm `A`** (Definition 3.1): for every
`ε, δ ∈ (0,1)`, every distribution `D` over `X` and every (measurable) labeling function `f` for
which the realizability assumption holds, running `A` on `m ≥ mH(ε, δ)` i.i.d. examples labeled
by `f` returns `h` with `L_{(D,f)}(h) > ε` with probability at most `δ`. -/
def IsPACWith (H : Set (X → Bool)) (A : Learner (X × Bool) (X → Bool)) (mH : ℝ → ℝ → ℕ) :
    Prop :=
  ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 → ∀ D : Measure X, IsProbabilityMeasure D →
    ∀ f : X → Bool, Measurable f → Realizable H D f → ∀ m : ℕ, mH ε δ ≤ m →
      iidLaw (labeledLaw D f) m {S | ε < trueError D f (A m S)} ≤ ENNReal.ofReal δ

/-- `H` is **PAC learnable** (Definition 3.1). -/
def PACLearnable (H : Set (X → Bool)) : Prop :=
  ∃ (mH : ℝ → ℝ → ℕ) (A : Learner (X × Bool) (X → Bool)), IsPACWith H A mH

end Classification

end UnderstandingML


