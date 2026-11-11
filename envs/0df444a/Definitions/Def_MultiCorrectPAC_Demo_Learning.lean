-- Prove2me | Definitions.Def_MultiCorrectPAC_Demo_Learning
-- name    : MultiCorrectPAC_Demo_Learning
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:44:52.022185+00:00
-- url     : https://prove2.me/theorems/3e0a2ec4-9f0a-4f59-aa1c-973cba6f9b11
-- title:
--   Errors, randomized learners, full-set and one-correct-label feedback, realizable and agnostic PAC learnability, sample complexities
-- statement:
--   Let $\mathcal X,\mathcal Y$ be countable. For a distribution $P$ on $\mathcal X$ with $P(\operatorname{supp}(h^\star))=1$, a **predictor** $g:\mathcal X\to\mathcal Y$ and a **randomized prediction** $p(\cdot\mid x)$ have errors
--   $$L_{P,h^\star}(g)=\Pr_{x\sim P}[g(x)\notin h^\star(x)],\qquad L_{P,h^\star}(p)=\mathbb E_{x\sim P}\big[1-p(h^\star(x)\mid x)\big].$$
--   A learner using $m$ examples maps the observations and an independent seed $\omega\sim\mathrm{Unif}([0,1])$ to a predictor (or to a randomized prediction rule). Under **full-set feedback** it observes $(x_i,h^\star(x_i))$, $x_i$ i.i.d. from $P$. Under **one-correct-label feedback** it observes $(x_i,y_i)$ i.i.d. from a joint law $\mathcal D$ on $\mathcal X\times\mathcal Y$ with marginal $P$ that is **compatible** with $h^\star$: $\Pr_{(x,y)\sim\mathcal D}[y\in h^\star(x)]=1$; the demonstrator is otherwise arbitrary.
--
--   $\mathcal H$ is **realizably PAC learnable** (Definition 1) if for all $\varepsilon,\delta\in(0,1)$ some $m$ and some learner satisfy: for every $h^\star\in\mathcal H$ and every admissible $P$ (and $\mathcal D$), with probability at least $1-\delta$ over the $m$ examples and the seed, $L_{P,h^\star}(\hat g)\le\varepsilon$. The least such $m$ is the **sample complexity** $m^{\mathrm{full}}_{\mathcal H}(\varepsilon,\delta)$ or $m^{\mathrm{one}}_{\mathcal H}(\varepsilon,\delta)$, $=\infty$ if no $m$ works.
--
--   In the **agnostic** model (Definition 2) examples $(x,A)$ come from any distribution $\mathcal D$ on $\mathcal X\times\mathcal A$; under one-correct-label feedback the learner sees $(x,y)$ with $y$ drawn from a demonstrator supported on $A$. With $L_{\mathcal D}(g)=\Pr[g(x)\notin A]$ and the benchmark $L^{\mathrm{set}}_{\mathcal D}(\mathcal H)=\inf_{h\in\mathcal H}\Pr[h(x)\ne A]$ (5), $\mathcal H$ is agnostically learnable if finitely many examples give $\Pr[L_{\mathcal D}(\hat g)>L^{\mathrm{set}}_{\mathcal D}(\mathcal H)+\varepsilon]\le\delta$ for every $\mathcal D$ (and every demonstrator); $m^{\mathrm{full,ag}}_{\mathcal H}$ is the least number of full-set examples. A **most probable label** of a distribution on $\mathcal Y$ has maximal mass; a **plurality label** of votes $v_1,\dots,v_T$ receives the most votes.
--
--   **Formalization Note** Distributions are `PMF`s; the seed space is `unitInterval` with `volume`. `Learner Z X Y m` / `RandLearner Z X Y m` are maps `(Fin m → Z) → unitInterval → X → Y` (resp. `→ PMF Y`) measurable in the seed. The probability over $m$ i.i.d. observations and the seed is written out as `∑' σ, (∏ i, D (σ i)) * volume {ω | …}`; a failure probability `≤ ENNReal.ofReal δ` is the PAC condition. Errors are in `ℝ≥0∞`. `mOne`, `mFull`, `mFullAg` are `ℕ∞`-valued infima over the working `m` (`⊤` if none). The randomized error counts only inputs of `supp(h)`, a $P$-null complement. The expected error `oneExpLoss` is a lower Lebesgue integral over the seed.
-- source:
--   Hanneke, Mansouri, Pour, Shaeiri, Wang, PAC Learning with Multiple Correct Answers, STOC 2027 submission (manuscript sha256 2844bd34…), pp. 26–27 (PDF 28–29), §5.2, (3), Definitions 1–2, (5); p. 32 (PDF 34), §5.5

import Mathlib
import Definitions.Def_MultiCorrectPAC_Demo_Hypotheses

open MeasureTheory
open scoped ENNReal

namespace MultiCorrectPAC.Demo

/-! Hanneke, Mansouri, Pour, Shaeiri, Wang, *PAC Learning with Multiple Correct Answers*,
§5.2 (printed pp. 26–27, PDF 28–29): errors (3), the full-set and one-correct-label feedback
models, randomized learners, Definition 1 (realizable PAC learnability, sample complexity),
Definition 2 with the benchmark (5) (agnostic PAC learnability), §5.5 (p. 32, PDF 34): most
probable and plurality labels.

Conventions. Distributions on the countable spaces `X`, `X × Y`, `X × Finset Y` are `PMF`s.
A learner that uses `m` examples is a map from the sample `σ : Fin m → Z` (the observation
space `Z` depends on the feedback model) and a seed `ω ∈ [0, 1]` (`unitInterval`, uniform law
`volume`) to a predictor `X → Y`; it is required to be measurable in the seed. The probability,
over `m` i.i.d. observations and the independent seed, of an event is written out as
`∑' σ, (∏ᵢ D(σᵢ)) · volume {ω | event}` (the product law on the countable sample space), so the
failure probability is a plain number in `ℝ≥0∞`. Errors are values in `ℝ≥0∞`. -/

/-- The prediction `y` is invalid for `h` at `x`: `x ∈ supp(h)` and `y ∉ h(x)`. -/
def IsInvalid {X Y : Type*} (h : Hyp X Y) (x : X) (y : Y) : Prop :=
  ∃ A, h x = some A ∧ y ∉ A

/-- `P(supp(h)) = 1`: every input of positive probability lies in `supp(h)`. -/
def SupportedIn {X Y : Type*} (P : PMF X) (h : Hyp X Y) : Prop :=
  ∀ x, P x ≠ 0 → x ∈ supp h

/-- The error `L_{P,h}(g) = Pr_{x∼P}[g(x) ∉ h(x)]` of a predictor (3). -/
noncomputable def predLoss {X Y : Type*} (P : PMF X) (h : Hyp X Y) (g : X → Y) : ℝ≥0∞ :=
  P.toOuterMeasure {x | IsInvalid h x (g x)}

/-- The error `L_{P,h}(p) = E_{x∼P}[1 − p(h(x) | x)]` of a randomized prediction `p` (3); inputs
outside `supp(h)` (a `P`-null set whenever `P(supp(h)) = 1`) contribute `0`. -/
noncomputable def randLoss {X Y : Type*} (P : PMF X) (h : Hyp X Y) (p : X → PMF Y) : ℝ≥0∞ :=
  ∑' x, P x * (match h x with
    | none => 0
    | some A => 1 - (p x).toOuterMeasure (A : Set Y))

/-- A (randomized) learner that uses `m` observations from `Z` and outputs a predictor
`X → Y`; the seed is `ω ∈ [0, 1]`, and the output is measurable in the seed. -/
structure Learner (Z X Y : Type*) (m : ℕ) where
  run : (Fin m → Z) → unitInterval → X → Y
  measurable_run : ∀ (σ : Fin m → Z) (x : X) (y : Y), MeasurableSet {ω | run σ ω x = y}

/-- A learner that uses `m` observations from `Z` and outputs a randomized prediction rule
`x ↦ p(· | x)`, measurable in the seed. -/
structure RandLearner (Z X Y : Type*) (m : ℕ) where
  run : (Fin m → Z) → unitInterval → X → PMF Y
  measurable_run : ∀ (σ : Fin m → Z) (x : X) (y : Y), Measurable fun ω => run σ ω x y

/-- The joint law `D` on `X × Y` is compatible with `h` (§5.2 (iii)):
`Pr_{(x,y)∼D}[y ∈ h(x)] = 1`. Its marginal is `D.map Prod.fst`. -/
def Compatible {X Y : Type*} (h : Hyp X Y) (D : PMF (X × Y)) : Prop :=
  ∀ p, D p ≠ 0 → IsCorrect h p.1 p.2

/-- One-correct-label feedback: probability, over `m` i.i.d. demonstrations from `D` and the
seed, that the output has error `> ε` against `h` under the marginal `P = D.map Prod.fst`. -/
noncomputable def oneFailProb {X Y : Type*} {m : ℕ} (D : PMF (X × Y)) (h : Hyp X Y) (ε : ℝ)
    (A : Learner (X × Y) X Y m) : ℝ≥0∞ :=
  ∑' σ : Fin m → X × Y, (∏ i, D (σ i)) *
    volume {ω | ENNReal.ofReal ε < predLoss (D.map Prod.fst) h (A.run σ ω)}

/-- Full-set feedback: probability, over `x₁, …, x_m` i.i.d. from `P` (the learner observes
`(xᵢ, h(xᵢ))`) and the seed, that the output has error `> ε` against `h`. -/
noncomputable def fullFailProb {X Y : Type*} {m : ℕ} (P : PMF X) (h : Hyp X Y) (ε : ℝ)
    (A : Learner (X × Option (Finset Y)) X Y m) : ℝ≥0∞ :=
  ∑' xs : Fin m → X, (∏ i, P (xs i)) *
    volume {ω | ENNReal.ofReal ε < predLoss P h (A.run (fun i => (xs i, h (xs i))) ω)}

/-- Some learner using `m` one-correct-label examples is `(ε, δ)`-good for every target `h ∈ H`
and every law `D` compatible with `h` (Definition 1). -/
def OneWorks {X Y : Type*} (H : Set (Hyp X Y)) (ε δ : ℝ) (m : ℕ) : Prop :=
  ∃ A : Learner (X × Y) X Y m, ∀ h ∈ H, ∀ D : PMF (X × Y), Compatible h D →
    oneFailProb D h ε A ≤ ENNReal.ofReal δ

/-- Some learner using `m` full-set examples is `(ε, δ)`-good for every target `h ∈ H` and
every `P` with `P(supp(h)) = 1` (Definition 1). -/
def FullWorks {X Y : Type*} (H : Set (Hyp X Y)) (ε δ : ℝ) (m : ℕ) : Prop :=
  ∃ A : Learner (X × Option (Finset Y)) X Y m, ∀ h ∈ H, ∀ P : PMF X, SupportedIn P h →
    fullFailProb P h ε A ≤ ENNReal.ofReal δ

/-- The one-correct-label sample complexity `m^one_H(ε, δ)`: the least `m` that works, `⊤` if
none does. -/
noncomputable def mOne {X Y : Type*} (H : Set (Hyp X Y)) (ε δ : ℝ) : ℕ∞ :=
  ⨅ (m : ℕ) (_ : OneWorks H ε δ m), (m : ℕ∞)

/-- The full-set sample complexity `m^full_H(ε, δ)`: the least `m` that works, `⊤` if none does. -/
noncomputable def mFull {X Y : Type*} (H : Set (Hyp X Y)) (ε δ : ℝ) : ℕ∞ :=
  ⨅ (m : ℕ) (_ : FullWorks H ε δ m), (m : ℕ∞)

/-- Realizable one-correct-label PAC learnability (Definition 1). -/
def OneLearnable {X Y : Type*} (H : Set (Hyp X Y)) : Prop :=
  ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 → ∃ m : ℕ, OneWorks H ε δ m

/-- Realizable full-set PAC learnability (Definition 1). -/
def FullLearnable {X Y : Type*} (H : Set (Hyp X Y)) : Prop :=
  ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 → ∃ m : ℕ, FullWorks H ε δ m

/-- Expected error `E[L_{P,h}(p̂)]` of a randomized-prediction learner under one-correct-label
feedback, over `m` i.i.d. demonstrations from `D` and the seed, with `P = D.map Prod.fst`. -/
noncomputable def oneExpLoss {X Y : Type*} {m : ℕ} (D : PMF (X × Y)) (h : Hyp X Y)
    (A : RandLearner (X × Y) X Y m) : ℝ≥0∞ :=
  ∑' σ : Fin m → X × Y, (∏ i, D (σ i)) *
    ∫⁻ ω, randLoss (D.map Prod.fst) h (A.run σ ω)

/-! ### Agnostic learning (Definition 2, benchmark (5)) -/

/-- An agnostic data law: a distribution on `X × 𝒜` (every set of positive probability is a
nonempty set of at most `ℓ` labels). -/
def AgnLaw {X Y : Type*} (ℓ : ℕ) (D : PMF (X × Finset Y)) : Prop :=
  ∀ p, D p ≠ 0 → InA ℓ p.2

/-- `L_D(g) = Pr_{(x,A)∼D}[g(x) ∉ A]` (5). -/
noncomputable def agnLoss {X Y : Type*} (D : PMF (X × Finset Y)) (g : X → Y) : ℝ≥0∞ :=
  D.toOuterMeasure {p | g p.1 ∉ p.2}

/-- The benchmark `L^set_D(H) = inf_{h∈H} Pr_{(x,A)∼D}[h(x) ≠ A]` (5); `h(x) = ⋆` is a mismatch. -/
noncomputable def setBench {X Y : Type*} (D : PMF (X × Finset Y)) (H : Set (Hyp X Y)) : ℝ≥0∞ :=
  ⨅ h ∈ H, D.toOuterMeasure {p | h p.1 ≠ some p.2}

/-- Agnostic full-set feedback: probability over `m` i.i.d. pairs `(xᵢ, Aᵢ)` and the seed that
`L_D(ĝ) > L^set_D(H) + ε`. -/
noncomputable def agnFullFailProb {X Y : Type*} {m : ℕ} (D : PMF (X × Finset Y))
    (H : Set (Hyp X Y)) (ε : ℝ) (A : Learner (X × Finset Y) X Y m) : ℝ≥0∞ :=
  ∑' σ : Fin m → X × Finset Y, (∏ i, D (σ i)) *
    volume {ω | setBench D H + ENNReal.ofReal ε < agnLoss D (A.run σ ω)}

/-- Some learner using `m` agnostic full-set examples is `(ε, δ)`-good for every agnostic law. -/
def AgnFullWorks {X Y : Type*} (ℓ : ℕ) (H : Set (Hyp X Y)) (ε δ : ℝ) (m : ℕ) : Prop :=
  ∃ A : Learner (X × Finset Y) X Y m, ∀ D : PMF (X × Finset Y), AgnLaw ℓ D →
    agnFullFailProb D H ε A ≤ ENNReal.ofReal δ

/-- `m^{full,ag}_H(ε, δ)`: the least `m` that works, `⊤` if none does. -/
noncomputable def mFullAg {X Y : Type*} (ℓ : ℕ) (H : Set (Hyp X Y)) (ε δ : ℝ) : ℕ∞ :=
  ⨅ (m : ℕ) (_ : AgnFullWorks ℓ H ε δ m), (m : ℕ∞)

/-- Agnostic full-set PAC learnability (Definition 2). -/
def AgnFullLearnable {X Y : Type*} (ℓ : ℕ) (H : Set (Hyp X Y)) : Prop :=
  ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 → ∃ m : ℕ, AgnFullWorks ℓ H ε δ m

/-- A demonstrator for the agnostic law `D`: a conditional law of the demonstrated label given
`(x, A)`, supported on `A` (for every `(x, A)` of positive probability). -/
def IsDemonstrator {X Y : Type*} (D : PMF (X × Finset Y)) (κ : X × Finset Y → PMF Y) : Prop :=
  ∀ p, D p ≠ 0 → ∀ y, κ p y ≠ 0 → y ∈ p.2

/-- The law of the observed pair `(x, y)`: draw `(x, A) ∼ D`, then `y ∼ κ(x, A)`. -/
noncomputable def demoLaw {X Y : Type*} (D : PMF (X × Finset Y)) (κ : X × Finset Y → PMF Y) :
    PMF (X × Y) :=
  D.bind fun p => (κ p).map fun y => (p.1, y)

/-- Agnostic one-correct-label feedback: probability over `m` i.i.d. observed pairs `(xᵢ, yᵢ)`
and the seed that `L_D(ĝ) > L^set_D(H) + ε`. -/
noncomputable def agnOneFailProb {X Y : Type*} {m : ℕ} (D : PMF (X × Finset Y))
    (κ : X × Finset Y → PMF Y) (H : Set (Hyp X Y)) (ε : ℝ) (A : Learner (X × Y) X Y m) :
    ℝ≥0∞ :=
  ∑' σ : Fin m → X × Y, (∏ i, demoLaw D κ (σ i)) *
    volume {ω | setBench D H + ENNReal.ofReal ε < agnLoss D (A.run σ ω)}

/-- Some learner using `m` demonstrations is `(ε, δ)`-good for every agnostic law and every
demonstrator. -/
def AgnOneWorks {X Y : Type*} (ℓ : ℕ) (H : Set (Hyp X Y)) (ε δ : ℝ) (m : ℕ) : Prop :=
  ∃ A : Learner (X × Y) X Y m, ∀ (D : PMF (X × Finset Y)) (κ : X × Finset Y → PMF Y),
    AgnLaw ℓ D → IsDemonstrator D κ → agnOneFailProb D κ H ε A ≤ ENNReal.ofReal δ

/-- Agnostic PAC learnability from one correct label (Definition 2). -/
def AgnOneLearnable {X Y : Type*} (ℓ : ℕ) (H : Set (Hyp X Y)) : Prop :=
  ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 → ∃ m : ℕ, AgnOneWorks ℓ H ε δ m

/-! ### Most probable and plurality labels (§5.5) -/

/-- `y` is a most probable label of the distribution `p` on `Y`. -/
def IsMostProbable {Y : Type*} (p : PMF Y) (y : Y) : Prop :=
  ∀ y', p y' ≤ p y

/-- `y` is a plurality label of the votes `v₁, …, v_T`: no label receives more votes. -/
def IsPlurality {Y : Type*} {T : ℕ} (votes : Fin T → Y) (y : Y) : Prop :=
  ∀ y', {j | votes j = y'}.ncard ≤ {j | votes j = y}.ncard

end MultiCorrectPAC.Demo


