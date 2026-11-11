-- Prove2me | Definitions.Def_PrivInfoHier_Main_Filter
-- name    : PrivInfoHier_Main_Filter
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:13:59.660728+00:00
-- url     : https://prove2.me/theorems/5ac600b9-da80-45f1-93db-adc975e812d8
-- title:
--   Privacy filters, (ε, δ)-validity, spec- and mechanism-level classes, quantile function and δ-clipped mean (Defs. 2.1, 2.2, 2.4, 3.1)
-- statement:
--   Fix a data-release process. A **privacy filter** (Definition 2.1) determines a stopping time $T\in\mathbb N$, the number of outputs it allows: $\{T\ge t\}$ is the event that the $t$-th output is released. It may use an auxiliary random variable $Z$, internal to it and independent of the interaction. All quantities live on the canonical space $\Omega=\mathcal Z\times(\mathcal R\times\mathcal Y)^{\mathbb N}$ with law $P_x=\mathrm{law}(Z)\otimes P_{x,\mathcal A}$.
--
--   **Validity** (Definition 2.2). The **stopped transcript** $(R^T,Y^T)$ is the variable-length transcript of the first $T$ rounds (its length is part of it). The filter is $(\varepsilon,\delta)$-valid if for every request strategy, every ordered neighbouring pair $x\sim x'$ and every measurable set $S$ of stopped transcripts
--   $$P_x\big((R^T,Y^T)\in S\big)\le e^{\varepsilon}P_{x'}\big((R^T,Y^T)\in S\big)+\delta.$$
--
--   **Classes** (Definition 2.4). Spec-level information is trivial, mechanism-level information at step $t$ is $\sigma(M^t)=\sigma(M_1,\dots,M_t)$. A filter is **spec-level** if $\{T\ge t\}\in\sigma(Z)$ for every $t$, and **mechanism-level** if $\{T\ge t\}\in\sigma(Z,M^t)$ for every $t$ but it is not spec-level. These σ-algebras are fixed by the process and do not depend on the database or the strategy.
--
--   **δ-clipped mean** (Definition 3.1). The quantile function of $T$ under $P$ is $Q_T(u)=\inf\{t\in\mathbb N: P(T\le t)\ge u\}$, and
--   $$U_\delta(T)=\inf_{x,\mathcal A}\frac1{1-\delta}\int_0^{1-\delta}Q^{x,\mathcal A}_T(u)\,du.$$
--
--   **Hockey-stick quantities** (App. B.1). $\delta^+_t=\sup_S\big(P_x((R^t,Y^t)\in S)-e^\varepsilon P_{x'}((R^t,Y^t)\in S)\big)$ is the smallest $\delta$ for which the transcript after $t$ releases satisfies the $(\varepsilon,\delta)$-DP inequality from $x$ to $x'$, and $\delta^+_{(T)}$ is the same quantity for the stopped transcript of a filter.
--
--   **Formalization Note.** A filter is a map `T : 𝒵 × Path ℛ 𝒴 → ℕ` together with a probability measure `μZ` on a measurable type `𝒵` (the law of $Z$); `filterLaw P A x μZ = μZ.prod (interLaw P A x)`. The stopped transcript lives in `Σ n, Hist ℛ 𝒴 n` with Mathlib's σ-algebra on a sigma type. The horizon of §2.3 is not part of these definitions; statements that need it say `∀ ω, T ω ≤ N`. `specSigma` is `comap Prod.fst` of the σ-algebra of `𝒵`; `mechSigma t` adds `comap (realisedMech P k ·.2) ⊤` for `k < t` ($M_1,\dots,M_t$), with the discrete σ-algebra on mechanisms. Membership is in the σ-algebra sense, not up to null sets. `quantile μ T u = ⨅ t, ⨅ (_ : ofReal u ≤ μ{T ≤ t}), t` in $[0,\infty]$ (value $\infty$ if the set is empty; $0$ for $u\le0$). `clippedMean law T δ = ⨅ i, ofReal(1/(1−δ)) · ∫⁻ u ∈ (0, 1−δ], quantile (law i) T u`; `filterClippedMean` takes the infimum over all pairs (database, strategy). `deltaPlus`/`deltaPlusStopped` take the supremum over measurable sets of the truncated difference `μ S − ofReal(e^ε)·ν S` in $[0,\infty]$; since $S=\varnothing$ gives $0$ this equals the real supremum.
-- source:
--   Taylor, Vippathalla, Coon, An Information Hierarchy of Privacy Filters and Odometers, arXiv:2611.03130 (held version, sha256 77181933…), p. 6 (PDF 8), Definitions 2.1–2.2; p. 7 (PDF 9), Definition 2.4; p. 9 (PDF 11), Definition 3.1; p. 18 (PDF 20), δ⁺_t and δ⁺_(T_S)

import Mathlib
import Definitions.Def_PrivInfoHier_Main_Model

namespace PrivInfoHier.Main

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {𝒳 ℛ 𝒴 : Type} [MeasurableSpace ℛ] [MeasurableSpace 𝒴]
variable {𝒵 : Type} [m𝒵 : MeasurableSpace 𝒵]

/-- The law on the canonical space `Ω = 𝒵 × Path` of a filter with internal randomness
`Z ∼ μZ`, independent of the interaction: `law(Z) ⊗ P_{x,𝒜}` (§2.2–§2.3). -/
noncomputable def filterLaw (P : Process 𝒳 ℛ 𝒴) (A : RequestStrategy ℛ 𝒴) (x : 𝒳)
    (μZ : Measure 𝒵) : Measure (𝒵 × Path ℛ 𝒴) :=
  μZ.prod (interLaw P A x)

/-- The stopped transcript `(R^T, Y^T)` (Definition 2.2, p. 6): the variable-length transcript of
the first `T` rounds, in `Σ n, Hist ℛ 𝒴 n` with Mathlib's σ-algebra on a sigma type (so its
length `T` is part of it). -/
def stoppedTranscript (T : 𝒵 × Path ℛ 𝒴 → ℕ) (ω : 𝒵 × Path ℛ 𝒴) : Σ n, Hist ℛ 𝒴 n :=
  ⟨T ω, fun j => ω.2 j⟩

/-- `(ε, δ)`-validity of a privacy filter (Definitions 2.1–2.2, p. 6). The filter is a stopping
time `T : 𝒵 × Path → ℕ` (the number of released outputs, `{T ≥ t}` the event that the `t`-th output
is released) with internal randomness `Z ∼ μZ`. It is valid if for every request strategy, every
ordered neighbouring pair `x ∼ x′` and every measurable set `S` of stopped transcripts,
`P_x((R^T, Y^T) ∈ S) ≤ e^ε P_{x′}((R^T, Y^T) ∈ S) + δ`. -/
def IsValid (P : Process 𝒳 ℛ 𝒴) (nb : 𝒳 → 𝒳 → Prop) (ε δ : ℝ) (μZ : Measure 𝒵)
    (T : 𝒵 × Path ℛ 𝒴 → ℕ) : Prop :=
  ∀ (A : RequestStrategy ℛ 𝒴) (x x' : 𝒳), nb x x' →
    ∀ S : Set (Σ n, Hist ℛ 𝒴 n), MeasurableSet S →
      filterLaw P A x μZ (stoppedTranscript T ⁻¹' S)
        ≤ ENNReal.ofReal (Real.exp ε) * filterLaw P A x' μZ (stoppedTranscript T ⁻¹' S)
          + ENNReal.ofReal δ

/-- Spec-level information together with the internal randomness: `σ(I_S, Z) = σ(Z)` on
`Ω = 𝒵 × Path` (§2.2, Definition 2.4(i)). -/
@[instance_reducible] def specSigma (𝒵 : Type) [m𝒵 : MeasurableSpace 𝒵] (ℛ 𝒴 : Type) :
    MeasurableSpace (𝒵 × Path ℛ 𝒴) :=
  MeasurableSpace.comap Prod.fst m𝒵

/-- Mechanism-level information at step `t` together with the internal randomness:
`σ(I_{M,t}, Z) = σ(Z, M_1, …, M_t)` (§2.2, Definition 2.4(ii)), where the type of mechanisms
carries the discrete σ-algebra. -/
@[instance_reducible] def mechSigma (𝒵 : Type) [m𝒵 : MeasurableSpace 𝒵] (P : Process 𝒳 ℛ 𝒴) (t : ℕ) :
    MeasurableSpace (𝒵 × Path ℛ 𝒴) :=
  MeasurableSpace.comap Prod.fst m𝒵 ⊔
    ⨆ k ∈ Finset.range t,
      MeasurableSpace.comap (fun ω : 𝒵 × Path ℛ 𝒴 => realisedMech P k ω.2)
        (instMeasurableSpaceMechanism 𝒳 𝒴)

/-- A spec-level filter (Definition 2.4(i), p. 7): `{T ≥ t} ∈ σ(I_S, Z)` for every step `t`. -/
def IsSpecLevel (T : 𝒵 × Path ℛ 𝒴 → ℕ) : Prop :=
  ∀ t : ℕ, MeasurableSet[specSigma 𝒵 ℛ 𝒴] {ω | t ≤ T ω}

/-- A mechanism-level filter (Definition 2.4(ii), p. 7): `{T ≥ t} ∈ σ(I_{M,t}, Z)` for every step
`t`, but the filter is not spec-level. -/
def IsMechanismLevel (P : Process 𝒳 ℛ 𝒴) (T : 𝒵 × Path ℛ 𝒴 → ℕ) : Prop :=
  (∀ t : ℕ, MeasurableSet[mechSigma 𝒵 P t] {ω | t ≤ T ω}) ∧ ¬ IsSpecLevel T

/-- The quantile function of an `ℕ`-valued random variable `T` under `μ` (Definition 3.1): the
left-continuous generalised inverse `Q(u) = inf {t ∈ ℕ : μ(T ≤ t) ≥ u}`, valued in `ℝ≥0∞`
(`= ∞` when the set is empty). -/
noncomputable def quantile {α : Type} [MeasurableSpace α] (μ : Measure α) (T : α → ℕ) (u : ℝ) :
    ℝ≥0∞ :=
  ⨅ (t : ℕ) (_ : ENNReal.ofReal u ≤ μ {a | T a ≤ t}), (t : ℝ≥0∞)

/-- The δ-clipped mean (Definition 3.1, p. 9) of `T` over a family of laws indexed by `ι`:
`inf_i (1/(1 − δ)) ∫_0^{1−δ} Q^i_T(u) du`, in `ℝ≥0∞` (lower Lebesgue integral). -/
noncomputable def clippedMean {ι α : Type} [MeasurableSpace α] (law : ι → Measure α)
    (T : α → ℕ) (δ : ℝ) : ℝ≥0∞ :=
  ⨅ i : ι, ENNReal.ofReal (1 / (1 - δ)) * ∫⁻ u in Set.Ioc 0 (1 - δ), quantile (law i) T u

/-- The δ-clipped mean `U_δ(T)` of a filter (Definition 3.1): the infimum over every database `x`
and every request strategy `𝒜` of `(1/(1 − δ)) ∫_0^{1−δ} Q^{x,𝒜}_T(u) du`. -/
noncomputable def filterClippedMean (P : Process 𝒳 ℛ 𝒴) (μZ : Measure 𝒵)
    (T : 𝒵 × Path ℛ 𝒴 → ℕ) (δ : ℝ) : ℝ≥0∞ :=
  clippedMean (fun i : 𝒳 × RequestStrategy ℛ 𝒴 => filterLaw P i.2 i.1 μZ) T δ

/-- `δ⁺_t` (App. B.1, (B.5), p. 18): the smallest `δ` for which the transcript after `t` releases
satisfies the `(ε, δ)`-DP inequality from `x` to `x′`,
`sup_S (P_x((R^t, Y^t) ∈ S) − e^ε P_{x′}((R^t, Y^t) ∈ S))`, `S` measurable. -/
noncomputable def deltaPlus (P : Process 𝒳 ℛ 𝒴) (A : RequestStrategy ℛ 𝒴) (x x' : 𝒳) (ε : ℝ)
    (t : ℕ) : ℝ≥0∞ :=
  ⨆ (S : Set (Hist ℛ 𝒴 t)) (_ : MeasurableSet S),
    interLaw P A x ((fun p : Path ℛ 𝒴 => fun j : Fin t => p j) ⁻¹' S)
      - ENNReal.ofReal (Real.exp ε) * interLaw P A x' ((fun p : Path ℛ 𝒴 => fun j : Fin t => p j) ⁻¹' S)

/-- `δ⁺_{(T)}` (App. B.1, p. 18): the smallest `δ` for which the stopped transcript of the filter
satisfies the `(ε, δ)`-DP inequality from `x` to `x′`. -/
noncomputable def deltaPlusStopped (P : Process 𝒳 ℛ 𝒴) (A : RequestStrategy ℛ 𝒴) (x x' : 𝒳)
    (ε : ℝ) (μZ : Measure 𝒵) (T : 𝒵 × Path ℛ 𝒴 → ℕ) : ℝ≥0∞ :=
  ⨆ (S : Set (Σ n, Hist ℛ 𝒴 n)) (_ : MeasurableSet S),
    filterLaw P A x μZ (stoppedTranscript T ⁻¹' S)
      - ENNReal.ofReal (Real.exp ε) * filterLaw P A x' μZ (stoppedTranscript T ⁻¹' S)

end PrivInfoHier.Main


