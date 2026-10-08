-- Prove2me | Definitions.Def_AffinePSD_Existence_MartingaleProblem
-- name    : AffinePSD_Existence_MartingaleProblem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:40.993981+00:00
-- url     : https://prove2.me/theorems/623ccb7f-d1af-4415-a921-ddd07d222e34
-- title:
--   Natural filtration, martingales, and càdlàg solutions of a martingale problem; the state space S_d^+ ∪ {Δ}
-- statement:
--   Let $X=(X_t)_{t\ge0}$ be a process on a probability space $(\Omega,\mathcal F,\mathbb P)$ with values in a topological space $E$ carrying its Borel $\sigma$-algebra, and let $\mathcal F^X_s=\sigma(X_r:0\le r\le s)$ be its natural filtration. A real process $M$ is a **martingale** for $(\mathcal F^X_t)$ if each $M_t$ is integrable, $M_s$ is $\mathcal F^X_s$-measurable, and $\int_A M_t\,d\mathbb P=\int_A M_s\,d\mathbb P$ for $s\le t$ and $A\in\mathcal F^X_s$.
--
--   Given test pairs $(f_i,g_i)_{i\in I}$ (in the paper, $g_i=\mathcal Af_i$) and $x_0\in E$, $X$ is a **càdlàg solution of the martingale problem** started at $x_0$ if every $X_t$ is measurable, every path is right-continuous with left limits, $X_0=x_0$ almost surely, and for every $i$ the process
--   $$f_i(X_t)-\int_0^t g_i(X_s)\,ds$$
--   is an $(\mathcal F^X_t)$-martingale, the time integral existing along every path.
--
--   The file also equips the one-point compactification $S_d^+\cup\{\Delta\}$ with its Borel $\sigma$-algebra, and extends a function $f$ on $S_d^+$ by $f(\Delta)=0$, the convention of §2.
--
--   **Formalization Note** Time is $\mathbb R_{\ge0}$, and càdlàg paths are the platform predicate `EthierKurtz.HasCadlagPaths`. The martingale property is stated directly through the natural $\sigma$-algebras rather than through Mathlib's `Filtration` structure.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), §1.2 p. 6, §2 p. 7, §5.2 (Lemmas 5.6, 5.8), pp. 44, 48; Ethier–Kurtz, Markov Processes, Ch. 4

import Mathlib
import Definitions.Def_AffinePSD_Existence_Cone
import Definitions.Def_EthierKurtz_HasCadlagPaths

open MeasureTheory
open scoped NNReal SchwartzMap

namespace AffinePSD.Existence

/-- The Borel σ-algebra on the one-point compactification `S_d^+ ∪ {Δ}`
(arXiv:0910.0137v3, §1.2, p. 6). -/
noncomputable instance instMeasurableSpaceOnePointCone (d : ℕ) :
    MeasurableSpace (OnePoint (Cone d)) := borel _

instance instBorelSpaceOnePointCone (d : ℕ) : BorelSpace (OnePoint (Cone d)) := ⟨rfl⟩

/-- Extension of a function on `S_d^+` to `S_d^+ ∪ {Δ}` by `f(Δ) = 0`
(the convention of arXiv:0910.0137v3, §2, p. 7). -/
def extΔ {d : ℕ} (f : Cone d → ℝ) (z : OnePoint (Cone d)) : ℝ := OnePoint.elim z 0 f

/-- The natural σ-algebra `F^X_s = σ(X_r : 0 ≤ r ≤ s)` of a process `X`. -/
def natPast {Ω E : Type*} [MeasurableSpace E] (X : ℝ≥0 → Ω → E) (s : ℝ≥0) : MeasurableSpace Ω :=
  ⨆ r ∈ Set.Icc (0 : ℝ≥0) s, MeasurableSpace.comap (X r) inferInstance

/-- `M` is a martingale with respect to the natural filtration of `X` under `Pr`: for `s ≤ t`,
`M_t` is integrable, `M_s` is `F^X_s`-measurable, and `∫_A M_t dPr = ∫_A M_s dPr` for every
`A ∈ F^X_s`. -/
def IsNatMartingale {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] (Pr : Measure Ω)
    (X : ℝ≥0 → Ω → E) (M : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ s t : ℝ≥0, s ≤ t → Integrable (M t) Pr ∧ StronglyMeasurable[natPast X s] (M s) ∧
    ∀ A, MeasurableSet[natPast X s] A → ∫ ω in A, M t ω ∂Pr = ∫ ω in A, M s ω ∂Pr

/-- `X` is a càdlàg solution, started at `x₀`, of the martingale problem for the pairs
`(f_i, A f_i)` = `(f i, g i)`, `i ∈ ι` ([Ethier–Kurtz, Ch. 4]; arXiv:0910.0137v3, §5.2,
Lemmas 5.6 and 5.8, pp. 44, 48): `Pr` is a probability measure, every `X_t` is measurable, every path
is càdlàg on `[0, ∞)`, `X_0 = x₀` a.s., and for every `i` the process
`f_i(X_t) − ∫_0^t g_i(X_s) ds` is a martingale for the natural filtration of `X`; the time integral
is required to exist on every path. -/
def SolvesMP {ι Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [MeasurableSpace E]
    (f g : ι → E → ℝ) (x₀ : E) (Pr : Measure Ω) (X : ℝ≥0 → Ω → E) : Prop :=
  IsProbabilityMeasure Pr ∧ (∀ t, Measurable (X t)) ∧ EthierKurtz.HasCadlagPaths X ∧
  (∀ᵐ ω ∂Pr, X 0 ω = x₀) ∧
  ∀ i : ι,
    (∀ ω (t : ℝ), IntervalIntegrable (fun r : ℝ => g i (X r.toNNReal ω)) volume 0 t) ∧
    IsNatMartingale Pr X (fun t ω => f i (X t ω) - ∫ r in (0 : ℝ)..(t : ℝ), g i (X r.toNNReal ω))

end AffinePSD.Existence


