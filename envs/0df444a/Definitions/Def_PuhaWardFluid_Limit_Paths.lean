-- Prove2me | Definitions.Def_PuhaWardFluid_Limit_Paths
-- name    : PuhaWardFluid_Limit_Paths
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:20:11.768189+00:00
-- url     : https://prove2.me/theorems/2163101b-97c4-4879-9023-3f7d3281748a
-- title:
--   §1.1.5, p. 4 — rcll paths, D↑, Skorokhod J₁ convergence, convergence in distribution, relative compactness, C-tightness, Kurtz' (K.2)
-- statement:
--   This file fixes the path-space vocabulary used throughout the mission (Puha–Ward, §1.1.5, p. 4, and Appendix A.1, p. 34).
--
--   1. A path $x:\mathbb R_+\to S$ into a topological space $S$ is **rcll** (càdlàg) if it is right continuous at every $t\ge 0$ and has a finite left limit at every $t>0$.
--   2. A **time change** is a continuous, strictly increasing map of $\mathbb R_+$ onto itself.
--   3. Given a distance $d$ on $S$, rcll paths $x_n$ converge to an rcll path $x$ in the **Skorokhod $J_1$ topology** if there are time changes $\lambda_n$ with
--   $$\sup_{t\le T} d\big(x_n(\lambda_n(t)),x(t)\big)\to 0\quad\text{and}\quad \sup_{t\le T}|\lambda_n(t)-t|\to 0\qquad\text{for every }T\ge0 .$$
--   For a product space there is one time change for all coordinates.
--   4. $\mathbf D_\uparrow(\mathbb R^J_+)$ is the set of rcll paths in $\mathbb R^J$ each of whose coordinates is nondecreasing with initial value $0$.
--   5. Random paths $Y_n$ on $(\Omega,\mathbb P)$ **converge in distribution** to a random path $Y'$ on $(\Omega',\mathbb P')$ if, on some probability space, there are copies $W_n\stackrel{d}{=}Y_n$ and $W'\stackrel{d}{=}Y'$ with $W_n\to W'$ in $J_1$ almost surely. $(\Omega',\mathbb P',Y')$ is a **distributional limit point** of $(Y_n)$ if some subsequence converges to it in distribution.
--   6. $(Y_n)$ is **relatively compact** if every subsequence has a further subsequence converging in distribution, and **C-tight** if moreover the further subsequence can be chosen with a limit whose paths are almost surely continuous.
--   7. A sequence of real processes $(H^n)$ satisfies **(K.2) of Kurtz' criteria** if for every rational $t>0$ there is $q>0$ with $\lim_{\varepsilon\to0}\sup_n\mathbb E\big[|H^n(t+\varepsilon)-H^n(t)|^q\big]=0$.
--
--   These notions are the language of Theorem 1: tightness of the fluid-scaled states, their distributional limit points, and the C-tightness alternative of Assumption 5.
--
--   **Formalization Note** Convergence in distribution is stated in coupling (Skorokhod representation) form; laws of paths are compared on the product σ-algebra of $S^{\mathbb R_+}$, which on rcll paths coincides with the Borel σ-algebra of $J_1$. For a Polish $S$ the coupling form is equivalent to weak convergence of the laws on $\mathbf D(S)$, and relative compactness is equivalent to tightness (Prohorov's theorem). The paper uses "C-tight" without defining it; the standard meaning is encoded. (K.2) is encoded exactly as printed.
-- source:
--   Puha & Ward, Fluid limits for multiclass many-server queues with general reneging distributions and head-of-the-line scheduling, Math. Oper. Res., Articles in Advance (21 Dec 2021), doi:10.1287/moor.2021.1166, pp. 4, 34 (PDF 5, 35), §1.1.5, Appendix A.1.1

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace PuhaWardFluid.Limit

/-- An **rcll (càdlàg) path** `x : ℝ₊ → S` (Puha–Ward, §1.1.5, p. 4): right continuous at every
`t ≥ 0`, with a finite left limit at every `t > 0`. -/
def IsCadlag {S : Type*} [TopologicalSpace S] (x : ℝ≥0 → S) : Prop :=
  (∀ t : ℝ≥0, ContinuousWithinAt x (Set.Ici t) t) ∧
    ∀ t : ℝ≥0, 0 < t → ∃ a : S, Tendsto x (𝓝[<] t) (𝓝 a)

/-- A **time change**: a continuous, strictly increasing map of `ℝ₊` onto `ℝ₊`. -/
def IsTimeChange (l : ℝ≥0 → ℝ≥0) : Prop :=
  Continuous l ∧ StrictMono l ∧ Function.Surjective l

/-- `x_n → x` uniformly on `[0, T]` for every `T`, measured with the distance function `d`. -/
def UnifOnCompacts {S : Type*} (d : S → S → ℝ) (xs : ℕ → ℝ≥0 → S) (x : ℝ≥0 → S) : Prop :=
  ∀ T : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ T → d (xs n t) (x t) < ε

/-- **Skorokhod `J₁` convergence** in `D(S)` (§1.1.5, p. 4; Billingsley; Ethier–Kurtz Prop. 3.5.3):
the rcll paths `x_n` converge to the rcll path `x` if there are time changes `λ_n` with
`x_n(λ_n(t)) → x(t)` and `λ_n(t) → t`, both uniformly on bounded intervals. The distance `d`
metrizes the topology of `S`; for a product space there is one time change for all coordinates. -/
def J1Tendsto {S : Type*} [TopologicalSpace S] (d : S → S → ℝ) (xs : ℕ → ℝ≥0 → S)
    (x : ℝ≥0 → S) : Prop :=
  (∀ n, IsCadlag (xs n)) ∧ IsCadlag x ∧
    ∃ l : ℕ → ℝ≥0 → ℝ≥0, (∀ n, IsTimeChange (l n)) ∧
      UnifOnCompacts d (fun n => xs n ∘ l n) x ∧
      UnifOnCompacts (fun a b : ℝ≥0 => dist (a : ℝ) (b : ℝ)) l id

/-- `D↑(ℝ^k₊)` (§1.1.5, p. 4): rcll paths each of whose coordinates is nondecreasing with initial
value zero (hence nonnegative). -/
def IsDUp {J : ℕ} (x : ℝ≥0 → Fin J → ℝ) : Prop :=
  IsCadlag x ∧ (∀ j, Monotone fun t => x t j) ∧ x 0 = 0

/-- **Convergence in distribution** of random paths `Y n` on `(Ω, P)` to the random path `Y'` on
`(Ω', P')`, in coupling (Skorokhod representation) form: on some probability space there are
copies `W n` of `Y n` and `W'` of `Y'` (equal in law for the product σ-algebra on paths) with
`W n → W'` in `J₁`, almost surely. For a Polish `S` this is equivalent to weak convergence of the
laws on `D(S)`. -/
def ConvInDist {S : Type*} [TopologicalSpace S] [MeasurableSpace S] (d : S → S → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : ℕ → Ω → ℝ≥0 → S)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') (Y' : Ω' → ℝ≥0 → S) : Prop :=
  IsProbabilityMeasure P ∧ IsProbabilityMeasure P' ∧
    ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (P'' : Measure Ω'') (W : ℕ → Ω'' → ℝ≥0 → S)
      (W' : Ω'' → ℝ≥0 → S),
      IsProbabilityMeasure P'' ∧ (∀ n, IdentDistrib (W n) (Y n) P'' P) ∧
      IdentDistrib W' Y' P'' P' ∧ ∀ᵐ ω ∂P'', J1Tendsto d (fun n => W n ω) (W' ω)

/-- `(Ω', P', Y')` is a **distributional limit point** of the sequence `Y`: some subsequence
converges to it in distribution. -/
def IsDistLimitPoint {S : Type*} [TopologicalSpace S] [MeasurableSpace S] (d : S → S → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : ℕ → Ω → ℝ≥0 → S)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') (Y' : Ω' → ℝ≥0 → S) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvInDist d P (fun n => Y (φ n)) P' Y'

/-- **Relative compactness** of the laws of `Y` in `D(S)`: every subsequence has a further
subsequence converging in distribution. On a Polish `D(S)` this is tightness (Prohorov). -/
def RelCompactInDist {S : Type*} [TopologicalSpace S] [MeasurableSpace S] (d : S → S → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : ℕ → Ω → ℝ≥0 → S) : Prop :=
  ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (Y' : Ω' → ℝ≥0 → S),
      ConvInDist d P (fun n => Y (φ (ψ n))) P' Y'

/-- **C-tightness**: every subsequence has a further subsequence converging in distribution to a
limit with almost surely continuous paths. Equivalently, the laws are relatively compact in
`D(S)` and every distributional limit point is supported on continuous paths. -/
def CTight {S : Type*} [TopologicalSpace S] [MeasurableSpace S] (d : S → S → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : ℕ → Ω → ℝ≥0 → S) : Prop :=
  ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (Y' : Ω' → ℝ≥0 → S),
      ConvInDist d P (fun n => Y (φ (ψ n))) P' Y' ∧ ∀ᵐ ω ∂P', Continuous (Y' ω)

/-- Condition **(K.2) of Kurtz' criteria** (Appendix A.1.1, p. 34), exactly as printed, for real
processes `H n` on `(Ω, P)`: for all rational `t > 0` there is `q > 0` with
`lim_{ε → 0} sup_n E[|H^n(t + ε) − H^n(t)|^q] = 0` (the expectation in `[0, ∞]`). -/
def KurtzK2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (H : ℕ → Ω → ℝ≥0 → ℝ) : Prop :=
  ∀ t : ℚ, 0 < t → ∃ q : ℝ, 0 < q ∧
    Tendsto (fun ε : ℝ≥0 => ⨆ n, ∫⁻ ω, ENNReal.ofReal
        (|H n ω ((t : ℝ).toNNReal + ε) - H n ω (t : ℝ).toNNReal| ^ q) ∂P)
      (𝓝[>] 0) (𝓝 0)

end PuhaWardFluid.Limit


