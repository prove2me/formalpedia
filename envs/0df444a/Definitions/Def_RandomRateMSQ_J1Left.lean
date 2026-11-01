-- Prove2me | Definitions.Def_RandomRateMSQ_J1Left
-- name    : RandomRateMSQ_J1Left
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:24:48.135832+00:00
-- url     : https://prove2.me/theorems/4df1f5e7-cebc-402b-8e9e-c3f1aa993173
-- title:
--   Skorokhod $J_1$ convergence of left-continuous paths, and convergence in distribution in coupling form
-- statement:
--   A path $x:[0,\infty)\to S$ is **left-continuous with right limits** if it is left continuous at every $t$ and has a right limit at every $t$; these paths form $G_S[0,\infty)$.
--
--   Left-continuous paths $x_n$ converge to $x$ in **Skorokhod $J_1$** (with distance $d$ on $S$) if there are continuous, strictly increasing time changes $\lambda_n$ of $[0,\infty)$ onto itself with
--
--   $$
--   \sup_{t\le T}d\big(x_n(\lambda_n(t)),x(t)\big)\to0,\qquad \sup_{t\le T}|\lambda_n(t)-t|\to0\qquad\text{for every }T.
--   $$
--
--   On the space $\mathcal P$ of probability measures on $\mathbb R_+$ the distance is Lévy–Prokhorov. **Convergence in distribution** of random left-continuous paths is stated in coupling form: there are copies on one probability space converging almost surely. **Tightness** is relative compactness: every subsequence has a further subsequence converging in distribution. A generic coupling form is also given for random elements of a topological space.
--
--   These are the convergence notions of Definition 1 and Theorem 2.
--
--   **Formalization Note** The definitions are twins of the public `PuhaWardFluid.Limit.J1Tendsto`, `ConvInDist` and `RelCompactInDist` (càdlàg paths). The paper defines $J_1$ on $G_X[a,b]$ by time reversal into $D_X[a-b,0]$; on each $[0,T]$ time changes commute with time reversal.
-- source:
--   Büke and Qin, Many-Server Queues with Random Service Rates in the Halfin-Whitt Regime, arXiv:1905.04198v1, §1.1, p.3 (G_X[a,b], Skorokhod J1, Prokhorov metric) and Definition 1, p.10

import Mathlib
import Definitions.Def_PuhaWardFluid_Limit_Paths

open MeasureTheory ProbabilityTheory Filter Topology
open PuhaWardFluid.Limit
open scoped NNReal ENNReal

namespace RandomRateMSQ

/-- A path `x : ℝ₊ → S` is **left-continuous with right limits** (a member of `G_S[0, ∞)`,
Büke–Qin, arXiv:1905.04198v1, §1.1, p.3: "left-continuous functions … G_X[a, b]"): it is left
continuous at every `t` and has a right limit at every `t`. -/
def IsCaglad {S : Type*} [TopologicalSpace S] (x : ℝ≥0 → S) : Prop :=
  (∀ t : ℝ≥0, ContinuousWithinAt x (Set.Iic t) t) ∧
    ∀ t : ℝ≥0, ∃ a : S, Tendsto x (𝓝[>] t) (𝓝 a)

/-- **Skorokhod `J₁` convergence of left-continuous paths** on `G_S[0, ∞)`
(arXiv:1905.04198v1, §1.1, p.3, and Definition 1, p.10): the left-continuous paths `x_n` converge
to the left-continuous path `x` if there are time changes `λ_n` (public
`PuhaWardFluid.Limit.IsTimeChange`) with `x_n(λ_n(t)) → x(t)` and `λ_n(t) → t`, both uniformly on
bounded intervals, distances in `S` measured by `d`. It is the twin of public
`PuhaWardFluid.Limit.J1Tendsto` with `IsCaglad` in place of `IsCadlag`.

**Formalization Note.** The paper defines the topology on `G_X[a, b]` by time reversal into
`D_X[a − b, 0]` and extends it to `[0, ∞)` "in a similar manner"; time changes of `[0, T]`
commute with time reversal, so on each `[0, T]` this is the same convergence. On `[0, ∞)` the
global time changes (uniform on compacts) are used, as in public `J1Tendsto`. -/
def J1LeftTendsto {S : Type*} [TopologicalSpace S] (d : S → S → ℝ) (xs : ℕ → ℝ≥0 → S)
    (x : ℝ≥0 → S) : Prop :=
  (∀ n, IsCaglad (xs n)) ∧ IsCaglad x ∧
    ∃ l : ℕ → ℝ≥0 → ℝ≥0, (∀ n, IsTimeChange (l n)) ∧
      UnifOnCompacts d (fun n => xs n ∘ l n) x ∧
      UnifOnCompacts (fun a b : ℝ≥0 => dist (a : ℝ) (b : ℝ)) l id

/-- The Lévy–Prokhorov distance between probability measures on `ℝ₊` (the paper's Prokhorov metric
on `P`, arXiv:1905.04198v1, §1.1, p.3). -/
noncomputable def lpDist (ν ν' : ProbabilityMeasure ℝ≥0) : ℝ :=
  levyProkhorovDist (ν : Measure ℝ≥0) (ν' : Measure ℝ≥0)

/-- **Convergence in distribution of left-continuous random paths**, in coupling (Skorokhod
representation) form: on some probability space there are copies `W n` of `Y n` and `W'` of `Y'`
(equal in law for the product σ-algebra on paths) with `W n → W'` in left-continuous `J₁` almost
surely. The twin of public `PuhaWardFluid.Limit.ConvInDist`. -/
def ConvInDistLeft {S : Type*} [TopologicalSpace S] [MeasurableSpace S] (d : S → S → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : ℕ → Ω → ℝ≥0 → S)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') (Y' : Ω' → ℝ≥0 → S) : Prop :=
  IsProbabilityMeasure P ∧ IsProbabilityMeasure P' ∧
    ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (P'' : Measure Ω'') (W : ℕ → Ω'' → ℝ≥0 → S)
      (W' : Ω'' → ℝ≥0 → S),
      IsProbabilityMeasure P'' ∧ (∀ n, IdentDistrib (W n) (Y n) P'' P) ∧
      IdentDistrib W' Y' P'' P' ∧ ∀ᵐ ω ∂P'', J1LeftTendsto d (fun n => W n ω) (W' ω)

/-- **Tightness (relative compactness in distribution) of left-continuous random paths**: every
subsequence has a further subsequence converging in distribution (`ConvInDistLeft`). The twin of
public `PuhaWardFluid.Limit.RelCompactInDist`. -/
def RelCompactInDistLeft {S : Type*} [TopologicalSpace S] [MeasurableSpace S] (d : S → S → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : ℕ → Ω → ℝ≥0 → S) : Prop :=
  ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (Y' : Ω' → ℝ≥0 → S),
      ConvInDistLeft d P (fun n => Y (φ (ψ n))) P' Y'

/-- **Convergence in distribution of random elements** `Y n` (on `(Ω, P)`) of a topological space
`E` to `Y'` (on `(Ω', P')`), in coupling form: on some probability space there are copies of every
`Y n` and of `Y'` with almost sure convergence. For `E` Polish this is weak convergence of the
laws. -/
def ConvInDistCoupling {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : ℕ → Ω → E)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') (Y' : Ω' → E) : Prop :=
  IsProbabilityMeasure P ∧ IsProbabilityMeasure P' ∧
    ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (P'' : Measure Ω'') (W : ℕ → Ω'' → E)
      (W' : Ω'' → E),
      IsProbabilityMeasure P'' ∧ (∀ n, IdentDistrib (W n) (Y n) P'' P) ∧
      IdentDistrib W' Y' P'' P' ∧ ∀ᵐ ω ∂P'', Tendsto (fun n => W n ω) atTop (𝓝 (W' ω))

end RandomRateMSQ


