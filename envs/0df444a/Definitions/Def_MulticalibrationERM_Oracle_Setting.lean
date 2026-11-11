-- Prove2me | Definitions.Def_MulticalibrationERM_Oracle_Setting
-- name    : MulticalibrationERM_Oracle_Setting
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:48:44.328079+00:00
-- url     : https://prove2.me/theorems/47df917a-f34f-4aac-ba0d-1baee426fa38
-- title:
--   §2 (Definition 2.1) — auditors, distributions over X × [0,1], randomized and deterministic predictors on the grid, MC and SMC
-- statement:
--   Let $X$ be a measurable space of **inputs**. An **auditor** is a function $h:X\to\{-1,+1\}$; in Lean it is `X → Bool` with real value `pm (h x)` ($+1$ for `true`, $-1$ for `false`). A **class** is a set $H$ of auditors. $\mathrm{VC}(H)\in\mathbb N\cup\{\infty\}$ is the largest size of a set shattered by $H$ (the published `NatureSLT.GrowthFunction.vcDim`). `IsAuditorClass H d` says $1\le d$, $\mathrm{VC}(H)\le d$, every $h\in H$ is measurable, and $H$ is **pointwise measurable**: some countable $H_0\subseteq H$ has, for every $h\in H$, a sequence in $H_0$ that is eventually equal to $h$ at every point (the concrete form of the paper's "standard measurability conditions for suprema over $H$").
--
--   A **distribution** $D$ over $X\times[0,1]$ is a probability measure on $X\times\mathbb R$ whose outcome coordinate lies in $[0,1]$ almost surely; $D_X$ is its input marginal, $\omega_x=D_X(\{x\})$ the mass of an input, and at an atom ($\omega_x>0$) $f^\star(x)=\mathbb E[Y\mathbf 1\{X=x\}]/\omega_x$ is the conditional mean outcome.
--
--   A **randomized predictor** with finite value set $V\subseteq[0,1]$ gives at each input a probability vector $Q_x$ on $V$, measurable in $x$. For an auditor $h$ and $v\in V$ the **bias** is
--   $$B_h(Q,v)=\mathbb E_{(X,Y)\sim D}\big[h(X)\,Q_X(v)\,(v-Y)\big],$$
--   and the multicalibration and swap multicalibration errors are
--   $$\mathrm{MC}(Q)=\sup_{h\in H}\sum_{v\in V}|B_h(Q,v)|,\qquad \mathrm{SMC}(Q)=\sum_{v\in V}\sup_{h\in H}|B_h(Q,v)|.$$
--   For an integer $K\ge1$ the **grid** is $\Lambda=\{0,1/K,\dots,1\}$, $m=K+1$; grid value $i/K$ is indexed by $i\in\{0,\dots,K\}$ (`Fin (K+1)`). A predictor on the grid is `Q : X → Fin (K+1) → ℝ` (`IsGridPred`: nonnegative, summing to $1$, measurable), with errors `gridMC`, `gridSMC`. A **deterministic predictor** $p:X\to\Lambda$ is identified with the point masses $Q_x=\delta_{p(x)}$ (`detPred`). `SupportNear K Q x lo hi` says every grid value of positive probability at $x$ lies in $[lo-1/K,\,hi+1/K]$. Finally `softLog d ε δ` $=\log(e\,d/(\varepsilon\delta))$ is the logarithmic factor in which every $\tilde O(\cdot)$ of the mission is expressed: $\tilde O(f)$ means at most $C\,f\cdot\mathrm{softLog}^a$ for absolute $C,a$.
--
--   **Formalization Note.** Probabilities of events that may be non-measurable are outer measures (a measure applied to an arbitrary set). The suprema in MC and SMC are over the subtype $H$; each term is bounded by $\sum_v\mathbb E[Q_X(v)]=1$.
-- source:
--   Okoroafor, The Sample Complexity of Multicalibration with an ERM Oracle, supplied 61-page preprint (PDF SHA256 654c7a8127547d76c5a4b6db236ce672c2c09a70d21d56a3981583e1805d0f8d; exact arXiv revision unresolved, not arXiv:2610.14363v1), pp. 3, 12–13, §2 and Definition 2.1

import Mathlib
import Definitions.Def_NatureSLT_GrowthFunction_vcDim

namespace MulticalibrationERM.Oracle

open MeasureTheory

/-! # Auditors, labeled distributions, predictors, and the multicalibration errors

Okoroafor, *The Sample Complexity of Multicalibration with an ERM Oracle* (supplied 61-page
preprint, SHA256 654c7a81…), Section 2, pp. 12–13 (Definition 2.1).

An auditor is a `{−1, +1}`-valued function on the input set `X`; it is stored as `X → Bool`
(`true` is `+1`) and its real value is `pm (h x)`. A class of auditors is `H : Set (X → Bool)` and
its VC dimension is the published `NatureSLT.GrowthFunction.vcDim` of the indexed family
`h ↦ h`. -/

/-- The real value `±1` of a Boolean auditor value: `true ↦ +1`, `false ↦ −1`. -/
def pm (b : Bool) : ℝ := if b then 1 else -1

/-- The VC dimension of a class `H ⊆ {−1, +1}^X` of auditors (in `ℕ∞`). -/
noncomputable def VC {X : Type*} (H : Set (X → Bool)) : ℕ∞ :=
  NatureSLT.GrowthFunction.vcDim (fun h : H => (h : X → Bool))

/-- Pointwise measurability of a class of `{−1, +1}`-valued functions, the concrete form used here
for the paper's "standard measurability conditions for suprema over `H`" (p. 12): there is a
countable subclass `H₀ ⊆ H` such that every member of `H` is the pointwise limit of a sequence in
`H₀` (for `{−1, +1}`-valued functions: at every point the sequence is eventually equal to it).
Then every supremum over `H` of the quantities used in the paper equals the supremum over the
countable `H₀`. -/
def PointwiseMeasurableClass {Z : Type*} (H : Set (Z → Bool)) : Prop :=
  ∃ H₀ : Set (Z → Bool), H₀ ⊆ H ∧ H₀.Countable ∧
    ∀ h ∈ H, ∃ u : ℕ → Z → Bool, (∀ k, u k ∈ H₀) ∧ ∀ z, ∀ᶠ k in Filter.atTop, u k z = h z

/-- `H` is a class of auditors of VC dimension at most `d`, with `1 ≤ d` (the paper's standing
assumption `1 ≤ d = VC(H) < ∞`, p. 12, with `d` an upper bound on the VC dimension), whose members
are measurable and which satisfies the standing measurability condition for suprema over `H`
(`PointwiseMeasurableClass`). -/
def IsAuditorClass {X : Type*} [MeasurableSpace X] (H : Set (X → Bool)) (d : ℕ) : Prop :=
  1 ≤ d ∧ VC H ≤ d ∧ (∀ h ∈ H, Measurable h) ∧ PointwiseMeasurableClass H

/-- The logarithmic factor `log(e d / (ε δ))` (at least `1` for `d ≥ 1`, `ε, δ ∈ (0, 1]`). A bound
`Õ(f)` in `d, 1/ε, 1/δ` (the paper's convention, p. 3 and p. 12: factors polylogarithmic in
`d, 1/ε, 1/δ` are hidden) is stated as `C · f · softLog d ε δ ^ a` for absolute constants `C, a`. -/
noncomputable def softLog (d ε δ : ℝ) : ℝ := Real.log (Real.exp 1 * d / (ε * δ))

/-- A distribution `D` over `X × [0, 1]`: a probability measure on `X × ℝ` whose outcome
coordinate lies in `[0, 1]` almost surely. -/
structure LabeledDist (X : Type*) [MeasurableSpace X] where
  /-- the joint law of `(X, Y)` -/
  μ : Measure (X × ℝ)
  isProb : IsProbabilityMeasure μ
  outcome_mem : ∀ᵐ z ∂μ, z.2 ∈ Set.Icc (0 : ℝ) 1

attribute [instance] LabeledDist.isProb

variable {X : Type*} [MeasurableSpace X]

/-- The input marginal `D_X`. -/
noncomputable def LabeledDist.marg (D : LabeledDist X) : Measure X := D.μ.map Prod.fst

/-- The mass `ω_x = D_X({x})` of a single input. -/
noncomputable def LabeledDist.atom (D : LabeledDist X) (x : X) : ℝ :=
  (D.μ (Prod.fst ⁻¹' {x})).toReal

/-- The conditional mean outcome `f⋆(x) = E[Y | X = x]` at an atom `x` of `D_X`
(`E[Y 1{X = x}] / D_X({x})`). At inputs of mass zero the conditional mean is not determined
pointwise; the value there is `0` and is never used (every statement that uses `f⋆(x)` requires
`0 < D_X({x})`). -/
noncomputable def LabeledDist.fstar (D : LabeledDist X) (x : X) : ℝ :=
  (∫ z in Prod.fst ⁻¹' {x}, z.2 ∂D.μ) / D.atom x

/-- The bias `B_h(Q, v) = E_{(X,Y)∼D}[h(X) Q_X(v) (v − Y)]` of a randomized predictor given by
its probabilities `P x v`, for an auditor `h` and a value `v` (Definition 2.1). -/
noncomputable def bias (D : LabeledDist X) (h : X → Bool) (P : X → ℝ → ℝ) (v : ℝ) : ℝ :=
  ∫ z, pm (h z.1) * P z.1 v * (v - z.2) ∂D.μ

/-- The (ℓ₁) multicalibration error `MC(Q; H, D) = sup_{h ∈ H} ∑_{v ∈ V} |B_h(Q, v)|` of a
randomized predictor with value set `V` and probabilities `P` (Definition 2.1). The supremum is
over the subtype `H`; every term is at most `∑_v E[Q_X(v)] = 1`, so it is bounded. -/
noncomputable def MCgen (D : LabeledDist X) (H : Set (X → Bool)) (V : Finset ℝ)
    (P : X → ℝ → ℝ) : ℝ :=
  ⨆ h : H, ∑ v ∈ V, |bias D h P v|

/-- The swap multicalibration error `SMC(Q; H, D) = ∑_{v ∈ V} sup_{h ∈ H} |B_h(Q, v)|`
(Definition 2.1). -/
noncomputable def SMCgen (D : LabeledDist X) (H : Set (X → Bool)) (V : Finset ℝ)
    (P : X → ℝ → ℝ) : ℝ :=
  ∑ v ∈ V, ⨆ h : H, |bias D h P v|

/-- A finitely supported randomized predictor: a finite value set `V ⊆ [0, 1]` and, at each input
`x`, a probability distribution `Q_x` on `V` (given by `prob x v`, zero off `V`), measurable in
`x`. -/
structure RandPred (X : Type*) [MeasurableSpace X] where
  V : Finset ℝ
  prob : X → ℝ → ℝ
  V_subset : ∀ v ∈ V, v ∈ Set.Icc (0 : ℝ) 1
  nonneg : ∀ x v, 0 ≤ prob x v
  sum_eq_one : ∀ x, ∑ v ∈ V, prob x v = 1
  zero_off : ∀ x v, v ∉ V → prob x v = 0
  meas : ∀ v, Measurable (fun x => prob x v)

/-- `MC(Q)` of a finitely supported randomized predictor. -/
noncomputable def RandPred.MC (D : LabeledDist X) (H : Set (X → Bool)) (Q : RandPred X) : ℝ :=
  MCgen D H Q.V Q.prob

/-! ### The grid `Λ = {0, 1/K, …, 1}` and predictors on it

A grid value is indexed by `i : Fin (K + 1)` and equals `i / K`; `m = K + 1 = |Λ|`. -/

/-- The grid value `i / K`. -/
noncomputable def gv (K : ℕ) (i : Fin (K + 1)) : ℝ := (i : ℝ) / K

/-- The grid `Λ_K = {0, 1/K, …, 1}` as a finite set of reals. -/
noncomputable def gridSet (K : ℕ) : Finset ℝ := Finset.univ.image (gv K)

/-- The probabilities `v ↦ Q_x(v)` on `ℝ` of a grid predictor `Q : X → Fin (K+1) → ℝ`
(`Q x i` is the probability of the grid value `i / K`). -/
noncomputable def gridProb (K : ℕ) (Q : X → Fin (K + 1) → ℝ) : X → ℝ → ℝ :=
  fun x v => ∑ i, if gv K i = v then Q x i else 0

/-- `Q : X → Fin (K+1) → ℝ` is a randomized predictor on the grid: each `Q x` is a probability
vector and each coordinate is measurable in `x`. -/
def IsGridPred (K : ℕ) (Q : X → Fin (K + 1) → ℝ) : Prop :=
  (∀ x i, 0 ≤ Q x i) ∧ (∀ x, ∑ i, Q x i = 1) ∧ ∀ i, Measurable (fun x => Q x i)

/-- `MC(Q)` of a randomized predictor on the grid `Λ_K`. -/
noncomputable def gridMC (D : LabeledDist X) (H : Set (X → Bool)) (K : ℕ)
    (Q : X → Fin (K + 1) → ℝ) : ℝ :=
  MCgen D H (gridSet K) (gridProb K Q)

/-- `SMC(Q)` of a randomized predictor on the grid `Λ_K`. -/
noncomputable def gridSMC (D : LabeledDist X) (H : Set (X → Bool)) (K : ℕ)
    (Q : X → Fin (K + 1) → ℝ) : ℝ :=
  SMCgen D H (gridSet K) (gridProb K Q)

/-- A deterministic predictor `p : X → Λ_K`, identified with the randomized predictor
`Q_x = δ_{p(x)}`. -/
def detPred (K : ℕ) (p : X → Fin (K + 1)) : X → Fin (K + 1) → ℝ :=
  fun x i => if p x = i then 1 else 0

/-- `Q` is supported within distance `1/K` of the interval `[lo, hi]` at `x`:
every grid value of positive probability lies in `[lo − 1/K, hi + 1/K]`. -/
def SupportNear (K : ℕ) (Q : X → Fin (K + 1) → ℝ) (x : X) (lo hi : ℝ) : Prop :=
  ∀ i, Q x i ≠ 0 → lo - 1 / (K : ℝ) ≤ gv K i ∧ gv K i ≤ hi + 1 / (K : ℝ)

end MulticalibrationERM.Oracle


