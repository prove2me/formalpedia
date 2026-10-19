-- Prove2me | Definitions.Def_PeriodicDividend_FixedPoint_Model
-- name    : PeriodicDividend_FixedPoint_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:27.700312+00:00
-- url     : https://prove2.me/theorems/26e88ceb-c95d-4561-bc90-85727b7ff56e
-- title:
--   §3.1–§3.3 — periodic dividends, issuance controls and fixed-point operators
-- statement:
--   Let the reserve of a firm start at $x\ge0$, receive Brownian cash flow $C_t=\mu t+\sigma W_t$, pay dividends $\ell_n$ at dates $nT$, and receive locally finite equity issues $\zeta_k$ at stopping times $\tau_k$. Positive issues cost $c(\zeta)=\lambda_f+(1+\lambda_p)\zeta$. Ruin occurs when reserves first become negative. Policies are adapted, issues and dividends are nonnegative, dividends are covered by reserves immediately before payment, and actions stop at ruin.
--
--   The model defines the discounted objective, its supremum $V(x)$ over admissible policies, the one-period issuance operator $\mathcal L$, the dividend operator $\mathcal D$, and $\mathcal T=\mathcal D\circ\mathcal L$. It also defines the classes $\widehat{\mathcal C}_A$ and $\mathcal C_A$ of Definition 3.2, the threshold $A^*=\mu T/(e^{\rho T}-1)$, and the arbitrary-maturity one-period value and PDE class of §3.3.
--
--   These definitions are the shared setting for Theorems 3.3, 3.4 and 3.6.
--
--   **Formalization Note** Values that may be infinite use extended reals. An issue at the period endpoint is excluded from $\mathcal L$, which uses the reserve immediately before $T$. The usual right-continuity and initial completeness conditions are encoded separately.
-- source:
--   Keppo, Reppen, Soner, Discrete dividend payments in continuous time, arXiv:1805.05077v2, pp. 4–8, §3.1–§3.3, Definition 3.2, Definition 3.5, equations (3.1)–(3.6)

import Mathlib
import Definitions.Def_AtaBarjesteh23_Workload_DriftBM

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace PeriodicDividend.FixedPoint

/-- Parameters of the periodic dividend and fixed-cost equity issuance model. -/
structure Params where
  rho : ℝ
  mu : ℝ
  sigma : ℝ
  lamF : ℝ
  lamP : ℝ
  T : ℝ

/-- The positive-parameter regime of §3.1, with the implicit positive period made explicit. -/
def Params.Standing (p : Params) : Prop :=
  0 < p.rho ∧ 0 < p.mu ∧ 0 < p.sigma ∧ 0 < p.lamF ∧ 0 < p.lamP ∧ 0 < p.T

/-- The usual filtration conditions on nonnegative times: right continuity and
inclusion of all ambient null subsets in the initial σ-algebra. -/
def UsualConditions {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (𝔽 : Filtration ℝ mΩ) : Prop :=
  𝔽.IsRightContinuous ∧
    ∀ s : Set Ω, MeasurableSet s → P s = 0 →
      ∀ t : Set Ω, t ⊆ s → MeasurableSet[𝔽 0] t

/-- The fixed plus proportional cost of a positive issue, and zero cost for no issue. -/
noncomputable def issueCost (p : Params) (z : ℝ) : ℝ :=
  if 0 < z then p.lamF + (1 + p.lamP) * z else 0

/-- The threshold specified in the proof of Theorem 3.3. -/
noncomputable def Astar (p : Params) : ℝ :=
  p.mu * p.T / (Real.exp (p.rho * p.T) - 1)

/-- Issuance is a locally finite sequence of dated impulses. `⊤` means no issue. -/
structure Issuance (Ω : Type*) where
  τ : ℕ → Ω → ℝ≥0∞
  ζ : ℕ → Ω → ℝ

/-- A periodic dividend amount is chosen at every `nT`, including `n = 0`. -/
abbrev Dividends (Ω : Type*) := ℕ → Ω → ℝ

/-- Cumulative issues through time `t`. -/
noncomputable def issuedThrough {Ω : Type*} (I : Issuance Ω) (t : ℝ) (ω : Ω) : ℝ :=
  ∑' k, if I.τ k ω ≤ ENNReal.ofReal t then I.ζ k ω else 0

/-- Cumulative issues strictly before time `t`. -/
noncomputable def issuedBefore {Ω : Type*} (I : Issuance Ω) (t : ℝ) (ω : Ω) : ℝ :=
  ∑' k, if I.τ k ω < ENNReal.ofReal t then I.ζ k ω else 0

/-- Cumulative dividends through time `t`. -/
noncomputable def paidThrough {Ω : Type*} (p : Params) (d : Dividends Ω)
    (t : ℝ) (ω : Ω) : ℝ :=
  ∑' (n : ℕ), if (n : ℝ) * p.T ≤ t then d n ω else 0

/-- Cumulative dividends strictly before time `t`. -/
noncomputable def paidBefore {Ω : Type*} (p : Params) (d : Dividends Ω)
    (t : ℝ) (ω : Ω) : ℝ :=
  ∑' (n : ℕ), if (n : ℝ) * p.T < t then d n ω else 0

/-- Cash reserves immediately after actions at `t`. -/
noncomputable def reserve {Ω : Type*} (C : ℝ → Ω → ℝ) (p : Params)
    (x : ℝ≥0) (d : Dividends Ω) (I : Issuance Ω) (t : ℝ) (ω : Ω) : ℝ :=
  (x : ℝ) + C t ω - paidThrough p d t ω + issuedThrough I t ω

/-- Cash reserves immediately before actions at `t`. -/
noncomputable def reserveBefore {Ω : Type*} (C : ℝ → Ω → ℝ) (p : Params)
    (x : ℝ≥0) (d : Dividends Ω) (I : Issuance Ω) (t : ℝ) (ω : Ω) : ℝ :=
  (x : ℝ) + C t ω - paidBefore p d t ω + issuedBefore I t ω

/-- First strictly positive time at which reserves are negative; `⊤` if none. -/
noncomputable def ruin {Ω : Type*} (C : ℝ → Ω → ℝ) (p : Params)
    (x : ℝ≥0) (d : Dividends Ω) (I : Issuance Ω) (ω : Ω) : ℝ≥0∞ :=
  sInf ((fun t : ℝ => ENNReal.ofReal t) ''
    {t : ℝ | 0 < t ∧ reserve C p x d I t ω < 0})

/-- The policy that never issues equity. -/
def noIssuance (Ω : Type*) : Issuance Ω := ⟨fun _ _ => ⊤, fun _ _ => 0⟩

/-- The zero dividend stream. -/
def noDividends (Ω : Type*) : Dividends Ω := fun _ _ => 0

/-- Admissible locally finite, adapted issuance and covered periodic dividends, both stopped at ruin. -/
def Admissible {Ω : Type*} [mΩ : MeasurableSpace Ω] (𝔽 : Filtration ℝ mΩ)
    (C : ℝ → Ω → ℝ) (p : Params) (x : ℝ≥0)
    (d : Dividends Ω) (I : Issuance Ω) : Prop :=
  (∀ k t, 0 ≤ t → MeasurableSet[𝔽 t] {ω | I.τ k ω ≤ ENNReal.ofReal t}) ∧
  (∀ k t, 0 ≤ t → StronglyMeasurable[𝔽 t]
    (fun ω => if I.τ k ω ≤ ENNReal.ofReal t then I.ζ k ω else 0)) ∧
  (∀ k ω, 0 ≤ I.ζ k ω) ∧
  (∀ k ω, I.τ k ω ≤ I.τ (k + 1) ω) ∧
  (∀ ω t, 0 ≤ t → {k | I.τ k ω ≤ ENNReal.ofReal t}.Finite) ∧
  (∀ k ω, I.τ k ω ≠ ⊤ → I.τ k ω ≤ ruin C p x d I ω) ∧
  (∀ (n : ℕ), StronglyMeasurable[𝔽 ((n : ℝ) * p.T)] (d n)) ∧
  (∀ (n : ℕ) ω, 0 ≤ d n ω ∧
    (ENNReal.ofReal ((n : ℝ) * p.T) ≤ ruin C p x d I ω →
      d n ω ≤ reserveBefore C p x d I ((n : ℝ) * p.T) ω) ∧
    (ENNReal.ofReal ((n : ℝ) * p.T) > ruin C p x d I ω → d n ω = 0))

/-- Discounted dividends, as an extended nonnegative integral. -/
noncomputable def dividendReward {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (p : Params) (d : Dividends Ω) : ℝ≥0∞ :=
  ∫⁻ ω, ∑' (n : ℕ), ENNReal.ofReal
    (Real.exp (-p.rho * ((n : ℝ) * p.T)) * d n ω) ∂P

/-- Discounted issuance costs, as an extended nonnegative integral. -/
noncomputable def issuanceCost {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (p : Params) (I : Issuance Ω) : ℝ≥0∞ :=
  ∫⁻ ω, ∑' k, if I.τ k ω = ⊤ then 0 else ENNReal.ofReal
    (Real.exp (-p.rho * (I.τ k ω).toReal) * issueCost p (I.ζ k ω)) ∂P

/-- The payoff `J`: expected dividends less expected issuance costs. -/
noncomputable def payoff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (p : Params) (d : Dividends Ω) (I : Issuance Ω) : EReal :=
  (dividendReward P p d : EReal) - (issuanceCost P p I : EReal)

/-- The control-defined value function, the supremum over admissible dividend and issuance policies. -/
noncomputable def valueFn {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (𝔽 : Filtration ℝ mΩ) (C : ℝ → Ω → ℝ) (p : Params) (x : ℝ≥0) : EReal :=
  sSup {y : EReal | ∃ (d : Dividends Ω) (I : Issuance Ω),
    Admissible 𝔽 C p x d I ∧ y = payoff P p d I}

/-- The intervention operator `I(φ)(x)` of §3.2. -/
noncomputable def Iop (p : Params) (φ : ℝ≥0 → ℝ) (x : ℝ≥0) : ℝ :=
  sSup {y : ℝ | ∃ z : ℝ≥0, 0 < z ∧ y = φ (x + z) - issueCost p z}

/-- The space Ĉ_A of Definition 3.2. -/
def ChatA (p : Params) (A : ℝ) (φ : ℝ≥0 → ℝ) : Prop :=
  Continuous φ ∧ Monotone φ ∧
  (∀ x, 0 ≤ φ x ∧ max (Iop p φ x) 0 ≤ φ x ∧ φ x ≤ (x : ℝ) + A) ∧
  φ 0 = max (Iop p φ 0) 0

/-- The space C_A of Definition 3.2. -/
def CA (p : Params) (A : ℝ) (φ : ℝ≥0 → ℝ) : Prop :=
  ChatA p A φ ∧ Monotone (fun x => φ x - (x : ℝ)) ∧
  (∀ x, |φ x - (x : ℝ)| ≤ A)

/-- No-dividend reserve immediately before the maturity `t`. -/
noncomputable def oneReserveBefore {Ω : Type*} (C : ℝ → Ω → ℝ)
    (x : ℝ≥0) (I : Issuance Ω) (t : ℝ) (ω : Ω) : ℝ :=
  (x : ℝ) + C t ω + issuedBefore I t ω

/-- Expected terminal reward on survival, for a one-period issuance control. -/
noncomputable def terminalReward {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : ℝ → Ω → ℝ) (p : Params) (φ : ℝ≥0 → ℝ)
    (x : ℝ≥0) (I : Issuance Ω) (t : ℝ) (strict : Bool) : ℝ≥0∞ :=
  ∫⁻ ω, if (if strict then ENNReal.ofReal t < ruin C p x (noDividends Ω) I ω
    else ENNReal.ofReal t ≤ ruin C p x (noDividends Ω) I ω) then
      ENNReal.ofReal (Real.exp (-p.rho * t) *
        φ (Real.toNNReal (oneReserveBefore C x I t ω))) else 0 ∂P

/-- Cost of issues strictly before one-period maturity `t`. -/
noncomputable def costBefore {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (p : Params) (I : Issuance Ω) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∑' k, if I.τ k ω < ENNReal.ofReal t then ENNReal.ofReal
    (Real.exp (-p.rho * (I.τ k ω).toReal) * issueCost p (I.ζ k ω)) else 0 ∂P

/-- The one-period objective with a strict survival indicator, as in (3.2). -/
noncomputable def onePayoff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : ℝ → Ω → ℝ) (p : Params) (φ : ℝ≥0 → ℝ)
    (x : ℝ≥0) (I : Issuance Ω) : EReal :=
  (terminalReward P C p φ x I p.T true : EReal) - (costBefore P p I p.T : EReal)

/-- The operator L of (3.2), a supremum over admissible issuance-only policies. -/
noncomputable def Lop {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (𝔽 : Filtration ℝ mΩ) (C : ℝ → Ω → ℝ) (p : Params)
    (φ : ℝ≥0 → ℝ) (x : ℝ≥0) : EReal :=
  sSup {y : EReal | ∃ I : Issuance Ω,
    Admissible 𝔽 C p x (noDividends Ω) I ∧ y = onePayoff P C p φ x I}

/-- The dividend operator D of (3.3). -/
noncomputable def Dop (φ : ℝ≥0 → ℝ) (x : ℝ≥0) : ℝ :=
  sSup {y : ℝ | ∃ d : ℝ≥0, d ≤ x ∧ y = φ (x - d) + (d : ℝ)}

/-- The one-period dividend-and-issuance operator `T = D ∘ L`. -/
noncomputable def Top {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (𝔽 : Filtration ℝ mΩ) (C : ℝ → Ω → ℝ) (p : Params)
    (φ : ℝ≥0 → ℝ) : ℝ≥0 → ℝ :=
  Dop (fun x => (Lop P 𝔽 C p φ x).toReal)

/-- The arbitrary-maturity objective of §3.3, with non-strict survival. -/
noncomputable def Jt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : ℝ → Ω → ℝ) (p : Params) (φ : ℝ≥0 → ℝ)
    (t : ℝ) (x : ℝ≥0) (I : Issuance Ω) : EReal :=
  (terminalReward P C p φ x I t false : EReal) - (costBefore P p I t : EReal)

/-- The control-defined arbitrary-maturity one-period value. -/
noncomputable def vOneExtended {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (𝔽 : Filtration ℝ mΩ) (C : ℝ → Ω → ℝ) (p : Params)
    (φ : ℝ≥0 → ℝ) (t : ℝ) (x : ℝ≥0) : EReal :=
  sSup {y : EReal | ∃ I : Issuance Ω,
    Admissible 𝔽 C p x (noDividends Ω) I ∧ y = Jt P C p φ t x I}

/-- Real value of the arbitrary-maturity problem, used where finiteness is asserted. -/
noncomputable def vOne {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (𝔽 : Filtration ℝ mΩ) (C : ℝ → Ω → ℝ) (p : Params)
    (φ : ℝ≥0 → ℝ) (t : ℝ) (x : ℝ≥0) : ℝ :=
  (vOneExtended P 𝔽 C p φ t x).toReal

/-- The class C_A^T from Definition 3.5, restricted to the closed time-state rectangle. -/
def CTA (p : Params) (A : ℝ) (u : ℝ → ℝ≥0 → ℝ) : Prop :=
  (∀ t ∈ Icc (0 : ℝ) p.T, Monotone
    (fun x : ℝ≥0 => u t x - Real.exp (-p.rho * t) * (x : ℝ))) ∧
  (∀ t ∈ Icc (0 : ℝ) p.T, ∀ x : ℝ≥0,
    Real.exp (-p.rho * t) * (x : ℝ) ≤ u t x ∧
    u t x ≤ Real.exp (-p.rho * t) * ((x : ℝ) + A + p.mu * t))

/-- The open time-state rectangle Q. -/
def Q (p : Params) : Set (ℝ × ℝ) :=
  Ioo (0 : ℝ) p.T ×ˢ Ioi (0 : ℝ)

/-- The closed time-state rectangle Q̄. -/
def Qbar (p : Params) : Set (ℝ × ℝ) :=
  Icc (0 : ℝ) p.T ×ˢ Ici (0 : ℝ)

/-- The parabolic equation (3.4), in time-to-maturity coordinates. -/
def SolvesPDE (p : Params) (u : ℝ → ℝ → ℝ) : Prop :=
  ∀ q ∈ Q p, p.rho * u q.1 q.2 +
    deriv (fun t => u t q.2) q.1 - p.mu * deriv (u q.1) q.2 -
    (p.sigma ^ 2 / 2) * deriv (deriv (u q.1)) q.2 = 0

/-- A modulus of continuity, with “increasing” read as monotone. -/
def IsModulus (m : ℝ≥0 → ℝ≥0) : Prop :=
  Monotone m ∧ m 0 = 0 ∧ ContinuousAt m 0

end PeriodicDividend.FixedPoint


