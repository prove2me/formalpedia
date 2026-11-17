-- Prove2me | Definitions.Def_TwoStageRnQ_Model
-- name    : TwoStageRnQ_Model
-- status  : Definition
-- author  : @beatlesmania
-- created : 2026-11-17T00:20:06.835144+00:00
-- url     : https://prove2.me/theorems/ed1e573b-d775-4778-bee9-734761245aba
-- title:
--   Stochastic two-stage serial system and classical $(R,nQ)$ rules
-- statement:
--   This file defines the stochastic two-stage serial system, its admissible policies and the classical $(R,nQ)$ rule (Section 3, Appendix A).
--
--   1. **Demand environment.** A probability space with an information filtration $(\mathcal F_t)_{t\in\mathbb R}$ and an integer, nondecreasing, right-continuous, adapted demand count $N$; for $s\le t$, $N(t)-N(s)$ is Poisson with mean $\lambda(t-s)$, and it is independent of $\mathcal F_s$ whenever $0\le s\le t$. Before time $0$, $N$ is the compatible history of the paper (Appendix A.2): a two-sided Poisson counter plus an arbitrary initial count. A model is a two-sided Poisson process with an independent integer initial count and its natural filtration.
--   2. **Shipment policy.** Initial constants $x_1,x_2$ and integer cumulative dispatch processes $U_1,U_2$, adapted, nondecreasing and right-continuous, satisfying the material restriction $x_1+U_1(t)\le x_2+U_2(t-L_2)$ for $t\ge0$. The states are $\mathit{IP}_i(t)=x_i+U_i(t)-N(t)$ and $\mathit{IL}_i(t)=x_i+U_i(t-L_i)-N(t)$ (eq. (A.2)), with $I_1=\mathit{IL}_1^+$, $\mathsf B=\mathit{IL}_1^-$, $I_2=\mathit{IL}_2+\mathsf B$ and $c_I=h_1I_1+h_2I_2+p\mathsf B$.
--   3. **Costs.** For a setup-charge count $Z(T)$, the long-run cost is $\limsup_{T\to\infty}T^{-1}\mathbb E\big[\int_0^Tc_I\,dt+Z(T)\big]$ in $[0,\infty]$ (eq. (4)). Shipment accounting charges $K_i$ per jump of $U_i$ in $(0,T]$; a fixed-lot policy with lot sizes $(q_1,q_2)$ has every increment of $U_i$ divisible by $q_i$ and pays $K_i(U_i(T)-U_i(0))/q_i$.
--   4. **Admissibility** (Appendix A.1): finite first moments of the initial levels and pipelines, finite expected cost on finite horizons, the flow and stability conditions (eqs. (A.3)–(A.5)), and the unfinished-path condition: the chronological inventory-position path (unit demand decreases recorded before coincident dispatch increases), after chronological loop erasure, keeps $o(T)$ downward transitions in expectation.
--   5. **Benchmarks.** $\mathrm{OPT}^{\mathrm{sh}}$ and $\mathrm{OPT}^{\mathrm{lot}}$ are the infima of these costs over admissible shipment, respectively fixed-lot, policies on all demand environments.
--   6. **Classical rule.** Controls $R_1,R_2\in\mathbb Z$, $Q,n\ge1$ and an initial upstream remainder $0\le\rho<Q$; with $s=R_1+Q$ and $\ell=R_2-R_1$, the counters $A=\lfloor N/Q\rfloor$, $O=\lfloor(N+\ell-\rho+(n-1)Q)/(nQ)\rfloor$, $\mathsf S(t)=nO(t-L_2)$, $M=\min\{A,\mathsf S\}$ give $U_1=QM$, $U_2=nQO$, $x_1=s$, $x_2=s+\rho$ (eqs. (A.6)–(A.8), Lemma A.2). Its lot-accounted cost charges $K_1(M(T)-M(0))+K_2(O(T)-O(0))$; its shipment-accounted cost charges $K_i$ per jump of $U_i$.
--
--   **Formalization Note** Expectations of costs are lower Lebesgue integrals in $[0,\infty]$, so no integrability side condition is hidden. The classical rule is evaluated on a given demand environment, whose initial count $N(0)$ is arbitrary; Appendix A.3 shows that every compatible initialization coincides with such a counter construction after a finite transient. The residue of $N$ modulo $nQ$ is uniform only in the limit, as in the paper's Lemma A.1, unless the initial count is randomized.
-- source:
--   M. Hu, "A 5/3 Guarantee for Echelon Stock (R,nQ) Policies in Two-Stage Stochastic Serial Systems", manuscript rq_167.tex (Sept. 28, 2026 version); posted as arXiv:2609.06318. Section 3; Appendix A.1-A.3 (eqs. (A.2)-(A.8)).

import Definitions.Def_TwoStageRnQ_Analytic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.Finset.Sort

/-!
# Echelon stock `(R,nQ)` policies: the stochastic serial system

Operational model of M. Hu, "A 5/3 Guarantee for Echelon Stock (R,nQ) Policies in Two-Stage
Stochastic Serial Systems" (manuscript `rq_167.tex`), Section 3 and Appendix A:
Poisson demand with an information filtration, admissible shipment policies, fixed-lot
policies, the classical counter construction of the `(R,nQ)` rule, the long-run cost rates
under shipment and lot accounting, and the benchmarks `OPT^sh`, `OPT^lot`.

Demand after time `0` is Poisson and independent of everything a policy may know; values of
`N` before time `0` record a compatible history, the signed counter of a two-sided Poisson
process plus an arbitrary initial count (Appendix A.2). Accordingly, increments are Poisson on
every interval and independent of the information at `s` for `0 ≤ s ≤ t`.

A model: on a probability space carrying a two-sided Poisson process of rate `λ` and an
independent integer `N₀`, let `N t = N₀ + ` (signed number of arrivals in `(0, t]`) and let `𝓕` be
the natural filtration of `N`. For `s ≥ 0`, `𝓕 s` is generated by `N₀` and the arrivals in
`(-∞, s]`, which are independent of the arrivals in `(s, t]`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace TwoStageRnQ

/-- The demand environment (Section 3.1, Appendices A.1-A.2): a probability space with an
information filtration and an integer, nondecreasing, right-continuous, adapted demand count `N`.
Every increment `N t - N s` (`s ≤ t`) is Poisson with mean `λ (t - s)`, so the values before time
`0` form a compatible two-sided Poisson history with an arbitrary initial count. Increments after
a nonnegative time `s` are independent of the information at `s`, which carries everything a
policy may use (demand history and independent private randomization). -/
structure DemandSpace (P : Params) where
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  ν : Measure Ω
  [prob : IsProbabilityMeasure ν]
  𝓕 : Filtration ℝ mΩ
  N : ℝ → Ω → ℤ
  N_adapted : ∀ t, Measurable[𝓕 t] (N t)
  N_mono : ∀ ω, Monotone (fun t => N t ω)
  N_rcont : ∀ ω t, ∃ δ > 0, ∀ s, t ≤ s → s < t + δ → N s ω = N t ω
  N_law : ∀ s t, s ≤ t → ∀ k : ℕ,
    ν {ω | N t ω - N s ω = (k : ℤ)} = ENNReal.ofReal (poisW (P.lam * (t - s)) k)
  N_indep : ∀ s t, 0 ≤ s → s ≤ t →
    Indep (MeasurableSpace.comap (fun ω => N t ω - N s ω) inferInstance) (𝓕 s) ν

attribute [instance] DemandSpace.mΩ DemandSpace.prob

/-- A shipment policy (Appendix A.1): integer initial constants `x₁, x₂` and cumulative
dispatch processes `U₁` (dispatches into echelon 1, i.e. Stage-2 to Stage-1 shipments) and `U₂`
(supplier orders into echelon 2). Values at negative times encode the initial pipelines. The
processes are adapted, nondecreasing and right-continuous (so integer valued with finitely many
dispatches on bounded intervals), and satisfy the material restriction
`IP₁(t) ≤ IL₂(t)`, i.e. `x₁ + U₁(t) ≤ x₂ + U₂(t - L₂)`, for `t ≥ 0`. -/
structure ShipmentPolicy (P : Params) (S : DemandSpace P) where
  x1 : S.Ω → ℤ
  x2 : S.Ω → ℤ
  U1 : ℝ → S.Ω → ℤ
  U2 : ℝ → S.Ω → ℤ
  x1_meas : Measurable[S.𝓕 0] x1
  x2_meas : Measurable[S.𝓕 0] x2
  U1_adapted : ∀ t, Measurable[S.𝓕 t] (U1 t)
  U2_adapted : ∀ t, Measurable[S.𝓕 t] (U2 t)
  U1_mono : ∀ ω, Monotone (fun t => U1 t ω)
  U2_mono : ∀ ω, Monotone (fun t => U2 t ω)
  U1_rcont : ∀ ω t, ∃ δ > 0, ∀ s, t ≤ s → s < t + δ → U1 s ω = U1 t ω
  U2_rcont : ∀ ω t, ∃ δ > 0, ∀ s, t ≤ s → s < t + δ → U2 s ω = U2 t ω
  material : ∀ ω t, 0 ≤ t → x1 ω + U1 t ω ≤ x2 ω + U2 (t - P.L2) ω

section Raw

variable {Ω : Type}

/-- Echelon inventory position `IP(t) = x + U(t) - N(t)` (eq. (A.2)). -/
def invPos (x : Ω → ℤ) (U N : ℝ → Ω → ℤ) (t : ℝ) (ω : Ω) : ℤ := x ω + U t ω - N t ω

/-- Net echelon inventory `IL(t) = x + U(t - L) - N(t)` (eq. (A.2)). -/
def netInv (L : ℝ) (x : Ω → ℤ) (U N : ℝ → Ω → ℤ) (t : ℝ) (ω : Ω) : ℤ := x ω + U (t - L) ω - N t ω

/-- Inventory and backlog cost rate `c_I = h₁ I₁ + h₂ I₂ + p 𝖡` with `I₁ = IL₁⁺`, `𝖡 = IL₁⁻`,
`I₂ = IL₂ + 𝖡` (eqs. (3), (A.2)). -/
def costRate (P : Params) (x1 x2 : Ω → ℤ) (U1 U2 N : ℝ → Ω → ℤ) (t : ℝ) (ω : Ω) : ℝ :=
  P.h1 * max (netInv P.L1 x1 U1 N t ω : ℝ) 0
    + P.h2 * ((netInv P.L2 x2 U2 N t ω : ℝ) + max (-(netInv P.L1 x1 U1 N t ω : ℝ)) 0)
    + P.p * max (-(netInv P.L1 x1 U1 N t ω : ℝ)) 0

/-- Number of positive dispatches (jump times) of a nondecreasing integer path in `(0, T]`. -/
def jumpCount (f : ℝ → ℤ) (T : ℝ) : ℕ := Set.ncard {t | t ∈ Set.Ioc 0 T ∧ ∀ s < t, f s < f t}

/-- Long-run expected cost rate (eq. (4)): `limsup_{T→∞} T⁻¹ 𝔼[∫₀ᵀ c_I(t) dt + Z(T)]`, where
`Z(T)` is the total setup charge incurred up to `T`. -/
def longRunCost [MeasurableSpace Ω] (ν : Measure Ω) (cI : ℝ → Ω → ℝ) (Z : ℝ → Ω → ℝ) : ℝ≥0∞ :=
  limsup (fun T : ℝ => ENNReal.ofReal T⁻¹ *
    ∫⁻ ω, ((∫⁻ t in Set.Ioc 0 T, ENNReal.ofReal (cI t ω)) + ENNReal.ofReal (Z T ω)) ∂ν) atTop

/-- The left limit `f(t-)` of a nondecreasing integer path. -/
def leftVal (f : ℝ → ℤ) (t : ℝ) : ℤ := sSup (f '' Set.Iio t)

open Classical in
/-- The chronological inventory-position path on `[0, T]` (Appendix A.1): starting from
`IP(0)`, at each event epoch in `(0, T]` (in increasing order) every unit demand is recorded as a
unit decrease, before any coincident dispatch increase. -/
def chronPath (x : ℤ) (U N : ℝ → ℤ) (T : ℝ) : List ℤ :=
  let E : Set ℝ := {t | t ∈ Set.Ioc 0 T ∧ (leftVal N t < N t ∨ leftVal U t < U t)}
  if hE : E.Finite then
    ((hE.toFinset.sort (· ≤ ·)).foldl
      (fun (acc : List ℤ × ℤ) t =>
        let dn : ℕ := (N t - leftVal N t).toNat
        let du : ℤ := U t - leftVal U t
        let downs : List ℤ := (List.range dn).map (fun k => acc.2 - ((k : ℤ) + 1))
        let s1 : ℤ := acc.2 - (dn : ℤ)
        if 0 < du then (acc.1 ++ downs ++ [s1 + du], s1 + du) else (acc.1 ++ downs, s1))
      ([x + U 0 - N 0], x + U 0 - N 0)).1
  else []

/-- One step of chronological loop erasure: a return to a state already in the retained path
removes the segment from that earlier visit through the return, keeping the state once. -/
def loopEraseStep (R : List ℤ) (s : ℤ) : List ℤ :=
  if s ∈ R then R.takeWhile (· ≠ s) ++ [s] else R ++ [s]

/-- Chronological loop erasure of a path. -/
def loopErase (path : List ℤ) : List ℤ := path.foldl loopEraseStep []

/-- Number of downward (unit demand) transitions in a path. -/
def downCount : List ℤ → ℕ
  | a :: b :: t => (if b = a - 1 then 1 else 0) + downCount (b :: t)
  | _ => 0

/-- `r_T`: downward demand transitions remaining after loop erasure through time `T`. -/
def unfinishedCount (x : ℤ) (U N : ℝ → ℤ) (T : ℝ) : ℕ := downCount (loopErase (chronPath x U N T))

end Raw

namespace ShipmentPolicy

variable {P : Params} {S : DemandSpace P} (π : ShipmentPolicy P S)

/-- Inventory and backlog cost rate of the policy. -/
def cI (t : ℝ) (ω : S.Ω) : ℝ := costRate P π.x1 π.x2 π.U1 π.U2 S.N t ω

/-- Cumulative customer deliveries `U₀(t) = N(t) - 𝖡(t)`, so that `U₀(T) - U₀(0)` counts the
deliveries in `(0, T]`. -/
def U0 (t : ℝ) (ω : S.Ω) : ℤ := S.N t ω - max (-(netInv P.L1 π.x1 π.U1 S.N t ω)) 0

/-- Shipment-accounted setup charges up to `T`: `K₁ Z₁^sh(T) + K₂ Z₂^sh(T)`. -/
def shipSetup (T : ℝ) (ω : S.Ω) : ℝ :=
  P.K1 * (jumpCount (fun t => π.U1 t ω) T : ℝ) + P.K2 * (jumpCount (fun t => π.U2 t ω) T : ℝ)

/-- Shipment-accounted long-run cost `C^sh(Π)` (eq. (4)). -/
def shipCost : ℝ≥0∞ := longRunCost S.ν π.cI π.shipSetup

/-- A fixed-lot policy with lot sizes `q = (q₁, q₂)`: every dispatch consists of complete lots. -/
def IsFixedLot (q : ℕ+ × ℕ+) : Prop :=
  ∀ ω s t, s ≤ t → ((q.1 : ℕ) : ℤ) ∣ (π.U1 t ω - π.U1 s ω) ∧ ((q.2 : ℕ) : ℤ) ∣ (π.U2 t ω - π.U2 s ω)

/-- Lot-accounted setup charges up to `T`: every lot pays its stage's setup charge. -/
def lotSetup (q : ℕ+ × ℕ+) (T : ℝ) (ω : S.Ω) : ℝ :=
  P.K1 * (((π.U1 T ω - π.U1 0 ω : ℤ) : ℝ) / ((q.1 : ℕ) : ℝ))
    + P.K2 * (((π.U2 T ω - π.U2 0 ω : ℤ) : ℝ) / ((q.2 : ℕ) : ℝ))

/-- Lot-accounted long-run cost `C^lot(Π)`. -/
def lotCost (q : ℕ+ × ℕ+) : ℝ≥0∞ := longRunCost S.ν π.cI (π.lotSetup q)

/-- Admissibility (Section 3.1, Appendix A.1) relative to a setup-charge accounting `Z`:
finite first moments of the initial levels and pipelines, finite expected costs on finite
horizons, the long-run flow and stability conditions (A.3)–(A.5), and the unfinished-path
condition `𝔼 r_{i,T} = o(T)`. -/
structure Admissible (Z : ℝ → S.Ω → ℝ) : Prop where
  init_moments : ∫⁻ ω, ENNReal.ofReal
      (|(netInv P.L1 π.x1 π.U1 S.N 0 ω : ℝ)| + |(netInv P.L2 π.x2 π.U2 S.N 0 ω : ℝ)|
        + ((π.U1 0 ω - π.U1 (-P.L1) ω : ℤ) : ℝ) + ((π.U2 0 ω - π.U2 (-P.L2) ω : ℤ) : ℝ)) ∂S.ν < ⊤
  finite_horizon : ∀ T : ℝ, 0 ≤ T →
    ∫⁻ ω, ((∫⁻ t in Set.Ioc 0 T, ENNReal.ofReal (π.cI t ω)) + ENNReal.ofReal (Z T ω)) ∂S.ν < ⊤
  rate_deliveries : Tendsto (fun T : ℝ => ENNReal.ofReal T⁻¹ *
      ∫⁻ ω, ENNReal.ofReal ((π.U0 T ω - π.U0 0 ω : ℤ) : ℝ) ∂S.ν) atTop (nhds (ENNReal.ofReal P.lam))
  rate_U1 : Tendsto (fun T : ℝ => ENNReal.ofReal T⁻¹ *
      ∫⁻ ω, ENNReal.ofReal ((π.U1 T ω - π.U1 0 ω : ℤ) : ℝ) ∂S.ν) atTop (nhds (ENNReal.ofReal P.lam))
  rate_U2 : Tendsto (fun T : ℝ => ENNReal.ofReal T⁻¹ *
      ∫⁻ ω, ENNReal.ofReal ((π.U2 T ω - π.U2 0 ω : ℤ) : ℝ) ∂S.ν) atTop (nhds (ENNReal.ofReal P.lam))
  terminal_1 : Tendsto (fun T : ℝ => ENNReal.ofReal T⁻¹ *
      ∫⁻ ω, ENNReal.ofReal (|(netInv P.L1 π.x1 π.U1 S.N T ω : ℝ)|
        + ((π.U1 T ω - π.U1 (T - P.L1) ω : ℤ) : ℝ)) ∂S.ν) atTop (nhds 0)
  terminal_2 : Tendsto (fun T : ℝ => ENNReal.ofReal T⁻¹ *
      ∫⁻ ω, ENNReal.ofReal (|(netInv P.L2 π.x2 π.U2 S.N T ω : ℝ)|
        + ((π.U2 T ω - π.U2 (T - P.L2) ω : ℤ) : ℝ)) ∂S.ν) atTop (nhds 0)
  window_cost : Tendsto (fun T : ℝ => ENNReal.ofReal T⁻¹ *
      ∫⁻ ω, (∫⁻ t in Set.Ioc T (T + (P.L1 + P.L2)), ENNReal.ofReal (π.cI t ω)) ∂S.ν)
      atTop (nhds 0)
  window_U1 : Tendsto (fun T : ℝ => ENNReal.ofReal T⁻¹ *
      ∫⁻ ω, ENNReal.ofReal ((π.U1 (T + (P.L1 + P.L2)) ω - π.U1 T ω : ℤ) : ℝ) ∂S.ν)
      atTop (nhds 0)
  window_U2 : Tendsto (fun T : ℝ => ENNReal.ofReal T⁻¹ *
      ∫⁻ ω, ENNReal.ofReal ((π.U2 (T + (P.L1 + P.L2)) ω - π.U2 T ω : ℤ) : ℝ) ∂S.ν)
      atTop (nhds 0)
  unfinished_1 : Tendsto (fun T : ℝ => ENNReal.ofReal T⁻¹ *
      ∫⁻ ω, (unfinishedCount (π.x1 ω) (fun t => π.U1 t ω) (fun t => S.N t ω) T : ℝ≥0∞) ∂S.ν)
      atTop (nhds 0)
  unfinished_2 : Tendsto (fun T : ℝ => ENNReal.ofReal T⁻¹ *
      ∫⁻ ω, (unfinishedCount (π.x2 ω) (fun t => π.U2 t ω) (fun t => S.N t ω) T : ℝ≥0∞) ∂S.ν)
      atTop (nhds 0)

end ShipmentPolicy

/-- `OPT^sh`: infimum of the shipment-accounted long-run cost over all admissible shipment
policies, on every demand environment of the instance (Section 3.2). -/
def OPTsh (P : Params) : ℝ≥0∞ :=
  ⨅ (S : DemandSpace P) (π : ShipmentPolicy P S) (_ : π.Admissible π.shipSetup), π.shipCost

/-- `OPT^lot`: infimum of the lot-accounted long-run cost over all admissible fixed-lot policies
(Section 3.2). -/
def OPTlot (P : Params) : ℝ≥0∞ :=
  ⨅ (S : DemandSpace P) (π : ShipmentPolicy P S) (q : ℕ+ × ℕ+) (_ : π.IsFixedLot q)
    (_ : π.Admissible (π.lotSetup q)), π.lotCost q

/-- Controls of a classical rule: reorder points `R₁, R₂`, downstream lot `Q`, multiplier `n`,
and an initial remainder `ρ ∈ {0,…,Q-1}` of physical upstream stock (Appendix A.3). -/
def ClassicalControls : Type := {c : ℤ × ℤ × ℕ+ × ℕ+ × ℕ // c.2.2.2.2 < (c.2.2.1 : ℕ)}

namespace Classical'

variable {P : Params} (S : DemandSpace P) (c : ClassicalControls)

/-- Downstream request counter `A(t) = ⌊N(t)/Q⌋` (eq. (A.6)). -/
def reqCount (t : ℝ) (ω : S.Ω) : ℤ := ⌊((S.N t ω : ℤ) : ℝ) / ((c.1.2.2.1 : ℕ) : ℝ)⌋

/-- Upstream order counter `O(t) = ⌊(N(t) + ℓ - ρ + (n-1)Q)/(nQ)⌋` with `ℓ = R₂ - R₁`
(eq. (A.6) and Appendix A.3). -/
def ordCount (t : ℝ) (ω : S.Ω) : ℤ :=
  ⌊(((S.N t ω : ℤ) : ℝ) + ((c.1.2.1 - c.1.1 : ℤ) : ℝ) - (c.1.2.2.2.2 : ℝ)
      + (((c.1.2.2.2.1 : ℕ) : ℝ) - 1) * ((c.1.2.2.1 : ℕ) : ℝ))
    / (((c.1.2.2.2.1 : ℕ) : ℝ) * ((c.1.2.2.1 : ℕ) : ℝ))⌋

/-- Received sublots `𝖲(t) = n O(t - L₂)` (eq. (A.6)). -/
def recvCount (t : ℝ) (ω : S.Ω) : ℤ := ((c.1.2.2.2.1 : ℕ) : ℤ) * ordCount S c (t - P.L2) ω

/-- Matched sublots `M(t) = min{A(t), 𝖲(t)}` (eq. (A.6)). -/
def matchCount (t : ℝ) (ω : S.Ω) : ℤ := min (reqCount S c t ω) (recvCount S c t ω)

/-- Downstream endpoint `s = R₁ + Q` (initial constant of echelon 1). -/
def x1 (_ : S.Ω) : ℤ := c.1.1 + ((c.1.2.2.1 : ℕ) : ℤ)

/-- Initial constant of echelon 2, `s + ρ`. -/
def x2 (_ : S.Ω) : ℤ := c.1.1 + ((c.1.2.2.1 : ℕ) : ℤ) + (c.1.2.2.2.2 : ℤ)

/-- Downstream dispatches `U₁ = Q M`. -/
def U1 (t : ℝ) (ω : S.Ω) : ℤ := ((c.1.2.2.1 : ℕ) : ℤ) * matchCount S c t ω

/-- Supplier dispatches `U₂ = nQ O`. -/
def U2 (t : ℝ) (ω : S.Ω) : ℤ :=
  ((c.1.2.2.2.1 : ℕ) : ℤ) * ((c.1.2.2.1 : ℕ) : ℤ) * ordCount S c t ω

/-- Inventory and backlog cost rate of the classical rule (eq. (A.8)). -/
def cI (t : ℝ) (ω : S.Ω) : ℝ := costRate P (x1 S c) (x2 S c) (U1 S c) (U2 S c) S.N t ω

end Classical'

/-- Lot-accounted long-run cost `C^lot` of the classical rule with controls `c`: each matched
downstream lot pays `K₁`, each upstream lot pays `K₂`. -/
def classicalLotCost (P : Params) (S : DemandSpace P) (c : ClassicalControls) : ℝ≥0∞ :=
  longRunCost S.ν (Classical'.cI S c) (fun T ω =>
    P.K1 * ((Classical'.matchCount S c T ω - Classical'.matchCount S c 0 ω : ℤ) : ℝ)
      + P.K2 * ((Classical'.ordCount S c T ω - Classical'.ordCount S c 0 ω : ℤ) : ℝ))

/-- Shipment-accounted long-run cost `C^sh` of the classical rule with controls `c`. -/
def classicalShipCost (P : Params) (S : DemandSpace P) (c : ClassicalControls) : ℝ≥0∞ :=
  longRunCost S.ν (Classical'.cI S c) (fun T ω =>
    P.K1 * (jumpCount (fun t => Classical'.U1 S c t ω) T : ℝ)
      + P.K2 * (jumpCount (fun t => Classical'.U2 S c t ω) T : ℝ))

end TwoStageRnQ


