-- Prove2me | Definitions.Def_ImpatientMatching_Supplement_PatientModel
-- name    : ImpatientMatching_Supplement_PatientModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:30:28.412911+00:00
-- url     : https://prove2.me/theorems/d1d1d9a7-b6da-49b2-92a6-5f7fc46709ab
-- title:
--   General weighted matching with infinite patience, the flow optimum $F^*$, and the per-edge routing policy
-- statement:
--   A **patient matching input** consists of finite supplier and customer type sets, a bipartite compatibility graph $E_G$, positive rational Poisson arrival rates $\lambda_i$ and $\gamma_j$, nonnegative rational edge rewards $w_{ij}$, and one of three explicitly designated patience categories at each type: infinite patience, positive finite exponential patience, or immediate departure. Compatibility is separate from reward, so a compatible edge may have reward zero. A genuinely infinitely patient agent never abandons.
--
--   An **admissible policy** is nonanticipating, matches only present compatible pairs, never matches an agent twice, and makes matches only at an arrival or a genuine finite-patience abandonment event. With $W^\pi(T)$ the accumulated nonnegative reward,
--
--   $$
--   r^\pi(T)=\frac{\mathbb E W^\pi(T)}{T},\qquad
--   g^\pi=\liminf_{T\to\infty}r^\pi(T),\qquad
--   g^*=\sup_\pi g^\pi.
--   $$
--
--   The weighted-flow optimum is
--
--   $$
--   F^*=\max\left\{\sum_{(i,j)\in E_G}w_{ij}f_{ij}:
--   f_{ij}\ge0,\ \sum_j f_{ij}\le\lambda_i,\ \sum_i f_{ij}\le\gamma_j\right\}.
--   $$
--
--   A finite policy description contains a rational optimal flow and, for each positive-flow edge, a choice of an infinitely patient storage endpoint. Supplier arrivals route independently to edge $(i,j)$ with probability $f_{ij}/\lambda_i$, customer arrivals with probability $f_{ij}/\gamma_j$, and each edge keeps its own FIFO inventory. An arrival routed to the other endpoint matches the head of that edge's inventory when it is nonempty.
--
--   This layer supplies the exact objects used by Theorem 3.1.
--
--   **Formalization Note** Supplier and customer types are the separate blocks `Fin nS` and `Fin nC`. The published independent marked-Poisson seed layer and generic stopping-time policy representation are reused. Infinite departure times, accumulated rewards, expectations and long-run values use $[0,\infty]$, preventing a nonintegrable expectation or infinite patience from silently becoming zero or a finite duration. The real flow program defines $F^*$; its policy description records the rational optimum whose existence for rational LP data is asserted by Theorem 3.1. Running time uses the published Cook-machine notion on binary strings. The observation filtration also exposes the later virtual departure of an already matched finite-patience agent; this time is independent of the future and acts only as additional private randomization.
-- source:
--   C. Yan and S. M. Varma, Impatience Makes Matching NP-Hard, manuscript (sha256 7b1051b6c661435675185b0663cb08ab217698a2c4ee07fa0f473686dbb6bed9), §2.1–§2.2, pp.6–8; display (2) and Theorem 3.1, p.8; Appendix A, pp.24–25

import Definitions.Def_CookPvsNP_defs
import Definitions.Def_DynStochMatching_Reward_Policies
import Definitions.Def_ImpatientMatching_Input

open MeasureTheory Filter
open scoped ENNReal Classical
open DynStochMatching.Reward

namespace ImpatientMatching.Supplement

/-- The three patience categories of Yan–Varma, manuscript (sha256 7b1051b6…), §2.1,
pp.6–7: no abandonment, positive finite exponential abandonment, and immediate departure.

**Formalization Note.** A finite positive rate is rational because every finite rate is part of the
binary-encoded input. `infinite` is a genuine non-abandoning case, not exponential rate zero. -/
inductive PatientLifetime where
  | infinite
  | exponential (rate : ℚ) (positive : 0 < rate)
  | immediate
  deriving DecidableEq

/-- The sojourn duration attached to a patience category. Infinite patience is represented by `⊤`
in `ℝ≥0∞`, so it cannot silently become a large finite duration. -/
noncomputable def patientLifetimeDuration (l : PatientLifetime) (seed : ℝ) : ℝ≥0∞ :=
  match l with
  | .infinite => ⊤
  | .exponential rate _ => ENNReal.ofReal (seed / (rate : ℝ))
  | .immediate => 0

/-- The general rational weighted bipartite matching input of §2.1, pp.6–7.

Compatibility is separate from reward, so a compatible zero-reward edge remains representable.
The source's finite supplier and customer type sets are encoded as `Fin nS` and `Fin nC`. -/
structure PatientInput where
  nS : ℕ
  nC : ℕ
  edge : Fin nS → Fin nC → Bool
  rateS : Fin nS → ℚ
  rateC : Fin nC → ℚ
  posS : ∀ i, 0 < rateS i
  posC : ∀ j, 0 < rateC j
  reward : Fin nS → Fin nC → ℚ
  reward_nonneg : ∀ i j, 0 ≤ reward i j
  lifetimeS : Fin nS → PatientLifetime
  lifetimeC : Fin nC → PatientLifetime

/-- The published marked-Poisson arrival layer associated with a patient matching input. -/
noncomputable def PatientInput.toMarkedPoissonData (I : PatientInput) :
    MarkedPoissonData (I.nS + I.nC) where
  arrivalRate := Fin.addCases (fun i => (I.rateS i : ℝ)) (fun j => (I.rateC j : ℝ))
  positive := by
    refine Fin.addCases (fun i => ?_) (fun j => ?_)
    · simp only [Fin.addCases_left]
      exact_mod_cast I.posS i
    · simp only [Fin.addCases_right]
      exact_mod_cast I.posC j

/-- The patience category of a flat supplier-or-customer type. -/
def PatientInput.lifetime (I : PatientInput) : Fin (I.nS + I.nC) → PatientLifetime :=
  Fin.addCases I.lifetimeS I.lifetimeC

/-- The bipartite compatibility relation on flat type indices. -/
def PatientInput.compat (I : PatientInput) :
    Fin (I.nS + I.nC) → Fin (I.nS + I.nC) → Bool :=
  Fin.addCases
    (fun i => Fin.addCases (fun _ => false) (fun j => I.edge i j))
    (fun j => Fin.addCases (fun i => I.edge i j) (fun _ => false))

/-- The nonnegative reward on a flat compatible pair; same-side and incompatible pairs have reward
zero. Keeping `compat` separate means that zero reward does not erase an edge. -/
def PatientInput.flatReward (I : PatientInput) :
    Fin (I.nS + I.nC) → Fin (I.nS + I.nC) → ℚ :=
  Fin.addCases
    (fun i => Fin.addCases (fun _ => 0) (fun j => if I.edge i j then I.reward i j else 0))
    (fun j => Fin.addCases (fun i => if I.edge i j then I.reward i j else 0) (fun _ => 0))

/-- The departure time of an agent. It is `⊤` exactly for an infinitely patient agent. -/
noncomputable def patientDepartureTime (I : PatientInput) (omega : RandomSeeds) (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (arrivalTime I.toMarkedPoissonData omega k) +
    match arrivalType I.toMarkedPoissonData omega k with
    | some i => patientLifetimeDuration (I.lifetime i) (omega (k, 2))
    | none => 0

/-- The observable event history at time `t`, together with independent private coins. Unrealized
finite patience durations are hidden; an infinite departure time never appears as an event. -/
noncomputable def patientObservation (I : PatientInput) (t : ℝ) (omega : RandomSeeds) :=
  ((fun k : ℕ => if arrivalTime I.toMarkedPoissonData omega k ≤ t then
      (true, arrivalTime I.toMarkedPoissonData omega k,
        (arrivalType I.toMarkedPoissonData omega k).map Fin.val |>.getD (I.nS + I.nC))
    else (false, (0 : ℝ), I.nS + I.nC)),
   (fun k : ℕ => if patientDepartureTime I omega k ≤ ENNReal.ofReal t then
      (true, patientDepartureTime I omega k) else (false, (0 : ℝ≥0∞))),
   (fun k : ℕ × ℕ => omega (k.1, k.2 + 3)))

@[instance_reducible]
noncomputable def patientObservableSpace (I : PatientInput) (t : ℝ) : MeasurableSpace RandomSeeds :=
  MeasurableSpace.comap (patientObservation I t) inferInstance

/-- Presence at time `t`: infinite patience remains present forever, finite patience is present
strictly before departure, and immediate patience is present only at its arrival event. -/
noncomputable def patientPresent (I : PatientInput) (omega : RandomSeeds)
    (t : ℝ) (k : ℕ) : Prop :=
  0 ≤ t ∧ arrivalTime I.toMarkedPoissonData omega k ≤ t ∧
    ∃ i, arrivalType I.toMarkedPoissonData omega k = some i ∧
      (ENNReal.ofReal t < patientDepartureTime I omega k ∨
        (I.lifetime i = PatientLifetime.immediate ∧
          t = arrivalTime I.toMarkedPoissonData omega k))

/-- Whether two agent identities have compatible endpoint types. -/
noncomputable def patientPairCompatible (I : PatientInput) (omega : RandomSeeds)
    (e : ℕ × ℕ) : Prop :=
  match arrivalType I.toMarkedPoissonData omega e.1,
      arrivalType I.toMarkedPoissonData omega e.2 with
  | some i, some j => I.compat i j = true
  | _, _ => False

/-- Pathwise feasibility: matches use distinct present compatible agents and no agent twice. -/
noncomputable def patientFeasiblePath (I : PatientInput) (pi : MatchingPolicy)
    (omega : RandomSeeds) : Prop :=
  (∀ e, pi e omega ≠ ⊤ → e.1 < e.2 ∧
    patientPresent I omega (pi e omega).toReal e.1 ∧
    patientPresent I omega (pi e omega).toReal e.2 ∧ patientPairCompatible I omega e) ∧
  (∀ e f, pi e omega ≠ ⊤ → pi f omega ≠ ⊤ → sharesAgent e f → e = f)

/-- Nonanticipating feasible matching policies on the patient extension of the published seed space. -/
noncomputable def patientAdmissible (I : PatientInput) (pi : MatchingPolicy) : Prop :=
  (∀ e, Measurable (pi e)) ∧
  (∀ e t, 0 ≤ t → ∃ A : Set RandomSeeds,
    @MeasurableSet RandomSeeds (patientObservableSpace I t) A ∧
      ∀ᵐ omega ∂seedLaw, (omega ∈ A ↔ pi e omega ≤ ENNReal.ofReal t)) ∧
  (∀ᵐ omega ∂seedLaw, patientFeasiblePath I pi omega)

/-- An agent is unmatched immediately before an extended-nonnegative time. -/
noncomputable def patientUnmatchedBefore (pi : MatchingPolicy) (omega : RandomSeeds)
    (k : ℕ) (t : ℝ≥0∞) : Prop :=
  ∀ e, e.1 = k ∨ e.2 = k → pi e omega = ⊤ ∨ t < pi e omega

/-- The real system events of §2.2: an arrival or an unmatched finite-patience abandonment. -/
inductive PatientEvent (n : ℕ) where
  | arrival (i : Fin n)
  | abandon (i : Fin n)

/-- The extended-nonnegative epochs of arrivals and genuine abandonment events. -/
noncomputable def patientRealEventTimes (I : PatientInput) (pi : MatchingPolicy)
    (omega : RandomSeeds) : Set ℝ≥0∞ :=
  {s | (∃ k i, arrivalType I.toMarkedPoissonData omega k = some i ∧
          s = ENNReal.ofReal (arrivalTime I.toMarkedPoissonData omega k)) ∨
       (∃ k i rate hrate,
          arrivalType I.toMarkedPoissonData omega k = some i ∧
          I.lifetime i = PatientLifetime.exponential rate hrate ∧
          s = patientDepartureTime I omega k ∧ patientUnmatchedBefore pi omega k s)}

/-- The paper's policy class (§2.2, p.7): nonanticipating, feasible, compatible, and making matches
only at an arrival or abandonment event. Strategic idling and unbounded inventories are allowed. -/
noncomputable def IsPatientPolicy (I : PatientInput) (pi : MatchingPolicy) : Prop :=
  patientAdmissible I pi ∧ ∀ᵐ omega ∂seedLaw, ∀ e, pi e omega ≠ ⊤ →
    pi e omega ∈ patientRealEventTimes I pi omega

/-- The reward of a matched identity pair as an extended nonnegative real. -/
noncomputable def patientPairReward (I : PatientInput) (omega : RandomSeeds)
    (e : ℕ × ℕ) : ℝ≥0∞ :=
  match arrivalType I.toMarkedPoissonData omega e.1,
      arrivalType I.toMarkedPoissonData omega e.2 with
  | some i, some j => ENNReal.ofReal (I.flatReward i j)
  | _, _ => 0

/-- The nonnegative accumulated reward through horizon `T`. -/
noncomputable def patientAccumulatedReward (I : PatientInput) (pi : MatchingPolicy)
    (T : ℝ) (omega : RandomSeeds) : ℝ≥0∞ :=
  ∑' e : ℕ × ℕ, if e.1 < e.2 ∧ pi e omega ≠ ⊤ ∧ pi e omega ≤ ENNReal.ofReal T then
    patientPairReward I omega e else 0

/-- `E W^pi(T)`, using a lower Lebesgue integral because rewards are nonnegative. -/
noncomputable def patientExpectedReward (I : PatientInput) (pi : MatchingPolicy) (T : ℝ) : ℝ≥0∞ :=
  ∫⁻ omega, patientAccumulatedReward I pi T omega ∂seedLaw

/-- `r^pi(T) = E W^pi(T) / T` from (1), p.7. -/
noncomputable def patientRate (I : PatientInput) (pi : MatchingPolicy) (T : ℝ) : ℝ≥0∞ :=
  patientExpectedReward I pi T / ENNReal.ofReal T

/-- `g^pi = liminf_(T→∞) r^pi(T)` from (1), p.7. -/
noncomputable def patientLongRunReward (I : PatientInput) (pi : MatchingPolicy) : ℝ≥0∞ :=
  Filter.liminf (patientRate I pi) Filter.atTop

/-- `g* = sup_pi g^pi`, over exactly the paper's admissible event-driven policies. -/
noncomputable def patientGStar (I : PatientInput) : ℝ≥0∞ :=
  ⨆ pi : {pi : MatchingPolicy // IsPatientPolicy I pi}, patientLongRunReward I pi.val

/-- A real edge flow for the weighted flow problem (2), p.8. -/
abbrev RealFlow (I : PatientInput) := Fin I.nS → Fin I.nC → ℝ

/-- Feasibility in (2): nonnegative compatible-edge flow and one arrival-capacity constraint at
every supplier and every customer. -/
def FeasibleFlow (I : PatientInput) (f : RealFlow I) : Prop :=
  (∀ i j, 0 ≤ f i j) ∧
  (∀ i j, I.edge i j = false → f i j = 0) ∧
  (∀ i, ∑ j, f i j ≤ (I.rateS i : ℝ)) ∧
  (∀ j, ∑ i, f i j ≤ (I.rateC j : ℝ))

/-- The objective `sum_(i,j) w_ij f_ij` of (2). -/
noncomputable def flowValue (I : PatientInput) (f : RealFlow I) : ℝ :=
  ∑ i, ∑ j, (I.reward i j : ℝ) * f i j

/-- `F*`, the maximum value in (2), represented as the supremum of feasible real flow values. The
zero flow makes the set nonempty, and the vertex capacities bound it. -/
noncomputable def FStar (I : PatientInput) : ℝ :=
  sSup {x : ℝ | ∃ f : RealFlow I, FeasibleFlow I f ∧ x = flowValue I f}

/-- A rational flow, used in the finite binary policy description. -/
abbrev RationalFlow (I : PatientInput) := Fin I.nS → Fin I.nC → ℚ

/-- Coercion of a rational flow into the real flow problem (2). -/
def RationalFlow.toReal {I : PatientInput} (f : RationalFlow I) : RealFlow I :=
  fun i j => (f i j : ℝ)

/-- A rational flow that attains the real LP optimum. Rational LP data admit such an optimum. -/
def IsOptimalRationalFlow (I : PatientInput) (f : RationalFlow I) : Prop :=
  FeasibleFlow I f.toReal ∧ flowValue I f.toReal = FStar I

/-- Which endpoint of an edge stores its independently routed inventory. -/
inductive StorageEndpoint where
  | supplier
  | customer
  deriving DecidableEq

/-- The storage choice is valid on every positive-flow edge: the chosen endpoint is genuinely
infinitely patient. -/
def ValidStorage (I : PatientInput) (f : RationalFlow I)
    (storage : Fin I.nS → Fin I.nC → StorageEndpoint) : Prop :=
  ∀ i j, 0 < f i j →
    (storage i j = .supplier ∧ I.lifetimeS i = .infinite) ∨
    (storage i j = .customer ∧ I.lifetimeC j = .infinite)

/-- The finite rational description of Appendix A's policy: an optimal rational flow and one
patient storage endpoint for every edge. -/
structure PolicyDescription (I : PatientInput) where
  flow : RationalFlow I
  storage : Fin I.nS → Fin I.nC → StorageEndpoint
  optimal : IsOptimalRationalFlow I flow
  validStorage : ValidStorage I flow storage

/-- A self-delimiting binary encoding of the three patience categories. -/
def encPatientLifetime : PatientLifetime → List Bool
  | .infinite => [false, false]
  | .immediate => [false, true]
  | .exponential rate _ => true :: ImpatientMatching.encRat rate

/-- Binary encoding of all rational input data, as required by §1.3 and p.7. -/
def encPatientInput (I : PatientInput) : List Bool :=
  NSWApxHard.Reduction.natBits I.nS ++ NSWApxHard.Reduction.natBits I.nC ++
    (List.ofFn fun i => List.ofFn fun j => I.edge i j).flatten ++
    (List.ofFn fun i => ImpatientMatching.encRat (I.rateS i)).flatten ++
    (List.ofFn fun j => ImpatientMatching.encRat (I.rateC j)).flatten ++
    (List.ofFn fun i => List.ofFn fun j => ImpatientMatching.encRat (I.reward i j)).flatten.flatten ++
    (List.ofFn fun i => encPatientLifetime (I.lifetimeS i)).flatten ++
    (List.ofFn fun j => encPatientLifetime (I.lifetimeC j)).flatten

/-- Binary encoding of the rational flow and the per-edge storage choices. -/
def encPolicyDescription {I : PatientInput} (d : PolicyDescription I) : List Bool :=
  (List.ofFn fun i => List.ofFn fun j => ImpatientMatching.encRat (d.flow i j)).flatten.flatten ++
    (List.ofFn fun i => List.ofFn fun j => decide (d.storage i j = .supplier)).flatten

/-- A routed arrival records its chosen edge and whether it joins that edge's storage inventory. -/
structure RoutedArrival (I : PatientInput) where
  supplier : Fin I.nS
  customer : Fin I.nC
  atStorage : Bool

/-- Appendix A's independent routing choice. A supplier of type `i` chooses `(i,j)` with
probability `f_ij/lambda_i`; a customer of type `j` chooses `(i,j)` with probability
`f_ij/gamma_j`. The published exponential seed transformed by `exp (-seed)` is uniform. -/
noncomputable def routedArrival (I : PatientInput) (d : PolicyDescription I)
    (omega : RandomSeeds) (k : ℕ) : Option (RoutedArrival I) :=
  match arrivalType I.toMarkedPoissonData omega k with
  | none => none
  | some a =>
      Fin.addCases
        (fun i =>
          (categorical I.nC (fun j => (d.flow i j : ℝ) / (I.rateS i : ℝ))
            (Real.exp (-omega (k, 3)))).map fun j =>
              ⟨i, j, d.storage i j = .supplier⟩)
        (fun j =>
          (categorical I.nS (fun i => (d.flow i j : ℝ) / (I.rateC j : ℝ))
            (Real.exp (-omega (k, 3)))).map fun i =>
              ⟨i, j, d.storage i j = .customer⟩)
        a

/-- One FIFO inventory for every edge, even when several edges store the same endpoint type. -/
abbrev EdgeInventories (I : PatientInput) := Fin I.nS → Fin I.nC → List ℕ

/-- Process one globally indexed arrival in the per-edge inventories. -/
noncomputable def inventoryStep (I : PatientInput) (d : PolicyDescription I)
    (omega : RandomSeeds) (k : ℕ) (q : EdgeInventories I) : EdgeInventories I :=
  match routedArrival I d omega k with
  | none => q
  | some a => fun i j =>
      if i = a.supplier ∧ j = a.customer then
        if a.atStorage then q i j ++ [k] else (q i j).drop 1
      else q i j

/-- Inventories immediately before processing arrival identity `k`. -/
noncomputable def edgeInventories (I : PatientInput) (d : PolicyDescription I)
    (omega : RandomSeeds) : ℕ → EdgeInventories I
  | 0 => fun _ _ => []
  | k + 1 => inventoryStep I d omega k (edgeInventories I d omega k)

/-- The stored agent matched by arrival `k`, if `k` is routed to the other endpoint and that
edge's inventory is nonempty. -/
noncomputable def matchedStorageAt (I : PatientInput) (d : PolicyDescription I)
    (omega : RandomSeeds) (k : ℕ) : Option ℕ :=
  match routedArrival I d omega k with
  | some a => if a.atStorage then none else (edgeInventories I d omega k a.supplier a.customer).head?
  | none => none

/-- Appendix A's per-edge storage and routing policy. Each other-endpoint arrival matches the FIFO
head of its selected edge inventory when nonempty, and otherwise is never subsequently matched. -/
noncomputable def storageRoutingPolicy (I : PatientInput) (d : PolicyDescription I) : MatchingPolicy :=
  fun e omega => if e.1 < e.2 ∧ matchedStorageAt I d omega e.2 = some e.1 then
    ENNReal.ofReal (arrivalTime I.toMarkedPoissonData omega e.2) else ⊤

/-- The vertex-cover hypothesis of Theorem 3.1: every compatibility edge has an infinitely patient
endpoint, and the endpoint may vary from edge to edge. -/
def PatientEdgeCover (I : PatientInput) : Prop :=
  ∀ i j, I.edge i j = true →
    I.lifetimeS i = PatientLifetime.infinite ∨ I.lifetimeC j = PatientLifetime.infinite

end ImpatientMatching.Supplement


