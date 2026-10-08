-- Prove2me | Definitions.Def_TwoSidedMatching_Guarantee_Market
-- name    : TwoSidedMatching_Guarantee_Market
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T10:18:16.490993+00:00
-- url     : https://prove2.me/theorems/abde7ab5-d3bb-4e6d-8c8b-be3b4b547fe3
-- title:
--   Fluid program, Poisson arrivals, greedy matching and waiting-adjusted prices
-- statement:
--   The market has independent Poisson buyer and seller counts with means λᵈT and λˢT. Conditional on a count, arrival times are uniform on [0,T], and valuations or costs are independent marks. Buyers request on arrival when v ≥ p* and sellers when c ≤ w*. Greedy first-come-first-served matching pairs the requesting sides in arrival order, with index tie-breaking.
--
--   The fluid benchmark J̄* is the supremum of program (D) over measurable, nonnegative, market-clearing price trajectories with integrable objective terms. The prices p* and w* are the inverse-distribution prices at the greatest volume μ* whose marginal virtual surplus is nonnegative. The clairvoyant benchmark J̄(Hᵀ) maximizes virtual surplus less both waiting penalties over partial matchings.
--
--   For a tagged request at time t, the compensation is expected time in the system divided by match probability. The buyer compensation conditions on nonpositive inventory Iₜ₋; the seller compensation is unconditional. Posted ask and bid are p* − b·compensation and w* + h·compensation. Policy profit is expected posted-price receipts from matched buyers less payments to matched sellers.
--
--   These independent definitions support the performance theorem and its proof milestones.
--
--   **Formalization Note** C.d.f.s are clamped outside their supports. Uniform arrival time law has mass one when T is positive. The tagged-arrival construction is the Poisson add-one representation. A zero match probability gives Lean's zero quotient; for a tagged buyer arriving at T with no waiting seller, this is a null-time convention. Policy profit is defined from actual matched payments, separately from the profit identity. The supremum definitions are used with positive rates, a positive horizon and the support conditions carried by the paper's theorems.
-- source:
--   Chen and Hu, Pricing and Matching with Forward-looking Buyers and Sellers, submitted manuscript (SSRN 2859864, TSpace copy), main text pp. 14–18, (B), (D), (1)–(2), waiting-adjusted FP policy

import Mathlib
import Definitions.Def_AssignmentGame_CoreLP_Game
import Definitions.Def_TwoSidedMatching_Guarantee_Primitives

open MeasureTheory

namespace TwoSidedMatching.Guarantee

noncomputable def Fd (E : Environment) (p : ℝ) : ℝ :=
  E.cdfB (max E.loB (min p E.hiB))

noncomputable def FdBar (E : Environment) (p : ℝ) : ℝ := 1 - Fd E p

noncomputable def Fs (E : Environment) (w : ℝ) : ℝ :=
  E.cdfS (max E.loS (min w E.hiS))

noncomputable def FdBarInv (E : Environment) (q : ℝ) : ℝ :=
  Function.invFunOn (FdBar E) (Set.Icc E.loB E.hiB) q

noncomputable def FsInv (E : Environment) (q : ℝ) : ℝ :=
  Function.invFunOn (Fs E) (Set.Icc E.loS E.hiS) q

noncomputable def V (E : Environment) (lamD lamS T μ : ℝ) : ℝ :=
  E.psiB (FdBarInv E (μ / (lamD * T))) -
    E.psiS (FsInv E (μ / (lamS * T)))

def admissibleVolume (E : Environment) (lamD lamS T : ℝ) : Set ℝ :=
  {μ | μ ∈ Set.Icc 0 (min (lamD * T) (lamS * T)) ∧ 0 ≤ V E lamD lamS T μ}

noncomputable def muStar (E : Environment) (lamD lamS T : ℝ) : ℝ :=
  sSup (admissibleVolume E lamD lamS T)

noncomputable def pStar (E : Environment) (lamD lamS T : ℝ) : ℝ :=
  FdBarInv E (muStar E lamD lamS T / (lamD * T))

noncomputable def wStar (E : Environment) (lamD lamS T : ℝ) : ℝ :=
  FsInv E (muStar E lamD lamS T / (lamS * T))

def IsFeasiblePath (E : Environment) (lamD lamS T : ℝ)
    (π : ℝ → ℝ × ℝ) : Prop :=
  Measurable π ∧
    (∀ t ∈ Set.Icc 0 T, 0 ≤ (π t).1 ∧ 0 ≤ (π t).2 ∧
      lamD * FdBar E (π t).1 = lamS * Fs E (π t).2) ∧
    IntervalIntegrable (fun t => lamD * (π t).1 * FdBar E (π t).1) volume 0 T ∧
    IntervalIntegrable (fun t => lamS * (π t).2 * Fs E (π t).2) volume 0 T

noncomputable def fluidObjective (E : Environment) (lamD lamS T : ℝ)
    (π : ℝ → ℝ × ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..T, lamD * (π t).1 * FdBar E (π t).1) -
    (∫ t in (0 : ℝ)..T, lamS * (π t).2 * Fs E (π t).2)

noncomputable def fluidValue (E : Environment) (lamD lamS T : ℝ) : ℝ :=
  sSup {z : ℝ | ∃ π, IsFeasiblePath E lamD lamS T π ∧
    fluidObjective E lamD lamS T π = z}

abbrev Ω := (ℕ × (ℕ → ℝ × ℝ)) × (ℕ × (ℕ → ℝ × ℝ))

/-- A time mark is uniform on `[0,T]`; its mass is one when `T>0`. -/
noncomputable def timeLaw (T : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (1 / T)) • (volume.restrict (Set.Icc 0 T))

noncomputable def valLaw (E : Environment) : Measure ℝ :=
  (volume.restrict (Set.Icc E.loB E.hiB)).withDensity
    (fun v => ENNReal.ofReal (E.fB v))

noncomputable def costLaw (E : Environment) : Measure ℝ :=
  (volume.restrict (Set.Icc E.loS E.hiS)).withDensity
    (fun c => ENNReal.ofReal (E.fS c))

noncomputable def buyerMark (E : Environment) (T : ℝ) : Measure (ℝ × ℝ) :=
  (timeLaw T).prod (valLaw E)

noncomputable def sellerMark (E : Environment) (T : ℝ) : Measure (ℝ × ℝ) :=
  (timeLaw T).prod (costLaw E)

noncomputable def sideLaw (r T : ℝ) (Q : Measure (ℝ × ℝ)) :
    Measure (ℕ × (ℕ → ℝ × ℝ)) :=
  (ProbabilityTheory.poissonMeasure ⟨max (r * T) 0, le_max_right _ _⟩).prod
    (Measure.infinitePi (fun _ : ℕ => Q))

noncomputable def P (E : Environment) (lamD lamS T : ℝ) : Measure Ω :=
  (sideLaw lamD T (buyerMark E T)).prod
    (sideLaw lamS T (sellerMark E T))

def buyerTime (ω : Ω) (i : Fin ω.1.1) : ℝ := (ω.1.2 i).1
def buyerValue (ω : Ω) (i : Fin ω.1.1) : ℝ := (ω.1.2 i).2
def sellerTime (ω : Ω) (j : Fin ω.2.1) : ℝ := (ω.2.2 j).1
def sellerCost (ω : Ω) (j : Fin ω.2.1) : ℝ := (ω.2.2 j).2

noncomputable def assignmentWeight (E : Environment) (b h : ℝ)
    (ω : Ω) (j : Fin ω.2.1) (i : Fin ω.1.1) : ℝ :=
  E.psiB (buyerValue ω i) - E.psiS (sellerCost ω j) -
    b * max (sellerTime ω j - buyerTime ω i) 0 -
    h * max (buyerTime ω i - sellerTime ω j) 0

noncomputable def Jbar (E : Environment) (b h : ℝ) (ω : Ω) : ℝ :=
  AssignmentGame.CoreLP.worth (assignmentWeight E b h ω) Finset.univ Finset.univ

noncomputable def reqB (E : Environment) (lamD lamS T : ℝ)
    (ω : Ω) : Finset (Fin ω.1.1) :=
  Finset.univ.filter (fun i => pStar E lamD lamS T ≤ buyerValue ω i)

noncomputable def reqS (E : Environment) (lamD lamS T : ℝ)
    (ω : Ω) : Finset (Fin ω.2.1) :=
  Finset.univ.filter (fun j => sellerCost ω j ≤ wStar E lamD lamS T)

/-- FCFS order, with arrival index breaking simultaneous arrivals. -/
noncomputable def sortedB (E : Environment) (lamD lamS T : ℝ)
    (ω : Ω) : List (Fin ω.1.1) :=
  (reqB E lamD lamS T ω).toList.insertionSort
    (fun i j => buyerTime ω i < buyerTime ω j ∨
      (buyerTime ω i = buyerTime ω j ∧ i ≤ j))

noncomputable def sortedS (E : Environment) (lamD lamS T : ℝ)
    (ω : Ω) : List (Fin ω.2.1) :=
  (reqS E lamD lamS T ω).toList.insertionSort
    (fun i j => sellerTime ω i < sellerTime ω j ∨
      (sellerTime ω i = sellerTime ω j ∧ i ≤ j))

/-- Seller--buyer pairs produced by greedy first-come-first-served matching. -/
noncomputable def greedyPairs (E : Environment) (lamD lamS T : ℝ)
    (ω : Ω) : List (Fin ω.2.1 × Fin ω.1.1) :=
  (sortedS E lamD lamS T ω).zip (sortedB E lamD lamS T ω)

noncomputable def Nd (E : Environment) (lamD lamS T : ℝ)
    (ω : Ω) (t : ℝ) : ℕ :=
  ((reqB E lamD lamS T ω).filter (fun i => buyerTime ω i ≤ t)).card

noncomputable def Ns (E : Environment) (lamD lamS T : ℝ)
    (ω : Ω) (t : ℝ) : ℕ :=
  ((reqS E lamD lamS T ω).filter (fun j => sellerTime ω j ≤ t)).card

noncomputable def Iminus (E : Environment) (lamD lamS T : ℝ)
    (ω : Ω) (t : ℝ) : ℤ :=
  (((reqS E lamD lamS T ω).filter (fun j => sellerTime ω j < t)).card : ℤ) -
    (((reqB E lamD lamS T ω).filter (fun i => buyerTime ω i < t)).card : ℤ)

/-- Rank of a tagged buyer, inserted just before any simultaneous arrivals. -/
noncomputable def taggedBuyerRank (E : Environment) (lamD lamS T : ℝ)
    (ω : Ω) (t : ℝ) : ℕ :=
  ((reqB E lamD lamS T ω).filter (fun i => buyerTime ω i < t)).card

noncomputable def taggedSellerRank (E : Environment) (lamD lamS T : ℝ)
    (ω : Ω) (t : ℝ) : ℕ :=
  ((reqS E lamD lamS T ω).filter (fun j => sellerTime ω j < t)).card

noncomputable def Md (E : Environment) (lamD lamS T : ℝ)
    (ω : Ω) (t : ℝ) : ℝ :=
  if taggedBuyerRank E lamD lamS T ω t < (sortedS E lamD lamS T ω).length then 1 else 0

noncomputable def Ms (E : Environment) (lamD lamS T : ℝ)
    (ω : Ω) (t : ℝ) : ℝ :=
  if taggedSellerRank E lamD lamS T ω t < (sortedB E lamD lamS T ω).length then 1 else 0

/-- Tagged waiting time, including the wait until `T` for an unmatched request. -/
noncomputable def Wd (E : Environment) (lamD lamS T : ℝ)
    (ω : Ω) (t : ℝ) : ℝ :=
  match (sortedS E lamD lamS T ω)[taggedBuyerRank E lamD lamS T ω t]? with
  | some j => max t (sellerTime ω j) - t
  | none => T - t

noncomputable def Ws (E : Environment) (lamD lamS T : ℝ)
    (ω : Ω) (t : ℝ) : ℝ :=
  match (sortedB E lamD lamS T ω)[taggedSellerRank E lamD lamS T ω t]? with
  | some i => max t (buyerTime ω i) - t
  | none => T - t

/-- Waiting per match probability on the demand side, conditioned on `I_{t-}≤0`. -/
noncomputable def compD (E : Environment) (lamD lamS T : ℝ) (t : ℝ) : ℝ :=
  (∫ ω, Wd E lamD lamS T ω t *
    (if Iminus E lamD lamS T ω t ≤ 0 then (1 : ℝ) else 0) ∂P E lamD lamS T) /
    (∫ ω, Md E lamD lamS T ω t *
      (if Iminus E lamD lamS T ω t ≤ 0 then (1 : ℝ) else 0) ∂P E lamD lamS T)

/-- Waiting per match probability on the supply side, without an inventory signal. -/
noncomputable def compS (E : Environment) (lamD lamS T : ℝ) (t : ℝ) : ℝ :=
  (∫ ω, Ws E lamD lamS T ω t ∂P E lamD lamS T) /
    (∫ ω, Ms E lamD lamS T ω t ∂P E lamD lamS T)

noncomputable def askPrice (E : Environment) (lamD lamS T b : ℝ)
    (ω : Ω) (t : ℝ) : ℝ :=
  pStar E lamD lamS T - b *
    (if Iminus E lamD lamS T ω t ≤ 0 then compD E lamD lamS T t else 0)

noncomputable def bidPrice (E : Environment) (lamD lamS T h : ℝ) (t : ℝ) : ℝ :=
  wStar E lamD lamS T + h * compS E lamD lamS T t

/-- Actual posted-price receipts less payments of matched requests. -/
noncomputable def profit (E : Environment) (lamD lamS T b h : ℝ) (ω : Ω) : ℝ :=
  ∑ p ∈ (greedyPairs E lamD lamS T ω).toFinset,
    (askPrice E lamD lamS T b ω (buyerTime ω p.2) -
      bidPrice E lamD lamS T h (sellerTime ω p.1))

noncomputable def policyProfit (E : Environment) (lamD lamS T b h : ℝ) : ℝ :=
  ∫ ω, profit E lamD lamS T b h ω ∂P E lamD lamS T

noncomputable def JbarEta (E : Environment) (lamD lamS T η : ℝ) : ℝ :=
  ∫ ω,
    ((∑ i : Fin ω.1.1, max (E.psiB (buyerValue ω i) - η) 0) +
     (∑ j : Fin ω.2.1, max (η - E.psiS (sellerCost ω j)) 0))
    ∂P E lamD lamS T

end TwoSidedMatching.Guarantee


