-- Prove2me | Definitions.Def_JointParametricPricing_PSC_Policy
-- name    : JointParametricPricing_PSC_Policy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T08:49:22.46838+00:00
-- url     : https://prove2.me/theorems/a698e6c5-86b0-4834-aaf8-ddf3b4966a62
-- title:
--   PSC and expected regret under proportional scaling
-- statement:
--   For scale $k$, PSC has $N=kT$ periods, initial stock $kC$, and exploration length $L=\lceil\sqrt N\rceil$. At each exploration period it offers the prescribed block-scheduled price if every product fits; otherwise it shuts all products off permanently. After successful exploration it selects an MLE from those $L$ observations and optimizes the deterministic program once. Its later target is the optimal estimated rate minus the sum of realized-minus-estimated sales divided by the remaining periods. The inverse candidate exists only within the estimated feasible-rate image. If the candidate is feasible and every product fits, it is offered. Otherwise each product that does not fit is shut off and each fitting product keeps its previous price. This reads the printed strict comparison as failure of componentwise inventory dominance (I4). Current stock is initial stock minus cumulative realized consumption. The mixed-action demand law determines each subsequent observation. Revenue is the posted ordinary price of the purchased product, or zero for no purchase; off actions produce no sale. Regret subtracts the finite-path expected revenue from $kT r(\lambda^D(\theta^*);\theta^*)$.
-- source:
--   Chen, Jasin and Duenyas (2021), Technical Note—Joint Learning and Optimization of Multi-Product Pricing with Finite Resource Capacity and Unknown Demand Parameters, DOI:10.1287/opre.2020.2078; held LBS manuscript/online appendix (published citation basis); PSC box and equation (1), printed 11 / PDF 12; scaling, printed 10 / PDF 11

import Definitions.Def_JointParametricPricing_PSC_Exploration

open scoped BigOperators
noncomputable section

namespace JointParametricPricing.PSC

namespace Model
variable {n m q : ℕ}
def ValidAction (M : Model n m q) (a : Action n) : Prop :=
  ∀ j p, a j = some p → M.lower j ≤ p ∧ p ≤ M.upper j
abbrev Offer (M : Model n m q) := {a : Action n // M.ValidAction a}

def off (M : Model n m q) : M.Offer := ⟨allOff, by simp [ValidAction, allOff]⟩
def offer (M : Model n m q) (p : M.prices) : M.Offer :=
  ⟨ordinary p, by intro j z hz; cases Option.some.inj hz; exact p.property j⟩

def experiment (M : Model n m q) : FiniteExperiment M.Offer (Sale n) M.Θ where
  mass a θ y := categoricalMass (M.extendedDemand a θ) y
  nonneg a θ y := by
    have hh := M.extended_simplex θ θ.property a a.property
    cases y with
    | none => exact sub_nonneg.mpr hh.2
    | some j => exact hh.1 j
  total a θ := by
    simp [categoricalMass, Fintype.sum_option]

abbrev History (M : Model n m q) := List (M.Offer × Sale n)

def remaining (M : Model n m q) (k : ℕ) (h : M.History) (i : Fin m) : ℝ :=
  (k : ℝ) * M.C i - (h.map (fun z => ∑ j, M.A i j * saleVector z.2 j)).sum

def Fits (M : Model n m q) (k : ℕ) (h : M.History) (j : Fin n) : Prop :=
  ∀ i, M.A i j ≤ M.remaining k h i

def fallback (M : Model n m q) (k : ℕ) (h : M.History) : M.Offer := by
  classical
  let prev := (h.headD (M.off, none)).1
  exact ⟨(fun j => if M.Fits k h j then prev.val j else none), by
    intro j p hp
    dsimp only at hp
    split_ifs at hp with hj
    exact prev.property j p hp⟩

def explorationLength (M : Model n m q) (k : ℕ) : ℕ := ⌈Real.sqrt (k * M.T : ℕ)⌉₊

def explorationData (M : Model n m q) (L : ℕ) (h : M.History) : Fin L → Sale n :=
  fun i => ((h.reverse)[i.val]?.getD (M.off, none)).2

/-- Inverse is queried only in its image domain, then its price is checked. -/
def candidate (M : Model n m q) (θ : M.Θ) (x : Vec n) : Option M.Offer := by
  classical
  exact if hx : x ∈ M.rates θ then
    some (M.offer ⟨M.inverse x θ, (M.inverse_right θ θ.property x hx).1⟩)
  else none

def target (M : Model n m q) (hf : M.Feasible) (θ : M.Θ)
    (N L : ℕ) (h : M.History) : Vec n :=
  M.optimalRate hf θ - ∑ s ∈ Finset.Ico L h.length,
    if s + 1 < N then
      let obs := ((h.reverse)[s]?.getD (M.off, none))
      ((N : ℝ) - (s + 1 : ℕ))⁻¹ • (saleVector obs.2 - M.extendedDemand obs.1 θ)
    else 0

/-- PSC, as the price rule on its finite histories. Histories are most recent first. -/
def psc (M : Model n m q) (hf : M.Feasible) (E : ExplorationPrices M)
    (S : E.MLESelector) (k : ℕ) : FiniteExperiment.Policy (Action := M.Offer) (Outcome := Sale n) := by
  classical
  intro h
  let N := k * M.T
  let L := M.explorationLength k
  exact if hN : h.length < N then
    if hL : h.length < L then
      if ∀ j, M.Fits k h j then M.offer (E.scheduled L ⟨h.length, hL⟩) else M.off
    else if ((h.reverse.take L).any (fun z => decide (z.1.val = allOff))) then M.off
    else
      let θ := S.choose L (M.explorationData L h)
      match M.candidate θ (M.target hf θ N L h) with
      | some p => if ∀ j, M.Fits k h j then p else M.fallback k h
      | none => M.fallback k h
  else M.off

def earned (M : Model n m q) (h : M.History) : ℝ :=
  (h.map (fun z => match z.2 with
    | none => 0
    | some j => (z.1.val j).getD 0)).sum

def regret (M : Model n m q) (hf : M.Feasible) (E : ExplorationPrices M)
    (S : E.MLESelector) (k : ℕ) : ℝ :=
  (k * M.T : ℕ) * M.revenue M.thetaStar (M.optimalRate hf ⟨M.thetaStar, M.thetaStar_mem⟩) -
    M.experiment.expectation (M.psc hf E S k) ⟨M.thetaStar, M.thetaStar_mem⟩ (k * M.T) M.earned
end Model
end JointParametricPricing.PSC


