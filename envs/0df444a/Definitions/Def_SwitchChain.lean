-- Prove2me | Definitions.Def_SwitchChain
-- name    : SwitchChain
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:07.212496+00:00
-- url     : https://prove2.me/theorems/6d1e53b6-42fc-455e-a37b-b5955bd67873
-- statement:
--   For n labelled vertices and a degree sequence d, graphDegree counts the neighbours of a vertex, Realizes d G means every vertex v has degree d(v), GraphState n d is the type of simple graphs on Fin n realizing d, and Graphical means this type is nonempty. A FourSet is a 4-element vertex subset, and a perfect matching on such a set S is a graph in which each vertex of S has exactly one neighbour and every vertex outside S has none. A SwitchProposal is a choice of a FourSet S together with an ordered pair of distinct perfect matchings on S, the first to be removed and the second to be added. validSwitch G p holds when every edge of the removed matching is an edge of G and no edge of the added matching is an edge of G; replaceEdges deletes the removed matching's edges from G and adds the new ones, and proposalResult applies this when the switch is valid and otherwise returns G unchanged. The switchKernel from G to H is 1/2 if G = H (a lazy holding term) plus the number of proposals whose result is H divided by 12 times C(n,4), as a real number. kernelPow gives the t-step kernel by iterated matrix multiplication, starting from the identity. On states, uniformAverage, uniformInner and uniformVariance are taken with respect to the uniform distribution over all states, markovApply applies the kernel to a real function, and dirichletEnergy of f is the uniform inner product of f with f minus its kernel image. hasSpectralGapAtLeast γ means γ times the variance of f is at most the Dirichlet energy for every real function f. tvDistanceFrom t G is half the sum over states H of the absolute difference between the t-step probability from G to H and 1/stateCount, MixedAt t requires this to be at most 1/4 from every starting state, and mixingTime is the least such t, given a proof that one exists. SwitchStep G H says some proposal is valid at G and yields H.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SwitchChain.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SwitchChain.lean; bytes 16..4693
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem315

def graphDegree {n : Nat} (G : SimpleGraph (Fin n)) (v : Fin n) : Nat := by
  classical
  exact (Finset.univ.filter (fun w => G.Adj v w)).card

def Realizes (n : Nat) (d : Fin n → Nat) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ v, graphDegree G v = d v

abbrev GraphState (n : Nat) (d : Fin n → Nat) :=
  {G : SimpleGraph (Fin n) // Realizes n d G}

def Graphical (n : Nat) (d : Fin n → Nat) : Prop :=
  Nonempty (GraphState n d)

abbrev FourSet (n : Nat) := {S : Finset (Fin n) // S.card = 4}

def IsPerfectMatchingOn {n : Nat} (S : Finset (Fin n))
    (M : SimpleGraph (Fin n)) : Prop :=
  ∀ v, (v ∈ S → ∃! w, M.Adj v w) ∧
    (v ∉ S → ∀ w, ¬ M.Adj v w)

abbrev PerfectMatching {n : Nat} (S : FourSet n) :=
  {M : SimpleGraph (Fin n) // IsPerfectMatchingOn S.1 M}

abbrev SwitchProposal (n : Nat) :=
  Σ S : FourSet n,
    {p : PerfectMatching S × PerfectMatching S // p.1 ≠ p.2}

def removedMatching {n : Nat} (p : SwitchProposal n) : SimpleGraph (Fin n) :=
  p.2.val.1.val

def addedMatching {n : Nat} (p : SwitchProposal n) : SimpleGraph (Fin n) :=
  p.2.val.2.val

def validSwitch {n : Nat} (G : SimpleGraph (Fin n))
    (p : SwitchProposal n) : Prop :=
  (∀ ⦃u v⦄, (removedMatching p).Adj u v → G.Adj u v) ∧
  (∀ ⦃u v⦄, (addedMatching p).Adj u v → ¬ G.Adj u v)

def replaceEdges {n : Nat} (G M N : SimpleGraph (Fin n)) :
    SimpleGraph (Fin n) where
  Adj u v := (G.Adj u v ∧ ¬ M.Adj u v) ∨ N.Adj u v
  symm := by
    constructor
    intro u v h
    rcases h with h | h
    · left
      exact ⟨G.symm.symm u v h.1, fun hm => h.2 (M.symm.symm v u hm)⟩
    · right
      exact N.symm.symm u v h
  loopless := by
    constructor
    intro v h
    rcases h with h | h
    · exact G.loopless.irrefl v h.1
    · exact N.loopless.irrefl v h

def proposalResult {n : Nat} (G : SimpleGraph (Fin n))
    (p : SwitchProposal n) : SimpleGraph (Fin n) := by
  classical
  exact
    if validSwitch G p then
      replaceEdges G (removedMatching p) (addedMatching p)
    else G

def allGraphStates (n : Nat) (d : Fin n → Nat) :
    Finset (GraphState n d) := by
  classical
  exact Finset.univ

def allProposals (n : Nat) : Finset (SwitchProposal n) := by
  classical
  exact Finset.univ

def stateCount (n : Nat) (d : Fin n → Nat) : Nat :=
  (allGraphStates n d).card

def switchKernel (n : Nat) (d : Fin n → Nat)
    (G H : GraphState n d) : ℝ := by
  classical
  exact
    (if G = H then (1 : ℝ) / 2 else 0) +
      (((allProposals n).filter
          (fun p => proposalResult G.val p = H.val)).card : ℝ) /
        (12 * (Nat.choose n 4 : ℝ))

def kernelPow (n : Nat) (d : Fin n → Nat) :
    Nat → GraphState n d → GraphState n d → ℝ := by
  classical
  intro t
  induction t with
  | zero =>
      exact fun G H => if G = H then 1 else 0
  | succ t previous =>
      exact fun G H =>
        Finset.sum (allGraphStates n d)
          (fun K => previous G K * switchKernel n d K H)

def uniformAverage (n : Nat) (d : Fin n → Nat)
    (f : GraphState n d → ℝ) : ℝ :=
  Finset.sum (allGraphStates n d) (fun G => f G) /
    (stateCount n d : ℝ)

def uniformInner (n : Nat) (d : Fin n → Nat)
    (f g : GraphState n d → ℝ) : ℝ :=
  uniformAverage n d (fun G => f G * g G)

def uniformVariance (n : Nat) (d : Fin n → Nat)
    (f : GraphState n d → ℝ) : ℝ :=
  uniformAverage n d
    (fun G => (f G - uniformAverage n d f) ^ 2)

def markovApply (n : Nat) (d : Fin n → Nat)
    (f : GraphState n d → ℝ) (G : GraphState n d) : ℝ :=
  Finset.sum (allGraphStates n d)
    (fun H => switchKernel n d G H * f H)

def dirichletEnergy (n : Nat) (d : Fin n → Nat)
    (f : GraphState n d → ℝ) : ℝ :=
  uniformInner n d f (fun G => f G - markovApply n d f G)

def hasSpectralGapAtLeast (n : Nat) (d : Fin n → Nat) (γ : ℝ) : Prop :=
  ∀ f : GraphState n d → ℝ,
    γ * uniformVariance n d f ≤ dirichletEnergy n d f

def tvDistanceFrom (n : Nat) (d : Fin n → Nat)
    (t : Nat) (G : GraphState n d) : ℝ :=
  (1 / 2 : ℝ) *
    Finset.sum (allGraphStates n d)
      (fun H =>
        |kernelPow n d t G H - (1 : ℝ) / (stateCount n d : ℝ)|)

def MixedAt (n : Nat) (d : Fin n → Nat) (t : Nat) : Prop :=
  ∀ G : GraphState n d, tvDistanceFrom n d t G ≤ (1 : ℝ) / 4

def mixingTime (n : Nat) (d : Fin n → Nat)
    (h : ∃ t : Nat, MixedAt n d t) : Nat := by
  classical
  exact Nat.find h

def SwitchStep (n : Nat) (d : Fin n → Nat)
    (G H : GraphState n d) : Prop :=
  ∃ p : SwitchProposal n,
    validSwitch G.val p ∧ proposalResult G.val p = H.val



end Problem315
end
end OAI


