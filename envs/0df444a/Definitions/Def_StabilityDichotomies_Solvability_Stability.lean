-- Prove2me | Definitions.Def_StabilityDichotomies_Solvability_Stability
-- name    : StabilityDichotomies_Solvability_Stability
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:04:38.00464+00:00
-- url     : https://prove2.me/theorems/087f0a4b-7052-478c-ad04-8bb6ee7d21c3
-- title:
--   Total solver laws and Hamming transport average sensitivity
-- statement:
--   A solver law $A$ assigns a probability distribution on all Boolean assignments to every multiset instance, on every finite variable set. It solves the language when every satisfiable input receives mass one on its solution set; unsatisfiable inputs impose no condition. A deterministic solver's law is a point mass. With unnormalized Hamming distance $d_H$, set
--
--   $$W_1(\mu,\nu)=\inf_{\pi\in\Pi(\mu,\nu)}\sum_{x,y}\pi(x,y)d_H(x,y),\qquad
--   \operatorname{ASens}(A,I)=\begin{cases}|C|^{-1}\sum_{c\in C}W_1(A(I),A(I-c)),&C\ne\varnothing,\\0,&C=\varnothing.\end{cases}$$
--
--   The coupling set is the referenced general finite probability-vector interface with the prescribed row and column sums. Each mass is an arbitrary nonnegative real number, not a rational or a uniform weight. A product coupling exists; all feasible costs lie in $[0,|V|]$, and compactness implies attainment. Thus the infimum equals the source's minimum.
--
--   This definition compares output laws across actual deletions using one total rule, with no running-time restriction. PMF supplies normalized probabilities; their masses are finite, so conversion to real numbers loses no values. On a finite space zero mass outside the solutions is equivalent to probability one of correctness.
-- source:
--   Chunyang Wang, Yuichi Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535 (October 2026), pp.8,10–11, Definition 2.1, Section 2.3 and Definition 2.13, equation (2); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Solvability_Model
import Definitions.Def_FairProxy_ClosedFormDD_Coupling

noncomputable section

namespace StabilityDichotomies.Solvability

open scoped Classical

/-- Section 2.3, p.10: the unnormalized Hamming cost. -/
def hammingCost {V : Type} [Fintype V] (x y : V → Bool) : ℝ :=
  (hammingDist x y : ℝ)

/-- Finite transport cost over all real coupling matrices. The imported couplingSet
has no support restrictions. Product weights always give a feasible coupling;
all costs lie in [0, card V], so this real infimum has neither empty nor unbounded inputs. -/
def wasserstein {V : Type} [Fintype V] (μ ν : PMF (V → Bool)) : ℝ :=
  sInf {t : ℝ | ∃ π ∈ FairProxy.ClosedFormDD.couplingSet
      (fun x => (μ x).toReal) (fun y => (ν y).toReal),
    t = ∑ x, ∑ y, π x y * hammingCost x y}

/-- One total law family, on every finite labelled carrier and every multiset input. -/
abbrev Solver (Γ : Language) :=
  ∀ (V : Type) [Fintype V], Instance Γ V → PMF (V → Bool)

abbrev DeterministicSolver (Γ : Language) :=
  ∀ (V : Type) [Fintype V], Instance Γ V → (V → Bool)

def deterministicLaw {Γ : Language} (D : DeterministicSolver Γ) : Solver Γ :=
  fun V _ I => PMF.pure (D V I)

/-- On a finite space, vanishing mass outside Sol(I) is exactly mass one on Sol(I). -/
def Solves {Γ : Language} (A : Solver Γ) : Prop :=
  ∀ (V : Type) [Fintype V] (I : Instance Γ V), Satisfiable I →
    ∀ x, ¬ Solution I x → A V I x = 0

/-- Definition 2.13 (2), p.11: multiplicities contribute separately to the sum. -/
def averageSensitivity {Γ : Language} (A : Solver Γ)
    {V : Type} [Fintype V] (I : Instance Γ V) : ℝ :=
  if I.constraints = 0 then 0 else
    (I.constraints.map fun c => wasserstein (A V I) (A V (I.delete c))).sum /
      (I.constraints.card : ℝ)

end StabilityDichotomies.Solvability


