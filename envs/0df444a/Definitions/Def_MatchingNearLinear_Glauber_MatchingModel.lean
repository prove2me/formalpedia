-- Prove2me | Definitions.Def_MatchingNearLinear_Glauber_MatchingModel
-- name    : MatchingNearLinear_Glauber_MatchingModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T15:55:37.638479+00:00
-- url     : https://prove2.me/theorems/1dc98611-6382-44d4-9449-594eedfae043
-- title:
--   Labeled simple graphs and weighted matching laws with conditioning
-- statement:
--   A labeled input has vertices $[n]$, edges $[m]$, and two distinct ordered endpoints for each edge; injectivity of the unordered endpoint pair imposes simplicity. Its underlying loopless graph and matching law reuse the published MaxEntOCRS definitions. The monomer indicator is $J_v(M)=1$ when $v$ is unmatched. Arbitrary positive monomer weights are included through
--
--   $$p(M)\propto\prod_{e\in M}\lambda_e\prod_{v:J_v(M)=1}z_v.$$
--
--   The file defines conditioning on present or absent edge or monomer coordinates, means and covariance quadratic forms, minimum activity and maximum degree. A residual graph retains precisely the unpinned edges disjoint from the endpoints of pinned-present edges and inherits their activities. Deleted vertices may remain as isolated labels; residual edges are relabeled bijectively. The push-forward of the conditional matching law is defined by summing the actual conditional masses. This supports both arbitrary feasible monomer conditionings and correctly normalized residual-edge clocks.
-- source:
--   Tianshun Miao, Yitong Yin, Sampling Matchings in Near-linear Time, STOC 2027 submission #444 (October 2026), §1, printed pp.1–2 (PDF pp.3–4); §2, printed p.8 (PDF p.10); Lemma A.3, printed p.48 (PDF p.50); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/444.pdf

import Mathlib
import Definitions.Def_MatchingNearLinear_Glauber_SubsetLaws
import Definitions.Def_MaxEntOCRS_monomerDimer

set_option autoImplicit false

namespace MatchingNearLinear.Glauber


open scoped BigOperators
noncomputable section
open Classical

/-- Ordered labeled edge list. Injective unordered endpoints impose simplicity. -/
structure Input (n m : ℕ) where
  u : Fin m → Fin n
  v : Fin m → Fin n
  distinct : ∀ e, u e ≠ v e
  simple : Function.Injective (fun e => s(u e, v e))

def Input.graph {n m : ℕ} (G : Input n m) : EdmondsMatching65.Polyhedron.Graph (Fin n) (Fin m) where
  ends e := s(G.u e, G.v e)
  loopless e := by simpa only [Sym2.mk_isDiag_iff] using G.distinct e

/-- Reuse the actual published monomer–dimer law, zero off matchings. -/
def matchingLaw {n m : ℕ} (G : Input n m) (lam : Fin m → ℝ) : Config m → ℝ :=
  MaxEntOCRS.monomerDimer G.graph lam

def ActivityBound {m : ℕ} (lam : Fin m → ℝ) (a : ℝ) : Prop :=
  ∀ e, 0 < lam e ∧ lam e ≤ a

def minActivity {m : ℕ} (lam : Fin m → ℝ) : ℝ := sInf (Set.range lam)
def maxDegree {n m : ℕ} (G : Input n m) : ℕ :=
  Finset.univ.sup fun w => (Finset.univ.filter fun e => G.u e = w ∨ G.v e = w).card

def monomer {n m : ℕ} (G : Input n m) (M : Config m) (w : Fin n) : ℝ :=
  if ∀ e ∈ M, G.u e ≠ w ∧ G.v e ≠ w then 1 else 0

/-- Arbitrary positive monomer weights, not implicitly unit weights. -/
def monomerWeightedLaw {n m : ℕ} (G : Input n m) (lam : Fin m → ℝ) (z : Fin n → ℝ)
    (M : Config m) : ℝ :=
  let w := fun S : Config m => MaxEntOCRS.mdWeight G.graph lam S *
    ∏ v : Fin n, if monomer G S v = 1 then z v else 1
  w M / ∑ S, w S

/-- Feasible conditioning on any family of binary observables. -/
def eventMass {α ι : Type} [Fintype α] [Fintype ι] (p : α → ℝ) (X : α → ι → ℝ)
    (τ : ι → Option Bool) : ℝ :=
  ∑ x, if ∀ i b, τ i = some b → X x i = (if b then 1 else 0) then p x else 0

def conditionObservables {α ι : Type} [Fintype α] [Fintype ι] (p : α → ℝ) (X : α → ι → ℝ)
    (τ : ι → Option Bool) (x : α) : ℝ :=
  if ∀ i b, τ i = some b → X x i = (if b then 1 else 0)
  then p x / eventMass p X τ else 0

def observableMean {α ι : Type} [Fintype α] (p : α → ℝ) (X : α → ι → ℝ) (i : ι) : ℝ :=
  ∑ x, p x * X x i

def observableCov {α ι : Type} [Fintype α] (p : α → ℝ) (X : α → ι → ℝ) (i j : ι) : ℝ :=
  (∑ x, p x * X x i * X x j) - observableMean p X i * observableMean p X j

def ObservableCovarianceBound {α ι : Type} [Fintype α] [Fintype ι]
    (p : α → ℝ) (X : α → ι → ℝ) (c : ℝ) : Prop :=
  ∀ a : ι → ℝ, (∑ i, ∑ j, a i * observableCov p X i j * a j) ≤
    c * ∑ i, observableMean p X i * (a i)^2

/-- Arbitrary feasible present/absent edge pin, on the original configuration carrier. -/
def edgeConditional {n m : ℕ} (G : Input n m) (lam : Fin m → ℝ) (τ : Fin m → Option Bool) :=
  conditionObservables (matchingLaw G lam) indicator τ


abbrev AvailableEdge {n m : ℕ} (G : Input n m) (τ : Fin m → Option Bool) :=
  {e : Fin m // τ e = none ∧ ∀ f, τ f = some true →
    G.u e ≠ G.u f ∧ G.u e ≠ G.v f ∧ G.v e ≠ G.u f ∧ G.v e ≠ G.v f}

noncomputable instance availableFintype {n m : ℕ} (G : Input n m) (τ : Fin m → Option Bool) :
    Fintype (AvailableEdge G τ) := Fintype.ofFinite _

def residualEdgeCount {n m : ℕ} (G : Input n m) (τ : Fin m → Option Bool) : ℕ :=
  Fintype.card (AvailableEdge G τ)

def originalEdge {n m : ℕ} (G : Input n m) (τ : Fin m → Option Bool)
    (e : Fin (residualEdgeCount G τ)) : Fin m :=
  ((Fintype.equivFin (AvailableEdge G τ)).symm e).val

/-- Deleted vertices are retained as isolated labels, which changes no matching or time unit. -/
def residualInput {n m : ℕ} (G : Input n m) (τ : Fin m → Option Bool) :
    Input n (residualEdgeCount G τ) where
  u e := G.u (originalEdge G τ e)
  v e := G.v (originalEdge G τ e)
  distinct e := G.distinct _
  simple := by
    intro e f h
    have he := G.simple h
    exact (Fintype.equivFin (AvailableEdge G τ)).symm.injective (Subtype.ext he)

def residualActivities {n m : ℕ} (G : Input n m) (τ : Fin m → Option Bool) (lam : Fin m → ℝ) :=
  fun e : Fin (residualEdgeCount G τ) => lam (originalEdge G τ e)

def residualConfig {n m : ℕ} (G : Input n m) (τ : Fin m → Option Bool) (M : Config m) :
    Config (residualEdgeCount G τ) := Finset.univ.filter fun e => originalEdge G τ e ∈ M

def residualPushLaw {n m : ℕ} (G : Input n m) (lam : Fin m → ℝ) (τ : Fin m → Option Bool)
    (S : Config (residualEdgeCount G τ)) : ℝ :=
  ∑ M, if residualConfig G τ M = S then edgeConditional G lam τ M else 0

end
end MatchingNearLinear.Glauber


