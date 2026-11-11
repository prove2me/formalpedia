-- Prove2me | Definitions.Def_StochMatchQuery_Union_Instance
-- name    : StochMatchQuery_Union_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:06:13.253252+00:00
-- url     : https://prove2.me/theorems/96bb17e7-5e25-441f-aa64-2e0580997051
-- title:
--   Finite realizations, subset optima, and fixed maximum-weight selectors
-- statement:
--   Let $G=(V,E)$ be a finite undirected simple graph. A realization is a subset $F\subseteq E$. The imported matching predicate and weight sum are used without additional assumptions. For weights $w$, define
--   $$\operatorname{opt}(F)=\max\{\sum_{e\in M}w_e:M\subseteq F\text{ is a matching}\}.$$
--   The empty matching is a competitor. A selector deterministically chooses an attaining matching for every subset. Independent-edge realizations have mass $\prod_{e\in F}p_e\prod_{e\notin F}(1-p_e)$. The bundle also defines degree, matched vertices, expectation, covariance, and finite-fiber conditioning. These provide the model shared by every statement.
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Tao Yu, STOC 2027 submission #394 (October 2026), §§1, 2.10; pp.1–3, 9. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/394.pdf

import Definitions.Def_ProphetMatchingEFGT_MatchingModel

open MeasureTheory ProbabilityTheory
open ProphetMatchingEFGT

namespace StochMatchQuery.Union
noncomputable section
open Classical
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The finite set of realized edges. All subsets, including the empty one, are allowed. -/
abbrev Realization := Finset (Edge G)

def incident (S : Realization G) (v : V) : Realization G := S.filter (fun e => v ∈ (e : Sym2 V))
def vertices (S : Realization G) : Finset V := Finset.univ.filter (fun v => (incident G S v).Nonempty)
def degree (S : Realization G) (v : V) : ℕ := (incident G S v).card
def maxDegree (S : Realization G) : ℕ := Finset.univ.sup (degree G S)
def subsetMatchings (S : Realization G) : Finset (Realization G) :=
  (ProphetMatchingEFGT.matchings G).filter (fun M => M ⊆ S)

theorem subsetMatchings_nonempty (S : Realization G) : (subsetMatchings G S).Nonempty :=
  ⟨∅, by simp [subsetMatchings, ProphetMatchingEFGT.matchings, IsMatching]⟩

/-- A finite maximum, with the empty matching among its competitors. -/
def subsetOpt (w : Edge G → ℝ) (S : Realization G) : ℝ :=
  (subsetMatchings G S).sup' (subsetMatchings_nonempty G S) (weightOf w)

/-- Fixed deterministic tie-breaking, shared by all samples and OPT. -/
structure Selector (w : Edge G → ℝ) where
  choose : Realization G → Realization G
  contained : ∀ S, choose S ⊆ S
  matching : ∀ S, IsMatching G (choose S)
  optimal : ∀ S, weightOf w (choose S) = subsetOpt G w S

/-- Independent-edge mass; the theorems impose the appropriate bounds on p. -/
def realizationMass (p : Edge G → ℝ) (S : Realization G) : ℝ :=
  ∏ e : Edge G, if e ∈ S then p e else 1 - p e

def realizationLaw (p : Edge G → ℝ) : Measure (Realization G) :=
  ∑ S : Realization G, ENNReal.ofReal (realizationMass G p S) • Measure.dirac S

def minProbability (p : Edge G → ℝ) (hne : (Finset.univ : Realization G).Nonempty) : ℝ :=
  Finset.univ.inf' hne p

def ind (P : Prop) : ℝ := if P then 1 else 0

def prob {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (P : Ω → Prop) : ℝ :=
  (μ {ω | P ω}).toReal

def mean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) : ℝ := ∫ ω, X ω ∂μ

def cov {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X Y : Ω → ℝ) : ℝ :=
  mean μ (fun ω => X ω * Y ω) - mean μ X * mean μ Y

def var {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) : ℝ := cov μ X X

/-- Finite-valued conditioning, zero on null fibers, and no totalized nonintegrable integral. -/
def fiberMean {Ω : Type*} [MeasurableSpace Ω] {A : Type*} [Fintype A]
    (μ : Measure Ω) (Z : Ω → A) (X : Ω → ℝ) (ω : Ω) : ℝ :=
  mean μ (fun η => ind (Z η = Z ω) * X η) / prob μ (fun η => Z η = Z ω)

def fiberVar {Ω : Type*} [MeasurableSpace Ω] {A : Type*} [Fintype A]
    (μ : Measure Ω) (Z : Ω → A) (X : Ω → ℝ) (ω : Ω) : ℝ :=
  fiberMean μ Z (fun η => (X η - fiberMean μ Z X ω)^2) ω

end
end StochMatchQuery.Union


