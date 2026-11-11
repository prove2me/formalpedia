-- Prove2me | Definitions.Def_StochMatchQuery_Union_Algorithm1
-- name    : StochMatchQuery_Union_Algorithm1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:06:57.503667+00:00
-- url     : https://prove2.me/theorems/0b724737-4811-4c55-92b9-bc129fd3de22
-- title:
--   Algorithm 1 and optimal-edge marginals
-- statement:
--   Draw $r$ independent realizations, independently of the actual realization $\mathcal G$. For a fixed selector $S$, put
--   $$M_j=S(\mathcal G_j),\quad Q=\bigcup_{j=1}^r M_j,\quad\mathcal Q=Q\cap\mathcal G.$$
--   The expected output weight is the finite average of $\operatorname{opt}(\mathcal Q)$. Define $x_e=\Pr(e\in S(\mathcal G))$, $q_e=\Pr(e\in Q)$, and $W(T)=\sum_{e\in T}w_ex_e$. Full negative association compares expectations of arbitrary increasing functions on disjoint coordinate subfamilies, with integrability whenever those expectations are used. This is the stronger notion needed for load threshold events.
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Tao Yu, STOC 2027 submission #394 (October 2026), Algorithm 1, p.3; (2.1), p.9. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/394.pdf

import Definitions.Def_StochMatchQuery_Union_Instance

open MeasureTheory ProbabilityTheory ProphetMatchingEFGT

namespace StochMatchQuery.Union
noncomputable section
open Classical
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {w : Edge G → ℝ}

def sampleMatching (s : Selector G w) {r : ℕ} (samples : Fin r → Realization G) (j : Fin r) := s.choose (samples j)
def querySet (s : Selector G w) {r : ℕ} (samples : Fin r → Realization G) : Realization G :=
  Finset.univ.biUnion (fun j => sampleMatching G s samples j)
def queriedRealization (s : Selector G w) {r : ℕ} (a : Realization G) (samples : Fin r → Realization G) :=
  querySet G s samples ∩ a

def sampleMass (p : Edge G → ℝ) {r : ℕ} (samples : Fin r → Realization G) : ℝ :=
  ∏ j, realizationMass G p (samples j)
def sampleLaw (p : Edge G → ℝ) (r : ℕ) : Measure (Fin r → Realization G) :=
  ∑ samples, ENNReal.ofReal (sampleMass G p samples) • Measure.dirac samples

def algorithmLaw (p : Edge G → ℝ) (r : ℕ) : Measure (Realization G × (Fin r → Realization G)) :=
  (realizationLaw G p).prod (sampleLaw G p r)

def marginal (p : Edge G → ℝ) (s : Selector G w) (e : Edge G) : ℝ :=
  ∑ a : Realization G, realizationMass G p a * ind (e ∈ s.choose a)
def queryProbability (p : Edge G → ℝ) (s : Selector G w) (r : ℕ) (e : Edge G) : ℝ :=
  ∑ samples : Fin r → Realization G, sampleMass G p samples * ind (e ∈ querySet G s samples)
def W (p : Edge G → ℝ) (s : Selector G w) (S : Realization G) : ℝ :=
  ∑ e ∈ S, w e * marginal G p s e

def expectedOpt (p : Edge G → ℝ) : ℝ :=
  ∑ a : Realization G, realizationMass G p a * subsetOpt G w a

def algorithmValue (p : Edge G → ℝ) (s : Selector G w) (r : ℕ) : ℝ :=
  ∑ a : Realization G, ∑ samples : Fin r → Realization G,
    realizationMass G p a * sampleMass G p samples *
      subsetOpt G w (queriedRealization G s a samples)

/-- A realization and its samples on an arbitrary common probability space.
No restriction on additional variables sharing that space. -/
def HasAlgorithmLaw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (p : Edge G → ℝ) {r : ℕ} (actual : Ω → Realization G)
    (samples : Ω → Fin r → Realization G) : Prop :=
  Measurable actual ∧ Measurable samples ∧
  Measure.map (fun ω => (actual ω, samples ω)) μ = algorithmLaw G p r

/-- Full negative association, with arbitrary increasing functions of disjoint subfamilies. -/
def NegativelyAssociated {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
    (μ : Measure Ω) (X : ι → Ω → ℝ) : Prop :=
  ∀ (I J : Finset ι), Disjoint I J →
    ∀ (f : (I → ℝ) → ℝ) (g : (J → ℝ) → ℝ), Monotone f → Monotone g →
      Integrable (fun ω => f (fun i => X i ω)) μ →
      Integrable (fun ω => g (fun j => X j ω)) μ →
      Integrable (fun ω => f (fun i => X i ω) * g (fun j => X j ω)) μ →
      mean μ (fun ω => f (fun i => X i ω) * g (fun j => X j ω)) ≤
        mean μ (fun ω => f (fun i => X i ω)) * mean μ (fun ω => g (fun j => X j ω))
end
end StochMatchQuery.Union


