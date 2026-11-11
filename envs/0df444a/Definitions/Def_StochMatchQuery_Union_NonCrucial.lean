-- Prove2me | Definitions.Def_StochMatchQuery_Union_NonCrucial
-- name    : StochMatchQuery_Union_NonCrucial
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:08:40.12274+00:00
-- url     : https://prove2.me/theorems/03e849de-b9d0-49cc-8b70-ba141c4f150a
-- title:
--   Non-crucial coefficients, loads, and fractional matching
-- statement:
--   On a common probability space, let $A$ be the available set, $I_v=1_{\{v\in A\}}$, and $\pi_{uv}=\Pr(u,v\in A)$. For $e=uv\in N$, put
--   $$g_e=\frac{x_e}{p_eq_e\pi_{uv}},\quad L_v=\sum_{uv\in N}g_{uv}I_u1_{\{uv\in\mathcal Q\}},\quad\kappa=\frac{h^3\beta^2}{10^5},\quad b_0(K)=\min\{\kappa\beta^2/6,h^3\beta^6/(10^5K)\}.$$
--   An edge receives $g_e/(1+h)$ precisely when queried, realized, both endpoints are available, and neither endpoint has load above $1+h$; otherwise it receives zero. The hypothesis record contains exactly the distributional, threshold, capacity, availability, covariance and sample conditions in Lemma 6.1. It contains no load bound, output matching or other conclusion.
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Tao Yu, STOC 2027 submission #394 (October 2026), §6, (6.1)–(6.20), pp.24–29. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/394.pdf

import Definitions.Def_StochMatchQuery_Union_LocalComputation

open MeasureTheory ProbabilityTheory ProphetMatchingEFGT

namespace StochMatchQuery.Union
noncomputable section
open Classical
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {Ω : Type} [MeasurableSpace Ω]

def kappa (h beta : ℝ) : ℝ := h^3 * beta^2 / 100000
def bZero (h beta K : ℝ) : ℝ := min (kappa h beta * beta^2 / 6) (h^3 * beta^6 / (100000*K))

def availability (μ : Measure Ω) (A : Ω → Finset V) (v : V) : ℝ := prob μ (fun ω => v ∈ A ω)
def pairAvailability (μ : Measure Ω) (A : Ω → Finset V) (e : Edge G) : ℝ :=
  prob μ (fun ω => ∀ v, v ∈ (e : Sym2 V) → v ∈ A ω)
def coefficient (μ : Measure Ω) (p : Edge G → ℝ) {w : Edge G → ℝ}
    (s : Selector G w) (r : ℕ) (A : Ω → Finset V) (e : Edge G) : ℝ :=
  marginal G p s e / (p e * queryProbability G p s r e * pairAvailability G μ A e)

def load (μ : Measure Ω) (p : Edge G → ℝ) {w : Edge G → ℝ}
    (s : Selector G w) {r : ℕ} (N : Realization G) (A : Ω → Finset V)
    (actual : Ω → Realization G) (samples : Ω → Fin r → Realization G) (v : V) (ω : Ω) : ℝ :=
  ∑ e ∈ incident G N v, ∑ u ∈ Finset.univ.filter (fun u => u ∈ (e : Sym2 V) ∧ u ≠ v),
    coefficient G μ p s r A e * ind (u ∈ A ω) *
      ind (e ∈ queriedRealization G s (actual ω) (samples ω))

def loadWithout (μ : Measure Ω) (p : Edge G → ℝ) {w : Edge G → ℝ}
    (s : Selector G w) {r : ℕ} (N : Realization G) (A : Ω → Finset V)
    (actual : Ω → Realization G) (samples : Ω → Fin r → Realization G)
    (e : Edge G) (v : V) (ω : Ω) : ℝ :=
  load G μ p s (N.erase e) A actual samples v ω

def gamma (h : ℝ) : ℝ := 1/(1+h)

def overloaded (μ : Measure Ω) (p : Edge G → ℝ) {w : Edge G → ℝ}
    (s : Selector G w) {r : ℕ} (N : Realization G) (A : Ω → Finset V)
    (actual : Ω → Realization G) (samples : Ω → Fin r → Realization G)
    (h : ℝ) (v : V) (ω : Ω) : Prop :=
  load G μ p s N A actual samples v ω > 1+h

def untrimmedFractionalValue (μ : Measure Ω) (p : Edge G → ℝ) {w : Edge G → ℝ}
    (s : Selector G w) {r : ℕ} (N : Realization G) (A : Ω → Finset V)
    (actual : Ω → Realization G) (samples : Ω → Fin r → Realization G)
    (h : ℝ) (ω : Ω) (e : Edge G) : ℝ :=
  gamma h * coefficient G μ p s r A e * ind (e ∈ N) *
    ind (∀ v, v ∈ (e : Sym2 V) → v ∈ A ω) *
    ind (e ∈ queriedRealization G s (actual ω) (samples ω))

def fractionalValue (μ : Measure Ω) (p : Edge G → ℝ) {w : Edge G → ℝ}
    (s : Selector G w) {r : ℕ} (N : Realization G) (A : Ω → Finset V)
    (actual : Ω → Realization G) (samples : Ω → Fin r → Realization G)
    (h : ℝ) (ω : Ω) (e : Edge G) : ℝ :=
  if ∃ v, v ∈ (e : Sym2 V) ∧ overloaded G μ p s N A actual samples h v ω
  then 0 else untrimmedFractionalValue G μ p s N A actual samples h ω e

/-- Exactly the hypotheses of §6, on a common space; no output or variance conclusions. -/
structure NonCrucialData (μ : Measure Ω) (p w : Edge G → ℝ) (s : Selector G w)
    (r : ℕ) (N : Realization G) (actual : Ω → Realization G)
    (samples : Ω → Fin r → Realization G) (M : Ω → Realization G) (A : Ω → Finset V)
    (h beta K b : ℝ) : Prop where
  probability : IsProbabilityMeasure μ
  p_bounds : ∀ e, 0 < p e ∧ p e ≤ 1
  weights : ∀ e, 0 ≤ w e
  algorithm : HasAlgorithmLaw G μ p actual samples
  M_measurable : Measurable M
  A_measurable : Measurable A
  matching : ∀ ω, IsMatching G (M ω)
  available : ∀ ω, Disjoint (A ω) (vertices G (M ω))
  independence : IndepFun (fun ω => (M ω, A ω))
    (fun ω => (querySet G s (samples ω), actual ω ∩ N)) μ
  h_bounds : 0 < h ∧ h ≤ 1/10
  beta_bounds : 0 < beta ∧ beta ≤ 1/10
  K_bound : 1 ≤ K
  b_positive : 0 < b
  b_bound : b ≤ bZero h beta K
  threshold : ∀ e ∈ N, marginal G p s e / p e ≤ b
  vertex_floor : ∀ v, beta ≤ availability μ A v
  pair_floor : ∀ e ∈ N, beta^2 ≤ pairAvailability G μ A e
  capacity : ∀ v, ∑ e ∈ incident G N v, marginal G p s e ≤ availability μ A v
  covariance : ∀ u, ∑ v : V, |cov μ (fun ω => ind (u ∈ A ω)) (fun ω => ind (v ∈ A ω))| ≤ K
  samples_bound : ∀ e, (6 / (kappa h beta * beta^2 * p e)) ≤ (r : ℝ)
end
end StochMatchQuery.Union


