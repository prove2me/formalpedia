-- Prove2me | Definitions.Def_StochMatchQuery_Union_Thresholds
-- name    : StochMatchQuery_Union_Thresholds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:10:00.179362+00:00
-- url     : https://prove2.me/theorems/0a4bcea7-740b-4863-9d40-3105e4597292
-- title:
--   Threshold recursion, marking, and the §7 assembly space
-- statement:
--   For $\varepsilon\in(0,1)$ set $h=\beta=\varepsilon/10$ and $J=\lceil1/h\rceil$. Define
--   $$a_0=1,\quad K_i=1+K_{\rm cov}(a_i,h),\quad a_{i+1}=\min\{a_i/2,b_0(K_i)\},\quad C_\varepsilon=\max\{6/(\kappa\beta^2),\log(1/h)/a_J\}.$$
--   For an index $i$, define $C=\{e:x_e/p_e\ge a_i\}$, $N=\{e:x_e/p_e\le a_{i+1}\}$, and the open band between them. Actual edges, samples, vertex seeds and Bernoulli marks form one product space. Given the map supplied by Lemma 5.1, $M_C^0$ is its output on $\mathcal G_C$, $M_C$ deletes edges with marked endpoints, and $A$ consists of vertices unmatched in $M_C^0$ together with marked vertices. The assembly guarantee names exactly (7.8)–(7.10) as hypotheses on that supplied map.
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Tao Yu, STOC 2027 submission #394 (October 2026), (7.1), (7.3)–(7.11), pp.30–33. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/394.pdf

import Definitions.Def_StochMatchQuery_Union_NonCrucial

open MeasureTheory ProbabilityTheory ProphetMatchingEFGT

namespace StochMatchQuery.Union
noncomputable section
open Classical

def accuracy (eps : ℝ) : ℝ := eps/10
def bandCount (eps : ℝ) : ℕ := ⌈1/accuracy eps⌉₊
def threshold (eps : ℝ) : ℕ → ℝ
  | 0 => 1
  | i+1 => min (threshold eps i / 2)
      (bZero (accuracy eps) (accuracy eps) (1 + covarianceBound (threshold eps i) (accuracy eps)))
def thresholdK (eps : ℝ) (i : ℕ) : ℝ := 1 + covarianceBound (threshold eps i) (accuracy eps)
def sampleConstant (eps : ℝ) : ℝ :=
  max (6/(kappa (accuracy eps) (accuracy eps) * (accuracy eps)^2))
    (Real.log (1/accuracy eps) / threshold eps (bandCount eps))

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (p : Edge G → ℝ) {w : Edge G → ℝ} (s : Selector G w)

def crucial (eps : ℝ) (i : ℕ) : Realization G :=
  Finset.univ.filter (fun e => threshold eps i ≤ marginal G p s e / p e)
def nonCrucial (eps : ℝ) (i : ℕ) : Realization G :=
  Finset.univ.filter (fun e => marginal G p s e / p e ≤ threshold eps (i+1))
def band (eps : ℝ) (i : ℕ) : Realization G :=
  Finset.univ.filter (fun e => threshold eps (i+1) < marginal G p s e / p e ∧
    marginal G p s e / p e < threshold eps i)
/-- The resampled reference of §7.3 is used for its law only. -/
def crucialReference (eps : ℝ) (i : ℕ) (actual fresh : Realization G) : Realization G :=
  let C := crucial G p s eps i
  s.choose ((actual ∩ C) ∪ (fresh \ C)) ∩ C

def markedMatching (M : Realization G) (marks : V → Bool) : Realization G :=
  M.filter (fun e => ∀ v, v ∈ (e : Sym2 V) → marks v = false)
def availableVertices (M : Realization G) (marks : V → Bool) : Finset V :=
  Finset.univ.filter (fun v => v ∉ vertices G M ∨ marks v = true)
def markLaw (beta : ℝ) : Measure (V → Bool) :=
  ∑ m : V → Bool, ENNReal.ofReal (∏ v : V, if m v then beta else 1-beta) • Measure.dirac m

/-- The §7 product space; auxiliary randomness remains continuous if the chosen ν is. -/
abbrev AssemblySpace (r : ℕ) (ν : VertexLaw V) :=
  (Realization G × (Fin r → Realization G)) × (((v : V) → ν.carrier v) × (V → Bool))

def assemblyLaw (r : ℕ) (ν : VertexLaw V) (eps : ℝ) : Measure (AssemblySpace G r ν) :=
  (algorithmLaw G p r).prod (ν.joint.prod (markLaw (accuracy eps)))
def crucialRaw {r : ℕ} (ν : VertexLaw V)
    (alg : Realization G → ((v : V) → ν.carrier v) → Realization G)
    (eps : ℝ) (i : ℕ) (z : AssemblySpace G r ν) : Realization G :=
  alg (z.1.1 ∩ crucial G p s eps i) z.2.1

def crucialMarked {r : ℕ} (ν : VertexLaw V)
    (alg : Realization G → ((v : V) → ν.carrier v) → Realization G)
    (eps : ℝ) (i : ℕ) (z : AssemblySpace G r ν) : Realization G :=
  markedMatching G (crucialRaw G p s ν alg eps i z) z.2.2

def assemblyAvailable {r : ℕ} (ν : VertexLaw V)
    (alg : Realization G → ((v : V) → ν.carrier v) → Realization G)
    (eps : ℝ) (i : ℕ) (z : AssemblySpace G r ν) : Finset V :=
  availableVertices G (crucialRaw G p s ν alg eps i z) z.2.2

/-- The exact (7.8)-(7.10) conclusions used to instantiate the chosen map from Lemma 5.1.
The map is an input to the assembly claims; it is never manufactured by choice from an unproved theorem. -/
def CrucialGuarantee (ν : VertexLaw V)
    (alg : Realization G → ((v : V) → ν.carrier v) → Realization G)
    (eps : ℝ) (i : ℕ) : Prop :=
  let C := crucial G p s eps i
  let μ := (realizationLaw G p).prod ν.joint
  (∀ F ξ, alg (F ∩ C) ξ ⊆ F ∩ C ∧ IsMatching G (alg (F ∩ C) ξ)) ∧
  Measurable (fun z : Realization G × ((v : V) → ν.carrier v) => alg (z.1 ∩ C) z.2) ∧
  (∀ e ∈ C, prob μ (fun z => e ∈ alg (z.1 ∩ C) z.2) ≤ marginal G p s e) ∧
  mean μ (fun z => weightOf w (alg (z.1 ∩ C) z.2)) ≥
    (1-2*accuracy eps) * W G p s C ∧
  (∀ u, ∑ v : V,
    |cov μ (fun z => ind (u ∉ vertices G (alg (z.1 ∩ C) z.2)))
      (fun z => ind (v ∉ vertices G (alg (z.1 ∩ C) z.2)))| ≤
        covarianceBound (threshold eps i) (accuracy eps))
end
end StochMatchQuery.Union


