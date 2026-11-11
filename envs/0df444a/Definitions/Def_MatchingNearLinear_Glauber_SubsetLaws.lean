-- Prove2me | Definitions.Def_MatchingNearLinear_Glauber_SubsetLaws
-- name    : MatchingNearLinear_Glauber_SubsetLaws
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T15:54:34.048547+00:00
-- url     : https://prove2.me/theorems/19f6947f-bb27-4e27-82c9-c25553ba088f
-- title:
--   Subset laws, positive pinnings, polynomial spaces and single-site dynamics
-- statement:
--   For $N$ coordinates, let $p$ be a nonnegative mass function summing to one on subsets of $[N]$. Its actual support is $\Omega=\{S:p(S)>0\}$. Downward closure and maximum occupied size $r$ are defined from this support. Positive pinning and scalar fields are
--
--   $$p^\tau(T)=\frac{p(\tau\cup T)}{\sum_{U\supseteq\tau}p(U)},\quad T\cap\tau=\varnothing,\qquad \nu_t(S)\propto(1-t)^{|S|}p(S).$$
--
--   The definitions include indicator marginals and covariance, mean-normalized covariance bounds, spectral stability after every positive pin, the extended nonnegative stability integral, insertion-ratio and occupied-marginal bounds, and multilinear polynomial spaces with their true weighted projections. The single-site heat bath selects uniformly among all $N$ original coordinates. For homogeneous laws, the down–up walk deletes one uniform occupied coordinate and resamples conditional on the remainder. These are common interfaces for the analytic milestones. Finiteness of the integral is an explicit theorem hypothesis; it never defaults to zero on divergence.
-- source:
--   Tianshun Miao, Yitong Yin, Sampling Matchings in Near-linear Time, STOC 2027 submission #444 (October 2026), Definition 1.1, printed p.3 (PDF p.5); §3.1–3.2, printed pp.10,13 (PDF pp.12,15), Eqs. (1)–(4),(12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/444.pdf

import Mathlib
import Definitions.Def_MatchingNearLinear_Glauber_FiniteAnalysis

set_option autoImplicit false

namespace MatchingNearLinear.Glauber


open scoped BigOperators
noncomputable section
open Classical
abbrev Config (N : ℕ) := Finset (Fin N)

def IsSubsetLaw {N : ℕ} (p : Config N → ℝ) : Prop := MarkovMixing.IsDist p

abbrev Support {N : ℕ} (p : Config N → ℝ) := {S : Config N // 0 < p S}
noncomputable instance supportFintype {N : ℕ} (p : Config N → ℝ) : Fintype (Support p) := Fintype.ofFinite _
noncomputable instance supportDecEq {N : ℕ} (p : Config N → ℝ) : DecidableEq (Support p) := Classical.decEq _

def supportMass {N : ℕ} (p : Config N → ℝ) : Support p → ℝ := fun S => p S.val

def DownwardClosed {N : ℕ} (p : Config N → ℝ) : Prop :=
  ∀ S T, 0 < p S → T ⊆ S → 0 < p T

def rank {N : ℕ} (p : Config N → ℝ) : ℕ :=
  (Finset.univ.filter fun S => 0 < p S).sup Finset.card

def pinMass {N : ℕ} (p : Config N → ℝ) (τ : Config N) : ℝ :=
  ∑ S, if τ ⊆ S then p S else 0

/-- Positive pinning fixes only occupation; residual coordinates exclude τ. -/
def positivePin {N : ℕ} (p : Config N → ℝ) (τ : Config N) (T : Config N) : ℝ :=
  if Disjoint τ T then p (τ ∪ T) / pinMass p τ else 0

def scalarTilt {N : ℕ} (p : Config N → ℝ) (t : ℝ) (S : Config N) : ℝ :=
  (1-t)^S.card * p S / ∑ T, (1-t)^T.card * p T

def indicator {N : ℕ} (S : Config N) (i : Fin N) : ℝ := if i ∈ S then 1 else 0

def marginal {N : ℕ} (p : Config N → ℝ) (i : Fin N) : ℝ :=
  ∑ S, p S * indicator S i

def covariance {N : ℕ} (p : Config N → ℝ) (i j : Fin N) : ℝ :=
  (∑ S, p S * indicator S i * indicator S j) - marginal p i * marginal p j

/-- Loewner order tested against every real coefficient vector; normalized by means. -/
def CovarianceBound {N : ℕ} (p : Config N → ℝ) (c : ℝ) : Prop :=
  ∀ a : Fin N → ℝ,
    (∑ i, ∑ j, a i * covariance p i j * a j) ≤ c * ∑ i, marginal p i * (a i)^2

/-- Definition 1.1. Zero and deterministic residual rows cause no problem. -/
def SpectralStability {N : ℕ} (p : Config N → ℝ) (C : ℝ → ℝ) : Prop :=
  (∀ t ∈ Set.Ico (0:ℝ) 1, 0 ≤ C t) ∧
  ∀ t ∈ Set.Ico (0:ℝ) 1, ∀ τ, 0 < p τ → CovarianceBound (positivePin (scalarTilt p t) τ) (C t)

/-- Nonnegative extended integral, so divergence is not silently replaced by zero. -/
def stabilityIntegral (C : ℝ → ℝ) : ENNReal :=
  ∫⁻ t in Set.Ioo (0:ℝ) 1, ENNReal.ofReal ((C t - 1)/(1-t))

def RateConditions (C : ℝ → ℝ) : Prop :=
  AntitoneOn C (Set.Ico (0:ℝ) 1) ∧ (∀ t ∈ Set.Ico (0:ℝ) 1, 1 ≤ C t) ∧
  stabilityIntegral C ≠ ⊤

def RatioBound {N : ℕ} (p : Config N → ℝ) (κ : ℝ) : Prop :=
  ∀ S i, 0 < p S → i ∉ S → 0 < p (insert i S) → p (insert i S) / p S ≤ κ

def OccupiedLowerBound {N : ℕ} (p : Config N → ℝ) (b : ℝ) : Prop :=
  ∀ τ i, 0 < p τ → i ∉ τ → 0 < p (insert i τ) → b ≤ marginal (positivePin p τ) i

/-- All multilinear monomials, including zero ones; same span as feasible pins only. -/
def polynomialSpace {N : ℕ} (p : Config N → ℝ) (j : ℕ) : Submodule ℝ (Support p → ℝ) :=
  Submodule.span ℝ {g | ∃ A : Config N, A.card ≤ j ∧ g = fun S => if A ⊆ S.val then 1 else 0}

def polynomialProjection {N : ℕ} (p : Config N → ℝ) (j : ℕ) (f : Support p → ℝ) :=
  projection (supportMass p) (polynomialSpace p j) f

/-- Uniform original-coordinate heat bath, one coordinate per discrete step. -/
def subsetGlauber {N : ℕ} (p : Config N → ℝ) : Matrix (Support p) (Support p) ℝ :=
  fun S T => (1 / (N:ℝ)) * ∑ i : Fin N,
    if S.val.erase i = T.val.erase i then
      p T.val / (p (S.val.erase i) + p (insert i (S.val.erase i))) else 0

/-- Delete a uniformly chosen element, then resample conditional on the remainder. -/
def downUp {N : ℕ} (p : Config N → ℝ) (r : ℕ) : Matrix (Support p) (Support p) ℝ :=
  fun S T => (1 / (r:ℝ)) * ∑ i ∈ S.val,
    if S.val.erase i ⊆ T.val then p T.val / pinMass p (S.val.erase i) else 0

end
end MatchingNearLinear.Glauber


