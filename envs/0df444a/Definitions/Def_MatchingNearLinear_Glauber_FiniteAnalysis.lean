-- Prove2me | Definitions.Def_MatchingNearLinear_Glauber_FiniteAnalysis
-- name    : MatchingNearLinear_Glauber_FiniteAnalysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T15:54:00.502816+00:00
-- url     : https://prove2.me/theorems/2d669997-7930-4ad6-9c37-d66f5ab96221
-- title:
--   Finite-support norms, orthogonal projection and functional inequalities
-- statement:
--   Let $\Omega$ be a finite state space, $p$ a positive probability vector and $P$ a transition matrix. The general stochasticity, probability and reversibility predicates come from the published MarkovMixing interface. The source conventions are
--
--   $$\mathcal E_P(f,g)=\tfrac12\sum_{x,y}p(x)P(x,y)(f(x)-f(y))(g(x)-g(y)),\qquad \operatorname{Ent}_p(h)=E_p[h\log h]-E_p[h]\log E_p[h].$$
--
--   The file defines weighted norms, the constant subspace, and the weighted orthogonal projection onto any real linear subspace by its unique orthogonality equations. LSI and MLSI upper bounds are expressed as the defining inequalities rather than reciprocals of potentially invalid extrema. A mixing bound supplies a natural integer horizon uniformly valid over starting states. Total variation is one half the sum of absolute mass differences. These shared conventions support every analytic statement. The zero-log convention is $0\log0=0$; finite positive laws make all norms, projections and minimum masses well posed.
-- source:
--   Tianshun Miao, Yitong Yin, Sampling Matchings in Near-linear Time, STOC 2027 submission #444 (October 2026), §§1.1–2.1, printed pp.3–4,8 (PDF pp.5–6,10), Eqs. (6)–(8); §3.1, printed p.10 (PDF p.12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/444.pdf

import Mathlib
import Definitions.Def_mm_basic

set_option autoImplicit false

namespace MatchingNearLinear.Glauber


open scoped BigOperators
noncomputable section
open Classical
variable {α : Type} [Fintype α] [DecidableEq α]

/-- Positive mass on the actual finite support; stochasticity uses the published general API. -/
def PositiveLaw (p : α → ℝ) : Prop := MarkovMixing.IsDist p ∧ ∀ x, 0 < p x

def mean (p f : α → ℝ) : ℝ := ∑ x, p x * f x

def entropy (p h : α → ℝ) : ℝ :=
  mean p (fun x => h x * Real.log (h x)) - mean p h * Real.log (mean p h)

/-- The pair-sum convention (6), with one update as time unit. -/
def energy (p : α → ℝ) (P : Matrix α α ℝ) (f g : α → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ x, ∑ y, p x * P x y * (f x - f y) * (g x - g y)

def normSq (p f : α → ℝ) : ℝ := mean p (fun x => (f x)^2)
def normTwo (p f : α → ℝ) : ℝ := Real.sqrt (normSq p f)
def normInfinity (f : α → ℝ) : ℝ := sSup (Set.range fun x => |f x|)

/-- The uniquely characterized weighted orthogonal projection. The fallback is only for
invalid weights. For a positive law, finite-dimensional projection exists uniquely. -/
def projection (p : α → ℝ) (V : Submodule ℝ (α → ℝ)) (f : α → ℝ) : α → ℝ :=
  if h : ∃ g ∈ V, ∀ v ∈ V, mean p (fun x => (f x - g x) * v x) = 0
  then h.choose else 0

def constantSpace : Submodule ℝ (α → ℝ) :=
  Submodule.span ℝ {g | ∃ c : ℝ, g = fun _ => c}

/-- Direct inequalities avoid an empty/unbounded real extremum for an invalid kernel. -/
def LSIBound (p : α → ℝ) (P : Matrix α α ℝ) (B : ℝ) : Prop :=
  ∀ f : α → ℝ, entropy p (fun x => (f x)^2) ≤ B * energy p P f f

def MLSIBound (p : α → ℝ) (P : Matrix α α ℝ) (B : ℝ) : Prop :=
  ∀ h : α → ℝ, (∀ x, 0 < h x) → entropy p h ≤ B * energy p P h (fun x => Real.log (h x))

def totalVariation (p q : α → ℝ) : ℝ := (1 / 2 : ℝ) * ∑ x, |p x - q x|

/-- Equivalent to the least-integer mixing-time bound, with finiteness certified. -/
def MixingBound (p : α → ℝ) (P : Matrix α α ℝ) (ε B : ℝ) : Prop :=
  ∃ t : ℕ, (t : ℝ) ≤ B ∧ ∀ x, totalVariation (fun y => (P^t) x y) p ≤ ε

def minMass (p : α → ℝ) : ℝ := sInf (Set.range p)

end
end MatchingNearLinear.Glauber


